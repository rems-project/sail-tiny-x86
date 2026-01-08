union ast = {
    // Structure of all possible executable instructions
    // if a type contains 2 operands, the first operand is dest and the second is src, unless the instruction is CMP
    MOV: (operand_size, rm_operand, rmi_operand),
    XOR: (bool, operand_size, rm_operand, rmi_operand),
    SFENCE: unit,
    LFENCE: unit,
    MFENCE: unit,
    CMP: (operand_size, rm_operand, rmi_operand),
    PUSH: (operand_size, rmi_operand),
    POP: (operand_size, rm_operand),
    ADD: (bool, operand_size, rm_operand, rmi_operand),
    SUB: (bool, operand_size, rm_operand, rmi_operand),
    IMUL: (operand_size, reg_index, rm_operand), // IMUL with only 2 arguments (dest and src)
    CALL: imm32,
    LEAVE: {16, 64}, // operand size can be 16 or 64 bits
    RET: unit, // near return only
    JMP: imm8, // jump short only
    JNS: imm8 // jump short if not sign only
}

// bitfield to easily access fields within the REX prefix
bitfield REX: bits(8) = {
    W: 3,
    R: 2,
    X: 1,
    B: 0
}

// bitfield to easily access fields within the mod r/m byte
bitfield modRMByte: bits(8) = {
    Mod: 7 .. 6,
    REG: 5 .. 3,
    RM: 2 .. 0,
}

// bitfield to easily access fields within the SIB byte
bitfield SIBByte: bits(8) = {
    Scale: 7 .. 6,
    Index: 5 .. 3,
    Base: 2 .. 0
}

// struct to store decoded prefixes
struct decodedPrefixes = {
    lock: bool, // encoding is F0 (hex)
    op_size_override: bool, // encoding is 66 (hex)
    mandatory_prefix_66H: bool, // encoding is 66 (hex) + must occur right before opcode or REX prefix
    REX: REX // encoding is 0100WRXB (binary) + must occur right before opcode
}

// types of addressing method used to represent operands
enum addressingMethod = { 
    addressingMethod_E, 
    addressingMethod_G
}



/*------------------------------------------------------------------------------
 * DECODE Prefix
 *-----------------------------------------------------------------------------*/

// resets a prefix if it is ignored when not the last prefix
val reset_prefixes_not_at_end: decodedPrefixes -> decodedPrefixes
function reset_prefixes_not_at_end(decoded_prefixes) = {
    {decoded_prefixes with 
        // 66H is only counted as a mandatory prefix if it is the last prefix (other than REX) to occur
        mandatory_prefix_66H = false, 
        // REX prefix is only used if it is the last prefix to occur
        REX = struct {bits = 0x00}
    }
}

// function to decode prefixes
val decode_prefix_inner: (bits(64), int, decodedPrefixes, bits(8), int) -> (int, decodedPrefixes)
function decode_prefix_inner(instruction_ptr, read_offset, decoded_prefixes, prev_prefix, max_iters) = {
    if max_iters == 0 then
        // either all prefixes have been read, or max number of possible prefixes has been exceeded
        (read_offset, decoded_prefixes)
    else {
        // read next potential prefix
        let next_prefix: bits(8) = read_memory(1, instruction_ptr + read_offset, create_iFetchAccessDescriptor());

        // if we have a lock prefix
        if next_prefix == 0xF0 then {
            // (reset placement-dependent prefixes)
            let reset_decoded_prefixes = reset_prefixes_not_at_end(decoded_prefixes) in
            // set lock to true
            let new_decoded_prefixes = {reset_decoded_prefixes with lock = true} in
            // check for more prefixes
                decode_prefix_inner(instruction_ptr, read_offset + 1, new_decoded_prefixes, next_prefix, max_iters - 1)
        }
        // if we have a operand size override (to 16 bits) / potential mandatory prefix, 
        else if next_prefix == 0x66 then {
            // (reset placement-dependent prefixes)
            let reset_decoded_prefixes = reset_prefixes_not_at_end(decoded_prefixes) in
            // set the corresponding fields to true
            let new_decoded_prefixes = {reset_decoded_prefixes with op_size_override = true, mandatory_prefix_66H = true} in
            // check for more prefixes
                decode_prefix_inner(instruction_ptr, read_offset + 1, new_decoded_prefixes, next_prefix, max_iters - 1)
        }
        // if we have a REX prefix
        else if next_prefix[7 .. 4] == 0x4 then {
            // (reset placement-dependent prefixes if necessary)
            let reset_decoded_prefixes = (if prev_prefix == 0x66 then decoded_prefixes else reset_prefixes_not_at_end(decoded_prefixes)) in
            // set the REX field according to the prefix's value
            let rex_contents: REX = struct{bits = next_prefix} in
            let new_decoded_prefixes = {reset_decoded_prefixes with REX = rex_contents} in
            // check for more prefixes
                decode_prefix_inner(instruction_ptr, read_offset + 1, new_decoded_prefixes, next_prefix, max_iters - 1)
        }
        else
            // return the result of decoding all the prefixes, as there are no more potential prefixes to check
            decode_prefix_inner(instruction_ptr, read_offset, decoded_prefixes, prev_prefix, 0)
    }
}

// Tells rocq that max_iters bounds the number of times that decode_prefix_inner is called
termination_measure decode_prefix_inner(_,_,_,_,max_iters) = max_iters

// wrapper function to decode the prefixes of an instruction
val decode_prefix: (bits(64), decodedPrefixes) -> (int, decodedPrefixes)
function decode_prefix(instruction_ptr, decoded_prefixes) = {
    let (read_offset, decoded_prefixes) = decode_prefix_inner(instruction_ptr, 0, decoded_prefixes, 0x00, 15);
    (read_offset, decoded_prefixes)
}



/*------------------------------------------------------------------------------
 * DECODE SIB byte, Mod r/m byte, and opcode reg field
 *-----------------------------------------------------------------------------*/

// for the following 4 helper functions, see section 2.2.1.2 - More on REX Prefix Fields
// The REX prefix may allow one to access registers R8-R15

val get_mod_rm_byte_REG: (modRMByte, REX) -> reg_index
function get_mod_rm_byte_REG(mod_rm_byte, REX) = {
    let base_reg_loc = unsigned(mod_rm_byte[REG]) in 
    if REX[R] == 0b1 then 8 + base_reg_loc else base_reg_loc
}

val get_mod_rm_byte_RM: (modRMByte, REX) -> reg_index
function get_mod_rm_byte_RM(mod_rm_byte, REX) = {
    let base_reg_loc = unsigned(mod_rm_byte[RM])in 
    if REX[B] == 0b1 then 8 + base_reg_loc else base_reg_loc
}

val get_sib_byte_BASE: (SIBByte, REX) -> reg_index
function get_sib_byte_BASE(sib_byte, REX) = {
    let base_reg_loc = unsigned(sib_byte[Base]) in
    if REX[B] == 0b1 then 8 + base_reg_loc else base_reg_loc
}

val get_sib_byte_INDEX: (SIBByte, REX) -> reg_index
function get_sib_byte_INDEX(sib_byte, REX) = {
    let base_reg_loc = unsigned(sib_byte[Index]) in
    if REX[X] == 0b1 then 8 + base_reg_loc else base_reg_loc
}

val get_reg_value_in_opcode_byte: (bits(3), REX) -> reg_index
function get_reg_value_in_opcode_byte(reg_field, REX) = {
    let base_reg_loc = unsigned(reg_field) in
    if REX[B] == 0b1 then 8 + base_reg_loc else base_reg_loc
}

// Decode SIB byte (sometimes needed for decoding register or memory operands)
val decode_sib_byte: (SIBByte, REX) -> bits(64)
function decode_sib_byte(sib_byte, REX) = {
    // value stored in the SIB byte is base + index * (2^scale)
    /* Note: if the value stored in the base or index fields of the SIB byte is 5, 
    then we can't read the value stored in this register location, as the index is of the RBP,*/
    let sib_byte_BASE = get_sib_byte_BASE(sib_byte, REX);
    let sib_byte_INDEX = get_sib_byte_INDEX(sib_byte, REX);
    let base = if sib_byte_BASE == 5 then sail_zero_extend(0x0, 64) else {
        // base = value stored in this register location
        read_GPR(64, REG_NORMAL(sib_byte_BASE))
    };
    let index = if sib_byte_INDEX == 4 then sail_zero_extend(0x0, 64) else {
        // index = value stored in this register location
        read_GPR(64, REG_NORMAL(sib_byte_INDEX))
    };
    // return the value stored in the SIB byte, which is base + index * (2^scale)
    add_bits(base, sail_shiftleft(index, unsigned(sib_byte[Scale])))
}

val read_mod_rm_byte: (bits(64), int) -> (int, modRMByte)
function read_mod_rm_byte(instruction_ptr, read_offset) = {
    let mod_rm_byte_contents = 
        read_memory(1, instruction_ptr + read_offset, create_iFetchAccessDescriptor()) in
        (read_offset + 1, struct {bits = mod_rm_byte_contents})
}



/*------------------------------------------------------------------------------
 * DECODE Register or Memory operands
 *-----------------------------------------------------------------------------*/

// Get the operand size for an instruction which doesn't ignore the REX prefix
val get_operand_size_using_REX: (decodedPrefixes, {32, 64}) -> {16, 32, 64}
function get_operand_size_using_REX(decoded_prefixes, default_operand_size) = {
    if decoded_prefixes.REX[W] == 0b1 then 64 
    else if decoded_prefixes.op_size_override then 16 
    else default_operand_size
}

// Get the operand size for an instruction which ignores the REX prefix
val get_operand_size_ignoring_REX: (decodedPrefixes, {32, 64}) -> {16, 32, 64}
function get_operand_size_ignoring_REX(decoded_prefixes, default_operand_size) = {
    if decoded_prefixes.op_size_override then 16
    else default_operand_size
}

// Read and decode immediate operand
val read_imm_operand: (bits(64), int, operand_size) -> (int, imm)
function read_imm_operand(instruction_ptr, read_offset, operand_size) = {
    let operand_size_bytes = operand_size / 8;
    assert(operand_size == 8 * operand_size_bytes); // required for type-checking
    let imm_value = read_memory(operand_size_bytes, instruction_ptr + read_offset, create_iFetchAccessDescriptor());
    let wrapped_imm: imm = match operand_size {
        8 => IMM8(imm_value),
        16 => IMM16(imm_value),
        32 => IMM32(imm_value),
        64 => IMM64(imm_value)
    };
    (read_offset + operand_size_bytes, wrapped_imm)
}

val wrap_reg: (reg_index, operand_size, REX) -> reg
function wrap_reg(reg_index, operand_size, REX) = {
    if operand_size == 8 & REX.bits == 0x00 & reg_index >=4 & reg_index <= 7 then
        // Register is high byte. reg_index 4-7 represents actual reg_index 0-3
        REG_HIGH_BYTE(reg_index - 4)
    else
        REG_NORMAL(reg_index)
}

// function to decode single r/m operand, given the mod_rm_byte
// returns the new read offset and the operand
val decode_rm_operand_inner: (addressingMethod, bits(64), int, modRMByte, operand_size, REX) -> (int, rm_operand)
scattered function decode_rm_operand_inner

/* function definition for addressing method E:
 of the mod r/m byte, the mod bits and r/m bits determine the operand */
function clause decode_rm_operand_inner(addressingMethod_E, instruction_ptr, read_offset, mod_rm_byte, operand_size, REX) = {
    // read r/m bits (returns register index)
    let reg_used: reg_index = get_mod_rm_byte_RM(mod_rm_byte, REX);

    if mod_rm_byte[Mod] == 0b11 then 
        // the r/m bits specify the register index of the operand
        let wrapped_reg = wrap_reg(reg_used, operand_size, REX) in
        (read_offset, rm_REG(wrapped_reg))
    else {
        // the mod and r/m bits are used to specify a memory location
        var new_read_offset: int = read_offset;
        var mem_loc: bits(64) = {
            // get original 3-bit register location stored in the mod r/m byte
            let three_bit_reg_used = mod(reg_used, 8) in
            if three_bit_reg_used == 4 then { 
                // this register value means that we need to decode the SIB byte
                let sib_byte: SIBByte = struct {
                    // read SIB byte
                    bits = read_memory(1, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor())
                };
                // convert the byte to a value
                let sib_value = decode_sib_byte(sib_byte, REX);
                // increment read_offset (add 1 to it)
                new_read_offset = new_read_offset + 1;
                // working value is set to the value stored in the SIB byte
                sib_value
            }
            // else working value is set to the value stored in the register index that we read earlier
            else read_GPR(64, REG_NORMAL(reg_used))
        };
        match mod_rm_byte[Mod] {
            0b01 => {
                // we need to add an 8 bit displacement value to mem_loc
                // fetch the 8 bit displacement
                let displacement = read_memory(1, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor());
                // sign-extend the 8 bit displacement, then add it to mem_loc
                mem_loc = add_bits(mem_loc, sail_sign_extend(displacement, 64));
                // increment read offset
                new_read_offset = new_read_offset + 1;
            },
            0b10 => {
                // we need to add a sign-extended 32-bit displacement to mem_loc
                // fetch the 32 bit (4 byte) displacement
                let displacement = read_memory(4, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor());
                // sign-extend the 32 bit displacement, then add it to mem_loc
                mem_loc = add_bits(mem_loc, sail_sign_extend(displacement, 64));
                // increment read offset
                new_read_offset = new_read_offset + 4;
            },
            // if our mod bits are 00, then we don't add a displacement to mem_loc
            // this match statement is not reachable for mod bits = 11
            _ => () 
        };
        // return the new read offset and decoded operand
        (new_read_offset, rm_MEM(mem_loc))
    }
}

/* function definition for addressing method E:
 of the mod r/m byte, the reg bits determine the register index of the operand */
function clause decode_rm_operand_inner(addressingMethod_G, instruction_ptr, read_offset, mod_rm_byte, operand_size, REX) = {
    // read reg bits of the mod r/m byte
    let reg_index = get_mod_rm_byte_REG(mod_rm_byte, REX) in
    let wrapped_reg = wrap_reg(reg_index, operand_size, REX) in
    // return the read offset and decoded operand
    (read_offset, rm_REG(wrapped_reg))
}

// function to decode 2 register or memory operands
// returns the new read offset, operand1, and operand2
val decode_2_rm_operands: (bits(64), int, addressingMethod, addressingMethod, operand_size, REX) -> (int, rm_operand, rmi_operand)
function decode_2_rm_operands(instruction_ptr, read_offset, operand1_addr_method, operand2_addr_method, operand_size, REX) = {
    let (new_offset, mod_rm_byte) = read_mod_rm_byte(instruction_ptr, read_offset);
    let (new_offset2, operand1) = decode_rm_operand_inner(operand1_addr_method, instruction_ptr, new_offset, mod_rm_byte, operand_size, REX);
    let (new_offset3, working_operand2) = decode_rm_operand_inner(operand2_addr_method, instruction_ptr, new_offset2, mod_rm_byte, operand_size, REX);
    let operand2: rmi_operand = match working_operand2 {
        rm_REG(value) => rmi_REG(value),
        rm_MEM(value) => rmi_MEM(value)
    };
    (new_offset3, operand1, operand2)
}

// Get 2 operands of the addressing method + operand type: Operand 1 = Ev, Operand 2 = Gv
val get_Ev_Gv_operands: (bits(64), int, decodedPrefixes) -> (int, operand_size, rm_operand, rmi_operand)
function get_Ev_Gv_operands(instruction_ptr, read_offset, decoded_prefixes) = {
    // the operand type is v, so operand size is determined by the instruction prefices. Default operand size is 32 bits.
    let operand_size = get_operand_size_using_REX(decoded_prefixes, 32);
    // decode operands
    let (new_read_offset, operand1, operand2) = 
        decode_2_rm_operands(instruction_ptr, read_offset, addressingMethod_E, addressingMethod_G, operand_size, decoded_prefixes.REX);
    (new_read_offset, operand_size, operand1, operand2)
}

// Get 2 operands of the addressing method + operand type: Operand 1 = Gv, Operand 2 = Ev
val get_Gv_Ev_operands: (bits(64), int, decodedPrefixes) -> (int, operand_size, rm_operand, rmi_operand)
function get_Gv_Ev_operands(instruction_ptr, read_offset, decoded_prefixes) = {
    // the operand type is v, so operand size is determined by the instruction prefices. Default operand size is 32 bits.
    let operand_size = get_operand_size_using_REX(decoded_prefixes, 32);
    // decode operands
    let (new_read_offset, operand1, operand2) = 
        decode_2_rm_operands(instruction_ptr, read_offset, addressingMethod_G, addressingMethod_E, operand_size, decoded_prefixes.REX);
    (new_read_offset, operand_size, operand1, operand2)
}

// Get 2 operands of the addressing method + operand type: Operand 1 = Eb, Operand 2 = Gb
// Operand type is b, which means that the operand size is 8 bits. So we don't need to return this information
val get_Eb_Gb_operands: (bits(64), int, REX) -> (int, rm_operand, rmi_operand)
function get_Eb_Gb_operands(instruction_ptr, read_offset, REX) = 
    decode_2_rm_operands(instruction_ptr, read_offset, addressingMethod_E, addressingMethod_G, 8, REX)

// Get 2 operands of the addressing method + operand type: Operand 1 = Gb, Operand 2 = Eb
// Operand type is b, which means that the operand size is 8 bits. So we don't need to return this information
val get_Gb_Eb_operands: (bits(64), int, REX) -> (int, rm_operand, rmi_operand)
function get_Gb_Eb_operands(instruction_ptr, read_offset, REX) = 
    decode_2_rm_operands(instruction_ptr, read_offset, addressingMethod_G, addressingMethod_E, 8, REX)

// function to decode a r/m operand for PUSH and POP instructions
val decode_push_or_pop_rm_operand: (bits(64), int, decodedPrefixes, modRMByte) -> (int, operand_size, rm_operand)
function decode_push_or_pop_rm_operand(instruction_ptr, read_offset, decoded_prefixes, mod_rm_byte) = {
    // Get operand size. Default operand size is 64 bits. Ignore REX.
    let operand_size = get_operand_size_ignoring_REX(decoded_prefixes, 64);
    // Decode operand. Operand addressing method + operand type is Ev
    let (final_offset, operand) = decode_rm_operand_inner(addressingMethod_E, instruction_ptr, read_offset, mod_rm_byte, operand_size, decoded_prefixes.REX);
    (final_offset, operand_size, operand)
}

// Get 2 operands of the addressing method + operand type: Operand 1 = Ev, Operand 2 = Iz
val get_Ev_Iz_operands: (bits(64), int, decodedPrefixes, modRMByte) -> (int, operand_size, rm_operand, imm)
function get_Ev_Iz_operands(instruction_ptr, read_offset, decoded_prefixes, mod_rm_byte) = {
    // Get operand size. Default is 32 bits.
    let operand_size = get_operand_size_using_REX(decoded_prefixes, 32);
    // Get r/m operand
    let (read_offset, operand1) = decode_rm_operand_inner(addressingMethod_E, instruction_ptr, read_offset, mod_rm_byte, operand_size, decoded_prefixes.REX);
    // Get imm operand
    let imm_size = if operand_size == 64 then 32 else operand_size;
    let (read_offset, imm) = read_imm_operand(instruction_ptr, read_offset, imm_size);
    // return new read offset, operand size, and operands
    (read_offset, operand_size, operand1, imm)
}

// Get 2 operands of the addressing method + operand type: Operand 1 = Ev, Operand 2 = Iz
val get_Eb_Ib_operands: (bits(64), int, REX, modRMByte) -> (int, rm_operand, imm)
function get_Eb_Ib_operands(instruction_ptr, read_offset, REX, mod_rm_byte) = {
    // Get r/m operand
    let (read_offset, operand1) = decode_rm_operand_inner(addressingMethod_E, instruction_ptr, read_offset, mod_rm_byte, 8, REX);
    // Get imm operand
    let (read_offset, imm) = read_imm_operand(instruction_ptr, read_offset, 8);
    // return new read offset and operands
    (read_offset, operand1, imm)
}



/*------------------------------------------------------------------------------
 * DECODE Instruction
 *-----------------------------------------------------------------------------*/

// function to decode one byte instructions. Function definitions are inlined with corresponding execute definitions
val decode_one_byte_instruction: (bits(8), bits(64), int, decodedPrefixes) -> option((int, ast))
scattered function decode_one_byte_instruction

// function to decode three byte instructions. Function definitions are inlined with corresponding execute definitions
val decode_two_byte_instruction: (bits(16), bits(64), int, decodedPrefixes) -> option((int, ast))
scattered function decode_two_byte_instruction

// function to decode the main instruction
// returns the new read offset, an incomplete AST entry, and a struct of optional instruction parts we now know to exist
val decode_instruction: (bits(64), int, decodedPrefixes) -> option((int, ast))
function decode_instruction(instruction_ptr, read_offset, decoded_prefixes) = {
    /* first see if our opcode is one byte. If so, decode the instruction */
    // fetch the first opcode byte from memory
    let one_byte_opcode = read_memory(1, instruction_ptr + read_offset, create_iFetchAccessDescriptor());
    // increment read_offset
    var new_read_offset: int = read_offset + 1;
    // try to decode the opcode and find the instruction operands
    var res = decode_one_byte_instruction(one_byte_opcode, instruction_ptr, new_read_offset, decoded_prefixes);

    // If the first byte of the opcode could not be decoded
    if res == None() then {
        /* See if our opcode is two bytes long. If so, decode the instruction */
        let two_byte_opcode = one_byte_opcode @ read_memory(1, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor());
        new_read_offset = new_read_offset + 1;
        res = decode_two_byte_instruction(two_byte_opcode, instruction_ptr, new_read_offset, decoded_prefixes);
    };

    res
}

// base decode function: decode the prefix and then the main instruction
val decode: bits(64) -> option((bits(64), ast))
function decode(instruction_ptr) = {
    // keep a counter of how many bytes of the instruction we have read so far
    var read_offset: int = 0;
    // keep a struct of which prefixes the instruction has
    var decoded_prefixes: decodedPrefixes = struct { 
        lock = false, 
        op_size_override = false, 
        mandatory_prefix_66H = false,
        REX = struct {bits = 0x00}
    };

    // decode prefix
    (read_offset, decoded_prefixes) = decode_prefix(instruction_ptr, decoded_prefixes);

    // decode rest of instruction
    let res = decode_instruction(instruction_ptr, read_offset, decoded_prefixes);
    match res {
        None() => None(),
        Some(offset, instruction) => {
            if offset > 15 then 
                fail("Instruction is longer than 15 bytes, hence is not valid")
            else
                Some(instruction_ptr + offset, instruction)
        }
    }
}



/*------------------------------------------------------------------------------
 * Fetch-execute
 *-----------------------------------------------------------------------------*/

val execute : ast -> unit
scattered function execute

val fetch_execute: unit -> unit
function fetch_execute() = {
    let decoded = decode(RIP);
    match decoded {
        Some(new_RIP, instr) => {
            RIP = new_RIP;
            execute(instr)
        },
        None() => {
            fail("Instruction is either not implemented in this model, reserved, or malformed.")
        }
    }
}