union ast = {
    // Structure of all possible executable instructions
    // if a type contains 2 operands, the first operand is dest and the second is src, unless the instruction is CMP
    MOV: (word_size, rm_operand, rmi_operand),
    XOR: (bool, word_size, rm_operand, rmi_operand),
    SFENCE: unit,
    LFENCE: unit,
    MFENCE: unit,
    CMP: (word_size, rm_operand, rmi_operand),
    PUSH: (word_size, rmi_operand), // only allowing 64 bit operand
    POP: (word_size, rm_operand),
    ADD: (bool, word_size, rm_operand, rmi_operand),
    SUB: (bool, word_size, rm_operand, rmi_operand),
    IMUL: (word_size, reg_index, rm_operand), // IMUL with only 2 arguments (dest and src)
    CALL: imm32,
    LEAVE: unit,
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
    addr_size_override: bool, // encoding is 67 (hex)
    mandatory_prefix_66H: bool, // encoding is 66 (hex) + must occur right before opcode or REX prefix
    REX: REX // encoding is 0100WRXB (binary) + must occur right before opcode
}

// types of addressing method used to represent operands
enum addressingMethod = { 
    addressingMethod_E, 
    addressingMethod_G
}

struct decodeOperandType = {
    addressing_method: addressingMethod,
    wsize: word_size
}

/*------------------------------------------------------------------------------
 * DECODE Functions
 *-----------------------------------------------------------------------------*/

/*
 The rough plan (not yet fully implemented):
    decode -> decode_prefix + decode_instruction*
    decode_instruction -> decodes opcode + decode_operands*
    decode_operands -> decode_non_immediate* (if opcode says modr/m exists) + decode_immediate
    decode_non_immediate -> decode modr/m byte + decode sib byte (if modr/m says it exists) + decode displacement (if modr/, says it exists)
*/

/*------------------------------------------------------------------------------
 * DECODE Prefix
 *-----------------------------------------------------------------------------*/

// resets a prefix if it is ignored when not the last prefix
val reset_prefixes_not_at_end: decodedPrefixes -> decodedPrefixes
function reset_prefixes_not_at_end(decodedPrefixes) = {
    {decodedPrefixes with 
        // 66H is only counted as a mandatory prefix if it is the last prefix (other than REX) to occur
        mandatory_prefix_66H = false, 
        // REX prefix is only used if it is the last prefix to occur
        REX = struct {bits = 0x00}
    }
}

// function to decode prefixes
val decode_prefix_inner: (bits(64), int, decodedPrefixes, bits(8)) -> (int, decodedPrefixes)
function decode_prefix_inner(instruction_ptr, read_offset, decoded_prefixes, prev_prefix) = {
    // read next potential prefix
    let next_prefix: bits(8) = read_memory(1, instruction_ptr + read_offset, create_iFetchAccessDescriptor());

    // if we have a lock prefix
    if next_prefix == 0xF0 then {
        // (reset placement-dependent prefixes)
        let reset_decoded_prefixes = reset_prefixes_not_at_end(decoded_prefixes) in
        // set lock to true
        let new_decoded_prefixes = {reset_decoded_prefixes with lock = true} in
        // check for more prefixes
            decode_prefix_inner(instruction_ptr, read_offset + 1, new_decoded_prefixes, next_prefix)
    }
    // if we have a operand size override (to 16 bits) / potential mandatory prefix, 
    else if next_prefix == 0x66 then {
        // (reset placement-dependent prefixes)
        let reset_decoded_prefixes = reset_prefixes_not_at_end(decoded_prefixes) in
        // set the corresponding fields to true
        let new_decoded_prefixes = {reset_decoded_prefixes with op_size_override = true, mandatory_prefix_66H = true} in
        // check for more prefixes
            decode_prefix_inner(instruction_ptr, read_offset + 1, new_decoded_prefixes, next_prefix)
    }
    // if we have a address size override (to 16 bits) prefix
    else if next_prefix == 0x67 then {
        // (reset placement-dependent prefixes)
        let reset_decoded_prefixes = reset_prefixes_not_at_end(decoded_prefixes) in
        // set addr_size_override to true
        let new_decoded_prefixes = {reset_decoded_prefixes with addr_size_override = true} in
        // heck for more prefixes
            decode_prefix_inner(instruction_ptr, read_offset + 1, new_decoded_prefixes, next_prefix)
    }
    // if we have a REX prefix
    else if next_prefix[7 .. 4] == 0x4 then {
        // (reset placement-dependent prefixes if necessary)
        let reset_decoded_prefixes = (if prev_prefix == 0x66 then decoded_prefixes else reset_prefixes_not_at_end(decoded_prefixes)) in
        // set the REX field according to the prefix's value
        let rex_contents: REX = struct{bits = next_prefix} in
        let new_decoded_prefixes = {reset_decoded_prefixes with REX = rex_contents} in
        // check for more prefixes
            decode_prefix_inner(instruction_ptr, read_offset + 1, new_decoded_prefixes, next_prefix)
    }
    else {
        // return the result of decoding all the prefixes, as there are no more potential prefixes to check
        (read_offset, decoded_prefixes)
    }
}

// wrapper function to decode the prefixes of an instruction
val decode_prefix: (bits(64), decodedPrefixes) -> (int, decodedPrefixes)
function decode_prefix(instruction_ptr, decoded_prefixes) = {
    let (read_offset, decoded_prefixes) = decode_prefix_inner(instruction_ptr, 0, decoded_prefixes, 0x00);
    if decoded_prefixes.REX[W] == 0b1 then {
        // If the REX prefix was the last prefix before the opcode (i.e. REX is not ignored / reset), and REX[W] is set
        // then the op_size_override prefix is ignored / reset
        (read_offset, {decoded_prefixes with op_size_override = false})
    }
    else (read_offset, decoded_prefixes)
}

/*------------------------------------------------------------------------------
 * DECODE SIB byte (sometimes needed for decoding register or memory operands)
 *-----------------------------------------------------------------------------*/

val decode_sib_byte: forall 'wsize, 'wsize in {8, 16, 32, 64}. (SIBByte, int('wsize)) -> bits('wsize)
function decode_sib_byte(sib_byte, wsize) = {
    // value stored in the SIB byte is base + index * (2^scale)
    /* Note: if the value stored in the base or index fields of the SIB byte is 5, 
    then we can't read the value stored in this register location, as the index is of the RBP,*/

    let base = if unsigned(sib_byte[Base]) == 5 then sail_zero_extend(0x0, wsize) else {
        // read the register location stored in the base field of the SIB byte
        let reg_index = unsigned(sib_byte[Base]) in
        // base = value stored in this register location
        read_GPR(wsize, reg_index)
    };
    let index = if unsigned(sib_byte[Index]) == 5 then sail_zero_extend(0x0, wsize) else {
        // read the register location stored in the index field of the SIB byte
        let reg_index = unsigned(sib_byte[Index]) in
        // index = value stored in this register location
        read_GPR(wsize, reg_index)
    };
    // return the value stored in the SIB byte, which is base + index * (2^scale)
    add_bits(base, sail_shiftleft(index, unsigned(sib_byte[Scale])))
}

/*------------------------------------------------------------------------------
 * DECODE Register or Memory operands
 *-----------------------------------------------------------------------------*/

// function to decode single r/m operand
// returns the new read offset and the operand
val decode_rm_operand: (addressingMethod, bits(64), int, modRMByte, word_size) -> (int, rm_operand)
scattered function decode_rm_operand

/* function definition for addressing method E:
 of the mod r/m byte, the mod bits and r/m bits determine the operand */
function clause decode_rm_operand(addressingMethod_E, instruction_ptr, read_offset, mod_rm_byte, wsize) = {
    // read r/m bits (returns register index)
    let reg_used: range(0,7) = unsigned(mod_rm_byte[RM]);
    if mod_rm_byte[Mod] == 0b11 then 
        // the r/m bits specify the register index of the operand
        (read_offset, rm_REG(reg_used))
    else {
        // the mod and r/m bits are used to specify a memory location
        var new_read_offset: int = read_offset;
        var working_val = {
            if reg_used == 4 then {
                // decode SIB byte
                let sib_value = 
                let sib_byte: SIBByte = struct {
                    bits = read_memory(1, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor())
                } in
                decode_sib_byte(sib_byte, wsize);
                // increment read_offset (add 1 to it)
                new_read_offset = new_read_offset + 1;
                // working value is set to the value stored in the SIB byte
                sib_value
            }
            else read_GPR(wsize, reg_used) // working value is set to the value stored in the register index we read earlier
        };
        match mod_rm_byte[Mod] {
            0b01 => {
                // we need to add an 8 bit displacement value to our working value
                // fetch the 8 bit displacement
                let displacement = read_memory(1, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor());
                // add it to our working value
                working_val = add_bits(working_val, sail_sign_extend(displacement, wsize));
                // increment read offset
                new_read_offset = new_read_offset + 1;
            },
            0b10 => {
                // we need to add a wsize bit displacement to our working value. 
                // But if wsize is 64, then our displacement is a sign-extended 32-bit displacement
                let wsize_bytes = if wsize >= 32 then 32 / 8 else wsize / 8;
                assert(wsize_bytes > 0 & wsize >= 8 * wsize_bytes); // required for type-checking because of the wsize = 64 case
                // fetch the displacement
                let displacement = read_memory(wsize_bytes, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor());
                // add it to our working value
                working_val = add_bits(working_val, sail_sign_extend(displacement, wsize));
                // increment read offset
                new_read_offset = new_read_offset + wsize_bytes;
            },
            // if our mod bits are 00, then we don't add a displacement to our working value
            // this match statement is not reachable for mod bits = 11
            _ => () 
        };
        // zero-extend to 64 bits to get a valid memory address in 64-bit mode
        let final_val = sail_zero_extend(working_val, 64) in
        // return the new read offset and decoded operand
        (new_read_offset, rm_MEM(final_val))
    }
}

/* function definition for addressing method E:
 of the mod r/m byte, the reg bits determine the register index of the operand */
function clause decode_rm_operand(addressingMethod_G, instruction_ptr, read_offset, mod_rm_byte, wsize) = {
    // read reg bits of the mod r/m byte
    let reg_index = unsigned(mod_rm_byte[REG]) in
    // return the read offset and decoded operand
    (read_offset, rm_REG(reg_index))
}

// function to decode 2 register or memory operands
// returns the new read offset, operand1, and operand2
val decode_2_rm_operands: (bits(64), int, decodeOperandType, decodeOperandType) -> (int, rm_operand, rmi_operand)
function decode_2_rm_operands(instruction_ptr, read_offset, operand1_type, operand2_type) = {
    let mod_rm_byte: modRMByte = {
        let mod_rm_byte_contents = 
        read_memory(1, instruction_ptr + read_offset, create_iFetchAccessDescriptor()) in
        struct {bits = mod_rm_byte_contents}
    };
    let new_offset = read_offset + 1;
    let (new_offset2, operand1) = decode_rm_operand(operand1_type.addressing_method, instruction_ptr, new_offset, mod_rm_byte, operand1_type.wsize);
    let (new_offset3, working_operand2) = decode_rm_operand(operand2_type.addressing_method, instruction_ptr, new_offset2, mod_rm_byte, operand2_type.wsize);
    let operand2: rmi_operand = match working_operand2 {
        rm_REG(value) => rmi_REG(value),
        rm_MEM(value) => rmi_MEM(value)
    };
    (new_offset3, operand1, operand2)
}

/*------------------------------------------------------------------------------
 * DECODE Instruction
 *-----------------------------------------------------------------------------*/

// function to decode one byte instructions. Function definitions are inlined with corresponding execute definitions
val decode_one_byte_instruction: (bits(8), bits(64), int, decodedPrefixes) -> option((int, ast))
scattered function decode_one_byte_instruction

// function to decode the main instruction
// returns the new read offset, an incomplete AST entry, and a struct of optional instruction parts we now know to exist
val decode_instruction: (bits(64), int, decodedPrefixes) -> option((int, ast))
function decode_instruction(instruction_ptr, read_offset, decoded_prefixes) = {
    /* decode the opcode */
    // first try one byte decode
    // fetch the first opcode byte from memory
    let one_byte_opcode = read_memory(1, instruction_ptr + read_offset, create_iFetchAccessDescriptor());
    // increment read_offset
    let new_read_offset = read_offset + 1;
    // try to decode the opcode and findd the instruction operands
    let res = decode_one_byte_instruction(one_byte_opcode, instruction_ptr, new_read_offset, decoded_prefixes);
    res
}

// base decode function: decode the prefix and then the main instruction
val decode: bits(64) -> (bits(64), ast)
function decode(instruction_ptr) = {
    // keep a counter of how many bytes of the instruction we have read so far
    var read_offset: int = 0;
    // keep a struct of which prefixes the instruction has
    var decoded_prefixes: decodedPrefixes = struct { 
        lock = false, 
        op_size_override = false, 
        addr_size_override = false,
        mandatory_prefix_66H = false,
        REX = struct {bits = 0x00}
    };

    // decode prefix
    (read_offset, decoded_prefixes) = decode_prefix(instruction_ptr, decoded_prefixes);

    // decode rest of instruction
    let res = decode_instruction(instruction_ptr, read_offset, decoded_prefixes);
    match res {
        None() => {
            fail("Invalid instruction");
            (instruction_ptr, LEAVE())
        },
        Some(offset, instruction) => {
            if offset > 15 then fail("Instruction is longer than 15 bytes, hence is not valid");
            (instruction_ptr + offset, instruction)
        }
    }
}
