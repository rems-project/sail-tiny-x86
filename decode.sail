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

// DECODE: bitfield to easily access fields within the REX prefix
bitfield REX: bits(8) = {
    W: 3,
    R: 2,
    X: 1,
    B: 0
}

// DECODE: struct to store the implications of the decoded prefixes
struct decodedPrefixes = {
    lock: bool, // encoding is F0 (hex)
    op_size_override: bool, // encoding is 66 (hex)
    addr_size_override: bool, // encoding is 67 (hex)
    mandatory_prefix_66H: bool, // encoding is 66 (hex) + must occur right before opcode or REX prefix
    REX: REX // encoding is 0100WRXB (binary) + must occur right before opcode
}

// DECODE: types of addressing method used to represent operands
enum addressingMethod = { 
    addressingMethod_E, 
    addressingMethod_G
}

/*------------------------------------------------------------------------------
 * DECODE
 *-----------------------------------------------------------------------------*/

/* decode prefixes */

// resets a prefix implication if the corresponding prefix had to be at the end for the implication to hold
// REX prefix is only used if it is the last prefix to occur
// 66H is only counted as a mandatory prefix if it is the last prefix (other than REX) to occur
val reset_prefixes_not_at_end: decodedPrefixes -> decodedPrefixes
function reset_prefixes_not_at_end(decodedPrefixes) = {
    {decodedPrefixes with mandatory_prefix_66H = false, REX = struct {bits = 0x00}}
}

// function to decode prefixes and return their implications
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
    decode_prefix_inner(instruction_ptr, 0, decoded_prefixes, 0x00)
}

struct optionalInstructionParts = {
    modRM_byte: bool, // existence depends on opcode's corresponding addressing method
    SIB_byte: bool, // existence depends on contents of the ModR/M byte. If no ModR/M byte, this doesn't exist.
    displacement_bytes: {0,1,2,4,8}, // existence and size depends on contents of the ModR/M byte. If no ModR/M byte, this doesn't exist.
    immediate_bytes: {0,1,2,4,8} // existence depends on the opcode, size depends on opcode or prefix
}

bitfield modRMByte: bits(8) = {
    Mod: 7 .. 6,
    REG: 5 .. 3,
    RM: 2 .. 0,
}

bitfield SIBByte: bits(8) = {
    Scale: 7 .. 6,
    Index: 5 .. 3,
    Base: 2 .. 0
}

val decode_sib_byte: forall 'wsize, 'wsize in {8, 16, 32, 64}. (SIBByte, int('wsize)) -> bits('wsize)
function decode_sib_byte(sib_byte, wsize) = {
    let base = if unsigned(sib_byte[Base]) == 5 then sail_zero_extend(0x0, wsize) else {
        let reg_index = unsigned(sib_byte[Base]) in
        read_GPR(wsize, reg_index)
    };
    let index = if unsigned(sib_byte[Index]) == 5 then sail_zero_extend(0x0, wsize) else {
        let reg_index = unsigned(sib_byte[Index]) in
        read_GPR(wsize, reg_index)
    };
    add_bits(base, sail_shiftleft(index, unsigned(sib_byte[Scale])))
}

// function to decode single r/m operand
// returns the new read offset and the operand
val decode_rm_operand: (addressingMethod, bits(64), int, modRMByte, word_size) -> (int, rm_operand)
scattered function decode_rm_operand // MY DEFINITIONS FOR THIS MIGHT BE WRONG

function clause decode_rm_operand(addressingMethod_E, instruction_ptr, read_offset, mod_rm_byte, wsize) = {
    let reg_used: range(0,7) = unsigned(mod_rm_byte[RM]);
    if mod_rm_byte[Mod] == 0b11 then 
        (read_offset, rm_REG(reg_used))
    else {
        var new_read_offset: int = read_offset;
        var working_val = {
            if reg_used == 4 then {
                // decode SIB byte, then return here with SIB value
                // increment read_offset (add 1 to it)
                let sib_value = 
                let sib_byte: SIBByte = struct {bits = read_memory(1, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor())} in
                decode_sib_byte(sib_byte, wsize);
                new_read_offset = new_read_offset + 1;
                sib_value
            }
            else read_GPR(wsize, reg_used)
        };
        match mod_rm_byte[Mod] {
            0b01 => {
                // 8 bit displacement 
                let displacement = read_memory(1, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor());
                working_val = add_bits(working_val, sail_sign_extend(displacement, wsize));
                new_read_offset = new_read_offset + 1;
            },
            0b10 => {
                // wsize bit displacement
                let wsize_bytes = if wsize >= 32 then 32 / 8 else wsize / 8;
                assert(wsize_bytes > 0); // required for type-checking
                assert(wsize >= 8 * wsize_bytes);
                let displacement = read_memory(wsize_bytes, instruction_ptr + new_read_offset, create_iFetchAccessDescriptor());
                working_val = add_bits(working_val, sail_sign_extend(displacement, wsize));
                new_read_offset = new_read_offset + wsize_bytes;
            },
            _ => ()
        };
        let final_val = sail_sign_extend(working_val, 64) in
        (new_read_offset, rm_MEM(final_val))
    }
}

function clause decode_rm_operand(addressingMethod_G, instruction_ptr, read_offset, mod_rm_byte, wsize) = {
    let reg_index = unsigned(mod_rm_byte[REG]) in
    (read_offset, rm_REG(reg_index))
}

// function to decode operands
// returns the new read offset, operand1, and operand2
val decode_2_operands: (bits(64), int, addressingMethod, word_size, addressingMethod, word_size) -> (int, rm_operand, rmi_operand)
function decode_2_operands(instruction_ptr, read_offset, addressing_method_1, wsize_1, addressing_method_2, wsize_2) = {
    let mod_rm_byte: modRMByte = {
        let mod_rm_byte_contents = 
        read_memory(1, instruction_ptr + read_offset, create_iFetchAccessDescriptor()) in
        struct {bits = mod_rm_byte_contents}
    };
    let offset = read_offset + 1;
    let (offset1, operand1) = decode_rm_operand(addressing_method_1, instruction_ptr, offset, mod_rm_byte, wsize_1);
    let (offset2, working_operand2) = decode_rm_operand(addressing_method_2, instruction_ptr, offset1, mod_rm_byte, wsize_2);
    let operand2: rmi_operand = match working_operand2 {
        rm_REG(value) => rmi_REG(value),
        rm_MEM(value) => rmi_MEM(value)
    };
    (offset2, operand1, operand2)
}

val decode_one_byte_instruction: (bits(8), bits(64), int, decodedPrefixes) -> option((int, ast))
scattered function decode_one_byte_instruction

// function to decode the instruction opcode
// returns the new read offset, an incomplete AST entry, and a struct of optional instruction parts we now know to exist
val decode_instruction: (bits(64), int, decodedPrefixes) -> option((int, ast))
function decode_instruction(instruction_ptr, read_offset, decoded_prefixes) = {
    // try one byte, then two byte, then three byte opcode
    // try one byte decode
    let one_byte_opcode = read_memory(1, instruction_ptr + read_offset, create_iFetchAccessDescriptor());
    let res = decode_one_byte_instruction(one_byte_opcode, instruction_ptr, read_offset, decoded_prefixes);
    res
}

val decode: bits(64) -> (bits(64), ast)
function decode(instruction_ptr) = {
    var read_offset: int = 0;
    var decoded_prefixes: decodedPrefixes = struct { 
        lock = false, 
        op_size_override = false, 
        addr_size_override = false,
        mandatory_prefix_66H = false,
        REX = struct {bits = 0x00}
    };

    /* decode prefix */
    (read_offset, decoded_prefixes) = decode_prefix(instruction_ptr, decoded_prefixes);

    // TODO: decode instruction
    let res = decode_instruction(instruction_ptr, read_offset, decoded_prefixes);
    match res {
        None() => {
            fail("Invalid instruction");
            (instruction_ptr, LEAVE())
        },
        Some(int, ast) => (instruction_ptr + int, ast)
    }
}

/*
decode -> decode_prefix + decode_instruction*
decode_instruction -> decodes opcode + decode_operands*
decode_operands -> decode_non_immediate* (if opcode says modr/m exists) + decode_immediate
decode_non_immediate -> decode modr/m byte + decode sib byte (if modr/m says it exists) + decode displacement (if modr/, says it exists)
*/