val fail_if_two_mem_operands : (rm_operand, rmi_operand, string) -> unit
function fail_if_two_mem_operands(dest, src, operation) = {
    let error_message = concat_str(operation, " operation cannot occur between 2 memory locations");
    match (dest, src) {
        (rm_MEM(_), rmi_MEM(_)) => fail(error_message),
        (_,_) => ()
    }
}

val fail_if_lock : (bool, string) -> unit
function fail_if_lock(lock, operation) = {
    let error_message = concat_str(
        "Exception #UD — Invalid Opcode (Undefined Opcode): ",
        concat_str(operation, " instruction does not support the LOCK prefix")
    );
    if lock then 
        fail(error_message)
    else ()
}



/*------------------------------------------------------------------------------
 * MOV
 *-----------------------------------------------------------------------------*/

function clause execute(MOV(operand_size, dest, src)) = {
    // MOV cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "MOV");
    // MOV operation cannot be executed on dest = mem64 and src = imm64
    match (dest, src) {
        (rm_MEM(_), rmi_IMM(IMM64(_))) => fail("MOV operation cannot be executed on dest = mem64 and src = imm64"),
        (_,_) => ()
    };

    // execute MOV instruction
    let val_to_write = read_operand(operand_size, src);
    write_operand(operand_size, dest, val_to_write)
}

// Decode MOV r/m8 r8
function clause decode_one_byte_instruction(0x88, instruction_ptr, read_offset, decoded_prefixes) = {
    // MOV does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "MOV");
    // get 2 operands of the addressing method + operand type: Operand 1 = Eb, Operand 2 = Gb
    let (new_read_offset, operand1, operand2) = get_Eb_Gb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    // return new read offset and decoded instruction
    Some(new_read_offset, MOV(8, operand1, operand2))
}

// Decode MOV r/m{16, 32, 64}, r{16, 32, 64}
function clause decode_one_byte_instruction(0x89, instruction_ptr, read_offset, decoded_prefixes) = {
    // MOV does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "MOV");
    // get 2 operands of the addressing method + operand type: Operand 1 = Ev, Operand 2 = Gv
    let (new_read_offset, operand_size, operand1, operand2) = get_Ev_Gv_operands(instruction_ptr, read_offset, decoded_prefixes);
    // return new read offset and decoded instruction
    Some(new_read_offset, MOV(operand_size, operand1, operand2))
}

// Decode MOV r8, r/m8
function clause decode_one_byte_instruction(0x8A, instruction_ptr, read_offset, decoded_prefixes) = {
    // MOV does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "MOV");
    // get 2 operands of the addressing method + operand type: Operand 1 = Gb, Operand 2 = Eb
    let (new_read_offset, operand1, operand2) = get_Gb_Eb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    // return new read offset and decoded instruction
    Some(new_read_offset, MOV(8, operand1, operand2))
}

// Decode MOV r{16, 32, 64}, r/m{16, 32, 64}
function clause decode_one_byte_instruction(0x8B, instruction_ptr, read_offset, decoded_prefixes) = {
    // MOV does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "MOV");
    // get 2 operands of the addressing method + operand type: Operand 1 = Gv, Operand 2 = Ev
    let (new_read_offset, operand_size, operand1, operand2) = get_Gv_Ev_operands(instruction_ptr, read_offset, decoded_prefixes);
    // return new read offset and decoded instruction
    Some(new_read_offset, MOV(operand_size, operand1, operand2))
}

// Decode MOV r{8, 16, 32, 64} imm{8, 16, 32, 64}
function clause decode_one_byte_instruction(0xB @ not_8_bit: bits(1) @ reg_field, instruction_ptr, read_offset, decoded_prefixes) = {
    // MOV does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "MOV");
    // get register location embedded in the opcode
    let reg_index = get_reg_value_in_opcode_byte(reg_field, decoded_prefixes.REX);
    let reg = 
        if not_8_bit == 0b1 then
            REG_NORMAL(reg_index)
        else
            wrap_reg(reg_index, 8, decoded_prefixes.REX);
    // Get operand_size. 
    let operand_size = 
        if not_8_bit == 0b1 then
            // Default is 32 bits.
            get_operand_size_using_REX(decoded_prefixes, 32)
        else
            8;
    // get imm operand
    let (new_read_offset, imm) = read_imm_operand(instruction_ptr, read_offset, operand_size);
    // return new read offset and decoded instruction
    Some(new_read_offset, MOV(operand_size, rm_REG(reg), rmi_IMM(imm)))
}

// Decode MOV r/m{8, 16, 32, 64} imm{8, 16, 32, 32}
/* WARNING: Opcodes C6 (r/m8 imm8) and C7 (all others) encode a group of instructions. 
The exact instruction encoded is specified in the reg field of the mod r/m byte.
Out of all instructions with opcodes C6 and C7, we currently only support the MOV instruction. */
function clause decode_one_byte_instruction(0b1100_110 @ not_8_bit, instruction_ptr, read_offset, decoded_prefixes) = {
    // fetch mod r/m byte
    let (read_offset_2, mod_rm_byte) = read_mod_rm_byte(instruction_ptr, read_offset);

    // If the opcode extension does not point to a MOV instruction then fail
    if unsigned(mod_rm_byte[REG]) != 0 then fail("The instruction to be decoded is either reserved or not implemented in this model");

    // MOV does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "MOV");

    // Get operands
    let (new_read_offset, operand_size, operand1, imm) = {
        if not_8_bit == 0b1 then
            // Get 2 operands of the addressing method + operand type: Operand 1 = Ev, Operand 2 = Iz
            get_Ev_Iz_operands(instruction_ptr, read_offset, decoded_prefixes, mod_rm_byte)
        else {
            // Get 2 operands of the addressing method + operand type: Operand 1 = Eb, Operand 2 = Ib
            let (new_read_offset, operand1, imm) = get_Eb_Ib_operands(instruction_ptr, read_offset, decoded_prefixes.REX, mod_rm_byte);
            (new_read_offset, 8, operand1, imm)
        }
    };

    // return new read offset and decoded instruction
    Some(new_read_offset, MOV(operand_size, operand1, rmi_IMM(imm)))
}



/*------------------------------------------------------------------------------
 * XOR
 *-----------------------------------------------------------------------------*/

function clause execute(XOR(lock, operand_size, dest, src)) = {
    // XOR cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "XOR");
    // For operation XOR, src = imm64 is not a valid operand 
    match src {
        rmi_IMM(IMM64(_)) => fail("For operation XOR, src = imm64 is not a valid operand"),
        _ => ()
    };
    // XOR is not valid with lock = true if dest is a register location
    match dest {
        rm_REG(_) if lock => fail("Exception #UD — Invalid Opcode (Undefined Opcode): LOCK prefix cannot be applied to dest = reg"),
        _ => ()
    };

    // execute XOR instruction
    let dest_val = read_operand(lock, operand_size, dest);
    let src_val = read_operand(false, operand_size, src);
    let result = xor_vec(dest_val, src_val);
    write_operand(lock, operand_size, dest, result);

    /* change value of status flags */
    // clear overflow and carry flag
    RFLAGS[OF] = 0b0;
    RFLAGS[CF] = 0b0;
    // assign values to other flags (but not AF as its value is undefined for XOR)
    update_sign_flag(result);
    update_zero_flag(result);
    update_parity_flag(result);
}

// Decode XOR r/m8, r8
function clause decode_one_byte_instruction(0x30, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Eb, Operand 2 = Gb
    let (new_read_offset, operand1, operand2) = get_Eb_Gb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    // return new read offset and decoded instruction
    Some(new_read_offset, XOR(decoded_prefixes.lock, 8, operand1, operand2))
}

// Decode XOR r/m{16, 32, 64}, r{16, 32, 64}
function clause decode_one_byte_instruction(0x31, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Ev, Operand 2 = Gv
    let (new_read_offset, operand_size, operand1, operand2) = get_Ev_Gv_operands(instruction_ptr, read_offset, decoded_prefixes);
    // return new read offset and decoded instruction
    Some(new_read_offset, XOR(decoded_prefixes.lock, operand_size, operand1, operand2))
}

// Decode XOR r8, r/m8
function clause decode_one_byte_instruction(0x32, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Gb, Operand 2 = Eb
    let (new_read_offset, operand1, operand2) = get_Gb_Eb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    // return new read offset and decoded instruction
    Some(new_read_offset, XOR(decoded_prefixes.lock, 8, operand1, operand2))
}

// Decode XOR r{16, 32, 64}, r/m{16, 32, 64}
function clause decode_one_byte_instruction(0x33, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Gv, Operand 2 = Ev
    let (new_read_offset, operand_size, operand1, operand2) = get_Gv_Ev_operands(instruction_ptr, read_offset, decoded_prefixes);
    // return new read offset and decoded instruction
    Some(new_read_offset, XOR(decoded_prefixes.lock, operand_size, operand1, operand2))
}

// Decode XOR, ADD, SUB, CMP r/m{8, 16, 32, 64} imm{8, 16, 32, 32}
/* WARNING: Opcodes 80 (r/m8 imm8) and 81 (all others) encode a group of instructions. 
The exact instruction encoded is specified in the reg field of the mod r/m byte.
Out of all instructions with opcodes 80 and 81, we currently only support the ADD, SUB, XOR and CMP instructions. */
function clause decode_one_byte_instruction(0b1000_000 @ not_8_bit, instruction_ptr, read_offset, decoded_prefixes) = {
    // fetch mod r/m byte
    let (read_offset, mod_rm_byte) = read_mod_rm_byte(instruction_ptr, read_offset);

    // get operands
    let (new_read_offset, operand_size, operand1, imm) = {
        if not_8_bit == 0b1 then
            // Get 2 operands of the addressing method + operand type: Operand 1 = Ev, Operand 2 = Iz
            get_Ev_Iz_operands(instruction_ptr, read_offset, decoded_prefixes, mod_rm_byte)
        else {
            // Get 2 operands of the addressing method + operand type: Operand 1 = Eb, Operand 2 = Ib
            let (new_read_offset, operand1, imm) = get_Eb_Ib_operands(instruction_ptr, read_offset, decoded_prefixes.REX, mod_rm_byte);
            (new_read_offset, 8, operand1, imm)
        }
    };
    
    // Match to instruction based on opcode extension.
    // Return new read offset and decoded instruction
    match unsigned(mod_rm_byte[REG]) {
        0 => Some(new_read_offset, ADD(decoded_prefixes.lock, operand_size, operand1, rmi_IMM(imm))),
        5 => Some(new_read_offset, SUB(decoded_prefixes.lock, operand_size, operand1, rmi_IMM(imm))),
        6 => Some(new_read_offset, XOR(decoded_prefixes.lock, operand_size, operand1, rmi_IMM(imm))),
        7 => {
            // CMP does not support the lock prefix
            fail_if_lock(decoded_prefixes.lock, "CMP");
            Some(new_read_offset, CMP(operand_size, operand1, rmi_IMM(imm)))
        },
        _ => {
            fail("The instruction to be decoded is not implemented in this model")
        }
    }
}



/*------------------------------------------------------------------------------
 * FENCE instructions
 *-----------------------------------------------------------------------------*/

// Wait_On_Following_Stores_Until(preceding_stores_globally_visible);
function clause execute(SFENCE()) = {
    // apply barrier
    sail_barrier(Barrier_SFENCE)
}

// Wait_On_Following_Instructions_Until(preceding_instructions_complete);
function clause execute(LFENCE()) = {
    // apply barrier
    sail_barrier(Barrier_LFENCE)
}

// Wait_On_Following_Loads_And_Stores_Until(preceding_loads_and_stores_globally_visible);
function clause execute(MFENCE()) = {
    // apply barrier
    sail_barrier(Barrier_MFENCE)
}

// Decode SFENCE, LFENCE and MFENCE instructions
function clause decode_two_byte_instruction(0x0FAE, instruction_ptr, read_offset, decoded_prefixes) = {
    // FENCEs do not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "FENCE");

    // get opcode extension (located in mod r/m byte)
    let (new_read_offset, mod_rm_byte) = read_mod_rm_byte(instruction_ptr, read_offset);

    if mod_rm_byte[Mod] == 0b11 then {
        match mod_rm_byte[REG] {
            0b111 => {
                // SFENCE
                // Use of 66 / F2 / F3 prefixes are not allowed in the instruction. Only prefix 66 has been implemented in this model.
                if decoded_prefixes.op_size_override then 
                    fail("Prefix 66H is not allowed in the SFENCE instruction")
                else
                    Some(new_read_offset, SFENCE())
            },
            0b101 => {
                // LFENCE
                // Use of 66 / F2 / F3 prefixes are not allowed in the instruction. Only prefix 66 has been implemented in this model.
                if decoded_prefixes.op_size_override then 
                    fail("Prefix 66H is not allowed in the LFENCE instruction")
                else
                    Some(new_read_offset, LFENCE())
            },
            0b110 => {
                // MFENCE
                // Use of 66 / F2 / F3 prefixes are not allowed in the instruction. Only prefix 66 has been implemented in this model.
                if decoded_prefixes.op_size_override then 
                    fail("Prefix 66H is not allowed in the MFENCE instruction")
                else
                    Some(new_read_offset, MFENCE())
            },
            _ => {
                fail("This instruction decode is either reserved or not implemented in this model")
            }
        }
    }
    else {
        fail("This instruction decode is not implemented in this model")
    }
}



/*------------------------------------------------------------------------------
 * CMP
 *-----------------------------------------------------------------------------*/

function clause execute(CMP(operand_size, first, second)) = {
    // CMP cannot occur between first = memory location and second = memory location
    fail_if_two_mem_operands(first, second, "CMP");
    // For operation CMP, second = imm64 is not a valid operand 
    match second {
        rmi_IMM(IMM64(_)) => fail("For operation CMP, second = imm64 is not a valid operand"),
        _ => ()
    };

    // execute CMP instruction
    let first_val = read_operand(operand_size, first);
    let second_val = read_operand(operand_size, second);
    let result = sub_bits(first_val, second_val);

    /* change value of status flags. Equivalent to the changes made on executing the SUB instruction. */
    update_RFLAGS_sub(first_val, second_val, result);
}

// Decode CMP r/m8, r8
function clause decode_one_byte_instruction(0x38, instruction_ptr, read_offset, decoded_prefixes) = {
    // CMP does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "CMP");

    // addressing method + operand type: Eb, Gb
    let (new_read_offset, operand1, operand2) = 
        get_Eb_Gb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    Some(new_read_offset, CMP(8, operand1, operand2))
}

// Decode CMP r/m{16, 32, 64}, r{16, 32, 64}
function clause decode_one_byte_instruction(0x39, instruction_ptr, read_offset, decoded_prefixes) = {
    // CMP does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "CMP");

    // addressing method + operand type: Ev, Gv
    let (new_read_offset, operand_size, operand1, operand2) = 
        get_Ev_Gv_operands(instruction_ptr, read_offset, decoded_prefixes);
    Some(new_read_offset, CMP(operand_size, operand1, operand2))
}

// Decode CMP r8, r/m8
function clause decode_one_byte_instruction(0x3A, instruction_ptr, read_offset, decoded_prefixes) = {
    // CMP does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "CMP");

    // addressing method + operand type: Gb, Eb
    let (new_read_offset, operand1, operand2) = 
        get_Gb_Eb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    Some(new_read_offset, CMP(8, operand1, operand2))
}

// Decode CMP r{16, 32, 64}, r/m{16, 32, 64}
function clause decode_one_byte_instruction(0x3B, instruction_ptr, read_offset, decoded_prefixes) = {
    // CMP does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "CMP");

    // addressing method + operand type: Gv, Ev
    let (new_read_offset, operand_size, operand1, operand2) = 
        get_Gv_Ev_operands(instruction_ptr, read_offset, decoded_prefixes);
    Some(new_read_offset, CMP(operand_size, operand1, operand2))
}

// Decode CMP r/m{8, 16, 32, 64} imm{8, 16, 32, 32} is located in the XOR section



/*------------------------------------------------------------------------------
 * PUSH
 *-----------------------------------------------------------------------------*/

function clause execute(PUSH(operand_size, src)) = {
    // PUSH instruction does not allow src = imm64, reg8 or mem8
    // and in 64-bit mode, src = reg32 and mem32 are not encodable
    match src {
        rmi_IMM(_) if operand_size == 64 => fail("Operand for PUSH operation not allowed"),
        rmi_REG(_) if operand_size == 8 | operand_size == 32 => fail("Operand for PUSH operation not allowed"),
        rmi_MEM(_) if operand_size == 8 | operand_size == 32 => fail("Operand for PUSH operation not allowed"),
        _ => ()
    };

    // If the source operand is an immediate of size less than the operand size, then sign-extend the value
    // default operand size is 8 bytes = 64 bits
    let src_val = sail_sign_extend(read_operand(operand_size, src), 64);
    // subtract 8 from RSP to point to the new top of the stack
    RSP = sub_bits(RSP, sail_zero_extend(0x8, 64));
    // push the new item to the top of the stack
    let dest_address = rm_MEM(RSP);
    write_operand(64, dest_address, src_val)
}

// Decode PUSH imm8
function clause decode_one_byte_instruction(0x6A, instruction_ptr, read_offset, decoded_prefixes) = {
    // PUSH does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "PUSH");

    // Decode instruction
    let (new_read_offset, imm) = read_imm_operand(instruction_ptr, read_offset, 8);
    Some(new_read_offset, PUSH(8, rmi_IMM(imm)))
}

// Decode PUSH imm{16, 32}
function clause decode_one_byte_instruction(0x68, instruction_ptr, read_offset, decoded_prefixes) = {
    // PUSH does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "PUSH");

    // Get operand size. Default is 32 bits. Ignore REX prefix as we can't have a 64 bit immediate.
    let operand_size = get_operand_size_ignoring_REX(decoded_prefixes, 32);
    // Decode instruction
    let (new_read_offset, imm) = read_imm_operand(instruction_ptr, read_offset, operand_size);
    Some(new_read_offset, PUSH(operand_size, rmi_IMM(imm)))
}

// Decode PUSH r/m{16, 64}
/* WARNING: Opcode FF encodes a group of instructions. The exact instruction encoded is specified in the reg field of the mod r/m byte.
Out of all instructions with opcode FF, we currently only support the PUSH instruction. */
function clause decode_one_byte_instruction(0xFF, instruction_ptr, read_offset, decoded_prefixes) = {
    // fetch mod r/m byte
    let (new_read_offset, mod_rm_byte) = read_mod_rm_byte(instruction_ptr, read_offset);

    // If the opcode extension does not point to a PUSH instruction then fail
    if unsigned(mod_rm_byte[REG]) != 6 then fail("The instruction to be decoded is either reserved or not implemented in this model");
    
    // We have a push instruction (PUSH r/m{16, 64})

    // PUSH does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "PUSH");

    // Decode operand
    let (final_read_offset, operand_size, working_operand) = 
        decode_push_or_pop_rm_operand(instruction_ptr, new_read_offset, decoded_prefixes, mod_rm_byte);

    // Change the operand type from rm_operand to rmi_operand to match the AST
    let operand: rmi_operand = match working_operand {
        rm_REG(contents) => rmi_REG(contents),
        rm_MEM(contents) => rmi_MEM(contents)
    };

    // return decoded instruction
    Some(final_read_offset, PUSH(operand_size,operand))
}

// Decode PUSH r{16, 64} and POP r{16, 64}
function clause decode_one_byte_instruction(0x5 @ is_pop: bits(1) @ reg_field: bits(3), instruction_ptr, read_offset, decoded_prefixes) = {
    // get register location embedded in the opcode
    let reg_index = get_reg_value_in_opcode_byte(reg_field, decoded_prefixes.REX);
    let reg = REG_NORMAL(reg_index);
    // get operand size. For PUSH, the default operand size is 64 bits. Ignore REX prefix
    let operand_size = get_operand_size_ignoring_REX(decoded_prefixes, 64);

    if is_pop == 0b0 then {
        // PUSH does not support the lock prefix
        fail_if_lock(decoded_prefixes.lock, "PUSH");

        Some(read_offset, PUSH(operand_size, rmi_REG(reg)))
    }
    else {
        // POP does not support the lock prefix
        fail_if_lock(decoded_prefixes.lock, "POP");

        Some(read_offset, POP(operand_size, rm_REG(reg)))
    }
}



/*------------------------------------------------------------------------------
 * POP
 *-----------------------------------------------------------------------------*/

function clause execute(POP(operand_size, dest)) = {
    // POP instruction does not allow dest to be 8 bits long. Due to 64 bit addressing, dest also cannot be 32 bits long.
    // Also not allowing a 16-bit dest in this model for simplicity (to keep the stack aligned)
    if operand_size == 8 | operand_size == 32 then fail("dest size for POP operation not supported");
    if operand_size == 16 then fail("dest size for POP operation not implemented in this model");

    // pop the value at the top of the stack to dest
    let popped_val = read_operand(64, rm_MEM(RSP));
    write_operand(64, dest, popped_val);
    // increment stack pointer to free the popped stack space
    RSP = RSP + 8;
}

// Decode POP r/m{16, 64}
function clause decode_one_byte_instruction(0x8F, instruction_ptr, read_offset, decoded_prefixes) = {
    // POP does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "POP");

    // fetch mod r/m byte
    let (new_read_offset, mod_rm_byte) = read_mod_rm_byte(instruction_ptr, read_offset);
    // If the opcode extension does not point to a PUSH instruction then fail
    if unsigned(mod_rm_byte[REG]) != 0 then fail("The instruction to be decoded is reserved");
    
    // We have a pop instruction (POP r/m{16, 64})
    // Decode operand
    let (final_read_offset, operand_size, operand) = 
        decode_push_or_pop_rm_operand(instruction_ptr, new_read_offset, decoded_prefixes, mod_rm_byte);
    // return decoded instruction
    Some(final_read_offset, POP(operand_size,operand))
}

// Decode POP r{16, 64} is implemented with "Decode PUSH r{16, 64}"



/*------------------------------------------------------------------------------
 * ADD
 *-----------------------------------------------------------------------------*/

function clause execute(ADD(lock, operand_size, dest, src)) = {
    // ADD cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "ADD");
    // For operation ADD, src = imm64 is not a valid operand 
    match src {
        rmi_IMM(IMM64(_)) => fail("For operation ADD, src = imm64 is not a valid operand"),
        _ => ()
    };
    // ADD is not valid with prefix lock = true if dest is a register location
    match dest {
        rm_REG(_) if lock => fail("Exception #UD — Invalid Opcode (Undefined Opcode): LOCK prefix cannot be applied to dest = reg"),
        _ => ()
    };

    // execute ADD instruction
    let dest_val = read_operand(lock, operand_size, dest);
    let src_val = read_operand(false, operand_size, src);
    let result = add_bits(dest_val, src_val);
    write_operand(lock, operand_size, dest, result);

    /* change value of status flags */
    update_RFLAGS_add(dest_val, src_val, result);
}

// Decode ADD r/m8, r8
function clause decode_one_byte_instruction(0x00, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Eb, Operand 2 = Gb
    let (new_read_offset, operand1, operand2) = get_Eb_Gb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    // return new read offset and decoded instruction
    Some(new_read_offset, ADD(decoded_prefixes.lock, 8, operand1, operand2))
}

// Decode ADD r/m{16, 32, 64}, r{16, 32, 64}
function clause decode_one_byte_instruction(0x01, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Ev, Operand 2 = Gv
    let (new_read_offset, operand_size, operand1, operand2) = get_Ev_Gv_operands(instruction_ptr, read_offset, decoded_prefixes);
    // return new read offset and decoded instruction
    Some(new_read_offset, ADD(decoded_prefixes.lock, operand_size, operand1, operand2))
}

// Decode ADD r8, r/m8
function clause decode_one_byte_instruction(0x02, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Gb, Operand 2 = Eb
    let (new_read_offset, operand1, operand2) = get_Gb_Eb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    // return new read offset and decoded instruction
    Some(new_read_offset, ADD(decoded_prefixes.lock, 8, operand1, operand2))
}

// Decode ADD r{16, 32, 64}, r/m{16, 32, 64}
function clause decode_one_byte_instruction(0x03, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Gv, Operand 2 = Ev
    let (new_read_offset, operand_size, operand1, operand2) = get_Gv_Ev_operands(instruction_ptr, read_offset, decoded_prefixes);
    // return new read offset and decoded instruction
    Some(new_read_offset, ADD(decoded_prefixes.lock, operand_size, operand1, operand2))
}

// Decode ADD r/m{8, 16, 32, 64} imm{8, 16, 32, 32} is located in the XOR section



/*------------------------------------------------------------------------------
 * SUB
 *-----------------------------------------------------------------------------*/

function clause execute(SUB(lock, operand_size, dest, src)) = {
    // SUB cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "SUB");
    // For operation SUB, src = imm64 is not a valid operand 
    match src {
        rmi_IMM(IMM64(_)) => fail("For operation SUB, src = imm64 is not a valid operand"),
        _ => ()
    };
    // SUB is not valid with prefix lock = true if dest is a register location
    match dest {
        rm_REG(_) if lock => fail("Exception #UD — Invalid Opcode (Undefined Opcode): LOCK prefix cannot be applied to dest = reg"),
        _ => ()
    };

    // execute SUB instruction
    let dest_val = read_operand(lock, operand_size, dest);
    let src_val = read_operand(false, operand_size, src);
    let result = sub_bits(dest_val, src_val);
    write_operand(lock, operand_size, dest, result);

    /* change value of status flags */
    update_RFLAGS_sub(dest_val, src_val, result);
}

// Decode SUB r/m8, r8
function clause decode_one_byte_instruction(0x28, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Eb, Operand 2 = Gb
    let (new_read_offset, operand1, operand2) = get_Eb_Gb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    // return new read offset and decoded instruction
    Some(new_read_offset, SUB(decoded_prefixes.lock, 8, operand1, operand2))
}

// Decode SUB r/m{16, 32, 64}, r{16, 32, 64}
function clause decode_one_byte_instruction(0x29, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Ev, Operand 2 = Gv
    let (new_read_offset, operand_size, operand1, operand2) = get_Ev_Gv_operands(instruction_ptr, read_offset, decoded_prefixes);
    // return new read offset and decoded instruction
    Some(new_read_offset, SUB(decoded_prefixes.lock, operand_size, operand1, operand2))
}

// Decode SUB r8, r/m8
function clause decode_one_byte_instruction(0x2A, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Gb, Operand 2 = Eb
    let (new_read_offset, operand1, operand2) = get_Gb_Eb_operands(instruction_ptr, read_offset, decoded_prefixes.REX);
    // return new read offset and decoded instruction
    Some(new_read_offset, SUB(decoded_prefixes.lock, 8, operand1, operand2))
}

// Decode SUB r{16, 32, 64}, r/m{16, 32, 64}
function clause decode_one_byte_instruction(0x2B, instruction_ptr, read_offset, decoded_prefixes) = {
    // get 2 operands of the addressing method + operand type: Operand 1 = Gv, Operand 2 = Ev
    let (new_read_offset, operand_size, operand1, operand2) = get_Gv_Ev_operands(instruction_ptr, read_offset, decoded_prefixes);
    // return new read offset and decoded instruction
    Some(new_read_offset, SUB(decoded_prefixes.lock, operand_size, operand1, operand2))
}

// Decode SUB r/m{8, 16, 32, 64} imm{8, 16, 32, 32} is located in the XOR section



/*------------------------------------------------------------------------------
 * IMUL
 *-----------------------------------------------------------------------------*/

function clause execute(IMUL(operand_size, dest, src)) = {
    // IMUL cannot occur between 8 bit operands
    if operand_size == 8 then fail("8 bit operands are not valid for operation IMUL");

    // execute IMUL
    let wrapped_dest = REG_NORMAL(dest);
    let dest_val = read_GPR(operand_size, wrapped_dest);
    let src_val = read_operand(operand_size, src);
    let result_int = signed(dest_val) * signed(src_val);
    let result_128 = get_slice_int(operand_size * 2, result_int, 0);
    let result = result_128[operand_size - 1 .. 0];
    write_GPR(operand_size, wrapped_dest, result);

    // set carry and overflow flag if the result overflows the allocated space (operand_size bits), else clear
    if sail_sign_extend(result, operand_size * 2) == result_128 then {
        RFLAGS[CF] = 0b0;
        RFLAGS[OF] = 0b0;
    }
    else {
        RFLAGS[CF] = 0b1;
        RFLAGS[OF] = 0b1;
    }
}

// Decode IMUL r{16, 32, 64} r/m{16, 32, 64}
function clause decode_two_byte_instruction(0x0FAF, instruction_ptr, read_offset, decoded_prefixes) = {
    // IMUL does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "IMUL");

    // Get 2 operands of the addressing method + operand type: Operand 1 = Gv, Operand 2 = Ev
    let (new_read_offset, operand_size, rm_operand1, rmi_operand2) = 
        get_Gv_Ev_operands(instruction_ptr, read_offset, decoded_prefixes);
    // 
    match (rm_operand1, rmi_operand2) {
        // both operands are registers
        (rm_REG(REG_NORMAL(reg_index_1)), rmi_REG(reg_2)) => {
            Some(new_read_offset, IMUL(operand_size, reg_index_1, rm_REG(reg_2)))
        },
        // operand 1 is a register and operand 2 is a memory location
        (rm_REG(REG_NORMAL(reg_index)), rmi_MEM(mem_loc)) => {
            Some(new_read_offset, IMUL(operand_size, reg_index, rm_MEM(mem_loc)))
        },
        // This case should be unreachable
        _ => {
            fail("Invalid decoding for IMUL r r/m instruction")
        }
    }
}



/*------------------------------------------------------------------------------
 * CALL
 *-----------------------------------------------------------------------------*/

function clause execute(CALL(rel32)) = {
    /* execute near relative call */
    let displacement = sail_sign_extend(rel32, 64);
    // update stack pointer to point to the new top of the stack
    RSP = sub_bits(RSP, sail_zero_extend(0x8, 64));
    // push current RIP to the stack
    write_operand(64, rm_MEM(RSP), RIP);
    // change RIP as specified by the instruction
    RIP = add_bits(RIP, displacement);
}

// Decode CALL rel32
function clause decode_one_byte_instruction(0xE8, instruction_ptr, read_offset, decoded_prefixes) = {
    // CALL does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "CALL");
    // CALL rel16, an instruction with the same opcode, is not supported in 64-bit mode
    if decoded_prefixes.op_size_override then fail("CALL rel16 is not supported in 64-bit mode");

    // read 32-bit immediate
    let operand = read_memory(4, instruction_ptr + read_offset, create_iFetchAccessDescriptor());
    // increment read offset
    let new_read_offset = read_offset + 4;
    // return new read offset + decoded instruction
    Some(new_read_offset, CALL(operand))
}



/*------------------------------------------------------------------------------
 * LEAVE
 *-----------------------------------------------------------------------------*/

function clause execute(LEAVE(operand_size)) = {
    /* copy frame pointer (RBP) into the stack pointer register (RSP)
    to release the stack space allocated to the topmost stack frame */
    RSP = RBP;

    // pop value from the stack
    let popped_value = read_operand(operand_size, rm_MEM(RSP));
    // store popped value in RBP
    write_GPR(operand_size, REG_NORMAL(5), popped_value);
    // increment stack pointer to free the popped stack space
    RSP = RSP + (operand_size / 8);
}

// Decode LEAVE instruction (operand size = 16 or 64 bits)
function clause decode_one_byte_instruction(0xC9, instruction_ptr, read_offset, decoded_prefixes) = {
    // LEAVE does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "LEAVE");

    // Get operand size. Default is 64 bits. Ignore REX prefix.
    let operand_size = get_operand_size_ignoring_REX(decoded_prefixes, 64);
    assert(operand_size == 16 | operand_size == 64); // required for type-checking as only LEAVE(16) and LEAVE(64) are allowed instructions
    Some(read_offset, LEAVE(operand_size))
}



/*------------------------------------------------------------------------------
 * RET
 *-----------------------------------------------------------------------------*/

function clause execute(RET()) = {
    /* execute near return */
    // pop value into RIP
    RIP = read_operand(64, rm_MEM(RSP));
    // increment stack pointer to free the popped stack space
    RSP = RSP + 8;
}

// Decode near RET instruction
function clause decode_one_byte_instruction(0xC3, instruction_ptr, read_offset, decoded_prefixes) = {
    // RET does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, "RET");

    Some(read_offset, RET())
}



/*------------------------------------------------------------------------------
 * JMP, JNS, JNE
 *-----------------------------------------------------------------------------*/

function clause execute(JMP(rel8)) = {
    /* execute jump short */
    // add the operand to the current instruction pointer value
    let displacement = sail_sign_extend(rel8, 64);
    RIP = RIP + displacement;
}

function clause execute(JNS(rel8)) = {
    /* execute jump short if not sign */
    if RFLAGS[SF] == 0b0 then execute(JMP(rel8))
}

function clause execute(JNE(rel8)) = {
    /* execute jump short if not equal */
    if RFLAGS[ZF] == 0b0 then execute(JMP(rel8))
}

// Decode J?? rel8
function clause decode_one_byte_instruction (
    (opc, instruction_ptr, read_offset, decoded_prefixes) if opc == 0xEB | opc == 0x79 | opc == 0x75) = {
        
    let string_op: string = match opc {
        0xEB => "JMP",
        0x79 => "JNS",
        0x75 => "JNE",
        _ => "Unreachable op" // Should be unreachable
    } in
    // J?? does not support the lock prefix
    fail_if_lock(decoded_prefixes.lock, string_op);

    // read 8-bit immediate
    let operand = read_memory(1, instruction_ptr + read_offset, create_iFetchAccessDescriptor());
    // increment read offset
    let new_read_offset = read_offset + 1;

    // return new read offset + decoded instruction
    match opc {
        0xEB => Some(new_read_offset, JMP(operand)),
        0x79 => Some(new_read_offset, JNS(operand)),
        0x75 => Some(new_read_offset, JNE(operand)),
        _ => None() // Should be unreachable
    }
}



end execute

// Decode cases for opcodes that the model, or x86, does not support
function clause decode_one_byte_instruction(_, instruction_ptr, read_offset, decoded_prefixes) = None()
function clause decode_two_byte_instruction(_, instruction_ptr, read_offset, decoded_prefixes) = None()

end decode_one_byte_instruction
end decode_two_byte_instruction
