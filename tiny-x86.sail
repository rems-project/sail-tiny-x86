let DEFAULT_PREFIX: prefix(64) = struct {lock = false, wsize = 64}

union ast('wsize) = {
    // Structure of all possible executable instructions
    // if one of the types is a tuple with first element prefix, the tuple represents (prefix, dest, src), unless the instruction is CMP
    MOV: (prefix('wsize), rm_operand, rmi_operand),
    XOR: (prefix('wsize), rm_operand, rmi_operand),
    SFENCE: unit,
    LFENCE: unit,
    MFENCE: unit,
    CMP: (prefix('wsize), rm_operand, rmi_operand),
    PUSH: (prefix('wsize), rmi_operand), // only allowing 64 bit operand
    POP: (prefix('wsize), rm_operand),
    ADD: (prefix('wsize), rm_operand, rmi_operand),
    SUB: (prefix('wsize), rm_operand, rmi_operand),
    IMUL: (prefix('wsize), reg_index, rm_operand), // IMUL with only 2 arguments (dest and src)
    CALL: imm32,
    LEAVE: unit,
    RET: unit, // near return only
    JMP: imm8, // jump short only
    JNS: imm8, // jump short if not sign only
    HLT: unit
}

type default_ast = ast(64)

val fail_if_two_mem_operands : (rm_operand, rmi_operand, string) -> unit
function fail_if_two_mem_operands(dest, src, operation) = {
    let error_message = concat_str(operation, " operation cannot occur between 2 memory locations");
    match (dest, src) {
        (rm_MEM(_), rmi_MEM(_)) => fail(error_message),
        (_,_) => ()
    }
}

val fail_if_invalid_lock : forall 'wsize, 'wsize in {8, 16, 32, 64}. (prefix('wsize), ast('wsize)) -> unit
function fail_if_invalid_lock(prefix, op) = {
    if prefix.lock then {
        match op {
            XOR(prefix, rm_REG(_), src) => fail("undefined opcode exception (#UD): LOCK prefix cannot be applied to dest = reg"),
            ADD(prefix, rm_REG(_), src) => fail("undefined opcode exception (#UD): LOCK prefix cannot be applied to dest = reg"),
            SUB(prefix, rm_REG(_), src) => fail("undefined opcode exception (#UD): LOCK prefix cannot be applied to dest = reg"),
            _ => fail("undefined opcode exception (#UD): LOCK prefix cannot be prepended to instruction")
        }
    }
}

val execute : forall 'wsize, 'wsize in {8, 16, 32, 64}. ast('wsize) -> unit
scattered function execute

function clause execute(MOV(prefix, dest, src)) = {
    // required assertion for type-checking
    assert(prefix.wsize == 8 | prefix.wsize == 16 | prefix.wsize == 32 | prefix.wsize == 64);
    // MOV cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "MOV");
    // MOV operation cannot be executed on dest = mem64 and src = imm64
    match (dest, src) {
        (rm_MEM(_), rmi_IMM(IMM64(_))) => fail("MOV operation cannot be executed on dest = mem64 and src = imm64"),
        (_,_) => ()
    };
    // MOV is not valid with prefix lock = true
    fail_if_invalid_lock(prefix, MOV(prefix, dest, src));

    // execute MOV instruction
    let val_to_write = read_operand(prefix, src);
    write_operand(prefix, dest, val_to_write)
}

function clause execute(XOR(prefix, dest, src)) = {
    // required assertion for type-checking
    assert(prefix.wsize == 8 | prefix.wsize == 16 | prefix.wsize == 32 | prefix.wsize == 64);
    // XOR cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "XOR");
    // For operation XOR, src = imm64 is not a valid operand 
    match src {
        rmi_IMM(IMM64(_)) => fail("For operation XOR, src = imm64 is not a valid operand"),
        _ => ()
    };
    // XOR is not valid with prefix lock = true if dest is a register location
    fail_if_invalid_lock(prefix, XOR(prefix, dest, src));

    // execute XOR instruction
    let dest_val = read_operand(prefix, dest);
    let src_val = read_operand({prefix with lock = false}, src);
    let result = xor_vec(dest_val, src_val);
    write_operand(prefix, dest, result);

    /* change value of status flags */
    // clear overflow and carry flag
    RFLAGS[OF] = 0b0;
    RFLAGS[CF] = 0b0;
    // sign flag = msb of result (0 = +ve, 1 = -ve)
    RFLAGS[SF] = [result[prefix.wsize - 1]];
    // set zero flag if result = 0, else clear zero flag
    RFLAGS[ZF] = if result == sail_zero_extend(0x0, prefix.wsize) then 0b1 else 0b0;
    // set parity flag if least significant byte of result contains an even number of 1 bits, else clear
    modify_parity_flag(result);
}

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

function clause execute(CMP(prefix, first, second)) = {
    // required assertion for type-checking
    assert(prefix.wsize == 8 | prefix.wsize == 16 | prefix.wsize == 32 | prefix.wsize == 64);
    // CMP cannot occur between first = memory location and second = memory location
    fail_if_two_mem_operands(first, second, "CMP");
    // For operation CMP, second = imm64 is not a valid operand 
    match second {
        rmi_IMM(IMM64(_)) => fail("For operation CMP, second = imm64 is not a valid operand"),
        _ => ()
    };
    // CMP is not valid with prefix lock = true
    fail_if_invalid_lock(prefix, CMP(prefix, first, second));

    // execute CMP instruction
    let first_val = read_operand(prefix, first);
    let second_val = read_operand(prefix, second);
    let result = sub_bits(first_val, second_val);

    /* change value of status flags. Equivalent to the changes made on executing the SUB instruction. */
    let wsize = prefix.wsize;
    // sign flag = msb of result (0 = +ve, 1 = -ve)
    RFLAGS[SF] = [result[wsize - 1]];
    // set overflow flag (which is for signed values) if first and second operand have opposite signs, but the sign of the result doesn't match the first operand, else clear
    RFLAGS[OF] = if not_bool(first_val[wsize - 1] == second_val[wsize - 1]) & not_bool(result[wsize - 1] == first_val[wsize - 1]) then 0b1 else 0b0;
    // set carry flag if result < 0 (as it represents a borrow when subtracting 2 unsigned values), else clear
    RFLAGS[CF] = if unsigned(first_val) < unsigned(second_val) then 0b1 else 0b0;
    // set zero flag if result = 0, else clear zero flag
    RFLAGS[ZF] = if result == sail_zero_extend(0x0, wsize) then 0b1 else 0b0;
    // Set aux carry flag if an arithmetic operation generates a borrow out of bit 3 (i.e. least significant 4 bits) of the result; cleared otherwise
    RFLAGS[AF] = if unsigned(first_val[3 .. 0]) < unsigned(second_val[3 .. 0]) then 0b1 else 0b0;
    // set parity flag if least significant byte of result contains an even number of 1 bits, else clear
    modify_parity_flag(result);
}

function clause execute(PUSH(prefix, src)) = {
    // required assertion for type-checking
    assert(prefix.wsize == 8 | prefix.wsize == 16 | prefix.wsize == 32 | prefix.wsize == 64);
    // PUSH instruction does not allow src = imm64, reg8 or mem8
    match src {
        rmi_IMM(_) if prefix.wsize == 64 => fail("Operand for PUSH operation not allowed"),
        rmi_REG(_) if prefix.wsize == 8 => fail("Operand for PUSH operation not allowed"),
        rmi_MEM(_) if prefix.wsize == 8 => fail("Operand for PUSH operation not allowed"),
        _ => ()
    };
    // PUSH is not valid with prefix lock = true
    fail_if_invalid_lock(prefix, PUSH(prefix, src));

    // If the source operand is an immediate of size less than the operand size, then sign-extend the value
    // default operand size is 8 bytes = 64 bits
    let src_val = sail_sign_extend(read_operand(prefix, src), 64);
    // subtract 8 from RSP to point to the new top of the stack
    RSP = sub_bits(RSP, sail_zero_extend(0x8, 64));
    // push the new item to the top of the stack
    let dest_address = rm_MEM(RSP);
    write_operand(DEFAULT_PREFIX, dest_address, src_val)
}

function clause execute(POP(prefix, dest)) = {
    // required assertion for type-checking
    assert(prefix.wsize == 8 | prefix.wsize == 16 | prefix.wsize == 32 | prefix.wsize == 64);
    // POP instruction does not allow dest to be 8 bits long. Due to 64 bit addressing, dest also cannot be 32 bits long.
    // Also not allowing a 16-bit dest in this model for simplicity (to keep the stack aligned)
    if prefix.wsize == 8 | prefix.wsize == 32 then fail("dest size for POP operation not supported");
    if prefix.wsize == 16 then fail("dest size for POP operation not implemented in this model");
    // POP is not valid with prefix lock = true
    fail_if_invalid_lock(prefix, POP(prefix, dest));

    // pop the value at the top of the stack to dest
    let popped_val = read_operand(DEFAULT_PREFIX, rm_MEM(RSP));
    write_operand(DEFAULT_PREFIX, dest, popped_val);
    // increment stack pointer to free the popped stack space
    RSP = RSP + 8;
}

function clause execute(ADD(prefix, dest, src)) = {
    // required assertion for type-checking
    assert(prefix.wsize == 8 | prefix.wsize == 16 | prefix.wsize == 32 | prefix.wsize == 64);
    // ADD cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "ADD");
    // For operation ADD, src = imm64 is not a valid operand 
    match src {
        rmi_IMM(IMM64(_)) => fail("For operation ADD, src = imm64 is not a valid operand"),
        _ => ()
    };
    // ADD is not valid with prefix lock = true if dest is a register location
    fail_if_invalid_lock(prefix, ADD(prefix, dest, src));

    // execute ADD instruction
    let dest_val = read_operand(prefix, dest);
    let src_val = read_operand({prefix with lock = false}, src);
    let result = add_bits(dest_val, src_val);
    write_operand(prefix, dest, result);

    /* change value of status flags */
    let wsize = prefix.wsize;
    // sign flag = msb of result (0 = +ve, 1 = -ve)
    RFLAGS[SF] = [result[wsize - 1]];
    // set overflow flag (which is for signed values) if dest and src operand have the same sign, but the sign of the result is different
    RFLAGS[OF] = if dest_val[wsize - 1] == src_val[wsize - 1] & not_bool(result[wsize - 1] == dest_val[wsize - 1]) then 0b1 else 0b0;
    // set carry flag (which is for unsigned values) if result is smaller than dest or src, else clear
    RFLAGS[CF] = if unsigned(result) < unsigned(dest_val) | unsigned(result) < unsigned(src_val) then 0b1 else 0b0;
    // set zero flag if result = 0, else clear zero flag
    RFLAGS[ZF] = if result == sail_zero_extend(0x0, wsize) then 0b1 else 0b0;
    // Set aux carry flag if an arithmetic operation generates a carry out of bit 3 (i.e. least significant 4 bits) of the result; cleared otherwise
    RFLAGS[AF] = if unsigned(dest_val[3 .. 0]) + unsigned(src_val[3 .. 0]) >= 16 then 0b1 else 0b0;
    // set parity flag if least significant byte of result contains an even number of 1 bits, else clear
    modify_parity_flag(result);
}

function clause execute(SUB(prefix, dest, src)) = {
    // required assertion for type-checking
    assert(prefix.wsize == 8 | prefix.wsize == 16 | prefix.wsize == 32 | prefix.wsize == 64);
    // SUB cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "SUB");
    // For operation SUB, src = imm64 is not a valid operand 
    match src {
        rmi_IMM(IMM64(_)) => fail("For operation SUB, src = imm64 is not a valid operand"),
        _ => ()
    };
    // SUB is not valid with prefix lock = true if dest is a register location
    fail_if_invalid_lock(prefix, SUB(prefix, dest, src));

    // execute SUB instruction
    let dest_val = read_operand(prefix, dest);
    let src_val = read_operand({prefix with lock = false}, src);
    let result = sub_bits(dest_val, src_val);
    write_operand(prefix, dest, result);

    /* change value of status flags */
    let wsize = prefix.wsize;
    // sign flag = msb of result (0 = +ve, 1 = -ve)
    RFLAGS[SF] = [result[wsize - 1]];
    // set overflow flag (which is for signed values) if dest and src operand have opposite signs, but the sign of the result doesn't match the dest operand, else clear
    RFLAGS[OF] = if not_bool(dest_val[wsize - 1] == src_val[wsize - 1]) & not_bool(result[wsize - 1] == dest_val[wsize - 1]) then 0b1 else 0b0;
    // set carry flag if result < 0 (as it represents a borrow when subtracting 2 unsigned values), else clear
    RFLAGS[CF] = if unsigned(dest_val) < unsigned(src_val) then 0b1 else 0b0;
    // set zero flag if result = 0, else clear zero flag
    RFLAGS[ZF] = if result == sail_zero_extend(0x0, wsize) then 0b1 else 0b0;
    // Set aux carry flag if an arithmetic operation generates a borrow out of bit 3 (i.e. least significant 4 bits) of the result; cleared otherwise
    RFLAGS[AF] = if unsigned(dest_val[3 .. 0]) < unsigned(src_val[3 .. 0]) then 0b1 else 0b0;
    // set parity flag if least significant byte of result contains an even number of 1 bits, else clear
    modify_parity_flag(result);
}

function clause execute(IMUL(prefix, dest, src)) = {
    // required assertion for type-checking
    assert(prefix.wsize == 8 | prefix.wsize == 16 | prefix.wsize == 32 | prefix.wsize == 64);
    
    let wsize = prefix.wsize;
    // IMUL cannot occur between 8 bit register or memory locations
    if wsize == 8 then fail("8 bit operands are not valid for operation IMUL");
    // IMUL is not valid with prefix lock = true
    fail_if_invalid_lock(prefix, IMUL(prefix, dest, src));

    // execute IMUL
    let dest_val = read_GPR(wsize, dest);
    let src_val = read_operand(prefix, src);
    let result_int = signed(dest_val) * signed(src_val);
    let result_temp = get_slice_int(wsize * 2, result_int, 0);
    let result = result_temp[wsize - 1 .. 0];
    write_GPR(wsize, dest, result);

    // set carry and overflow flag if the result overflows the allocated space (wsize bits), else clear
    if sail_sign_extend(result, wsize * 2) == result_temp then {
        RFLAGS[CF] = 0b0;
        RFLAGS[OF] = 0b0;
    }
    else {
        RFLAGS[CF] = 0b1;
        RFLAGS[OF] = 0b1;
    }
}

function clause execute(CALL(rel32)) = {
    /* execute near relative call */
    let displacement = read_imm(64, IMM32(rel32));
    // update stack pointer to point to the new top of the stack
    RSP = sub_bits(RSP, sail_zero_extend(0x8, 64));
    // push current RIP to the stack
    let dest_address = rm_MEM(RSP);
    write_operand(DEFAULT_PREFIX, dest_address, RIP);
    // change RIP as specified by the instruction
    RIP = add_bits(RIP, displacement);
}

function clause execute(LEAVE()) = {
    /* copy frame pointer (RBP) into the stack pointer register (RSP)
    to release the stack space allocated to the topmost stack frame */
    RSP = RBP;
    // pop value into RBP
    RBP = read_operand(DEFAULT_PREFIX, rm_MEM(RSP));
    // increment stack pointer to free the popped stack space
    RSP = RSP + 8;
}

function clause execute(RET()) = {
    /* execute near return */
    // pop value into RIP
    RIP = read_operand(DEFAULT_PREFIX, rm_MEM(RSP));
    // increment stack pointer to free the popped stack space
    RSP = RSP + 8;
}

function clause execute(JMP(rel8)) = {
    /* execute jump short */
    // add the operand to the current instruction pointer value
    let displacement = sail_sign_extend(read_imm(8, IMM8(rel8)), 64);
    RIP = RIP + displacement;
}

function clause execute(JNS(rel8)) = {
    /* execute jump short if not sign */
    if RFLAGS[SF] == 0b0 then {
        // add the operand to the current instruction pointer value
        let displacement = sail_sign_extend(read_imm(8, IMM8(rel8)), 64);
        RIP = RIP + displacement;
    }
}

function clause execute(HLT()) = ()

end execute
