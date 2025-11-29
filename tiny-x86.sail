union ast = {
    // if one of the types is a tuple with first element word_size, the tuple represents (word_size, dest, src), unless the instruction is CMP
    // only implementing instructions where both dest and src have the same word size
    MOV: (word_size, rm_operand, rmi_operand),
    XOR: (word_size, rm_operand, rmi_operand),
    SFENCE: unit,
    LFENCE: unit,
    MFENCE: unit,
    CMP: (word_size, rm_operand, rmi_operand),
    PUSH: (word_size, rmi_operand),
    POP: (word_size, rm_operand),
    ADD: (word_size, rm_operand, rmi_operand),
    SUB: (word_size, rm_operand, rmi_operand),
    IMUL: (word_size, reg_index, rm_operand), // IMUL with only 2 arguments (dest and src)
    LEAVE: unit,
    RET: unit,
    JMP_short: imm8,
    JNS_short: imm8,
    CALL: imm32
}

val fail_if_two_mem_operands : (rm_operand, rmi_operand, string) -> unit
function fail_if_two_mem_operands(dest, src, operation) = {
    let error_message = concat_str(operation, " operation cannot occur between 2 memory locations");

    assert(match (dest, src) {
        (rm_MEM(x), rmi_MEM(y)) => false,
        _ => true
    }, error_message)
}

val execute : ast -> unit
scattered function execute

function clause execute(MOV(wsize, dest, src)) = {
    // MOV cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "MOV");
    // execute MOV instruction
    let val_to_write = read_operand(wsize, src);
    write_operand(wsize, dest, val_to_write)
}

function clause execute(XOR(wsize, dest, src)) = {
    // XOR cannot occur between dest = memory location and src = memory location
    fail_if_two_mem_operands(dest, src, "XOR");
    // execute XOR instruction
    let operand1 = read_operand(wsize, dest);
    let operand2 = read_operand(wsize, src);
    let result = xor_vec(operand1, operand2);
    write_operand(wsize, dest, result);

    /* change value of status flags */
    // clear overflow and carry flag
    RFLAGS[OF] = 0b0;
    RFLAGS[CF] = 0b0;
    // sign flag = msb of result (0 = +ve, 1 = -ve)
    RFLAGS[SF] = [result[wsize - 1]];
    // set zero flag if result = 0, else clear zero flag
    if result == sail_zero_extend(0x0, wsize) then 
        RFLAGS[ZF] = 0b1
    else
        RFLAGS[ZF] = 0b0;
    // set parity flag if least significant byte of result contains an even number of 1 bits, else clear
    modify_parity_flag(result);
}

function clause execute(SFENCE()) = {
    // apply barrier
    sail_barrier(Barrier_SFENCE)
}

function clause execute(LFENCE()) = {
    // apply barrier
    sail_barrier(Barrier_LFENCE)
}

function clause execute(MFENCE()) = {
    // apply barrier
    sail_barrier(Barrier_MFENCE)
}

function clause execute(CMP(wsize, first, second)) = {
    fail_if_two_mem_operands(first, second, "CMP");
    let first_val = read_operand(wsize, first);
    let second_val = read_operand(wsize, second);

    // TODO: complete this function
}

end execute