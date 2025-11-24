union ast = {
    // if one of the types is a tuple with first element word_size, the tuple represents (word_size, dest, src)
    MOV: (word_size, reg_or_mem, any),
    XOR: (word_size, reg_or_mem, any),
    SFENCE: unit,
    LFENCE: unit,
    MFENCE: unit,
    CMP: (word_size, reg_or_mem, any),
    PUSH: (word_size, any),
    POP: (word_size, reg_or_mem),
    ADD: (word_size, reg_or_mem, any),
    SUB: (word_size, reg_or_mem, any),
    IMUL: (word_size, reg_index, reg_or_mem), // IMUL with only 2 arguments (dest and src)
    LEAVE: unit,
    RET: unit,
    JMP_short: imm8,
    JNS_short: imm8,
    CALL: imm32
}