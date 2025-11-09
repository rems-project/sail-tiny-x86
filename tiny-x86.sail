union ast = {
    // if one of the types is a tuple with first element word_size, the tuple represents (word_size, dest, src)
    MOV: (word_size, reg_index, imm_or_reg),
    XOR: (word_size, reg_index, imm_or_reg),
    SFENCE: unit,
    LFENCE: unit,
    MFENCE: unit,
    CMP: (word_size, reg_index, imm_or_reg),
    PUSH: imm_or_reg,
    POP: reg_index,
    SUB: (word_size, reg_index, imm_or_reg),
    IMUL: (word_size, reg_index, reg_index), // IMUL with only 2 arguments (dest and src)
    LEAVE: unit,
    RET: unit,
    JMP_short: imm8,
    JNS_short: imm8,
    CALL: imm32
}