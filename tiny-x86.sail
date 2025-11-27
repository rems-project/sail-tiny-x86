union ast = {
    // if one of the types is a tuple with first element word_size, the tuple represents (word_size, dest, src)
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