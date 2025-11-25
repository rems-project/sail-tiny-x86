/* range of registers that one can refer to */
type reg_index = range(0, 15)

/*
* Memory addresses are 64 bits, but not all of these are allowed to be used. 
* (Must verify that a memory address is valid before use. 
* Implementing a flat memory model, so no segmentation.)
*/
type mem_addr = bits(64)

/* permitted word sizes */
type word_size = {8,16,32,64}

/* immediate value types */
type imm8 = bits(8)
type imm16 = bits(16)
type imm32 = bits(32)
type imm64 = bits(64)
type generic_imm = bits(64)

/* union types for operand */
union reg_or_mem = {
    rm_REG: reg_index,
    rm_MEM: mem_addr
}
union any = {
    rmi_IMM: generic_imm,
    rmi_REG: reg_index,
    rmi_MEM: mem_addr
}

/* read operand */
union exception = {
    EUnsupported: string,
    EUnreachable: string
}