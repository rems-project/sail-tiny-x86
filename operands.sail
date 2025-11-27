/*
* Memory addresses are 64 bits, but not all of these are allowed to be used. 
* (Must verify that a memory address is valid before use. 
* Implementing a flat memory model, so no segmentation.)
*/
type mem_addr = bits(64)

/* immediate value types */
type imm8 = bits(8)
type imm16 = bits(16)
type imm32 = bits(32)
type imm64 = bits(64)
type generic_imm = bits(64)

/* union types for operand */
// register or memory operand
union rm_operand = {
    rm_REG: reg_index,
    rm_MEM: mem_addr
}
// register, memory, or immediate operand
union rmi_operand = {
    rmi_IMM: generic_imm,
    rmi_REG: reg_index,
    rmi_MEM: mem_addr
}

/* permitted word sizes */
type word_size = {8,16,32,64}

/* read immediate value from variable bit-extended to 64 bits */
val read_imm: forall 'm, 'm in {8, 16, 32, 64}. (int('m), generic_imm) -> bits('m)
function read_imm(wsize, imm) = imm[wsize - 1 .. 0]

/* read register or memory operand */
val read_rm_operand: forall 'm, 'm in {8, 16, 32, 64}. (int('m), rm_operand) -> bits('m)
function read_rm_operand(wsize, operand: rm_operand) = {
    let wsize_bytes = tdiv_int(wsize,8);
    assert('m == wsize_bytes * 8); // required for type-checking
    match operand {
        rm_REG(reg_index) => read_reg(wsize, reg_index),
        rm_MEM(mem_addr) => read_memory(wsize_bytes, mem_addr, create_readAccessDescriptor()),
    }
}

/* read register / memory / immediate operand */
val read_rmi_operand: forall 'm, 'm in {8, 16, 32, 64}. (int('m), rmi_operand) -> bits('m)
function read_rmi_operand(wsize, operand: rmi_operand) = {
    let wsize_bytes = tdiv_int(wsize,8);
    assert('m == wsize_bytes * 8); // required for type-checking
    match operand {
        rmi_IMM(imm) => read_imm(wsize, imm),
        rmi_REG(reg_index) => read_reg(wsize, reg_index),
        rmi_MEM(mem_addr) => read_memory(wsize_bytes, mem_addr, create_readAccessDescriptor()),
    }
}

/* overloaded function to read any operand type present in the ast */
overload read_operand = {read_rm_operand, read_rmi_operand, read_imm, read_reg}

/* write to reg or mem location */
val write_rm_operand: forall 'm, 'm in {8, 16, 32, 64}. (int('m), rm_operand, bits('m)) -> unit
function write_rm_operand(wsize, operand: rm_operand, value) = {
    let wsize_bytes = tdiv_int(wsize,8);
    assert('m == wsize_bytes * 8); // required for type-checking
    match operand {
        rm_REG(reg_index) => write_reg(wsize, reg_index, value),
        rm_MEM(mem_addr) => write_memory(wsize_bytes, mem_addr, value, create_writeAccessDescriptor()),
    }
}

/* overloaded function to write to any register or memory type */
overload write_operand = {write_rm_operand, write_reg}