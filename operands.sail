/* Memory addresses are 64 bits. Assume all possible addresses can be used. */
type mem_addr = bits(64)

/* immediate value types */
type imm8 = bits(8)
type imm16 = bits(16)
type imm32 = bits(32)
type imm64 = bits(64)
union imm = {
    IMM8: imm8,
    IMM16: imm16,
    IMM32: imm32,
    IMM64: imm64
}

/* union types for operand */
// register or memory operand
union rm_operand = {
    rm_REG: reg_ref,
    rm_MEM: mem_addr
}
// register, memory, or immediate operand
union rmi_operand = {
    rmi_IMM: imm,
    rmi_REG: reg_ref,
    rmi_MEM: mem_addr
}

/* permitted word sizes */
type word_size = {8,16,32,64}

/* read immediate value from variable bit-extended to 64 bits */
val read_imm: forall 'm, 'm in {8, 16, 32, 64}. (int('m), imm) -> bits('m)
function read_imm(wsize, imm) = {
    // If imm size is smaller than word size, then sign-extend the imm before returning it
    match imm {
        IMM8(value) => {
            assert(wsize == 8, "Immediate value size is 8 bits, but word size is not.");
            value[7 .. 0]
        },
        IMM16(value) => {
            assert(wsize == 16, "Immediate value size is 16 bits, but word size is not.");
            value[15 .. 0]
        },
        IMM32(value) => {
            assert(wsize >= 32, "Immediate value size is 32 bits, but word size is not 32 or 64 bits.");
            sail_sign_extend(value[31 .. 0], wsize)
        },
        IMM64(value) => {
            assert(wsize == 64, "Immediate value size is 64 bits, but word size is not.");
            value[63 .. 0]
        },
    }
}

/* read register or memory operand */
val read_rm_operand: forall 'm, 'm in {8, 16, 32, 64}. (int('m), rm_operand) -> bits('m)
function read_rm_operand(wsize, operand: rm_operand) = {
    let wsize_bytes = wsize / 8;
    assert('m == wsize_bytes * 8); // required for type-checking
    match operand {
        rm_REG(reg_ref) => read_reg(wsize, reg_ref),
        rm_MEM(mem_addr) => read_memory(wsize_bytes, mem_addr, create_readAccessDescriptor()),
    }
}

/* read register / memory / immediate operand */
val read_rmi_operand: forall 'm, 'm in {8, 16, 32, 64}. (int('m), rmi_operand) -> bits('m)
function read_rmi_operand(wsize, operand: rmi_operand) = {
    let wsize_bytes = wsize / 8;
    assert('m == wsize_bytes * 8); // required for type-checking
    match operand {
        rmi_IMM(imm) => read_imm(wsize, imm),
        rmi_REG(reg_ref) => read_reg(wsize, reg_ref),
        rmi_MEM(mem_addr) => read_memory(wsize_bytes, mem_addr, create_readAccessDescriptor()),
    }
}

/* overloaded function to read any operand type present in the ast */
overload read_operand = {read_rm_operand, read_rmi_operand, read_imm, read_reg}

/* write to reg or mem location */
val write_rm_operand: forall 'm, 'm in {8, 16, 32, 64}. (int('m), rm_operand, bits('m)) -> unit
function write_rm_operand(wsize, operand: rm_operand, value) = {
    let wsize_bytes = wsize / 8;
    assert('m == wsize_bytes * 8); // required for type-checking
    match operand {
        rm_REG(reg_ref) => write_reg(wsize, reg_ref, value),
        rm_MEM(mem_addr) => write_memory(wsize_bytes, mem_addr, value, create_writeAccessDescriptor()),
    }
}

/* overloaded function to write to any register or memory type */
overload write_operand = {write_rm_operand, write_reg}