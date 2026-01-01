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
    rm_REG: reg_index,
    rm_MEM: mem_addr
}
// register, memory, or immediate operand
union rmi_operand = {
    rmi_IMM: imm,
    rmi_REG: reg_index,
    rmi_MEM: mem_addr
}

/* permitted operand sizes */
type operand_size = {8,16,32,64}

/* read immediate value from operand */
val read_imm: forall 'operand_size, 'operand_size in {8, 16, 32, 64}. (int('operand_size), imm) -> bits('operand_size)
function read_imm(operand_size, imm) = {
    match imm {
        IMM8(value) => {
            assert(operand_size == 8, "Immediate value size is 8 bits, but operand size is not.");
            value
        },
        IMM16(value) => {
            assert(operand_size == 16, "Immediate value size is 16 bits, but operand size is not.");
            value
        },
        IMM32(value) => {
            // If imm size is smaller than operand size, then sign-extend the imm before returning it
            assert(operand_size >= 32, "Immediate value size is 32 bits, but operand size is not 32 or 64 bits.");
            sail_sign_extend(value, operand_size)
        },
        IMM64(value) => {
            assert(operand_size == 64, "Immediate value size is 64 bits, but operand size is not.");
            value
        },
    }
}

/* read register or memory operand */
val read_rm_operand: forall 'operand_size, 'operand_size in {8, 16, 32, 64}. (bool, int('operand_size), rm_operand) -> bits('operand_size)
function read_rm_operand(lock, operand_size, operand) = {
    match operand {
        rm_REG(reg_index) => read_GPR(operand_size, reg_index),
        rm_MEM(mem_addr) => {
            let acc_desc = if lock then create_atomicReadAccessDescriptor() else create_readAccessDescriptor();
            let operand_size_bytes = operand_size / 8;
            assert(operand_size == operand_size_bytes * 8); // required for type-checking
            read_memory(operand_size_bytes, mem_addr, acc_desc)
        },
    }
}

/* read register / memory / immediate operand */
val read_rmi_operand: forall 'operand_size, 'operand_size in {8, 16, 32, 64}. (bool, int('operand_size), rmi_operand) -> bits('operand_size)
function read_rmi_operand(lock, operand_size, operand) = {
    match operand {
        rmi_IMM(imm) => read_imm(operand_size, imm),
        rmi_REG(reg_index) => read_GPR(operand_size, reg_index),
        rmi_MEM(mem_addr) => {
            let acc_desc = if lock then create_atomicReadAccessDescriptor() else create_readAccessDescriptor();
            let operand_size_bytes = operand_size / 8;
            assert(operand_size == operand_size_bytes * 8); // required for type-checking
            read_memory(operand_size_bytes, mem_addr, acc_desc)
        },
    }
}

/* overloaded function to read any operand type present in the ast */
overload read_operand = {read_rm_operand, read_rmi_operand}

/* write to reg or mem location */
val write_rm_operand: forall 'operand_size, 'operand_size in {8, 16, 32, 64}. (bool, int('operand_size), rm_operand, bits('operand_size)) -> unit
function write_rm_operand(lock, operand_size, operand, value) = {
    match operand {
        rm_REG(reg_index) => write_GPR(operand_size, reg_index, value),
        rm_MEM(mem_addr) => {
            let acc_desc = if lock then create_atomicWriteAccessDescriptor() else create_writeAccessDescriptor();
            let operand_size_bytes = operand_size / 8;
            assert(operand_size == operand_size_bytes * 8); // required for type-checking
            write_memory(operand_size_bytes, mem_addr, value, acc_desc)
        },
    }
}

/* overloaded function to write to any register or memory type */
overload write_operand = {write_rm_operand}
