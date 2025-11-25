// TODO: Implement read and write operand for memory

/* read immediate value from variable bit-extended to 64 bits */
val read_imm: forall 'm, 'm in {8, 16, 32, 64}. (int('m), generic_imm) -> bits('m)
function read_imm(wsize, imm) = imm[wsize - 1 .. 0]

/* read reg_or_mem operand */
val read_rm_operand: forall 'm, 'm in {8, 16, 32, 64}. (int('m), reg_or_mem) -> bits('m)
function read_rm_operand(wsize, operand: reg_or_mem) = {
    match operand {
        rm_REG(reg_index) => read_reg(wsize, reg_index),
        _ => throw(EUnsupported("This operand is not supported"))
    }
}

/* read any (reg / mem / imm) operand */
val read_rmi_operand: forall 'm, 'm in {8, 16, 32, 64}. (int('m), any) -> bits('m)
function read_rmi_operand(wsize, operand: any) = {
    match operand {
        rmi_IMM(imm) => read_imm(wsize, imm),
        rmi_REG(reg_index) => read_reg(wsize, reg_index),
        _ => throw(EUnsupported("This operand is not supported"))
    }
}

/* overloaded function to read any operand type present in the ast */
overload read_operand = {read_rm_operand, read_rmi_operand, read_imm, read_reg}

/* write to reg or mem location */
val write_rm_operand: forall 'm, 'm in {8, 16, 32, 64}. (int('m), reg_or_mem, bits('m)) -> unit
function write_rm_operand(wsize: operand: reg_or_mem, value) = {
    match operand {
        rm_REG(reg_index) => write_reg(wsize, operand, value),
        _ => throw(EUnsupported("This operand is not supported"))
    }
}

/* overloaded function to write to any register or memory type */
overload write_operand = {write_rm_operand, write_reg}