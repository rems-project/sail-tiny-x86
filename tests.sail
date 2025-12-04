function write_then_read_mem() -> unit = {
  let mem_addr = 0x0000_0000_0000_0007;
  let value = 0x0000_0000_0000_0004;
  write_memory(8, mem_addr, value, create_writeAccessDescriptor());
  let read_value: bits(64) = read_memory(8, mem_addr, create_readAccessDescriptor());
  assert(read_value == value, "Writing then reading from the same memory address was inconsistent");
}

function mov_reg_to_mem() -> unit = {
  let wsize = 16;
  write_reg(wsize, ref R8, get_slice_int(wsize, -236, 0));
  execute(MOV(wsize, rm_MEM(0xFFFF_FFFF_FFFF_FFF8), rmi_REG(ref R8)));
  assert(signed(read_operand(wsize, rm_MEM(0xFFFF_FFFF_FFFF_FFF8))) == -236, "MOV(mem, reg) gave an incorrect answer")
}

function xor_2_numbers() -> unit = {
  let wsize1 = 64;
  let wsize2 = 32;
  write_reg(wsize1, ref R8, 0x0101_0101_0101_0101);
  let imm_val = 0x0000_1111;
  execute(XOR(wsize1, rm_REG(ref R8), rmi_IMM(IMM32(imm_val))));
  assert(read_reg(wsize1, ref R8) == 0x0101_0101_0101_1010, "XOR(reg, imm) gave an incorrect answer")
}

function cmp_jns() -> unit = {
  write_reg(32, ref RAX, 0x4444_4444);
  execute(CMP(32, rm_REG(ref RAX), rmi_IMM(IMM32(0x5555_5555))));
  assert(RFLAGS[SF] == 1, "CMP does not set sign flag correctly");
  let current_RIP = RIP;
  execute(JNS(0x34));
  assert(RIP == current_RIP, "JNS performs a jump when the sign is set");
  RFLAGS[SF] = 0b0;
  execute(JNS(0x34));
  assert(RIP == add_bits(current_RIP, sail_sign_extend(0x34, 64)), "JNS does not perform a correct jump when the sign is cleared");
}

function push_pop() -> unit = {
  let wsize1 = 16;
  let RSP1 = RSP;
  execute(PUSH(wsize1, rmi_IMM(IMM16(0xF0F0))));
  assert(RSP + 8 == RSP1, "PUSH does not correctly change stack pointer");
  assert(read_operand(64, rm_MEM(RSP)) == sail_sign_extend(0xF0F0, 64), "PUSH does not push the correct value to the top of the stack");
  execute(POP(64, rm_REG(ref R15)));
  assert(RSP == RSP1, "POP does not correctly change stack pointer");
  assert(read_reg(64, ref R15) == sail_sign_extend(0xF0F0, 64), "POP does not put the correct value in the destination")
}

function add_2_numbers() -> unit = {
  let wsize1 = 64;
  let wsize2 = 32;
  write_reg(wsize1, ref R8, get_slice_int(wsize1, 30, 0));
  let imm_val = get_slice_int(wsize2, -250, 0);
  execute(ADD(wsize1, rm_REG(ref R8), rmi_IMM(IMM32(imm_val))));
  assert(signed(read_reg(wsize1, ref R8)) == 30 - 250, "ADD(reg, imm) gave an incorrect answer")
}

function subtract_2_numbers() -> unit = {
  let wsize1 = 64;
  let wsize2 = 32;
  write_reg(wsize1, ref R8, get_slice_int(wsize1, 30, 0));
  let imm_val = get_slice_int(wsize2, -250, 0);
  execute(SUB(wsize1, rm_REG(ref R8), rmi_IMM(IMM32(imm_val))));
  assert(signed(read_reg(wsize1, ref R8)) == 30 - (- 250), "SUB(reg, imm) gave an incorrect answer");
}

function multiply_2_numbers() -> unit = {
  let wsize = 16;
  write_reg(wsize, ref R8, get_slice_int(wsize, 30, 0));
  write_reg(wsize, ref R9, get_slice_int(wsize, -250, 0));
  execute(IMUL(wsize, ref R8, rm_REG(ref R9)));
  assert(signed(read_reg(wsize, ref R8)) == 30 * (- 250), "IMUL(reg, reg) gave an incorrect answer");
}

function jmp() -> unit = {
  let current_RIP = RIP;
  execute(JMP(0xFF));
  assert(RIP == add_bits(current_RIP, sail_sign_extend(0xFF, 64)), "JMP does not perform a correct jump");
}

function main() : unit -> unit = {
  write_then_read_mem();
  mov_reg_to_mem();
  xor_2_numbers();
  cmp_jns();
  push_pop();
  add_2_numbers();
  subtract_2_numbers();
  multiply_2_numbers();
  jmp();
}