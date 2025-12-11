function write_then_read_mem() -> unit = {
  // write test
  let mem_addr = 0x0000_0000_0000_0007;
  let value = 0x0000_0000_0000_0004;
  write_memory(8, mem_addr, value, create_writeAccessDescriptor());
  // read test
  let read_value: bits(64) = read_memory(8, mem_addr, create_readAccessDescriptor());
  assert(read_value == value, "Writing then reading from the same memory address was inconsistent");
}

function mov_reg_to_mem() -> unit = {
  let wsize = 16;
  write_GPR(wsize, 8, get_slice_int(wsize, -236, 0));
  execute(MOV(wsize, rm_MEM(0xFFFF_FFFF_FFFF_FFF8), rmi_REG(8)));
  assert(signed(read_operand(false, wsize, rm_MEM(0xFFFF_FFFF_FFFF_FFF8))) == -236, "MOV(mem, reg) gave an incorrect answer")
}

function xor_2_numbers() -> unit = {
  let lock = false;
  let wsize1 = 64;
  let wsize2 = 32;
  write_GPR(wsize1, 8, 0x0101_0101_0101_0101);
  let imm_val = 0x0000_1111;
  execute(XOR(lock, wsize1, rm_REG(8), rmi_IMM(IMM32(imm_val))));
  assert(read_GPR(wsize1, 8) == 0x0101_0101_0101_1010, "XOR(reg, imm) gave an incorrect answer")
}

function cmp_jns() -> unit = {
  // cmp test
  write_GPR(32, 0, 0x4444_4444);
  execute(CMP(32, rm_REG(0), rmi_IMM(IMM32(0x5555_5555))));
  assert(RFLAGS[SF] == 1, "CMP does not set sign flag correctly");
  // jns test
  let current_RIP = RIP;
  execute(JNS(0x34));
  assert(RIP == current_RIP, "JNS performs a jump when the sign is set");
  RFLAGS[SF] = 0b0;
  execute(JNS(0x34));
  assert(RIP == add_bits(current_RIP, sail_sign_extend(0x34, 64)), "JNS does not perform a correct jump when the sign is cleared");
}

function push_pop() -> unit = {
  let RSP1 = RSP;
  // push test
  let wsize1 = 16;
  execute(PUSH(wsize1, rmi_IMM(IMM16(0xF0F0))));
  assert(RSP + 8 == RSP1, "PUSH does not correctly change stack pointer");
  assert(read_operand(false, 64, rm_MEM(RSP)) == sail_sign_extend(0xF0F0, 64), "PUSH does not push the correct value to the top of the stack");
  // pop test
  execute(POP(64, rm_REG(15)));
  assert(RSP == RSP1, "POP does not correctly change stack pointer");
  assert(read_GPR(64, 15) == sail_sign_extend(0xF0F0, 64), "POP does not put the correct value in the destination")
}

function add_2_numbers() -> unit = {
  let lock = false;
  let wsize1 = 64;
  let wsize2 = 32;
  write_GPR(wsize1, 8, get_slice_int(wsize1, 30, 0));
  let imm_val = get_slice_int(wsize2, -250, 0);
  execute(ADD(lock, wsize1, rm_REG(8), rmi_IMM(IMM32(imm_val))));
  assert(signed(read_GPR(wsize1, 8)) == 30 - 250, "ADD(reg, imm) gave an incorrect answer")
}

function subtract_2_numbers() -> unit = {
  let lock = false;
  let wsize1 = 64;
  let wsize2 = 32;
  write_GPR(wsize1, 8, get_slice_int(wsize1, 30, 0));
  let imm_val = get_slice_int(wsize2, -250, 0);
  execute(SUB(lock, wsize1, rm_REG(8), rmi_IMM(IMM32(imm_val))));
  assert(signed(read_GPR(wsize1, 8)) == 30 - (- 250), "SUB(reg, imm) gave an incorrect answer");
}

function multiply_2_numbers() -> unit = {
  let wsize = 16;
  write_GPR(wsize, 8, get_slice_int(wsize, 30, 0));
  write_GPR(wsize, 9, get_slice_int(wsize, -250, 0));
  execute(IMUL(wsize, 8, rm_REG(9)));
  assert(signed(read_GPR(wsize, 8)) == 30 * (- 250), "IMUL(reg, reg) gave an incorrect answer");
}

function call_leave_ret() -> unit = {
  // call test
  RSP = 0x0000_0000_0000_ABC8;
  RIP = 0xFFFF_0000_0000_0000;
  let original_RIP = RIP;
  let original_RSP = RSP;
  execute(CALL(0xFEFE_FEFE));
  assert(RSP == 0x0000_0000_0000_ABC0, "CALL instruction does not decrement RSP correctly (when pushing a value to the stack)");
  assert(read_operand(false, 64, rm_MEM(RSP)) == original_RIP, "CALL instruction puts incorrect value at the top of the stack");
  assert(RIP == add_bits(original_RIP, sail_sign_extend(0xFEFE_FEFE, 64)), "CALL instruction does not change RIP correctly");

  // "push" and "mov" instructions used to test "leave" and "ret"
  let old_RBP = RBP;
  let old_RSP = RSP;
  // push RBP value to the stack
  execute(PUSH(64, rmi_REG(5))); // 5 is the reg_index for RBP
  // copy RSP value into RBP register
  execute(MOV(64, rm_REG(5), rmi_REG(4))); // 4 is the reg_index for RSP, 5 for RBP

  // leave test
  execute(LEAVE());
  assert(RSP == old_RSP, "LEAVE instruction does not increment RSP correctly (when popping from the stack)");
  assert(RBP == old_RBP, "LEAVE instruction does not pop correct item from the stack into RBP");

  // ret test
  execute(RET());
  assert(RSP == original_RSP, "RET instruction does not increment RSP correctly (when popping from the stack)");
  assert(RIP == original_RIP, "RET instruction does not pop correct item from the stack into RIP");
}

function jmp() -> unit = {
  let current_RIP = RIP;
  execute(JMP(0xFF));
  assert(RIP == add_bits(current_RIP, sail_sign_extend(0xFF, 64)), "JMP does not perform a correct jump");
}

function test_execute() -> unit = {
  write_then_read_mem();
  mov_reg_to_mem();
  xor_2_numbers();
  cmp_jns();
  push_pop();
  add_2_numbers();
  subtract_2_numbers();
  multiply_2_numbers();
  call_leave_ret();
  jmp();
}

function test_decode() -> unit = {
  write_memory(2, RIP, 0x89E5, create_writeAccessDescriptor()); // we prob actually need to write instructions byte by byte
  print_bits("", read_memory(1, RIP, create_readAccessDescriptor()));
}

function main() : unit -> unit = {
  test_execute();
  test_decode();
}
