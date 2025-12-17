/*===========================================================
Non-unit execute tests
============================================================*/

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
  let operand_size = 16;
  write_GPR(operand_size, REG_NORMAL(8), get_slice_int(operand_size, -236, 0));
  execute(MOV(operand_size, rm_MEM(0xFFFF_FFFF_FFFF_FFF8), rmi_REG(REG_NORMAL(8))));
  assert(signed(read_operand(operand_size, rm_MEM(0xFFFF_FFFF_FFFF_FFF8))) == -236, "MOV(mem, reg) gave an incorrect answer")
}

function xor_2_numbers() -> unit = {
  let lock = false;
  let operand_size1 = 64;
  write_GPR(operand_size1, REG_NORMAL(8), 0x0101_0101_0101_0101);
  let imm_val = 0x0000_1111;
  execute(XOR(lock, operand_size1, rm_REG(REG_NORMAL(8)), rmi_IMM(IMM32(imm_val))));
  assert(read_GPR(operand_size1, REG_NORMAL(8)) == 0x0101_0101_0101_1010, "XOR(reg, imm) gave an incorrect answer")
}

function cmp_jns() -> unit = {
  // cmp test
  write_GPR(32, REG_NORMAL(0), 0x4444_4444);
  execute(CMP(32, rm_REG(REG_NORMAL(0)), rmi_IMM(IMM32(0x5555_5555))));
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
  let operand_size1 = 16;
  execute(PUSH(operand_size1, rmi_IMM(IMM16(0xF0F0))));
  assert(RSP + 8 == RSP1, "PUSH does not correctly change stack pointer");
  assert(read_operand(64, rm_MEM(RSP)) == sail_sign_extend(0xF0F0, 64), "PUSH does not push the correct value to the top of the stack");
  // pop test
  execute(POP(64, rm_REG(REG_NORMAL(15))));
  assert(RSP == RSP1, "POP does not correctly change stack pointer");
  assert(read_GPR(64, REG_NORMAL(15)) == sail_sign_extend(0xF0F0, 64), "POP does not put the correct value in the destination")
}

function add_2_numbers() -> unit = {
  let lock = false;
  let operand_size1 = 64;
  let operand_size2 = 32;
  write_GPR(operand_size1, REG_NORMAL(8), get_slice_int(operand_size1, 30, 0));
  let imm_val = get_slice_int(operand_size2, -250, 0);
  execute(ADD(lock, operand_size1, rm_REG(REG_NORMAL(8)), rmi_IMM(IMM32(imm_val))));
  assert(signed(read_GPR(operand_size1, REG_NORMAL(8))) == 30 - 250, "ADD(reg, imm) gave an incorrect answer")
}

function subtract_2_numbers() -> unit = {
  let lock = false;
  let operand_size1 = 64;
  let operand_size2 = 32;
  write_GPR(operand_size1, REG_NORMAL(8), get_slice_int(operand_size1, 30, 0));
  let imm_val = get_slice_int(operand_size2, -250, 0);
  execute(SUB(lock, operand_size1, rm_REG(REG_NORMAL(8)), rmi_IMM(IMM32(imm_val))));
  assert(signed(read_GPR(operand_size1, REG_NORMAL(8))) == 30 - (- 250), "SUB(reg, imm) gave an incorrect answer");
}

function multiply_2_numbers() -> unit = {
  let operand_size = 16;
  write_GPR(operand_size, REG_NORMAL(8), get_slice_int(operand_size, 30, 0));
  write_GPR(operand_size, REG_NORMAL(9), get_slice_int(operand_size, -250, 0));
  execute(IMUL(operand_size, 8, rm_REG(REG_NORMAL(9))));
  assert(signed(read_GPR(operand_size, REG_NORMAL(8))) == 30 * (- 250), "IMUL(reg, reg) gave an incorrect answer");
}

function call_leave_ret() -> unit = {
  // call test
  RSP = 0x0000_0000_0000_ABC8;
  RIP = 0xFFFF_0000_0000_0000;
  let original_RIP = RIP;
  let original_RSP = RSP;
  execute(CALL(0xFEFE_FEFE));
  assert(RSP == 0x0000_0000_0000_ABC0, "CALL instruction does not decrement RSP correctly (when pushing a value to the stack)");
  assert(read_operand(64, rm_MEM(RSP)) == original_RIP, "CALL instruction puts incorrect value at the top of the stack");
  assert(RIP == add_bits(original_RIP, sail_sign_extend(0xFEFE_FEFE, 64)), "CALL instruction does not change RIP correctly");

  // "push" and "mov" instructions used to test "leave" and "ret"
  let old_RBP = RBP;
  let old_RSP = RSP;
  // push RBP value to the stack
  execute(PUSH(64, rmi_REG(REG_NORMAL(5)))); // 5 is the reg_index for RBP
  // copy RSP value into RBP register
  execute(MOV(64, rm_REG(REG_NORMAL(5)), rmi_REG(REG_NORMAL(4)))); // 4 is the reg_index for RSP, 5 for RBP

  // leave test
  execute(LEAVE(64));
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

/*===========================================================
Decode test helper functions
============================================================*/

// reverse the order of each byte then write the resulting instruction to memory
val write_instruction_to_memory : forall 'm, 'm > 0. (implicit('m), bits(8 * 'm), bits(64)) -> unit
function write_instruction_to_memory(m, inst, instruction_ptr) = {
  var res = sail_zeros(8 * m);
  // reverse the order of each byte (e.g. first byte becomes the last byte)
  foreach (i from 0 to (m - 1)) {
    let j = m - i - 1;
    res[(8 * i + 7) .. (8 * i)] = inst[(8 * j + 7) .. (8 * j)]
  };
  // store the resulting instruction in memory
  write_memory(m, instruction_ptr, res, create_writeAccessDescriptor())
}

// rough function (only for rough testing) that returns new rip and instruction if it exists, or a random rip and instruction if it doesn't
val unwrap_decoded_instr: option((bits(64), ast)) -> (bits(64), ast)
function unwrap_decoded_instr(res) = {
  match res {
    Some(new_RIP, instr) => (new_RIP, instr),
    None() => {
      fail("Instruction not decodable by the model");
      (sail_zero_extend(0x0, 64), RET()) // placeholder values
    }
  }
}

/*===========================================================
Decode MOV tests
============================================================*/

function test_decode_mov_rm8_r8() -> unit = {
  // Testing that MOV AH, AL is decoded correctly
  let old_rip = RIP;
  let instruction: bits(16) = 0x88 @ 0b11_000_100;
  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 2, "MOV(rm8, r8): Wrong instruction length has been read");
  assert(decoded_instruction == MOV(8, rm_REG(REG_HIGH_BYTE(4)), rmi_REG(REG_NORMAL(0))), "MOV(rm8, r8) instruction not decoded properly");
}

function test_decode_mov_rm32_r32() -> unit = {
  // Testing that MOV EBP, ESP is decoded correctly
  let old_rip = RIP;
  let instruction: bits(16) = 0x89 @ 0b11_100_101;
  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 2, "MOV(rm32, r32): Wrong instruction length has been read");
  assert(decoded_instruction == MOV(32, rm_REG(REG_NORMAL(5)), rmi_REG(REG_NORMAL(4))), "MOV(rm32, r32) instruction not decoded properly");
}

function test_decode_mov_r8_rm8() -> unit = {
  // Testing that MOV SPL, M(RAX) is decoded correctly
  let old_rip = RIP;
  let instruction: bits(24) = 0b0100_0000 @ 0x8A @ 0b00_100_000;
  write_instruction_to_memory(instruction, RIP);
  write_GPR(64, REG_NORMAL(0), 0xFEDC_BA98_7654_3210);
  let expected_rmi_MEM = read_GPR(64, REG_NORMAL(0));
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 3, "MOV(r8, rm8): Wrong instruction length has been read");
  assert(decoded_instruction == MOV(8, rm_REG(REG_NORMAL(4)), rmi_MEM(expected_rmi_MEM)), "MOV(r8, rm8) instruction not decoded properly");
}

function test_decode_mov_r64_rm64() -> unit = {
  // Testing that MOV R12, M(R13) is decoded correctly
  let old_rip = RIP;
  let instruction: bits(24) = 0b0100_1101 @ 0x8B @ 0b00_100_101;
  write_instruction_to_memory(instruction, RIP);
  write_GPR(64, REG_NORMAL(5 + 8), 0xFEDC_BA98_7654_3210);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 3, "MOV(r64, rm64): Wrong instruction length has been read");
  let expected_rmi_MEM = read_GPR(64, REG_NORMAL(5 + 8));
  assert(decoded_instruction == MOV(64, rm_REG(REG_NORMAL(4 + 8)), rmi_MEM(expected_rmi_MEM)), "MOV(r64, rm64) instruction not decoded properly");
}

function test_decode_mov_r8_imm8() -> unit = {
  // Testing that MOV BH, 0x34 is decoded correctly
  let old_rip = RIP;
  let instruction: bits(16) = 0xB @ 0b0 @ 0b111 @ 0x34;
  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 2, "MOV(r8, imm8): Wrong instruction length has been read");
  assert(decoded_instruction == MOV(8, rm_REG(REG_HIGH_BYTE(7)), rmi_IMM(IMM8(0x34))), "MOV(r8, imm8) instruction not decoded properly");
}

function test_decode_mov_r32_imm32() -> unit = {
  // Testing that MOV R15D, 0x0000_0000 is decoded correctly
  let old_rip = RIP;
  let instruction: bits(48) = 0b0100_0001 @ 0xB @ 0b1 @ 0b111 @ reverse_endianness(0x0000_1111);
  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 6, "MOV(r32, imm32): Wrong instruction length has been read");
  assert(decoded_instruction == MOV(32, rm_REG(REG_NORMAL(15)), rmi_IMM(IMM32(0x0000_1111))), "MOV(r32, imm32) instruction not decoded properly");
}

/*===========================================================
Decode XOR, CMP, ADD, SUB tests
============================================================*/

enum group1instr = {
  TEST_XOR,
  TEST_CMP,
  TEST_ADD,
  TEST_SUB
}

function group1instr_to_string(instr: group1instr) -> string = {
  match instr {
    TEST_XOR => "XOR",
    TEST_CMP => "CMP",
    TEST_ADD => "ADD",
    TEST_SUB => "SUB"
  }
}

function test_decode_group1_rm8_r8(instr: group1instr) -> unit = {
  // Testing that instr m(R15 + 0x3A), AL is decoded correctly

  let opcode: bits(8) = match instr {
    TEST_XOR => 0x30,
    TEST_CMP => 0x38,
    TEST_ADD => 0x00,
    TEST_SUB => 0x28
  };

  let old_rip = RIP;
  let instruction: bits(32) = 0b0100_0001 @ opcode @ 0b01_000_111 @ 0x3A;
  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 4, concat_str(group1instr_to_string(instr),"(rm8, r8): Wrong instruction length has been read"));
  
  let expected_mem_addr = add_bits(R15, sail_sign_extend(0x3A, 64));
  let error_message = concat_str(group1instr_to_string(instr), "(rm8, r8) instruction not decoded properly");
  match instr {
    TEST_XOR => assert(decoded_instruction == XOR(false, 8, rm_MEM(expected_mem_addr), rmi_REG(REG_NORMAL(0))), error_message),
    TEST_CMP => assert(decoded_instruction == CMP(8, rm_MEM(expected_mem_addr), rmi_REG(REG_NORMAL(0))), error_message),
    TEST_ADD => assert(decoded_instruction == ADD(false, 8, rm_MEM(expected_mem_addr), rmi_REG(REG_NORMAL(0))), error_message),
    TEST_SUB => assert(decoded_instruction == SUB(false, 8, rm_MEM(expected_mem_addr), rmi_REG(REG_NORMAL(0))), error_message)
  }
}

function test_decode_group1_rm16_r16(instr: group1instr) -> unit = {
  // Testing that instr m(R15 + 0x3A), AX (with lock) is decoded correctly

  let opcode: bits(8) = match instr {
    TEST_XOR => 0x31,
    TEST_CMP => 0x39,
    TEST_ADD => 0x01,
    TEST_SUB => 0x29
  };

  let old_rip = RIP;

  let first_prefix: bits(8) = if instr == TEST_CMP then 0x40 else 0xF0;
  let instruction: bits(48) = first_prefix @ 0x66 @ 0b0100_0001 @ opcode @ 0b01_000_111 @ 0x3A;

  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 6, concat_str(group1instr_to_string(instr), "(rm16, r16): Wrong instruction length has been read"));

  let expected_mem_addr = add_bits(R15, sail_sign_extend(0x3A, 64));
  let error_message = concat_str(group1instr_to_string(instr), "(rm16, r16) instruction not decoded properly");
  match instr {
    TEST_XOR => assert(decoded_instruction == XOR(true, 16, rm_MEM(expected_mem_addr), rmi_REG(REG_NORMAL(0))), error_message),
    TEST_CMP => assert(decoded_instruction == CMP(16, rm_MEM(expected_mem_addr), rmi_REG(REG_NORMAL(0))), error_message),
    TEST_ADD => assert(decoded_instruction == ADD(true, 16, rm_MEM(expected_mem_addr), rmi_REG(REG_NORMAL(0))), error_message),
    TEST_SUB => assert(decoded_instruction == SUB(true, 16, rm_MEM(expected_mem_addr), rmi_REG(REG_NORMAL(0))), error_message)
  }
}

function test_decode_group1_r8_rm8(instr: group1instr) -> unit = {
  // Testing that instr AL, m(R15 + 0x3A) (with lock) is decoded correctly

  let opcode: bits(8) = match instr {
    TEST_XOR => 0x32,
    TEST_CMP => 0x3A,
    TEST_ADD => 0x02,
    TEST_SUB => 0x2A
  };

  let old_rip = RIP;

  let first_prefix: bits(8) = if instr == TEST_CMP then 0x40 else 0xF0;
  let instruction: bits(40) = first_prefix @ 0b0100_0001 @ opcode @ 0b01_000_111 @ 0x3A;

  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 5, concat_str(group1instr_to_string(instr),"(r8, rm8): Wrong instruction length has been read"));
  
  let expected_mem_addr = add_bits(R15, sail_sign_extend(0x3A, 64));
  let error_message = concat_str(group1instr_to_string(instr), "(r8, rm8) instruction not decoded properly");
  match instr {
    TEST_XOR => assert(decoded_instruction == XOR(true, 8, rm_REG(REG_NORMAL(0)), rmi_MEM(expected_mem_addr)), error_message),
    TEST_CMP => assert(decoded_instruction == CMP(8, rm_REG(REG_NORMAL(0)), rmi_MEM(expected_mem_addr)), error_message),
    TEST_ADD => assert(decoded_instruction == ADD(true, 8, rm_REG(REG_NORMAL(0)), rmi_MEM(expected_mem_addr)), error_message),
    TEST_SUB => assert(decoded_instruction == SUB(true, 8, rm_REG(REG_NORMAL(0)), rmi_MEM(expected_mem_addr)), error_message)
  }
}

function test_decode_group1_r64_rm64(instr: group1instr) -> unit = {
  // Testing that instr RAX, RDI is decoded correctly

  let opcode: bits(8) = match instr {
    TEST_XOR => 0x33,
    TEST_CMP => 0x3B,
    TEST_ADD => 0x03,
    TEST_SUB => 0x2B
  };

  let old_rip = RIP;
  let instruction: bits(24) = 0b0100_1000 @ opcode @ 0b11_000_111;
  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  assert(unsigned(new_rip) - unsigned(old_rip) == 3, concat_str(group1instr_to_string(instr), "(r64, rm64): Wrong instruction length has been read"));
  
  let error_message = concat_str(group1instr_to_string(instr), "(r64, rm64) instruction not decoded properly");
  match instr {
    TEST_XOR => assert(decoded_instruction == XOR(false, 64, rm_REG(REG_NORMAL(0)), rmi_REG(REG_NORMAL(7))), error_message),
    TEST_CMP => assert(decoded_instruction == CMP(64, rm_REG(REG_NORMAL(0)), rmi_REG(REG_NORMAL(7))), error_message),
    TEST_ADD => assert(decoded_instruction == ADD(false, 64, rm_REG(REG_NORMAL(0)), rmi_REG(REG_NORMAL(7))), error_message),
    TEST_SUB => assert(decoded_instruction == SUB(false, 64, rm_REG(REG_NORMAL(0)), rmi_REG(REG_NORMAL(7))), error_message)
  }
}

function test_decode_group1_rm8_imm8(instr: group1instr) -> unit = {
  // Testing that instr m(R15 + 0x3A), 0xFF is decoded correctly

  let reg_field: bits(3) = match instr {
    TEST_XOR => 0b110,
    TEST_CMP => 0b111,
    TEST_ADD => 0b000,
    TEST_SUB => 0b101
  };

  let old_rip = RIP;
  let instruction: bits(40) = 0b0100_0001 @ 0x80 @ 0b01 @ reg_field @ 0b111 @ 0x3A @ 0xFF;
  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  let expected_mem_addr = add_bits(R15, sail_sign_extend(0x3A, 64));
  assert(unsigned(new_rip) - unsigned(old_rip) == 5, concat_str(group1instr_to_string(instr), "(rm8, imm8): Wrong instruction length has been read"));

  let error_message = concat_str(group1instr_to_string(instr), "(rm8, imm8) instruction not decoded properly");
  match instr {
    TEST_XOR => assert(decoded_instruction == XOR(false, 8, rm_MEM(expected_mem_addr), rmi_IMM(IMM8(0xFF))), error_message),
    TEST_CMP => assert(decoded_instruction == CMP(8, rm_MEM(expected_mem_addr), rmi_IMM(IMM8(0xFF))), error_message),
    TEST_ADD => assert(decoded_instruction == ADD(false, 8, rm_MEM(expected_mem_addr), rmi_IMM(IMM8(0xFF))), error_message),
    TEST_SUB => assert(decoded_instruction == SUB(false, 8, rm_MEM(expected_mem_addr), rmi_IMM(IMM8(0xFF))), error_message)
  }
}

function test_decode_group1_rm64_imm32(instr: group1instr) -> unit = {
  // Testing that instr m(RAX * 2 + RCX), 0xABCD_1234 (with lock) is decoded correctly

  let reg_field: bits(3) = match instr {
    TEST_XOR => 0b110,
    TEST_CMP => 0b111,
    TEST_ADD => 0b000,
    TEST_SUB => 0b101
  };

  let old_rip = RIP;

  let first_prefix = if instr == TEST_CMP then 0x40 else 0xF0;
  let instruction: bits(72) = first_prefix @ 0b0100_1000 @ 0x81 @ 0b00 @ reg_field @ 0b100 @ 0b01_000_001 @ reverse_endianness(0xABCD_1234);
  write_instruction_to_memory(instruction, RIP);
  RAX = 0xFEDC_BA98_7654_3210;
  RCX = 0xF0F0_F0F0_EEEE_CCCC;
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;
  let expected_mem_addr = add_bits(add_bits(RAX, RAX), RCX);
  assert(unsigned(new_rip) - unsigned(old_rip) == 9, concat_str(group1instr_to_string(instr), "(rm64, imm32): Wrong instruction length has been read"));

  let error_message = concat_str(group1instr_to_string(instr), "(rm64, imm32) instruction not decoded properly");
  match instr {
    TEST_XOR => assert(decoded_instruction == XOR(true, 64, rm_MEM(expected_mem_addr), rmi_IMM(IMM32(0xABCD_1234))), error_message),
    TEST_CMP => assert(decoded_instruction == CMP(64, rm_MEM(expected_mem_addr), rmi_IMM(IMM32(0xABCD_1234))), error_message),
    TEST_ADD => assert(decoded_instruction == ADD(true, 64, rm_MEM(expected_mem_addr), rmi_IMM(IMM32(0xABCD_1234))), error_message),
    TEST_SUB => assert(decoded_instruction == SUB(true, 64, rm_MEM(expected_mem_addr), rmi_IMM(IMM32(0xABCD_1234))), error_message)
  }
}

/*===========================================================
Decode FENCE tests
============================================================*/

function test_decode_sfence() -> unit = {
  foreach (i from 0 to 7) {
    let old_rip = RIP;
    let instruction: bits(24) = 0x0F @ 0xAE @ 0b11_111 @ get_slice_int(3, i, 0);
    write_instruction_to_memory(instruction, RIP);
    let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
    RIP = new_rip;
    assert(unsigned(new_rip) - unsigned(old_rip) == 3, "SFENCE: Wrong instruction length has been read");
    assert(decoded_instruction == SFENCE(), "SFENCE instruction not decoded properly");
  }
}

function test_decode_lfence() -> unit = {
  foreach (i from 0 to 7) {
    let old_rip = RIP;
    let instruction: bits(24) = 0x0F @ 0xAE @ 0b11_101 @ get_slice_int(3, i, 0);
    write_instruction_to_memory(instruction, RIP);
    let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
    RIP = new_rip;
    assert(unsigned(new_rip) - unsigned(old_rip) == 3, "LFENCE: Wrong instruction length has been read");
    assert(decoded_instruction == LFENCE(), "LFENCE instruction not decoded properly");
  }
}

function test_decode_mfence() -> unit = {
  foreach (i from 0 to 7) {
    let old_rip = RIP;
    let instruction: bits(24) = 0x0F @ 0xAE @ 0b11_110 @ get_slice_int(3, i, 0);
    write_instruction_to_memory(instruction, RIP);
    let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
    RIP = new_rip;
    assert(unsigned(new_rip) - unsigned(old_rip) == 3, "MFENCE: Wrong instruction length has been read");
    assert(decoded_instruction == MFENCE(), "MFENCE instruction not decoded properly");
  }
}

/*===========================================================
Decode PUSH tests
============================================================*/

function test_decode_push_imm16() -> unit = {
  // Testing that PUSH IMM16(0x4567) is decoded correctly

  // Write prefix and opcode to memory
  let instruction: bits(32) = 0x66 @ 0x68 @ reverse_endianness(0x4567);
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 4, "PUSH(imm16): Wrong instruction length has been read");
  assert(decoded_instruction == PUSH(16, rmi_IMM(IMM16(0x4567))), "PUSH(imm16) instruction not decoded properly");
}

function test_decode_push_m64() -> unit = {
  // Testing that PUSH MEM64([RDI] + 0xFF (sign-extended)) is decoded correctly

  // Write to RDI
  write_GPR(64, REG_NORMAL(7), 0x1234_5678_9ABC_DEF0);
  // Write instruction to memory. Instruction consists of opcode, mod r/m byte, then 8-bit displacement
  let instruction: bits(24) = 0xFF @ 0b01_110_111 @ 0xFF;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;
  // Calculate expected memory address ([RDI] + 0xFF (sign-extended))
  let expected_mem_address = add_bits(read_GPR(64, REG_NORMAL(7)), sail_sign_extend(0xFF, 64));

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 3, "PUSH(m64): Wrong instruction length has been read");
  assert(decoded_instruction == PUSH(64, rmi_MEM(expected_mem_address)), "PUSH(m64) instruction not decoded properly");
}

function test_decode_push_r16() -> unit = {
  // Testing that PUSH REG16(R8) is decoded correctly

  // Write instruction to memory. Instruction consists of operand size override prefix, rex prefix, and opcode with embedded register location
  let instruction: bits(24) = 0x66 @ 0b0100_0001 @ 0x5 @ 0b0 @ 0b000;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 3, "PUSH(r16): Wrong instruction length has been read");
  assert(decoded_instruction == PUSH(16, rmi_REG(REG_NORMAL(8))), "PUSH(r16) instruction not decoded properly")
}

/*===========================================================
Decode POP tests
============================================================*/

function test_decode_pop_r16() -> unit = {
  // Testing that POP REG16(RSI) is decoded correctly

  // Write instruction to memory. Instruction consists of operand size override prefix, opcode, and mod r/m byte
  let instruction: bits(24) = 0x66 @ 0x8F @ 0b11_000_110;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // TEST
  assert(unsigned(new_rip) - unsigned(old_rip) == 3, "POP(r16): Wrong instruction length has been read");
  assert(decoded_instruction == POP(16, rm_REG(REG_NORMAL(6))), "POP(r16) not decoded properly")
}

function test_decode_pop_r64() -> unit = {
  // Testing that POP REG64(RAX) is decoded correctly

  // Write instruction to memory. Instruction consists of empty REX prefix, and opcode with embedded register location
  let instruction: bits(16) = 0b0100_0000 @ 0x5 @ 0b1 @ 0b000;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 2, "POP(r64): Wrong instruction length has been read");
  assert(decoded_instruction == POP(64, rm_REG(REG_NORMAL(0))), "POP(r64) not decoded properly")
}

/*===========================================================
Decode IMUL tests
============================================================*/

function test_decode_imul_r16_rm16() -> unit = {
  // Testing that IMUL AX, AX is decoded correctly

  // Write instruction to memory
  let instruction: bits(32) = 0x66 @ 0x0F @ 0xAF @ 0b11_000_000;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 4, "IMUL(r16, rm16): Wrong instruction length has been read");
  assert(decoded_instruction == IMUL(16, 0, rm_REG(REG_NORMAL(0))), "IMUL(r16, rm16) not decoded properly")
}

function test_decode_imul_r64_rm64() -> unit = {
  // Testing that IMUL R8, RAX is decoded correctly

  // Write instruction to memory
  let instruction: bits(32) = 0b0100_1100 @ 0x0F @ 0xAF @ 0b11_000_000;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 4, "IMUL(r64, rm64): Wrong instruction length has been read");
  assert(decoded_instruction == IMUL(64, 8, rm_REG(REG_NORMAL(0))), "IMUL(r64, rm64) not decoded properly")
}

/*===========================================================
Decode CALL test
============================================================*/

function test_decode_call_rel32() -> unit = {
  // Testing that CALL 0xFEFE_1010 is decoded correctly

  // Write instruction to memory
  let instruction: bits(40) = 0xE8 @ reverse_endianness(0xFEFE_1010);
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 5, "CALL(rel32): Wrong instruction length has been read");
  assert(decoded_instruction == CALL(0xFEFE_1010), "CALL(rel32) not decoded properly")
}

/*===========================================================
Decode LEAVE tests
============================================================*/

function test_decode_leave16() -> unit = {
  // Testing that LEAVE (operand size 16 - even if there is a REX prefix) is decoded correctly

  // Write instruction to memory
  let instruction: bits(24) = 0x66 @ 0x40 @ 0xC9;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 3, "LEAVE16: Wrong instruction length has been read");
  assert(decoded_instruction == LEAVE(16), "LEAVE16 not decoded properly")
}

function test_decode_leave64() -> unit = {
  // Testing that LEAVE (operand size 64 - default operand size) is decoded correctly

  // Write instruction to memory
  let instruction: bits(8) = 0xC9;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 1, "LEAVE64: Wrong instruction length has been read");
  assert(decoded_instruction == LEAVE(64), "LEAVE64 not decoded properly")
}

/*===========================================================
Decode RET test
============================================================*/

function test_decode_ret() -> unit = {
  // Write instruction to memory
  let instruction: bits(8) = 0xC3;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 1, "RET: Wrong instruction length has been read");
  assert(decoded_instruction == RET(), "RET not decoded properly")
}

/*===========================================================
Decode JMP test
============================================================*/

function test_decode_jmp_rel8() -> unit = {
  // Write instruction to memory
  let instruction: bits(16) = 0xEB @ 0xF0;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 2, "JMP(rel8): Wrong instruction length has been read");
  assert(decoded_instruction == JMP(0xF0), "JMP(rel8) not decoded properly")
}

/*===========================================================
Decode JNS test
============================================================*/

function test_decode_jns_rel8() -> unit = {
  // Write instruction to memory
  let instruction: bits(16) = 0x79 @ 0x7A;
  write_instruction_to_memory(instruction, RIP);
  let old_rip = RIP;

  // Decode
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  RIP = new_rip;

  // Test
  assert(unsigned(new_rip) - unsigned(old_rip) == 2, "JNS(rel8): Wrong instruction length has been read");
  assert(decoded_instruction == JNS(0x7A), "JNS(rel8) not decoded properly")
}

function test_decode() -> unit = {
  test_decode_mov_rm8_r8();
  test_decode_mov_rm32_r32();
  test_decode_mov_r8_rm8();
  test_decode_mov_r64_rm64();
  test_decode_mov_r8_imm8();
  test_decode_mov_r32_imm32();

  test_decode_group1_rm8_r8(TEST_XOR);
  test_decode_group1_rm16_r16(TEST_XOR);
  test_decode_group1_r8_rm8(TEST_XOR);
  test_decode_group1_r64_rm64(TEST_XOR);
  test_decode_group1_rm8_imm8(TEST_XOR);
  test_decode_group1_rm64_imm32(TEST_XOR);
  
  test_decode_sfence();
  test_decode_lfence();
  test_decode_mfence();

  test_decode_group1_rm8_r8(TEST_CMP);
  test_decode_group1_rm16_r16(TEST_CMP);
  test_decode_group1_r8_rm8(TEST_CMP);
  test_decode_group1_r64_rm64(TEST_CMP);
  test_decode_group1_rm8_imm8(TEST_CMP);
  test_decode_group1_rm64_imm32(TEST_CMP);

  test_decode_push_imm16();
  test_decode_push_m64();
  test_decode_push_r16();

  test_decode_pop_r16();
  test_decode_pop_r64();

  test_decode_group1_rm8_r8(TEST_ADD);
  test_decode_group1_rm16_r16(TEST_ADD);
  test_decode_group1_r8_rm8(TEST_ADD);
  test_decode_group1_r64_rm64(TEST_ADD);
  test_decode_group1_rm8_imm8(TEST_ADD);
  test_decode_group1_rm64_imm32(TEST_ADD);

  test_decode_group1_rm8_r8(TEST_SUB);
  test_decode_group1_rm16_r16(TEST_SUB);
  test_decode_group1_r8_rm8(TEST_SUB);
  test_decode_group1_r64_rm64(TEST_SUB);
  test_decode_group1_rm8_imm8(TEST_SUB);
  test_decode_group1_rm64_imm32(TEST_SUB);

  test_decode_imul_r16_rm16();
  test_decode_imul_r64_rm64();

  test_decode_call_rel32();

  test_decode_leave16();
  test_decode_leave64();

  test_decode_ret();

  test_decode_jmp_rel8();

  test_decode_jns_rel8();
}

function main() : unit -> unit = {
  test_execute();
  test_decode();
}
