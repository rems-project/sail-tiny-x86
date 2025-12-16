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

function decode_mov_rm32_r32() -> unit = {
  // Testing that MOV RBP, RSP is decoded correctly
  let old_rip = RIP;
  let instruction: bits(16) = 0x89 @ 0b11_100_101;
  write_instruction_to_memory(instruction, RIP);
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  assert(decoded_instruction == MOV(32, rm_REG(REG_NORMAL(5)), rmi_REG(REG_NORMAL(4))), "MOV(32, rm32, r32) instruction not decoded properly");
}

function decode_mov_r64_rm64() -> unit = {
  // Testing that MOV R12, M(R13) is decoded correctly
  let old_rip = RIP;
  let instruction: bits(24) = 0b0100_1101 @ 0x8B @ 0b00_100_101;
  write_instruction_to_memory(instruction, RIP);
  write_GPR(64, REG_NORMAL(5 + 8), 0xFEDC_BA98_7654_3210);
  let expected_rmi_MEM = read_GPR(64, REG_NORMAL(5 + 8));
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  assert(decoded_instruction == MOV(64, rm_REG(REG_NORMAL(4 + 8)), rmi_MEM(expected_rmi_MEM)), "MOV(64, r64, rm64) instruction not decoded properly");
}

function decode_push_imm16() -> unit = {
  // Testing that PUSH IMM16(0x4567) is decoded correctly
  // Write prefix and opcode to memory
  let instruction: bits(16) = 0x66 @ 0x68;
  write_instruction_to_memory(instruction, RIP);
  // Write immediate value to memory
  let imm = 0x4567;
  write_memory(2, RIP + 2, imm, create_writeAccessDescriptor());
  // Decode and test
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  assert(decoded_instruction == PUSH(16, rmi_IMM(IMM16(0x4567))), "PUSH(16, imm16) instruction not decoded properly");
}

function decode_push_m64() -> unit = {
  // Testing that PUSH MEM64([RDI] + 0xFF (sign-extended)) is decoded correctly
  // Write to RDI
  write_GPR(64, REG_NORMAL(7), 0x1234_5678_9ABC_DEF0);
  // Write instruction to memory. Instruction consists of opcode, mod r/m byte, then 8-bit displacement
  let instruction: bits(24) = 0xFF @ 0b01_110_111 @ 0xFF;
  write_instruction_to_memory(instruction, RIP);
  // Calculate expected memory address ([RDI] + 0xFF (sign-extended))
  let expected_mem_address = add_bits(read_GPR(64, REG_NORMAL(7)), sail_sign_extend(0xFF, 64));
  // Decode and test
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  assert(decoded_instruction == PUSH(64, rmi_MEM(expected_mem_address)), "PUSH(64, m64) instruction not decoded properly");
}

function decode_push_r16() -> unit = {
  // Testing that PUSH REG16(R8) is decoded correctly
  // Write instruction to memory. Instruction consists of operand size override prefix, rex prefix, and opcode with embedded register location
  let instruction: bits(24) = 0x66 @ 0b0100_0001 @ 0x5 @ 0b0 @ 0b000;
  write_instruction_to_memory(instruction, RIP);
  // Decode and test
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  assert(decoded_instruction == PUSH(16, rmi_REG(REG_NORMAL(8))), "PUSH(16, r16) instruction not decoded properly")
}

function decode_pop_r16() -> unit = {
  // Testing that POP REG16(RSI) is decoded correctly
  // Write instruction to memory. Instruction consists of operand size override prefix, opcode, and mod r/m byte
  let instruction: bits(24) = 0x66 @ 0x8F @ 0b11_000_110;
  write_instruction_to_memory(instruction, RIP);
  // Decode and test
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  assert(decoded_instruction == POP(16, rm_REG(REG_NORMAL(6))), "POP(16, r16) not decoded properly")
}

function decode_pop_r64() -> unit = {
  // Testing that POP REG64(RAX) is decoded correctly
  // Write instruction to memory. Instruction consists of empty REX prefix, and opcode with embedded register location
  let instruction: bits(16) = 0b0100_0000 @ 0x5 @ 0b1 @ 0b000;
  write_instruction_to_memory(instruction, RIP);
  // Decode and test
  let (new_rip, decoded_instruction) = unwrap_decoded_instr(decode(RIP));
  assert(decoded_instruction == POP(64, rm_REG(REG_NORMAL(0))), "POP(64, r64) not decoded properly")
}

function test_decode() -> unit = {
  decode_mov_rm32_r32();
  decode_mov_r64_rm64();
  decode_push_imm16();
  decode_push_m64();
  decode_push_r16();
  decode_pop_r16();
  decode_pop_r64();
}

function main() : unit -> unit = {
  test_execute();
  test_decode();
}
