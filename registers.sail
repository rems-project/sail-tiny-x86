/* range of registers that one can refer to */
type reg_index = range(0, 15)

// operand representation of register locations
union reg = {
    REG_HIGH_BYTE: range(0, 3),
    REG_NORMAL: reg_index
}

/* program counter */

register rip: bits(64)

/* general purpose registers, in ascending index order */

register rax: bits(64)
register rcx: bits(64)
register rdx: bits(64)
register rbx: bits(64)
register rsp: bits(64)
register rbp: bits(64)
register rsi: bits(64)
register rdi: bits(64)

register r8: bits(64)
register r9: bits(64)
register r10: bits(64)
register r11: bits(64)
register r12: bits(64)
register r13: bits(64)
register r14: bits(64)
register r15: bits(64)

let GPRs : vector(16, register(bits(64))) = [
    ref r15,
    ref r14,
    ref r13,
    ref r12,
    ref r11,
    ref r10,
    ref r9,
    ref r8,
    ref rdi,
    ref rsi,
    ref rbp,
    ref rsp,
    ref rbx,
    ref rdx,
    ref rcx,
    ref rax
]

/* register rflags, system and status flags + mostly restricted access */
bitfield rflags_type : bits(64) = {
    // status flags
    OF: 11, // overflow flag (for operations between signed values)
    SF: 7, // sign flag
    ZF: 6, // zero flag
    AF: 4, // auxiliary carry flag
    PF: 2, // parity flag
    CF: 0 // carry flag (for operations between unsigned values)
}
register rflags: rflags_type

/* read and write least-significant 8,16,32,64 (32 with 0 extend for write) bits */
 val read_GPR: forall 'm, 'm in {8, 16, 32, 64}. (int('m), reg) -> bits('m)

 function read_GPR(operand_size, reg) = {
    match reg {
        // read lowest operand_size bits from register
        REG_NORMAL(i) => {
            let reg = *GPRs[i];
            reg[operand_size - 1 .. 0]
        },
        // read 8 bits from the high byte of a register
        REG_HIGH_BYTE(i) => {
            assert(operand_size == 8, "Register is high byte enabled but operand size is not 8 bits");
            // Read high byte register
            // AH = rax[15 .. 8], CH = rcx[15 .. 8], DH = rdx[15 .. 8], BH = rbx[15 .. 8]
            let reg = *GPRs[i];
            reg[15 .. 8]
        }
    }
}

val write_GPR: forall 'm, 'm in {8, 16, 32, 64}. (int('m), reg, bits('m)) -> unit

function write_GPR(operand_size, reg, value) = {
    match reg {
        // write to the lowest 8 or 16 bits of a register, or write 32 or 64 bits to a register
        REG_NORMAL(i) => {
            if operand_size == 32 then {
                // if writing 32 bits to a register, the value to be written is zero-extended to 64 bits
                (*GPRs[i])[63 .. 32] = 0x0000_0000;
                (*GPRs[i])[31 .. 0] = value;
            }
            else
                // the value is written to the last operand_size bits of the register
                (*GPRs[i])[operand_size - 1 .. 0] = value;
        },
        // write 8 bits to the high byte of a register
        REG_HIGH_BYTE(i) => {
            assert(operand_size == 8, "Register is high byte enabled but operand size is not 8 bits");
            // Write to high byte register
            // AH = rax[15 .. 8], CH = rcx[15 .. 8], DH = rdx[15 .. 8], BH = rbx[15 .. 8]
            (*GPRs[i])[15 .. 8] = value;
        }
    }
}


/* UPDATE rflags */

/* Update sign flag depending on the result of an operation */
val update_sign_flag: forall 'm, 'm > 0. (implicit('m), bits('m)) -> unit
function update_sign_flag(operand_size, result) = {
    // sign flag = msb of result (0 = +ve, 1 = -ve)
    rflags[SF] = [result[operand_size - 1]];
}

/* Update overflow flag depending on the result of an operation
Overflow flag is for signed values. */

val update_overflow_flag_add_inner: (bit, bit, bit) -> unit
function update_overflow_flag_add_inner(first_msb, second_msb, result_msb) = {
    /* set overflow flag if, when ADDING first and second operand, 
    first and second operand have the same sign, 
    but the sign of the result is different */
    rflags[OF] = 
        if (first_msb == second_msb) & not_bool(result_msb == first_msb) then 
            0b1 
        else 
            0b0;
}

val update_overflow_flag_sub: forall 'm, 'm > 0. (implicit('m), bits('m), bits('m), bits('m)) -> unit
function update_overflow_flag_sub(size, first, second, result) = 
    update_overflow_flag_add_inner(
        first[size - 1], 
        flip_bit(second[size - 1]), // first - second = first + (- second)
        result[size - 1]
    )

val update_overflow_flag_add: forall 'm, 'm > 0. (implicit('m), bits('m), bits('m), bits('m)) -> unit
function update_overflow_flag_add(size, first, second, result) = 
    update_overflow_flag_add_inner(
        first[size - 1], 
        second[size - 1], 
        result[size - 1]
    )

/* Update carry flag depending on the result of an operation.
Carry flag is for unsigned values (so underlying logic is different for sub and add). */

val update_carry_flag_sub: forall 'm, 'm > 0. (bits('m), bits('m)) -> unit
function update_carry_flag_sub(first, second) = {
    // set carry flag if result < 0 (as it represents a borrow when subtracting 2 unsigned values), else clear
    rflags[CF] = if unsigned(first) < unsigned(second) then 0b1 else 0b0;
}

val update_carry_flag_add: forall 'm, 'm > 0. (implicit('m), bits('m), bits('m)) -> unit
function update_carry_flag_add(size, first, second) = {
    // set carry flag if actual result is too large to fit in size bits, else clear
    rflags[CF] = if unsigned(first) + unsigned(second) > 2^size - 1 then 0b1 else 0b0;
}

/* Update auxiliary carry flag depending on the result of an operation.
Same operation as the carry flag but only concerned with least significant 4 bits of each parameter */

val update_aux_carry_flag_sub: forall 'm, 'm >= 4. (bits('m), bits('m)) -> unit
function update_aux_carry_flag_sub(first, second) = update_carry_flag_sub(first[3..0], second[3..0])

val update_aux_carry_flag_add: forall 'm, 'm >= 4. (bits('m), bits('m)) -> unit
function update_aux_carry_flag_add(first, second) = update_carry_flag_add(first[3..0], second[3..0])

/* Update zero flag depending on the result of an operation */
val update_zero_flag: forall 'm, 'm >= 8. (implicit('m), bits('m)) -> unit
function update_zero_flag(operand_size, result) = {
    // set zero flag if result = 0, else clear zero flag
    rflags[ZF] = if result == sail_zero_extend(0x0, operand_size) then 0b1 else 0b0;
}

/* Update parity flag depending on the result of an operation */
val update_parity_flag: forall 'm, 'm >= 8. bits('m) -> unit
function update_parity_flag(result) = {
    // we set if least significant byte of result has an even number of 1s, else clear
    var even_parity = bitone;
    foreach (i from 0 to 7) {
        if result[i] == bitone then even_parity = flip_bit(even_parity);
    };
    rflags[PF] = [even_parity];
}

/* Update rflags for sub and add operations */

val update_rflags_sub: forall 'm, 'm >=8. (bits('m), bits('m), bits('m)) -> unit
function update_rflags_sub(first, second, result) = {
    update_sign_flag(result);
    update_overflow_flag_sub(first, second, result);
    update_carry_flag_sub(first, second);
    update_zero_flag(result);
    update_aux_carry_flag_sub(first, second);
    update_parity_flag(result);
}

val update_rflags_add: forall 'm, 'm >=8. (bits('m), bits('m), bits('m)) -> unit
function update_rflags_add(first, second, result) = {
    update_sign_flag(result);
    update_overflow_flag_add(first, second, result);
    update_carry_flag_add(first, second);
    update_zero_flag(result);
    update_aux_carry_flag_add(first, second);
    update_parity_flag(result);
}