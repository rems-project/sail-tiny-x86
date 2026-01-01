/* range of registers that one can refer to */
type reg_index = range(0, 15)

// operand representation of register locations
union reg = {
    REG_HIGH_BYTE: range(4, 7),
    REG_NORMAL: reg_index
}

/* program counter */

register RIP: bits(64)

/* general purpose registers, in ascending index order */

register RAX: bits(64)
register RCX: bits(64)
register RDX: bits(64)
register RBX: bits(64)
register RSP: bits(64)
register RBP: bits(64)
register RSI: bits(64)
register RDI: bits(64)

register R8: bits(64)
register R9: bits(64)
register R10: bits(64)
register R11: bits(64)
register R12: bits(64)
register R13: bits(64)
register R14: bits(64)
register R15: bits(64)

let GPRs : vector(16, register(bits(64))) = [
    ref R15,
    ref R14,
    ref R13,
    ref R12,
    ref R11,
    ref R10,
    ref R9,
    ref R8,
    ref RDI,
    ref RSI,
    ref RBP,
    ref RSP,
    ref RBX,
    ref RDX,
    ref RCX,
    ref RAX
]

/* register RFLAGS, system and status flags + mostly restricted access */
bitfield rflags : bits(64) = {
    // status flags
    OF: 11, // overflow flag (for operations between signed values)
    SF: 7, // sign flag
    ZF: 6, // zero flag
    AF: 4, // auxiliary carry flag
    PF: 2, // parity flag
    CF: 0 // carry flag (for operations between unsigned values)
}
register RFLAGS: rflags

/* read and write least-significant 8,16,32,64 (32 with 0 extend for write) bits */
 val read_GPR: forall 'm, 'm in {8, 16, 32, 64}. (int('m), reg) -> bits('m)

 function read_GPR(operand_size, reg) = {
    match reg {
        // read lowest operand_size bits from register
        REG_NORMAL(i) => {
            let reg = *GPRs[i];
            reg[operand_size - 1 .. 0]
        },
        // read 8 bits from register. Read high byte depending on reg_index (i)
        REG_HIGH_BYTE(i) => {
            assert(operand_size == 8, "Register is high byte enabled but operand size is not 8 bits");
            // Read high byte register
            // AH = RAX[15 .. 8], CH = RCX[15 .. 8], DH = RDX[15 .. 8], BH = RBX[15 .. 8]
            let reg = *GPRs[i - 4];
            (*GPRs[i - 4])[15 .. 8]
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
        // write 8 bits to a register. Write to low or high byte depending on reg_index (i)
        REG_HIGH_BYTE(i) => {
            assert(operand_size == 8, "Register is high byte enabled but operand size is not 8 bits");
            // Write to high byte register
            // AH = RAX[15 .. 8], CH = RCX[15 .. 8], DH = RDX[15 .. 8], BH = RBX[15 .. 8]
            (*GPRs[i - 4])[15 .. 8] = value;
        }
    }
}


/* UPDATE RFLAGS */

/* Update sign flag depending on the result of an operation */
val update_sign_flag: forall 'm, 'm > 0. (implicit('m), bits('m)) -> unit
function update_sign_flag(operand_size, result) = {
    // sign flag = msb of result (0 = +ve, 1 = -ve)
    RFLAGS[SF] = [result[operand_size - 1]];
}

/* Update overflow flag depending on the result of an operation
Overflow flag is for signed values. */

val update_overflow_flag_add_inner: (bit, bit, bit) -> unit
function update_overflow_flag_add_inner(first_msb, second_msb, result_msb) = {
    /* set overflow flag if, when ADDING first and second operand, 
    first and second operand have the same sign, 
    but the sign of the result is different */
    RFLAGS[OF] = 
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
    RFLAGS[CF] = if unsigned(first) < unsigned(second) then 0b1 else 0b0;
}

val update_carry_flag_add: forall 'm, 'm > 0. (implicit('m), bits('m), bits('m)) -> unit
function update_carry_flag_add(size, first, second) = {
    // set carry flag if actual result is too large to fit in size bits, else clear
    RFLAGS[CF] = if unsigned(first) + unsigned(second) > 2^size - 1 then 0b1 else 0b0;
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
    RFLAGS[ZF] = if result == sail_zero_extend(0x0, operand_size) then 0b1 else 0b0;
}

/* Update parity flag depending on the result of an operation */
val update_parity_flag: forall 'm, 'm >= 8. bits('m) -> unit
function update_parity_flag(result) = {
    // we set if least significant byte of result has an even number of 1s, else clear
    var even_parity = bitone;
    foreach (i from 0 to 7) {
        if result[i] == bitone then even_parity = flip_bit(even_parity);
    };
    RFLAGS[PF] = [even_parity];
}

/* Update RFLAGS for sub and add operations */

val update_RFLAGS_sub: forall 'm, 'm >=8. (bits('m), bits('m), bits('m)) -> unit
function update_RFLAGS_sub(first, second, result) = {
    update_sign_flag(result);
    update_overflow_flag_sub(first, second, result);
    update_carry_flag_sub(first, second);
    update_zero_flag(result);
    update_aux_carry_flag_sub(first, second);
    update_parity_flag(result);
}

val update_RFLAGS_add: forall 'm, 'm >=8. (bits('m), bits('m), bits('m)) -> unit
function update_RFLAGS_add(first, second, result) = {
    update_sign_flag(result);
    update_overflow_flag_add(first, second, result);
    update_carry_flag_add(first, second);
    update_zero_flag(result);
    update_aux_carry_flag_add(first, second);
    update_parity_flag(result);
}