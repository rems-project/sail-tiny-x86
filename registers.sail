/* register pointer type */
type reg_ref = register(bits(64))

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
 val read_reg: forall 'm, 'm in {8, 16, 32, 64}. (int('m), reg_ref) -> bits('m)

 function read_reg(wsize, reg_ref) = {
    (*reg_ref)[wsize - 1 .. 0]
}

val write_reg: forall 'm, 'm in {8, 16, 32, 64}. (int('m), reg_ref, bits('m)) -> unit

function write_reg(wsize, reg_ref, value) = {
    if wsize == 32 then {
        // if writing 32 bits to a register, the value to be written is zero-extended to 64 bits
        (*reg_ref)[63 .. 32] = 0x0000_0000;
        (*reg_ref)[31 .. 0] = value;
    }
    else
        // the value is written to the last wsize bits of the register
        (*reg_ref)[wsize - 1 .. 0] = value;
}

/* change the value of the parity flag depending on the result of an operation */
val modify_parity_flag: forall 'm, 'm >= 8. bits('m) -> unit
function modify_parity_flag(result) = {
    // we set if least significant byte of result has an even number of 1s, else clear
    var even_parity = bitone;
    foreach (i from 0 to 7) {
        if result[i] == bitone then even_parity = flip_bit(even_parity);
    };
    RFLAGS[PF] = [even_parity];
}