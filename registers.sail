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

/* status flags, part of register RFLAGS (which is mostly restricted access) */
// could use bitfield for this
register CF: bits(1) // bit 0
register PF: bits(1) // bit 2
register AF: bits(1) // bit 4
register ZF: bits(1) // bit 6
register SF: bits(1) // bit 7
register OF: bits(1) // bit 11

/*
read and write least-significant 8,16,32,64 (32 with 0 extend for write) bits 
 */

 val read_reg: forall 'm, 'm in {8, 16, 32, 64}. (int('m), reg_index) -> bits('m)

 function read_reg(wsize, i: reg_index) = {
    let reg = *GPRs[i];
    reg[wsize - 1 .. 0]
}

val write_reg: forall 'm, 'm in {8, 16, 32, 64}. (int('m), reg_index, bits('m)) -> unit

function write_reg(wsize, i: reg_index, value) = {
    if wsize == 32 then {
        // if writing 32 bits to a register, the value to be written is zero-extended to 64 bits
        (*GPRs[i])[63 .. 32]= 0x0000_0000;
        (*GPRs[i])[31 .. 0]= value;
    }
    else
        // the value is written to the last wsize bits of the register
        (*GPRs[i])[wsize - 1 .. 0] = value;
}