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
    // system flags and IOPL field
    ID: 21,
    VIP: 20,
    VIF: 19,
    AC: 18,
    VM: 17,
    RF: 16,
    NT: 14,
    IOPL: 13 .. 12,
    IF: 9,
    TF: 8,

    // status flags
    OF: 11,
    SF: 7,
    ZF: 6,
    AF: 4,
    PF: 2,
    CF: 0
}
register RFLAGS: rflags

/* Code Segment register - bits 0-1 contain CPL (Current Provilege Level) of the currently executing program*/
bitfield cs: bits(16) = {
    CPL: 1 .. 0
}
register CS: cs

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