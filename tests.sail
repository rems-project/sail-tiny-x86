function main() : unit -> unit = {
  let x: imm = IMM16(0x0002);
  let y: bits(64) = 0x0000_0000_0000_0007;
  print_bits("",y + 0x0000_0000_0000_0004)
}