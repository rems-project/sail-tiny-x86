function write_then_read_mem() -> unit = {
  let mem_addr = 0x0000_0000_0000_0007;
  let value = 0x0000_0000_0000_0004;
  write_memory(8, mem_addr, value, create_writeAccessDescriptor());
  let read_value: bits(64) = read_memory(8, mem_addr, create_readAccessDescriptor());
  assert(read_value == value, "Writing then reading from the same memory address was inconsistent");
}

function main() : unit -> unit = {
  write_then_read_mem()
}