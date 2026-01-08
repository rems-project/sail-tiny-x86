default Order dec // LSB is index 0
$define CONCURRENCY_INTERFACE_V2 // use concurrency_interface/read_write_v2.sail instead of v1
$include <prelude.sail>
$include <reverse_endianness.sail>

// use equality overload from sail-tiny-arm
val eq_any = pure {ocaml: "(fun (x, y) -> x = y)", interpreter: "eq_anything", lem: "eq", coq: "generic_eq", lean: "BEq.beq", c: "eq_anything"} : forall ('a : Type). ('a, 'a) -> bool
val eq_bits_int : forall 'n 'm, 'n >= 0 & 'm >= 0. (bits('n), int('m)) -> bool
function eq_bits_int (x, y) = (unsigned(x) == y)
overload operator == = {eq_any, eq_bits_int}

overload operator != = {not_bool}

overload operator / = {tdiv_int}

val mod: (int, int) -> int
function mod(x, y) = tmod_int(x, y)

val fail: forall 'a. string -> 'a
function fail(message) = {
    assert(false, message);
    exit()
}

val flip_bit: bit -> bit
function flip_bit(bit_to_flip) = {
    if bit_to_flip == bitzero then bitone else bitzero;
}
