(lang dune 3.21)
(name rocq-sail-tiny-x86)
(using rocq 0.11)

(source (github rems-project/sail-tiny-x86))
(license "BSD-2-Clause")
(authors "Shreeka Lohani")
(maintainers "Shreeka Lohani <sl2189@cam.ac.uk>")

(package
 (name rocq-sail-tiny-x86)
 (synopsis " A very simplified and cut down version of the X86 ISA sail specification, handwritten")
 (depends
  (rocq-core (>= 9.0))
  (rocq-stdlib (>= 9.0))
  (sail (>= 0.20.1))
  sail_coq_backend
  sail_lem_backend
  sail_c_backend
  sail_lean_backend
  sail_smt_backend
  sail_sv_backend
  sail_ocaml_backend
  sail_latex_backend
  sail_output
  (rocq-stdpp (>= 1.10.0))
  (rocq-stdpp-bitvector (>= 1.10.0))
  (rocq-sail-stdpp (>= 0.20.1))
  (coq-record-update (>= 0.3.4))
 )
)

(generate_opam_files)
