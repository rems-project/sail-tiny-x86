(lang dune 3.8)
(name coq-sail-tiny-x86)
(using coq 0.8)

(source (github rems-project/sail-tiny-x86))
(license "BSD-2-Clause")
(authors "Shreeka Lohani")
(maintainers "Shreeka Lohani <sl2189@cam.ac.uk>")

(package
 (name coq-sail-tiny-x86)
 (synopsis " A very simplified and cut down version of the X86 ISA sail specification, handwritten")
 (depends
  (coq (>= 9.0))
  (sail (>= 0.19.1))
  sail_coq_backend
  sail_lem_backend
  sail_c_backend
  sail_lean_backend
  sail_smt_backend
  sail_sv_backend
  sail_ocaml_backend
  sail_latex_backend
  sail_output
  (coq-stdpp (>= 1.10.0))
  (coq-stdpp-bitvector (>= 1.10.0))
  (coq-sail-stdpp (>= 0.19.1))
  (coq-record-update (>= 0.3.4))
 )
)

(generate_opam_files)
