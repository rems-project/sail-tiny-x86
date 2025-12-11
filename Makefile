SAIL_DIR=`sail --dir`
X86_FILES=prelude.sail registers.sail interface.sail operands.sail decode.sail tiny-x86.sail tests.sail

type-check:
	sail $(X86_FILES)

test: test.o
	./test.o;

test.o: test.c
	gcc test.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -o test.o;

test.c: $(X86_FILES)
	sail -c $(X86_FILES) -o test;

rocq: $(X86_FILES)
	sail -coq $(X86_FILES) -o test;

.PHONY: type-check test
