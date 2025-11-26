SAIL_DIR=`sail --dir`
X86_FILES=prelude.sail operand_types.sail registers.sail interface.sail operands.sail tiny-x86.sail tests.sail

type-check:
	sail $(X86_FILES)

test: test.o
	./test.o;

test.o: test.c
	gcc test.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -o test.o;

test.c: prelude.sail operand_types.sail registers.sail interface.sail operands.sail tiny-x86.sail tests.sail
	sail -c $(X86_FILES) -o test;

.PHONY: type-check test