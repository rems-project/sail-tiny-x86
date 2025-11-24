SAIL_DIR=`sail --dir`

type-check:
	sail prelude.sail operands.sail registers.sail tiny-x86.sail tests.sail

test: test.o
	./test.o;

test.o: test.c
	gcc test.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -o test.o;

test.c: prelude.sail operands.sail registers.sail tiny-x86.sail tests.sail
	sail -c prelude.sail operands.sail registers.sail tiny-x86.sail tests.sail -o test;

.PHONY: type-check test