SAIL_DIR=`sail --dir`
MODEL=$(shell cat sail_files)
MODEL_WITH_TEST=$(MODEL) tests.sail
# Those 2 are picked up by dune, hence the export
export SAIL_OPTS=--strict-var
export SAIL_COQ_OPTS=--coq-record-update

default: rocq

rocq:
	dune build;

rocq-snapshot:
	@# First build the file and then check that they match
	-dune build @snapshot --auto-promote
	@dune build @snapshot

type-check:
	sail $(SAIL_OPTS) --just-check $(MODEL_WITH_TEST)

test: testing/test.o
	testing/test.o;

testing/test.o: testing/test.c
	gcc testing/test.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -o testing/test.o;

testing/test.c: $(MODEL_WITH_TEST)
	mkdir -p testing && \
	sail -c $(MODEL_WITH_TEST) -o testing/test;

.PHONY: default rocq rocq-snapshot type-check test
