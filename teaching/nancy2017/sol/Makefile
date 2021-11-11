
FSTAR_HOME=/home/hritcu/Projects/fstar/pub

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: init-freeze factorial
	fstar.exe --verify_all Incr.fst Ex04c.fst RefinedStackLengthClient.fst RefinedStackLength.fst

factorial: # this one is flaky because of nonlinear arithmetic
	fstar.exe FactorialST.fst

init-freeze:
	fstar.exe InitFreeze.fst
