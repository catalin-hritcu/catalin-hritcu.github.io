include $(FSTAR_HOME)/ulib/ml/Makefile.include

all:
	fstar.exe Heap.fsti
	fstar.exe Heap2.fsti
	fstar.exe ST.fsti
	fstar.exe IncrST.fst
	fstar.exe Incr2ST.fst
	fstar.exe SwapIntRefsST.fst
	fstar.exe SwapRefsST.fst
	fstar.exe CountST.fst
	fstar.exe FibonacciST.fst
	fstar.exe InvariantsST.fst

swap:
	$(MAKE) -C $(ULIB_ML)
	mkdir -p out
	fstar.exe $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml SwapIntRefsST.fst
	$(OCAMLOPT) out/SwapIntRefsST.ml -o SwapIntRefsST.exe
	./SwapIntRefsST.exe

clean:
	rm -dfr *~ *.exe out
