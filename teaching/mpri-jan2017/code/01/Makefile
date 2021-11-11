FSTAR_HOME=/home/hritcu/Projects/fstar/pub

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all:
	fstar.exe --verify_all Fun.fst Types.fst Purity.fst Divergence.fst Stack.fst StackClient.fst Swap2.fst Swap3.fst

divergence:
#	$(MAKE) -C $(ULIB_ML)
	mkdir -p out
	fstar.exe $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Divergence.fst
	$(OCAMLOPT) out/Divergence.ml -w p -o Divergence.exe
	./Divergence.exe

clean:
	rm -dfr *~ *.exe out
