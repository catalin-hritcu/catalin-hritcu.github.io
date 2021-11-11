include $(FSTAR_HOME)/ulib/ml/Makefile.include

all:
	fstar.exe Fact.fst
	fstar.exe Fun.fst
	fstar.exe Types.fst
	fstar.exe Purity.fst
	fstar.exe Divergence.fst
	fstar.exe DivergenceEvalClosed.fst
	fstar.exe Rev.fst
	fstar.exe AppendLength.fst
	fstar.exe Stack.fst
	fstar.exe StackClient.fst
	fstar.exe RefinedStackClient.fst
	fstar.exe RefinedStack.fst
	fstar.exe AbstractStack.fst
	fstar.exe AbstractStackClient.fst

divergence:
	$(MAKE) -C $(ULIB_ML)
	mkdir -p out
	fstar.exe $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Divergence.fst
	$(OCAMLOPT) out/Divergence.ml -w p -o Divergence.exe
	./Divergence.exe

clean:
	rm -dfr *~ *.exe out
