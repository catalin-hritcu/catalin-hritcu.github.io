.PHONY: clean pulp

PDFLATEX = pdflatex -synctex=-1 $(OTHERFLAGS)

NAME = paper

# You can get pulp here: https://github.com/dmwit/pulp
PULP = "$(shell which pulp || echo \"$(HOME)\"~/.cabal/bin/pulp)"

pulp:
	rm -f $(NAME).log
	-$(PDFLATEX) -interaction nonstopmode $(NAME) &> /dev/null
	-$(PDFLATEX) -interaction nonstopmode $(NAME) &> /dev/null
	-$(PULP) $(NAME).log | grep -v "/usr/share/texmf-dist/tex/"

clean:
	rm -f *~ *.aux *.synctex *.log *.out *.pdf
