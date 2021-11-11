# This uses Madoko (https://madoko.codeplex.com/)

deck:
	@madoko fstar-tfp.mdk --odir=out | grep -v "warning: unable to read language definition: fstar" | true
	@sed -i "s/lib\/font\/source-sans-pro\/source-sans-pro\.css/slides\/reveal.js\/lib\/font\/source-sans-pro\/source-sans-pro.css/g" out/fstar-tfp.html

clean:
	rm -f *~ css.sty madoko.css madoko.sty *math-dvi.tex *math-pdf.tex *math-dvi.final.tex *math-pdf.final.tex  *.aux *.dim *.dvi *.log *.out *.upa *.dimx *.html *.log *.pdf *.upa *.upb *.bbl *.blg .*~
	rm -dfr math
