# This uses Madoko (https://madoko.codeplex.com/)

deck:
	@madoko slides01.mdk --odir=out/01 | grep -v "warning: unable to read language definition: fstar" | true
	@sed -i "s/lib\/font\/source-sans-pro\/source-sans-pro\.css/slides\/reveal.js\/lib\/font\/source-sans-pro\/source-sans-pro.css/g" out/01/slides01.html
	@madoko slides02.mdk --odir=out/02 | grep -v "warning: unable to read language definition: fstar" | true
	@sed -i "s/lib\/font\/source-sans-pro\/source-sans-pro\.css/slides\/reveal.js\/lib\/font\/source-sans-pro\/source-sans-pro.css/g" out/02/slides02.html
	@madoko slides04.mdk --odir=out/04 | grep -v "warning: unable to read language definition: fstar" | true
	@sed -i "s/lib\/font\/source-sans-pro\/source-sans-pro\.css/slides\/reveal.js\/lib\/font\/source-sans-pro\/source-sans-pro.css/g" out/04/slides04.html

clean:
	rm -f *~ css.sty madoko.css madoko.sty *math-dvi.tex *math-pdf.tex *math-dvi.final.tex *math-pdf.final.tex  *.aux *.dim *.dvi *.log *.out *.upa *.dimx *.html *.log *.pdf *.upa *.upb *.bbl *.blg .*~
	rm -dfr math
