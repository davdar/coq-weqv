pdf: darais-quals.pdf
darais-quals.pdf: darais-quals.tex darais-quals.bbl $(wildcard sections/*/*.tex) $(wildcard lib/*.tex) $(wildcard hs/*.hs)
	pdflatex -shell-escape darais-quals.tex

darais-quals.bbl: darais-quals.tex davdar.bib
	pdflatex -shell-escape darais-quals.tex
	bibtex darais-quals
	pdflatex -shell-escape darais-quals.tex

davdar.bib:
	curl http://www.citeulike.org/bibtex/user/davdar > davdar.bib

open: darais-quals.pdf
	open ./darais-quals.pdf

clean:
	rm *.aux *.log *.bbl *.blg *.bib darais-quals.pdf

touch:
	touch darais-quals.tex

.PHONY: pdf open clean touch

