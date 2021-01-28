

file=./handin
bib=bibtex

quiet=-synctex=1 -interaction=nonstopmode
flags=--shell-escape
cc=pdflatex $(flags)

compile:
	$(cc) $(file).tex
	$(cc) $(file).tex

quiet:
	$(cc) $(quiet) $(file).tex
	$(cc) $(quiet) $(file).tex

rebib:
	rm -f ./*.bbl
	$(cc)  $(file).tex
	$(bib) $(file)

clean:
	rm -f ./*.aux
	rm -f ./*.log
	rm -f ./*.out
	rm -f ./*.zip
	rm -f ./*.pdf
	rm -f ./*.pyg

handin:
	$(MAKE) clean
	$(MAKE) rebib
	$(MAKE) compile
