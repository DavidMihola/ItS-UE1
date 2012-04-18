all: tex
	pdflatex cypher.tex

tex:
	lhs2TeX -o cypher.tex cypher.lhs

clean:
	rm cypher.tex cypher.pdf
