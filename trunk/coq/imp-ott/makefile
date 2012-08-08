all: imp.pdf imp.v

imp.pdf: imp.tex
	pdflatex imp.tex

imp.tex: test10.ott
	ott test10.ott -o imp.tex

imp.v: test10.ott
	ott test10.ott -o imp.v
