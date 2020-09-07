RM = rm -f
BROWSER = firefox-bin

.PHONY: all build clean show

all: build

build: wp.tex
	latexmk -pdf wp.tex

show: build
	$(BROWSER) ${PWD}/wp.pdf

clean:
	$(RM) *.iml .DS_Store *.aux *.log *.bcf *.bbl *.fdb_latexmk *.fls *.run.xml *.blg wp.pdf
