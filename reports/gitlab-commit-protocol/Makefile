RM = rm -f
BUILD = pdflatex
BIB = bibtex
BUIL_OPTS := -file-line-error -halt-on-error -interaction=nonstopmode -recorder
SRC := gitlab-commit-protocol

.PHONY: all build clean show

all: clean build

build: $(SRC).pdf

$(SRC).pdf: $(SRC).tex
	$(BUILD) $(BUILD_OPTS) $(SRC).tex
	# $(BIB) wp
	# $(BUILD) $(BUILD_OPTS) wp.tex
	# $(BUILD) $(BUILD_OPTS) wp.tex

clean:
	$(RM) *.iml .DS_Store *.aux *.log *.bcf *.bbl *.fdb_latexmk *.fls *.run.xml *.blg wp.pdf
