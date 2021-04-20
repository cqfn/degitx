RM = rm -f
BUILD = pdflatex
BIB = bibtex
BUIL_OPTS := -file-line-error -halt-on-error -interaction=nonstopmode -recorder
SRC := 3pc-evaluation
SRC_TEX := $(SRC).tex
TARGET := $(SRC).pdf

.PHONY: all build clean show

all: clean build

build: $(TARGET)


$(TARGET): $(SRC_TEX)
	$(BUILD) $(BUILD_OPTS) $(SRC_TEX)
	$(BIB) $(SRC)
	$(BUILD) $(BUILD_OPTS) $(SRC_TEX)
	$(BUILD) $(BUILD_OPTS) $(SRC_TEX)

clean:
	$(RM) *.iml .DS_Store *.aux *.log *.bcf *.bbl *.fdb_latexmk *.fls *.run.xml *.blg wp.pdf
