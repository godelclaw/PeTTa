BUILD_DIR ?= build

.PHONY: all
all: runtime-types.pdf

runtime-types.pdf: runtime-types.tex
	mkdir -p $(BUILD_DIR)
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=$(BUILD_DIR) $<
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=$(BUILD_DIR) $<
	cp $(BUILD_DIR)/runtime-types.pdf $@
