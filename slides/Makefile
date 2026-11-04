TEX := symmetry-slides.tex
PDF := symmetry-slides.pdf
BOOK_ARGS := $(if $(BOOK),--book "$(BOOK)",)

.PHONY: all pdf check-sync refresh-snapshot clean

all: check-sync pdf

pdf: $(PDF)

$(PDF): $(TEX) preamble.tex ../VERSION $(wildcard sections/*.tex) ../references.bib ../lean/generated/lean-ledger-counts.tex $(wildcard ../results/figures/*)
	pdflatex -interaction=nonstopmode -halt-on-error $(TEX)
	bibtex symmetry-slides
	pdflatex -interaction=nonstopmode -halt-on-error $(TEX)
	pdflatex -interaction=nonstopmode -halt-on-error $(TEX)

check-sync:
	./check-book-sync.sh $(BOOK_ARGS)

refresh-snapshot:
	./check-book-sync.sh --write $(BOOK_ARGS)

clean:
	rm -f symmetry-slides.aux symmetry-slides.bbl symmetry-slides.blg
	rm -f symmetry-slides.log symmetry-slides.nav symmetry-slides.out
	rm -f symmetry-slides.snm symmetry-slides.toc symmetry-slides.vrb
	rm -f symmetry-slides.pdf
