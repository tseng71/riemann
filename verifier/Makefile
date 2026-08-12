.PHONY: test verify cross paper clean

PYTHON ?= python3.12

test:
	PYTHONPATH=src $(PYTHON) -m unittest discover -s tests -v

verify:
	PYTHONPATH=src $(PYTHON) scripts/verify_release.py

cross:
	PYTHONPATH=src $(PYTHON) scripts/verify_cross_precision.py

paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -cd ../paper/riemann.tex

clean:
	latexmk -C -cd ../paper/riemann.tex
