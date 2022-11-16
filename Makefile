# TODO Move this to lakefile, if possible

.PHONY: build
build:
	lake build
	@echo "--------------------------------------------------------------------------------------"
	souffle --fact-dir=./gen/facts --output-dir=./gen/outputs ./LeanLCNF.dl
	@echo "--------------------------------------------------------------------------------------"
