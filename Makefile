OUT_DIR ?= _slides
PORT ?= 8000
SLIDES_EXE ?= demo-slides

.PHONY: generate serve

generate:
	lake build
	lake exe $(SLIDES_EXE) --output $(OUT_DIR)

serve: 
	python3 -m http.server $(PORT) -d $(OUT_DIR)
