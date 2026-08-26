AGDA = agda +RTS -A128M -M18G -RTS -v0

check-interpreter:
	$(AGDA) -i . -i ../GTSFImp Interpreter.agda

check-isomorphism:
	$(AGDA) -i . -i ../GTSFImp NarrowWidenIsomorphism.agda

check-lr:
	$(AGDA) -i . -i ../GTSFImp LR-narrow/LRNarrowAll.agda

check: check-interpreter check-isomorphism check-lr

.PHONY: check check-interpreter check-isomorphism check-lr
