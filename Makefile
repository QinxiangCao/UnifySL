COQC = coqc

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) -q -R "." -as IntuitionisticLogic $*.v

all: Wf.vo base.vo IPC.vo
