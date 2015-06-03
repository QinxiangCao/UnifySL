COQC = coqc

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) -q -R IntuitionisticLogic -as IntuitionisticLogic $*.v

all: IntuitionisticLogic/Wf.vo IntuitionisticLogic/base.vo IntuitionisticLogic/IPC.vo
