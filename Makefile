COQC = coqc

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) -q -R "." -as Logic $*.v

all: Wf.vo base.vo IPC.vo trivial.vo Kripke.vo enumerate.vo LogicBase.vo PropositionalLogic/Syntax.vo PropositionalLogic/ClassicalPropositionalLogic.vo
