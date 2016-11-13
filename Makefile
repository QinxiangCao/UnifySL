COQC = coqc

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) -q -R "." -as Logic $*.v

all: Wf.vo base.vo IPC.vo trivial.vo Kripke.vo enumerate.vo LogicBase.vo \
     MinimunLogic/HenkinCompleteness.v MinimunLogic/MinimunLogic.vo MinimunLogic/ContextProperty.vo \
     PropositionalLogic/IntuitionisticPropositionalLogic.vo \
     PropositionalLogic/KripkeSemantics.vo \
     PropositionalLogic/Syntax.vo PropositionalLogic/ClassicalPropositionalLogic.vo \
     PropositionalLogic/TrivialSemantics.vo PropositionalLogic/Sound_Classical_Trivial.vo \
     PropositionalLogic/Complete_Classical_Trivial.vo lib/Coqlib.vo \
     lib/Bijection.vo lib/Countable.vo PropositionalLogic/Complete_Intuitionistic_Kripke.vo \
     PropositionalLogic/CanonicalKripke.vo 
