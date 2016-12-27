CURRENT_DIR=./
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = lib MinimunLogic PropositionalLogic SeparationLogic HoareLogic
INCLUDE_DEMO = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) Logic.$(d))
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -R $(CURRENT_DIR) Logic
DEP_FLAG = $(DEP_DEMO) 

lib_FILES = \
  Coqlib.v Bijection.v Countable.v NatChoice.v \
  Stream/SigStream.v Stream/StreamFunctions.v

MinimunLogic_FILES = \
  LogicBase.v MinimunLogic.v RewriteClass.v \
  ContextProperty.v HenkinCompleteness.v

PropositionalLogic_FILES = \
  Syntax.v \
  IntuitionisticPropositionalLogic.v ClassicalPropositionalLogic.v \
  GodelDummettLogic.v WeakClassicalLogic.v \
  RewriteClass.v \
  KripkeSemantics.v TrivialSemantics.v \
  Sound_Classical_Trivial.v Complete_Classical_Trivial.v \
  Sound_Kripke.v Complete_Kripke.v 

SeparationLogic_FILES = \
  Syntax.v SoundCompleteParameter.v \
  SeparationLogic.v SeparationLogicExtension.v \
  SeparationAlgebra.v SeparationAlgebraConstruction.v \
  SeparationAlgebraExamples.v \
  Semantics.v \
  Sound_Downwards.v Sound_Upwards.v Sound_Flat.v \
  DownUpSemantics_Fail.v Sound_DownUp_Fail.v \
  Complete_Flat.v \
  Downwards2Upwards.v Upwards2Downwards.v

HoareLogic_FILES = \
  ImperativeLanguage.v ProgramState.v Trace.v \
  SimpleSmallStepSemantics.v SmallStepSemantics.v \
  BigStepSemantics.v ConcurrentSemantics.v LocalTraceSemantics.v \
  OperationalSemanticsGenerator.v \
  HoareLogic_Sequential.v HoareLogic_Concurrent.v \
  Sound_Basic.v Sound_Imp.v Sound_Frame.v Sound_Resource.v

FILES = \
  $(lib_FILES:%.v=lib/%.v) \
  $(MinimunLogic_FILES:%.v=MinimunLogic/%.v) \
  $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.v) \
  $(SeparationLogic_FILES:%.v=SeparationLogic/%.v) \
  $(HoareLogic_FILES:%.v=HoareLogic/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(FILES:%.v=%.vo) \

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob

.DEFAULT_GOAL := all

include .depend


#COQC = coqc
# 
#%.vo: %.v
# 	@echo COQC $*.v
# 	@$(COQC) -q -R "." -as Logic $*.v
# 
#all: 
#     
#     SeparationLogic/Syntax.vo SeparationLogic/SeparationLogic.vo \
#     SeparationLogic/QinxiangSantiagoSemantics.vo
