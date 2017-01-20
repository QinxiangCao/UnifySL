CURRENT_DIR=./
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = lib GeneralLogic MinimunLogic PropositionalLogic SeparationLogic HoareLogic
INCLUDE_DEMO = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) Logic.$(d))
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -R $(CURRENT_DIR) Logic
DEP_FLAG = $(DEP_DEMO) 

lib_FILES = \
  Coqlib.v Ensembles_ext.v \
  Bijection.v Countable.v NatChoice.v StrongInduction.v \
  Stream/SigStream.v Stream/StreamFunctions.v Stream/StreamSplit.v 

GeneralLogic_FILES = \
  Base.v HenkinCompleteness.v

MinimunLogic_ProofTheory_FILES = \
  Normal.v Minimun.v RewriteClass.v ContextProperty.v

MinimunLogic_FILES = \
  Syntax.v $(MinimunLogic_ProofTheory_FILES:%.v=ProofTheory/%.v)

PropositionalLogic_ProofTheory_FILES = \
  Intuitionistic.v WeakClassical.v \
  GodelDummett.v Classical.v \
  RewriteClass.v

PropositionalLogic_Semantics_FILES = \
  Kripke.v Trivial.v

PropositionalLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Classical_Trivial.v

PropositionalLogic_DeepEmbedded_FILES = \
  PropositionalLanguage.v \
  IntuitionisticLogic.v WeakClassicalLogic.v \
  GodelDummettLogic.v ClassicalLogic.v \
  KripkeSemantics.v TrivialSemantics.v \
  Soundness.v

PropositionalLogic_Complete_FILES = \
  Complete_Classical_Trivial.v \
  Complete_Kripke.v

PropositionalLogic_FILES = \
  Syntax.v\
  KripkeModel.v \
  $(PropositionalLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(PropositionalLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(PropositionalLogic_Sound_FILES:%.v=Sound/%.v) \
  $(PropositionalLogic_DeepEmbedded_FILES:%.v=DeepEmbeddedInstance/%.v) \
  $(PropositionalLogic_Complete_FILES:%.v=Complete/%.v)

SeparationLogic_Model_FILES = \
  SeparationAlgebra.v OrderedSA.v \
  UpwardsClosure.v DownwardsClosure.v

SeparationLogic_DeepEmbedded_FILES = \
  SeparationLanguage.v SeparationEmpLanguage.v

SeparationLogic_FILES = \
  Syntax.v SoundCompleteParameter.v \
  $(SeparationLogic_Model_FILES:%.v=Model/%.v) \
  $(SeparationLogic_DeepEmbedded_FILES:%.v=DeepEmbeddedInstance/%.v) \
  SeparationLogic.v SeparationLogicExtension.v \
  SeparationAlgebra.v SeparationAlgebraConstruction.v \
  SeparationAlgebraGenerators.v \
  SeparationAlgebraExamples.v \
  Semantics.v SemanticsExtension.v \
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
  Sound_Basic.v Sound_Imp.v Sound_Frame.v \
  Sound_ResourceBrookes.v

FILES = \
  $(lib_FILES:%.v=lib/%.v) \
  $(GeneralLogic_FILES:%.v=GeneralLogic/%.v) \
  $(MinimunLogic_FILES:%.v=MinimunLogic/%.v) \
  $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.v) \
  $(SeparationLogic_FILES:%.v=SeparationLogic/%.v) \
  $(HoareLogic_FILES:%.v=HoareLogic/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

lib: \
  .depend $(lib_FILES:%.v=lib/%.vo)

GeneralLogic: \
  .depend $(GeneralLogic_FILES:%.v=GeneralLogic/%.vo)

MinimunLogic: \
  .depend $(MinimunLogic_FILES:%.v=MinimunLogic/%.vo)

all: \
  $(FILES:%.v=%.vo) \

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob */*/*.vo */*/*.glob

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
