Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

  Class SeparatingSemantics
        (L: Language)
        {sL: SeparationLanguage L}
        (MD: Model)
        {kMD: KripkeModel MD}
        (M: Kmodel)
        {R: Relation (Kworlds M)}
        {kiM: KripkeIntuitionisticModel (Kworlds M)}
        {J: Join (Kworlds M)}
        (SM: Semantics L MD): Type :=
    {
      sat_sepcon: forall m x y,
        KRIPKE: M , m |= x * y <->
                    exists m1 m2, join m1 m2 m /\
                                  KRIPKE: M , m1 |= x /\
                                  KRIPKE: M, m2 |= y;
      sat_wand: forall m x y,
          KRIPKE: M , m |= x -* y <->
                      forall m0 m1 m2,
                        m <= m0 -> join m0 m1 m2 ->
                        KRIPKE: M , m1 |= x -> KRIPKE: M, m2 |= y
}.

Class EmpSemantics
      (L: Language)
      {sL: SeparationLanguage L}
      {s'L: SeparationEmpLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      {R: Relation (Kworlds M)}
      {kiM: KripkeIntuitionisticModel (Kworlds M)}
      {J: Join (Kworlds M)}
      (SM: Semantics L MD): Type :=
    sat_emp: forall (m: Kworlds M), KRIPKE: M, m |= emp <-> increasing' m.

