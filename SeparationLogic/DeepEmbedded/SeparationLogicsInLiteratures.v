Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Logic.SeparationLogic.DeepEmbedded.SeparationLanguage.
Require Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Module ReynoldsLogic.
Section ReynoldsLogic.

Context {Sigma: SeparationLanguage.PropositionalVariables}.

Existing Instances SeparationLanguage.L SeparationLanguage.minL SeparationLanguage.pL SeparationLanguage.sL.

Inductive provable: SeparationLanguage.expr Sigma -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| sepcon_comm: forall x y, provable (x * y --> y * x)
| sepcon_assoc: forall x y z, provable (x * (y * z) <--> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_elim1: forall x y, provable (x * y --> x).

Instance GP: Provable SeparationLanguage.L := Build_Provable _ provable.

Instance GD: Derivable SeparationLanguage.L := Provable2Derivable.

Instance AX: NormalAxiomatization SeparationLanguage.L GP GD :=
  Provable2Derivable_Normal.

Instance minAX: MinimumAxiomatization SeparationLanguage.L GP.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipAX: IntuitionisticPropositionalLogic SeparationLanguage.L GP.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance sAX: SeparationLogic SeparationLanguage.L GP.
Proof.
  constructor.
  + apply sepcon_comm.
  + apply sepcon_assoc.
  + intros; split.
    - apply wand_sepcon_adjoint1.
    - apply wand_sepcon_adjoint2.
Qed.

Instance gcsAX: GarbageCollectSeparationLogic SeparationLanguage.L GP.
Proof.
  constructor.
  apply sepcon_elim1.
Qed.

End ReynoldsLogic.
End ReynoldsLogic.

Module OHearnLogic.
Section OHearnLogic.

Context {Sigma: SeparationEmpLanguage.PropositionalVariables}.

Existing Instances SeparationEmpLanguage.L SeparationEmpLanguage.minL SeparationEmpLanguage.pL SeparationEmpLanguage.sL SeparationEmpLanguage.s'L.

Inductive provable: SeparationEmpLanguage.expr Sigma -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| excluded_middle: forall x, provable (x || ~~ x)
| sepcon_comm: forall x y, provable (x * y --> y * x)
| sepcon_assoc: forall x y z, provable (x * (y * z) <--> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_emp: forall x, provable (x * emp <--> x).

Instance GP: Provable SeparationEmpLanguage.L := Build_Provable _ provable.

Instance GD: Derivable SeparationEmpLanguage.L := Provable2Derivable.

Instance AX: NormalAxiomatization SeparationEmpLanguage.L GP GD :=
  Provable2Derivable_Normal.

Instance minAX: MinimumAxiomatization SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipAX: IntuitionisticPropositionalLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance cpAX: ClassicalPropositionalLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  apply excluded_middle.
Qed.

Instance sAX: SeparationLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply sepcon_comm.
  + apply sepcon_assoc.
  + intros; split.
    - apply wand_sepcon_adjoint1.
    - apply wand_sepcon_adjoint2.
Qed.

Instance EmpsAX: EmpSeparationLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  apply sepcon_emp.
Qed.

End OHearnLogic.
End OHearnLogic.

Module LogicOnModuResModel.
Section LogicOnModuResModel.

Context {Sigma: SeparationEmpLanguage.PropositionalVariables}.

Existing Instances SeparationEmpLanguage.L SeparationEmpLanguage.minL SeparationEmpLanguage.pL SeparationEmpLanguage.sL SeparationEmpLanguage.s'L.

Inductive provable: SeparationEmpLanguage.expr Sigma -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| sepcon_comm: forall x y, provable (x * y --> y * x)
| sepcon_assoc: forall x y z, provable (x * (y * z) <--> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_emp: forall x, provable (x * emp <--> x)
| sepcon_elim1: forall x y, provable (x * y --> x).

Instance GP: Provable SeparationEmpLanguage.L := Build_Provable _ provable.

Instance GD: Derivable SeparationEmpLanguage.L := Provable2Derivable.

Instance AX: NormalAxiomatization SeparationEmpLanguage.L GP GD :=
  Provable2Derivable_Normal.

Instance minAX: MinimumAxiomatization SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipAX: IntuitionisticPropositionalLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance sAX: SeparationLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply sepcon_comm.
  + apply sepcon_assoc.
  + intros; split.
    - apply wand_sepcon_adjoint1.
    - apply wand_sepcon_adjoint2.
Qed.

Instance EmpsAX: EmpSeparationLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  apply sepcon_emp.
Qed.

Instance gcsAX: GarbageCollectSeparationLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  apply sepcon_elim1.
Qed.

End LogicOnModuResModel. 
End LogicOnModuResModel.

Module LogicOnMSL.
Section LogicOnMSL.

Context {Sigma: SeparationEmpLanguage.PropositionalVariables}.

Existing Instances SeparationEmpLanguage.L SeparationEmpLanguage.minL SeparationEmpLanguage.pL SeparationEmpLanguage.sL SeparationEmpLanguage.s'L.

Inductive provable: SeparationEmpLanguage.expr Sigma -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| impp_choice: forall x y, provable ((x --> y) || (y --> x))
| sepcon_comm: forall x y, provable (x * y --> y * x)
| sepcon_assoc: forall x y z, provable (x * (y * z) <--> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_emp: forall x, provable (x * emp <--> x).

Instance GP: Provable SeparationEmpLanguage.L := Build_Provable _ provable.

Instance GD: Derivable SeparationEmpLanguage.L := Provable2Derivable.

Instance AX: NormalAxiomatization SeparationEmpLanguage.L GP GD :=
  Provable2Derivable_Normal.

Instance minAX: MinimumAxiomatization SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipAX: IntuitionisticPropositionalLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance sAX: SeparationLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply sepcon_comm.
  + apply sepcon_assoc.
  + intros; split.
    - apply wand_sepcon_adjoint1.
    - apply wand_sepcon_adjoint2.
Qed.

Instance EmpsAX: EmpSeparationLogic SeparationEmpLanguage.L GP.
Proof.
  constructor.
  apply sepcon_emp.
Qed.


End LogicOnMSL.
End LogicOnMSL.
