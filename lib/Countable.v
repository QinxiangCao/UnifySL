Require Import Logic.lib.Bijection.

Definition Countable (A: Type): Type := injection A nat.

Definition injection_Countable {A B} (R: injection A B) (CB: Countable B): Countable A := injection_trans R CB.

Definition bijection_Countable {A B} (R: bijection A B) (CB: Countable B): Countable A := injection_Countable (bijection_injection R) CB.

Definition sum_Countable {A B} (CA: Countable A) (CB: Countable B): Countable (sum A B) :=
  injection_trans (sum_injection CA CB) (bijection_injection nat2_nat_bijection).

Definition prod_Countable {A B} (CA: Countable A) (CB: Countable B): Countable (prod A B) :=
  injection_trans (prod_injection CA CB) (bijection_injection natnat_nat_bijection).



