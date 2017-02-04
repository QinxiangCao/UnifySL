Module KM.

Class Relation (worlds: Type): Type :=
  Krelation: worlds -> worlds -> Prop.

End KM.

Export KM.

Class KripkeModalModel_PFunctional (worlds: Type) {R: Relation worlds} :=
  Krelation_pfunc: forall m n n', Krelation m n -> Krelation m n' -> n = n'.

