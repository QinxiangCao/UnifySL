Record SL_Parameter: Type := {
  EM: bool;
  IC: bool;
  WEM: bool;
  SCE: bool;
  EMP: bool
}.

Record SA_Parameter: Type := {
  ID: bool;
  NB: bool;
  BJ: bool;
  GC: bool;
  Uni: bool
}.

Inductive Parameter_coincide (SLP: SL_Parameter) (SAP: SA_Parameter) : Prop :=
  Build_Parameter_coincide:
    EM SLP = ID SAP ->
    IC SLP = NB SAP ->
    WEM SLP = BJ SAP ->
    SCE SLP = GC SAP ->
    EMP SLP = Uni SAP ->
    Parameter_coincide SLP SAP.
