Record SL_Parameter: Type := {
  EM: bool;
  IC: bool;
  WEM: bool;
  SCE: bool;
  EMP: bool;
  EXT: bool
}.

Record SA_Parameter: Type := {
  ID: bool;
  NB: bool;
  BJ: bool;
  INCR: bool;
  UNI: bool;
  RES: bool
}.

Inductive Parameter_coincide (SLP: SL_Parameter) (SAP: SA_Parameter) : Prop :=
  Build_Parameter_coincide:
    EM SLP = ID SAP ->
    IC SLP = NB SAP ->
    WEM SLP = BJ SAP ->
    SCE SLP = INCR SAP ->
    EMP SLP = UNI SAP ->
    EXT SLP = RES SAP ->
    Parameter_coincide SLP SAP.
