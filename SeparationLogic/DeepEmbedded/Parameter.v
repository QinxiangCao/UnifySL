Record SL_Parameter: Type := {
  EM: bool;
  IC: bool;
  WEM: bool;
  SCE: bool;
  ESE: bool;
  ED: bool
}.

Record SA_Parameter: Type := {
  ID: bool;
  NB: bool;
  BJ: bool;
  INCR: bool;
  ISS: bool;
  IJS: bool
}.

Inductive Parameter_coincide (SLP: SL_Parameter) (SAP: SA_Parameter) : Prop :=
  Build_Parameter_coincide:
    EM SLP = ID SAP ->
    IC SLP = NB SAP ->
    WEM SLP = BJ SAP ->
    SCE SLP = INCR SAP ->
    ESE SLP = ISS SAP ->
    ED SLP = IJS SAP ->
    Parameter_coincide SLP SAP.
