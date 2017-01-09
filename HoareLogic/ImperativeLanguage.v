Class ProgrammingLanguage: Type := {
  cmd: Type
}.

Class ImperativeProgrammingLanguage (P: ProgrammingLanguage): Type := {
  bool_expr: Type;
  Ssequence: cmd -> cmd -> cmd;
  Sifthenelse: bool_expr -> cmd -> cmd -> cmd;
  Swhile: bool_expr -> cmd -> cmd;
  Sskip: cmd
}.

Class ConcurrentProgrammingLanguage (P: ProgrammingLanguage): Type := {
  Sparallel: cmd -> cmd -> cmd
}.

Class Resource_ConcurrentProgrammingLanguage (P: ProgrammingLanguage): Type := {
  resource: Type;
  Sresource: resource -> cmd -> cmd
}.

Class Lock_ConcurrentProgrammingLanguage (P: ProgrammingLanguage): Type := {
  lock_expr: Type;
  Sacquire: lock_expr -> cmd;
  Srelease: lock_expr -> cmd
}.

Class NormalImperativeProgrammingLanguage (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P}: Type := {
  Ssequence_inv: forall c1 c2 c1' c2', Ssequence c1 c2 = Ssequence c1' c2' -> c1 = c1' /\ c2 = c2';
  Ssequence_Sskip: forall c1 c2, Ssequence c1 c2 <> Sskip;
  Sifthenelse_inv: forall b c1 c2 b' c1' c2', Sifthenelse b c1 c2 = Sifthenelse b' c1' c2' -> b = b' /\ c1 = c1' /\ c2 = c2';
  Sifthenelse_Sskip: forall b c1 c2, Sifthenelse b c1 c2 <> Sskip;
  Swhile_inv: forall b c b' c', Swhile b c = Swhile b' c' -> b = b' /\ c = c';
  Swhile_Sskip: forall b c, Swhile b c <> Sskip;
  Ssequence_Swhile: forall c1 c2 b c, Ssequence c1 c2 <> Swhile b c
}.


