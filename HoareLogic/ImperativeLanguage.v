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
