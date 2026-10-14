module

public import KIP126.LinProgram.Certificates.Secondary.Seed5487.Input

@[expose] public section


namespace KIP126.Computation.Secondary.Seed5487

/-- The two actual first-differential columns used by the selected equations.
Unprovided columns are rejected; they are not interpreted as zero. -/
def firstDifferentialImages : Nat → Option ModuleExpression
  | 0 => some row524288.d
  | 1 => some row524289.d
  | _ => none

/-- The actual fourth-differential image used by row3145729's secondary lift.
Other local indices remain absent rather than being treated as zero columns. -/
def fourthDifferentialImages : Nat → Option ModuleExpression
  | 0 => some row2097152.d
  | _ => none

end KIP126.Computation.Secondary.Seed5487
