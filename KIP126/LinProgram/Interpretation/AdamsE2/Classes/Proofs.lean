module

public import KIP126.LinProgram.Interpretation.AdamsE2.Classes.Data
public import KIP126.Def.AdamsE2.Presentation.Proofs

@[expose] public section

namespace KIP126.AdamsE2.Input

theorem h6_ne_zero (myAdams : Input) : myAdams.h6 ≠ 0 :=
  (myAdams.presentation.basis (1, 64) myAdams.h6_mem).ne_zero _

end KIP126.AdamsE2.Input
