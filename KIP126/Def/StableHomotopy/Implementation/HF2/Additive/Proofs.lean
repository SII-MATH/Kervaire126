module

public import KIP126.Def.StableHomotopy.Implementation.Completion
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Abelian.Proofs
public import KIP126.Def.Algebra.Group.TwoElements.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

/-- The original source-model coefficient equivalence sends the actual
stable group zero to zero. -/
theorem SourceHF2Model.pi0_map_zero (M : SourceHF2Model) : M.pi0 0 = 0 := by
  simpa only [Prespectrum.loopClass_const] using M.pi0_zero

/-- The original coefficient identification is an isomorphism for the
abelian group operations constructed from the actual stable loops. -/
theorem SourceHF2Model.pi0_map_add (M : SourceHF2Model)
    (x y : Prespectrum.StableHomotopy M.spectrum 0) :
    M.pi0 (x+y) = M.pi0 x + M.pi0 y :=
  KIP126.Core.equivTwo_map_add M.pi0 M.pi0_map_zero x y

end KIP126.StableHomotopy.Implementation
