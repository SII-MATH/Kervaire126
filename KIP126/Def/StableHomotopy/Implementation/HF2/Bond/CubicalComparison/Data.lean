module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Bond.FiberIdentification

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The actual realized endpoint map of the specified simplicial path object. -/
noncomputable def hf2PathProjection (n : ℕ) :
    C(pathRealizationLevel (hf2SimplicialModule (n+1)), hf2RealizationLevel (n+1)) :=
  (SSet.toTop.map (decalageProjection (hf2SimplicialSet (n+1)))).hom

/-- The source of the bond is the actual topological endpoint fiber, through
the exact normalized coefficient isomorphism and realized kernel inclusion. -/
noncomputable def coefficientFiberHomeomorph (n : ℕ) :
    hf2RealizationLevel n ≃ₜ pathProjectionFiber n :=
  (coefficientLoopRealizationHomeomorph n).trans (loopFiberHomeomorph n)


end KIP126.StableHomotopy.Implementation.HF2Bond
