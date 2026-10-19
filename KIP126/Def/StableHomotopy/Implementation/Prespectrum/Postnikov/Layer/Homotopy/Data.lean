module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Layer.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The actual layer group identifies additively with the original stable
group, through the specified fiber inclusion and original truncation unit. -/
noncomputable def sourcePostnikovLayerHomotopyEquiv (X : SourceCategory.{0}) (n : ℤ) :
    (sourceStableHomotopyAddFunctor n).obj (sourcePostnikovLayer X n) ≃+
      (sourceStableHomotopyAddFunctor n).obj X :=
  (AddEquiv.ofBijective ((sourceStableHomotopyAddFunctor n).map
    (sourcePostnikovLayerInclusion X n)).hom
      (sourcePostnikovLayerInclusion_homotopy_bijective X n)).trans
    (AddEquiv.ofBijective ((sourceStableHomotopyAddFunctor n).map
      (sourcePostnikovUnit X (n+1))).hom
        (sourcePostnikovUnit_homotopy_bijective X (n+1) n (by omega))).symm

end KIP126.StableHomotopy.Implementation
