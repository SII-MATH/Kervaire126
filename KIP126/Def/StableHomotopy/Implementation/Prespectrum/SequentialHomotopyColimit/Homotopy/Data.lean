module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialHomotopyColimit
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The displayed cylinder-and-cell comparison identifies the actual
stable homotopy diagram with that of the original strict sequence. -/
noncomputable def sequentialHomotopyStableComparison (F : ℕ ⥤ Prespectrum.{u}) (d : ℤ) :
    sequentialHomotopyDiagram F ⋙ stableHomotopyFunctor d ≅ F ⋙ stableHomotopyFunctor d := by
  let α := Functor.whiskerRight (sequentialHomotopyComparison F) (stableHomotopyFunctor d)
  letI (k : ℕ) : IsIso (α.app k) :=
    (CategoryTheory.isIso_iff_bijective _).mpr
      (sequentialHomotopyComparison_stableEquivalence F k d)
  exact NatIso.ofComponents (fun k => asIso (α.app k)) (fun f => α.naturality f)

/-- The actual stable homotopy cocone on the original sequence, with
vertex the stable homotopy of the constructed topological telescope. -/
noncomputable def sequentialHomotopyStableCocone (F : ℕ ⥤ Prespectrum.{u}) (d : ℤ) :
    Cocone (F ⋙ stableHomotopyFunctor d) :=
  (Cocone.precompose (sequentialHomotopyStableComparison F d).inv).obj
    (sequentialStableHomotopyCocone (sequentialHomotopyDiagram F) d)

end KIP126.StableHomotopy.Implementation.Prespectrum
