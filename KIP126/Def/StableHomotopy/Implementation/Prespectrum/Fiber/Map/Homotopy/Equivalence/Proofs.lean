module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Map.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Map.Equivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- An actual homotopy-commuting square with stable-equivalence vertical
maps induces a stable equivalence of its actual path fibers. -/
theorem fiberHomotopyMap_stableEquivalence {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (H : StrictHomotopy (f ≫ b) (a ≫ g))
    (ha : stableEquivalences a) (hb : stableEquivalences b) :
    stableEquivalences (fiberHomotopyMap f g a b H) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts a ha
  letI := stableEquivalences.Q_inverts b hb
  apply source_fiber_map_isIso f g (sourceLocalization.map a) (sourceLocalization.map b)
  · simpa only [CategoryTheory.Functor.map_comp] using
      source_map_eq_of_pathHomotopic (show pathHomotopic (f ≫ b) (a ≫ g) from ⟨H⟩)
  · rw [← CategoryTheory.Functor.map_comp, fiberHomotopyMap_projection,
      CategoryTheory.Functor.map_comp]
  · simpa only [sourceLoopFunctor_map] using source_fiberConnecting_homotopyMap f g a b H

end KIP126.StableHomotopy.Implementation.Prespectrum
