module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual free-cubical replacement preserves stable equivalences,
by its strictly natural levelwise weak-equivalence comparison. -/
theorem cubicalReplacementFunctor_map_stableEquivalence {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (cubicalReplacementFunctor.map f) := by
  intro d
  have hn := congrArg ((stableHomotopyFunctor d).map)
    (cubicalReplacementComparison.naturality f)
  rw [(stableHomotopyFunctor d).map_comp,(stableHomotopyFunctor d).map_comp] at hn
  apply ((cubicalReplacementComparison_stableEquivalence Y d).of_comp_iff' _).1
  have he : stableHomotopyMap (cubicalReplacementComparison.app Y) d ∘
      stableHomotopyMap (cubicalReplacementFunctor.map f) d =
      stableHomotopyMap f d ∘ stableHomotopyMap (cubicalReplacementComparison.app X) d :=
    funext (ConcreteCategory.congr_hom hn)
  rw [he]
  exact (hf d).comp (cubicalReplacementComparison_stableEquivalence X d)

end KIP126.StableHomotopy.Implementation.Prespectrum
