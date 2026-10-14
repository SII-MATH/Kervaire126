module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u

/-- The initial inclusion into an actual sequential colimit of cubical
cofibrations has the same left lifting property. -/
theorem sequentialColimit_initial_isCubicalCofibration
    (F : ℕ ⥤ Prespectrum.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, IsCubicalCofibration (F.map (homOfLE (Nat.le_succ n)))) :
    IsCubicalCofibration (c.ι.app 0) := by
  intro E B p hp
  apply HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot hc
  intro n hn
  exact hF n p hp

/-- An actual sequential colimit of cubical cofibrations is cubically
cofibrant whenever its initial object is. -/
theorem sequentialColimit_isCubicallyCofibrant
    (F : ℕ ⥤ Prespectrum.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, IsCubicalCofibration (F.map (homOfLE (Nat.le_succ n))))
    (h₀ : IsCubicallyCofibrant (F.obj 0)) : IsCubicallyCofibrant c.pt := by
  intro E B p hp
  exact IsCubicallyCofibrant.of_cubicalCofibration h₀
    (sequentialColimit_initial_isCubicalCofibration F c hc hF) p hp

end KIP126.StableHomotopy.Implementation.Prespectrum
