module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- Homotopy out of the actual strict coproduct is detected independently
on all summands. -/
theorem pathHomotopic_coproduct_iff {J : Type u} {X : J → Prespectrum.{u}}
    {Y : Prespectrum.{u}} (f g : (∐ X) ⟶ Y) :
    pathHomotopic f g ↔ ∀ j, pathHomotopic (Sigma.ι X j ≫ f) (Sigma.ι X j ≫ g) := by
  constructor
  · rintro ⟨H⟩ j
    exact ⟨H.precomp (Sigma.ι X j)⟩
  · intro H
    exact ⟨StrictHomotopy.coproduct (fun j => Classical.choice (H j))⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
