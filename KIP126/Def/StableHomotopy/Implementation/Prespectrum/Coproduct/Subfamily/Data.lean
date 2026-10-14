module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Compact.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
universe u

/-- Collapse the omitted summands of the actual strict coproduct to zero. -/
noncomputable def coproductSubfamilyRetraction {J : Type u}
    (X : J → Prespectrum.{u}) (s : Set J) : (∐ X) ⟶ ∐ fun j : s => X j.val := by
  classical
  exact Sigma.desc (fun j => if h : j ∈ s then
    Sigma.ι (fun j : s => X j.val) ⟨j,h⟩ else zeroMap (X j) _)

end KIP126.StableHomotopy.Implementation.Prespectrum
