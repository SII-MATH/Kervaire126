module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- Assemble actual strict homotopies by the universal property of the strict
coproduct, with the actual path prespectrum as target. -/
noncomputable def StrictHomotopy.coproduct {J : Type u} {X : J → Prespectrum.{u}}
    {Y : Prespectrum.{u}} {f g : (∐ X) ⟶ Y}
    (H : ∀ j, StrictHomotopy (Sigma.ι X j ≫ f) (Sigma.ι X j ≫ g)) :
    StrictHomotopy f g where
  hom := Sigma.desc (fun j => (H j).hom)
  zero := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_desc_assoc]
    exact (H j).zero
  one := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_desc_assoc]
    exact (H j).one

end KIP126.StableHomotopy.Implementation.Prespectrum
