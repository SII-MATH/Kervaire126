module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Additive.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- Vanishing of an original stable group is retained by the actual
categorical product, with no finiteness assumption on its index. -/
theorem sourceProduct_homotopy_subsingleton {J : Type}
    (X : J → SourceCategory.{0}) (d : ℤ)
    (hX : ∀ j, Subsingleton ((sourceStableHomotopyAddFunctor d).obj (X j))) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (∏ᶜ X)) := by
  let e : (sourceStableHomotopyAddFunctor d).obj (∏ᶜ X) ≃+
      (Prespectrum.sourceSphere d ⟶ ∏ᶜ X) :=
    Prespectrum.sourceStableHomotopyAddEquiv (∏ᶜ X).as.obj d
  refine ⟨fun x y => e.injective ?_⟩
  apply Pi.hom_ext
  intro j
  exact (Prespectrum.sourceStableHomotopyAddEquiv (X j).as.obj d).symm.injective
    ((hX j).elim _ _)

/-- A common annihilator of the actual factor identities annihilates
the identity of the actual arbitrary product. -/
theorem sourceProduct_nsmul_id_eq_zero {J : Type}
    (X : J → SourceCategory.{0}) (p : ℕ) (hX : ∀ j, p • 𝟙 (X j) = 0) :
    p • 𝟙 (∏ᶜ X) = 0 := by
  apply Pi.hom_ext
  intro j
  rw [Preadditive.nsmul_comp,Category.id_comp,zero_comp]
  have h := congrArg (fun f => Pi.π X j ≫ f) (hX j)
  simpa only [Preadditive.comp_nsmul,Category.comp_id,comp_zero] using h

end KIP126.StableHomotopy.Implementation
