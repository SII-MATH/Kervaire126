import KIP126.Def.StableHomotopy.Context.CofiberFactorization.Proofs

namespace KIP126.StableHomotopy

open CategoryTheory Pretriangulated
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- A factorization through an isomorphism induces an isomorphism of the
chosen cofibers. No identity law for the chosen cofiber maps is required. -/
theorem cofiberFactorizationMap_isIso {A B D : C}
    (f : A ⟶ D) (g : B ⟶ D) (a : A ⟶ B) (h : a ≫ g = f) [IsIso a] :
    IsIso (cofiberFactorizationMap f g a h) := by
  let φ : Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f) ⟶
      Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g) :=
    { hom₁ := a
      hom₂ := 𝟙 D
      hom₃ := cofiberFactorizationMap f g a h
      comm₁ := by
        change f ≫ 𝟙 D = a ≫ g
        exact (Category.comp_id f).trans h.symm
      comm₂ := by
        change HasFunctorialCofiber.cofibι f ≫ cofiberFactorizationMap f g a h =
          𝟙 D ≫ HasFunctorialCofiber.cofibι g
        exact (cofiberFactorizationMap_ι f g a h).trans (Category.id_comp _).symm
      comm₃ := (cofiberFactorizationMap_δ f g a h).symm }
  exact isIso₃_of_isIso₁₂ φ (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished g) (inferInstanceAs (IsIso a))
    (inferInstanceAs (IsIso (𝟙 D)))

end KIP126.StableHomotopy
