module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Layer.Scalar.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Chosen.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- The original scalar cofiber of a single-degree object has stable
homotopy only in that degree and the following degree. -/
theorem sourceCofiber_nsmul_homotopy_subsingleton_of_singleDegree
    (X : SourceCategory.{0}) (n : ℤ) (p : ℕ)
    (hX : ∀ d, d ≠ n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (d : ℤ) (hd : d ≠ n) (hd' : d ≠ n+1) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj
      (HasFunctorialCofiber.cofib (p • 𝟙 X))) := by
  let F := sourceStableHomotopyAddFunctor d
  let f := p • 𝟙 X
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT := HasFunctorialCofiber.cofib_distinguished f
  letI := hX d hd
  letI : Subsingleton (F.obj T.obj₂) := hX d hd
  letI := hX (d-1) (by omega)
  letI : Subsingleton (F.obj (X⟦(1 : ℤ)⟧)) :=
    (sourceStableHomotopyShiftEquiv X d 1).surjective.subsingleton
  have hz₃ : F.map T.mor₃ = 0 := (AddCommGrpCat.isZero_of_subsingleton (F.obj (X⟦(1 : ℤ)⟧))).eq_of_tgt _ _
  haveI : Epi (F.map T.mor₂) :=
    (F.map_distinguished_exact T.rotate (rot_of_distTriang T hT)).epi_f hz₃
  exact ((AddCommGrpCat.epi_iff_surjective (F.map T.mor₂)).mp inferInstance).subsingleton

/-- Every original stable group of the actual scalar cofiber of a
single-degree object is killed by that scalar. This includes its kernel
and cokernel degrees, with no scalar hypothesis on the original object. -/
theorem sourceCofiber_nsmul_homotopy_nsmul_eq_zero_of_singleDegree
    (X : SourceCategory.{0}) (n : ℤ) (p : ℕ)
    (hX : ∀ d, d ≠ n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (d : ℤ) (x : (sourceStableHomotopyAddFunctor d).obj
      (HasFunctorialCofiber.cofib (p • 𝟙 X))) : p • x = 0 := by
  let F := sourceStableHomotopyAddFunctor d
  let f := p • 𝟙 X
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT := HasFunctorialCofiber.cofib_distinguished f
  by_cases hd : d = n
  · letI := hX (d-1) (by omega)
    letI : Subsingleton (F.obj (X⟦(1 : ℤ)⟧)) :=
      (sourceStableHomotopyShiftEquiv X d 1).surjective.subsingleton
    have hz₃ : F.map T.mor₃ = 0 := (AddCommGrpCat.isZero_of_subsingleton (F.obj (X⟦(1 : ℤ)⟧))).eq_of_tgt _ _
    haveI : Epi (F.map T.mor₂) :=
      (F.map_distinguished_exact T.rotate (rot_of_distTriang T hT)).epi_f hz₃
    obtain ⟨y,hy⟩ := ((AddCommGrpCat.epi_iff_surjective (F.map T.mor₂)).mp inferInstance) x
    rw [← hy]
    calc
      p • F.map T.mor₂ y = F.map T.mor₂ (p • y) := (map_nsmul (F.map T.mor₂).hom p y).symm
      _ = (F.map T.mor₁ ≫ F.map T.mor₂) y := by
        change _ = (F.map (p • 𝟙 X) ≫ F.map T.mor₂) y
        rw [Functor.map_nsmul,CategoryTheory.Functor.map_id]
        rfl
      _ = 0 := by
        rw [← F.map_comp,comp_distTriang_mor_zero₁₂ T hT,F.map_zero]
        rfl
  · letI := hX d hd
    have hz₂ : F.map T.mor₂ = 0 := (AddCommGrpCat.isZero_of_subsingleton (F.obj X)).eq_of_src _ _
    haveI : Mono (F.map T.mor₃) :=
      (F.map_distinguished_exact T.rotate (rot_of_distTriang T hT)).mono_g hz₂
    apply ((AddCommGrpCat.mono_iff_injective (F.map T.mor₃)).mp inferInstance)
    rw [map_nsmul,map_zero]
    have hmap : F.map (T.mor₁⟦(1 : ℤ)⟧') = p • 𝟙 (F.obj (T.obj₁⟦(1 : ℤ)⟧)) := by
      change F.map ((shiftFunctor SourceCategory (1 : ℤ)).map (p • 𝟙 X)) = p • 𝟙 (F.obj (X⟦(1 : ℤ)⟧))
      simp only [Functor.map_nsmul,CategoryTheory.Functor.map_id]
    have hz : F.map T.mor₃ ≫ (p • 𝟙 (F.obj (T.obj₁⟦(1 : ℤ)⟧))) = 0 := by
      rw [← hmap,← F.map_comp,comp_distTriang_mor_zero₃₁ T hT,F.map_zero]
    rw [Preadditive.comp_nsmul,Category.comp_id] at hz
    exact congrArg (fun k : F.obj T.obj₃ ⟶ F.obj (T.obj₁⟦(1 : ℤ)⟧) => k x) hz

/-- Every actual Postnikov layer of this original scalar cofiber has
its identity killed by the original scalar. -/
theorem sourceCofiber_nsmul_postnikovLayer_nsmul_id_eq_zero
    (X : SourceCategory.{0}) (n : ℤ) (p : ℕ)
    (hX : ∀ d, d ≠ n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X)) (d : ℤ) :
    p • 𝟙 (sourcePostnikovLayer (HasFunctorialCofiber.cofib (p • 𝟙 X)) d) = 0 :=
  sourcePostnikovLayer_nsmul_id_eq_zero_of_homotopy _ d p
    (sourceCofiber_nsmul_homotopy_nsmul_eq_zero_of_singleDegree X n p hX d)

end KIP126.StableHomotopy.Implementation

