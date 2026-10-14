module

public import KIP126.Def.StableHomotopy.Completion.Moore.Proofs
public import KIP126.Def.Algebra.InverseSequence.EventualRange.Proofs
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Detection.Proofs
public import KIP126.Def.CategoryTheory.Triangulated.Scalar.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

set_option backward.isDefEq.respectTransparency false

universe u v

section Tower

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A vanishing scalar power on the source annihilates every represented
morphism after that power. -/
theorem nsmul_pow_hom_eq_zero_of_le (p : ℕ) {U Y : C} {N k : ℕ}
    (hU : p ^ N • 𝟙 U = 0) (hk : N ≤ k) (a : U ⟶ Y) :
    p ^ k • a = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  have ha : p ^ N • a = 0 := by
    simpa only [Preadditive.nsmul_comp, Category.id_comp, zero_comp] using
      congrArg (fun f => f ≫ a) hU
  rw [pow_add, mul_comm, mul_smul, ha, smul_zero]

/-- Additive shifts retain an actual scalar annihilator. -/
theorem nsmul_pow_id_shift_eq_zero (p : ℕ) {U : C} {N : ℕ}
    (hU : p ^ N • 𝟙 U = 0) (d : ℤ) : p ^ N • 𝟙 (U⟦d⟧) = 0 := by
  simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
    congrArg (fun f => (shiftFunctor C d).map f) hU

variable [HasFunctorialCofiber (C := C)]

/-- The square of the scalar annihilates its actual cofiber. This follows
from triangle exactness and does not assume a chosen nullhomotopy. -/
theorem nsmul_square_id_cofiber_eq_zero (p : ℕ) (X : C) :
    p ^ 2 • 𝟙 (HasFunctorialCofiber.cofib (p • 𝟙 X)) = 0 := by
  simpa only [pow_two] using KIP126.Foundation.nsmul_id_square_eq_zero_of_scalar_triangle
    p (HasFunctorialCofiber.cofibι (p • 𝟙 X)) (HasFunctorialCofiber.cofibδ (p • 𝟙 X))
    (HasFunctorialCofiber.cofib_distinguished (p • 𝟙 X))

/-- Above an annihilator exponent, the actual Moore inclusion is
injective on maps from the torsion object. -/
theorem moorePowerSequence_inclusion_injective_of_torsion (p : ℕ) (X U : C)
    {N k : ℕ} (hU : p ^ N • 𝟙 U = 0) (hk : N ≤ k) :
    Function.Injective (fun a : U ⟶ X =>
      a ≫ HasFunctorialCofiber.cofibι (moorePowerMap p X k)) := by
  let f := moorePowerMap p X k
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  intro a b hab
  apply sub_eq_zero.mp
  have hz : (a - b) ≫ T.mor₂ = 0 := by
    rw [Preadditive.sub_comp]
    exact sub_eq_zero.mpr hab
  obtain ⟨c, hc⟩ := T.coyoneda_exact₂
    (HasFunctorialCofiber.cofib_distinguished f) (a - b) hz
  change U ⟶ X at c
  change a - b = c ≫ (p ^ k • 𝟙 X) at hc
  rw [hc, Preadditive.comp_nsmul, Category.comp_id]
  exact nsmul_pow_hom_eq_zero_of_le p hU hk c

/-- The actual reduction map multiplies the boundary by the scalar. -/
theorem moorePowerSequence_boundary_step (p : ℕ) (X : C) (k : ℕ) :
    (moorePowerSequence p X).step k ≫
      HasFunctorialCofiber.cofibδ (moorePowerMap p X k) =
        p • HasFunctorialCofiber.cofibδ (moorePowerMap p X (k + 1)) := by
  have h := HasFunctorialCofiber.cofibMap_δ (moorePowerMap p X (k + 1))
    (moorePowerMap p X k) (p • 𝟙 X) (𝟙 X) (by
      simp only [moorePowerMap, Preadditive.nsmul_comp, Category.id_comp,
        Category.comp_id, smul_smul, pow_succ'])
  simpa only [moorePowerSequence, Functor.map_nsmul, CategoryTheory.Functor.map_id,
    Preadditive.comp_nsmul, Category.comp_id] using h

/-- Iterating the actual Moore shift multiplies the boundary by the
corresponding scalar power. -/
theorem moorePowerSequence_iterate_boundary (p : ℕ) (X U : C)
    (a : ∀ k, U ⟶ (moorePowerSequence p X).obj k) (r k : ℕ) :
    (((fun b : ∀ k, U ⟶ (moorePowerSequence p X).obj k =>
      fun j => b (j + 1) ≫ (moorePowerSequence p X).step j)^[r]) a k) ≫
        HasFunctorialCofiber.cofibδ (moorePowerMap p X k) =
      p ^ r • (a (k + r) ≫ HasFunctorialCofiber.cofibδ (moorePowerMap p X (k + r))) := by
  induction r generalizing k with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    rw [Category.assoc, moorePowerSequence_boundary_step, Preadditive.comp_nsmul, ih]
    simp only [smul_smul, ← pow_succ']
    rw [show k + 1 + r = k + (r + 1) by omega]

/-- After a uniformly bounded number of reductions, every map from a
torsion object lies in the image of the Moore inclusion. -/
theorem moorePowerSequence_iterate_mem_inclusion (p : ℕ) (X U : C)
    {N : ℕ} (hU : p ^ N • 𝟙 U = 0)
    (a : ∀ k, U ⟶ (moorePowerSequence p X).obj k) (k : ℕ) :
    ∃ b : U ⟶ X, b ≫ HasFunctorialCofiber.cofibι (moorePowerMap p X k) =
      ((fun b : ∀ k, U ⟶ (moorePowerSequence p X).obj k =>
        fun j => b (j + 1) ≫ (moorePowerSequence p X).step j)^[N]) a k := by
  let f := moorePowerMap p X k
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hb : (((fun b : ∀ k, U ⟶ (moorePowerSequence p X).obj k =>
      fun j => b (j + 1) ≫ (moorePowerSequence p X).step j)^[N]) a k) ≫ T.mor₃ = 0 := by
    rw [show T.mor₃ = HasFunctorialCofiber.cofibδ (moorePowerMap p X k) from rfl,
      moorePowerSequence_iterate_boundary]
    exact nsmul_pow_hom_eq_zero_of_le p hU (Nat.le_refl N) _
  obtain ⟨b, hb⟩ := T.coyoneda_exact₃ (HasFunctorialCofiber.cofib_distinguished f) _ hb
  exact ⟨b, hb.symm⟩

/-- Torsion test objects give a surjective Moore difference operator.
The proof uses the actual uniformly stable inclusion image. -/
theorem moorePowerSequence_sub_shift_surjective_of_torsion (p : ℕ) (X U : C)
    {N : ℕ} (hU : p ^ N • 𝟙 U = 0) :
    Function.Surjective (fun a : ∀ k, U ⟶ (moorePowerSequence p X).obj k =>
      fun k => a k - a (k + 1) ≫ (moorePowerSequence p X).step k) := by
  let f (k : ℕ) : (U ⟶ (moorePowerSequence p X).obj (k + 1)) →+
      (U ⟶ (moorePowerSequence p X).obj k) :=
    { toFun := fun a => a ≫ (moorePowerSequence p X).step k
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.add_comp] }
  let i (k : ℕ) : (U ⟶ X) →+ (U ⟶ (moorePowerSequence p X).obj k) :=
    { toFun := fun a => a ≫ HasFunctorialCofiber.cofibι (moorePowerMap p X k)
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.add_comp] }
  refine KIP126.Core.InverseSequence.surjective_sub_shift_of_uniform_constant_image
    (fun k => U ⟶ (moorePowerSequence p X).obj k) (U ⟶ X) f i ?_ N ?_
  · intro k a
    exact (Category.assoc _ _ _).trans
      (congrArg (fun b => a ≫ b) (moorePowerSequence_inclusion_step p X k))
  · exact moorePowerSequence_iterate_mem_inclusion p X U hU

/-- Every compatible family from a bounded-torsion test object comes from
one unique map into the original object. -/
theorem moorePowerSequence_existsUnique_compatible_of_torsion (p : ℕ) (X U : C)
    {N : ℕ} (hU : p ^ N • 𝟙 U = 0)
    (a : ∀ k, U ⟶ (moorePowerSequence p X).obj k)
    (ha : ∀ k, a (k + 1) ≫ (moorePowerSequence p X).step k = a k) :
    ∃! b : U ⟶ X, ∀ k, b ≫ HasFunctorialCofiber.cofibι (moorePowerMap p X k) = a k := by
  have hfix : (fun b : ∀ k, U ⟶ (moorePowerSequence p X).obj k =>
      fun j => b (j + 1) ≫ (moorePowerSequence p X).step j) a = a := funext ha
  have himage (k : ℕ) : ∃ b : U ⟶ X,
      b ≫ HasFunctorialCofiber.cofibι (moorePowerMap p X k) = a k := by
    have hiter := Function.iterate_fixed
      (f := fun b : ∀ k, U ⟶ (moorePowerSequence p X).obj k =>
        fun j => b (j + 1) ≫ (moorePowerSequence p X).step j) (x := a) hfix N
    simpa only [hiter] using
      moorePowerSequence_iterate_mem_inclusion p X U hU a k
  have hdesc (m : ℕ) : ∀ k, k ≤ m → ∀ b : U ⟶ X,
      b ≫ HasFunctorialCofiber.cofibι (moorePowerMap p X m) = a m →
        b ≫ HasFunctorialCofiber.cofibι (moorePowerMap p X k) = a k := by
    induction m with
    | zero =>
      intro k hk b hb
      have : k = 0 := by omega
      subst k
      exact hb
    | succ m ih =>
      intro k hk b hb
      by_cases hkm : k = m + 1
      · subst k; exact hb
      · apply ih k (by omega) b
        calc
          _ = (b ≫ HasFunctorialCofiber.cofibι (moorePowerMap p X (m + 1))) ≫
              (moorePowerSequence p X).step m := by
                rw [Category.assoc, moorePowerSequence_inclusion_step]
          _ = a m := by rw [hb, ha]
  obtain ⟨b, hb⟩ := himage N
  refine ⟨b, ?_, ?_⟩
  · intro k
    obtain ⟨c, hc⟩ := himage (k + N)
    have hcN := hdesc (k + N) N (by omega) c hc
    have hcb : c = b := moorePowerSequence_inclusion_injective_of_torsion p X U
      hU (Nat.le_refl N) (hcN.trans hb.symm)
    subst c
    exact hdesc (k + N) k (by omega) b hc
  · intro c hc
    exact moorePowerSequence_inclusion_injective_of_torsion p X U
      hU (Nat.le_refl N) ((hc N).trans hb.symm)

variable [HasProductsOfShape ℕ C]

/-- The actual product difference map is surjective on torsion represented
groups; this is the Milnor derived-limit vanishing needed for uniqueness. -/
theorem moorePowerSequence_postcomp_oneSubShift_surjective_of_torsion
    (p : ℕ) (X U : C) {N : ℕ} (hU : p ^ N • 𝟙 U = 0) :
    Function.Surjective (fun a : U ⟶ ∏ᶜ (moorePowerSequence p X).obj =>
      a ≫ (moorePowerSequence p X).oneSubShift) := by
  intro b
  obtain ⟨a, ha⟩ := moorePowerSequence_sub_shift_surjective_of_torsion p X U hU
    (fun k => b ≫ Pi.π (moorePowerSequence p X).obj k)
  refine ⟨Pi.lift a, ?_⟩
  apply Pi.hom_ext
  intro k
  simpa only [InverseSequence.oneSubShift, InverseSequence.shiftMap,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Category.assoc, Pi.lift_π, Pi.lift_π_assoc] using congrFun ha k

end Tower

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]

/-- Maps from torsion objects into the constructed Moore limit are
determined by their actual projections. -/
theorem mooreCompletion_hom_ext_of_torsion (p : ℕ) (X U : C)
    {N : ℕ} (hU : p ^ N • 𝟙 U = 0) {a b : U ⟶ mooreCompletion p X}
    (hab : ∀ k, a ≫ (moorePowerSequence p X).homotopyLimitWitness.π k =
      b ≫ (moorePowerSequence p X).homotopyLimitWitness.π k) : a = b := by
  let e := (shiftFunctorZero C ℤ).hom.app U
  apply (cancel_epi e).mp
  apply (moorePowerSequence p X).homotopyLimitWitness.shiftedHom_ext_of_surjective U 0
  · exact moorePowerSequence_postcomp_oneSubShift_surjective_of_torsion p X (U⟦(1 : ℤ)⟧)
      (nsmul_pow_id_shift_eq_zero p hU 1)
  · intro k
    simpa only [Category.assoc] using congrArg (fun f => e ≫ f) (hab k)

/-- Every actual unit with the prescribed Moore projections is an
equivalence on maps from bounded-torsion objects. -/
theorem mooreCompletion_unit_postcomp_bijective_of_torsion (p : ℕ) (X U : C)
    {N : ℕ} (hU : p ^ N • 𝟙 U = 0) (u : X ⟶ mooreCompletion p X)
    (hu : ∀ k, u ≫ (moorePowerSequence p X).homotopyLimitWitness.π k =
      HasFunctorialCofiber.cofibι (moorePowerMap p X k)) :
    Function.Bijective (fun b : U ⟶ X => b ≫ u) := by
  constructor
  · intro a b hab
    apply moorePowerSequence_inclusion_injective_of_torsion p X U hU (Nat.le_refl N)
    have h := congrArg (fun f => f ≫ (moorePowerSequence p X).homotopyLimitWitness.π N) hab
    simpa only [Category.assoc, hu] using h
  · intro a
    obtain ⟨b, hb, _⟩ := moorePowerSequence_existsUnique_compatible_of_torsion p X U hU
      (fun k => a ≫ (moorePowerSequence p X).homotopyLimitWitness.π k) (fun k => by
        rw [Category.assoc, SequentialHomotopyLimit.π_step])
    refine ⟨b, mooreCompletion_hom_ext_of_torsion p X U hU (fun k => ?_)⟩
    rw [Category.assoc, hu]
    exact hb k

end KIP126.StableHomotopy
