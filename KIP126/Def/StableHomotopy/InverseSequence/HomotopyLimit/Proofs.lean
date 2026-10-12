module

public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Data
public import KIP126.Def.StableHomotopy.InverseSequence.Proofs
public import KIP126.Def.StableHomotopy.FiniteType.Predicates
public import KIP126.Def.Algebra.InverseSequence.Surjective.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits

universe u v

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasProductsOfShape ℕ C]

/-- Surjective transition maps on represented groups eliminate the
derived-limit obstruction to solving the Milnor difference equation. -/
theorem InverseSequence.postcomp_oneSubShift_surjective_of_surjective
    (D : InverseSequence C) (W : C)
    (hD : ∀ k, Function.Surjective (fun a : W ⟶ D.obj (k + 1) => a ≫ D.step k)) :
    Function.Surjective (fun a : W ⟶ ∏ᶜ D.obj => a ≫ D.oneSubShift) := by
  intro b
  let f (k : ℕ) : (W ⟶ D.obj (k + 1)) →+ (W ⟶ D.obj k) :=
    { toFun := fun a => a ≫ D.step k
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.add_comp] }
  obtain ⟨a, ha⟩ := KIP126.Core.InverseSequence.surjective_sub_shift_of_surjective
    (fun k => W ⟶ D.obj k) f hD (fun k => b ≫ Pi.π D.obj k)
  refine ⟨Pi.lift a, ?_⟩
  apply Pi.hom_ext
  intro k
  simpa only [InverseSequence.oneSubShift, InverseSequence.shiftMap,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Category.assoc, Pi.lift_π, Pi.lift_π_assoc, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    using congrFun ha k

end Preadditive

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasProductsOfShape ℕ C]

/-- Vanishing at every stage and surjective next-degree transitions imply
vanishing in the homotopy limit, with its derived-limit term accounted for. -/
theorem SequentialHomotopyLimit.homotopy_subsingleton_of_surjective
    {D : InverseSequence C} {L : C} (H : SequentialHomotopyLimit D L) (n : ℤ)
    [∀ k, Subsingleton (HomotopyGroup n (D.obj k))]
    (hD : ∀ k, Function.Surjective (inducedMap (D.step k) (n + 1))) :
    Subsingleton (HomotopyGroup n L) := by
  let T : HoCofiberSequence (C := C) :=
    ⟨L, ∏ᶜ D.obj, ∏ᶜ D.obj, H.toProduct, D.oneSubShift, H.boundary, H.distinguished⟩
  have hzero (a : HomotopyGroup ((n + 1) - 1) L) : a = 0 := by
    have hprod : a ≫ H.toProduct = 0 := by
      apply Pi.hom_ext
      intro k
      letI : Subsingleton (HomotopyGroup ((n + 1) - 1) (D.obj k)) := by
        simpa only [add_sub_cancel_right] using
          (inferInstance : Subsingleton (HomotopyGroup n (D.obj k)))
      exact Subsingleton.elim _ _
    have hp : inducedMap T.f ((n + 1) - 1) a = 0 := hprod
    obtain ⟨z, hz⟩ := (lesHomotopyExactH T (n + 1) a).mp hp
    have hc : connectingHomomorphism T (n + 1) z = 0 := by
      apply (les_homotopy_exact_g T (n + 1) z).mpr
      exact D.postcomp_oneSubShift_surjective_of_surjective (Sphere (n + 1)) hD z
    exact hz.symm.trans hc
  have h : Subsingleton (HomotopyGroup ((n + 1) - 1) L) :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  simpa only [add_sub_cancel_right] using h

/-- The finite next-degree groups remove the derived-limit contribution
when every stage vanishes in the specified degree. -/
theorem SequentialHomotopyLimit.homotopy_subsingleton_of_finite
    {D : InverseSequence C} {L : C} (H : SequentialHomotopyLimit D L) (n : ℤ)
    [∀ k, Subsingleton (HomotopyGroup n (D.obj k))]
    [∀ k, Finite (HomotopyGroup (n + 1) (D.obj k))] :
    Subsingleton (HomotopyGroup n L) :=
  ⟨fun _ _ => H.homotopy_ext_of_finite n (fun _ => Subsingleton.elim _ _)⟩

/-- A uniform lower bound survives the homotopy limit when the groups in
the first possibly nonzero degree are finite at every stage. -/
theorem SequentialHomotopyLimit.homotopy_subsingleton_of_uniform_bound
    {D : InverseSequence C} {L : C} (H : SequentialHomotopyLimit D L) (N : ℤ)
    (hD : ∀ k n, n < N → Subsingleton (HomotopyGroup n (D.obj k)))
    (hfinite : ∀ k, Finite (HomotopyGroup N (D.obj k)))
    (n : ℤ) (hn : n < N) : Subsingleton (HomotopyGroup n L) := by
  letI : ∀ k, Subsingleton (HomotopyGroup n (D.obj k)) := fun k => hD k n hn
  letI : ∀ k, Finite (HomotopyGroup (n + 1) (D.obj k)) := fun k => by
    by_cases h : n + 1 = N
    · rw [h]
      exact hfinite k
    · letI := hD k (n + 1) (by omega)
      infer_instance
  exact H.homotopy_subsingleton_of_finite n

variable [HasFunctorialCofiber (C := C)]

/-- Connectivity of the homotopy limit constructed from `1 - shift`.
Only the boundary-degree finiteness is needed, including degree zero
when deriving connectivity of a Moore completion tower. -/
theorem InverseSequence.homotopyLimit_boundedBelow (D : InverseSequence C) (N : ℤ)
    (hD : ∀ k n, n < N → Subsingleton (HomotopyGroup n (D.obj k)))
    (hfinite : ∀ k, Finite (HomotopyGroup N (D.obj k))) :
    BoundedBelow D.homotopyLimit :=
  ⟨N, D.homotopyLimitWitness.homotopy_subsingleton_of_uniform_bound N hD hfinite⟩

end KIP126.StableHomotopy
