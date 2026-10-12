module

public import KIP126.Def.Topology.SimplicialRealization.Horn.Data
public import KIP126.Def.Topology.SimplicialRealization.Boundary.Proofs
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The omitted-coordinate minimum is nonnegative. -/
theorem hornMin_nonneg {n : ℕ} (i : Fin (n+2))
    (x : stdSimplex ℝ (Fin (n+2))) : 0 ≤ hornMin i x := by
  exact Finset.le_inf' _ _ (fun j _ => x.property.1 _)

/-- This minimum is bounded by each coordinate other than the distinguished one. -/
theorem hornMin_le {n : ℕ} (i : Fin (n+2))
    (x : stdSimplex ℝ (Fin (n+2))) (j : Fin (n+2)) (hji : j ≠ i) :
    hornMin i x ≤ x j := by
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
  exact Finset.inf'_le _ (Finset.mem_univ _)

/-- The minimum is attained at a vertex other than the distinguished one. -/
theorem hornMin_attained {n : ℕ} (i : Fin (n+2))
    (x : stdSimplex ℝ (Fin (n+2))) :
    ∃ j, j ≠ i ∧ hornMin i x = x j := by
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j : Fin (n+1) => x (i.succAbove j))
  exact ⟨i.succAbove k,Fin.succAbove_ne i k,hk⟩

/-- A finite minimum of barycentric coordinates varies continuously. -/
theorem continuous_hornMin {n : ℕ} (i : Fin (n+2)) : Continuous (hornMin i) := by
  apply Continuous.finset_inf'_apply
  intro j _
  exact (continuous_apply _).comp continuous_subtype_val

/-- The explicit retraction has nonnegative coordinates. -/
theorem hornRetractionCoordinates_nonneg {n : ℕ} (i : Fin (n+2))
    (x : stdSimplex ℝ (Fin (n+2))) (j : Fin (n+2)) :
    0 ≤ hornRetractionCoordinates i x j := by
  by_cases h : j = i
  · simp only [hornRetractionCoordinates,if_pos h]
    exact add_nonneg (x.property.1 _) (mul_nonneg (Nat.cast_nonneg _) (hornMin_nonneg i x))
  · simp only [hornRetractionCoordinates,if_neg h]
    exact sub_nonneg.mpr (hornMin_le i x j h)

/-- Transferring the common minimum preserves the total barycentric mass. -/
theorem hornRetractionCoordinates_sum {n : ℕ} (i : Fin (n+2))
    (x : stdSimplex ℝ (Fin (n+2))) :
    ∑ j, hornRetractionCoordinates i x j = 1 := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [hornRetractionCoordinates, Fin.succAbove_ne, ↓reduceIte]
  rw [Finset.sum_sub_distrib]
  have hx := stdSimplex.sum_eq_one x
  rw [Fin.sum_univ_succAbove _ i] at hx
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  linarith

/-- Retraction coordinates vary continuously. -/
theorem continuous_hornRetractionCoordinates {n : ℕ} (i : Fin (n+2)) :
    Continuous (hornRetractionCoordinates i) := by
  apply continuous_pi
  intro j
  by_cases h : j = i
  · simp only [hornRetractionCoordinates,if_pos h]
    exact ((continuous_apply _).comp continuous_subtype_val).add
      (continuous_const.mul (continuous_hornMin i))
  · simp only [hornRetractionCoordinates,if_neg h]
    exact ((continuous_apply _).comp continuous_subtype_val).sub (continuous_hornMin i)

/-- At least one retracted coordinate other than the distinguished one is zero. -/
theorem hornRetractionCoordinates_mem {n : ℕ} (i : Fin (n+2))
    (x : stdSimplex ℝ (Fin (n+2))) :
    ∃ j, j ≠ i ∧ hornRetractionCoordinates i x j = 0 := by
  obtain ⟨j,hji,hj⟩ := hornMin_attained i x
  exact ⟨j,hji,by simp [hornRetractionCoordinates,hji,hj]⟩

/-- Every point already on the geometric horn is fixed by the retraction. -/
theorem hornRetractionCoordinates_fixed {n : ℕ} (i : Fin (n+2))
    (x : stdSimplex ℝ (Fin (n+2))) (hx : ∃ j, j ≠ i ∧ x j = 0) :
    hornRetractionCoordinates i x = x.val := by
  obtain ⟨j,hji,hj⟩ := hx
  have hm : hornMin i x = 0 :=
    le_antisymm ((hornMin_le i x j hji).trans_eq hj) (hornMin_nonneg i x)
  funext k
  simp only [hornRetractionCoordinates,hm,mul_zero,add_zero,sub_zero]
  split_ifs with h
  · subst k; rfl
  · rfl

/-- The realization of an actual simplicial horn is exactly the union of
all geometric faces other than the omitted face. -/
theorem horn_realization_range (n : ℕ) (i : Fin (n+2))
    (p : stdSimplex ℝ (Fin (n+2))) :
    p ∈ Set.range (fun x : |(Λ[n+1,i] : SSet.{u})| =>
      SimplexCategory.toTopHomeo ⦋n+1⦌ (SSet.toTop.map (Λ[n+1,i]).ι x)) ↔
      ∃ j, j ≠ i ∧ p j = 0 := by
  classical
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨S,hS,hSA,a,rfl⟩ := subcomplex_point_lies_in_face (Λ[n+1,i]) x
    have hproper : ∃ j, j ≠ i ∧ j ∉ S := by
      by_contra! h
      have hsub : ({i}ᶜ : Finset (Fin (n+2))) ⊆ S := by
        intro j hj
        exact h j (by simpa using hj)
      exact (SSet.subcomplex_le_horn_iff _ i).mp hSA
        ((SSet.stdSimplex.face_le_face_iff _ _).mpr hsub)
    obtain ⟨j,hji,hj⟩ := hproper
    refine ⟨j,hji,?_⟩
    change (SimplexCategory.toTopHomeo ⦋n+1⦌
      (SSet.toTop.map (Λ[n+1,i]).ι
        (SSet.toTop.map (SSet.Subcomplex.homOfLE hSA) a))) j = 0
    rw [subcomplex_realization_inclusion_apply]
    exact (face_realization_range S hS _).mp ⟨a,rfl⟩ j hj
  · rintro ⟨j,hji,hj⟩
    have hS : ({j}ᶜ : Finset (Fin (n+2))).Nonempty :=
      ⟨i,by simpa using hji.symm⟩
    have hsupport : ∀ k, k ∉ ({j}ᶜ : Finset (Fin (n+2))) → p k = 0 := by
      intro k hk
      have : k = j := by simpa using hk
      simpa only [this] using hj
    obtain ⟨a,ha⟩ := (face_realization_range {j}ᶜ hS p).mpr hsupport
    refine ⟨SSet.toTop.map (SSet.Subcomplex.homOfLE (SSet.face_le_horn j i hji)) a,?_⟩
    exact (subcomplex_realization_inclusion_apply (SSet.face_le_horn j i hji) a).trans ha

/-- The actual simplicial horn and its geometric coordinate model are
homeomorphic, compatibly with the specified horn inclusion. -/
theorem exists_horn_realization_homeomorph (n : ℕ) (i : Fin (n+2)) :
    ∃ e : |(Λ[n+1,i] : SSet.{u})| ≃ₜ
      {p : stdSimplex ℝ (Fin (n+2)) // ∃ j, j ≠ i ∧ p j = 0},
      ∀ x, (e x).1 = SimplexCategory.toTopHomeo ⦋n+1⦌
        (SSet.toTop.map (Λ[n+1,i]).ι x) := by
  letI : SSet.Finite (Λ[n+1,i] : SSet.{u}) := SSet.finite_of_mono (Λ[n+1,i]).ι
  letI : CompactSpace |(Λ[n+1,i] : SSet.{u})| := compactSpace_of_finite _
  let f : |(Λ[n+1,i] : SSet.{u})| →
      {p : stdSimplex ℝ (Fin (n+2)) // ∃ j, j ≠ i ∧ p j = 0} := fun x =>
    ⟨SimplexCategory.toTopHomeo ⦋n+1⦌ (SSet.toTop.map (Λ[n+1,i]).ι x),
      (horn_realization_range n i _).mp ⟨x,rfl⟩⟩
  have hf : Continuous f := ((SimplexCategory.toTopHomeo ⦋n+1⦌).continuous.comp
    (SSet.toTop.map (Λ[n+1,i]).ι).hom.continuous).subtype_mk _
  have hb : Function.Bijective f := by
    constructor
    · intro x y h
      exact subcomplex_realization_injective (Λ[n+1,i]) (congrArg Subtype.val h)
    · intro y
      obtain ⟨x,hx⟩ := (horn_realization_range n i y.1).mpr y.2
      exact ⟨x,Subtype.ext hx⟩
  let e : |(Λ[n+1,i] : SSet.{u})| ≃ _ := Equiv.ofBijective f hb
  exact ⟨hf.homeoOfEquivCompactToT2 (f := e),fun _ => rfl⟩

/-- Every actual realized horn inclusion has a continuous retraction,
constructed by moving the least non-distinguished barycentric coordinate
to the distinguished vertex. -/
theorem exists_horn_realization_retraction (n : ℕ) (i : Fin (n+2)) :
    ∃ r : C(|(Δ[n+1] : SSet.{u})|, |(Λ[n+1,i] : SSet.{u})|),
      ∀ x, r (SSet.toTop.map (Λ[n+1,i]).ι x) = x := by
  obtain ⟨e,he⟩ := exists_horn_realization_homeomorph.{u} n i
  let R : C(stdSimplex ℝ (Fin (n+2)),stdSimplex ℝ (Fin (n+2))) := {
    toFun := fun x => ⟨hornRetractionCoordinates i x,
      hornRetractionCoordinates_nonneg i x,hornRetractionCoordinates_sum i x⟩
    continuous_toFun := (continuous_hornRetractionCoordinates i).subtype_mk _ }
  let r : C(|(Δ[n+1] : SSet.{u})|, |(Λ[n+1,i] : SSet.{u})|) := {
    toFun := fun x => e.symm ⟨R (SimplexCategory.toTopHomeo ⦋n+1⦌ x),
      hornRetractionCoordinates_mem i _⟩
    continuous_toFun := e.symm.continuous.comp
      ((R.continuous.comp (SimplexCategory.toTopHomeo ⦋n+1⦌).continuous).subtype_mk _) }
  refine ⟨r,?_⟩
  intro x
  apply e.injective
  change e (e.symm _) = e x
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change R (SimplexCategory.toTopHomeo ⦋n+1⦌ (SSet.toTop.map (Λ[n+1,i]).ι x)) = (e x).val
  rw [← he x]
  apply stdSimplex.ext
  exact hornRetractionCoordinates_fixed i (e x).val (e x).property

end KIP126.Topology.SimplicialRealization
