module

public import KIP126.Def.Topology.Simplex.FiniteFiber.Data

@[expose] public section

namespace KIP126.Topology.Simplex

open Finset
open scoped Classical

@[simp] theorem mem_positiveSupport {A : Type*} [Fintype A]
    (x : stdSimplex ℝ A) (a : A) : a ∈ positiveSupport x ↔ 0 < x a := by
  classical
  simp only [positiveSupport, mem_filter, mem_univ, true_and]

/-- Nonnegative barycentric pushforward has precisely the image support,
including when the vertex map identifies vertices. -/
theorem positiveSupport_map {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (x : stdSimplex ℝ A) :
    positiveSupport (stdSimplex.map f x) = (positiveSupport x).image f := by
  classical
  ext b
  simp only [mem_positiveSupport, mem_image]
  change (0 < FunOnFinite.linearMap ℝ ℝ f x b) ↔ _
  rw [FunOnFinite.linearMap_apply_apply]
  rw [sum_pos_iff_of_nonneg (fun a _ => stdSimplex.zero_le x a)]
  simp only [mem_filter, mem_univ, true_and, mem_positiveSupport]
  aesop

/-- A vertex map injective on the actual support retains every positive
coordinate even if it identifies vertices elsewhere. -/
theorem map_apply_of_injOn_positiveSupport {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (x : stdSimplex ℝ A)
    (hf : Set.InjOn f (positiveSupport x)) (a : A) (ha : a ∈ positiveSupport x) :
    stdSimplex.map f x (f a) = x a := by
  classical
  change FunOnFinite.linearMap ℝ ℝ f x (f a) = x a
  rw [FunOnFinite.linearMap_apply_apply]
  apply sum_eq_single a
  · intro b hb hba
    by_cases hpos : 0 < x b
    · exact (hba (hf ((mem_positiveSupport x b).mpr hpos) ha (mem_filter.mp hb).2)).elim
    · exact le_antisymm (le_of_not_gt hpos) (stdSimplex.zero_le x b)
  · intro h
    exact (h (mem_filter.mpr ⟨mem_univ _, rfl⟩)).elim

/-- An injective vertex map on a specified positive support determines
the entire barycentric point from its pushforward. -/
theorem eq_of_map_eq_of_positiveSupport_eq {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (x y : stdSimplex ℝ A)
    (hs : positiveSupport x = positiveSupport y)
    (hf : Set.InjOn f (positiveSupport x)) (hxy : stdSimplex.map f x = stdSimplex.map f y) :
    x = y := by
  apply stdSimplex.ext
  funext a
  by_cases ha : a ∈ positiveSupport x
  · have hb : a ∈ positiveSupport y := hs ▸ ha
    have hf' : Set.InjOn f (positiveSupport y) := hs ▸ hf
    exact (map_apply_of_injOn_positiveSupport f x hf a ha).symm.trans
      ((congrArg (fun z : stdSimplex ℝ B => z (f a)) hxy).trans
        (map_apply_of_injOn_positiveSupport f y hf' a hb))
  · have hb : a ∉ positiveSupport y := hs ▸ ha
    have hx : x a = 0 := le_antisymm (le_of_not_gt (by simpa using ha)) (stdSimplex.zero_le x a)
    have hy : y a = 0 := le_antisymm (le_of_not_gt (by simpa using hb)) (stdSimplex.zero_le y a)
    exact hx.trans hy.symm

/-- Over a point with N positive target coordinates, source points with
at most N positive coordinates form an actual finite fiber. -/
theorem finite_fiber_of_positiveSupport_card {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (y : stdSimplex ℝ B) (N : ℕ) (hy : (positiveSupport y).card = N) :
    Finite {x : stdSimplex ℝ A // (positiveSupport x).card ≤ N ∧ stdSimplex.map f x = y} := by
  classical
  apply Finite.of_injective (fun (x : {x : stdSimplex ℝ A //
    (positiveSupport x).card ≤ N ∧ stdSimplex.map f x = y}) => positiveSupport x.val)
  intro x z hxz
  apply Subtype.ext
  have himage : (positiveSupport x.val).image f = positiveSupport y := by
    rw [← positiveSupport_map, x.property.2]
  have hcard : ((positiveSupport x.val).image f).card = (positiveSupport x.val).card := by
    apply le_antisymm (card_image_le)
    rw [himage, hy]
    exact x.property.1
  exact eq_of_map_eq_of_positiveSupport_eq f x.val z.val hxz
    (injOn_of_card_image_eq hcard) (x.property.2.trans z.property.2.symm)

end KIP126.Topology.Simplex
