module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory _root_.Topology
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

theorem mappingCylinderMk_inl_eq_bottom_iff {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x z : X.level n) (s : I) :
    mappingCylinderMk f n (.inl (x,s)) = (mappingCylinderInclusion f).level n z ↔
      (s = 0 ∧ x = z) ∨
        (z = (X.level n).point ∧
          (x = (X.level n).point ∨ (s = 1 ∧ f.level n x = (Y.level n).point))) := by
  change mappingCylinderMk f n (.inl (x,s)) = mappingCylinderMk f n (.inl (z,0)) ↔ _
  rw [mappingCylinderMk_eq_iff]
  by_cases hx : x = (X.level n).point <;>
    by_cases hz : z = (X.level n).point <;>
    by_cases hs : s = 1 <;>
    simp_all [mappingCylinderNormalize,Prod.ext_iff,and_comm,eq_comm]

theorem mappingCylinderMk_inr_eq_bottom_iff {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (y : Y.level n) (z : X.level n) :
    mappingCylinderMk f n (.inr y) = (mappingCylinderInclusion f).level n z ↔
      z = (X.level n).point ∧ y = (Y.level n).point := by
  change mappingCylinderMk f n (.inr y) = mappingCylinderMk f n (.inl (z,0)) ↔ _
  rw [mappingCylinderMk_eq_iff]
  by_cases hz : z = (X.level n).point <;> simp [mappingCylinderNormalize,hz]

/-- No distinct source points are identified by the actual reduced quotient. -/
theorem mappingCylinderInclusion_injective {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Function.Injective ((mappingCylinderInclusion f).level n) := by
  intro x z h
  rcases (mappingCylinderMk_inl_eq_bottom_iff f n x z 0).mp h with h | ⟨hz,hx⟩
  · exact h.2
  · rcases hx with hx | ⟨h,_⟩
    · exact hx.trans hz.symm
    · exact zero_ne_one h |>.elim

/-- Exact preimage of a source subset, including the full collapsed basepoint fiber. -/
theorem mappingCylinderInclusion_preimage_image {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (C : Set (X.level n)) :
    mappingCylinderMk f n ⁻¹' ((mappingCylinderInclusion f).level n '' C) =
      Sum.inl '' (C ×ˢ {(0 : I)}) ∪
        (if (X.level n).point ∈ C then
          Sum.inl '' (({(X.level n).point} ×ˢ Set.univ) ∪
            ((f.level n ⁻¹' {(Y.level n).point}) ×ˢ {(1 : I)})) ∪
            Sum.inr '' {(Y.level n).point}
         else ∅) := by
  ext a
  rcases a with ⟨x,s⟩ | y
  · simp only [Set.mem_preimage,Set.mem_image]
    have he (z : X.level n) := (eq_comm (a := (mappingCylinderInclusion f).level n z)
      (b := mappingCylinderMk f n (.inl (x,s)))).trans
        (mappingCylinderMk_inl_eq_bottom_iff f n x z s)
    simp_rw [he]
    by_cases hc : (X.level n).point ∈ C <;> simp [hc,Set.mem_prod] <;> aesop
  · simp only [Set.mem_preimage,Set.mem_image]
    have he (z : X.level n) := (eq_comm (a := (mappingCylinderInclusion f).level n z)
      (b := mappingCylinderMk f n (.inr y))).trans
        (mappingCylinderMk_inr_eq_bottom_iff f n y z)
    simp_rw [he]
    by_cases hc : (X.level n).point ∈ C <;> simp [hc,Set.mem_prod]

/-- With actual T₁ source and target levels, the source is a closed subspace
of the actual reduced mapping cylinder. -/
theorem mappingCylinderInclusion_isClosedEmbedding {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) [T1Space (X.level n)] [T1Space (Y.level n)] :
    IsClosedEmbedding ((mappingCylinderInclusion f).level n) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    ((mappingCylinderInclusion f).level n).continuous
    (mappingCylinderInclusion_injective f n) ?_
  intro C hC
  apply (isQuotientMap_quot_mk.isCoinducing.isClosed_preimage).mp
  change IsClosed (mappingCylinderMk f n ⁻¹' ((mappingCylinderInclusion f).level n '' C))
  rw [mappingCylinderInclusion_preimage_image]
  apply (isClosedMap_inl _ (hC.prod isClosed_singleton)).union
  split_ifs
  · exact (isClosedMap_inl _ ((isClosed_singleton.prod isClosed_univ).union
      ((isClosed_singleton.preimage (f.level n).continuous).prod isClosed_singleton))).union
      (isClosedMap_inr _ isClosed_singleton)
  · exact isClosed_empty

theorem mappingCylinderMk_inl_eq_target_iff {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) (s : I) (y : Y.level n) :
    mappingCylinderMk f n (.inl (x,s)) = mappingCylinderMk f n (.inr y) ↔
      (s = 1 ∧ f.level n x = y) ∨
        (x = (X.level n).point ∧ y = (Y.level n).point) := by
  rw [mappingCylinderMk_eq_iff]
  by_cases hx : x = (X.level n).point <;> by_cases hs : s = 1 <;>
    simp_all [mappingCylinderNormalize,f.point,eq_comm]

theorem mappingCylinderMk_interior_fiber {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) (s : I) (hx : x ≠ (X.level n).point) (hs : s ≠ 1)
    (a : mappingCylinderRaw f n) :
    mappingCylinderMk f n a = mappingCylinderMk f n (.inl (x,s)) ↔ a = .inl (x,s) := by
  rw [mappingCylinderMk_eq_iff]
  rcases a with ⟨z,t⟩ | y
  · by_cases hz : z = (X.level n).point <;> by_cases ht : t = 1 <;>
      simp_all [mappingCylinderNormalize,Prod.ext_iff,eq_comm]
  · simp [mappingCylinderNormalize,hx,hs]

private theorem mappingCylinderMk_target_preimage_closed {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) [T1Space (X.level n)] [T1Space (Y.level n)] (y : Y.level n) :
    IsClosed (mappingCylinderMk f n ⁻¹' {mappingCylinderMk f n (.inr y)}) := by
  rw [isClosed_sum_iff]
  constructor
  · change IsClosed {z : X.level n × I |
      mappingCylinderMk f n (.inl z) = mappingCylinderMk f n (.inr y)}
    have he : {z : X.level n × I |
        mappingCylinderMk f n (.inl z) = mappingCylinderMk f n (.inr y)} =
        {z | (z.2 = 1 ∧ f.level n z.1 = y) ∨
          (z.1 = (X.level n).point ∧ y = (Y.level n).point)} := by
      ext ⟨x,s⟩
      exact mappingCylinderMk_inl_eq_target_iff f n x s y
    rw [he]
    by_cases hy : y = (Y.level n).point
    · simp only [hy,and_true]
      exact (isClosed_singleton.preimage continuous_snd |>.inter
        (isClosed_singleton.preimage ((f.level n).continuous.comp continuous_fst))).union
          (isClosed_singleton.preimage continuous_fst)
    · simp only [hy,and_false,or_false]
      exact (isClosed_singleton.preimage continuous_snd).inter
        (isClosed_singleton.preimage ((f.level n).continuous.comp continuous_fst))
  · change IsClosed {z : Y.level n |
      mappingCylinderMk f n (.inr z) = mappingCylinderMk f n (.inr y)}
    simp_rw [mappingCylinderMk_eq_iff]
    simpa only [mappingCylinderNormalize,Sum.inr.injEq,Set.setOf_eq_eq_singleton] using
      (isClosed_singleton : IsClosed ({y} : Set (Y.level n)))

/-- The actual reduced mapping-cylinder quotient retains the T₁ property. -/
instance mappingCylinderLevel_t1Space {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) [T1Space (X.level n)] [T1Space (Y.level n)] :
    T1Space (mappingCylinderLevel f n) where
  t1 z := by
    apply (isQuotientMap_quot_mk.isCoinducing.isClosed_preimage).mp
    obtain ⟨a,rfl⟩ := mappingCylinderMk_surjective f n z
    rcases a with ⟨x,s⟩ | y
    · by_cases hx : x = (X.level n).point
      · subst x
        rw [mappingCylinderMk_point]
        exact mappingCylinderMk_target_preimage_closed f n (Y.level n).point
      · by_cases hs : s = 1
        · subst s
          rw [mappingCylinderMk_top]
          exact mappingCylinderMk_target_preimage_closed f n (f.level n x)
        · change IsClosed {a : mappingCylinderRaw f n |
            mappingCylinderMk f n a = mappingCylinderMk f n (.inl (x,s))}
          simp_rw [mappingCylinderMk_interior_fiber f n x s hx hs]
          simpa only [Set.image_singleton,Set.setOf_eq_eq_singleton] using
            (isClosedMap_inl ({(x,s)} : Set (X.level n × I)) isClosed_singleton :
              IsClosed (Sum.inl '' ({(x,s)} : Set (X.level n × I)) : Set (mappingCylinderRaw f n)))
    · exact mappingCylinderMk_target_preimage_closed f n y

end KIP126.StableHomotopy.Implementation.Prespectrum
