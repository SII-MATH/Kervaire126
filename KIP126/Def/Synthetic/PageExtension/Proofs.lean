import KIP126.Def.Synthetic.PageExtension.Predicates
import KIP126.Def.Synthetic.PageExtension.Relation.Proofs
import KIP126.Def.Synthetic.PageExtension.Lambda.Proofs

namespace KIP126.Synthetic.PageExtension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.Core.SpectralSequence

universe u v u' v'
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}
  {P : NormalizedPageFamily H N F f}

theorem NormalizedPageFamily.lambdaExponent_coe (n : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) :
    (P.lambdaExponent n : ℤ) = n - normalizedExponent H f :=
  Int.toNat_of_nonneg (sub_nonneg.mpr hn)

namespace FiniteExtensionWitness
variable {r : ℕ} {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
  {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
  (W : FiniteExtensionWitness P r n s t x y)

include W in
/-- The finite λ-map's genuine domain condition gives exactly the paper's
upper length bound. -/
theorem length_le_page : n ≤ (r : ℤ) - 2 + normalizedExponent H f := by
  have he := P.lambdaExponent_coe n W.exponent_le_length
  have hk := W.exponent_lt_quotient
  have hr := W.page_ge_two
  omega

include W in
theorem targetCycleLevel_eq :
    ((r - 1 - P.lambdaExponent n : ℕ) : ℤ) =
      (r : ℤ) - 1 - n + normalizedExponent H f := by
  have he := P.lambdaExponent_coe n W.exponent_le_length
  have hk := W.exponent_lt_quotient
  have hr := W.page_ge_two
  omega

set_option backward.isDefEq.respectTransparency false in
theorem target_mem_targetCoset : W.targetCycle ∈ W.targetCoset := by
  dsimp only [targetCoset, Set.mem_setOf_eq]
  exact self_mem_targetCoset _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- This tests the complete inverse image of the actual ESS ambiguity.
The separate comparison-coherence problem is not used or claimed here. -/
theorem essential_iff_zero_not_mem_targetCoset :
    W.Essential ↔ 0 ∉ W.targetCoset := by
  simpa only [Essential, targetCoset, Set.mem_setOf_eq, map_zero, elementMap_zero] using
    (KIP126.Synthetic.PageExtension.essential_iff_zero_not_mem_targetCoset _ _ _ W.relation)

end FiniteExtensionWitness

namespace InfiniteExtensionWitness
variable {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
  {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
  (W : InfiniteExtensionWitness P n s t x y)

set_option backward.isDefEq.respectTransparency false in
theorem target_mem_targetCoset : W.targetCycle ∈ W.targetCoset := by
  dsimp only [targetCoset, Set.mem_setOf_eq]
  exact self_mem_targetCoset _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem essential_iff_zero_not_mem_targetCoset :
    W.Essential ↔ 0 ∉ W.targetCoset := by
  simpa only [Essential, targetCoset, Set.mem_setOf_eq, map_zero, elementMap_zero] using
    (KIP126.Synthetic.PageExtension.essential_iff_zero_not_mem_targetCoset _ _ _ W.relation)

end InfiniteExtensionWitness
end KIP126.Synthetic.PageExtension
