import KIP126.Def.Synthetic.PageExtension.Ambiguity.Predicates
import KIP126.Def.Synthetic.PageExtension.Proofs

namespace KIP126.Synthetic.PageExtension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams

universe u v u' v'

theorem elementMap_sub {A : ModuleCat.{v} ℤ} (x y : A) :
    elementMap (x - y) = elementMap x - elementMap y := by
  ext a
  simp [elementMap, smul_sub]

set_option backward.isDefEq.respectTransparency false in
/-- Categorical factorization through an actual module subobject is exactly
element membership in its arrow's range. -/
theorem factors_elementMap_iff {A : ModuleCat.{v} ℤ} (B : Subobject A) (z : A) :
    B.Factors (elementMap z) ↔ z ∈ LinearMap.range B.arrow.hom := by
  constructor
  · intro h
    refine ⟨(B.factorThru (elementMap z) h).hom (ULift.up 1), ?_⟩
    have he := congrArg (fun g => g.hom (ULift.up (1 : ℤ)))
      (B.factorThru_arrow (elementMap z) h)
    calc
      _ = (elementMap z).hom (ULift.up (1 : ℤ)) := he
      _ = z := by simp [elementMap]
  · rintro ⟨b, hb⟩
    have he : elementMap b ≫ B.arrow = elementMap z := by
      ext a
      simp only [elementMap, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
      simpa only [Int.cast_id, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hb] using
        (map_intCast_smul B.arrow.hom.toAddMonoidHom ℤ ℤ
          (ULift.moduleEquiv (R := ℤ) a) b)
    rw [← he]
    exact Subobject.factors_comp_arrow _

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}
  {P : NormalizedPageFamily H N F f}

namespace FiniteExtensionWitness
variable {r : ℕ} {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
  {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
  (W : FiniteExtensionWitness P r n s t x y)

/-- The inverse image of the actual ESS ambiguity, provided the two precise
comparison obligations hold. No surjectivity of the entire target map is
needed: only the stipulated shorter-image submodule maps onto the boundary. -/
theorem essBoundaries_comap_eq (hK : W.ClassicalBoundaryKernel)
    (hS : W.ShorterImagesCompatible) :
    W.essBoundaries.comap W.scaledTargetMap =
      W.ordinaryBoundaries ⊔ W.shorterImages := by
  change LinearMap.ker W.scaledTargetMap = W.ordinaryBoundaries at hK
  change W.shorterImages.map W.scaledTargetMap = W.essBoundaries at hS
  rw [← hS, Submodule.comap_map_eq, hK, sup_comm]

set_option backward.isDefEq.respectTransparency false in
/-- MainPaper's classical boundary-plus-shorter-images formula, for this
actual witness and under the separately visible comparison conditions. -/
theorem mem_targetCoset_iff (hK : W.ClassicalBoundaryKernel)
    (hS : W.ShorterImagesCompatible) (z : W.TargetCycles) :
    z ∈ W.targetCoset ↔
      W.targetCycle - z ∈ W.ordinaryBoundaries ⊔ W.shorterImages := by
  simp only [targetCoset, KIP126.Synthetic.PageExtension.targetCoset,
    Set.mem_setOf_eq, ← elementMap_sub, factors_elementMap_iff, ← map_sub]
  change W.targetCycle - z ∈ W.essBoundaries.comap W.scaledTargetMap ↔ _
  rw [W.essBoundaries_comap_eq hK hS]

theorem targetCoset_eq (hK : W.ClassicalBoundaryKernel)
    (hS : W.ShorterImagesCompatible) :
    W.targetCoset =
      {z | W.targetCycle - z ∈ W.ordinaryBoundaries ⊔ W.shorterImages} := by
  ext z
  exact W.mem_targetCoset_iff hK hS z

theorem essential_iff_not_mem_ambiguity (hK : W.ClassicalBoundaryKernel)
    (hS : W.ShorterImagesCompatible) :
    W.Essential ↔ W.targetCycle ∉ W.ordinaryBoundaries ⊔ W.shorterImages := by
  rw [W.essential_iff_zero_not_mem_targetCoset, W.mem_targetCoset_iff hK hS]
  simp only [sub_zero]

end FiniteExtensionWitness

namespace InfiniteExtensionWitness
variable {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
  {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
  (W : InfiniteExtensionWitness P n s t x y)

theorem essBoundaries_comap_eq (hK : W.ClassicalBoundaryKernel)
    (hS : W.ShorterImagesCompatible) :
    W.essBoundaries.comap W.scaledTargetMap =
      W.ordinaryBoundaries ⊔ W.shorterImages := by
  change LinearMap.ker W.scaledTargetMap = W.ordinaryBoundaries at hK
  change W.shorterImages.map W.scaledTargetMap = W.essBoundaries at hS
  rw [← hS, Submodule.comap_map_eq, hK, sup_comm]

set_option backward.isDefEq.respectTransparency false in
theorem mem_targetCoset_iff (hK : W.ClassicalBoundaryKernel)
    (hS : W.ShorterImagesCompatible) (z : W.TargetCycles) :
    z ∈ W.targetCoset ↔
      W.targetCycle - z ∈ W.ordinaryBoundaries ⊔ W.shorterImages := by
  simp only [targetCoset, KIP126.Synthetic.PageExtension.targetCoset,
    Set.mem_setOf_eq, ← elementMap_sub, factors_elementMap_iff, ← map_sub]
  change W.targetCycle - z ∈ W.essBoundaries.comap W.scaledTargetMap ↔ _
  rw [W.essBoundaries_comap_eq hK hS]

theorem targetCoset_eq (hK : W.ClassicalBoundaryKernel)
    (hS : W.ShorterImagesCompatible) :
    W.targetCoset =
      {z | W.targetCycle - z ∈ W.ordinaryBoundaries ⊔ W.shorterImages} := by
  ext z
  exact W.mem_targetCoset_iff hK hS z

theorem essential_iff_not_mem_ambiguity (hK : W.ClassicalBoundaryKernel)
    (hS : W.ShorterImagesCompatible) :
    W.Essential ↔ W.targetCycle ∉ W.ordinaryBoundaries ⊔ W.shorterImages := by
  rw [W.essential_iff_zero_not_mem_targetCoset, W.mem_targetCoset_iff hK hS]
  simp only [sub_zero]

end InfiniteExtensionWitness
end KIP126.Synthetic.PageExtension
