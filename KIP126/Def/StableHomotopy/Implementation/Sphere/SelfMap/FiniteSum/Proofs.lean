module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.SelfMap.FiniteSum.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Source.Finite.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- The free/evaluation universal property retains the actual quotient
wedge and its original branch maps, for every indexing family. -/
noncomputable def sphereWedgeFreeCofan_isColimit {J : Type} (n : ℕ) (Y : J → BasedSpace) :
    IsColimit (sphereWedgeFreeCofan n Y) := by
  refine Cofan.IsColimit.mk _ (fun c =>
    (freeEvaluation n (BasedSpace.wedge Y) c.pt).symm
      (BasedSpace.wedgeDesc (fun j => freeEvaluation n (Y j) c.pt (c.inj j)))) ?_ ?_
  · intro c j
    apply (freeEvaluation n (Y j) c.pt).injective
    change freeEvaluation n (Y j) c.pt (freeMap n (BasedSpace.wedgeι Y j) ≫ _) = _
    rw [freeEvaluation_freeMap_comp,Equiv.apply_symm_apply,BasedSpace.wedgeι_desc]
  · intro c m hm
    apply (freeEvaluation n (BasedSpace.wedge Y) c.pt).injective
    rw [Equiv.apply_symm_apply]
    apply (BasedSpace.wedgeCofan_isColimit Y).hom_ext
    rintro ⟨j⟩
    change BasedSpace.wedgeι Y j ≫ freeEvaluation n (BasedSpace.wedge Y) c.pt m =
      BasedSpace.wedgeι Y j ≫ BasedSpace.wedgeDesc _
    rw [BasedSpace.wedgeι_desc,← freeEvaluation_freeMap_comp]
    exact congrArg (freeEvaluation n (Y j) c.pt) (hm j)

@[simp] theorem sphereWedgeι_projection_self {J : Type} (Y : J → BasedSpace) (j : J) :
    BasedSpace.wedgeι Y j ≫ sphereWedgeProjection Y j = 𝟙 (Y j) := by
  classical
  simp [sphereWedgeProjection]

@[simp] theorem sphereWedgeι_projection_ne {J : Type} (Y : J → BasedSpace)
    (j k : J) (h : j ≠ k) :
    BasedSpace.wedgeι Y j ≫ sphereWedgeProjection Y k =
      ⟨ContinuousMap.const _ (Y k).point,rfl⟩ := by
  classical
  simp [sphereWedgeProjection,h]

/-- The original sphere self-map class is exactly its actual free map,
normalized by the specified source sphere and followed by the original
free counit. This retains the given self-map without a degree hypothesis. -/
theorem sphereSelfMapClass_sourceMap (n : ℕ) (f : sphereLevel n ⟶ sphereLevel n) :
    sourceStableHomotopyAddEquiv sphere 0 (sphereSelfMapClass n f) =
      (sourceFreeSphereDegreeIso 0 n n (by omega)).inv ≫
        sourceLocalization.map (freeMap n f) ≫ sourceLocalization.map (freeCounit sphere n) := by
  let p := KIP126.Topology.continuousGenLoopMap f.map
    (sphereLevel n).point (sphereLevel n).point f.point n (sphereCube n)
  have hf : freeEvaluation n (sphereLevel n) sphere (freeMap n f ≫ freeCounit sphere n) = f := by
    rw [freeEvaluation_freeMap_comp]
    change f ≫ (freeEvaluation n (sphere.level n) sphere)
      ((freeEvaluation n (sphere.level n) sphere).symm (𝟙 _)) = f
    rw [Equiv.apply_symm_apply]
    rfl
  have hgen : genLoopFreeSphereMap sphere n n p = freeMap n f ≫ freeCounit sphere n := by
    apply ((genLoop_freeSphere_map_exists_unique sphere n n p).choose_spec.2 _ _).symm
    intro t
    have h := freeEvaluation_natural n (sphereLevel n) (𝟙 (free n (sphereLevel n)))
      (freeMap n f ≫ freeCounit sphere n)
    rw [Category.id_comp,hf] at h
    exact (congrArg (fun a : sphereLevel n ⟶ sphereLevel n => a.map (sphereCube n t)) h).symm
  change (sourceFreeSphereDegreeIso 0 n n _).inv ≫
    sourceLocalization.map (genLoopFreeSphereMap sphere n n p) = _
  rw [hgen,Functor.map_comp]

private theorem freeMap_comp_actual (n : ℕ) {A B C : BasedSpace}
    (f : A ⟶ B) (g : B ⟶ C) : freeMap n (f ≫ g) = freeMap n f ≫ freeMap n g := by
  apply (freeEvaluation n A (free n C)).injective
  rw [freeEvaluation_freeMap_comp]
  simp only [freeMap,Equiv.apply_symm_apply,Category.assoc]

private theorem freeMap_id_actual (n : ℕ) (A : BasedSpace) : freeMap n (𝟙 A) = 𝟙 _ := by
  apply (freeEvaluation n A (free n A)).injective
  simp only [freeMap,Equiv.apply_symm_apply,Category.id_comp]

private theorem freeEvaluation_constant (n : ℕ) (A : BasedSpace) (X : Prespectrum) :
    freeEvaluation n A X (0 : free n A ⟶ X) =
      ⟨ContinuousMap.const _ (X.level n).point,rfl⟩ := by
  apply BasedSpace.Hom.ext
  have h := (freeEvaluation_exists n A X).choose_spec (0 : free n A ⟶ X)
  have hc (B : BasedSpace) (hB : B = A) :
      HEq (ContinuousMap.const B (X.level n).point) (ContinuousMap.const A (X.level n).point) := by
    subst B
    rfl
  exact eq_of_heq (h.trans (hc _ (free_level n A)))

private theorem freeMap_constant (n : ℕ) (A B : BasedSpace) :
    freeMap n (⟨ContinuousMap.const _ B.point,rfl⟩ : A ⟶ B) = 0 := by
  apply (freeEvaluation n A (free n B)).injective
  rw [freeEvaluation_constant]
  simp only [freeMap,Equiv.apply_symm_apply]
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro x
  exact (freeEvaluation n B (free n B) (𝟙 _)).point

/-- The actual finite quotient wedge, after applying the specified free
prespectrum and the original localization, is an actual source coproduct
with the original branch inclusions. -/
noncomputable def sphereWedgeSourceCofan_isColimit {J : Type} [Finite J]
    (n : ℕ) (Y : J → BasedSpace) : IsColimit (sphereWedgeSourceCofan n Y) :=
  isColimitCofanMkObjOfIsColimit sourceLocalization (fun j => free n (Y j))
    (fun j => freeMap n (BasedSpace.wedgeι Y j)) (sphereWedgeFreeCofan_isColimit n Y)

/-- The original localized map induced by a finite wedge fold is the sum
of the original localized branch projection maps followed by their given
branch maps. -/
theorem source_freeWedgeDesc_eq_sum {J : Type} [Fintype J]
    (n : ℕ) (Y : J → BasedSpace) {Z : BasedSpace} (r : ∀ j, Y j ⟶ Z) :
    sourceLocalization.map (freeMap n (BasedSpace.wedgeDesc r)) =
      ∑ j, sourceLocalization.map (freeMap n (sphereWedgeProjection Y j)) ≫
        sourceLocalization.map (freeMap n (r j)) := by
  classical
  apply (sphereWedgeSourceCofan_isColimit n Y).hom_ext
  rintro ⟨k⟩
  change sourceLocalization.map (freeMap n (BasedSpace.wedgeι Y k)) ≫
    sourceLocalization.map (freeMap n (BasedSpace.wedgeDesc r)) =
      sourceLocalization.map (freeMap n (BasedSpace.wedgeι Y k)) ≫ _
  rw [Preadditive.comp_sum,← sourceLocalization.map_comp,← freeMap_comp_actual,
    BasedSpace.wedgeι_desc]
  symm
  calc
    (∑ j, sourceLocalization.map (freeMap n (BasedSpace.wedgeι Y k)) ≫
        (sourceLocalization.map (freeMap n (sphereWedgeProjection Y j)) ≫
          sourceLocalization.map (freeMap n (r j)))) =
        sourceLocalization.map (freeMap n (BasedSpace.wedgeι Y k)) ≫
          (sourceLocalization.map (freeMap n (sphereWedgeProjection Y k)) ≫
            sourceLocalization.map (freeMap n (r k))) := by
      apply Finset.sum_eq_single k
      · intro j _ hj
        rw [← Category.assoc,← sourceLocalization.map_comp,← freeMap_comp_actual,
          sphereWedgeι_projection_ne Y k j (Ne.symm hj),freeMap_constant,
          sourceLocalization.map_zero,zero_comp]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    _ = sourceLocalization.map (freeMap n (r k)) := by
      rw [← Category.assoc,← sourceLocalization.map_comp,← freeMap_comp_actual,
        sphereWedgeι_projection_self,freeMap_id_actual,
        CategoryTheory.Functor.map_id,Category.id_comp]

/-- A map through the actual finite quotient wedge has original stable
sphere class equal to the sum of its actual branch classes. Both the
original incoming map and every original branch map are retained. -/
theorem sphereSelfMapClass_wedgeDesc_eq_sum {J : Type} [Fintype J]
    (n : ℕ) (Y : J → BasedSpace) (p : sphereLevel n ⟶ BasedSpace.wedge Y)
    (r : ∀ j, Y j ⟶ sphereLevel n) :
    sphereSelfMapClass n (p ≫ BasedSpace.wedgeDesc r) =
      ∑ j, sphereSelfMapClass n (p ≫ sphereWedgeProjection Y j ≫ r j) := by
  apply (sourceStableHomotopyAddEquiv sphere 0).injective
  rw [map_sum]
  simp only [sphereSelfMapClass_sourceMap,freeMap_comp_actual,Functor.map_comp]
  rw [source_freeWedgeDesc_eq_sum]
  simp only [Preadditive.sum_comp,Preadditive.comp_sum,Category.assoc]

end KIP126.StableHomotopy.Implementation.Prespectrum
