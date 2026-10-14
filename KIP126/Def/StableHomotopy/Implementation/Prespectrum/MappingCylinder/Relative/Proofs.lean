module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Relative.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Adjunction.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual interval-boundary pushout-product of a cubical
cofibration is again a cubical cofibration. The lift comes from the
original endpoint comparison, retaining the full prescribed source
cylinder and both target endpoints. -/
theorem IsCubicalCofibration.cylinderPushoutProduct {X Y : Prespectrum.{u}}
    {i : X ⟶ Y} (hi : IsCubicalCofibration i) :
    IsCubicalCofibration (cylinderPushoutProduct i) := by
  intro E B p hp
  constructor
  intro a b sq
  let e : Y ⨿ Y ⟶ E := pushout.inl (coprod.map i i) (cylinderEndpoints X) ≫ a
  let c : cylinderFunctor.obj X ⟶ E := pushout.inr (coprod.map i i) (cylinderEndpoints X) ≫ a
  let a₀ : Y ⟶ E := coprod.inl ≫ e
  let a₁ : Y ⟶ E := coprod.inr ≫ e
  have he : e ≫ p = cylinderEndpoints Y ≫ b := by
    dsimp only [e]
    rw [Category.assoc,sq.w,← Category.assoc]
    change (pushout.inl _ _ ≫ pushout.desc _ _ _) ≫ b = _
    rw [pushout.inl_desc]
  have hc : c ≫ p = cylinderFunctor.map i ≫ b := by
    dsimp only [c]
    rw [Category.assoc,sq.w,← Category.assoc]
    change (pushout.inr _ _ ≫ pushout.desc _ _ _) ≫ b = _
    rw [pushout.inr_desc]
  have hj : coprod.map i i ≫ e = cylinderEndpoints X ≫ c := by
    dsimp only [e,c]
    rw [← Category.assoc,← Category.assoc,pushout.condition]
  have h₀ : cylinderPathCurry b ≫ pathEvaluation B 0 = a₀ ≫ p := by
    rw [cylinderPathCurry_zero]
    dsimp only [a₀]
    rw [Category.assoc,he,← Category.assoc]
    change _ = (coprod.inl ≫ coprod.desc _ _) ≫ b
    rw [coprod.inl_desc]
  have h₁ : cylinderPathCurry b ≫ pathEvaluation B 1 = a₁ ≫ p := by
    rw [cylinderPathCurry_one]
    dsimp only [a₁]
    rw [Category.assoc,he,← Category.assoc]
    change _ = (coprod.inr ≫ coprod.desc _ _) ≫ b
    rw [coprod.inr_desc]
  have hc₀ : cylinderPathCurry c ≫ pathEvaluation E 0 = i ≫ a₀ := by
    rw [cylinderPathCurry_zero]
    have h := congrArg (fun k => coprod.inl ≫ k) hj
    dsimp only [a₀]
    change (coprod.inl ≫ coprod.map i i ≫ e) =
      coprod.inl ≫ coprod.desc _ _ ≫ c at h
    simpa only [coprod.inl_map_assoc,coprod.inl_desc_assoc] using h.symm
  have hc₁ : cylinderPathCurry c ≫ pathEvaluation E 1 = i ≫ a₁ := by
    rw [cylinderPathCurry_one]
    have h := congrArg (fun k => coprod.inr ≫ k) hj
    dsimp only [a₁]
    change (coprod.inr ≫ coprod.map i i ≫ e) =
      coprod.inr ≫ coprod.desc _ _ ≫ c at h
    simpa only [coprod.inr_map_assoc,coprod.inr_desc_assoc] using h.symm
  have hcp : cylinderPathCurry c ≫ pathMap p = i ≫ cylinderPathCurry b := by
    change cylinderPathCurry c ≫ pathFunctor.map p = _
    rw [← cylinderPathCurry_natural_right,hc,cylinderPathCurry_natural_left]
  let s : CommSq (cylinderPathCurry c) i (pathEndpointMap p)
      (pathEndpointLift p a₀ a₁ (cylinderPathCurry b) h₀ h₁) := ⟨by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (congrArg (fun k : X ⟶ E => k.level n x) hc₀)
        (congrArg (fun k : X ⟶ E => k.level n x) hc₁)
    · exact congrArg (fun k : X ⟶ pathPrespectrum B => k.level n x) hcp⟩
  letI := hi (pathEndpointMap p) (pathEndpointMap_level_hasCubeBoundaryLifting p hp)
  let G : Y ⟶ pathPrespectrum E := s.lift
  have G₀ : G ≫ pathEvaluation E 0 = a₀ := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro y
    exact congrArg (fun k : Y ⟶ pathEndpointPrespectrum p => (k.level n y).val.1.1) s.fac_right
  have G₁ : G ≫ pathEvaluation E 1 = a₁ := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro y
    exact congrArg (fun k : Y ⟶ pathEndpointPrespectrum p => (k.level n y).val.1.2) s.fac_right
  have Gp : G ≫ pathMap p = cylinderPathCurry b := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro y
    exact congrArg (fun k : Y ⟶ pathEndpointPrespectrum p => (k.level n y).val.2) s.fac_right
  let l := cylinderPathUncurry G
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
  · apply pushout.hom_ext
    · change pushout.inl _ _ ≫ pushout.desc _ _ _ ≫ l = e
      rw [pushout.inl_desc_assoc]
      apply coprod.hom_ext
      · change coprod.inl ≫ coprod.desc _ _ ≫ l = a₀
        rw [coprod.inl_desc_assoc]
        exact (cylinderPathCurry_zero l).symm.trans G₀
      · change coprod.inr ≫ coprod.desc _ _ ≫ l = a₁
        rw [coprod.inr_desc_assoc]
        exact (cylinderPathCurry_one l).symm.trans G₁
    · change pushout.inr _ _ ≫ pushout.desc _ _ _ ≫ l = c
      rw [pushout.inr_desc_assoc]
      apply (cylinderPathAdjunction.homEquiv X E).injective
      change cylinderPathCurry (cylinderFunctor.map i ≫ cylinderPathUncurry G) = cylinderPathCurry c
      rw [cylinderPathCurry_natural_left,cylinderPathCurry_uncurry]
      exact s.fac_left
  · apply (cylinderPathAdjunction.homEquiv Y B).injective
    change cylinderPathCurry (cylinderPathUncurry G ≫ p) = cylinderPathCurry b
    rw [cylinderPathCurry_natural_right,cylinderPathCurry_uncurry]
    exact Gp

end KIP126.StableHomotopy.Implementation.Prespectrum
