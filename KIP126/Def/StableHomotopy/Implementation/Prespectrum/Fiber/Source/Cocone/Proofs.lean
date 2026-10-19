module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Suspension.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Rotation.Equivalence
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Localization.Roofs.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Pretriangulated
universe u
set_option backward.isDefEq.respectTransparency false

/-- A strict source map is isomorphic to an actual fiber projection:
suspend the actual fiber of its connecting map and use the actual
suspension-loop counit and signed fiber-rotation comparison. -/
theorem source_map_is_fiberProjection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    ∃ (U V : Prespectrum.{u}) (k : U ⟶ V)
      (e₁ : sourceLocalization.obj X ≅ sourceLocalization.obj (fiber k))
      (e₂ : sourceLocalization.obj Y ≅ sourceLocalization.obj U),
      sourceLocalization.map f ≫ e₂.hom = e₁.hom ≫ sourceLocalization.map (fiberProjection k) := by
  obtain ⟨e,he⟩ := source_suspension_fiber_iso_exists (fiberConnecting f)
  let r := sourceFiberRotationIso f
  let ε := sourceSuspensionLoopCounitIso
  let e₁ := (ε.app (sourceLocalization.obj X)).symm ≪≫
    sourceSuspensionFunctor.mapIso r ≪≫ e
  refine ⟨(Prespectrum.loop Y).suspension,(fiber f).suspension,
    suspensionMap (fiberConnecting f),e₁,(ε.app (sourceLocalization.obj Y)).symm,?_⟩
  change sourceLocalization.map f ≫ (ε.app (sourceLocalization.obj Y)).inv =
    ((ε.app (sourceLocalization.obj X)).inv ≫ sourceSuspensionFunctor.map r.hom ≫ e.hom) ≫ _
  rw [Category.assoc,Category.assoc,he,← Functor.map_comp]
  rw [show r.hom ≫ sourceLocalization.map (fiberProjection (fiberConnecting f)) =
    sourceLocalization.map (loopMap f) from sourceFiberRotationIso_projection f]
  rw [← sourceLoopFunctor_map]
  exact ε.inv.naturality (sourceLocalization.map f)

/-- Every map in the original localization, including formal-inverse
composites, is isomorphic on its two objects to an actual fiber projection. -/
theorem source_morphism_is_fiberProjection {A B : SourceCategory.{u}} (a : A ⟶ B) :
    ∃ (U V : Prespectrum.{u}) (k : U ⟶ V)
      (e₁ : A ≅ sourceLocalization.obj (fiber k)) (e₂ : B ≅ sourceLocalization.obj U),
      a ≫ e₂.hom = e₁.hom ≫ sourceLocalization.map (fiberProjection k) := by
  rcases A with ⟨⟨A⟩⟩
  rcases B with ⟨⟨B⟩⟩
  obtain ⟨X,s,t,hs,ht⟩ := source_morphism_exists_roof a
  letI := stableEquivalences.Q_inverts s hs
  obtain ⟨U,V,k,e₁,e₂,hk⟩ := source_map_is_fiberProjection t
  refine ⟨U,V,k,(asIso (sourceLocalization.map s)).symm ≪≫ e₁,e₂,?_⟩
  change a ≫ e₂.hom = (inv (sourceLocalization.map s) ≫ e₁.hom) ≫ _
  apply (cancel_epi (sourceLocalization.map s)).mp
  rw [← Category.assoc,ht,hk,Category.assoc,IsIso.hom_inv_id_assoc]

/-- Every source morphism is the first map of a triangle isomorphic to
an actual standard fiber triangle; no triangulated structure is assumed. -/
theorem source_morphism_exists_fiber_triangle {A B : SourceCategory.{u}} (a : A ⟶ B) :
    ∃ (C : SourceCategory.{u}) (b : B ⟶ C) (c : C ⟶ A⟦(1 : ℤ)⟧)
      (U V : Prespectrum.{u}) (k : U ⟶ V),
      Nonempty (Triangle.mk a b c ≅ sourceFiberTriangle k) := by
  obtain ⟨U,V,k,e₁,e₂,hk⟩ := source_morphism_is_fiberProjection a
  let b := e₂.hom ≫ sourceLocalization.map k
  let c := sourceFiberBoundary k ≫ e₁.inv⟦(1 : ℤ)⟧'
  refine ⟨sourceLocalization.obj V,b,c,U,V,k,⟨Triangle.isoMk _ _ e₁ e₂ (Iso.refl _)
    hk ?_ ?_⟩⟩
  · change (e₂.hom ≫ sourceLocalization.map k) ≫ 𝟙 _ = e₂.hom ≫ sourceLocalization.map k
    rw [Category.comp_id]
  · change (sourceFiberBoundary k ≫ e₁.inv⟦(1 : ℤ)⟧') ≫ e₁.hom⟦(1 : ℤ)⟧' =
      𝟙 _ ≫ sourceFiberBoundary k
    rw [Category.assoc,← Functor.map_comp,Iso.inv_hom_id,CategoryTheory.Functor.map_id,
      Category.comp_id,Category.id_comp]

end KIP126.StableHomotopy.Implementation.Prespectrum
