module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Derived.Comparison.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Derived.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The comparison retains exactly the actual pointwise projections. -/
theorem sourceStabilizedPiIso_hom_projection {J : Type}
    (X : J → StabilizedPrespectrum.{u}) (j : J) :
    (sourceStabilizedPiIso X).hom ≫
        (sourceDerivedPiAdjunction J).counit.app
          (fun j => sourceLocalization.obj (X j).obj.obj) j =
      sourceLocalization.map (piProjection (fun j => (X j).obj.obj) j) := by
  let L := stabilizedInclusion.{u} ⋙ t1Inclusion ⋙ sourceLocalization
  let Lp := Functor.pi (fun _ : J => L)
  let Δ := Functor.pi' (fun _ : J => 𝟭 StabilizedPrespectrum.{u})
  let Δ' := Functor.pi' (fun _ : J => 𝟭 SourceCategory.{u})
  letI : CatCommSq Δ L Lp Δ' := ⟨Iso.refl _⟩
  letI : CatCommSq (stabilizedPiFunctor J) Lp L (sourceDerivedPiFunctor J) :=
    inferInstanceAs (CatCommSq (stabilizedPiLocalizer J).functor Lp L
      ((stabilizedPiLocalizer J).localizedFunctor Lp L))
  have h := (stabilizedPiAdjunction J).localization_counit_app L stabilizedStableEquivalences
    Lp (MorphismProperty.pi (fun _ : J => stabilizedStableEquivalences)) Δ'
      (sourceDerivedPiFunctor J) X
  have hj := congrFun h j
  change (sourceDerivedPiAdjunction J).counit.app
      (fun j => sourceLocalization.obj (X j).obj.obj) j =
    (sourceStabilizedPiIso X).inv ≫ 𝟙 _ ≫
      sourceLocalization.map (piProjection (fun j => (X j).obj.obj) j) at hj
  rw [hj, Category.id_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The actual pointwise cone of stabilized T₁ objects remains a genuine
limit cone in the ordinary stable localization, for arbitrary small families. -/
noncomputable def sourcePiFan_isLimit_of_stabilization {J : Type}
    (X : J → Prespectrum.{u}) [∀ j n, T1Space ((X j).level n)]
    (hX : ∀ j, HasBijectiveStabilization (X j)) :
    IsLimit (sourceLocalization.mapCone (piFan X)) := by
  let Y : J → StabilizedPrespectrum.{u} := fun j => ⟨⟨X j, fun _ => inferInstance⟩, hX j⟩
  refine (Fan.isLimitMapConeEquiv sourceLocalization X (piFan X)).symm ?_
  let e : Fan.mk (sourceLocalization.obj (piPrespectrum X))
      (fun j => sourceLocalization.map (piProjection X j)) ≅
      sourceDerivedPiFan (fun j => sourceLocalization.obj (X j)) :=
    Cone.ext (sourceStabilizedPiIso Y) (fun j => (sourceStabilizedPiIso_hom_projection Y j.as).symm)
  exact IsLimit.ofIsoLimit (sourceDerivedPiFan_isLimit _) e.symm

end

end KIP126.StableHomotopy.Implementation.Prespectrum
