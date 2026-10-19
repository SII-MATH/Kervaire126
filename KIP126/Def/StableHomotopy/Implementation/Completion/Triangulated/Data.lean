module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Triangle.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Integer.Additive.Proofs
public import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory CategoryTheory.Pretriangulated

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The already fixed category of HF₂-local spectra inherits actual source
triangles through its fully faithful, shift-preserving inclusion. -/
noncomputable instance pretriangulated : Pretriangulated CompletedSpectrum where
  distinguishedTriangles := toSource.mapTriangle.obj ⁻¹' (distTriang SourceCategory)
  isomorphic_distinguished T hT U e :=
    isomorphic_distinguished _ hT _ (toSource.mapTriangle.mapIso e)
  contractible_distinguished X :=
    isomorphic_distinguished _ (contractible_distinguished (toSource.obj X)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) toSource.mapZeroObject)
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨Z,hZ,g,h,hT⟩ := SourceIsHF2Local.cocone (toSource.map f) X.isLocal Y.isLocal
    rcases Z with ⟨⟨Z⟩⟩
    let W : CompletedSpectrum := ⟨Z,hZ⟩
    refine ⟨W,toSource.preimage g,
      toSource.preimage (h ≫ (toSource.commShiftIso (1 : ℤ)).inv.app X),?_⟩
    exact isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (toSource.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso (toSource.mapTriangleRotateIso.app T))
  complete_distinguished_triangle_morphism T U hT hU a b h := by
    obtain ⟨c,hc₁,hc₂⟩ := complete_distinguished_triangle_morphism
      (toSource.mapTriangle.obj T) (toSource.mapTriangle.obj U) hT hU
      (toSource.map a) (toSource.map b) (by simpa using toSource.congr_map h)
    refine ⟨toSource.preimage c, ?_, ?_⟩
    · apply toSource.map_injective
      simpa using hc₁
    · apply toSource.map_injective
      have := toSource.commShiftIso_hom_naturality a (1 : ℤ)
      rw [← cancel_mono ((toSource.commShiftIso (1 : ℤ)).hom.app U.obj₁)]
      cat_disch

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
