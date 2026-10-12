module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Retained.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Lifting.Equivalence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Endpoint.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Quotient.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual maps out of the cubical replacement lift up to strict
homotopy through every actual level weak equivalence. -/
theorem cubicalReplacement_exists_pathHomotopic_lift (X : Prespectrum.{u})
    {E B : Prespectrum.{u}} (f : E ⟶ B)
    (hf : ∀ n (x : E.level n) r, Function.Bijective
      (KIP126.Topology.continuousHomotopyMap (f.level n) x (f.level n x) rfl r))
    (b : cubicalReplacementFunctor.obj X ⟶ B) :
    ∃ a : cubicalReplacementFunctor.obj X ⟶ E, pathHomotopic (a ≫ f) b := by
  obtain ⟨l,hl⟩ := cubicalReplacement_lift_of_level_cubeBoundary X (mappingPathProjection f)
    (mappingPathProjection_level_hasCubeBoundaryLifting f hf) b
  refine ⟨l ≫ mappingPathRetraction f,?_⟩
  have H := pathHomotopic_precomp l (show pathHomotopic (mappingPathRetraction f ≫ f)
    (mappingPathProjection f) from ⟨mappingPathRetainedHomotopy f⟩)
  simpa only [← Category.assoc,hl] using H

/-- Actual level weak equivalences reflect strict homotopy classes of
maps out of the genuine free-cubical replacement. -/
theorem cubicalReplacement_pathHomotopic_of_level_homotopy_bijective
    (X : Prespectrum.{u}) {E B : Prespectrum.{u}} (f : E ⟶ B)
    (hf : ∀ n (x : E.level n) r, Function.Bijective
      (KIP126.Topology.continuousHomotopyMap (f.level n) x (f.level n x) rfl r))
    {a b : cubicalReplacementFunctor.obj X ⟶ E}
    (H : pathHomotopic (a ≫ f) (b ≫ f)) : pathHomotopic a b := by
  have h' : pathHomotopic ((a ≫ mappingPathInclusion f) ≫ mappingPathProjection f)
      ((b ≫ mappingPathInclusion f) ≫ mappingPathProjection f) := by
    simpa only [Category.assoc,mappingPathInclusion_projection] using H
  have h'' := cubicalReplacement_pathHomotopic_of_postcomp X (mappingPathProjection f)
    (mappingPathProjection_level_hasCubeBoundaryLifting f hf) h'
  have h''' := pathHomotopic_postcomp h'' (mappingPathRetraction f)
  simpa only [Category.assoc,mappingPathInclusion_retraction,Category.comp_id] using h'''

/-- The actual homotopy-category Hom out of the constructed cubical
replacement sends level weak equivalences to bijections. -/
theorem cubicalReplacement_homotopyClass_postcomp_bijective
    (X : Prespectrum.{u}) {E B : Prespectrum.{u}} (f : E ⟶ B)
    (hf : ∀ n (x : E.level n) r, Function.Bijective
      (KIP126.Topology.continuousHomotopyMap (f.level n) x (f.level n x) rfl r)) :
    Function.Bijective (fun a : homotopyQuotient.obj (cubicalReplacementFunctor.obj X) ⟶
      homotopyQuotient.obj E => a ≫ homotopyQuotient.map f) := by
  constructor
  · intro a b h
    obtain ⟨a,rfl⟩ := homotopyQuotient_map_surjective a
    obtain ⟨b,rfl⟩ := homotopyQuotient_map_surjective b
    change homotopyQuotient.map a ≫ homotopyQuotient.map f =
      homotopyQuotient.map b ≫ homotopyQuotient.map f at h
    rw [← Functor.map_comp,← Functor.map_comp] at h
    exact (homotopyQuotient_map_eq_iff _ _).mpr
      (cubicalReplacement_pathHomotopic_of_level_homotopy_bijective X f hf
        ((homotopyQuotient_map_eq_iff _ _).mp h))
  · intro b
    obtain ⟨b,rfl⟩ := homotopyQuotient_map_surjective b
    obtain ⟨a,ha⟩ := cubicalReplacement_exists_pathHomotopic_lift X f hf b
    exact ⟨homotopyQuotient.map a,by
      change homotopyQuotient.map a ≫ homotopyQuotient.map f = homotopyQuotient.map b
      rw [← Functor.map_comp]
      exact (homotopyQuotient_map_eq_iff _ _).mpr ha⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
