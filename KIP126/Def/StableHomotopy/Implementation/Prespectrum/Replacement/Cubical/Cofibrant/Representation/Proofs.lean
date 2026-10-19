module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Representation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual source lifting, via the constructed strict replacement retract,
gives strict representatives of stable maps into the actual loop target. -/
theorem source_map_surjective_of_isCubicallyCofibrant
    {X : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    (Z : Prespectrum.{u}) [∀ n,T1Space (Z.level n)] :
    Function.Surjective (fun f : X ⟶ loopSpectrificationFunctor.obj Z => sourceLocalization.map f) := by
  intro a
  obtain ⟨s,hs⟩ := hX.replacement_hasSection
  obtain ⟨b,hb⟩ := source_map_surjective_from_cubicalReplacement_to_loopSpectrification X Z
    (sourceLocalization.map (cubicalReplacementComparison.app X) ≫ a)
  change sourceLocalization.map b = _ at hb
  refine ⟨s ≫ b,?_⟩
  change sourceLocalization.map (s ≫ b) = a
  rw [Functor.map_comp,hb,← Category.assoc,← Functor.map_comp,hs,
    CategoryTheory.Functor.map_id,Category.id_comp]

/-- For a source with the actual lifting property, equality in the
specified stable localization is precisely actual strict homotopy. -/
theorem source_map_eq_iff_pathHomotopic_of_isCubicallyCofibrant
    {X : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    (Z : Prespectrum.{u}) [∀ n,T1Space (Z.level n)]
    (a b : X ⟶ loopSpectrificationFunctor.obj Z) :
    sourceLocalization.map a = sourceLocalization.map b ↔ pathHomotopic a b := by
  constructor
  · intro h
    obtain ⟨s,hs⟩ := hX.replacement_hasSection
    have he : sourceLocalization.map (cubicalReplacementComparison.app X ≫ a) =
        sourceLocalization.map (cubicalReplacementComparison.app X ≫ b) := by
      rw [Functor.map_comp,Functor.map_comp,h]
    have hH := (source_map_eq_iff_pathHomotopic_from_cubicalReplacement_to_loopSpectrification X Z _ _).mp he
    have hS := pathHomotopic_precomp s hH
    simpa only [← Category.assoc,hs,Category.id_comp] using hS
  · exact source_map_eq_of_pathHomotopic

end KIP126.StableHomotopy.Implementation.Prespectrum
