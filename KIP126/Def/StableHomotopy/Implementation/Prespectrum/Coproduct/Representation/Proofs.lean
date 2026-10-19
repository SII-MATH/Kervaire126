module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Replacement.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Representation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual strict representatives also exist from the strict coproduct of
the constructed replacements, using the proved strict section of its own
replacement comparison. -/
theorem source_map_surjective_from_coproduct_cubicalReplacement_to_loopSpectrification
    {J : Type u} (X : J → Prespectrum.{u}) (Z : Prespectrum.{u})
    [∀ n, T1Space (Z.level n)] :
    Function.Surjective (fun f : (∐ fun j => cubicalReplacementFunctor.obj (X j)) ⟶
      loopSpectrificationFunctor.obj Z => sourceLocalization.map f) := by
  intro a
  let V := ∐ fun j => cubicalReplacementFunctor.obj (X j)
  obtain ⟨s, hs⟩ := coproduct_cubicalReplacement_comparison_hasSection X
  obtain ⟨g, hg⟩ :=
    source_map_surjective_from_cubicalReplacement_to_loopSpectrification V Z
      (sourceLocalization.map (cubicalReplacementComparison.app V) ≫ a)
  change sourceLocalization.map g = sourceLocalization.map (cubicalReplacementComparison.app V) ≫ a at hg
  change s ≫ cubicalReplacementComparison.app V = 𝟙 V at hs
  refine ⟨s ≫ g, ?_⟩
  change sourceLocalization.map (s ≫ g) = a
  rw [sourceLocalization.map_comp, hg, ← Category.assoc, ← sourceLocalization.map_comp,
    hs, sourceLocalization.map_id, Category.id_comp]

/-- Equality of localized strict representatives from this actual
coproduct is exactly an actual strict homotopy. -/
theorem source_map_eq_iff_pathHomotopic_from_coproduct_cubicalReplacement_to_loopSpectrification
    {J : Type u} (X : J → Prespectrum.{u}) (Z : Prespectrum.{u})
    [∀ n, T1Space (Z.level n)]
    (a b : (∐ fun j => cubicalReplacementFunctor.obj (X j)) ⟶
      loopSpectrificationFunctor.obj Z) :
    sourceLocalization.map a = sourceLocalization.map b ↔ pathHomotopic a b := by
  constructor
  · intro h
    let V := ∐ fun j => cubicalReplacementFunctor.obj (X j)
    obtain ⟨s, hs⟩ := coproduct_cubicalReplacement_comparison_hasSection X
    change s ≫ cubicalReplacementComparison.app V = 𝟙 V at hs
    have H :=
      (source_map_eq_iff_pathHomotopic_from_cubicalReplacement_to_loopSpectrification V Z
        (cubicalReplacementComparison.app V ≫ a)
        (cubicalReplacementComparison.app V ≫ b)).mp (by
          rw [sourceLocalization.map_comp, sourceLocalization.map_comp, h])
    have H' := pathHomotopic_precomp s H
    rw [← Category.assoc, ← Category.assoc, hs] at H'
    change pathHomotopic (𝟙 _ ≫ a) (𝟙 _ ≫ b) at H'
    simpa only [Category.id_comp] using H'
  · exact source_map_eq_of_pathHomotopic

end KIP126.StableHomotopy.Implementation.Prespectrum
