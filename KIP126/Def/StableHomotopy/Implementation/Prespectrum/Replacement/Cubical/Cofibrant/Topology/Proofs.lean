module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.CompactlyGenerated.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual cofibrant spectra are T1 in each original level, through
the proved strict retract of the actual free-cell replacement. -/
theorem IsCubicallyCofibrant.level_t1Space {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (n : ℕ) : T1Space (X.level n) := by
  obtain ⟨s,hs⟩ := hX.replacement_hasSection
  apply t1Space_of_injective_of_continuous (f := s.level n) _ (s.level n).continuous
  have he (x : X.level n) : (cubicalReplacementComparison.app X).level n (s.level n x) = x :=
    congrArg (fun k : X ⟶ X => k.level n x) hs
  exact Function.LeftInverse.injective he

/-- Actual cofibrant spectra have compactly generated original levels;
this is proved by the actual strict replacement section. -/
theorem IsCubicallyCofibrant.level_uCompactlyGeneratedSpace {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (n : ℕ) : UCompactlyGeneratedSpace.{u} (X.level n) := by
  obtain ⟨s,hs⟩ := hX.replacement_hasSection
  have he (x : X.level n) : (cubicalReplacementComparison.app X).level n (s.level n x) = x :=
    congrArg (fun k : X ⟶ X => k.level n x) hs
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f hf
  have hc : Continuous (f ∘ (cubicalReplacementComparison.app X).level n) := by
    apply continuous_from_uCompactlyGeneratedSpace
    intro S g
    exact hf S (((cubicalReplacementComparison.app X).level n).comp g)
  have ht := hc.comp (s.level n).continuous
  simpa only [Function.comp_def, he] using ht

end KIP126.StableHomotopy.Implementation.Prespectrum
