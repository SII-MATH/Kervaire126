module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Stability.General.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- An arbitrary strict map is a stable equivalence exactly when its original
literal cone is a zero object after stable localization. -/
theorem stableEquivalence_iff_source_cone_isZero_general
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences f ↔ IsZero (sourceLocalization.obj (cone f)) := by
  let h : f ≫ 𝟙 Y = f ≫ 𝟙 Y := rfl
  let c := coneMap (f := f) (g := 𝟙 Y) f (𝟙 Y) h
  have hi : stableEquivalences (𝟙 Y) := by
    apply (stableEquivalence_iff_source_isIso _).mpr
    rw [sourceLocalization.map_id]
    infer_instance
  constructor
  · intro hf
    letI := stableEquivalences.Q_inverts c (coneMap_stableEquivalence f (𝟙 Y) h hf hi)
    exact (source_cone_identity_isZero Y).of_iso (asIso (sourceLocalization.map c))
  · intro hc
    have hci : stableEquivalences c := by
      apply (stableEquivalence_iff_source_isIso _).mpr
      rw [hc.eq_zero_of_src (sourceLocalization.map c)]
      exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hc, source_cone_identity_isZero Y⟩
    exact stableEquivalence_source_of_coneMap_general f (𝟙 Y) h hi hci

/-- The original cone's stable homotopy groups detect stable equivalences,
with no extra condition on the original point-set objects. -/
theorem stableEquivalence_iff_cone_stableHomotopy_subsingleton_general
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences f ↔ ∀ d : ℤ, Subsingleton (StableHomotopy (cone f) d) := by
  rw [stableEquivalence_iff_source_cone_isZero_general f,
    source_isZero_iff_stableHomotopy_subsingleton]

end KIP126.StableHomotopy.Implementation.Prespectrum
