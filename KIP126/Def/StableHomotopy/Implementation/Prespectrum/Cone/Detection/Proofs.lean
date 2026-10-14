module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Detection.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Identity.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual strict contraction makes the identity cone a zero object
in the original source category. -/
theorem source_cone_identity_isZero (X : Prespectrum.{u}) :
    IsZero (sourceLocalization.obj (cone (𝟙 X))) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have h := source_map_eq_of_pathHomotopic ⟨coneIdentityContraction X⟩
  rw [sourceLocalization.map_id] at h
  exact h.trans (sourceLocalization.map_zero _ _)

/-- For actual cubically cofibrant spectra, the literal mapping cone
is stably zero precisely when the original strict map is a stable equivalence. -/
theorem stableEquivalence_iff_source_cone_isZero
    {X Y : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y) :
    stableEquivalences f ↔ IsZero (sourceLocalization.obj (cone f)) := by
  let h : f ≫ 𝟙 Y = f ≫ 𝟙 Y := rfl
  let c := coneMap (f := f) (g := 𝟙 Y) f (𝟙 Y) h
  have hi : stableEquivalences (𝟙 Y) := by
    apply (stableEquivalence_iff_source_isIso _).mpr
    rw [sourceLocalization.map_id]
    infer_instance
  constructor
  · intro hf
    have hc := coneMap_stableEquivalence_of_isCubicallyCofibrant hX hY hY hY f (𝟙 Y) h hf hi
    letI := stableEquivalences.Q_inverts c hc
    exact (source_cone_identity_isZero Y).of_iso (asIso (sourceLocalization.map c))
  · intro hc
    have hci : stableEquivalences c := by
      apply (stableEquivalence_iff_source_isIso _).mpr
      rw [hc.eq_zero_of_src (sourceLocalization.map c)]
      exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hc, source_cone_identity_isZero Y⟩
    exact stableEquivalence_source_of_coneMap hX hY hY hY f (𝟙 Y) h hi hci

/-- This detection uses the original stable homotopy groups of the literal
cone, not a newly postulated homology theory. -/
theorem stableEquivalence_iff_cone_stableHomotopy_subsingleton
    {X Y : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y) :
    stableEquivalences f ↔ ∀ d : ℤ, Subsingleton (StableHomotopy (cone f) d) := by
  rw [stableEquivalence_iff_source_cone_isZero hX hY f,
    source_isZero_iff_stableHomotopy_subsingleton]

end KIP126.StableHomotopy.Implementation.Prespectrum
