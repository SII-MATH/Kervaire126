module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.ScalarLocalization.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Detection.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Source.Shift.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

private theorem shifted_target_hom_subsingleton (E X : SourceCategory.{0})
    (hX : ∀ d : ℤ, Subsingleton (E⟦d⟧ ⟶ X)) (d : ℤ) :
    Subsingleton (E⟦d⟧ ⟶ X⟦(1 : ℤ)⟧) := by
  letI := hX (d + (-1))
  let e : (E⟦d⟧)⟦(-1 : ℤ)⟧ ≅ E⟦d + (-1)⟧ :=
    by simpa only [Functor.comp_obj] using (shiftFunctorAdd SourceCategory d (-1)).symm.app E
  letI : Subsingleton ((E⟦d⟧)⟦(-1 : ℤ)⟧ ⟶ X) :=
    (Iso.homCongr e (Iso.refl X)).injective.subsingleton
  let h : ((E⟦d⟧)⟦(-1 : ℤ)⟧ ⟶ X) ≃ (E⟦d⟧ ⟶ X⟦(1 : ℤ)⟧) :=
    by simpa only [shiftEquiv'] using
      (shiftEquiv' SourceCategory (-1 : ℤ) 1 (neg_add_cancel (1 : ℤ))).toAdjunction.homEquiv (E⟦d⟧) X
  exact h.symm.injective.subsingleton

/-- Testing against all integer shifts of the actual scalar telescope of
S⁰ already makes the original Moore unit an isomorphism. The proof uses
the actual unit cofiber, its proved scalar invertibility, and the original
stable groups detecting zero. No identification with the doubled-bond
sphere is assumed or asserted here. -/
theorem sourceMooreCompletionUnit_isIso_of_scalarSphereTelescope_orthogonal
    (p : ℕ) (X : SourceCategory.{0})
    (hX : ∀ d : ℤ,
      Subsingleton ((sourceScalarTelescope p (Prespectrum.sourceSphere 0))⟦d⟧ ⟶ X)) :
    IsIso (sourceMooreCompletionUnit p X) := by
  let E := sourceScalarTelescope p (Prespectrum.sourceSphere 0)
  let T := Triangle.mk (sourceMooreCompletionUnit p X)
    (HasFunctorialCofiber.cofibι (sourceMooreCompletionUnit p X))
    (HasFunctorialCofiber.cofibδ (sourceMooreCompletionUnit p X))
  have hT : T ∈ distTriang SourceCategory :=
    HasFunctorialCofiber.cofib_distinguished (sourceMooreCompletionUnit p X)
  letI : IsIso (p • 𝟙 E) := sourceScalarTelescope_scalar_isIso p _
  letI : IsIso (p • 𝟙 T.obj₃) := sourceMooreCompletionUnit_cofiber_scalar_isIso p X
  have hC (d : ℤ) : Subsingleton (E⟦d⟧ ⟶ T.obj₃) := by
    letI : Subsingleton (E⟦d⟧ ⟶ T.obj₂) := sourceMooreCompletion_shifted_hom_subsingleton p X E d
    letI : Subsingleton (E⟦d⟧ ⟶ T.obj₁⟦(1 : ℤ)⟧) := shifted_target_hom_subsingleton E X hX d
    have hz (a : E⟦d⟧ ⟶ T.obj₃) : a = 0 := by
      obtain ⟨b, hb⟩ := T.coyoneda_exact₃ hT a
        (show a ≫ T.mor₃ = 0 from Subsingleton.elim _ _)
      rw [show b = 0 from Subsingleton.elim _ _] at hb
      exact hb.trans zero_comp
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩
  have hz : IsZero T.obj₃ := by
    apply Prespectrum.source_isZero_of_stableHomotopy_subsingleton T.obj₃.as.obj
    intro d
    letI := hC d
    letI : Subsingleton ((Prespectrum.sourceSphere 0)⟦d⟧ ⟶ T.obj₃) :=
      (sourceScalarTelescopeUnit_shift_precomp_bijective p (Prespectrum.sourceSphere 0)
        T.obj₃ d).surjective.subsingleton
    let e : (Prespectrum.sourceSphere 0)⟦d⟧ ≅ Prespectrum.sourceSphere d :=
      Prespectrum.sourceSphere_addShiftIso 0 d ≪≫ eqToIso (by rw [zero_add])
    letI : Subsingleton (Prespectrum.sourceSphere d ⟶ T.obj₃) :=
      (Iso.homCongr e.symm (Iso.refl T.obj₃)).injective.subsingleton
    letI : Subsingleton (Prespectrum.sourceSphere d ⟶ sourceLocalization.obj T.obj₃.as.obj) := by
      change Subsingleton (Prespectrum.sourceSphere d ⟶ T.obj₃)
      infer_instance
    exact (Prespectrum.sourceStableHomotopyEquiv T.obj₃.as.obj d).injective.subsingleton
  exact (T.isZero₃_iff_isIso₁ hT).mp hz

/-- Scalar completeness is detected by one concrete scalar telescope and
all its integer shifts. This genuinely upgrades orthogonality to these
specific generators to orthogonality to every scalar-invertible source. -/
theorem sourceIsScalarComplete_iff_scalarSphereTelescope_orthogonal
    (p : ℕ) (X : SourceCategory.{0}) :
    SourceIsScalarComplete p X ↔ ∀ d : ℤ,
      Subsingleton ((sourceScalarTelescope p (Prespectrum.sourceSphere 0))⟦d⟧ ⟶ X) := by
  constructor
  · intro hX d
    letI := sourceScalarTelescope_scalar_isIso p (Prespectrum.sourceSphere 0)
    exact hX _ (isIso_nsmul_id_shift p _ d)
  · intro hX
    letI := sourceMooreCompletionUnit_isIso_of_scalarSphereTelescope_orthogonal p X hX
    exact (sourceMooreCompletion_scalarComplete p X).of_iso
      (asIso (sourceMooreCompletionUnit p X))

end KIP126.StableHomotopy.Implementation
