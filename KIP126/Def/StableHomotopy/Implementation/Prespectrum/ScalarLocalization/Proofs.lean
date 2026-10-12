module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.ScalarLocalization.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Represented.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.Orthogonality.Proofs
public import KIP126.Def.StableHomotopy.Completion.Moore.ScalarInverse.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem sourceScalarSequence_step (p : ℕ) (X : SourceCategory.{u}) (k : ℕ) :
    (sourceScalarSequence p X).map (homOfLE (Nat.le_succ k)) = p • 𝟙 X :=
  Functor.ofSequence_map_homOfLE_succ _ k

/-- The actual scalar Milnor map is one minus the scalar multiple of the
unweighted forward shift on the same original coproduct. -/
theorem sourceScalarSequence_oneSubShift (p : ℕ) (X : SourceCategory.{u}) :
    sourceSequentialOneSubShift (sourceScalarSequence p X) =
      𝟙 _ - p • sourceSequentialShiftMap (sourceScalarSequence 1 X) := by
  apply congrArg (fun a => 𝟙 _ - a)
  apply Sigma.hom_ext
  intro k
  simp only [sourceSequentialShiftMap, Sigma.ι_desc, sourceScalarSequence_step,
    Preadditive.comp_nsmul, Preadditive.nsmul_comp, one_smul]
  rfl

/-- Multiplication by the scalar is invertible on this actual telescope,
by the actual cofiber division argument for one minus a scalar multiple. -/
theorem sourceScalarTelescope_scalar_isIso (p : ℕ) (X : SourceCategory.{u}) :
    IsIso (p • 𝟙 (sourceScalarTelescope p X)) := by
  change IsIso (p • 𝟙 (HasFunctorialCofiber.cofib
    (sourceSequentialOneSubShift (sourceScalarSequence p X))))
  rw [sourceScalarSequence_oneSubShift]
  exact isIso_nsmul_id_cofiber_one_sub_nsmul p
    (sourceSequentialShiftMap (sourceScalarSequence 1 X))

private theorem scalar_precomp_bijective (p : ℕ) (X Y : SourceCategory.{u})
    [IsIso (p • 𝟙 Y)] :
    Function.Bijective (fun a : X ⟶ Y => (p • 𝟙 X) ≫ a) := by
  have he (a : X ⟶ Y) : (p • 𝟙 X) ≫ a = a ≫ (p • 𝟙 Y) := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.id_comp, Category.comp_id]
  constructor
  · intro a b hab
    change (p • 𝟙 X) ≫ a = (p • 𝟙 X) ≫ b at hab
    rw [he, he] at hab
    exact (cancel_mono (p • 𝟙 Y)).mp hab
  · intro a
    refine ⟨a ≫ inv (p • 𝟙 Y), ?_⟩
    change (p • 𝟙 X) ≫ (a ≫ inv (p • 𝟙 Y)) = a
    rw [he, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The specified zeroth-stage map is universal into every source object
on which the scalar is invertible. The shifted Milnor ambiguity is removed
using the same scalar invertibility, rather than assuming a colimit property. -/
theorem sourceScalarTelescopeUnit_precomp_bijective (p : ℕ) (X Y : SourceCategory.{u})
    [IsIso (p • 𝟙 Y)] :
    Function.Bijective (fun a : sourceScalarTelescope p X ⟶ Y =>
      sourceScalarTelescopeUnit p X ≫ a) := by
  apply sourceHomotopyColimitInclusion_zero_precomp_bijective
  · intro k
    rw [sourceScalarSequence_step]
    change Function.Bijective (fun a : X ⟶ Y => (p • 𝟙 X) ≫ a)
    exact scalar_precomp_bijective p X Y
  · intro k
    rw [sourceScalarSequence_step]
    change Function.Surjective (fun a : X⟦(1 : ℤ)⟧ ⟶ Y =>
      (shiftFunctor SourceCategory (1 : ℤ)).map (p • 𝟙 X) ≫ a)
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    exact (scalar_precomp_bijective p (X⟦(1 : ℤ)⟧) Y).surjective

/-- Shifting the original scalar telescope unit retains the universal
property into each scalar-invertible target. -/
theorem sourceScalarTelescopeUnit_shift_precomp_bijective
    (p : ℕ) (X Y : SourceCategory.{u}) (d : ℤ) [IsIso (p • 𝟙 Y)] :
    Function.Bijective (fun a : (sourceScalarTelescope p X)⟦d⟧ ⟶ Y =>
      (sourceScalarTelescopeUnit p X)⟦d⟧' ≫ a) := by
  letI := isIso_nsmul_id_shift p Y (-d)
  let adj := (shiftEquiv SourceCategory d).toAdjunction
  have h := sourceScalarTelescopeUnit_precomp_bijective p X (Y⟦-d⟧)
  constructor
  · intro a b hab
    apply (adj.homEquiv _ _).injective
    apply h.injective
    exact (adj.homEquiv_naturality_left (sourceScalarTelescopeUnit p X) a).symm.trans
      ((congrArg (adj.homEquiv X Y) hab).trans
        (adj.homEquiv_naturality_left (sourceScalarTelescopeUnit p X) b))
  · intro a
    obtain ⟨b, hb⟩ := h.surjective ((adj.homEquiv X Y) a)
    refine ⟨(adj.homEquiv (sourceScalarTelescope p X) Y).symm b, ?_⟩
    apply (adj.homEquiv X Y).injective
    exact (adj.homEquiv_naturality_left (sourceScalarTelescopeUnit p X)
      ((adj.homEquiv (sourceScalarTelescope p X) Y).symm b)).trans
        ((congrArg (fun q => sourceScalarTelescopeUnit p X ≫ q)
          ((adj.homEquiv (sourceScalarTelescope p X) Y).apply_symm_apply b)).trans hb)

end KIP126.StableHomotopy.Implementation
