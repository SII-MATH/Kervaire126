module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Proofs
public import KIP126.Def.StableHomotopy.Completion.Moore.Orthogonality.Proofs
public import KIP126.Def.CategoryTheory.Triangulated.Scalar.Proofs
public import KIP126.Def.CategoryTheory.Preadditive.Scalar.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Shift.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

/-- Each actual Moore stage is annihilated by the square of its defining
scalar power, as a consequence of its actual distinguished triangle. -/
theorem sourceMoorePowerSequence_scalarSquare (p : ℕ) (X : SourceCategory.{u}) (k : ℕ) :
    (p^k)^2 • 𝟙 ((moorePowerSequence p X).obj k) = 0 := by
  simpa only [pow_two, moorePowerSequence] using KIP126.Foundation.nsmul_id_square_eq_zero_of_scalar_triangle
    (p^k) (HasFunctorialCofiber.cofibι (moorePowerMap p X k))
    (HasFunctorialCofiber.cofibδ (moorePowerMap p X k))
    (HasFunctorialCofiber.cofib_distinguished (moorePowerMap p X k))

/-- An actual scalar-invertible source has only the zero map into every
stage of the actual Moore tower. -/
theorem sourceMoorePowerSequence_hom_subsingleton (p : ℕ) (X U : SourceCategory.{u})
    [IsIso (p • 𝟙 U)] (k : ℕ) :
    Subsingleton (U ⟶ (moorePowerSequence p X).obj k) := by
  letI := isIso_nsmul_pow_id p U k
  letI := isIso_nsmul_pow_id (p^k) U 2
  exact KIP126.Foundation.hom_subsingleton_of_nsmul_id_isIso U
    ((moorePowerSequence p X).obj k) ((p^k)^2)
    (sourceMoorePowerSequence_scalarSquare p X k)

/-- Both consecutive represented degrees vanish on the actual tower,
so its genuine Milnor limit is orthogonal to every scalar-invertible source. -/
theorem sourceMooreCompletion_hom_subsingleton (p : ℕ) (X U : SourceCategory.{u})
    [IsIso (p • 𝟙 U)] : Subsingleton (U ⟶ sourceMooreCompletion p X) := by
  letI (k : ℕ) : Subsingleton (U ⟶ (moorePowerSequence p X).obj k) :=
    sourceMoorePowerSequence_hom_subsingleton p X U k
  letI := isIso_nsmul_id_shift p U (1 : ℤ)
  letI (k : ℕ) : Subsingleton (U⟦(1 : ℤ)⟧ ⟶ (moorePowerSequence p X).obj k) :=
    sourceMoorePowerSequence_hom_subsingleton p X (U⟦(1 : ℤ)⟧) k
  constructor
  intro a b
  exact (sourceHomotopyLimitWitness (moorePowerSequence p X)).hom_ext_of_finite
    (fun k => Subsingleton.elim _ _)

/-- Orthogonality holds for every actual coherent integer shift. -/
theorem sourceMooreCompletion_shifted_hom_subsingleton (p : ℕ) (X U : SourceCategory.{u})
    [IsIso (p • 𝟙 U)] (d : ℤ) : Subsingleton (U⟦d⟧ ⟶ sourceMooreCompletion p X) := by
  letI := isIso_nsmul_id_shift p U d
  exact sourceMooreCompletion_hom_subsingleton p X (U⟦d⟧)

/-- The actual dyadic Moore limit satisfies the original point-set
2-completeness predicate, for the fixed positive and negative shifts of S[1/2]. -/
theorem sourceMooreCompletion_isTwoComplete (X : SourceCategory.{0}) :
    (sourceMooreCompletion 2 X).as.obj.IsTwoComplete := by
  intro n
  letI := Prespectrum.sphereInvertTwo_suspension_two_id_isIso n
  letI := Prespectrum.sphereInvertTwo_desuspension_two_id_isIso n
  exact ⟨sourceMooreCompletion_hom_subsingleton 2 X _,
    sourceMooreCompletion_hom_subsingleton 2 X _⟩

end KIP126.StableHomotopy.Implementation
