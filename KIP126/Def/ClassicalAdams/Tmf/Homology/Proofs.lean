module

public import KIP126.Def.ClassicalAdams.Tmf.Homology.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Proofs
public import Mathlib.Data.Finsupp.Fintype

@[expose] public section

namespace KIP126.Classical.Adams.Tmf.Homology

open KIP126.Core.Algebra KIP126.Steenrod.Milnor

/-- The polynomial source of the tmf homology calculation is degreewise
finite; this is proved from its monomials, without an E₂ calculation. -/
theorem coefficients_finite (n : ℤ) : Finite (Coefficients n) := by
  classical
  letI := milnorMonomial_finite n
  letI := Fintype.ofFinite (Monomial n)
  change Finite (Monomial n →₀ F2)
  infer_instance

/-- The source polynomial grading has no negative-degree elements. -/
theorem coefficients_negative_subsingleton (n : ℤ) (hn : n < 0) :
    Subsingleton (Coefficients n) := by
  letI : IsEmpty (Monomial n) := ⟨fun d => by
    have h := d.val.property
    have hp := Int.natCast_nonneg (slotWeight d.val.val)
    omega⟩
  infer_instance

end KIP126.Classical.Adams.Tmf.Homology
