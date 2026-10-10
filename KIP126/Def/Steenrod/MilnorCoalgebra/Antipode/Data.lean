import KIP126.Def.Steenrod.MilnorCoalgebra.Antipode.Raw.Proofs
import KIP126.Def.Steenrod.MilnorCoalgebra.Data

/-!
Restrict the actual polynomial antipode to every integer-graded component.
The restriction sums its finite polynomial support into the full homogeneous
Milnor basis. It uses no inverse selected from an existence statement.
-/

namespace KIP126.Steenrod.Milnor.Coalgebra.Antipode

open CategoryTheory KIP126.Core.Algebra KIP126.Algebra.GradedVectorSpace

noncomputable section

/-- Reassemble the homogeneous polynomial image as its actual finite support. -/
def monomial {n : ℤ} (m : MilnorMonomial n) : Carrier n :=
  (monomialImage m).support.attach.sum fun d =>
    MvPolynomial.coeff d.val (monomialImage m) •
      Finsupp.single
        ⟨slotExponentsEquiv 1 d.val 0, monomialImage_support_degree m d.val d.property⟩ 1

/-- The degreewise linear antipode on the same Milnor graded coalgebra. -/
def map : dualSteenrod.X ⟶ dualSteenrod.X :=
  fun n => ModuleCat.ofHom (Finsupp.linearCombination F2 (monomial (n := n)))

end
end KIP126.Steenrod.Milnor.Coalgebra.Antipode
