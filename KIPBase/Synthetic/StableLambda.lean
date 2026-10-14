/-
  KIPBase.Synthetic.StableLambda
  Stable compatibility of the synthetic lambda action and exactness of its
  finite cofiber quotients.
-/
import KIPBase.Synthetic.ShiftCofiber

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIPBase.StableHomotopy

universe u v

noncomputable section

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]
    [SyntheticShiftCofiberCompatibility (Syn := Syn)]

/-- The primitive stable content of the synthetic lambda action: every
lambda power is a morphism of functors commuting with triangulated suspension.

This does not assume that a finite lambda quotient is exact. Exactness is
derived below from the stable 3×3 property of the selected functorial cofiber. -/
class SyntheticStableLambdaCompatibility where
  lambdaPow_commShift (n : ℕ) :
    NatTrans.CommShift (lambdaPowNatTrans (Syn := Syn) n) ℤ

namespace SyntheticStableLambdaCompatibility

variable [SyntheticStableLambdaCompatibility (Syn := Syn)]

/-- Install the stable coherence of each lambda power. -/
noncomputable instance lambdaPowNatTrans_commShift (n : ℕ) :
    NatTrans.CommShift (lambdaPowNatTrans (Syn := Syn) n) ℤ :=
  SyntheticStableLambdaCompatibility.lambdaPow_commShift n

end SyntheticStableLambdaCompatibility

namespace XModLambdaN

variable [SyntheticStableLambdaCompatibility (Syn := Syn)]

noncomputable local instance stableFunctorialCofiberInstance :
    KIPBase.StableHomotopy.TensorTriangulatedCatWithFunctorialCofiber Syn :=
  syn_functorial_cofiber

omit [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    [SyntheticStableLambdaCompatibility (Syn := Syn)] in
/-- The finite lambda quotient functor is definitionally the pointwise
cofiber of the stable natural transformation `lambdaPowNatTrans`. -/
theorem functor_eq_natCofiberFunctor (n : ℕ) :
    functor (Syn := Syn) n =
      HasFunctorialCofiber.natCofiberFunctor Syn
        (lambdaPowNatTrans (Syn := Syn) n) :=
  rfl

/-- Finite lambda quotients commute coherently with triangulated suspension.
This is obtained from stable functorial cofibers, not supplied as a quotient
functor hypothesis. -/
noncomputable instance functor_commShift (n : ℕ) :
    (functor (Syn := Syn) n).CommShift ℤ := by
  change (HasFunctorialCofiber.natCofiberFunctor Syn
    (lambdaPowNatTrans (Syn := Syn) n)).CommShift ℤ
  infer_instance

/-- Finite lambda quotients preserve distinguished triangles. The proof is
the stable 3×3 theorem for the pointwise cofiber of the exact functors
`biShift (0,-n)` and the identity. -/
noncomputable instance functor_isTriangulated (n : ℕ) :
    (functor (Syn := Syn) n).IsTriangulated := by
  change (HasFunctorialCofiber.natCofiberFunctor Syn
    (lambdaPowNatTrans (Syn := Syn) n)).IsTriangulated
  infer_instance

end XModLambdaN

end

end KIPBase.Synthetic
