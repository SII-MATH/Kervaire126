import KIP126.Def.Algebra.GradedComodule.Shift.Data

/-!
The concrete maps between the tensor of two degree lines and the line in
their sum degree. The unique nonzero Cauchy summand uses scalar multiplication;
the inverse sends a scalar `a` to `1 ⊗ a` in that summand.
-/

namespace KIP126.Algebra.GradedComodule.TensorLine

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u

variable (K : Type u) [Field K]

noncomputable section

/-- Multiply the two scalar coordinates in the unique nonzero tensor summand. -/
def hom (t u : ℤ) :
    degreeLine K t ⊗ degreeLine K u ⟶ degreeLine K (t + u) := by
  classical
  intro n
  exact if hn : n = t + u then
    GradedObject.Monoidal.tensorObjDesc fun i j _ =>
      if hi : i = t then
        if hj : j = u then
          ((GradedObject.singleObjApplyIsoOfEq t (ModuleCat.of K K) i hi).hom ⊗ₘ
              (GradedObject.singleObjApplyIsoOfEq u (ModuleCat.of K K) j hj).hom) ≫
            ModuleCat.ofHom (TensorProduct.lid K K).toLinearMap ≫
            (GradedObject.singleObjApplyIsoOfEq (t + u) (ModuleCat.of K K) n hn).inv
        else 0
      else 0
    else 0

/-- Insert `1 ⊗ a` into the unique nonzero Cauchy summand. -/
def inv (t u : ℤ) :
    degreeLine K (t + u) ⟶ degreeLine K t ⊗ degreeLine K u := by
  classical
  intro n
  exact if hn : n = t + u then
    (GradedObject.singleObjApplyIsoOfEq (t + u) (ModuleCat.of K K) n hn).hom ≫
      ModuleCat.ofHom (TensorProduct.lid K K).symm.toLinearMap ≫
      ((GradedObject.singleObjApplyIso t (ModuleCat.of K K)).inv ⊗ₘ
        (GradedObject.singleObjApplyIso u (ModuleCat.of K K)).inv) ≫
      tensorInclusion K (degreeLine K t) (degreeLine K u) t u n hn.symm
    else 0

end

end KIP126.Algebra.GradedComodule.TensorLine
