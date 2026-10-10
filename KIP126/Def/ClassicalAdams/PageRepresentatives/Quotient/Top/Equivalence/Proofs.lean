import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Top.Equivalence.Data

namespace KIP126.Classical.Adams.PageRepresentatives

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

@[simp] theorem finiteTopEquiv_apply (q : ℕ) (p : ℤ × ℤ)
    (z : cycles H X q p) : finiteTopEquiv H X q p z = finiteTopClass H X q p z := rfl

@[simp] theorem permanentTopEquiv_apply (p : ℤ × ℤ)
    (z : permanentCycles H X p) :
    permanentTopEquiv H X p z = permanentTopClass H X p z := rfl

@[simp] theorem finiteTopEquiv_symm_topClass (q : ℕ) (p : ℤ × ℤ)
    (z : cycles H X q p) :
    (finiteTopEquiv H X q p).symm (finiteTopClass H X q p z) = z :=
  (finiteTopEquiv H X q p).symm_apply_apply z

@[simp] theorem permanentTopEquiv_symm_topClass (p : ℤ × ℤ)
    (z : permanentCycles H X p) :
    (permanentTopEquiv H X p).symm (permanentTopClass H X p z) = z :=
  (permanentTopEquiv H X p).symm_apply_apply z

end KIP126.Classical.Adams.PageRepresentatives
