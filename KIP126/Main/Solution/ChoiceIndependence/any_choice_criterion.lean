import KIP126.Def.Kervaire.Route.Conditions.Predicates
import KIP126.Def.Kervaire.Route.Model.Coherent.Data

open KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (M : MilnorCooperations H)
  (D : Model H M Syn) (L : Labels H)

namespace KIP126.Solution.Near126.Thm7_3BJMBX
open KIP126.Kervaire
/-- The actual-model Theorem 7.3 / Remark 7.4 obligation. The original BX
criterion at its source choice remains A(M); transport to every θ₅ and the
normalized exponent are paper deductions. This definition asserts neither. -/
def any_choice_criterion (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toModelData η →
    ∀ θ, ThetaChoice M D.toModelData θ →
      BJMNormalizedFiniteCriterion H M η θ ∧
      BJMUntruncatedCriterion H M η θ
end KIP126.Solution.Near126.Thm7_3BJMBX
