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

namespace KIP126.Solution.Near126.OnlyD12
/-- LWX Proposition 7.8, as a proof target on one model.
This definition does NOT prove it for arbitrary labels/models, nor assume it
as M, A(M), or C(M). Its proof must use the separately established A/C inputs.
The historical unrestricted sorry theorem has deliberately been retired. -/
def d12_dichotomy_and_condition_equivalence (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toModelData η →
    (((PermanentH6Square M ∧ ¬ D12 M L) ∨
        (D12 M L ∧ ¬ PermanentH6Square M)) ∧
      (D12 M L ↔ C3 L ∧ C4 M D.toModelData L ∧ C5 M D.toModelData L η))
end KIP126.Solution.Near126.OnlyD12
