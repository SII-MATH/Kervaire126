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

namespace KIP126.Solution.Near126.Conditions
/-- LWX Lemmas 7.10 and 7.11. The quantified types are different:
C₄ varies θ₅ in π_(62,64); C₅ varies [U] in π_(124,134).
Existence of these choices is a proof input, not a hidden M field. -/
def c4_c5_choice_equivalence (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toModelData η →
    (C4 M D.toModelData L ↔
      ∀ θ, ThetaChoice M D.toModelData θ → C4At M D.toModelData L θ) ∧
    (C5 M D.toModelData L η ↔
      ∀ u, UChoice M D.toModelData L u → C5At M D.toModelData L η u)
end KIP126.Solution.Near126.Conditions
