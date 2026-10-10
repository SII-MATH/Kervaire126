import KIP126.Main.Solution.DifferentialReduction.d12_dichotomy_and_condition_equivalence
import KIP126.Main.Solution.ExtensionObstruction.c3_excludes_c5
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

namespace KIP126.Main.Solution
/-- The purely logical last step of LWX Theorem 7.1. This is conditional
on the two pending propositions; it is not another Final declaration. -/
theorem permanent_of_propositions (η : BiHom 1 2 (S_0_0 : Syn))
    (hη : EtaChoice M D.toModelData η)
    (h78 : KIP126.Solution.Near126.OnlyD12.d12_dichotomy_and_condition_equivalence M D L η)
    (h79 : KIP126.Solution.Near126.C3NotC5.c3_excludes_c5 M D L η) :
    PermanentH6Square M := by
  obtain ⟨cases, criteria⟩ := h78 hη
  rcases cases with h | h
  · exact h.1
  · obtain ⟨h3, _, h5⟩ := criteria.mp h.1
    exact False.elim (h79 hη h3 h5)
end KIP126.Main.Solution
