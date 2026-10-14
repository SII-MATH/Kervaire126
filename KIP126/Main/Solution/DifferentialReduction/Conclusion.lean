module

public import KIP126.Main.Solution.DifferentialReduction.d12_dichotomy_and_condition_equivalence
public import KIP126.Main.Solution.ExtensionObstruction.eta_extension_excluded_of_d6_vanishes
public import KIP126.Def.Kervaire.Route.Conditions.Predicates
public import KIP126.Def.Kervaire.Route.Model.Coherent.Data

@[expose] public section

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
theorem h6_square_permanent_of_differential_criterion_and_eta_obstruction (η : BiHom 1 2 (S_0_0 : Syn))
    (hη : EtaChoice M D.toModelData η)
    (hcriterion : KIP126.Solution.Near126.OnlyD12.d12_dichotomy_and_condition_equivalence M D L η)
    (hobstruction : KIP126.Solution.Near126.EtaExtensionObstruction.eta_extension_excluded_of_d6_vanishes M D L η) :
    PermanentH6Square M := by
  obtain ⟨cases, criteria⟩ := hcriterion hη
  rcases cases with h | h
  · exact h.1
  · obtain ⟨hvanishing, _, hextension⟩ := criteria.mp h.1
    exact False.elim (hobstruction hη hvanishing hextension)
end KIP126.Main.Solution
