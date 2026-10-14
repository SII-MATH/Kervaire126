module

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

namespace KIP126.Solution.Near126.EtaExtensionObstruction
/-- LWX Proposition 7.9. This is the proposition to derive from the selected
route's inputs, not an unconditional theorem about arbitrary data. The source
differential, η, homotopy product and detection all use D's same objects. -/
def eta_extension_excluded_of_d6_vanishes (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toModelData η → Stem126D6Vanishes L → ¬ EtaExtensionDetection M D.toModelData L η
end KIP126.Solution.Near126.EtaExtensionObstruction

namespace KIP126.Solution.Near126.ExcludeEta
/-- Historical second name; exactly the same pending proposition. -/
abbrev eta_extension_excluded_of_d6_vanishes := @KIP126.Solution.Near126.EtaExtensionObstruction.eta_extension_excluded_of_d6_vanishes
end KIP126.Solution.Near126.ExcludeEta
