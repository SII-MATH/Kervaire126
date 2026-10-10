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

namespace KIP126.Solution.Near126.C3NotC5
/-- LWX Proposition 7.9. This is the proposition to derive from the selected
route's inputs, not an unconditional theorem about arbitrary data. The source
differential, η, homotopy product and detection all use D's same objects. -/
def c3_excludes_c5 (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toModelData η → C3 L → ¬ C5 M D.toModelData L η
end KIP126.Solution.Near126.C3NotC5

namespace KIP126.Solution.Near126.ExcludeEta
/-- Historical second name; exactly the same pending proposition. -/
abbrev c3_excludes_c5 := @KIP126.Solution.Near126.C3NotC5.c3_excludes_c5
end KIP126.Solution.Near126.ExcludeEta
