module

public import KIP126.Def.ClassicalAdams.Suspension.Construction.Comparison.Data
public import Lean.Elab.Command

@[expose] public section


/-! The arbitrary-object constructor uses the selected tensor/unit shift
structures. Its complete integer tower and signed layer squares must remain
independent of the fixed model, native artifacts, and project deliveries. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod then
      throwError "generic suspension construction imports a stage or native artifact: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Classical.Adams.Suspension.Construction.fiberTriangleIso,
      ``KIP126.Classical.Adams.Suspension.Construction.fiberIso,
      ``KIP126.Classical.Adams.Suspension.Construction.fiberIso_hom_ι,
      ``KIP126.Classical.Adams.Suspension.Construction.towerIso,
      ``KIP126.Classical.Adams.Suspension.Construction.towerIso_mapAt,
      ``KIP126.Classical.Adams.Suspension.Construction.cofiberTriangleIso,
      ``KIP126.Classical.Adams.Suspension.Construction.cofiberIso,
      ``KIP126.Classical.Adams.Suspension.Construction.cofiberIso_inclusion,
      ``KIP126.Classical.Adams.Suspension.Construction.cofiberIso_connecting,
      ``KIP126.Classical.Adams.Suspension.Construction.towerComparisonOfTower,
      ``KIP126.Classical.Adams.Suspension.Construction.towerComparison] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in arbitrary-object suspension construction {decl}: {ax}"

namespace KIP126.Checks.ClassicalAdams.SuspensionConstruction

open CategoryTheory MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Classical.Adams.Suspension
open KIP126.Classical.Adams.Suspension.Construction

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(mod2UnitNatTrans H).CommShift ℤ]
  (X : C)

-- The constructor requires no further tensor exactness or octahedron instance.
noncomputable example : TowerComparison H X := towerComparison H X

example : (towerComparison H X).tower 0 = Iso.refl (X⟦(1 : ℤ)⟧) :=
  (towerComparison H X).tower_zero

example (s t : ℤ) (hst : s ≤ t) :
    ((towerComparison H X).tower t).hom ≫
        (adamsTowerMapAt H.unit X s t hst)⟦(1 : ℤ)⟧' =
      adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s t hst ≫
        ((towerComparison H X).tower s).hom :=
  (towerComparison H X).tower_comm s t hst

example (s : ℤ) :
    HasFunctorialCofiber.cofibι
        (adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s (s + 1) (by omega)) ≫
        ((towerComparison H X).layer s).hom =
      ((towerComparison H X).tower s).hom ≫
        (HasFunctorialCofiber.cofibι
          (adamsTowerMapAt H.unit X s (s + 1) (by omega)))⟦(1 : ℤ)⟧' :=
  (towerComparison H X).layer_inclusion s

example (s : ℤ) :
    ((towerComparison H X).layer s).hom ≫
        (HasFunctorialCofiber.cofibδ
          (adamsTowerMapAt H.unit X s (s + 1) (by omega)))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorComm C (1 : ℤ) (1 : ℤ)).hom.app
          (adamsTowerAt H.unit X (s + 1)) =
      -(HasFunctorialCofiber.cofibδ
          (adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s (s + 1) (by omega)) ≫
        ((towerComparison H X).tower (s + 1)).hom⟦(1 : ℤ)⟧') :=
  (towerComparison H X).layer_connecting s

end KIP126.Checks.ClassicalAdams.SuspensionConstruction

#print axioms KIP126.Classical.Adams.Suspension.Construction.towerIso_mapAt
#print axioms KIP126.Classical.Adams.Suspension.Construction.cofiberIso_connecting
#print axioms KIP126.Classical.Adams.Suspension.Construction.towerComparison
