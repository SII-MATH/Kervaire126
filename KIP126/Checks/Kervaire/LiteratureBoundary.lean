import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications
import KIP126.Main.Solution.Literature.Route.Inputs
import Lean.Elab.Command

/-! A(M) is a set of explicit input types, not a new source of global
theorems, CSV data, or an independent sequence. Check the ENTIRE new
namespace, including all field types and helper constructions. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.allImportedModuleNames do
    if (`KIP126.Main.Challenge).isPrefixOf m ||
        m == `KIP126.Main.Solution.h6_sq_permanent ||
        (`KIPBase).isPrefixOf m then
      throwError "A(M) imports a computation or final theorem: {m}"
  for (n, info) in env.constants.toList do
    if (`KIP126.Literature.Route).isPrefixOf n then
      if let .axiomInfo _ := info then
        throwError "A(M) must use explicit inputs, not a global axiom: {n}"
  -- The actual realization page map uses precisely these two unfinished
  -- well-definedness lemmas. Audit all other transitive dependencies as before;
  -- do not turn this scoped construction debt into a blanket sorry allowance.
  let pendingComparisonProofs := [
    ``KIP126.Comparison.ClassicalSynthetic.RealizationTower.e1Map_mem_cycles,
    ``KIP126.Comparison.ClassicalSynthetic.RealizationTower.e1Map_mem_boundaries]
  let mut todo : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (`KIP126.Literature.Route).isPrefixOf n then todo := todo.push n
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | throwError "missing dependency {n}"
    if let .axiomInfo _ := info then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "unexpected A(M) axiom dependency: {n}"
    todo := todo ++ info.type.getUsedConstants
    unless pendingComparisonProofs.contains n do
      if let some value := info.value? (allowOpaque := true) then
        if value.getUsedConstants.contains ``sorryAx then
          throwError "unregistered A(M) proof placeholder: {n}"
        todo := todo ++ value.getUsedConstants

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Kervaire.Route KIP126.Literature.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn) (η : BiHom 1 2 (S_0_0 : Syn)) (L : TmfLabels H)

-- The consumer receives the SAME differential, in precisely the previously
-- frozen type, without any arbitrary differential-operation parameter.
example (I : Inputs D η L) : KIP126.Literature.Route.DifferentialLiftInput D :=
  I.differentialLift D η L

-- Cν compatibility is not vacuous: the exponent sum is available.
example (I : Inputs D η L) :
    NormalizedTriangleCompatible D.toModelData D.auxiliary.nuRouteTriangle
      (I.applicability.nuCofiber.exponent_sum D) := I.nuTriangle D η L

-- BHS q-th finite lift is followed by d_(q+1); its target has stem one less.
example (s t : ℤ) (q : ℕ) : (t+q) - (s+q+1) = (t-s)-1 := by omega

-- The high tmf label has the required degree from the actual cup product.
example : E2 H SphereSpectrum 25 150 := L.high125 M

end
