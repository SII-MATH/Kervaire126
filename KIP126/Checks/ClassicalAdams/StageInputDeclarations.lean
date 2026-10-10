import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications
import KIP126.Interface.Solution.Challenge2
import KIP126.Interface.Solution.LinProgram.BasisTable
import KIP126.Main.Solution.Computation.LinProgram.Basis.Proofs
import KIP126.Def.StageInput.Milnor
import KIP126.Def.StageInput.StandardSphere.Sequence.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differentials.Certificate
import Lean.Elab.Command

/-!
Check the single direct Challenge2 input and its independent producer. The
fixed sphere applicability statement and its unfinished proof remain in Def.
No second stage assumption, source wrapper or dummy goal is needed.
-/

example : KIP126.Classical.Adams.BHSObjectApplicability
    KIP126.Def.fixedImplementation.foundationInput.countableProducts
    KIP126.Def.fixedImplementation.foundationInput.hf2.unit
    (KIP126.StableHomotopy.SphereSpectrum
      (C := KIP126.Def.fixedImplementation.foundationInput.Spectrum)) :=
  KIP126.Def.standardSphereApplicability

example : KIP126.Def.StageInput.witness = KIP126.Def.fixedImplementation := rfl
example : KIP126.Main.StageInput.witness = KIP126.Main.Axiom.challenge2 := rfl

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless getStructureFields env ``KIP126.Challenge2 == #[`literature, `computation] do
    throwError "Challenge2 must contain exactly the literature and computation deliveries"
  for name in [``KIP126.Def.StageInput.witness,
      ``KIP126.Main.StageInput.witness,
      ``KIP126.Main.StageInput.literature,
      ``KIP126.Main.StageInput.computation,
      ``KIP126.Classical.Adams.standardFoundation,
      ``KIP126.Classical.Adams.standardMilnorCooperations,
      ``KIP126.Classical.Adams.linE2Presentation] do
    let some (.defnInfo _) := env.find? name
      | throwError "compatibility interface must be a definition: {name}"
  for (witness, input) in [
      (``KIP126.Main.StageInput.witness, ``KIP126.Main.Axiom.challenge2)] do
    let axioms ← liftCoreM (collectAxioms witness)
    unless axioms.contains input do
      throwError "stage witness does not consume its matching input: {witness}"
  for background in [``KIP126.Def.StageInput.witness,
      ``KIP126.Def.standardRouteInput, ``KIP126.Def.standardRouteBackground,
      ``KIP126.Def.standardRouteEta, ``KIP126.Def.standardTmfTarget] do
    let foundationAxioms ← liftCoreM (collectAxioms background)
    if foundationAxioms.contains ``KIP126.Main.Axiom.challenge2 then
      throwError "Def's fixed background depends on a consuming stage axiom: {background}"
  let some (.thmInfo _) := env.find? ``KIP126.Computation.LinProofs.sphereTable_sound
    | throwError "sphereTable_sound must be a theorem projected from Challenge 2"

open KIP126.Computation.LinProofs in
example : ∀ (shard offset : Nat) (row : DifferentialRow),
    RawData.lookup shard offset = some row → DifferentialStatement row :=
  sphereTable_sound

-- The independent table certification remains available only from Solution.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for removed in [`KIP126.Challenge1, `KIP126.Interface.Axiom.challenge1,
      `KIP126.Interface.Challenge.challenge2,
      `KIP126.External.ExternalResult, `KIP126.External.ExternalEvidence,
      `KIP126.External.SourceId,
      `KIP126.Challenge2.GeneralizedLeibnizLaw,
      `KIP126.Challenge2.GeneralizedMahowaldLaw,
      `KIP126.Challenge2.FinitePageExtensionStretchingLaw,
      `KIP126.Challenge2.GeometryModel,
      `KIP126.Challenge2.ModelBindings.geometry,
      `KIP126.Challenge2.LiteratureInterface.geometry,
      `KIP126.Challenge2.GeometryLiteratureInterface,
      `KIP126.Challenge2.BrowderInterface,
      `KIP126.Challenge2.LowDimensionalSquarePermanence,
      `KIP126.Foundation.GeometryInterface,
      `KIP126.Interface.Solution.lowDimensionalSquarePermanence,
      `KIP126.Main.StageInput.geometryModel,
      `KIP126.Main.StageInput.geometryLiterature,
      `KIP126.Main.StageInput.geometry,
      `KIP126.Main.StageInput.browder] do
    if env.contains removed then
      throwError "obsolete foundation/computation classification: {removed}"
  let some (.thmInfo _) := env.find? ``KIP126.Interface.Solution.LinE2.basisTable_correct
    | throwError "missing independent basis certification producer"
  let axs ← liftCoreM (collectAxioms ``KIP126.Interface.Solution.LinE2.basisTable_correct)
  if axs.contains ``KIP126.Main.Axiom.challenge2 then
    throwError "basis producer depends on its own stage consumer axiom"

example (s t : ℕ) (ht : t ≤ 261) : KIP126.LinE2.BasisTableCorrect s t :=
  KIP126.Interface.Solution.LinE2.basisTable_correct s t ht

example (c : KIP126.Challenge2) (s t : ℕ) (ht : t ≤ 261)
    (i : KIP126.LinE2.BasisIndex s t) :
    ((c.computation.bindings.presentation.comparison s t ht).symm
      ((c.computation.results.sphereBasis.coordinates s t ht).symm (Finsupp.single i 1))).val =
        KIP126.LinE2.basisValue (KIP126.LinE2.basisRowAt s t i) :=
  c.computation.results.sphereBasis.csv_values s t ht i

-- Both route parts are projections of one witness, never separate choices.
open KIP126.Main.StageInput in
example : routeComputation = witness.computation.route := rfl

open KIP126.Main.StageInput in
example : routeLiterature = KIP126.Literature.Route.Statements.toInputs
    routeModel routeEta tmfLabels routeStatements routeApplication routeTmf := rfl

open KIP126 KIP126.Classical.Adams KIP126.Main.StageInput in
example (s t : ℕ) (ht : t ≤ 261) (x : LinE2.E2At s t) :
    routeComputation.realization.sphere s t x = witness.computation.bindings.presentation.comparison s t ht x :=
  witness.computation.results.route_presentation s t ht x

open KIP126 KIP126.Classical.Adams in
example : KIP126.Main.StageInput.routeModel = standardRouteModel := rfl

open KIP126 KIP126.Classical.Adams in
example (I : KIP126.Challenge2) :
    I.computation.route.realization = I.computation.bindings.routeRealization := rfl

open KIP126 KIP126.Classical.Adams in
example (I : KIP126.Challenge2) :
    I.computation.results.route.toInputs = I.computation.route := rfl

open KIP126 KIP126.Main.StageInput in
example : routeLabels = witness.computation.bindings.routeLabels := rfl

open KIP126 KIP126.Main.StageInput in
example : tmfLabels = witness.literature.bindings.tmfLabels := rfl

open KIP126 KIP126.Main.StageInput in
example : routeEta = Def.standardRouteEta := rfl

open KIP126 KIP126.Classical.Adams in
example : Kervaire.Route.PermanentH6Square standardMilnorCooperations =
    Core.SpectralSequence.NonzeroSurvival sphereAdamsData (2,128) standardH6Square := rfl

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let producer := ``KIP126.Interface.Solution.challenge2
  let consumer := ``KIP126.Main.Axiom.challenge2
  let some (.defnInfo p) := env.find? producer
    | throwError "missing direct package constructor: {producer}"
  let some (.axiomInfo a) := env.find? consumer
    | throwError "missing direct package input: {consumer}"
  unless p.levelParams.isEmpty && a.levelParams.isEmpty do
    throwError "project input acquired universe parameters"
  unless p.type == a.type && p.type == mkConst ``KIP126.Challenge2 do
    throwError "producer and consumer must have precisely type Challenge2"
  for root in [producer, ``KIP126.Def.standardSphereApplicability] do
    if (← liftCoreM (collectAxioms root)).contains consumer then
      throwError "producer depends on the consumer axiom: {root}"
  -- The aggregate's field projections retain their actual proofs in Solution;
  -- their proof debt belongs to the aggregate producer, not a new stage axiom.
  for projection in [``KIP126.Interface.Solution.literatureInterface,
      ``KIP126.Interface.Solution.computationInterface] do
    let some (.thmInfo p) := env.find? projection
      | throwError "missing Solution projection: {projection}"
    if p.value.getUsedConstants.contains ``sorryAx then
      throwError "stage projection lost its existing proof: {projection}"
  -- A producer may use contract definitions, never the final goal placeholder.
  let mut todo : Array Name := #[``KIP126.Interface.Solution.challenge2,
    ``KIP126.Interface.Solution.literatureInterface,
    ``KIP126.Interface.Solution.computationInterface,
    ``KIP126.Interface.Solution.LinE2.basisTable_correct]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "missing producer dependency: {name}"
    if let some moduleIdx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[moduleIdx]!
      if (`KIP126.Main.Challenge).isPrefixOf owner then
        throwError "stage producer borrows an intentional goal proof: {name}: {owner}"
      unless (`KIP126).isPrefixOf owner do continue
    todo := todo ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      todo := todo ++ value.getUsedConstants
  for name in [``KIP126.Main.StageInput.routeModel,
      ``KIP126.Main.StageInput.routeLiterature, ``KIP126.Main.StageInput.routeComputation] do
    let some (.defnInfo _) := env.find? name
      | throwError "route inputs must only be definitions: {name}"

example : Nonempty KIP126.Challenge2.LiteratureInterface :=
  KIP126.Interface.Solution.literatureInterface

example : ∃ literature : KIP126.Challenge2.LiteratureInterface,
      Nonempty (KIP126.Challenge2.ComputationInterface literature) :=
  KIP126.Interface.Solution.computationInterface

-- Introductory classification results are excluded; the classical θ₅
-- results and the body’s Hopf differential remain required route inputs.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for removed in [`KIP126.Challenge2.LiteratureResults.adamsOneLine_at_power,
      `KIP126.Challenge2.LiteratureResults.adamsOneLine_other_degree,
      `KIP126.Challenge2.LiteratureResults.adamsHi_nonzeroSurvival_iff,
      `KIP126.Challenge2.LiteratureResults.may_lowDimensionalProducts_permanent,
      `KIP126.Challenge2.LiteratureResults.may_lowDimensionalSquares_permanent] do
    if env.contains removed then
      throwError "introductory-only result returned to Challenge2: {removed}"
  for retained in [``KIP126.Challenge2.LiteratureResults.adamsOneLine_d2,
      ``KIP126.Literature.Route.ClassicalSourceResults.h5Square_permanent,
      ``KIP126.Literature.Route.ClassicalSourceResults.theta5_detection,
      ``KIP126.Literature.Route.ClassicalSourceResults.theta5_order_two,
      ``KIP126.Literature.Route.ClassicalSourceResults.theta5_filtration_gap] do
    unless env.contains retained do
      throwError "selected route lost a stable-homotopy source input: {retained}"
