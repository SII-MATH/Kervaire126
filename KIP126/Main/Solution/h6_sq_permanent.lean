import KIP126.Main.Solution.Route.Selected
import KIP126.Def.StageInput.StandardSphere.Classes.Data
import KIP126.Def.SpectralSequence.Permanence.Predicates

/-! The single final proof obligation T(M), paired with
Main/Challenge/h6_sq_permanent.lean.
The final logical step now uses the same delivered A(M)/C(M).
Propositions 7.8 and 7.9 remain unfinished in Main/Solution/Route/Selected. CSV/standard class comparisons are reusable lemmas in the
computation interpretation layer, not a second version of the final theorem.
No Challenge placeholder is used as a proof.
-/
namespace KIP126.Solution.Final.H6SquarePermanent

open KIP126.Classical.Adams KIP126.Core.SpectralSequence

/-- The standard h₆² has a common Z∞ representative projecting to it on E₂,
whose E∞ image is nonzero, in bidegree (s,t) = (2,128). -/
theorem h6_sq_permanent :
    NonzeroSurvival sphereAdamsData (2, 128) standardH6Square := by
  exact KIP126.Main.Solution.permanent_of_propositions
    standardMilnorCooperations KIP126.Main.StageInput.routeModel
    KIP126.Main.StageInput.routeLabels KIP126.Main.StageInput.routeEta
    KIP126.Main.StageInput.routeLiterature.classical.hopf.1
    (KIP126.Main.Solution.Route.proposition_7_8 KIP126.Main.StageInput.witness)
    KIP126.Main.Solution.Route.proposition_7_9

end KIP126.Solution.Final.H6SquarePermanent
