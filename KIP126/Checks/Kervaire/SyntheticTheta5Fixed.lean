import KIP126.Def.Kervaire.Theta5.Synthetic.Predicates
import KIP126.Def.StageInput.StandardSphere.Classes.Data
import Lean.Elab.Command

open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire KIP126.Kervaire.SyntheticTheta5 KIP126.Classical.Adams
open KIP126.Core.SpectralSequence
universe w
variable {Syn : Type w} [SyntheticCategory.{w, 0} Syn]
  [HasFunctorialCofiber (C := Syn)]

-- Specialization uses exactly T(M)'s existing sphere sequence and standard class.
example (η : Eta Syn) (θ : Theta Syn) :
    BJMUntruncatedCriterion standardFoundation.hf2 standardMilnorCooperations η θ ↔
      (NonzeroSurvival sphereAdamsData (2, 128) standardH6Square ↔
        lambdaEtaThetaSquare η θ = 0) := Iff.rfl

open Lean Elab Command in
run_cmd do
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Main.Axiom).isPrefixOf m || m == `KIP126.Challenge2 then
      throwError "fixed standard comparison acquired C(M): {m}"
