import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications
import KIP126.Def.Kervaire.Route.Tools.GeneralizedLeibniz
import KIP126.Def.Kervaire.Route.Tools.GeneralizedMahowald
import KIP126.Def.Kervaire.Route.Tools.PageExtensionStretching
import Lean.Elab.Command

/-! Compilation/audit boundary for the selected complete route language.
The flat Challenge2 contract uses the implementation already fixed in Def, but
no Main consumer axiom or computed basis may construct the route definitions. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.allImportedModuleNames do
    if (`KIP126.Main.Axiom).isPrefixOf m ||
        (`KIPBase).isPrefixOf m || (`KIP126.Mathlib).isPrefixOf m then
      throwError "route language imports a consumer axiom or a second model: {m}"
  for n in [``KIP126.Kervaire.Route.C3, ``KIP126.Kervaire.Route.C4,
      ``KIP126.Kervaire.Route.C5, ``KIP126.Kervaire.Route.Model,
      ``KIP126.Literature.Route.ThetaBMossInput,
      ``KIP126.Literature.Route.DifferentialLiftInput] do
    for a in ← liftCoreM (collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "route definition has acquired an unproved input: {n}: {a}"

-- Adams and extension degrees compose with exactly one stem loss.
example (s t r m l : ℤ) :
    (s+m,t+m) + (r+l-m,r+l-m-1) = (s+r+l,t+r-1+l) := by
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

-- Moss crossings move from below the possible product preimage to above
-- the product; equivalently IWX Definition 2.15's 0 < targetAF-productAF < n+1.
example (q f r n : ℤ) :
    (q < f-(r-1) ∧ f < q+(r+n)) ↔ (0 < q+(r+n)-f ∧ q+(r+n)-f < n+1) := by omega
