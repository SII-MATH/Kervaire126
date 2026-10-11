import Batteries.Tactic.OpenPrivate
import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
import Init.Data.String.Lemmas.Splits
import KIP126.Def.SpectralSequence.FilteredComplex.Crossing.Proofs
import KIP126.Def.Kervaire.Route.Tools.GeneralizedMahowald.Proofs
import KIP126.Def.Kervaire.Route.Section7.AlphaOne
import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
import KIP126.Def.SpectralSequence.Permanence.Proofs
import KIP126.Def.Synthetic.QuotientTower.Proofs
import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Proofs
import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Predicates
import KIP126.Def.ClassicalAdams.TowerNaturality.Isomorphism.Proofs
import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Data
import KIP126.Def.StableHomotopy.Toda.Law.Proofs
import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs
import KIP126.Def.Synthetic.Context.Coherence.Proofs
import Mathlib.CategoryTheory.Triangulated.Functor
import KIP126.Interface.Solution.Literature.Applications
import KIP126.Main.Solution.Computation.Route.Consequences
import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
import KIP126.LinProgram.Model.Classes.Proofs
import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
import KIP126.Def.SpectralSequence.Computation.Proofs
import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
import KIP126.Def.Algebra.NestedQuotient.Proofs
import KIP126.Def.Synthetic.Detection.Proofs
import KIP126.Def.SpectralSequence.Basic.Category.Proofs
import KIP126.Main.Solution.StageInput
import KIP126.Main.Solution.Computation.Lambda
import KIP126.Def.Kervaire.Route.Section7.Predicates
import KIP126.Main.Solution.Route.AlphaOne

namespace KIP126.Main.Solution.Route.Section7
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Main.StageInput
noncomputable section

local notation "D" => routeModel
local notation "M" => standardMilnorCooperations
local notation "L" => routeLabels
local notation "I" => routeComputation
local notation "η" => routeEta
local notation "h₀" => routeLiterature.toda.h0

/-- This h2 is D's normalized lift of the very nu whose actual cofiber is
used by the computation, with its first-quotient h2 identification delivered
by the same nu applicability record. -/
abbrev h2 := normalizedNu D routeLiterature.applicability.nuCofiber.nu_exponent

abbrev eB := (I).realization.sphere 8 70 KIP126.Computation.Near126.B
abbrev eX := (I).realization.sphere 8 130 KIP126.Computation.Near126.X
abbrev eY := (I).realization.sphere 11 136 KIP126.Computation.Near126.Y
abbrev eH6B := Sphere.Internal.product standardFoundation.hf2 M
  (s := 1) (t := 64) (s' := 8) (t' := 70)
  (Sphere.Internal.hi standardFoundation.hf2 M 6) eB


end
end KIP126.Main.Solution.Route.Section7
