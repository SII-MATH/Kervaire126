module

public import KIP126.Def.Kervaire.Route.Section7.AlphaOne
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.LinProgram.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.Solution.Computation.Route.Staircase


import all Init.Data.String.Search
import all Init.Data.String.Slice

import all Init.Data.String.Legacy

@[expose] public section


/-! Main deductions in Proposition 7.8 and Lemma `lem:x_123_9`.
All source results, complete bases, products and staircase data are the
ones delivered by the sole correlated Challenge2 witness. These are proof
obligations, not added fields of M, A or C. -/
namespace KIP126.Main.Solution.Route.Section7
open KIP126.Core.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route
noncomputable section

-- Preserve the outer local attribute preceding this section in AlphaOne.
attribute [local irreducible] KIP126.LinE2.homogeneousPart
section AlphaOneStaircaseProof
open CategoryTheory
open KIP126.LinE2 KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Challenge2 KIP126.Computation.LinProofs KIP126.Computation.Route
set_option maxRecDepth 10000
private theorem full_staircase_high_cycles {literature : LiteratureInterface}
    (c : ComputationInterface literature)
    (V : SphereVanishingLine standardFoundation.hf2) :
    IsPermanentCycle (sequence standardRouteModel .sphere) (14,138)
      (c.route.realization.basis .sphere 14 138 2) ∧
    IsPermanentCycle (sequence standardRouteModel .sphere) (15,139)
      (c.route.realization.basis .sphere 15 139 1 + c.route.realization.basis .sphere 15 139 3) := by
  constructor
  · exact permanent_cycle_of_reaches1000 V 14 138 (by norm_num) (by norm_num) _
      (staircase_af14_reaches1000 c)
  · exact permanent_cycle_of_reaches1000 V 15 139 (by norm_num) (by norm_num) _
      (staircase_af15_reaches1000 c)

end AlphaOneStaircaseProof

end
end KIP126.Main.Solution.Route.Section7
