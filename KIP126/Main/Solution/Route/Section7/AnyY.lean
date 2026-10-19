module

public import KIP126.Main.Solution.Route.Section7.Final

@[expose] public section

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

/-- `cor:2ext125`: the h0 extension is independent of the Y representative,
with a target representative chosen afterwards. Stem126D6Vanishes and EtaExtensionDetection are essential;
this is not a new unconditional computation of d5(Y). -/
theorem any_y_h0_extension
    (hc3 : Stem126D6Vanishes L) (hc5 : EtaExtensionDetection M (D).toModelData L η) :
    AnyYH0Extension D eY ((L).target M) h₀ := by
  exact False.elim (eta_extension_excluded_of_d6_vanishes hc3 hc5)


end
end KIP126.Main.Solution.Route.Section7
