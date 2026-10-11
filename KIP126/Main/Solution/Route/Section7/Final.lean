module

public import KIP126.Main.Solution.Route.Section7.NuTarget
public import KIP126.Main.Solution.Route.Section7.CnuRigidity

@[expose] public section

/-! Internal obligations in the second half of LWX Section 7.

All statements use the sole correlated Challenge2 witness. None is a new
literature/computation input, and no statement here is used to certify its
own computational premises. These local proofs still inherit the unfinished
foundations and the existing Challenge2 axiom. Stable paper labels identify
the precise consumers.
-/
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

/-- The final contradiction uses precisely the decoded target and finite
incoming window already supplied by the independent Cnu reconstruction. -/
theorem c3_excludes_c5
    (hc3 : C3 L) : ¬ C5 M (D).toModelData L η := by
  intro hc5
  obtain ⟨y, hy, r, hr, hr', hhit⟩ :=
    target_divisibility_forces_cnu_incoming (target_nu_divisible hc3 hc5)
  obtain ⟨y', hy', _, hnot⟩ := KIP126.Computation.Route.cnu_target_through5 I
  have hyy : y = y' := Option.some.inj (hy.symm.trans hy')
  subst y'
  exact hnot.2.2 r hr hr' hhit

end
end KIP126.Main.Solution.Route.Section7
