import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications

namespace KIP126.Interface.Solution.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
open KIP126.Literature.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Apply the FULL source kernel theorem through the SAME actual adjunction,
λ action and realization comparisons, on exactly the route's selected objects. -/
theorem realizationKernel_of_source (S : RealizationKernelSourceData Syn)
    (hS : RealizationKernelSourceResults D S) (B : RealizationKernelBinding D S) :
    RealizationKernel D := by
  intro X m w a
  rw [B.realization_zero X m w a, hS X m w (S.representatives _ m w a)]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, (S.representatives _ m (w-k)).injective ?_⟩
    rw [map_zero, B.lambda X m w k a]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← B.lambda X m w k a, hk, map_zero]

end
end KIP126.Interface.Solution.Literature.Route
