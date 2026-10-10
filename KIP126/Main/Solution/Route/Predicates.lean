import KIP126.Interface.Challenge.Challenge2

/-! Paper-route predicates derived after the Challenge 2 boundary. -/
namespace KIP126.Main.Solution.Route

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.Kervaire.Route

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

/-- The local detection/injectivity target used in LWX Proposition 7.8.
It is a Main deduction target, rather than a literature or computation field of
`Challenge2`. The selected route uses `(m,w,s) = (125,130,15)`. -/
def DetectorInjectiveAt (m w s : ℤ) : Prop :=
  ∀ α : BiHom m w (S_0_0 : Syn),
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s α →
    α ≫ KIP126.Literature.Route.detectorMap D = 0 → α = 0

end KIP126.Main.Solution.Route
