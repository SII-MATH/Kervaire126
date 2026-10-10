import KIP126.Def.Kervaire.Route.Labels.Data

namespace KIP126.Literature.Route
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Kervaire.Route
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)}

/-- The two classical literature labels used by the tmf input, in the
actual sphere E₂. Their identification with CSV expressions belongs to
C(M). No new independent label for g⁴Δh₁g or product operation is chosen.
Source convention: BMQ §7, g detects κ̄ and Δh₁g detects w. -/
structure TmfLabels (H : Mod2EilenbergMacLane (C := C)) where
  g : E2 H SphereSpectrum 4 24
  delta_h_1_mul_g : E2 H SphereSpectrum 9 54

def TmfLabels.high125 (L : TmfLabels H) (M : MilnorCooperations H) :
    E2 H SphereSpectrum 25 150 :=
  let g_sq : E2 H SphereSpectrum 8 48 :=
    Sphere.Internal.product H M (s := 4) (t := 24) (s' := 4) (t' := 24) L.g L.g
  let g_pow_four : E2 H SphereSpectrum 16 96 :=
    Sphere.Internal.product H M (s := 8) (t := 48) (s' := 8) (t' := 48) g_sq g_sq
  Sphere.Internal.product H M (s := 16) (t := 96) (s' := 9) (t' := 54) g_pow_four L.delta_h_1_mul_g

end
end KIP126.Literature.Route
