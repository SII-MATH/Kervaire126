import KIP126.Def.ClassicalAdams.Tmf.Model.Binding.Data
import KIP126.Def.SpectralSequence.Computation.Predicates

/-! The exact target notation of BR21 Table 5.4 / Theorem 5.18.
This is a statement on supplied model coordinates, not a theorem about an
arbitrary algebra object or an identification of such an object with tmf. -/
namespace KIP126.Challenge2
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
universe u v

/-- BR21, author's preliminary book, PDF p.213 / printed p.196:
d₃(w₂²)=βg⁴. The source realization must identify the supplied comparison
with the actual tmf Adams tower. The separate quotient identity converts
this target to the selected β⁵g expression without a name-based inference. -/
def TmfModel.Br21BookStatement {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : Mod2EilenbergMacLane (C := C)}
    (model : TmfModel H) : Prop :=
  HasDifferential (adamsTowerInternalSpectralSequence H.unit model.target.X) 3
    (16, 112) (19, 114) model.coordinates.v2Sixteen model.coordinates.betaGFour

end KIP126.Challenge2

/-! Source endpoint classes for BR21, before any program-coordinate comparison. -/
namespace KIP126.Classical.Adams.Tmf
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The source's w₂² and βg⁴ in its actual HF₂-Adams E₂.
Their identification with program expressions is an Interface computation obligation. -/
structure Br21Classes (H : Mod2EilenbergMacLane (C := C)) (X : C) where
  v2Sixteen : (adamsTowerInternalSpectralSequence H.unit X).Page 2 (16, 112)
  betaGFour : (adamsTowerInternalSpectralSequence H.unit X).Page 2 (19, 114)

end KIP126.Classical.Adams.Tmf
