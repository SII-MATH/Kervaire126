import KIP126.Def.Kervaire.Route.Conditions.Predicates
import KIP126.Def.Kervaire.Route.Model.Coherent.Data

open KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (M : MilnorCooperations H)
  (D : Model H M Syn) (L : Labels H)

namespace KIP126.Solution.Near126.CandidateReduction
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
/-- The reduction is a pending implication about the actual differentials.
The existential target ranges over correctly graded E₂ labels; nonzero
always refers to E_r via HasNonzeroDifferential. -/
def only_d12_differential_reduction : Prop :=
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  (∀ (r : ℤ), 2 ≤ r → r ≠ 12 →
    ∀ y : E.Page 2 (2 + r, 127 + r),
      ¬ HasNonzeroDifferential E r (2, 128) (2 + r, 127 + r)
        (Sphere.Internal.hiSquare H M 6) y) ∧
    ((∃ y : E.Page 2 (14, 139),
      HasNonzeroDifferential E 12 (2, 128) (14, 139)
        (Sphere.Internal.hiSquare H M 6) y) ↔ D12 M L) ∧
    (¬ D12 M L ↔ PermanentH6Square M)
end KIP126.Solution.Near126.CandidateReduction
