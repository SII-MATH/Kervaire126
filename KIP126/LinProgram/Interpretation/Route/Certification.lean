import KIP126.LinProgram.Interpretation.Route.Predicates
import KIP126.Def.Kervaire.Route.Labels.Tmf.Data

/-! Parameterized computation certificates on one interpretation and shared labels. -/

namespace KIP126.Computation.Route
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Core.SpectralSequence KIP126.Synthetic.Context KIP126.Kervaire.Route
open KIP126.LinE2
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Standard Milnor classes and all public route/literature names refer to the
same comparison. These are E₂ identifications, never permanence assumptions. -/
structure LabelsCorrect {D : Model H M Syn} (R : Realization D)
    (L : Labels H) (G : KIP126.Literature.Route.TmfLabels H) : Prop where
  h0 : R.sphere 1 1 dataH0 = Sphere.Internal.hi H M 0
  h1 : R.sphere 1 2 dataH1 = Sphere.Internal.hi H M 1
  h2 : R.sphere 1 4 (Near126.atom .h2) = Sphere.Internal.hi H M 2
  h4 : R.sphere 1 16 (Near126.atom .h4) = Sphere.Internal.hi H M 4
  h5 : R.sphere 1 32 (Near126.atom .h5) = Sphere.Internal.hi H M 5
  h6 : R.sphere 1 64 dataH6 = Sphere.Internal.hi H M 6
  h0_square : R.sphere 2 2 Near126.h0Sq = Sphere.Internal.hiSquare H M 0
  h5_square : R.sphere 2 64 Near126.h5Sq = Sphere.Internal.hiSquare H M 5
  h6_square : R.sphere 2 128 dataH6Sq = Sphere.Internal.hiSquare H M 6
  x_126_8_4 : R.sphere 8 134 (Near126.atom .x_126_8_4) = L.x_126_8_4
  x_126_8 : R.sphere 8 134 (Near126.atom .x_126_8) = L.x_126_8
  x_124_8 : R.sphere 8 132 (Near126.atom .x_124_8) = L.x_124_8
  x_109_12 : R.sphere 12 121 (Near126.atom .x_109_12) = L.x_109_12
  g : R.sphere 4 24 (Near126.atom .g) = G.g
  delta_h_1_mul_g : R.sphere 9 54 (Near126.atom .delta_h_1_mul_g) = G.delta_h_1_mul_g

/-- Stage-1 delivery type. Supplying a value requires proving the selected
computation claims and their interpretation on D. Stage 2 can instead accept
this type as an explicit hypothesis, without invoking bulk/global axioms. -/
structure Inputs (D : Model H M Syn) (L : Labels H)
    (G : KIP126.Literature.Route.TmfLabels H) where
  realization : Realization D
  basis : ∀ d ∈ Raw.degrees, BasisCorrect realization d
  csv : ∀ d ∈ Raw.degrees, SphereBasisValue realization d
  products : ∀ p ∈ Raw.products, ProductCorrect realization p
  labels : LabelsCorrect realization L G
  results : ∀ c ∈ Raw.claims, Statement realization c
  bottom : ∀ p ∈ Raw.bottomMaps, BottomCorrect realization p
  top : TopCorrect realization

/-- Seven atomic certification obligations on ONE interpretation. These are
Interface proof targets; there is no extra stage axiom or fresh choice. -/
structure CertifiedRealization {D : Model H M Syn} (R : Realization D)
    (L : Labels H) (G : KIP126.Literature.Route.TmfLabels H) : Prop where
  basis : ∀ d ∈ Raw.degrees, BasisCorrect R d
  csv : ∀ d ∈ Raw.degrees, SphereBasisValue R d
  products : ∀ p ∈ Raw.products, ProductCorrect R p
  labels : LabelsCorrect R L G
  results : ∀ c ∈ Raw.claims, Statement R c
  bottom : ∀ p ∈ Raw.bottomMaps, BottomCorrect R p
  top : TopCorrect R

/-- Joint existence, not correctness for an arbitrary interpretation/label. -/
def Certification (D : Model H M Syn) (G : KIP126.Literature.Route.TmfLabels H) : Prop :=
  ∃ (R : Realization D) (L : Labels H), CertifiedRealization R L G

/-- Assemble exactly the certified realization. -/
def CertifiedRealization.toInputs {D : Model H M Syn} {R : Realization D}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}
    (h : CertifiedRealization R L G) : Inputs D L G where
  realization := R
  basis := h.basis
  csv := h.csv
  products := h.products
  labels := h.labels
  results := h.results
  bottom := h.bottom
  top := h.top

/-- Recover the same seven conditions without reinterpreting the data. -/
def Inputs.toCertifiedRealization {D : Model H M Syn} {L : Labels H}
    {G : KIP126.Literature.Route.TmfLabels H} (I : Inputs D L G) :
    CertifiedRealization I.realization L G where
  basis := I.basis
  csv := I.csv
  products := I.products
  labels := I.labels
  results := I.results
  bottom := I.bottom
  top := I.top

end
end KIP126.Computation.Route
