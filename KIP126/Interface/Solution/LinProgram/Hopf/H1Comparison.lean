module

public import KIP126.Interface.Challenge.Computation.Presentation
public import KIP126.LinProgram.Certificates.Hopf.H1Coordinates
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Hi.Proofs
public import KIP126.Def.StageInput.Milnor
public import KIP126.Interface.Challenge.Literature.Delivery
public import KIP126.Def.ClassicalAdams.Detection.Filtered.Proofs

@[expose] public section


/-!
# Interface/Solution/LinProgram/Hopf/H1Comparison

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! A genuine coordinate-to-class bridge on the fixed sphere's actual E₂.
Exhaustion identifies the unique nonzero class under any supplied presentation.
No imported basis correctness, differential, or higher-page law is assumed. -/

namespace KIP126.Interface.Solution

open CategoryTheory KIP126.Classical.Adams KIP126.StableHomotopy

/-- Every actual element of E₂^(1,2) is zero or the comparison image of CSV h₁. -/
theorem sphereH1_exhaustive (P : LinE2Presentation)
    (x : sphereAdamsData.Page 2 (1, 2)) :
    x = 0 ∨ x = P.comparison 1 2 (by decide) KIP126.LinE2.dataH1 := KIP126.Core.Algebra.LinearEquiv.zero_or_of_exhaustion
    (P.comparison 1 2 (by decide)) KIP126.LinE2.dataH1 KIP126.LinE2.E2At_h1_eq_zero_or x

/-- CSV h₁ denotes the existing standard Milnor class in the fixed actual
sphere E₂, rather than merely an element of an abstract data algebra. -/
theorem sphereH1_standard_class (P : LinE2Presentation) :
    P.comparison 1 2 (by decide) KIP126.LinE2.dataH1 =
      Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 1 := KIP126.Core.Algebra.LinearEquiv.image_eq_of_exhaustion
    (P.comparison 1 2 (by decide)) KIP126.LinE2.dataH1 KIP126.LinE2.E2At_h1_eq_zero_or _
    (MilnorCohomology.internal_hi_ne_zero standardFoundation.hf2 standardMilnorCooperations 1)

/-- The certified CSV class inherits the existing literature's actual Hopf
detection; this does not identify the representative of every filtered lift. -/
theorem sphereH1_detects_eta
    (literature : KIP126.Challenge2.LiteratureInterface) (P : LinE2Presentation) :
    TowerDetection.Detects literature.bindings.route.classicalSource.convergence (1, 2)
      (P.comparison 1 2 (by decide) KIP126.LinE2.dataH1)
      literature.bindings.route.classicalSource.eta := by
  rw [sphereH1_standard_class]
  exact literature.results.classical_eta_detection

/-- Extract an actual filtration-one homotopy lift of eta, giving the
one-sided long-layer construction an actual possible second input. The lift's
specific E2 representative still requires a separate comparison proof. -/
theorem sphereH1_eta_towerLift
    (literature : KIP126.Challenge2.LiteratureInterface) :
    ∃ a : HomotopyGroup (C := standardFoundation.Spectrum) 1
        (adamsTowerAt standardFoundation.hf2.unit SphereSpectrum 1),
      a ≫ adamsTowerMap standardFoundation.hf2.unit SphereSpectrum 0 1 (by decide) =
        literature.bindings.route.classicalSource.eta := by
  exact literature.results.classical_eta_detection.exists_towerLift

end KIP126.Interface.Solution
