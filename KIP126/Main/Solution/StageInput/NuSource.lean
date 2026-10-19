module

public import KIP126.Main.Solution.StageInput.Bindings
public import KIP126.LinProgram.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Def.StageInput.StandardSphere.Sequence.Proofs
public import KIP126.Interface.Solution.Literature.Route.RealizationKernel

import all KIP126.Main.Solution.StageInput.NuSource.FromSuspension
import all KIP126.Main.Solution.StageInput.NuSource.Suspension

@[expose] public section

/-! Assemble the ν-cofiber comparison on the sole correlated Challenge2 witness. -/

namespace KIP126.Main.StageInput

open private nu_source_from_suspension_square from
  KIP126.Main.Solution.StageInput.NuSource.FromSuspension
open private selected_nu_suspension_square from
  KIP126.Main.Solution.StageInput.NuSource.Suspension

section NuSourceBasis
open KIP126.LinE2
set_option maxRecDepth 100000
private theorem full_basis_nu_low :
    (∀ r ∈ basisRows, r.s=1 → r.t=4 → r.monomial="2,1") ∧
    (∀ r ∈ basisRows, r.s=2 → r.t=3 → False) := by
  have h := KIP126.LinE2.BasisCertificates.NuLow.nu_low
  exact h

end NuSourceBasis

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory in
theorem nuSourceResults :
    KIP126.Literature.Route.NuCofiberSourceResults routeModel
      literature.bindings.route.nuSource := by
  let c := KIP126.Def.StageInput.witness
  letI : KIP126.Foundation.TensorInput c.foundationInput := c.tensorInput
  letI : (CategoryTheory.MonoidalCategory.tensorLeft
      KIP126.Classical.Adams.standardFoundation.hf2.HF2).CommShift ℤ :=
    c.tensorInput.leftShift c.foundationInput.hf2.HF2
  letI : (CategoryTheory.MonoidalCategory.tensorLeft
      KIP126.Classical.Adams.standardFoundation.hf2.HF2).IsTriangulated :=
    c.tensorInput.leftExact c.foundationInput.hf2.HF2
  have hs : routeModel.nu.functor.map
      ((CategoryTheory.shiftFunctor KIP126.Classical.Adams.standardFoundation.Spectrum (1 : ℤ)).map
        routeModel.auxiliary.nuMap) ≫
      (routeModel.nu.suspensionIso KIP126.StableHomotopy.SphereSpectrum).hom =
    (routeModel.nu.suspensionIso (KIP126.StableHomotopy.Sphere
      (C := KIP126.Classical.Adams.standardFoundation.Spectrum) 3)).hom ≫
      (KIP126.Synthetic.Context.SyntheticCategory.biShift (1,1)).map
        (routeModel.nu.functor.map routeModel.auxiliary.nuMap) := by
    letI : CategoryTheory.SymmetricCategory
        KIP126.Classical.Adams.standardFoundation.Spectrum := c.tensorInput.symmetric
    letI : CategoryTheory.MonoidalPreadditive
        KIP126.Classical.Adams.standardFoundation.Spectrum := c.tensorInput.monoidalPreadditive
    letI : ∀ Z : KIP126.Classical.Adams.standardFoundation.Spectrum,
        (CategoryTheory.MonoidalCategory.tensorRight Z).CommShift ℤ := c.tensorInput.rightShift
    exact selected_nu_suspension_square
      (C := KIP126.Classical.Adams.standardFoundation.Spectrum)
      (Syn := KIP126.Def.standardRouteInput.Syn)
      (H := KIP126.Classical.Adams.standardFoundation.hf2)
      (M := KIP126.Classical.Adams.standardMilnorCooperations) routeModel
      c.cooperationInput.ring c.cooperationInput.kunneth c.cooperationInput.basis
      KIP126.Def.standardSphereSeparated literature.results.synthetic_triangle_lift
      (KIP126.Interface.Solution.Literature.Route.realizationKernel_of_source routeModel
        literature.bindings.route.kernelSource literature.results.route_realizationKernel
        literature.bindings.route.kernelBinding)
  exact @nu_source_from_suspension_square
    KIP126.Classical.Adams.standardFoundation.Spectrum inferInstance inferInstance
    KIP126.Def.standardRouteInput.Syn inferInstance inferInstance
    KIP126.Classical.Adams.standardFoundation.hf2
    KIP126.Classical.Adams.standardMilnorCooperations
    routeModel KIP126.Def.standardRouteBackground
    literature.results.synthetic_e2_weight_vanishing routeEta
    literature.bindings.route.classicalSource literature.bindings.route.classicalBinding
    literature.results.classical_nu_detection literature.results.classical_nu_permanent
    c.cooperationInput.ring
    (c.tensorInput.leftShift c.foundationInput.hf2.HF2)
    (c.tensorInput.leftExact c.foundationInput.hf2.HF2)
    literature.results.synthetic_triangle_lift
    literature.bindings.route.nuSource
    (computation.bindings.presentation.comparison 1 4 (by decide)).symm
    (computation.results.sphereBasis.coordinates 1 4 (by decide))
    (computation.results.sphereBasis.csv_values 1 4 (by decide)) full_basis_nu_low.1 hs

end KIP126.Main.StageInput
