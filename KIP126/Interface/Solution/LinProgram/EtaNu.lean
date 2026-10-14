module

public import KIP126.Def.ClassicalAdams.Detection.Vanishing
public import KIP126.Def.StageInput.StandardSphere.Sequence.Proofs
public import KIP126.LinProgram.Certificates.StemFour
public import KIP126.Interface.Challenge.Computation.Presentation
public import KIP126.Interface.Challenge.Literature.Delivery

@[expose] public section


/-! Eliminate the CW null-composite premise using the same sphere presentation
and literature results. This fixed-model deduction retains the existing
unfinished sphere separation theorem and the original foundational obligations. -/
namespace KIP126.Interface.Solution.LinProgram.EtaNu
open CategoryTheory KIP126.StableHomotopy KIP126.Classical.Adams
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem pageTwo_stemFour_subsingleton
    (bindings : KIP126.Challenge2.LiteratureBindings)
    (results : KIP126.Challenge2.LiteratureResults bindings)
    (P : LinE2Presentation) (s : ℕ) :
    Subsingleton (sphereAdamsData.Page 2 ((s : ℤ), (s : ℤ) + 4)) := by
  by_cases hs : s < 4
  · letI := KIP126.LinE2.StemFour.component_subsingleton s hs
    let e := P.comparison s (s + 4) (by omega)
    have h : Subsingleton (sphereAdamsData.Page 2 ((s : ℤ), ((s + 4 : ℕ) : ℤ))) :=
      ⟨fun x y => e.symm.injective (Subsingleton.elim _ _)⟩
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  · exact results.sphereVanishing (s : ℤ) ((s : ℤ) + 4) (by omega) (by omega)

/-- All nonnegative filtration pieces are used. The existing fixed-sphere
separation theorem remains a visible, currently unfinished dependency. -/
theorem homotopy_four_zero
    (bindings : KIP126.Challenge2.LiteratureBindings)
    (results : KIP126.Challenge2.LiteratureResults bindings)
    (P : LinE2Presentation)
    (x : HomotopyGroup (C := standardFoundation.Spectrum) 4 SphereSpectrum) : x = 0 :=
  TowerDetection.homotopy_eq_zero_of_pageTwo_zero_of_separated
    standardFoundation.hf2.unit SphereSpectrum 4
    (pageTwo_stemFour_subsingleton bindings results P)
    (KIP126.Def.standardSphereSeparated 4) x

/-- The fixed route's actual composite, with its source identified by the
standard shift-add isomorphism. No product/detection comparison is assumed. -/
theorem eta_nu_zero
    (bindings : KIP126.Challenge2.LiteratureBindings)
    (results : KIP126.Challenge2.LiteratureResults bindings)
    (P : LinE2Presentation) :
    (shiftFunctor standardFoundation.Spectrum (3 : ℤ)).map
      standardRouteModel.auxiliary.etaMap ≫ standardRouteModel.auxiliary.nuMap = 0 := by
  let e := (shiftFunctorAdd standardFoundation.Spectrum (1 : ℤ) (3 : ℤ)).app
    (SphereSpectrum (C := standardFoundation.Spectrum))
  apply (cancel_epi e.hom).mp
  have h := homotopy_four_zero bindings results P
    (e.hom ≫ (shiftFunctor standardFoundation.Spectrum (3 : ℤ)).map
      standardRouteModel.auxiliary.etaMap ≫ standardRouteModel.auxiliary.nuMap)
  simpa only [Limits.comp_zero] using h

end
end KIP126.Interface.Solution.LinProgram.EtaNu
