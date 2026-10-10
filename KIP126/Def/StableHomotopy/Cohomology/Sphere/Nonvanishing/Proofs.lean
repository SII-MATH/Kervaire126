import KIP126.Def.StableHomotopy.Cohomology.Sphere.Proofs

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))

/-- The sphere has a nonzero degree-zero mod-two coefficient, from the
actual tensor unitor and the specified π₀H coordinate. No Milnor or
Künneth comparison is needed. -/
theorem mod2SphereHomology_exists_ne_zero :
    ∃ x : Mod2Homology H 0 SphereSpectrum, x ≠ 0 := by
  let e : Mod2Homology H 0 SphereSpectrum ≃+ HomotopyGroup 0 H.HF2 :=
    ((homotopyGroupFunctor 0).mapIso (ρ_ H.HF2)).addCommGroupIsoToAddEquiv
  refine ⟨e.symm (H.pi0Equiv.symm 1), ?_⟩
  intro hx
  have h := congrArg (fun x => H.pi0Equiv (e x)) hx
  simp at h

end KIP126.StableHomotopy.Cohomology
