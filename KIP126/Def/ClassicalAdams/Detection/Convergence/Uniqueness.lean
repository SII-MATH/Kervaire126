import KIP126.Def.ClassicalAdams.Detection.Convergence.Proofs

/-! A canonical convergence cannot be reselected independently to alter
detection. Every filtration class comes from an actual tower lift and
`CanonicalIdentification` fixes its E-infinity image. The comparison is
unique; no bounded-range Lin calculation is used in this assertion. -/
namespace KIP126.Classical.Adams.TowerDetection
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

theorem Convergence.canonical_unique (A B : Convergence unit X) : A = B := by
  classical
  obtain ⟨eA, cA⟩ := A
  obtain ⟨eB, cB⟩ := B
  suffices he : eA = eB by cases he; rfl
  funext p
  apply Iso.ext_inv
  let π := (filtration unit X).toAssociatedGraded p.1 (p.2-p.1)
  letI : Epi π := inferInstanceAs (Epi (CategoryTheory.Limits.cokernel.π _))
  apply (cancel_epi π).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  have hb : ((filtration unit X).F p.1 (p.2-p.1)).arrow b ∈
      (ModuleCat.subobjectModule _) ((filtration unit X).F p.1 (p.2-p.1)) := ⟨b, rfl⟩
  change _ ∈ (ModuleCat.subobjectModule _) ((ModuleCat.subobjectModule _).symm
    (filtrationSubmodule unit X p.1 (p.2-p.1))) at hb
  rw [OrderIso.apply_symm_apply] at hb
  obtain ⟨a, ha⟩ := hb
  obtain ⟨z, hz⟩ := exists_liftRepresentative unit X p a
  have hA := cA p a z hz b ha.symm
  have hB := cB p a z hz b ha.symm
  change (eA p).inv (π b) = (eB p).inv (π b)
  calc
    _ = ((adamsTowerInternalSpectralSequence unit X).ssData p).pageπ ⊤ z := by
      rw [← hA]
      exact (eA p).toLinearEquiv.symm_apply_apply _
    _ = _ := by
      rw [← hB]
      exact ((eB p).toLinearEquiv.symm_apply_apply _).symm

end KIP126.Classical.Adams.TowerDetection
