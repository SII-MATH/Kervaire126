import KIP126.Def.ClassicalAdams.TowerSSData.NextCycles.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The internal successor relation uses exactly the same next-cycle
representative as the two actual tower quotient pages. -/
theorem adamsTowerSSData_next_relation (s t : ℤ) (n : ℕ)
    (x : (adamsTowerSSData unit X s t).page (n : WithTop ℕ))
    (y : (adamsTowerSSData unit X s t).page ((n + 1 : ℕ) : WithTop ℕ)) :
    (∃ z : (Subobject.underlying.obj
        ((adamsTowerSSData unit X s t).Z ((n + 1 : ℕ) : WithTop ℕ)) : ModuleCat ℤ),
      (Subobject.ofLE
        ((adamsTowerSSData unit X s t).Z ((n + 1 : ℕ) : WithTop ℕ))
        ((adamsTowerSSData unit X s t).Z (n : WithTop ℕ))
        ((adamsTowerSSData unit X s t).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        (adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ)) z = x ∧
      (adamsTowerSSData unit X s t).pageπ ((n + 1 : ℕ) : WithTop ℕ) z = y) ↔
    ∃ w : adamsCycles unit X (n + 2 + 1) (by omega) s t,
      adamsNextCycleToPage unit X (n + 2) (by omega) s t w =
        (adamsTowerSSDataPageIso unit X s t n).hom x ∧
      (adamsCycleBoundaries unit X (n + 2 + 1) (by omega) s t).mkQ w =
        (adamsTowerSSDataPageIso unit X s t (n + 1)).hom y := by
  let e := submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
    (adamsFiniteCycleSubmodule unit X s t (n + 1))
  let q := adamsFiniteCycleEquiv unit X s t (n + 1)
  let j := Subobject.ofLE
    ((adamsTowerSSData unit X s t).Z ((n + 1 : ℕ) : WithTop ℕ))
    ((adamsTowerSSData unit X s t).Z (n : WithTop ℕ))
    ((adamsTowerSSData unit X s t).Z_anti (by exact_mod_cast Nat.le_succ n))
  have h0 (w : adamsFiniteCycleSubmodule unit X s t (n + 1)) :
      (adamsTowerSSDataPageIso unit X s t n).hom
        ((adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ) (j (e.inv w))) =
      adamsNextCycleToPage unit X (n + 2) (by omega) s t (q w) := by
    exact congrArg (fun f => f.hom w) (adamsTowerSSDataPageIso_submodule_π unit X s t n
      (adamsFiniteCycleSubmodule unit X s t (n + 1))
      (adamsFiniteCycleSubmodule_antitone unit X s t (Nat.le_succ n)))
  have h1 (w : adamsFiniteCycleSubmodule unit X s t (n + 1)) :
      (adamsTowerSSDataPageIso unit X s t (n + 1)).hom
        ((adamsTowerSSData unit X s t).pageπ ((n + 1 : ℕ) : WithTop ℕ) (e.inv w)) =
      (adamsCycleBoundaries unit X (n + 2 + 1) (by omega) s t).mkQ (q w) := by
    exact congrArg (fun f => f.hom w) (adamsTowerSSDataPageIso_π unit X s t (n + 1))
  constructor
  · rintro ⟨z, hx, hy⟩
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective e.inv).mp inferInstance z
    exact ⟨q w, (h0 w).symm.trans (congrArg
      (adamsTowerSSDataPageIso unit X s t n).hom hx),
      (h1 w).symm.trans (congrArg (adamsTowerSSDataPageIso unit X s t (n + 1)).hom hy)⟩
  · rintro ⟨w, hx, hy⟩
    obtain ⟨w, rfl⟩ := q.surjective w
    refine ⟨e.inv w, ?_, ?_⟩
    · exact (adamsTowerSSDataPageIso unit X s t n).toLinearEquiv.injective ((h0 w).trans hx)
    · exact (adamsTowerSSDataPageIso unit X s t (n + 1)).toLinearEquiv.injective
        ((h1 w).trans hy)

end
end KIP126.Classical.Adams
