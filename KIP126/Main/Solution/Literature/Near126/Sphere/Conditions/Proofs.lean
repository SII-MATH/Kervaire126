import KIP126.Main.Solution.Literature.Near126.Sphere.Conditions.Predicates
import KIP126.Main.Solution.Literature.Near126.Sphere.Data
import KIP126.Def.SpectralSequence.Computation.Proofs

namespace KIP126.Computation.Near126
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence

/-- The table-facing notation and the fixed final class denote exactly the
same d₁₂ condition; this does not use any differential evidence. -/
theorem Sphere.d12_iff_differential :
    Sphere.D12 ↔ Sphere.Differential 12 KIP126.LinE2.dataH6Sq T := by
  constructor
  · intro h
    exact ⟨by decide, by decide, h⟩
  · rintro ⟨_, _, h⟩
    exact h

/-- Under the explicit survival and exhaustive target inputs, failure of C3
means the actual d₆ hits T. No new source fact or reduction axiom is used. -/
theorem SphereSurvivalFacts.c3_iff_not_d6 (F : SphereSurvivalFacts) :
    Sphere.C3 ↔ ¬ Sphere.Differential 6 W T := by
  have hvanish := differentialVanishesOn_iff_not_hasNonzeroDifferential
    (E := sphereAdamsData) (r := 6) (p := (8, 134))
    (x := linToSphereE2 8 134 (by decide) W)
    (linToSphereE2 14 139 (by decide) T) F.w_d6_targets
  constructor
  · rintro ⟨_, hz⟩ ⟨_, _, h⟩
    exact hvanish.mp hz h
  · intro hn
    refine ⟨F.w_to_e6, hvanish.mpr ?_⟩
    exact fun h => hn ⟨by decide, by decide, h⟩

/-- With C3, the complete incoming-exhaustion input for T reduces to the
fixed nonzero d₁₂ alternative. This is not a proof that D12 is false. -/
theorem SphereSurvivalFacts.hit_t_iff_d12 (F : SphereSurvivalFacts)
    (hc3 : Sphere.C3) (r : ℤ) :
    HitOnPage sphereAdamsData r (14, 139)
        (linToSphereE2 14 139 (by decide) T) ↔
      r = 12 ∧ Sphere.D12 := by
  constructor
  · intro h
    rcases F.t_only_incoming r h with ⟨_, h6⟩ | ⟨hr, h12⟩
    · exact False.elim ((F.c3_iff_not_d6.mp hc3) h6)
    · exact ⟨hr, Sphere.d12_iff_differential.mpr h12⟩
  · rintro ⟨rfl, h12⟩
    exact h12.hit_target

end KIP126.Computation.Near126
