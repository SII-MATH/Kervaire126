module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.WellBased.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Topology.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual cubical cofibrancy gives closed basepoints and full point
homotopy extension through the proved strict replacement retract. -/
theorem IsCubicallyCofibrant.level_wellBased {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (n : ℕ) : (X.level n).IsWellBased := by
  letI := hX.level_t1Space n
  refine ⟨isClosed_singleton, ?_⟩
  intro Y f p hp
  obtain ⟨s, hs⟩ := hX.replacement_hasSection
  let q := cubicalReplacementComparison.app X
  have he (x : X.level n) : q.level n (s.level n x) = x :=
    congrArg (fun k : X ⟶ X => k.level n x) hs
  obtain ⟨H, hH0, hHp⟩ := (cubicalReplacementFunctor_level_wellBased X n).2
    Y (f.comp (q.level n)) p (by
      change p 0 = f (q.level n ((cubicalReplacementFunctor.obj X).level n).point)
      rw [q.point]
      exact hp)
  let a : C(X.level n × I, (cubicalReplacementFunctor.obj X).level n × I) :=
    ⟨fun z => (s.level n z.1, z.2),
      ((s.level n).continuous.comp continuous_fst).prodMk continuous_snd⟩
  refine ⟨H.comp a, ?_, ?_⟩
  · intro x
    change H (s.level n x, 0) = f x
    rw [hH0]
    exact congrArg f (he x)
  · intro t
    change H (s.level n (X.level n).point, t) = p t
    rw [s.point]
    exact hHp t

/-- A spectrum with actual cubical left lifting is well based. -/
theorem IsCubicallyCofibrant.wellBased {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) : X.IsWellBased := hX.level_wellBased

end KIP126.StableHomotopy.Implementation.Prespectrum
