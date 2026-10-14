module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Cubical.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

/-- Exactness of actual cubical loops at every level passes to the original
stable homotopy groups; a stable nullhomotopy occurs at a finite later stage. -/
theorem stableHomotopy_exact_of_levelLoop_exact {A B C : Prespectrum.{u}}
    (f : A ⟶ B) (g : B ⟶ C)
    (h : ∀ n r (p : GenLoop (Fin r) (B.level n) (B.level n).point),
      GenLoop.Homotopic (g.levelLoop n r p) GenLoop.const ↔
        ∃ q, GenLoop.Homotopic (f.levelLoop n r q) p)
    (d : ℤ) (x : StableHomotopy B d) :
    stableHomotopyMap g d x = 0 ↔ ∃ y, stableHomotopyMap f d y = x := by
  constructor
  · intro hx
    obtain ⟨k,p,_,rfl,_⟩ := exists_stableLevelClass_pair B d x x
    rw [stableLevelClass_natural] at hx
    have hc := congrArg (stableGroupCode C d)
      (hx.trans (stableLevelClass_one C d k).symm)
    rw [stableGroupCode_levelClass,stableGroupCode_levelClass] at hc
    obtain ⟨j,hkj,_,hj⟩ := Quotient.exact hc
    rw [← g.stableLevelTransition_natural,map_one] at hj
    let p' := stableLevelTransition B d k j hkj p
    have hj' : g.levelHomotopy (stableGroupStage d j) (stableGroupDimension d j) p' = 1 := hj
    obtain ⟨q,hq⟩ := Quotient.exists_rep p'
    rw [← hq] at hj'
    have hh : GenLoop.Homotopic (g.levelLoop _ _ q) GenLoop.const := by
      exact Quotient.exact (hj'.trans _root_.HomotopyGroup.one_def)
    obtain ⟨a,ha⟩ := (h _ _ q).mp hh
    refine ⟨stableLevelClass A d j ⟦a⟧,?_⟩
    rw [stableLevelClass_natural]
    exact (congrArg (stableLevelClass B d j) ((Quotient.sound ha).trans hq)).trans
      (stableLevelClass_transition B d k j hkj p).symm
  · rintro ⟨y,rfl⟩
    induction y using Quot.inductionOn with
    | h a =>
      have hh := (h a.stage a.dimension (f.levelLoop a.stage a.dimension a.loop)).mpr
        ⟨a.loop,GenLoop.Homotopic.refl _⟩
      change loopClass C d a.stage a.dimension a.degree
        (g.levelLoop a.stage a.dimension (f.levelLoop a.stage a.dimension a.loop)) = 0
      exact (loopClass_eq_of_homotopic _ _ _ _ _ hh).trans
        (loopClass_const C d a.stage a.dimension a.degree)

/-- Exactness at πd(X) for the actual homotopy-fiber prespectrum, in every
integer degree and with no condition on the original strict map. -/
theorem fiberProjection_stableHomotopy_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (d : ℤ) (x : StableHomotopy X d) :
    stableHomotopyMap f d x = 0 ↔
      ∃ z, stableHomotopyMap (fiberProjection f) d z = x :=
  stableHomotopy_exact_of_levelLoop_exact (fiberProjection f) f
    (fiberProjection_levelLoop_exact f) d x

end KIP126.StableHomotopy.Implementation.Prespectrum
