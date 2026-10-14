module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Data
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual adjoint of a strict map out of levelwise reduced suspension. -/
def suspensionLoopCurry {X Y : Prespectrum.{u}} (f : X.suspension ⟶ Y) :
    X ⟶ Prespectrum.loop Y where
  level n :=
    { toFun x :=
        { toFun s := f.level n (BasedSpace.suspensionProjection (X.level n) (x,s))
          continuous_toFun := (f.level n).continuous.comp
            ((BasedSpace.suspensionProjection (X.level n)).continuous.comp
              (continuous_const.prodMk continuous_id))
          source' := by
            rw [BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))]
            exact f.point n
          target' := by
            rw [BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))]
            exact f.point n }
      continuous_toFun := Path.continuous_uncurry_iff.mp
        ((f.level n).continuous.comp (BasedSpace.suspensionProjection (X.level n)).continuous) }
  point n := by
    apply Path.ext
    funext s
    change f.level n (BasedSpace.suspensionProjection (X.level n) ((X.level n).point,s)) = _
    rw [BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)]
    exact f.point n
  bond n x t := by
    apply Path.ext
    funext s
    exact f.bond n (BasedSpace.suspensionProjection (X.level n) (x,s)) t

/-- Evaluation descends through the actual reduced suspension quotient. -/
def suspensionLoopUncurry {X Y : Prespectrum.{u}} (g : X ⟶ Prespectrum.loop Y) :
    X.suspension ⟶ Y := by
  let raw (n : ℕ) : C(X.level n × I,Y.level n) :=
    ⟨fun z => g.level n z.1 z.2,
      continuous_eval.comp (((g.level n).continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have collapsed (n : ℕ) (z : X.level n × I)
      (hz : BasedSpace.SuspensionCollapsed (X.level n) z) : raw n z = (Y.level n).point := by
    rcases hz with h | h | h
    · change g.level n z.1 z.2 = _
      rw [h,g.point]
      rfl
    · change g.level n z.1 z.2 = _
      rw [h,Path.source]
    · change g.level n z.1 z.2 = _
      rw [h,Path.target]
  have respects (n : ℕ) : ∀ a b, BasedSpace.SuspensionRelation (X.level n) a b →
      raw n a = raw n b := fun a b h => (collapsed n a h.1).trans (collapsed n b h.2).symm
  refine
    { level := fun n => ⟨Quot.lift (raw n) (respects n),
        continuous_quot_lift (respects n) (raw n).continuous⟩
      point := fun n => collapsed n ((X.level n).point,0) (Or.inl rfl)
      bond := ?_ }
  intro n x t
  refine Quot.inductionOn x ?_
  rintro ⟨x,s⟩
  exact congrArg (fun p : Path (Y.level (n+1)).point (Y.level (n+1)).point => p s)
    (g.bond n x t)

end KIP126.StableHomotopy.Implementation.Prespectrum
