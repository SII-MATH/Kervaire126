module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Transpose the retained null-path and the loop coordinate. -/
def fiberLoopTransposedPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(fiberLevel (loopMap f) n × I, C(I, Y.level n)) :=
  (⟨fun z => z.1.1.val.2 z.2 z.1.2,
    continuous_eval.comp
      (((continuous_fst.fst.subtype_val.snd).eval continuous_snd).prodMk
        continuous_fst.snd)⟩ : C((fiberLevel (loopMap f) n × I) × I, Y.level n)).curry

/-- A loop in the source and a null-path of loops determine a loop in
the actual path fiber by the coordinate transpose. -/
def fiberLoopToLoopFiber {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber (loopMap f) ⟶ Prespectrum.loop (fiber f) where
  level n :=
    { toFun z :=
        { toFun s := ⟨(z.val.1 s, fiberLoopTransposedPath f n (z,s)),
            ⟨congrArg (fun q : Path (Y.level n).point (Y.level n).point => q s) z.property.1,
              congrArg (fun q : Path (Y.level n).point (Y.level n).point => q s) z.property.2⟩⟩
          continuous_toFun :=
            (z.val.1.continuous.prodMk ((fiberLoopTransposedPath f n).continuous.comp
              (continuous_const.prodMk continuous_id))).subtype_mk _
          source' := by
            apply Subtype.ext
            refine Prod.ext z.val.1.source ?_
            apply ContinuousMap.ext
            intro t
            exact (z.val.2 t).source
          target' := by
            apply Subtype.ext
            refine Prod.ext z.val.1.target ?_
            apply ContinuousMap.ext
            intro t
            exact (z.val.2 t).target }
      continuous_toFun := Path.continuous_uncurry_iff.mp
        (((continuous_eval.comp (continuous_fst.subtype_val.fst.prodMk continuous_snd)).prodMk
          (fiberLoopTransposedPath f n).continuous).subtype_mk _) }
  point n := by
    apply Path.ext
    funext s
    rfl
  bond n z t := by
    apply Path.ext
    funext s
    rfl

/-- A loop in the actual fiber gives the source loop. -/
def loopFiberSourcePath {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (z : (Prespectrum.loop (fiber f)).level n) :
    Path (X.level n).point (X.level n).point where
  toFun s := (z s).val.1
  continuous_toFun := z.continuous.subtype_val.fst
  source' := congrArg (fun p : (fiber f).level n => p.val.1) z.source
  target' := congrArg (fun p : (fiber f).level n => p.val.1) z.target

/-- A loop in the actual fiber gives a null-path of target loops. -/
def loopFiberTransposedPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C((Prespectrum.loop (fiber f)).level n, C(I, (Prespectrum.loop Y).level n)) := by
  let family : C((Prespectrum.loop (fiber f)).level n × I, (Prespectrum.loop Y).level n) :=
    { toFun z :=
        { toFun s := (z.1 s).val.2 z.2
          continuous_toFun := (z.1.continuous.subtype_val.snd).eval continuous_const
          source' := congrArg (fun p : (fiber f).level n => p.val.2 z.2) z.1.source
          target' := congrArg (fun p : (fiber f).level n => p.val.2 z.2) z.1.target }
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        change Continuous (fun z : ((Prespectrum.loop (fiber f)).level n × I) × I =>
          (z.1.1 z.2).val.2 z.1.2)
        exact ((continuous_eval.comp
          (continuous_fst.fst.prodMk continuous_snd)).subtype_val.snd).eval
            continuous_fst.snd }
  exact family.curry

/-- Inverse coordinate transpose from loops of actual fibers. -/
def loopFiberToFiberLoop {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    Prespectrum.loop (fiber f) ⟶ fiber (loopMap f) where
  level n :=
    { toFun z := ⟨(loopFiberSourcePath f n z, loopFiberTransposedPath f n z),
        ⟨by
            apply Path.ext
            funext s
            change (z s).val.2 0 = f.level n (z s).val.1
            exact (z s).property.1,
          by
            apply Path.ext
            funext s
            change (z s).val.2 1 = (Y.level n).point
            exact (z s).property.2⟩⟩
      continuous_toFun :=
        ((Path.continuous_uncurry_iff.mp continuous_eval.subtype_val.fst).prodMk
          (loopFiberTransposedPath f n).continuous).subtype_mk _ }
  point n := by
    apply Subtype.ext
    apply Prod.ext
    · apply Path.ext; rfl
    · apply ContinuousMap.ext; intro t
      apply Path.ext; rfl
  bond n z t := by
    apply Subtype.ext
    apply Prod.ext
    · apply Path.ext; rfl
    · apply ContinuousMap.ext; intro s
      apply Path.ext; rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
