module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Cubical.Data
public import KIP126.Def.Topology.Cube.Square.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Read the source coordinate of a fiber-nullhomotopy as actual based loops. -/
def fiberConnectingKernelLoop {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) ((Prespectrum.loop Y).level n) ((Prespectrum.loop Y).level n).point)
    (H : ContinuousMap.HomotopyRel ((fiberConnecting f).levelLoop n r p).val
      (ContinuousMap.const _ ((fiber f).level n).point) (Cube.boundary (Fin r))) :
    GenLoop (Fin r) ((Prespectrum.loop X).level n) ((Prespectrum.loop X).level n).point := by
  let q (x : Fin r → I) : Path (X.level n).point (X.level n).point :=
    { toFun s := (H (s,x)).val.1
      continuous_toFun := continuous_subtype_val.fst.comp
        (H.continuous.comp (continuous_id.prodMk continuous_const))
      source' := congrArg (fun z : fiberLevel f n => z.val.1) (H.apply_zero x)
      target' := congrArg (fun z : fiberLevel f n => z.val.1) (H.apply_one x) }
  refine ⟨⟨q,Path.continuous_uncurry_iff.mp
    (continuous_subtype_val.fst.comp (H.continuous.comp continuous_swap))⟩,?_⟩
  intro x hx
  apply Path.ext
  funext s
  exact congrArg (fun z : fiberLevel f n => z.val.1) (H.eq_fst s hx)

/-- Sliding to the final endpoint contracts the image of an actual source loop
inside the homotopy fiber, with the cubical boundary fixed. -/
def fiberLoopMapNullhomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) ((Prespectrum.loop X).level n) ((Prespectrum.loop X).level n).point) :
    ContinuousMap.HomotopyRel
      ((fiberConnecting f).levelLoop n r ((loopMap f).levelLoop n r p)).val
      (ContinuousMap.const _ ((fiber f).level n).point) (Cube.boundary (Fin r)) := by
  let paths : C((I × (Fin r → I)) × I,Y.level n) :=
    ⟨fun z => f.level n (p z.1.2 (Set.Icc.convexComb z.1.1 1 z.2)),
      (f.level n).continuous.comp (by fun_prop)⟩
  refine
    { toFun := fun z => ⟨(p z.2 z.1,paths.curry z),⟨?_,?_⟩⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · simp only [paths,ContinuousMap.curry_apply,ContinuousMap.coe_mk,Set.Icc.convexComb_zero]
  · simpa only [paths,ContinuousMap.curry_apply,ContinuousMap.coe_mk,Set.Icc.convexComb_one,
      Path.target] using f.point n
  · exact (((p.val.continuous.comp continuous_snd).eval continuous_fst).prodMk
      paths.curry.continuous).subtype_mk _
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · exact (p x).source
    · apply ContinuousMap.ext
      intro s
      change f.level n (p x (Set.Icc.convexComb 0 1 s)) = f.level n (p x s)
      congr 2
      ext
      simp [Set.Icc.convexComb]
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · exact (p x).target
    · apply ContinuousMap.ext
      intro s
      change f.level n (p x (Set.Icc.convexComb 1 1 s)) = (Y.level n).point
      rw [Set.Icc.convexComb_eq,Path.target,f.point]
  · intro s x hx
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun q : Path (X.level n).point (X.level n).point => q s) (p.property x hx)
    · apply ContinuousMap.ext
      intro t
      change f.level n (p x (Set.Icc.convexComb s 1 t)) = f.level n (p x t)
      exact congrArg (f.level n)
        ((congrArg (fun q : Path (X.level n).point (X.level n).point =>
          q (Set.Icc.convexComb s 1 t)) (p.property x hx)).trans
          (congrArg (fun q : Path (X.level n).point (X.level n).point => q t) (p.property x hx)).symm)

end KIP126.StableHomotopy.Implementation.Prespectrum
