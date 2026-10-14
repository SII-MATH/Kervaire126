module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Kernel.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

variable {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
  (p : GenLoop (Fin r) ((fiber f).level n) ((fiber f).level n).point)
  (H : ContinuousMap.HomotopyRel ((fiberProjection f).levelLoop n r p).val
    (ContinuousMap.const _ (X.level n).point) (Cube.boundary (Fin r)))

/-- Moving the source along its nullhomotopy, while retaining an actual path. -/
noncomputable def fiberMoveLift : C(I × (Fin r → I),fiberLevel f n) where
  toFun z := ⟨(H z,(fiberMoveFamily f n r p H).curry z),
    ⟨(fiberMovePath f n r p H z).source,(fiberMovePath f n r p H z).target⟩⟩
  continuous_toFun := (H.continuous.prodMk (fiberMoveFamily f n r p H).curry.continuous).subtype_mk _

/-- The transported path at the nullhomotopy's final endpoint is a based loop. -/
noncomputable def fiberKernelLoop :
    GenLoop (Fin r) ((Prespectrum.loop Y).level n) ((Prespectrum.loop Y).level n).point := by
  let q (x : Fin r → I) : Path (Y.level n).point (Y.level n).point :=
    { toFun v := fiberMoveFamily f n r p H ((1,x),v)
      continuous_toFun := (fiberMoveFamily f n r p H).continuous.comp
        (continuous_const.prodMk continuous_id)
      source' := by
        change fiberMovePath f n r p H (1,x) 0 = _
        rw [Path.source]
        exact (congrArg (f.level n) (H.apply_one x)).trans (f.point n)
      target' := (fiberMovePath f n r p H (1,x)).target }
  refine ⟨⟨q,Path.continuous_uncurry_iff.mp
    ((fiberMoveFamily f n r p H).continuous.comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd))⟩,?_⟩
  intro x hx
  apply Path.ext
  funext v
  exact fiberMoveFamily_side f n r p H 1 x hx v

/-- At the initial endpoint only a constant path has been prefixed. -/
noncomputable def fiberPaddedLoop :
    GenLoop (Fin r) ((fiber f).level n) ((fiber f).level n).point := by
  refine ⟨(fiberMoveLift f n r p H).comp ⟨fun x => (0,x),continuous_const.prodMk continuous_id⟩,?_⟩
  intro x hx
  apply Subtype.ext
  apply Prod.ext
  · exact (H.eq_fst 0 hx).trans (congrArg (fun z : fiberLevel f n => z.val.1) (p.property x hx))
  · apply ContinuousMap.ext
    intro v
    exact fiberMoveFamily_side f n r p H 0 x hx v

/-- The source-nullhomotopy lifts to a relative homotopy in the actual fiber. -/
noncomputable def fiberMoveHomotopy : ContinuousMap.HomotopyRel
    (fiberPaddedLoop f n r p H).val
    ((fiberConnecting f).levelLoop n r (fiberKernelLoop f n r p H)).val
    (Cube.boundary (Fin r)) where
  toContinuousMap := fiberMoveLift f n r p H
  map_zero_left _ := rfl
  map_one_left x := by
    apply Subtype.ext
    apply Prod.ext
    · exact H.apply_one x
    · rfl
  prop' s x hx := by
    apply Subtype.ext
    apply Prod.ext
    · exact (H.eq_fst s hx).trans (H.eq_fst 0 hx).symm
    · apply ContinuousMap.ext
      intro v
      exact (fiberMoveFamily_side f n r p H s x hx v).trans
        (fiberMoveFamily_side f n r p H 0 x hx v).symm

/-- Removing the initial constant prefix is itself a based relative homotopy. -/
noncomputable def fiberPaddingHomotopy : ContinuousMap.HomotopyRel
    (fiberPaddedLoop f n r p H).val p.val (Cube.boundary (Fin r)) := by
  let paths : C((I × (Fin r → I)) × I,Y.level n) :=
    ⟨fun z => Path.delayReflLeft z.1.1 (fiberCarriedPath f n (p z.1.2)) z.2,by
      change Continuous (fun z : (I × (Fin r → I)) × I => (p z.1.2).val.2 _)
      fun_prop⟩
  refine
    { toFun := fun z => ⟨((p z.2).val.1,paths.curry z),
        ⟨(Path.delayReflLeft z.1 (fiberCarriedPath f n (p z.2))).source,
         (Path.delayReflLeft z.1 (fiberCarriedPath f n (p z.2))).target⟩⟩
      continuous_toFun := ((continuous_subtype_val.fst.comp
        (p.val.continuous.comp continuous_snd)).prodMk paths.curry.continuous).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · exact (H.apply_zero x).symm
    · apply ContinuousMap.ext
      intro v
      exact (congrArg (fun a : Path (f.level n (p x).val.1) (Y.level n).point => a v)
        (Path.delayReflLeft_zero (fiberCarriedPath f n (p x)))).trans
        (fiberMoveFamily_zero f n r p H x v).symm
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro v
      exact congrArg (fun a : Path (f.level n (p x).val.1) (Y.level n).point => a v)
        (Path.delayReflLeft_one (fiberCarriedPath f n (p x)))
  · intro s x hx
    apply Subtype.ext
    apply Prod.ext
    · exact (H.apply_zero x).symm
    · apply ContinuousMap.ext
      intro v
      have hs : paths ((s,x),v) = (Y.level n).point :=
        congrArg (fun z : fiberLevel f n => z.val.2 _) (p.property x hx)
      exact hs.trans (fiberMoveFamily_side f n r p H 0 x hx v).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
