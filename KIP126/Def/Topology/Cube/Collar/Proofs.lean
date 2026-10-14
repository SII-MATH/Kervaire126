module

public import KIP126.Def.Topology.Cube.Collar.Data

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval Topology.Homotopy

theorem continuous_collarCoordinate : Continuous collarCoordinate :=
  continuous_projIcc.comp ((continuous_const.mul continuous_id).sub continuous_const)

theorem collarCoordinate_eq_zero {x : ℝ} (hx : x ≤ 1 / 4) : collarCoordinate x = 0 := by
  exact Set.projIcc_of_le_left zero_le_one (by linarith)

theorem collarCoordinate_eq_one {x : ℝ} (hx : 3 / 4 ≤ x) : collarCoordinate x = 1 := by
  exact Set.projIcc_of_right_le zero_le_one (by linarith)

@[simp] theorem collarCoordinate_zero : collarCoordinate 0 = 0 :=
  collarCoordinate_eq_zero (by norm_num)

@[simp] theorem collarCoordinate_one : collarCoordinate 1 = 1 :=
  collarCoordinate_eq_one (by norm_num)

theorem continuous_collar (r : ℕ) : Continuous (collar r) :=
  continuous_pi fun i => continuous_collarCoordinate.comp (continuous_apply i)

theorem continuous_collarHomotopy (r : ℕ) :
    Continuous (fun z : I × (Fin r → I) => collarHomotopy r z.1 z.2) := by
  apply continuous_pi
  intro i
  exact continuous_projIcc.comp
    (((continuous_const.sub continuous_fst.subtype_val).mul
      ((continuous_apply i).comp continuous_snd).subtype_val).add
      (continuous_fst.subtype_val.mul
        ((continuous_collarCoordinate.comp
          ((continuous_apply i).comp continuous_snd).subtype_val).subtype_val)))

@[simp] theorem collarHomotopy_zero (r : ℕ) (x : Fin r → I) :
    collarHomotopy r 0 x = x := by
  funext i
  change Set.projIcc 0 1 zero_le_one
    (((1 : ℝ) - 0) * (x i : ℝ) + 0 * (collarCoordinate (x i) : ℝ)) = x i
  simpa only [sub_zero, one_mul, zero_mul, add_zero] using
    Set.projIcc_of_mem zero_le_one (x i).property

@[simp] theorem collarHomotopy_one (r : ℕ) (x : Fin r → I) :
    collarHomotopy r 1 x = collar r (fun i => (x i : ℝ)) := by
  funext i
  change Set.projIcc 0 1 zero_le_one
    (((1 : ℝ) - 1) * (x i : ℝ) + 1 * (collarCoordinate (x i) : ℝ)) = collarCoordinate (x i)
  simpa only [sub_self, zero_mul, one_mul, zero_add] using
    Set.projIcc_of_mem zero_le_one (collarCoordinate (x i)).property

theorem collarHomotopy_mem_boundary (r : ℕ) (s : I) (x : Fin r → I)
    (hx : x ∈ _root_.Cube.boundary (Fin r)) :
    collarHomotopy r s x ∈ _root_.Cube.boundary (Fin r) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · left
    change Set.projIcc 0 1 zero_le_one _ = 0
    simp [hi]
  · right
    change Set.projIcc 0 1 zero_le_one _ = 1
    simp [hi]

/-- Every cubical loop is based-homotopic to its explicit collar
reparametrization. The homotopy preserves each boundary face. -/
theorem exists_collared_loop_homotopic {Y : Type*} [TopologicalSpace Y] {b : Y}
    (r : ℕ) (p : GenLoop (Fin r) Y b) :
    ∃ q : GenLoop (Fin r) Y b,
      (∀ x, q x = p (collar r (fun i => (x i : ℝ)))) ∧ GenLoop.Homotopic p q := by
  have hc : Continuous (fun x : Fin r → I => collar r (fun i => (x i : ℝ))) :=
    (continuous_collar r).comp (continuous_pi fun i => (continuous_apply i).subtype_val)
  let q : GenLoop (Fin r) Y b :=
    ⟨⟨fun x => p (collar r (fun i => (x i : ℝ))), p.val.continuous.comp hc⟩, by
      intro x hx
      apply p.property
      simpa only [collarHomotopy_one] using collarHomotopy_mem_boundary r 1 x hx⟩
  refine ⟨q, fun _ => rfl, ⟨{
    toFun := fun z => p (collarHomotopy r z.1 z.2)
    continuous_toFun := p.val.continuous.comp (continuous_collarHomotopy r)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro x
    change p (collarHomotopy r 0 x) = p x
    rw [collarHomotopy_zero]
  · intro x
    change p (collarHomotopy r 1 x) = p (collar r (fun i => (x i : ℝ)))
    rw [collarHomotopy_one]
  · intro s x hx
    exact (p.property _ (collarHomotopy_mem_boundary r s x hx)).trans (p.property x hx).symm

end KIP126.Topology.Cube
