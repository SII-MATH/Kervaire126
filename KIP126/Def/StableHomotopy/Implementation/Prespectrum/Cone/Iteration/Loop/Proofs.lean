module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Loop.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Parameter.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology unitInterval
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

theorem coneIterationLoop_apply {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) (s : I) :
    (coneIterationLoop f).level n x s =
      if h : (s : ℝ) ≤ 1/2 then
        Quot.mk (ConeRelation (coneInclusion f) n)
          (.inr (f.level n x,unitInterval.symm ⟨2*s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1,h⟩⟩))
      else Quot.mk (ConeRelation (coneInclusion f) n)
        (.inl (Quot.mk (ConeRelation f n)
          (.inr (x,⟨2*s-1,two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le,s.2.2⟩⟩)))) := by
  unfold coneIterationLoop
  exact Path.trans_apply _ _ s

/-- At time zero the insertion parameter recovers the original inner
cylinder, including its attaching endpoint. -/
theorem coneIterationLoop_parameter_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) (s : I) :
    (coneIterationLoop f).level n x (coneIterationParameter s 0) =
      Quot.mk (ConeRelation (coneInclusion f) n)
        (.inl (Quot.mk (ConeRelation f n) (.inr (x,s)))) := by
  rw [coneIterationLoop_apply]
  split_ifs with h
  · have hs : s = 0 := Subtype.ext (by
      change (1 - (0:ℝ) + (1 + 0)*(s:ℝ))/2 ≤ 1/2 at h
      change (s : ℝ) = 0
      linarith [s.2.1])
    subst s
    have ht : unitInterval.symm
        (⟨2 * (coneIterationParameter 0 0 : ℝ),
          (mul_pos_mem_iff zero_lt_two).2 ⟨(coneIterationParameter 0 0).2.1,h⟩⟩ : I) = 0 :=
      Subtype.ext (by norm_num [coneIterationParameter, unitInterval.coe_symm_eq])
    rw [ht]
    exact (Quot.sound (ConeRelation.start (f.level n x))).trans
      (congrArg (fun z => Quot.mk (ConeRelation (coneInclusion f) n) (.inl z))
        (Quot.sound (ConeRelation.start x)).symm)
  · have ht : (⟨2 * (coneIterationParameter s 0 : ℝ) - 1,
        two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le,(coneIterationParameter s 0).2.2⟩⟩ : I) = s := by
      apply Subtype.ext
      dsimp [coneIterationParameter]
      ring
    rw [ht]

/-- At the attaching end, the insertion follows exactly the prescribed
outer cylinder homotopy. -/
theorem coneIterationLoop_parameter_zero_left {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) (t : I) :
    (coneIterationLoop f).level n x (coneIterationParameter 0 t) =
      Quot.mk (ConeRelation (coneInclusion f) n) (.inr (f.level n x,t)) := by
  rw [coneIterationLoop_apply]
  have h : (coneIterationParameter 0 t : ℝ) ≤ 1/2 := by
    dsimp [coneIterationParameter]
    linarith [t.2.1]
  rw [dif_pos h]
  congr 3
  apply Subtype.ext
  simp only [unitInterval.coe_symm_eq]
  dsimp [coneIterationParameter]
  ring

end KIP126.StableHomotopy.Implementation.Prespectrum
