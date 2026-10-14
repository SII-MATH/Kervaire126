module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Loop.Data
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Rotation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open Topology
open scoped unitInterval Topology.Homotopy
set_option backward.isDefEq.respectTransparency false

theorem diagonalGridLoopHorizontal_homotopic (X Y : Prespectrum.{0}) (n k r : ℕ)
    (p q : GenLoop (Fin r) ((X.level n).smash (Y.level k))
      ((X.level n).smash (Y.level k)).point) (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (diagonalGridLoopHorizontal X Y n k r p)
      (diagonalGridLoopHorizontal X Y n k r q) := by
  obtain ⟨H⟩ := hpq
  refine ⟨{
    toFun := fun z => diagonalGridBondLeft X Y n k
      (H (z.1,fun i => z.2 i.succ),suspensionDesuspensionSign (n+k) (z.2 0))
    continuous_toFun := (diagonalGridBondLeft X Y n k).continuous.comp
      ((H.continuous.comp (continuous_fst.prodMk
        (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
          ((suspensionDesuspensionSign (n+k)).continuous.comp
            ((continuous_apply 0).comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change diagonalGridBondLeft X Y n k (H (0,_),_) = _
    rw [H.apply_zero]
    rfl
  · intro t
    change diagonalGridBondLeft X Y n k (H (1,_),_) = _
    rw [H.apply_one]
    rfl
  · intro s t ht
    change diagonalGridBondLeft X Y n k (H (s,_),_) =
      diagonalGridLoopHorizontal X Y n k r p t
    apply Eq.trans ?_ ((diagonalGridLoopHorizontal X Y n k r p).property t ht).symm
    obtain ⟨i,hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
        rcases suspensionDesuspensionSign_boundary (n+k) (t 0) hi with h | h
        · rw [h,diagonalGridBondLeft_zero]
        · rw [h,diagonalGridBondLeft_one]
    | succ i =>
        have he : H (s,fun j => t j.succ) = p (fun j => t j.succ) := H.eq_fst s ⟨i,hi⟩
        have hp : p (fun j => t j.succ) = ((X.level n).smash (Y.level k)).point :=
          p.property _ ⟨i,hi⟩
        rw [he,hp,diagonalGridBondLeft_point]

theorem diagonalGridLoopVertical_homotopic (X Y : Prespectrum.{0}) (n k r : ℕ)
    (p q : GenLoop (Fin r) ((X.level n).smash (Y.level k))
      ((X.level n).smash (Y.level k)).point) (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (diagonalGridLoopVertical X Y n k r p)
      (diagonalGridLoopVertical X Y n k r q) :=
  stabilizeLoop_homotopic (spaceSmash (X.level n) Y) k r p q hpq

private theorem diagonalGridDoubleBond_collapsed (X Y : Prespectrum.{0}) (n k : ℕ)
    (z : (X.level n).smash (Y.level k)) (s t : I)
    (h : z = ((X.level n).smash (Y.level k)).point ∨
      s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) :
    (spaceSmash (X.level (n+1)) Y).bond k (diagonalGridBondLeft X Y n k (z,s),t) =
      ((X.level (n+1)).smash (Y.level (k+1))).point := by
  rcases h with h | h | h | h | h
  · rw [h,diagonalGridBondLeft_point]
    exact (spaceSmash (X.level (n+1)) Y).bond_point k t
  · rw [h,diagonalGridBondLeft_zero]
    exact (spaceSmash (X.level (n+1)) Y).bond_point k t
  · rw [h,diagonalGridBondLeft_one]
    exact (spaceSmash (X.level (n+1)) Y).bond_point k t
  · rw [h]
    exact (spaceSmash (X.level (n+1)) Y).bond_zero k _
  · rw [h]
    exact (spaceSmash (X.level (n+1)) Y).bond_one k _

/-- Horizontal and vertical actual loop transitions commute up to an
explicit based cubical homotopy. The alternating sign makes the required
coordinate exchange a boundary-preserving square rotation. -/
theorem diagonalGridLoop_interchange_homotopic (X Y : Prespectrum.{0}) (n k r : ℕ)
    (p : GenLoop (Fin r) ((X.level n).smash (Y.level k))
      ((X.level n).smash (Y.level k)).point) :
    GenLoop.Homotopic
      (diagonalGridLoopVertical X Y (n+1) k (r+1)
        (diagonalGridLoopHorizontal X Y n k r p))
      (diagonalGridLoopHorizontal X Y n (k+1) (r+1)
        (diagonalGridLoopVertical X Y n k r p)) := by
  obtain ⟨R,h0,h1,hb⟩ := suspensionDesuspension_signed_rotation_exists (n+k+1)
  let T : C(I × (Fin (r+1+1) → I), I × I) :=
    ⟨fun z => R (z.1,(suspensionDesuspensionSign (n+k) (z.2 1),z.2 0)),
      R.continuous.comp (continuous_fst.prodMk
        (((suspensionDesuspensionSign (n+k)).continuous.comp
          ((continuous_apply 1).comp continuous_snd)).prodMk
            ((continuous_apply 0).comp continuous_snd)))⟩
  refine ⟨{
    toFun := fun z => (spaceSmash (X.level (n+1)) Y).bond k
      (diagonalGridBondLeft X Y n k (p (fun i => z.2 i.succ.succ),(T z).1),(T z).2)
    continuous_toFun := (spaceSmash (X.level (n+1)) Y).bond k |>.continuous.comp
      (((diagonalGridBondLeft X Y n k).continuous.comp
        ((p.val.continuous.comp (continuous_pi fun i =>
          (continuous_apply i.succ.succ).comp continuous_snd)).prodMk T.continuous.fst)).prodMk
            T.continuous.snd)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change (spaceSmash (X.level (n+1)) Y).bond k
      (diagonalGridBondLeft X Y n k (p _,(R (0,_)).1),(R (0,_)).2) = _
    rw [h0]
    rfl
  · intro t
    have hs : suspensionDesuspensionSign (n+k+1+1)
        (suspensionDesuspensionSign (n+k) (t 1)) = t 1 := by
      rw [suspensionDesuspensionSign_succ,suspensionDesuspensionSign_succ,
        unitInterval.symm_symm,suspensionDesuspensionSign_twice]
    change (spaceSmash (X.level (n+1)) Y).bond k
      (diagonalGridBondLeft X Y n k (p _,(R (1,_)).1),(R (1,_)).2) = _
    rw [h1,hs]
    change (spaceSmash (X.level (n+1)) Y).bond k
      (diagonalGridBondLeft X Y n k
        (p (fun i => t i.succ.succ),suspensionDesuspensionSign (n+k+1) (t 0)),t 1) =
      diagonalGridBondLeft X Y n (k+1)
        ((spaceSmash (X.level n) Y).bond k (p (fun i => t i.succ.succ),t 1),
          suspensionDesuspensionSign (n+(k+1)) (t 0))
    simpa only [Nat.add_assoc] using
      (diagonalGridBondLeft_right X Y n k (p (fun i => t i.succ.succ))
        (suspensionDesuspensionSign (n+k+1) (t 0)) (t 1)).symm
  · intro s t ht
    change (spaceSmash (X.level (n+1)) Y).bond k
      (diagonalGridBondLeft X Y n k (p _,(T (s,t)).1),(T (s,t)).2) =
        diagonalGridLoopVertical X Y (n+1) k (r+1)
          (diagonalGridLoopHorizontal X Y n k r p) t
    apply Eq.trans ?_ ((diagonalGridLoopVertical X Y (n+1) k (r+1)
      (diagonalGridLoopHorizontal X Y n k r p)).property t ht).symm
    apply diagonalGridDoubleBond_collapsed
    obtain ⟨i,hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
        exact Or.inr (hb s _ (Or.inr (Or.inr hi)))
    | succ i =>
        induction i using Fin.cases with
        | zero =>
            have h := suspensionDesuspensionSign_boundary (n+k) (t 1) hi
            exact Or.inr (hb s _ (h.elim Or.inl (fun h => Or.inr (Or.inl h))))
        | succ i => exact Or.inl (p.property _ ⟨i,hi⟩)

end KIP126.StableHomotopy.Implementation.Prespectrum
