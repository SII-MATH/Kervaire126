module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Cubical.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem loopUncurryLast_loopCurryLast (A : BasedSpace.{u}) (r : ℕ)
    (p : GenLoop (Fin (r+1)) A A.point) :
    loopUncurryLast A r (loopCurryLast A r p) = p := by
  apply GenLoop.ext
  intro t
  change p (Fin.snoc (fun i => t i.castSucc) (t (Fin.last r))) = p t
  rw [show Fin.snoc (fun i => t i.castSucc) (t (Fin.last r)) = t from Fin.snoc_init_self t]

@[simp] theorem loopCurryLast_loopUncurryLast (A : BasedSpace.{u}) (r : ℕ)
    (p : GenLoop (Fin r) (loopLevel A) (loopLevel A).point) :
    loopCurryLast A r (loopUncurryLast A r p) = p := by
  apply GenLoop.ext
  intro t
  apply Path.ext
  funext s
  change p (fun i => (Fin.snoc t s : Fin (r+1) → I) i.castSucc)
    ((Fin.snoc t s : Fin (r+1) → I) (Fin.last r)) = p t s
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

theorem loopUncurryLast_injective (A : BasedSpace.{u}) (r : ℕ) :
    Function.Injective (loopUncurryLast A r) :=
  Function.LeftInverse.injective (loopCurryLast_loopUncurryLast A r)

theorem loopUncurryLast_homotopic_iff (A : BasedSpace.{u}) (r : ℕ)
    (p q : GenLoop (Fin r) (loopLevel A) (loopLevel A).point) :
    GenLoop.Homotopic (loopUncurryLast A r p) (loopUncurryLast A r q) ↔ GenLoop.Homotopic p q := by
  constructor
  · rintro ⟨H⟩
    have h := (show GenLoop.Homotopic
      (loopCurryLast A r (loopUncurryLast A r p))
      (loopCurryLast A r (loopUncurryLast A r q)) from ⟨loopCurryLastHomotopy A r H⟩)
    simpa only [loopCurryLast_loopUncurryLast] using h
  · rintro ⟨H⟩
    exact ⟨loopUncurryLastHomotopy A r H⟩

theorem loopCurryLast_homotopic (A : BasedSpace.{u}) (r : ℕ)
    {p q : GenLoop (Fin (r+1)) A A.point} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (loopCurryLast A r p) (loopCurryLast A r q) := by
  obtain ⟨H⟩ := h
  exact ⟨loopCurryLastHomotopy A r H⟩

/-- The last-coordinate convention makes this compatibility an exact equality. -/
theorem loopUncurryLast_stabilize (X : Prespectrum.{u}) (n r : ℕ)
    (p : GenLoop (Fin r) ((Prespectrum.loop X).level n) ((Prespectrum.loop X).level n).point) :
    loopUncurryLast (X.level (n+1)) (r+1) (stabilizeLoop (Prespectrum.loop X) n r p) =
      stabilizeLoop X n (r+1) (loopUncurryLast (X.level n) r p) := by
  apply GenLoop.ext
  intro t
  rfl

theorem loopCurryLast_stabilize (X : Prespectrum.{u}) (n r : ℕ)
    (p : GenLoop (Fin (r+1)) (X.level n) (X.level n).point) :
    loopCurryLast (X.level (n+1)) (r+1) (stabilizeLoop X n (r+1) p) =
      stabilizeLoop (Prespectrum.loop X) n r (loopCurryLast (X.level n) r p) := by
  apply loopUncurryLast_injective
  rw [loopUncurryLast_loopCurryLast,loopUncurryLast_stabilize,loopUncurryLast_loopCurryLast]

end KIP126.StableHomotopy.Implementation.Prespectrum
