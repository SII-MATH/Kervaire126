module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Desuspension.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Telescope.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

private theorem levelHomotopy_comp_apply {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n r : ℕ) (x : _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point) :
    (f ≫ g).levelHomotopy n r x = g.levelHomotopy n r (f.levelHomotopy n r x) := by
  induction x using Quotient.inductionOn with
  | h p => rfl

private theorem sequential_levelHomotopy_inclusion_map (F : ℕ ⥤ Prespectrum.{u})
    (k l : ℕ) (hkl : k ≤ l) (n r : ℕ)
    (x : _root_.HomotopyGroup (Fin r) ((F.obj k).level n) ((F.obj k).level n).point) :
    (sequentialColimitInclusion F l).levelHomotopy n r
      ((F.map (homOfLE hkl)).levelHomotopy n r x) =
        (sequentialColimitInclusion F k).levelHomotopy n r x := by
  rw [← levelHomotopy_comp_apply]
  exact congrArg (fun f => f.levelHomotopy n r x) ((sequentialColimitCocone F).w (homOfLE hkl))

private theorem telescope_levelHomotopy_inclusion_step (X : Prespectrum.{u})
    (k n r : ℕ)
    (x : _root_.HomotopyGroup (Fin r) ((spectrificationStages X k).level n)
      ((spectrificationStages X k).level n).point) :
    (sequentialColimitInclusion (spectrificationDiagram X) (k+1)).levelHomotopy n r
      ((spectrificationCylinderUnit (spectrificationStages X k)).levelHomotopy n r x) =
        (sequentialColimitInclusion (spectrificationDiagram X) k).levelHomotopy n r x := by
  have h := sequential_levelHomotopy_inclusion_map (spectrificationDiagram X) k (k+1)
    (Nat.le_succ k) n r x
  simpa only [spectrificationDiagram,Functor.ofSequence_map_homOfLE_succ] using h

private theorem telescope_levelHomotopy_jointly_surjective_pair (X : Prespectrum.{u})
    [∀ n, T1Space (X.level n)] (n r : ℕ)
    (x y : _root_.HomotopyGroup (Fin r) ((spectrificationTelescope X).level n)
      ((spectrificationTelescope X).level n).point) :
    ∃ (k : ℕ) (p q : _root_.HomotopyGroup (Fin r) ((spectrificationStages X k).level n)
      ((spectrificationStages X k).level n).point),
      (sequentialColimitInclusion (spectrificationDiagram X) k).levelHomotopy n r p = x ∧
      (sequentialColimitInclusion (spectrificationDiagram X) k).levelHomotopy n r q = y := by
  let F := spectrificationDiagram X
  letI (k n : ℕ) : T1Space ((F.obj k).level n) :=
    inferInstanceAs (T1Space ((spectrificationStages X k).level n))
  obtain ⟨k,p,hp⟩ := sequentialColimit_levelHomotopy_jointly_surjective F
    (spectrificationDiagram_successor_closed X) n r x
  obtain ⟨l,q,hq⟩ := sequentialColimit_levelHomotopy_jointly_surjective F
    (spectrificationDiagram_successor_closed X) n r y
  refine ⟨max k l, (F.map (homOfLE (le_max_left k l))).levelHomotopy n r p,
    (F.map (homOfLE (le_max_right k l))).levelHomotopy n r q, ?_, ?_⟩
  · exact (sequential_levelHomotopy_inclusion_map F k _ (le_max_left k l) n r p).trans hp
  · exact (sequential_levelHomotopy_inclusion_map F l _ (le_max_right k l) n r q).trans hq

/-- In the constructed telescope, every actual based stabilization is a
bijection. Its inverse comes from currying at one finite cylinder stage. -/
theorem spectrificationTelescope_stabilize_bijective (X : Prespectrum.{u})
    [∀ n, T1Space (X.level n)] (n r : ℕ) :
    Function.Bijective (stabilizeHomotopy (spectrificationTelescope X) n r) := by
  let F := spectrificationDiagram X
  letI (k n : ℕ) : T1Space ((F.obj k).level n) :=
    inferInstanceAs (T1Space ((spectrificationStages X k).level n))
  constructor
  · intro x y h
    obtain ⟨k,p,q,rfl,rfl⟩ := telescope_levelHomotopy_jointly_surjective_pair X n r x y
    have h' := ((sequentialColimitInclusion F k).levelHomotopy_stabilize n r p).trans
      (h.trans ((sequentialColimitInclusion F k).levelHomotopy_stabilize n r q).symm)
    obtain ⟨l,hkl,he⟩ := sequentialColimit_levelHomotopy_eq_eventually F
      (spectrificationDiagram_successor_closed X) k (n+1) (r+1) _ _ h'
    let p' := (F.map (homOfLE hkl)).levelHomotopy n r p
    let q' := (F.map (homOfLE hkl)).levelHomotopy n r q
    have he' : stabilizeHomotopy (F.obj l) n r p' = stabilizeHomotopy (F.obj l) n r q' :=
      ((F.map (homOfLE hkl)).levelHomotopy_stabilize n r p).symm.trans
        (he.trans ((F.map (homOfLE hkl)).levelHomotopy_stabilize n r q))
    have hd := (spectrificationDesuspend_stabilize (F.obj l) n r p').symm.trans
      ((congrArg (spectrificationDesuspend (F.obj l) n r) he').trans
        (spectrificationDesuspend_stabilize (F.obj l) n r q'))
    have hc := congrArg ((sequentialColimitInclusion F (l+1)).levelHomotopy n r) hd
    have hl := (telescope_levelHomotopy_inclusion_step X l n r p').symm.trans
      (hc.trans (telescope_levelHomotopy_inclusion_step X l n r q'))
    exact (sequential_levelHomotopy_inclusion_map F k l hkl n r p).symm.trans
      (hl.trans (sequential_levelHomotopy_inclusion_map F k l hkl n r q))
  · intro y
    obtain ⟨k,p,hp⟩ := sequentialColimit_levelHomotopy_jointly_surjective F
      (spectrificationDiagram_successor_closed X) (n+1) (r+1) y
    refine ⟨(sequentialColimitInclusion F (k+1)).levelHomotopy n r
      (spectrificationDesuspend (F.obj k) n r p), ?_⟩
    exact ((sequentialColimitInclusion F (k+1)).levelHomotopy_stabilize n r
      (spectrificationDesuspend (F.obj k) n r p)).symm.trans
        ((congrArg ((sequentialColimitInclusion F (k+1)).levelHomotopy (n+1) (r+1))
          (stabilize_spectrificationDesuspend (F.obj k) n r p)).trans
            ((telescope_levelHomotopy_inclusion_step X k (n+1) (r+1) p).trans hp))


end KIP126.StableHomotopy.Implementation.Prespectrum
