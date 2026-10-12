module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Path.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The associating homotopy is a strict based path-prespectrum map. -/
noncomputable def loopAssocPath {A X : Prespectrum.{u}}
    (f g h : A ⟶ Prespectrum.loop X) : A ⟶ pathPrespectrum (Prespectrum.loop X) :=
  loopGroupPathMap (fun n =>
    ⟨fun z => (Path.Homotopy.transAssoc (f.level n z.1) (g.level n z.1) (h.level n z.1)).eval z.2,
      continuous_loopAssocFamily _ _ _⟩)
    (by
      intro n s
      apply Path.ext
      funext v
      change ((f.level n (A.level n).point).trans
        ((g.level n (A.level n).point).trans (h.level n (A.level n).point))) _ = _
      rw [f.point,g.point,h.point]
      change ((Path.refl (X.level n).point).trans
        ((Path.refl (X.level n).point).trans (Path.refl (X.level n).point))) _ = _
      rw [Path.refl_trans_refl,Path.refl_trans_refl]
      rfl)
    (by
      intro n x t s
      apply Path.ext
      funext v
      change ((f.level (n+1) (A.bond n (x,t))).trans
        ((g.level (n+1) (A.bond n (x,t))).trans (h.level (n+1) (A.bond n (x,t))))) _ =
        X.bond n (((f.level n x).trans ((g.level n x).trans (h.level n x))) _,t)
      rw [f.bond,g.bond,h.bond]
      simp only [Path.trans_apply]
      split_ifs <;> rfl)

/-- Continuously remove the constant right factor, compatibly with all bonds. -/
noncomputable def loopRightUnitPath {A X : Prespectrum.{u}}
    (f : A ⟶ Prespectrum.loop X) : A ⟶ pathPrespectrum (Prespectrum.loop X) :=
  loopGroupPathMap (fun n =>
    ⟨fun z => Path.delayReflRight z.2 (f.level n z.1),
      Path.continuous_delayReflRight.comp
        (continuous_snd.prodMk ((f.level n).continuous.comp continuous_fst))⟩)
    (by
      intro n s
      apply Path.ext
      funext v
      change f.level n (A.level n).point _ = _
      rw [f.point]
      rfl)
    (by
      intro n x t s
      apply Path.ext
      funext v
      change f.level (n+1) (A.bond n (x,t)) _ = X.bond n (f.level n x _,t)
      exact congrArg (fun p : Path (X.level (n+1)).point (X.level (n+1)).point => p _)
        (f.bond n x t))

/-- Continuously remove the constant left factor, compatibly with all bonds. -/
noncomputable def loopLeftUnitPath {A X : Prespectrum.{u}}
    (f : A ⟶ Prespectrum.loop X) : A ⟶ pathPrespectrum (Prespectrum.loop X) :=
  loopGroupPathMap (fun n =>
    ⟨fun z => Path.delayReflLeft z.2 (f.level n z.1),
      Path.continuous_delayReflLeft.comp
        (continuous_snd.prodMk ((f.level n).continuous.comp continuous_fst))⟩)
    (by
      intro n s
      apply Path.ext
      funext v
      change f.level n (A.level n).point _ = _
      rw [f.point]
      rfl)
    (by
      intro n x t s
      apply Path.ext
      funext v
      change f.level (n+1) (A.bond n (x,t)) _ = X.bond n (f.level n x _,t)
      exact congrArg (fun p : Path (X.level (n+1)).point (X.level (n+1)).point => p _)
        (f.bond n x t))

/-- Contract a loop followed by its reverse through actual strict maps. -/
noncomputable def loopRightInversePath {A X : Prespectrum.{u}}
    (f : A ⟶ Prespectrum.loop X) : A ⟶ pathPrespectrum (Prespectrum.loop X) :=
  loopGroupPathMap (fun n =>
    ⟨fun z => (Path.Homotopy.reflTransSymm (f.level n z.1)).eval z.2,
      continuous_loopCancelFamily _⟩)
    (by
      intro n s
      apply Path.ext
      funext v
      change f.level n (A.level n).point _ = _
      rw [f.point]
      rfl)
    (by
      intro n x t s
      apply Path.ext
      funext v
      change f.level (n+1) (A.bond n (x,t)) _ = X.bond n (f.level n x _,t)
      exact congrArg (fun p : Path (X.level (n+1)).point (X.level (n+1)).point => p _)
        (f.bond n x t))

end KIP126.StableHomotopy.Implementation.Prespectrum
