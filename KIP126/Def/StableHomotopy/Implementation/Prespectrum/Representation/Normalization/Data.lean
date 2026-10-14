module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Free.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- The unique actual free sphere map representing a cubical loop. -/
noncomputable def genLoopFreeSphereMap (X : Prespectrum) (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) : free n (sphereLevel r) ⟶ X :=
  (genLoop_freeSphere_map_exists_unique X n r p).choose

/-- The actual free stabilization map is invertible in the ordinary source localization. -/
noncomputable def sourceFreeStabilizationIso (n r : ℕ) :
    sourceLocalization.obj (free (n+1) (sphereLevel (r+1))) ≅
      sourceLocalization.obj (free n (sphereLevel r)) := by
  haveI : IsIso (sourceLocalization.map (freeStabilization n (sphereLevel r))) :=
    stableEquivalences.Q_inverts _ (freeStabilization_stableEquivalence n (sphereLevel r))
  exact asIso (sourceLocalization.map (freeStabilization n (sphereLevel r)))

/-- Cancel simultaneous source-stage and sphere-dimension shifts using the actual free stabilization maps. -/
noncomputable def sourceFreeSphereNormalizeIso : ∀ n r : ℕ,
    sourceLocalization.obj (free n (sphereLevel r)) ≅
      sourceLocalization.obj (free (n-r) (sphereLevel (r-n)))
  | 0, r => eqToIso (by simp)
  | n+1, 0 => eqToIso (by simp)
  | n+1, r+1 => sourceFreeStabilizationIso n r ≪≫ sourceFreeSphereNormalizeIso n r ≪≫ eqToIso (by simp)

/-- A fixed point-set representative of each integer sphere: a suspension sphere in nonnegative degrees and a padded zero sphere in negative degrees. -/
def sourceSpherePrespectrum : ℤ → Prespectrum
  | .ofNat n => free 0 (sphereLevel n)
  | .negSucc n => free (n+1) (sphereLevel 0)

/-- The specified integer sphere in the ordinary, uncompleted source localization. -/
def sourceSphere (d : ℤ) : SourceCategory := sourceLocalization.obj (sourceSpherePrespectrum d)

/-- Identify a shifted free sphere of degree `d` with the specified source sphere, using the actual stabilization comparisons. -/
noncomputable def sourceFreeSphereDegreeIso (d : ℤ) (n r : ℕ) (h : (r : ℤ) = d+n) :
    sourceLocalization.obj (free n (sphereLevel r)) ≅ sourceSphere d :=
  sourceFreeSphereNormalizeIso n r ≪≫ eqToIso (by
    cases d with
    | ofNat k =>
      have hk : (Int.ofNat k : ℤ) = (k : ℤ) := rfl
      have hn : n-r = 0 := by omega
      have hr : r-n = k := by omega
      simp only [sourceSphere,sourceSpherePrespectrum,hn,hr]
    | negSucc k =>
      have hk : (Int.negSucc k : ℤ) = -(k+1 : ℕ) := rfl
      have hn : n-r = k+1 := by omega
      have hr : r-n = 0 := by omega
      simp only [sourceSphere,sourceSpherePrespectrum,hn,hr])

/-- The localized sphere morphism of an actual cubical representative. -/
noncomputable def Representative.sourceMap {X : Prespectrum} {d : ℤ}
    (a : Representative X d) : sourceSphere d ⟶ sourceLocalization.obj X :=
  (sourceFreeSphereDegreeIso d a.stage a.dimension a.degree).inv ≫
    sourceLocalization.map (genLoopFreeSphereMap X a.stage a.dimension a.loop)

/-- The actual stable cubical generator of the specified integer source sphere. -/
noncomputable def sourceSphereGenerator : (d : ℤ) →
    (sourceStableHomotopyFunctor.{0} d).obj (sourceSphere d)
  | .ofNat n => freeSphereGenerator _ 0 n (by simp)
  | .negSucc n => freeSphereGenerator _ (n+1) 0 (by omega)

end KIP126.StableHomotopy.Implementation.Prespectrum
