module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Representatives.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The doubled-bond stabilization relation becomes precisely the scalar
relation between consecutive stages of the actual telescope. -/
theorem sourceSphereInvertTwoRepresentativeLift_next {d : ℤ}
    (a : Representative sphereInvertTwo d) :
    sourceSphereInvertTwoRepresentativeLift a = sourceSphereInvertTwoRepresentativeLift a.next := by
  rcases a with ⟨n, r, hr, p⟩
  have hc : loopClass sphere d n r hr p =
      loopClass sphere d (n + 1) (r + 1) (by omega) (stabilizeLoop sphere n r p) :=
    Quot.sound (StableRelation.stabilization (⟨n, r, hr, p⟩ : Representative sphere d))
  have hd : sourceStableHomotopyAddEquiv sphere d
      (loopClass sphere d (n + 1) (r + 1) (by omega) (stabilizeLoop sphereInvertTwo n r p)) =
      2 • sourceStableHomotopyAddEquiv sphere d (loopClass sphere d n r hr p) := by
    rw [sphereInvertTwo_stabilizeLoop, loopClass_transAt, ← hc, two_nsmul]
    exact (sourceStableHomotopyAddEquiv sphere d).map_add _ _
  have hi : sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) n =
      2 • sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) (n + 1) := by
    have h := sourceHomotopyColimitInclusion_step (sourceScalarSequence 2 (sourceSphere 0)) n
    rw [sourceScalarSequence_step] at h
    change ((2 : ℕ) • 𝟙 (sourceSphere 0)) ≫
      sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) (n + 1) =
        sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) n at h
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using h.symm
  change sourceStableHomotopyAddEquiv sphere d (loopClass sphere d n r hr p) ≫
      (eqToIso sourceSphere_zero).inv ≫
        sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) n =
    sourceStableHomotopyAddEquiv sphere d
      (loopClass sphere d (n + 1) (r + 1) _ (stabilizeLoop sphereInvertTwo n r p)) ≫
      (eqToIso sourceSphere_zero).inv ≫
        sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) (n + 1)
  rw [hd, hi]
  simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul]

/-- Both defining relations of the unchanged cubical stable quotient
preserve this actual telescope lift. -/
theorem sourceSphereInvertTwoRepresentativeLift_relation {d : ℤ}
    (a b : Representative sphereInvertTwo d) (h : StableRelation sphereInvertTwo d a b) :
    sourceSphereInvertTwoRepresentativeLift a = sourceSphereInvertTwoRepresentativeLift b := by
  cases h with
  | homotopy p hp =>
    unfold sourceSphereInvertTwoRepresentativeLift
    congr 2
    exact Quot.sound (StableRelation.homotopy
      (⟨a.stage, a.dimension, a.degree, a.loop⟩ : Representative sphere d) p hp)
  | stabilization => exact sourceSphereInvertTwoRepresentativeLift_next a

end KIP126.StableHomotopy.Implementation.Prespectrum
