module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Loop.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Collapse the outer target cylinder in the actual second cone. The
remaining inner cylinder is precisely the suspension of the source. -/
def coneIterationComparison {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    cone (coneInclusion f) ⟶ X.suspension :=
  coneLift (coneInclusion f) (coneBoundary f)
    (zeroMap Y (pathPrespectrum X.suspension)) (by rfl) (by rfl)

/-- The inner square inserts the reverse outer cylinder before the
inner cylinder, with the same interval formula at every spectrum level. -/
noncomputable def coneIterationSquare {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    X ⟶ pathPrespectrum (pathPrespectrum (cone (coneInclusion f))) where
  level n := (⟨fun z : (X.level n × I) × I =>
      (coneIterationLoop f).level n z.1.1 (coneIterationParameter z.1.2 z.2),
    continuous_eval.comp (((coneIterationLoop f).level n).continuous.comp
      continuous_fst.fst |>.prodMk (continuous_coneIterationParameter.comp
        (continuous_fst.snd.prodMk continuous_snd)))⟩ :
      C((X.level n × I) × I,(cone (coneInclusion f)).level n)).curry.curry
  point n := by
    apply ContinuousMap.ext; intro s
    apply ContinuousMap.ext; intro t
    exact congrArg (fun p : Path ((cone (coneInclusion f)).level n).point
        ((cone (coneInclusion f)).level n).point => p (coneIterationParameter s t))
      ((coneIterationLoop f).point n)
  bond n x t := by
    apply ContinuousMap.ext; intro s
    apply ContinuousMap.ext; intro v
    exact congrArg (fun p : Path ((cone (coneInclusion f)).level (n+1)).point
        ((cone (coneInclusion f)).level (n+1)).point => p (coneIterationParameter s v))
      ((coneIterationLoop f).bond n x t)

/-- The outer square contracts its cylinder towards its tip. -/
def coneIterationOuterSquare {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    Y ⟶ pathPrespectrum (pathPrespectrum (cone (coneInclusion f))) where
  level n := by
    have hm : Continuous (fun z : (Y.level n × I) × I =>
        unitInterval.symm z.1.2 * unitInterval.symm z.2) := by
      apply Continuous.subtype_mk
      exact ((continuous_subtype_val.comp unitInterval.continuous_symm).comp continuous_fst.snd).mul
        ((continuous_subtype_val.comp unitInterval.continuous_symm).comp continuous_snd)
    exact (⟨fun z : (Y.level n × I) × I => Quot.mk (ConeRelation (coneInclusion f) n)
        (.inr (z.1.1,unitInterval.symm (unitInterval.symm z.1.2 * unitInterval.symm z.2))),
      continuous_quot_mk.comp (continuous_inr.comp
        (continuous_fst.fst.prodMk (unitInterval.continuous_symm.comp hm)))⟩ :
      C((Y.level n × I) × I,(cone (coneInclusion f)).level n)).curry.curry
  point n := by
    apply ContinuousMap.ext; intro s
    apply ContinuousMap.ext; intro t
    exact Quot.sound (ConeRelation.point _)
  bond n x t := by
    apply ContinuousMap.ext; intro s
    apply ContinuousMap.ext; intro v
    rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
