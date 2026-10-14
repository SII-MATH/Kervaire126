module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Pullback.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

/-- Compatible paths into the two factors give an actual path into the
strict pullback, with continuity in both the source and time parameters. -/
def pullbackPathLift {A X Y Z : Prespectrum.{u}} {f : X ⟶ Y} {g : Z ⟶ Y}
    (H : A ⟶ pathPrespectrum X) (K : A ⟶ pathPrespectrum Z)
    (h : ∀ s : I, H ≫ pathEvaluation X s ≫ f = K ≫ pathEvaluation Z s ≫ g) :
    A ⟶ pathPrespectrum (pullbackPrespectrum f g) where
  level n := by
    let Hn : C(A.level n, C(I, X.level n)) := H.level n
    let Kn : C(A.level n, C(I, Z.level n)) := K.level n
    exact (⟨fun p : A.level n × I => ⟨(Hn p.1 p.2, Kn p.1 p.2),
        congrArg (fun k : A ⟶ Y => k.level n p.1) (h p.2)⟩,
      (((Hn.continuous.comp continuous_fst).eval continuous_snd).prodMk
        ((Kn.continuous.comp continuous_fst).eval continuous_snd)).subtype_mk _⟩ :
      C(A.level n × I, pullbackLevel f g n)).curry
  point n := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p : C(I, X.level n) => p s) (H.point n))
      (congrArg (fun p : C(I, Z.level n) => p s) (K.point n))
  bond n x t := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p : C(I, X.level (n+1)) => p s) (H.bond n x t))
      (congrArg (fun p : C(I, Z.level (n+1)) => p s) (K.bond n x t))

end KIP126.StableHomotopy.Implementation.Prespectrum
