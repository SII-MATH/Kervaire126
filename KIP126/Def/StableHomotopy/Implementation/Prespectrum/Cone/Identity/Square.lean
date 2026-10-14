module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual contraction square of the identity mapping cone uses
s + (1-s)t, expressed inside the closed unit interval. -/
def coneIdentitySquare (X : Prespectrum.{u}) :
    X ⟶ pathPrespectrum (pathPrespectrum (cone (𝟙 X))) where
  level n := by
    have hm : Continuous (fun p : (X.level n × I) × I =>
        unitInterval.symm p.1.2 * unitInterval.symm p.2) := by
      apply Continuous.subtype_mk
      exact ((continuous_subtype_val.comp unitInterval.continuous_symm).comp continuous_fst.snd).mul
        ((continuous_subtype_val.comp unitInterval.continuous_symm).comp continuous_snd)
    exact (⟨fun p : (X.level n × I) × I => Quot.mk (ConeRelation (𝟙 X) n)
        (.inr (p.1.1,unitInterval.symm (unitInterval.symm p.1.2 * unitInterval.symm p.2))),
      continuous_quot_mk.comp (continuous_inr.comp
        (continuous_fst.fst.prodMk (unitInterval.continuous_symm.comp hm)))⟩ :
      C((X.level n × I) × I,coneLevel (𝟙 X) n)).curry.curry
  point n := by
    apply ContinuousMap.ext
    intro s
    apply ContinuousMap.ext
    intro t
    exact Quot.sound (ConeRelation.point _)
  bond n x t := by
    apply ContinuousMap.ext
    intro s
    apply ContinuousMap.ext
    intro u
    rfl
end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem coneIdentitySquare_zero (X : Prespectrum.{u}) :
    coneIdentitySquare X ≫ pathEvaluation (pathPrespectrum (cone (𝟙 X))) 0 = coneNullPath (𝟙 X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  change Quot.mk (ConeRelation (𝟙 X) n)
    (.inr (x,unitInterval.symm (unitInterval.symm 0 * unitInterval.symm t))) =
    Quot.mk (ConeRelation (𝟙 X) n) (.inr (x,t))
  simp

@[simp] theorem coneIdentitySquare_one (X : Prespectrum.{u}) :
    coneIdentitySquare X ≫ pathEvaluation (pathPrespectrum (cone (𝟙 X))) 1 =
      zeroMap X (pathPrespectrum (cone (𝟙 X))) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  change Quot.mk (ConeRelation (𝟙 X) n)
    (.inr (x,unitInterval.symm (unitInterval.symm 1 * unitInterval.symm t))) =
    (coneLevel (𝟙 X) n).point
  simp only [unitInterval.symm_one,zero_mul,unitInterval.symm_zero]
  exact Quot.sound (ConeRelation.finish x)
end KIP126.StableHomotopy.Implementation.Prespectrum

end
