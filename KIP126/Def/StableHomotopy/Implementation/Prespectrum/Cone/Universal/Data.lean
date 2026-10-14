module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Map.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal cone retains the specified cylinder nullhomotopy of the
composite with its inclusion. -/
def coneNullPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) : X ⟶ pathPrespectrum (cone f) where
  level n :=
    (⟨fun p : X.level n × I => Quot.mk (ConeRelation f n) (.inr p),
      continuous_quot_mk.comp continuous_inr⟩ : C(X.level n × I,coneLevel f n)).curry
  point n := by
    apply ContinuousMap.ext
    intro t
    exact Quot.sound (ConeRelation.point t)
  bond n x t := by
    apply ContinuousMap.ext
    intro s
    rfl

/-- A strict codomain map and actual strict nullhomotopy extend to the
literal mapping-cone quotient. -/
def coneLift {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (a : Y ⟶ Z)
    (H : X ⟶ pathPrespectrum Z) (h₀ : H ≫ pathEvaluation Z 0 = f ≫ a)
    (h₁ : H ≫ pathEvaluation Z 1 = zeroMap X Z) : cone f ⟶ Z := by
  let raw (n : ℕ) : C(Y.level n ⊕ (X.level n × I),Z.level n) :=
    ⟨Sum.elim (a.level n) (show C(X.level n,C(I,Z.level n)) from H.level n).uncurry,
      (a.level n).continuous.sumElim (show C(X.level n,C(I,Z.level n)) from H.level n).uncurry.continuous⟩
  have respects (n : ℕ) : ∀ p q, ConeRelation f n p q → raw n p = raw n q := by
    intro p q h
    cases h with
    | start x => exact congrArg (fun e : X ⟶ Z => e.level n x) h₀
    | finish x => exact (congrArg (fun e : X ⟶ Z => e.level n x) h₁).trans (a.point n).symm
    | point t => exact (congrArg (fun p : C(I,Z.level n) => p t) (H.point n)).trans (a.point n).symm
  refine {
    level n := ⟨Quot.lift (raw n) (respects n),continuous_quot_lift (respects n) (raw n).continuous⟩
    point n := a.point n
    bond := ?_ }
  intro n z t
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,s⟩)
  · exact a.bond n y t
  · exact congrArg (fun p : C(I,Z.level (n+1)) => p s) (H.bond n x t)

end KIP126.StableHomotopy.Implementation.Prespectrum
