module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Map.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- An actual based homotopy whose map to the compact-open path prespectrum
commutes strictly with the bonding maps. -/
structure StrictHomotopy {X Y : Prespectrum.{u}} (f g : X ⟶ Y) where
  hom : X ⟶ pathPrespectrum Y
  zero : hom ≫ pathEvaluation Y 0 = f
  one : hom ≫ pathEvaluation Y 1 = g

namespace StrictHomotopy

variable {X Y Z : Prespectrum.{u}} {f g k : X ⟶ Y}

/-- Read a strict homotopy as a continuously varying path at one level. -/
def levelPath (H : StrictHomotopy f g) (n : ℕ) (x : X.level n) :
    Path (f.level n x) (g.level n x) where
  toContinuousMap := H.hom.level n x
  source' := congrArg (fun e : X ⟶ Y => e.level n x) H.zero
  target' := congrArg (fun e : X ⟶ Y => e.level n x) H.one

def refl (f : X ⟶ Y) : StrictHomotopy f f where
  hom := f ≫ pathConstant Y
  zero := by rw [Category.assoc,pathConstant_comp_evaluation,Category.comp_id]
  one := by rw [Category.assoc,pathConstant_comp_evaluation,Category.comp_id]

/-- Reverse the actual homotopy parameter. -/
def symm (H : StrictHomotopy f g) : StrictHomotopy g f where
  hom :=
    { level n :=
        { toFun x := (H.levelPath n x).symm.toContinuousMap
          continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _
            (((show C(X.level n,C(I,Y.level n)) from H.hom.level n).continuous.comp
              continuous_fst).eval (unitInterval.continuous_symm.comp continuous_snd)) }
      point n := by
        apply ContinuousMap.ext; intro s
        exact congrArg (fun q : C(I,Y.level n) => q (unitInterval.symm s)) (H.hom.point n)
      bond n x t := by
        apply ContinuousMap.ext; intro s
        exact congrArg (fun q : C(I,Y.level (n+1)) => q (unitInterval.symm s)) (H.hom.bond n x t) }
  zero := by
    apply Hom.ext; funext n
    apply ContinuousMap.ext; intro x
    exact (H.levelPath n x).symm.source
  one := by
    apply Hom.ext; funext n
    apply ContinuousMap.ext; intro x
    exact (H.levelPath n x).symm.target

/-- Concatenate two actual strict homotopies, using the continuous family
of concatenated paths and the same scalar cut at every spectrum level. -/
noncomputable def trans (H : StrictHomotopy f g) (K : StrictHomotopy g k) : StrictHomotopy f k where
  hom :=
    { level n :=
        { toFun x := ((H.levelPath n x).trans (K.levelPath n x)).toContinuousMap
          continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _
            (Path.trans_continuous_family (H.levelPath n)
              (((show C(X.level n,C(I,Y.level n)) from H.hom.level n).continuous.comp
                continuous_fst).eval continuous_snd)
              (K.levelPath n)
              (((show C(X.level n,C(I,Y.level n)) from K.hom.level n).continuous.comp
                continuous_fst).eval continuous_snd)) }
      point n := by
        apply ContinuousMap.ext; intro s
        change ((H.levelPath n (X.level n).point).trans (K.levelPath n (X.level n).point)) s =
          (Y.level n).point
        rw [Path.trans_apply]
        split_ifs
        · exact congrArg (fun q : C(I,Y.level n) => q _) (H.hom.point n)
        · exact congrArg (fun q : C(I,Y.level n) => q _) (K.hom.point n)
      bond n x t := by
        apply ContinuousMap.ext; intro s
        change ((H.levelPath (n+1) (X.bond n (x,t))).trans
          (K.levelPath (n+1) (X.bond n (x,t)))) s =
            Y.bond n (((H.levelPath n x).trans (K.levelPath n x)) s,t)
        rw [Path.trans_apply,Path.trans_apply]
        split_ifs
        · exact congrArg (fun q : C(I,Y.level (n+1)) => q _) (H.hom.bond n x t)
        · exact congrArg (fun q : C(I,Y.level (n+1)) => q _) (K.hom.bond n x t) }
  zero := by
    apply Hom.ext; funext n
    apply ContinuousMap.ext; intro x
    exact ((H.levelPath n x).trans (K.levelPath n x)).source
  one := by
    apply Hom.ext; funext n
    apply ContinuousMap.ext; intro x
    exact ((H.levelPath n x).trans (K.levelPath n x)).target

/-- Strict precomposition preserves the displayed homotopy. -/
def precomp {A : Prespectrum.{u}} (a : A ⟶ X) (H : StrictHomotopy f g) :
    StrictHomotopy (a ≫ f) (a ≫ g) where
  hom := a ≫ H.hom
  zero := by rw [Category.assoc,H.zero]
  one := by rw [Category.assoc,H.one]

/-- Strict postcomposition preserves the displayed homotopy. -/
def postcomp (H : StrictHomotopy f g) (b : Y ⟶ Z) : StrictHomotopy (f ≫ b) (g ≫ b) where
  hom := H.hom ≫ pathMap b
  zero := by rw [Category.assoc,pathMap_evaluation,← Category.assoc,H.zero]
  one := by rw [Category.assoc,pathMap_evaluation,← Category.assoc,H.one]

end StrictHomotopy
end KIP126.StableHomotopy.Implementation.Prespectrum
