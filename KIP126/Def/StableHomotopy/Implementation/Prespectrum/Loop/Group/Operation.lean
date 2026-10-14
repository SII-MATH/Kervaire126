module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Data

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- Actual pointwise concatenation of two strict maps into a loop prespectrum. -/
noncomputable def loopAdd {A X : Prespectrum.{u}} (f g : A ⟶ Prespectrum.loop X) :
    A ⟶ Prespectrum.loop X where
  level n := ⟨fun x => (f.level n x).trans (g.level n x),
    (f.level n).continuous.path_trans (g.level n).continuous⟩
  point n := by change (f.level n _).trans (g.level n _) = _; rw [f.point,g.point]; exact Path.refl_trans_refl
  bond n x t := by
    apply Path.ext
    funext s
    change ((f.level (n+1) (A.bond n (x,t))).trans (g.level (n+1) (A.bond n (x,t)))) s = _
    rw [f.bond,g.bond]
    change (loopBond X n (f.level n x,t) |>.trans (loopBond X n (g.level n x,t))) s =
      X.bond n (((f.level n x).trans (g.level n x)) s,t)
    simp only [Path.trans_apply]
    split_ifs <;> rfl

/-- Path reversal on the actual loop prespectrum. -/
def loopInverse (X : Prespectrum.{u}) : Prespectrum.loop X ⟶ Prespectrum.loop X where
  level _ := ⟨Path.symm,Path.continuous_symm⟩
  point _ := rfl
  bond _ _ _ := by apply Path.ext; rfl

/-- Internal multiplication with the fixed actual twofold product. -/
noncomputable def loopConcat (X : Prespectrum.{u}) :
    piPrespectrum (fun _ : Fin 2 => Prespectrum.loop X) ⟶ Prespectrum.loop X :=
  loopAdd (piProjection _ 0) (piProjection _ 1)

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u

@[simp] theorem loopAdd_precomp {A B X : Prespectrum.{u}} (a : A ⟶ B)
    (f g : B ⟶ Prespectrum.loop X) : a ≫ loopAdd f g = loopAdd (a ≫ f) (a ≫ g) := rfl

@[simp] theorem loopAdd_postcomp {A X Y : Prespectrum.{u}}
    (f g : A ⟶ Prespectrum.loop X) (b : X ⟶ Y) :
    loopAdd f g ≫ loopMap b = loopAdd (f ≫ loopMap b) (g ≫ loopMap b) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change b.level n (((f.level n x).trans (g.level n x)) s) =
    ((loopMap b).level n (f.level n x) |>.trans ((loopMap b).level n (g.level n x))) s
  simp only [Path.trans_apply]
  split_ifs <;> rfl

@[simp] theorem loopInverse_natural {X Y : Prespectrum.{u}} (b : X ⟶ Y) :
    loopInverse X ≫ loopMap b = loopMap b ≫ loopInverse Y := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  rfl

theorem loopConcat_natural {X Y : Prespectrum.{u}} (b : X ⟶ Y) :
    loopConcat X ≫ loopMap b = piMap (fun _ : Fin 2 => loopMap b) ≫ loopConcat Y := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change b.level n (((x 0).trans (x 1)) s) =
    ((loopMap b).level n (x 0) |>.trans ((loopMap b).level n (x 1))) s
  simp only [Path.trans_apply]
  split_ifs <;> rfl

@[simp] theorem loopConcat_lift {A X : Prespectrum.{u}}
    (f g : A ⟶ Prespectrum.loop X) :
    piLift (Fin.cases f (fun _ : Fin 1 => g)) ≫ loopConcat X = loopAdd f g := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum

end
