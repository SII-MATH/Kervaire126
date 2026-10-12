module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Operation.Data

@[expose] public section

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
