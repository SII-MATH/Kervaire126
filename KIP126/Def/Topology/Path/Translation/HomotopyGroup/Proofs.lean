module

public import KIP126.Def.Topology.Path.Translation.Equivalence.Data
public import KIP126.Def.Topology.HomotopyGroup.Basepoint.HomotopyEquiv.Proofs

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u v w
set_option backward.isDefEq.respectTransparency false

theorem continuousHomotopyMap_comp_bijective {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X,Y)) (g : C(Y,Z)) (x : X) (n : ℕ)
    (hf : Function.Bijective (continuousHomotopyMap f x (f x) rfl n))
    (hg : Function.Bijective (continuousHomotopyMap g (f x) (g (f x)) rfl n)) :
    Function.Bijective (continuousHomotopyMap (g.comp f) x ((g.comp f) x) rfl n) := by
  change Function.Bijective (continuousHomotopyMap (g.comp f) x (g (f x)) rfl n)
  have e : continuousHomotopyMap (g.comp f) x (g (f x)) rfl n =
      continuousHomotopyMap g (f x) (g (f x)) rfl n ∘ continuousHomotopyMap f x (f x) rfl n :=
    funext (continuousHomotopyMap_comp f g x n)
  rw [e]
  exact hg.comp hf

theorem continuousHomotopyMap_bijective_of_comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X,Y)) (g : C(Y,Z)) (x : X) (n : ℕ)
    (hf : Function.Bijective (continuousHomotopyMap f x (f x) rfl n))
    (hc : Function.Bijective (continuousHomotopyMap (g.comp f) x ((g.comp f) x) rfl n)) :
    Function.Bijective (continuousHomotopyMap g (f x) (g (f x)) rfl n) := by
  apply (Function.Bijective.of_comp_iff _ hf).mp
  have e : continuousHomotopyMap (g.comp f) x (g (f x)) rfl n =
      continuousHomotopyMap g (f x) (g (f x)) rfl n ∘ continuousHomotopyMap f x (f x) rfl n :=
    funext (continuousHomotopyMap_comp f g x n)
  rw [← e]
  exact hc

/-- For the actual map of loop spaces, bijectivity at the constant loop
propagates to every loop as basepoint. The proof uses actual translations,
their homotopy inverses, and the specified unit path. -/
theorem continuousLoopMap_homotopy_bijective_at_all_points
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (a : X) (n : ℕ)
    (h : Function.Bijective (continuousHomotopyMap (continuousLoopMap f a)
      (Path.refl a) ((continuousLoopMap f a) (Path.refl a)) rfl n)) (p : Path a a) :
    Function.Bijective (continuousHomotopyMap (continuousLoopMap f a) p
      ((continuousLoopMap f a) p) rfl n) := by
  let F := continuousLoopMap f a
  have hleft : Function.Bijective (continuousHomotopyMap (loopLeftTranslate p)
      (Path.refl a) ((loopLeftTranslate p) (Path.refl a)) rfl n) :=
    homotopyEquiv_continuousHomotopyMap_bijective (loopLeftTranslateHomotopyEquiv p) (Path.refl a) n
  have hright : Function.Bijective (continuousHomotopyMap (loopLeftTranslate (p.map f.continuous))
      (F (Path.refl a)) ((loopLeftTranslate (p.map f.continuous)) (F (Path.refl a))) rfl n) :=
    homotopyEquiv_continuousHomotopyMap_bijective
      (loopLeftTranslateHomotopyEquiv (p.map f.continuous)) (F (Path.refl a)) n
  have hc : Function.Bijective (continuousHomotopyMap (F.comp (loopLeftTranslate p))
      (Path.refl a) ((F.comp (loopLeftTranslate p)) (Path.refl a)) rfl n) := by
    change Function.Bijective (continuousHomotopyMap ((continuousLoopMap f a).comp (loopLeftTranslate p))
      (Path.refl a) (((continuousLoopMap f a).comp (loopLeftTranslate p)) (Path.refl a)) rfl n)
    rw [continuousLoopMap_translate f p]
    exact continuousHomotopyMap_comp_bijective F (loopLeftTranslate (p.map f.continuous))
      (Path.refl a) n h hright
  have hp := continuousHomotopyMap_bijective_of_comp (loopLeftTranslate p) F (Path.refl a) n hleft hc
  let γ : Path ((loopLeftTranslate p) (Path.refl a)) p := {
    toFun t := Path.delayReflRight t p
    continuous_toFun := Path.continuous_delayReflRight.comp (continuous_id.prodMk continuous_const)
    source' := Path.delayReflRight_zero p
    target' := Path.delayReflRight_one p }
  exact continuousHomotopyMap_bijective_of_path F γ n hp

end KIP126.Topology
