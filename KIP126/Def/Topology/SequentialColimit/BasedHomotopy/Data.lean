module

public import KIP126.Def.Topology.SequentialColimit.Compact.Proofs
public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

variable (F : ℕ ⥤ TopCat.{u}) (x₀ : F.obj 0)

/-- The basepoint in a sequential stage is the actual image of the initial point. -/
def natColimitStagePoint (n : ℕ) : F.obj n := F.map (homOfLE (Nat.zero_le n)) x₀

/-- The actual transition on based cubical loops in the sequential diagram. -/
def natColimitLoopTransition {n m : ℕ} (h : n ≤ m) (r : ℕ)
    (p : GenLoop (Fin r) (F.obj n) (natColimitStagePoint F x₀ n)) :
    GenLoop (Fin r) (F.obj m) (natColimitStagePoint F x₀ m) :=
  ⟨(F.map (homOfLE h)).hom.comp p.val, fun t ht => by
    change F.map (homOfLE h) (p t) = natColimitStagePoint F x₀ m
    exact (congrArg (fun x : F.obj n => F.map (homOfLE h) x) (p.property t ht)).trans
      (ConcreteCategory.congr_hom
        (F.map_comp (homOfLE (Nat.zero_le n)) (homOfLE h)) x₀).symm⟩

/-- The actual map of cubical loops into the actual colimit. -/
def natColimitLoopInclusion (c : Cocone F) (n r : ℕ)
    (p : GenLoop (Fin r) (F.obj n) (natColimitStagePoint F x₀ n)) :
    GenLoop (Fin r) c.pt (c.ι.app 0 x₀) :=
  ⟨(c.ι.app n).hom.comp p.val, fun t ht => by
    change c.ι.app n (p t) = c.ι.app 0 x₀
    exact (congrArg (fun x : F.obj n => c.ι.app n x) (p.property t ht)).trans
      (ConcreteCategory.congr_hom (c.w (homOfLE (Nat.zero_le n))) x₀)⟩

/-- The original cubical homotopy quotients form an actual sequential diagram. -/
def natColimitHomotopyDiagram (r : ℕ) : ℕ ⥤ Type u where
  obj n := _root_.HomotopyGroup (Fin r) (F.obj n) (natColimitStagePoint F x₀ n)
  map h := TypeCat.ofHom (Quotient.map (natColimitLoopTransition F x₀ (leOfHom h) r)
    (fun _ _ hp => hp.comp_continuousMap (F.map h).hom))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro p
    induction p using Quotient.inductionOn with
    | h p =>
        apply congrArg Quotient.mk''
        apply GenLoop.ext
        intro t
        exact ConcreteCategory.congr_hom (F.map_id n) (p t)
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro p
    induction p using Quotient.inductionOn with
    | h p =>
        apply congrArg Quotient.mk''
        apply GenLoop.ext
        intro t
        exact ConcreteCategory.congr_hom (F.map_comp h k) (p t)

/-- The actual colimit inclusions induce the displayed cocone on cubical homotopy sets. -/
def natColimitHomotopyCocone (c : Cocone F) (r : ℕ) :
    Cocone (natColimitHomotopyDiagram F x₀ r) where
  pt := _root_.HomotopyGroup (Fin r) c.pt (c.ι.app 0 x₀)
  ι :=
    { app := fun n => TypeCat.ofHom (Quotient.map (natColimitLoopInclusion F x₀ c n r)
        (fun _ _ hp => hp.comp_continuousMap (c.ι.app n).hom))
      naturality := fun n m h => by
        apply ConcreteCategory.hom_ext
        intro p
        induction p using Quotient.inductionOn with
        | h p =>
            apply congrArg Quotient.mk''
            apply GenLoop.ext
            intro t
            exact ConcreteCategory.congr_hom (c.w h) (p t) }

end KIP126.Topology
