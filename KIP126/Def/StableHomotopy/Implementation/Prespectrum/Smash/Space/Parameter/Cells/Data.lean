module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Colimit
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe v
set_option backward.isDefEq.respectTransparency false

/-- The original family injections after smashing each parameter
with the same actual spectrum. -/
noncomputable def spaceSmashParameterCofan {J : Type} {A : J → BasedSpace.{0}}
    (c : Cofan A) (X : Prespectrum.{0}) : Cofan (fun j => spaceSmash (A j) X) :=
  Cofan.mk (spaceSmash c.pt X) (fun j => spaceSmashMap (c.inj j) (𝟙 X))

/-- This particular parameter-smash cofan has the actual coproduct
universal property, including arbitrary infinite cell families. -/
noncomputable def spaceSmashParameterCofan_isColimit {J : Type} {A : J → BasedSpace.{0}}
    (c : Cofan A) (hc : IsColimit c) [∀ j, UCompactlyGeneratedSpace.{0} (A j)]
    (X : Prespectrum.{0}) : IsColimit (spaceSmashParameterCofan c X) := by
  letI (j : Discrete J) : UCompactlyGeneratedSpace.{0}
      ((Discrete.functor A).obj j) := inferInstanceAs (UCompactlyGeneratedSpace.{0} (A j.as))
  exact (Cofan.isColimitMapCoconeEquiv (spaceSmashParameterFunctor X) A c)
    (spaceSmashParameter_mapCocone_isColimit (Discrete.functor A) c hc X)

/-- Smashing an actual simultaneous attachment constructs a genuine
simultaneous attachment of the smashed generators. The original
old-space arrow and all original cell indices are retained. -/
noncomputable def spaceSmashParameterAttachCells
    {α : Type v} {A B : α → BasedSpace.{0}} {g : ∀ i, A i ⟶ B i}
    [∀ i, UCompactlyGeneratedSpace.{0} (A i)]
    [∀ i, UCompactlyGeneratedSpace.{0} (B i)]
    {C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} C] {f : C ⟶ D}
    (c : AttachCells.{0} g f) (X : Prespectrum.{0}) :
    AttachCells.{0} (fun i => spaceSmashMap (g i) (𝟙 X)) (spaceSmashMap f (𝟙 X)) := by
  letI (j : Discrete c.ι) : UCompactlyGeneratedSpace.{0}
      ((Discrete.functor (fun j => A (c.π j))).obj j) :=
    inferInstanceAs (UCompactlyGeneratedSpace.{0} (A (c.π j.as)))
  letI (j : Discrete c.ι) : UCompactlyGeneratedSpace.{0}
      ((Discrete.functor (fun j => B (c.π j))).obj j) :=
    inferInstanceAs (UCompactlyGeneratedSpace.{0} (B (c.π j.as)))
  letI : UCompactlyGeneratedSpace.{0} c.cofan₁.pt :=
    BasedSpace.uCompactlyGeneratedSpace_of_isColimit _ c.cofan₁ c.isColimit₁
  letI : UCompactlyGeneratedSpace.{0} c.cofan₂.pt :=
    BasedSpace.uCompactlyGeneratedSpace_of_isColimit _ c.cofan₂ c.isColimit₂
  exact {
    ι := c.ι
    π := c.π
    cofan₁ := spaceSmashParameterCofan c.cofan₁ X
    cofan₂ := spaceSmashParameterCofan c.cofan₂ X
    isColimit₁ := spaceSmashParameterCofan_isColimit c.cofan₁ c.isColimit₁ X
    isColimit₂ := spaceSmashParameterCofan_isColimit c.cofan₂ c.isColimit₂ X
    m := spaceSmashMap c.m (𝟙 X)
    hm j := by
      change (spaceSmashParameterFunctor X).map (c.cofan₁.inj j) ≫
        (spaceSmashParameterFunctor X).map c.m =
        (spaceSmashParameterFunctor X).map (g (c.π j)) ≫
          (spaceSmashParameterFunctor X).map (c.cofan₂.inj j)
      rw [← Functor.map_comp,← Functor.map_comp,c.hm]
    g₁ := spaceSmashMap c.g₁ (𝟙 X)
    g₂ := spaceSmashMap c.g₂ (𝟙 X)
    isPushout := spaceSmashParameter_isPushout c.isPushout X }

end KIP126.StableHomotopy.Implementation.Prespectrum
