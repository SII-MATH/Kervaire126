module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Pullback.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

@[simp, reassoc] theorem pullbackFst_comp {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) : pullbackFst f g ≫ f = pullbackSnd f g ≫ g :=
  (pullbackPrespectrumCone f g).condition

@[simp, reassoc] theorem pullbackLift_fst {A X Y Z : Prespectrum.{u}}
    {f : X ⟶ Y} {g : Z ⟶ Y} (a : A ⟶ X) (b : A ⟶ Z) (h : a ≫ f = b ≫ g) :
    pullbackLift a b h ≫ pullbackFst f g = a := rfl

@[simp, reassoc] theorem pullbackLift_snd {A X Y Z : Prespectrum.{u}}
    {f : X ⟶ Y} {g : Z ⟶ Y} (a : A ⟶ X) (b : A ⟶ Z) (h : a ≫ f = b ≫ g) :
    pullbackLift a b h ≫ pullbackSnd f g = b := rfl

/-- The two actual projections detect equality of strict maps. -/
theorem pullbackHom_ext {A X Y Z : Prespectrum.{u}} {f : X ⟶ Y} {g : Z ⟶ Y}
    (a b : A ⟶ pullbackPrespectrum f g)
    (h₁ : a ≫ pullbackFst f g = b ≫ pullbackFst f g)
    (h₂ : a ≫ pullbackSnd f g = b ≫ pullbackSnd f g) : a = b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact Prod.ext (congrArg (fun k : A ⟶ X => k.level n x) h₁)
    (congrArg (fun k : A ⟶ Z => k.level n x) h₂)

/-- The actual pointwise cone satisfies the strict categorical pullback
universal property before localization. -/
def pullbackPrespectrumCone_isLimit {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsLimit (pullbackPrespectrumCone f g) :=
  PullbackCone.IsLimit.mk _ (fun s => pullbackLift s.fst s.snd s.condition)
    (fun _ => rfl) (fun _ => rfl) (fun s m h₁ h₂ =>
      pullbackHom_ext m (pullbackLift s.fst s.snd s.condition) h₁ h₂)

instance prespectrumHasPullbacks : HasPullbacks Prespectrum.{u} := by
  letI : ∀ {X Y Z : Prespectrum.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) :=
    fun {X Y Z f g} => ⟨⟨pullbackPrespectrumCone f g, pullbackPrespectrumCone_isLimit f g⟩⟩
  exact hasPullbacks_of_hasLimit_cospan Prespectrum

end KIP126.StableHomotopy.Implementation.Prespectrum
