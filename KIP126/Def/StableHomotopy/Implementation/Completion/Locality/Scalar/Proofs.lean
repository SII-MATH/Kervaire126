module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Triangle.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Cofiber.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- Actual retracts of original HF2-local source objects are local. -/
theorem SourceIsHF2Local.of_retract {X Y : SourceCategory.{0}}
    (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X)
    (hY : SourceIsHF2Local Y) : SourceIsHF2Local X := by
  intro A B f hf
  constructor
  · intro a b hab
    change f ≫ a = f ≫ b at hab
    have h : a ≫ i = b ≫ i := (hY f hf).injective (by
      rw [← Category.assoc,← Category.assoc,hab])
    have h' := congrArg (fun k => k ≫ r) h
    simpa only [Category.assoc,hir,Category.comp_id] using h'
  · intro a
    obtain ⟨b,hb⟩ := (hY f hf).surjective (a ≫ i)
    change f ≫ b = a ≫ i at hb
    refine ⟨b ≫ r,?_⟩
    change f ≫ (b ≫ r) = a
    rw [← Category.assoc,hb,Category.assoc,hir,Category.comp_id]

/-- In an actual distinguished source triangle, locality of the first
and third objects implies locality of the middle object. -/
theorem SourceIsHF2Local.triangle_middle (T : Triangle SourceCategory.{0})
    (hT : T ∈ distTriang SourceCategory) (h₁ : SourceIsHF2Local T.obj₁)
    (h₃ : SourceIsHF2Local T.obj₃) : SourceIsHF2Local T.obj₂ :=
  SourceIsHF2Local.triangle_first T.rotate (rot_of_distTriang T hT) h₃ h₁.suspension

/-- Actual chosen cofibers with local objects are closed under composition
of their original maps, by the actual source octahedron. -/
theorem sourceCofiber_isHF2Local_comp {X Y Z : SourceCategory.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : SourceIsHF2Local (HasFunctorialCofiber.cofib f))
    (hg : SourceIsHF2Local (HasFunctorialCofiber.cofib g)) :
    SourceIsHF2Local (HasFunctorialCofiber.cofib (f ≫ g)) := by
  let o := Triangulated.someOctahedron rfl
    (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished g)
    (HasFunctorialCofiber.cofib_distinguished (f ≫ g))
  exact @SourceIsHF2Local.triangle_middle o.triangle o.mem @hf @hg

/-- Locality of the original scalar cofiber passes to every positive
scalar-power cofiber, with no nilpotence assumption. -/
theorem sourceCofiber_nsmul_pow_isHF2Local
    (X : SourceCategory.{0}) (p : ℕ)
    (h : SourceIsHF2Local (HasFunctorialCofiber.cofib (p • 𝟙 X))) (n : ℕ) :
    SourceIsHF2Local (HasFunctorialCofiber.cofib (p^(n+1) • 𝟙 X)) := by
  induction n with
  | zero =>
    rw [show p^(0+1) = p by exact pow_one p]
    exact @h
  | succ n ih =>
    have hc : (p^(n+1) • 𝟙 X) ≫ (p • 𝟙 X) = p^(n+1+1) • 𝟙 X := by
      rw [Preadditive.nsmul_comp,Preadditive.comp_nsmul,Category.id_comp,smul_smul,← pow_succ]
    have hh : SourceIsHF2Local (HasFunctorialCofiber.cofib ((p^(n+1) • 𝟙 X) ≫ (p • 𝟙 X))) :=
      @sourceCofiber_isHF2Local_comp X X X _ _ @ih @h
    rw [hc] at hh
    exact @hh

/-- A finite scalar-nilpotent source object is local once its original
scalar cofiber is local. The actual zero composite splits its inclusion
into a positive-power cofiber. -/
theorem sourceIsHF2Local_of_nsmul_nilpotent
    (X : SourceCategory.{0}) (p n : ℕ) (hn : p^n • 𝟙 X = 0)
    (h : SourceIsHF2Local (HasFunctorialCofiber.cofib (p • 𝟙 X))) : SourceIsHF2Local X := by
  have hn' : p^(n+1) • 𝟙 X = 0 := by
    rw [pow_succ,mul_nsmul,hn,smul_zero]
  let f := p^(n+1) • 𝟙 X
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  obtain ⟨r,hr⟩ := T.yoneda_exact₂ (HasFunctorialCofiber.cofib_distinguished f) (𝟙 X)
    (by change f ≫ 𝟙 X = 0; rw [Category.comp_id]; exact hn')
  exact @SourceIsHF2Local.of_retract X _ (HasFunctorialCofiber.cofibι f) r hr.symm
    (@sourceCofiber_nsmul_pow_isHF2Local X p @h n)

end KIP126.StableHomotopy.Implementation

