import KIP126.Def.SpectralSequence.Computation.Proofs
import KIP126.Def.SpectralSequence.Basic.Category.Proofs

/-!
# Naturality of common representatives and differential equations

All maps here are the quotient maps induced by the ambient tower morphism.
No injectivity is assumed, so these results deliberately make no assertion
that a nonzero class stays nonzero.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A common cycle representative maps to a common cycle representative. -/
theorem SpectralSequenceMorphism.representsOnPage
    {E E' : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
    (f : SpectralSequenceMorphism E E') {r : ℤ} {p : ℤ × ℤ}
    {x : E.Page 2 p} {y : E.Page r p} (h : RepresentsOnPage E r p x y) :
    RepresentsOnPage E' r p (f.pageMap 2 p x) (f.pageMap r p y) := by
  rcases E with ⟨⟨r₀, D, δ, d⟩, dd, Zs, Bs⟩
  rcases E' with ⟨⟨r₀', D', δ', d'⟩, dd', Zs', Bs'⟩
  have hr₀ := f.r₀_eq
  dsimp at hr₀
  subst r₀'
  obtain ⟨hr, z, hx, hy⟩ := h
  let n : WithTop ℕ := ↑(2 - r₀).toNat
  let m : WithTop ℕ := ↑(r - r₀).toNat
  have hnm : n ≤ m := by
    dsimp [n, m]
    exact_mod_cast (show (2 - r₀).toNat ≤ (r - r₀).toNat by omega)
  let F := f.toSSDataMorphism
  refine ⟨hr, F.cycleMap p m z, ?_, ?_⟩
  · have hs := F.cycleMap_ofLE_assoc p hnm ((D' p).pageπ n)
    have hp := F.pageπ_pageMap p n
    have heq :
        (Subobject.ofLE ((D p).Z m) ((D p).Z n) ((D p).Z_anti hnm) ≫
          (D p).pageπ n) ≫ F.pageMap p n =
        F.cycleMap p m ≫
          Subobject.ofLE ((D' p).Z m) ((D' p).Z n) ((D' p).Z_anti hnm) ≫
            (D' p).pageπ n := by
      rw [Category.assoc, hp]
      exact hs
    have hz := congrArg (fun a => a z) heq
    simpa only [ModuleCat.comp_apply, hx, SpectralSequenceMorphism.pageMap,
      PreSSMorphism.pageMap, SSDataMorphism.pageMapAt, eqToHom_refl,
      Category.comp_id, F, n, m,
      SpectralSequenceMorphism.toPreSSMorphism] using hz.symm
  · have hz := congrArg (fun a => a z) (F.pageπ_pageMap p m)
    simpa only [ModuleCat.comp_apply, hy, SpectralSequenceMorphism.pageMap,
      PreSSMorphism.pageMap, SSDataMorphism.pageMapAt, eqToHom_refl,
      Category.comp_id, F, n, m,
      SpectralSequenceMorphism.toPreSSMorphism] using hz.symm

/-- Differential equations between named E₂ representatives are natural.
The image equation can have zero source or target. -/
theorem SpectralSequenceMorphism.hasDifferential
    {E E' : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
    (f : SpectralSequenceMorphism E E') {r : ℤ} {p q : ℤ × ℤ}
    {x : E.Page 2 p} {y : E.Page 2 q} (h : HasDifferential E r p q x y) :
    HasDifferential E' r p q (f.pageMap 2 p x) (f.pageMap 2 q y) := by
  obtain ⟨hdeg, xr, yr, hx, hy, hd⟩ := h
  have hdeg' : p + E'.diffDeg r = q := by rw [← f.diffDeg_eq]; exact hdeg
  refine ⟨hdeg', f.pageMap r p xr, f.pageMap r q yr,
    f.representsOnPage hx, f.representsOnPage hy, ?_⟩
  have heq : f.pageMap r p ≫ E'.d r p ≫ eqToHom (congrArg (E'.Page r) hdeg') =
      (E.d r p ≫ eqToHom (congrArg (E.Page r) hdeg)) ≫ f.pageMap r q := by
    rw [← Category.assoc, f.pageMap_comm_d, Category.assoc]
    subst q
    simp
  have hz := congrArg (fun a => a xr) heq
  simpa only [ModuleCat.comp_apply, hd] using hz

end KIP126.Core.SpectralSequence
