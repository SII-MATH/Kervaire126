module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Map.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Map.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Colimit.Universal.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

@[simp] theorem diagonalGridStableMap_mk (X : Prespectrum.{0}) {Y Z : Prespectrum.{0}}
    (f : Y ⟶ Z) (d : ℤ) (a : DiagonalGridClass X Y d) :
    diagonalGridStableMap X f d (Quot.mk _ a) = Quot.mk _ (a.mapRight f) := rfl

/-- The actual grid map and the original stable map of every row
commute with that row's specified inclusion into the grid quotient. -/
theorem diagonalGridRowInclusion_natural_right (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ) (n : ℕ)
    (a : StableHomotopy (spaceSmash (X.level n) Y) (d+n)) :
    diagonalGridStableMap X f d (diagonalGridRowInclusion X Y d n a) =
      diagonalGridRowInclusion X Z d n
        (stableHomotopyMap (spaceSmashMap (𝟙 (X.level n)) f) (d+n) a) := by
  induction a using Quot.inductionOn with
  | h a => exact congrArg (Quot.mk _) (diagonalGridClassOfRowRepresentative_mapRight X f d n a)

/-- Bijectivity on every original stable row implies bijectivity of
the actual grid map, by the proved universal property of its row cocone. -/
theorem diagonalGridStableMap_bijective_of_rows (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ)
    (hf : ∀ n, Function.Bijective
      (stableHomotopyMap (spaceSmashMap (𝟙 (X.level n)) f) (d+n))) :
    Function.Bijective (diagonalGridStableMap X f d) := by
  let α := diagonalGridRowMap X f d
  haveI (n : ℕ) : IsIso (α.app n) :=
    (CategoryTheory.isIso_iff_bijective _).mpr (hf n)
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  let c := (Cocone.precompose α).obj (diagonalGridRowCocone X Z d)
  have hc : IsColimit c := (IsColimit.precomposeHomEquiv (asIso α) _).symm
    (diagonalGridRowCocone_isColimit X Z d)
  let h := diagonalGridRowCocone_isColimit X Y d
  haveI : IsIso (h.desc c) := (h.nonempty_isColimit_iff_isIso_desc).mp ⟨hc⟩
  have he : h.desc c = TypeCat.ofHom (diagonalGridStableMap X f d) := by
    apply h.hom_ext
    intro n
    rw [h.fac]
    ext a
    exact (diagonalGridRowInclusion_natural_right X f d n a).symm
  rw [he] at this
  exact (CategoryTheory.isIso_iff_bijective _).mp this

@[simp] theorem diagonalGridDiagonalStableMap_mk (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ)
    (a : DiagonalGridDiagonalClass X Y d) :
    diagonalGridDiagonalStableMap X f d (Quot.mk _ a) =
      Quot.mk _ (a.mapRight f) := rfl

/-- The explicit equal-stage cofinal equivalence is natural for the
original right-spectrum map. -/
theorem diagonalGridStableDiagonalEquiv_natural_right (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ) (a : DiagonalGridStable X Y d) :
    diagonalGridStableDiagonalEquiv X Z d (diagonalGridStableMap X f d a) =
      diagonalGridDiagonalStableMap X f d (diagonalGridStableDiagonalEquiv X Y d a) := by
  induction a using Quot.inductionOn with
  | h a =>
      exact congrArg (Quot.mk _) (a.mapRight_toDiagonal f).symm

/-- Each original stable row being bijective also gives bijectivity
on the equal-stage quotient by the actual natural cofinal comparison. -/
theorem diagonalGridDiagonalStableMap_bijective_of_rows (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ)
    (hf : ∀ n, Function.Bijective
      (stableHomotopyMap (spaceSmashMap (𝟙 (X.level n)) f) (d+n))) :
    Function.Bijective (diagonalGridDiagonalStableMap X f d) := by
  have h : diagonalGridDiagonalStableMap X f d =
      diagonalGridStableDiagonalEquiv X Z d ∘ diagonalGridStableMap X f d ∘
        (diagonalGridStableDiagonalEquiv X Y d).symm := by
    funext a
    rw [Function.comp_apply,Function.comp_apply,
      diagonalGridStableDiagonalEquiv_natural_right,Equiv.apply_symm_apply]
  rw [h]
  exact (diagonalGridStableDiagonalEquiv X Z d).bijective.comp
    ((diagonalGridStableMap_bijective_of_rows X f d hf).comp
      (diagonalGridStableDiagonalEquiv X Y d).symm.bijective)

end KIP126.StableHomotopy.Implementation.Prespectrum
