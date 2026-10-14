module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Homotopy.Connectivity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- When every transition is bijective in a fixed stable degree, every
specified stage inclusion into the actual Milnor colimit is bijective there. -/
theorem sourceHomotopyColimitInclusion_stableHomotopy_bijective
    (F : ℕ ⥤ SourceCategory.{u}) (d : ℤ)
    (hF : ∀ n, Function.Bijective ((sourceStableHomotopyAddFunctor d).map
      (F.map (homOfLE (Nat.le_succ n))))) (n : ℕ) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map
      (sourceHomotopyColimitInclusion F n)) := by
  let G := sourceStableHomotopyAddFunctor d
  have hmap (a b : ℕ) (hab : a ≤ b) :
      Function.Bijective (G.map (F.map (homOfLE hab))) := by
    induction b, hab using Nat.le_induction with
    | base =>
      have he : homOfLE (le_refl a) = 𝟙 a := Subsingleton.elim _ _
      rw [he, F.map_id, G.map_id]
      exact Function.bijective_id
    | succ b hab ih =>
      have he : homOfLE (Nat.le_succ_of_le hab) =
          homOfLE hab ≫ homOfLE (Nat.le_succ b) := Subsingleton.elim _ _
      rw [he, F.map_comp, G.map_comp]
      exact (hF b).comp ih
  have hz (x : G.obj (F.obj n))
      (hx : G.map (sourceHomotopyColimitInclusion F n) x = 0) : x = 0 := by
    obtain ⟨m, hm, hx⟩ := (sourceHomotopyColimit_stableHomotopy_eq_zero_iff F d n x).mp hx
    exact (hmap n m hm).1 (hx.trans (map_zero _).symm)
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, hxy, sub_self]
  · intro x
    obtain ⟨m, y, rfl⟩ := sourceHomotopyColimit_stableHomotopy_exists_rep F d x
    let k := max n m
    obtain ⟨z, hz⟩ := (hmap n k (Nat.le_max_left n m)).2
      (G.map (F.map (homOfLE (Nat.le_max_right n m))) y)
    refine ⟨z, ?_⟩
    have hn := ConcreteCategory.congr_hom
      ((G.mapCocone (sourceHomotopyColimitCocone F)).w
        (homOfLE (Nat.le_max_left n m))) z
    have hm := ConcreteCategory.congr_hom
      ((G.mapCocone (sourceHomotopyColimitCocone F)).w
        (homOfLE (Nat.le_max_right n m))) y
    change G.map (sourceHomotopyColimitInclusion F k)
      (G.map (F.map (homOfLE (Nat.le_max_left n m))) z) =
        G.map (sourceHomotopyColimitInclusion F n) z at hn
    change G.map (sourceHomotopyColimitInclusion F k)
      (G.map (F.map (homOfLE (Nat.le_max_right n m))) y) =
        G.map (sourceHomotopyColimitInclusion F m) y at hm
    exact hn.symm.trans ((congrArg (G.map (sourceHomotopyColimitInclusion F k)) hz).trans hm)

end KIP126.StableHomotopy.Implementation
