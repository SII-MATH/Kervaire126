module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Homotopy.Connectivity.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Conservativity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- If the stage maps to a target are eventually bijective in one degree,
the map from the actual homotopy colimit is bijective in that degree. -/
theorem sourceHomotopyColimit_stableHomotopy_bijective_of_eventually
    (F : ℕ ⥤ SourceCategory.{u}) {Y : SourceCategory.{u}}
    (b : sourceHomotopyColimit F ⟶ Y) (d : ℤ) (N : ℕ)
    (hN : ∀ n, N ≤ n → Function.Bijective
      ((sourceStableHomotopyAddFunctor d).map (sourceHomotopyColimitInclusion F n ≫ b))) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map b) := by
  let G := sourceStableHomotopyAddFunctor d
  have hz (x : G.obj (sourceHomotopyColimit F)) (hx : G.map b x = 0) : x = 0 := by
    obtain ⟨n, y, rfl⟩ := sourceHomotopyColimit_stableHomotopy_exists_rep F d x
    let m := max n N
    let f : n ⟶ m := homOfLE (Nat.le_max_left n N)
    have hc : F.map f ≫ sourceHomotopyColimitInclusion F m =
        sourceHomotopyColimitInclusion F n := (sourceHomotopyColimitCocone F).w f
    have he : G.map (F.map f) ≫ G.map (sourceHomotopyColimitInclusion F m ≫ b) =
        G.map (sourceHomotopyColimitInclusion F n ≫ b) := by
      rw [← G.map_comp, ← Category.assoc, hc]
    have hy : G.map (sourceHomotopyColimitInclusion F m ≫ b) (G.map (F.map f) y) = 0 := by
      change (G.map (F.map f) ≫ G.map (sourceHomotopyColimitInclusion F m ≫ b)) y = 0
      rw [he, G.map_comp]
      exact hx
    have hy0 : G.map (F.map f) y = 0 :=
      (hN m (Nat.le_max_right n N)).1 (hy.trans (map_zero _).symm)
    apply (sourceHomotopyColimit_stableHomotopy_eq_zero_iff F d n y).mpr
    exact ⟨m, Nat.le_max_left n N, hy0⟩
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, hxy, sub_self]
  · intro y
    obtain ⟨x, hx⟩ := (hN N le_rfl).2 y
    refine ⟨G.map (sourceHomotopyColimitInclusion F N) x, ?_⟩
    change (G.map (sourceHomotopyColimitInclusion F N) ≫ G.map b) x = y
    rw [← G.map_comp]
    exact hx

/-- Degreewise eventual stabilization of the specified stage maps detects
an actual source isomorphism from the constructed homotopy colimit.
The stabilization index may depend on the degree. -/
theorem sourceHomotopyColimit_isIso_of_eventually_bijective
    (F : ℕ ⥤ SourceCategory.{u}) {Y : SourceCategory.{u}}
    (b : sourceHomotopyColimit F ⟶ Y)
    (hb : ∀ d : ℤ, ∃ N : ℕ, ∀ n, N ≤ n → Function.Bijective
      ((sourceStableHomotopyAddFunctor d).map (sourceHomotopyColimitInclusion F n ≫ b))) :
    IsIso b := by
  apply (source_isIso_iff_stableHomotopy_bijective b).mpr
  intro d
  obtain ⟨N, hN⟩ := hb d
  rw [← sourceStableHomotopyAddFunctor_forget_map]
  exact sourceHomotopyColimit_stableHomotopy_bijective_of_eventually F b d N hN

/-- A compatible family that eventually induces isomorphisms in every
stable degree extends to an actual isomorphism from the specified Milnor
homotopy colimit, retaining all of the given stage maps. -/
theorem sourceHomotopyColimit_exists_isIso_of_eventually_bijective
    (F : ℕ ⥤ SourceCategory.{u}) {Y : SourceCategory.{u}}
    (a : ∀ n, F.obj n ⟶ Y)
    (ha : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ a (n+1) = a n)
    (hπ : ∀ d : ℤ, ∃ N : ℕ, ∀ n, N ≤ n →
      Function.Bijective ((sourceStableHomotopyAddFunctor d).map (a n))) :
    ∃ b : sourceHomotopyColimit F ⟶ Y,
      (∀ n, sourceHomotopyColimitInclusion F n ≫ b = a n) ∧ IsIso b := by
  obtain ⟨b, hb⟩ := sourceHomotopyColimit_exists_desc F a ha
  refine ⟨b, hb, sourceHomotopyColimit_isIso_of_eventually_bijective F b ?_⟩
  intro d
  simpa only [hb] using hπ d

end KIP126.StableHomotopy.Implementation
