module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Heart.Product.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Shift.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Postnikov.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Layer.Scalar.Cofiber.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- The actual single-degree exponent-two objects in every integer
degree are local, conditional on the original Moore-heart comparison. -/
theorem sourceIsHF2Local_of_exponent_two_singleDegree
    [IsIso sourceModTwoMooreHeartToHF2]
    (X : SourceCategory.{0}) (n : ℤ)
    (hX : ∀ d : ℤ, d ≠ n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hX₂ : ∀ x : (sourceStableHomotopyAddFunctor n).obj X, 2 • x = 0) :
    SourceIsHF2Local X := by
  have hid : 2 • 𝟙 X = 0 :=
    source_nsmul_id_eq_zero_of_homotopy_nsmul_eq_zero X n 2 hX hX₂
  let Y := X⟦-n⟧
  have hY : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y) := by
    intro d hd
    let e := sourceStableHomotopyShiftEquiv X d (-n)
    exact ⟨fun x y => e.symm.injective ((hX (d - -n) (by omega)).elim _ _)⟩
  have hY₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0 := by
    intro y
    have h := congrArg (fun f : X ⟶ X =>
      (sourceStableHomotopyAddFunctor 0).map (f⟦-n⟧') y) hid
    simp only [Functor.map_nsmul,CategoryTheory.Functor.map_id,Functor.map_zero] at h
    exact h
  have hl : SourceIsHF2Local Y := sourceIsHF2Local_of_exponent_two_heart Y hY hY₂
  exact @SourceIsHF2Local.of_iso _ _
    ((shiftFunctorCompIsoId SourceCategory (-n) n (by omega)).app X).symm
    (@SourceIsHF2Local.shift Y @hl n)

/-- The original mod-two scalar cofiber of any single-degree object is
local: its two possible actual Postnikov layers both have exponent two. -/
theorem sourceCofiber_two_isHF2Local_of_singleDegree
    [IsIso sourceModTwoMooreHeartToHF2]
    (X : SourceCategory.{0}) (n : ℤ)
    (hX : ∀ d : ℤ, d ≠ n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X)) :
    SourceIsHF2Local (HasFunctorialCofiber.cofib (2 • 𝟙 X)) := by
  let Z := HasFunctorialCofiber.cofib (2 • 𝟙 X)
  apply sourceIsHF2Local_of_boundedBelow_layers Z n
    (fun d hd => sourceCofiber_nsmul_homotopy_subsingleton_of_singleDegree X n 2 hX d
      (by omega) (by omega))
  intro d _
  apply sourceIsHF2Local_of_exponent_two_singleDegree (sourcePostnikovLayer Z d) d
    (sourcePostnikovLayer_homotopy_subsingleton Z d)
  intro x
  have h := congrArg (fun f : sourcePostnikovLayer Z d ⟶ sourcePostnikovLayer Z d =>
    (sourceStableHomotopyAddFunctor d).map f x)
    (sourceCofiber_nsmul_postnikovLayer_nsmul_id_eq_zero X n 2 hX d)
  rw [Functor.map_nsmul,CategoryTheory.Functor.map_id,Functor.map_zero] at h
  exact h

/-- Every actual single-degree object killed by a finite power of two is
local under the original coefficient comparison. The scalar-cofiber
argument does not assume a splitting of its stable group. -/
theorem sourceIsHF2Local_of_two_power_singleDegree
    [IsIso sourceModTwoMooreHeartToHF2]
    (X : SourceCategory.{0}) (n : ℤ)
    (hX : ∀ d : ℤ, d ≠ n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (k : ℕ) (hk : 2^k • 𝟙 X = 0) : SourceIsHF2Local X :=
  @sourceIsHF2Local_of_nsmul_nilpotent X 2 k hk
    (@sourceCofiber_two_isHF2Local_of_singleDegree _ X n hX)

/-- Bounded-below objects whose original stable groups each have a finite
power-of-two annihilator are local. The exponent can vary with the degree. -/
theorem sourceIsHF2Local_of_boundedBelow_two_power_homotopy
    [IsIso sourceModTwoMooreHeartToHF2]
    (X : SourceCategory.{0}) (N : ℤ)
    (hX : ∀ d : ℤ, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (h₂ : ∀ d : ℤ, N ≤ d → ∃ k : ℕ,
      ∀ x : (sourceStableHomotopyAddFunctor d).obj X, 2^k • x = 0) : SourceIsHF2Local X := by
  apply sourceIsHF2Local_of_boundedBelow_layers X N hX
  intro d hd
  obtain ⟨k,hk⟩ := h₂ d hd
  exact @sourceIsHF2Local_of_two_power_singleDegree _ (sourcePostnikovLayer X d) d
    (sourcePostnikovLayer_homotopy_subsingleton X d) k
    (sourcePostnikovLayer_nsmul_id_eq_zero_of_homotopy X d (2^k) hk)

end KIP126.StableHomotopy.Implementation
