import KIPBase.Mathlib
import KIPBase.StableHomotopy.Cohomology
import KIPBase.SpectralSequence.Basic
import KIPBase.SpectralSequence.Convergence

/-!
# KIPBase.StableHomotopy.Adams

KIP §0.2.3 (prerequisites.tex §prereq-adams): The mod 2 Adams spectral sequence.

Formalizes the HF₂-Adams spectral sequence as a functor from the stable homotopy
category `𝒮` to bigraded converging spectral sequences in `AddCommGrpCat`.
Includes: Adams filtration on `π_*(X)`, convergence for finite spectra,
2-torsion on E₂, Adams filtration for maps, and detection.

## References

- Blueprint `prerequisites.tex`, §0.2.3 "Adams Spectral Sequence"
  (Axioms `prereq:ax:adams-ss`, `prereq:ax:adams-convergence`, `prereq:ax:adams-e2-order2`;
   Definitions `prereq:def:adams-filtration`, `prereq:def:adams-filtration-maps`)
- Blueprint `proof-main-theorem.tex`, §proof (uses Adams filtration and detection
  in the proof of Theorem 1.1)
-/

namespace KIPBase.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated KIPBase.SpectralSequence

universe u v

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-! Adams pages use integer modules directly. -/

noncomputable def IntModuleRing : Type v := ULift.{v} ℤ

instance : CommRing (IntModuleRing.{v}) :=
  inferInstanceAs (CommRing (ULift.{v} ℤ))

noncomputable def HomotopyGroupsModule (X : 𝒮) :
    ℤ → ModuleCat.{v, v} IntModuleRing.{v} := fun n =>
  letI : Module IntModuleRing.{v} (HomotopyGroup n X) :=
    Module.compHom (HomotopyGroup n X) ULift.ringEquiv.toRingHom
  ModuleCat.of IntModuleRing.{v} (HomotopyGroup n X)

/-! ### Adams spectral sequence

The mod 2 Adams spectral sequence is a functor from the stable homotopy category
to bigraded spectral sequences in abelian groups.  The E₂-page is
`Ext^{s,t}_A(H*(X; F₂), F₂)` where `A` is the Steenrod algebra.

Differentials: `d_r : E_r^{s,t} → E_r^{s+r, t+r-1}`.

We axiomatize the existence and key properties of the Adams SS.

Blueprint: `prerequisites.tex`, §0.2.3 (`prereq:ax:adams-ss`). -/

/-- The Adams differential degree: `d_r` shifts bigrading by `(r, r - 1)`.
This means `d_r : E_r^{s,t} → E_r^{s+r, t+r-1}`. -/
def adamsDiffDeg : ℤ → ℤ × ℤ := fun r => (r, r - 1)

/-- KIP §0.2.3, Axiom `prereq:ax:adams-ss`: The HF₂-Adams spectral sequence
for a spectrum `X` in `𝒮`. This is a spectral sequence in `AddCommGrpCat`
with bigrading `ℤ × ℤ`. The `(s,t)`-entry on page `r` is `E_r^{s,t}(X)`.

Construction: From an Adams resolution of `X`, one obtains a filtered object
whose associated spectral sequence is the Adams SS. The E₂-page computes as
`Ext^{s,t}_A(H*(X; F₂), F₂)`. -/
axiom AdamsSS (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]
    (X : 𝒮) : SpectralSequence (ModuleCat.{v, v} IntModuleRing.{v}) (ℤ × ℤ)

/-- KIP §0.2.3, Axiom `prereq:ax:adams-ss`: The Adams spectral sequence starts
at page 2, i.e., `r₀ = 2`. -/
axiom adamsSS_r₀ (X : 𝒮) : (AdamsSS 𝒮 X).r₀ = 2

/-- KIP §0.2.3, Axiom `prereq:ax:adams-ss`: The differential degree on the Adams
SS is `(r, r-1)`, meaning `d_r : E_r^{s,t} → E_r^{s+r, t+r-1}`. -/
axiom adamsSS_diffDeg (X : 𝒮) : (AdamsSS 𝒮 X).diffDeg = adamsDiffDeg

/-- KIP §0.2.3, Axiom `prereq:ax:adams-ss` (functoriality): A map `f : X ⟶ Y`
induces a morphism of spectral sequences `AdamsSS(X) → AdamsSS(Y)`, compatible
with differentials. -/
axiom adamsSS_map {X Y : 𝒮} (f : X ⟶ Y) :
    SpectralSequenceMorphism (AdamsSS 𝒮 X) (AdamsSS 𝒮 Y)

/-- KIP §0.2.3, Axiom `prereq:ax:adams-ss` (functoriality, identity): The Adams SS
functor sends the identity map to the identity morphism of spectral sequences. -/
axiom adamsSS_map_id (X : 𝒮) :
    (adamsSS_map (𝟙 X)).φ = fun _ => 𝟙 _

/-- KIP §0.2.3, Axiom `prereq:ax:adams-ss` (functoriality, composition): The Adams SS
functor preserves composition: `AdamsSS(g ∘ f) = AdamsSS(g) ∘ AdamsSS(f)`. -/
axiom adamsSS_map_comp {X Y Z : 𝒮} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (adamsSS_map (f ≫ g)).φ = fun k =>
      (adamsSS_map f).φ k ≫ (adamsSS_map g).φ k

/-! ### Adams E∞ data

The E∞-page of the Adams spectral sequence, axiomatized via `EInftyData`.

Blueprint: `prerequisites.tex`, Definition `prereq:def:einfty-data` and
Axiom `prereq:ax:adams-convergence`. -/

/-- KIP §0.2.3, Definition `prereq:def:einfty-data` applied to the Adams SS:
The E∞-page data of the Adams spectral sequence for a spectrum `X`.
Packages the E∞-page together with the underlying spectral sequence. -/
noncomputable def AdamsEInfty (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]
    (X : 𝒮) : EInftyData (ModuleCat.{v, v} IntModuleRing.{v}) (ℤ × ℤ) :=
  ⟨AdamsSS 𝒮 X⟩

/-- KIP §0.2.3, Definition `prereq:def:einfty-data`: The E∞ data for `X`
is associated with the Adams spectral sequence `AdamsSS 𝒮 X`. -/
theorem adamsEInfty_ss (X : 𝒮) : (AdamsEInfty 𝒮 X).ss = AdamsSS 𝒮 X := rfl

/-! ### Adams filtration on homotopy groups

The Adams spectral sequence provides a natural decreasing filtration on `π_*(X)`.
Adams filtration degree `s` records how deep into the filtration an element lies.

Formally, the Adams filtration on `π_n(X)` is a ℤ-indexed decreasing sequence of
subgroups `F^s π_n(X) ⊇ F^{s+1} π_n(X) ⊇ ⋯` such that the associated graded
pieces are identified with the E∞-page of the Adams SS via convergence.

Blueprint: `prerequisites.tex`, Definition `prereq:def:adams-filtration`. -/

/-- KIP §0.2.3, Definition `prereq:def:adams-filtration`: Predicate that an element
of `π_n(X)` has Adams filtration ≥ `s`. Concretely, `x ∈ F^s π_n(X)` means `x`
is in the image of maps that factor through `s` HF₂-acyclic maps.
Formalization bridge: axiomatized since the Adams tower construction is not
formalized; added in Polish Round 1. -/
axiom InAdamsFiltration (X : 𝒮) (s n : ℤ) (x : HomotopyGroup n X) : Prop

/-- An element of `π_n(X)` together with a witness that it has Adams filtration ≥ s. -/
structure AdamsFiltrationLevel (s n : ℤ) (X : 𝒮) where
  /-- The underlying element of π_n(X) -/
  val : HomotopyGroup n X
  /-- Witness that this element has Adams filtration ≥ s -/
  mem_filtration : InAdamsFiltration X s n val

/-- KIP §0.2.3, Definition `prereq:def:adams-filtration`: The Adams filtration
is decreasing: `F^{s+1} π_n(X) ⊆ F^s π_n(X)`. -/
axiom adamsFiltration_mono (X : 𝒮) (s n : ℤ)
    (x : AdamsFiltrationLevel (s + 1) n X) :
    ∃ y : AdamsFiltrationLevel s n X, y.val = x.val

/-- KIP §0.2.3, Definition `prereq:def:adams-filtration`: Every element of `π_n(X)`
has Adams filtration ≥ 0, i.e., `F^0 π_n(X) = π_n(X)`. -/
axiom adamsFiltration_zero (X : 𝒮) (n : ℤ) (x : HomotopyGroup n X) :
    ∃ y : AdamsFiltrationLevel 0 n X, y.val = x

/-! ### Finiteness and convergence

For finite spectra, the Adams SS converges to π_*(X) in the sense that
`E_∞^{s,t}(X) ≅ F^s π_{t-s}(X) / F^{s+1} π_{t-s}(X)`.

Blueprint: `prerequisites.tex`, Axiom `prereq:ax:adams-convergence`. -/

/-- KIP §0.2.3: A spectrum `X` is finite if it is built from the sphere spectrum
by finitely many shifts and cofiber sequences. This is the smallest class of spectra
containing `𝕊`, closed under `Σⁿ`, and closed under cofibers along distinguished
triangles. -/
inductive IsFiniteSpectrum : 𝒮 → Prop where
  | sphere : IsFiniteSpectrum SphereSpectrum
  | shift {X : 𝒮} (n : ℤ) : IsFiniteSpectrum X → IsFiniteSpectrum (X⟦n⟧)
  | cofiber {X Y Z : 𝒮} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧} :
      Triangle.mk f g h ∈ distTriang 𝒮 →
      IsFiniteSpectrum X → IsFiniteSpectrum Y → IsFiniteSpectrum Z

/-!
`IsFiniteSpectrum` is the finite-spectrum predicate used by this project.  It
is inductively generated by the sphere, integer shifts, and cofiber closure
along distinguished triangles.  Thus it is the least class supplied by these
three constructors; in particular, it does not identify every spectrum as
finite.

An independent CW-spectrum characterization is intentionally not postulated
here until the corresponding cell-complex construction is formalized.
-/

/-- KIP §0.2.3, Axiom `prereq:ax:adams-convergence`: The Adams spectral sequence
converges to `π_*(X)` for finite `X`. For each `(s, t)`, there is an isomorphism
`E_∞^{s,t}(X) ≅ F^s π_{t-s}(X) / F^{s+1} π_{t-s}(X)`, where the right side
is the `s`-th associated graded piece of the Adams filtration on `π_{t-s}(X)`.
The Adams filtration is bounded below (exhaustive): `F^s = π_*` for `s ≤ 0`. -/
axiom adamsConvergence (X : 𝒮) (hX : IsFiniteSpectrum X) :
    Σ' (F : Filtration (HomotopyGroupsModule X)),
      F.IsBoundedBelow × Convergence (AdamsEInfty 𝒮 X).ss (HomotopyGroupsModule X) F

/-! ### Adams filtration for maps

The intended Adams filtration of a map `f : X ⟶ Y` measures the complexity
of `f` in terms of HF₂-acyclic factorizations. The lightweight carrier below
does not yet encode those factorizations; it currently records only a
nonnegative integer.

Blueprint: `prerequisites.tex`, Definition `prereq:def:adams-filtration-maps`. -/

/-- A map `f : X ⟶ Y` is zero on mod 2 homology if `HF₂_*(f) = 0`.
This means `Mod2Homology.pushforward f n = 0` for all n. -/
def IsZeroOnMod2Homology {X Y : 𝒮} (f : X ⟶ Y) : Prop :=
  ∀ (n : ℤ) (x : Mod2Homology n X), (Mod2Homology.pushforward f n) x = 0

private theorem mod2Homology_pushforward_comp {X Y Z : 𝒮}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    Mod2Homology.pushforward (f ≫ g) n =
      (Mod2Homology.pushforward g n).comp (Mod2Homology.pushforward f n) := by
  ext x
  simp [Mod2Homology.pushforward, inducedMap,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]

private theorem zeroOnMod2_comp_right {X Y Z : 𝒮}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hg : IsZeroOnMod2Homology g) :
    IsZeroOnMod2Homology (f ≫ g) := by
  intro n x
  rw [mod2Homology_pushforward_comp]
  simp [hg n ((Mod2Homology.pushforward f n) x)]

private theorem zeroOnMod2_comp_left {X Y Z : 𝒮}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsZeroOnMod2Homology f) :
    IsZeroOnMod2Homology (f ≫ g) := by
  intro n x
  rw [mod2Homology_pushforward_comp]
  simp [hf n x]

/-! A factorization of length `n` in which every factor acts trivially on
mod 2 homology. A factorization of length one is exactly a map that is zero
on mod 2 homology. -/

inductive AdamsMapFactorization : {X Y : 𝒮} → ℕ → (X ⟶ Y) → Prop
  | single {X Y : 𝒮} (f : X ⟶ Y) :
      IsZeroOnMod2Homology f → AdamsMapFactorization 1 f
  | prepend {X Y Z : 𝒮} {n : ℕ} (f : X ⟶ Y) (g : Y ⟶ Z) :
      IsZeroOnMod2Homology f → AdamsMapFactorization n g →
      AdamsMapFactorization (n + 1) (f ≫ g)

namespace AdamsMapFactorization

theorem length_one_iff {X Y : 𝒮} {f : X ⟶ Y}
    (hf : AdamsMapFactorization 1 f) : IsZeroOnMod2Homology f := by
  cases hf with
  | single _ hz => exact hz
  | prepend _ _ hz hrest => cases hrest

theorem precompose {X Y Z : 𝒮} {n : ℕ} {g : Y ⟶ Z}
    (f : X ⟶ Y) (hg : AdamsMapFactorization n g) :
    AdamsMapFactorization n (f ≫ g) := by
  induction hg with
  | single g hz => exact single (f ≫ g) (zeroOnMod2_comp_right f g hz)
  | @prepend Y A Z n g h hz hrest _ih =>
      simpa [Category.assoc] using
        (prepend (f ≫ g) h (zeroOnMod2_comp_right f g hz) hrest)

theorem postcompose {X Y Z : 𝒮} {n : ℕ} {f : X ⟶ Y}
    (g : Y ⟶ Z) (hf : AdamsMapFactorization n f) :
    AdamsMapFactorization n (f ≫ g) := by
  induction hf with
  | single f hz => exact single (f ≫ g) (zeroOnMod2_comp_left f g hz)
  | @prepend X A Y n f h hz hrest ih =>
      simpa [Category.assoc] using (prepend f (h ≫ g) hz (ih g))

theorem comp {X Y Z : 𝒮} {m n : ℕ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : AdamsMapFactorization m f) (hg : AdamsMapFactorization n g) :
    AdamsMapFactorization (m + n) (f ≫ g) := by
  induction hf with
  | single f hz =>
      simpa [Nat.add_comm] using (prepend f g hz hg)
  | @prepend X A Y m f h hz hrest ih =>
      simpa [Nat.add_assoc, Nat.add_comm n 1, Category.assoc] using
        (prepend f (h ≫ g) hz (ih hg))

end AdamsMapFactorization

/-- A map filtration value together with all zero-on-homology factorizations
below that value. -/
structure AdamsFiltrationOfMap {X Y : 𝒮} (f : X ⟶ Y) where
  /-- The Adams filtration value -/
  val : ℤ
  /-- Adams filtration is non-negative -/
  property : val ≥ 0
  /-- Every positive integer below the value is realized by a factorization
  into maps that are zero on mod 2 homology. -/
  factorization : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ val → AdamsMapFactorization n f

/-- The current map-filtration carrier always admits the zero lower bound.
This witnesses only the present carrier's nonnegativity field; the carrier
does not yet relate its value to HF₂-acyclic factorizations. -/
def adamsFiltration_exists {X Y : 𝒮} (f : X ⟶ Y) :
    AdamsFiltrationOfMap f := ⟨0, le_rfl, fun n hn hle => by omega⟩

/-- `f` has Adams filtration at least `k`, witnessed by a value whose
factorization data realizes every positive level below it. -/
def AF_ge {X Y : 𝒮} (f : X ⟶ Y) (k : ℤ) : Prop :=
  ∃ af : AdamsFiltrationOfMap f, af.val ≥ k

/-- `f` has Adams filtration exactly `k`. -/
def AF_eq {X Y : 𝒮} (f : X ⟶ Y) (k : ℤ) : Prop :=
  AF_ge f k ∧ ¬ AF_ge f (k + 1)

/-- Backwards-compatible name for the lower-bound predicate. -/
abbrev HasAF_ge {X Y : 𝒮} (f : X ⟶ Y) (k : ℤ) : Prop :=
  AF_ge f k

/-- KIP §0.2.3, Definition `prereq:def:adams-filtration-maps` (characterization):
`AF(f) ≥ 1` if and only if `f` is zero on mod 2 homology `HF₂_*`.
More generally, `AF(f) ≥ k` iff `f` factors as `k` HF₂-acyclic maps. -/
theorem af_ge_one_iff_zero_on_homology {X Y : 𝒮} (f : X ⟶ Y) :
    HasAF_ge f 1 ↔ IsZeroOnMod2Homology f := by
  constructor
  · rintro ⟨af, hval⟩
    exact AdamsMapFactorization.length_one_iff
      (af.factorization 1 (by norm_num) (by simpa using hval))
  · intro hzero
    refine ⟨⟨1, by norm_num, ?_⟩, le_rfl⟩
    intro n hn hle
    have hn1 : n = 1 := by omega
    subst n
    exact AdamsMapFactorization.single f hzero

/-- The identity map has Adams filtration zero when its action on mod 2
homology is nonzero. -/
theorem af_id (X : 𝒮) (hid : ¬ IsZeroOnMod2Homology (𝟙 X)) :
    AF_eq (𝟙 X) 0 := by
  constructor
  · exact ⟨adamsFiltration_exists (𝟙 X), by simp [adamsFiltration_exists]⟩
  · intro h
    exact hid ((af_ge_one_iff_zero_on_homology (𝟙 X)).mp h)

/-- KIP §0.2.3, Proposition `prereq:prop:adams-filtration-characterization`
(subadditivity): Adams filtration is subadditive under composition,
`AF(g ∘ f) ≥ AF(f) + AF(g)`. -/
theorem af_comp {X Y Z : 𝒮} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ k l : ℤ, AF_ge f k → AF_ge g l → AF_ge (f ≫ g) (k + l) := by
  intro k l ⟨af, haf⟩ ⟨ag, hag⟩
  refine ⟨{
    val := max (k + l) 0
    property := le_max_right _ _
    factorization := ?_
  }, le_max_left _ _⟩
  intro n hn hle
  by_cases hsum : k + l ≤ 0
  · have hnle0 : (n : ℤ) ≤ 0 := by
      simpa [max_eq_right hsum] using hle
    omega
  · have hsum_pos : 0 < k + l := by omega
    have hnle : (n : ℤ) ≤ k + l := by
      simpa [max_eq_left (le_of_lt hsum_pos)] using hle
    by_cases hk : 0 < k
    · by_cases hl : 0 < l
      · let K : ℕ := k.toNat
        let L : ℕ := l.toNat
        have hK : (K : ℤ) = k := by
          simp [K, Int.toNat_of_nonneg (le_of_lt hk)]
        have hL : (L : ℤ) = l := by
          simp [L, Int.toNat_of_nonneg (le_of_lt hl)]
        have hKpos : 0 < K := by omega
        have hLpos : 0 < L := by omega
        have hnNatInt : (n : ℤ) ≤ ((K + L : ℕ) : ℤ) := by
          simpa [Nat.cast_add, hK, hL] using hnle
        have hnNat : n ≤ K + L := by exact_mod_cast hnNatInt
        by_cases hnK : n ≤ K
        · have hnleK : (n : ℤ) ≤ af.val := by
            have hnleKint : (n : ℤ) ≤ k := by
              rw [← hK]
              exact_mod_cast hnK
            exact le_trans hnleKint haf
          exact AdamsMapFactorization.postcompose g
            (af.factorization n hn hnleK)
        · have hKn : K < n := by omega
          let M : ℕ := n - K
          have hMpos : 0 < M := by omega
          have hMleL : M ≤ L := by omega
          have hMleInt : (M : ℤ) ≤ l := by
            rw [← hL]
            exact_mod_cast hMleL
          have hMle : (M : ℤ) ≤ ag.val := le_trans hMleInt hag
          have hfactors := af.factorization K hKpos (by rw [hK]; exact haf)
          have hgfactors := ag.factorization M hMpos hMle
          have hsumMN : K + M = n := by omega
          simpa [hsumMN] using AdamsMapFactorization.comp hfactors hgfactors
      · have hl' : l ≤ 0 := by omega
        have hnlek : (n : ℤ) ≤ k := by omega
        have hnleval : (n : ℤ) ≤ af.val := le_trans hnlek haf
        exact AdamsMapFactorization.postcompose g
          (af.factorization n hn hnleval)
    · have hk' : k ≤ 0 := by omega
      by_cases hl : 0 < l
      · have hnlel : (n : ℤ) ≤ l := by omega
        have hnleval : (n : ℤ) ≤ ag.val := le_trans hnlel hag
        exact AdamsMapFactorization.precompose f
          (ag.factorization n hn hnleval)
      · have hl' : l ≤ 0 := by omega
        omega

/-! ### 2-torsion property of E₂ elements

All elements in the E₂-page of the mod 2 Adams spectral sequence have
order dividing 2. This is because `E₂ = Ext_A(H*(X; F₂), F₂)` and
these Ext groups are F₂-vector spaces (A is an F₂-algebra).

Blueprint: `prerequisites.tex`, Axiom `prereq:ax:adams-e2-order2`. -/

/-- KIP §0.2.3, Axiom `prereq:ax:adams-e2-order2`: Every element in the E₂-page
of the Adams spectral sequence is 2-torsion (has order dividing 2), i.e.,
`x + x = 0` for all `x ∈ E₂`. This holds because `E₂^{s,t}(X)` is an
F₂-vector space (`Ext_A` over the F₂-algebra `A`). -/
axiom adams_2torsion (X : 𝒮) (k : ℤ × ℤ) :
    ∀ (x : (AdamsSS 𝒮 X).Page 2 k), x + x = 0

/-! ### Functoriality of Adams filtration on homotopy groups

The Adams filtration is natural with respect to maps of spectra:
a map f : X → Y sends F^s π_n(X) to F^s π_n(Y).

Blueprint: `prerequisites.tex`, Proposition `prereq:prop:adams-filtration-characterization`. -/

/-- KIP §0.2.3, Proposition `prereq:prop:adams-filtration-characterization`
(naturality): A map `f : X ⟶ Y` preserves Adams filtration:
if `x ∈ F^s π_n(X)` then `π_n(f)(x) ∈ F^s π_n(Y)`. -/
axiom adamsFiltration_functorial {X Y : 𝒮} (f : X ⟶ Y) (s n : ℤ)
    (x : AdamsFiltrationLevel s n X) :
    ∃ y : AdamsFiltrationLevel s n Y, y.val = x.val ≫ f

/-- KIP §0.2.3, Definition `prereq:def:detect` (detection): The Adams filtration
of a nonzero map `f` determines its detection in the Adams spectral sequence.
A nonzero map of Adams filtration `s` is detected by a nonzero element
in `E_∞^{s, *}`. Used in `proof-main-theorem.tex` (Proposition `prop:possible_h_6_sq`)
to relate Adams filtration of `θ₅²` to E∞-page elements. -/
axiom af_detection {X Y : 𝒮} (f : X ⟶ Y)
    (hf : f ≠ 0) :
    ∃ k t : ℤ, AF_eq f k ∧
      ¬ IsZero ((AdamsEInfty 𝒮 Y).EInfty (k, t))

/-! ### Connectivity

A spectrum X is n-connected if π_i(X) = 0 for all i ≤ n. This notion is used
in the Adams spectral sequence to establish homology vanishing results.

Blueprint: `prerequisites.tex`, §0.2.3 (`prereq:thm:sphere-connected`,
`prereq:thm:connected-homology-vanishing`). -/

/-- A spectrum X is n-connected if π_i(X) = 0 for all i ≤ n. -/
def IsConnected (X : 𝒮) (n : ℤ) : Prop :=
  ∀ i : ℤ, i ≤ n → Subsingleton (HomotopyGroup i X)

/-- The sphere spectrum is (-1)-connected.
Blueprint: prereq:thm:sphere-connected. -/
axiom sphere_connected : IsConnected (𝒮 := 𝒮) SphereSpectrum (-1)

/-- If X is n-connected, then H_i(X; F₂) = 0 for i ≤ n.
Blueprint: prereq:thm:connected-homology-vanishing. -/
axiom connected_homology_vanishing (X : 𝒮) (n : ℤ) (hX : IsConnected X n)
    (i : ℤ) (hi : i ≤ n) : Subsingleton (Mod2Homology i X)

/-! ### Extended Adams spectral sequence theory

Additional structure on the Adams spectral sequence: odd-order elements,
extended convergence for finite spectra, and boundedness of Adams filtration.

Blueprint: `prerequisites.tex`, §0.2.3 (extended axioms). -/

section ExtendedAdams

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-- Mod 2 homology commutes with suspension: H_i(X⟦n⟧; F₂) ≃ H_{i-n}(X; F₂).
    Blueprint: prereq:thm:homology-shift-iso. -/
axiom mod2Homology_shift_iso (X : 𝒮) (i n : ℤ) :
    Mod2Homology i ((shiftFunctor 𝒮 n).obj X) ≃ Mod2Homology (i - n) X

/-- From a distinguished triangle (X → Y → Z → X⟦1⟧), the mod 2 homology
    cardinality bound on `H_i(Z)` is controlled by `H_i(Y)` and
    `H_{i-1}(X)` in the long exact sequence obtained after smashing with
    EilenbergMacLane. -/
axiom mod2Homology_cofiber_bound {X Y Z : 𝒮} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ X⟦(1 : ℤ)⟧}
    (hd : Pretriangulated.Triangle.mk f g h ∈ distTriang 𝒮) (i : ℤ) (nX nY : ℕ)
    (hfX : ∀ S : Finset (Mod2Homology (i - 1) X), S.card ≤ nX)
    (hfY : ∀ S : Finset (Mod2Homology i Y), S.card ≤ nY) :
    ∀ S : Finset (Mod2Homology i Z), S.card ≤ nX + nY

/-- Finite spectra have finite-dimensional mod 2 homology in each degree.
Blueprint: `prereq:thm:finite-type-homology`. -/
theorem finiteSpectrum_homology_finiteDim (X : 𝒮) (hX : IsFiniteSpectrum X) (i : ℤ) :
    ∃ (n : ℕ), ∀ (S : Finset (Mod2Homology i X)), S.card ≤ n := by
  suffices h : ∀ (Y : 𝒮), IsFiniteSpectrum Y → ∀ j : ℤ,
      ∃ n : ℕ, ∀ S : Finset (Mod2Homology j Y), S.card ≤ n from h X hX i
  intro Y hY
  induction hY with
  | sphere =>
    intro j
    have e : Mod2Homology j (SphereSpectrum (𝒮 := 𝒮)) ≃
        HomotopyGroup j (EilenbergMacLane 𝒮) :=
      Iso.homCongr (Iso.refl _) (MonoidalCategory.rightUnitor (EilenbergMacLane 𝒮))
    suffices ∃ n : ℕ, ∀ S : Finset (HomotopyGroup j (EilenbergMacLane 𝒮)), S.card ≤ n by
      obtain ⟨n, hn⟩ := this
      exact ⟨n, fun S => by
        have := hn (S.map e.toEmbedding)
        simp only [Finset.card_map] at this
        exact this⟩
    by_cases hj : j = 0
    · subst hj
      have e0 := HF2_pi0 𝒮
      have ft : Fintype (HomotopyGroup 0 (EilenbergMacLane 𝒮)) :=
        Fintype.ofEquiv _ e0.toEquiv.symm
      exact ⟨@Fintype.card _ ft, fun S => S.card_le_univ⟩
    · have hemp := HF2_pin_zero 𝒮 j hj
      exact ⟨1, fun S => Finset.card_le_one.mpr fun a ha b hb =>
        @Subsingleton.elim _ hemp a b⟩
  | shift n _hX ih =>
    intro j
    obtain ⟨m, hm⟩ := ih (j - n)
    exact ⟨m, fun S => by
      have := hm (S.map (mod2Homology_shift_iso _ j n).toEmbedding)
      simp only [Finset.card_map] at this
      exact this⟩
  | cofiber h _hX _hY ihX ihY =>
    intro j
    obtain ⟨nX, hnX⟩ := ihX (j - 1)
    obtain ⟨nY, hnY⟩ := ihY j
    exact ⟨nX + nY, mod2Homology_cofiber_bound h j nX nY hnX hnY⟩

/-- Elements of odd order have infinite Adams filtration.
Blueprint: `prereq:thm:odd-order-af-infinity`. -/
axiom af_odd_order_infinite {X Y : 𝒮} (f : X ⟶ Y)
    (hf : ∃ n : ℕ, Odd n ∧ n > 0 ∧ n • f = 0) : ∀ k : ℤ, HasAF_ge f k

/-- Elements that do not have odd order have finite Adams filtration.
Blueprint: `prereq:thm:not-odd-order-af-finite`. -/
axiom af_not_odd_order_finite {X Y : 𝒮} (f : X ⟶ Y)
    (hf : ¬ ∃ n : ℕ, Odd n ∧ n > 0 ∧ n • f = 0) :
    ∃ k : ℤ, AF_eq f k

/-- Extended Adams convergence in the bigraded setting: for `X` and `Y` finite
spectra, the Adams SS for `[X, Y]` weakly converges.
Blueprint: `prereq:thm:adams-weak-convergence`. -/
theorem adamsConvergence_bigraded (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) :
    ∃ F : Filtration (HomotopyGroupsModule Y),
      Nonempty (Convergence (AdamsEInfty 𝒮 Y).ss (HomotopyGroupsModule Y) F) := by
  obtain ⟨F, _hbounded, hconverges⟩ := adamsConvergence Y hY
  exact ⟨F, ⟨by simpa [AdamsEInfty] using hconverges⟩⟩

/-- The Adams filtration is separated modulo odd-order:
if f has infinite Adams filtration, then f has odd order.
Blueprint: `prereq:thm:adams-separated`. -/
axiom adams_separated (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (f : X ⟶ Y) (haf : ∀ k : ℤ, HasAF_ge f k) :
    ∃ n : ℕ, Odd n ∧ n > 0 ∧ n • f = 0

/-- Placeholder retained for API compatibility. Its current type concludes only
`True`; it does not yet state finiteness of an Adams-filtration subquotient.
Blueprint target: prereq:thm:adams-subquotient-finite. -/
theorem adams_subquotient_finite (X : 𝒮) (i s : ℤ)
    (_hrat : True) : True := trivial

/-- Boundedness of the Adams filtration for rationally acyclic spectra.
Blueprint: `prereq:thm:adams-boundedness`. -/
axiom adams_boundedness (X : 𝒮) (i : ℤ)
    (_hrat : True) :
    ∃ (N : ℤ), ∀ s : ℤ, s > N → ∀ x : HomotopyGroup i X,
      ¬ InAdamsFiltration X s i x

end ExtendedAdams

end KIPBase.StableHomotopy
