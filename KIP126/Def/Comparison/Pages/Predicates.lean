import KIP126.Def.SpectralSequence.Basic.Category.Data
import KIP126.Def.SpectralSequence.Computation.Predicates
import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
/-!
# Spectral-sequence page and morphism calculus

These are parameterized mathematical definitions, independent of fixed program data
and stage witnesses. Existing public declaration names are preserved.
-/

namespace KIP126.Challenge2

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams Core.SpectralSequence

universe u v w

/-- am1：一般内部页面 calculus 的派生交付。页面与微分均来自同一个 E；
同调同构来自 nested Z/B 模型，不另选一套谱序列。 -/
structure PageCalculus {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : Core.SpectralSequence C ι) : Prop where
  homology : ∀ (r : ℤ) (k : ι), E.r₀ ≤ r →
    Nonempty (E.Page (r + 1) k ≅ (E.pageShortComplex r (k - E.diffDeg r)).homology)
  square_zero : ∀ (r : ℤ) (k : ι), E.d r k ≫ E.d r (k + E.diffDeg r) = 0

/-- am1：模页面的代表元、边界及非零微分条件。普通微分等式不能提供
非零存活；后两个字段明确保留 `HasNonzeroDifferential` 的非零前提。 -/
structure RepresentativeCalculus {R : Type u} [Ring R]
    (E : Core.SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)) : Prop where
  page_two : ∀ p (a b : E.Page 2 p), RepresentsOnPage E 2 p a b → a = b
  boundary_cycle : ∀ r p (a : E.Page r (p + E.diffDeg r)),
    IsPageBoundary E r p a → IsPageCycle E r (p + E.diffDeg r) a
  differential_source : ∀ r p q (x : E.Page 2 p) (y : E.Page 2 q),
    HasNonzeroDifferential E r p q x y → SurvivesTo E r p x
  differential_target : ∀ r p q (x : E.Page 2 p) (y : E.Page 2 q),
    HasNonzeroDifferential E r p q x y → SurvivesTo E r q y

/-- am1/am2/am7：论文的 Z_c、B_c 是实际 E₂ 内的子模，不能与尚未除去
第一微分边界的 raw ambient 混同。这里集中列出页码、商映射和 crossing
约定的派生交付；不新增可自由选择的 cycles、boundaries 或 differential。 -/
structure PaperCycleCalculus {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    (H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)) (X : C) : Prop where
  first_cycles : ∀ p, PageRepresentatives.cycles H X 1 p = ⊤
  first_boundaries : ∀ p, PageRepresentatives.boundaries H X 1 p = ⊥
  represents : ∀ r, 2 ≤ r → ∀ p (x : PageRepresentatives.Ambient H X p),
    PageRepresentatives.IsCycle H X (r - 1) p x ↔
      ∃ xr : (adamsTowerInternalSpectralSequence H.unit X).Page r p,
        RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X) r p x xr
  degree : ∀ r p q (x : PageRepresentatives.Ambient H X p)
    (y : PageRepresentatives.Ambient H X q),
    PageRepresentatives.DifferentialAt H X r p q x y → p + (r, r - 1) = q
  no_crossing_two : ∀ r, 2 ≤ r → ∀ p, PageRepresentatives.NoCrossingOn H X r 2 p

/-- am3：同一内部谱序列态射的派生自然性。所有页面映射由 f 的环境映射
诱导；不另选页面映射，也不把微分等式加强为非零结论。 -/
structure MorphismCalculus {R : Type u} [Ring R]
    (E E' : Core.SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (f : SpectralSequenceMorphism E E') : Prop where
  differential_comm : ∀ (r : ℤ) (p : ℤ × ℤ),
    f.pageMap r p ≫ E'.d r p =
      E.d r p ≫ f.pageMap r (p + E.diffDeg r) ≫
        eqToHom (by rw [f.diffDeg_eq])
  page_identity : ∀ (r : ℤ) (p : ℤ × ℤ),
    (𝟙 E : E ⟶ E).pageMap r p = 𝟙 _
  page_composition : ∀ (E'' : Core.SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (g : SpectralSequenceMorphism E' E'') (r : ℤ) (p : ℤ × ℤ),
    (CategoryStruct.comp (X := E) (Y := E') (Z := E'') f g).pageMap r p = f.pageMap r p ≫ g.pageMap r p
  infinity_identity : ∀ (p : ℤ × ℤ), (𝟙 E : E ⟶ E).eInftyMap p = 𝟙 _
  infinity_composition : ∀ (E'' : Core.SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (g : SpectralSequenceMorphism E' E'') (p : ℤ × ℤ),
    (CategoryStruct.comp (X := E) (Y := E') (Z := E'') f g).eInftyMap p = f.eInftyMap p ≫ g.eInftyMap p
  representatives : ∀ (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) (y : E.Page r p),
    RepresentsOnPage E r p x y →
      RepresentsOnPage E' r p (f.pageMap 2 p x) (f.pageMap r p y)
  differential : ∀ (r : ℤ) (p q : ℤ × ℤ) (x : E.Page 2 p) (y : E.Page 2 q),
    HasDifferential E r p q x y →
      HasDifferential E' r p q (f.pageMap 2 p x) (f.pageMap 2 q y)

end KIP126.Challenge2
