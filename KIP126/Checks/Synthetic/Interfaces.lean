import KIP126.Def.StableHomotopy.Implementation.Data
import Lean.Elab.Command

/-! Check the tower-based filtration and consume the exact synthetic
interfaces from explicit located inputs, without a historical or stage axiom. -/

open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic KIP126.Synthetic.Context

universe u v u' v'

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn)

-- Every map has filtration at least zero; the zero map admits every finite
-- lower bound. Neither requires choosing an arbitrary filtration integer.
example {X Y : C} (f : X ⟶ Y) : AdamsFiltrationAtLeast H f 0 := by
  refine ⟨f, ?_⟩
  simp [adamsTowerMap, adamsTowerComposite]

example {X Y : C} (k : ℕ) : AdamsFiltrationAtLeast H (0 : X ⟶ Y) k := by
  exact ⟨0, CategoryTheory.Limits.zero_comp⟩

example (input : SyntheticInterface H N) (T : Triangle C)
    (hT : T ∈ distTriang C) (hSES : HomologyShortExact H T) :
    ∃ δ : N.functor.obj T.obj₃ ⟶ (N.functor.obj T.obj₁)⟦(1 : ℤ)⟧,
      Triangle.mk (N.functor.map T.mor₁) (N.functor.map T.mor₂) δ ∈ distTriang Syn :=
  (input.nu_cofiber T hT).mpr hSES

example (input : SyntheticInterface H N) (T : Triangle C)
    (hT : T ∈ distTriang C) (hν : NuImageIsCofiber N T) (n : ℤ) :
    Function.Injective (Mod2Homology.pushforward H T.mor₁ n) ∧
      Function.Surjective (Mod2Homology.pushforward H T.mor₂ n) := by
  have h := (input.nu_cofiber T hT).mp hν n
  exact ⟨h.1, h.2.2⟩

example (input : SyntheticInterface H N) {X Y : C}
    (f : X ⟶ Y) (k : ℕ) (hf : AdamsFiltrationAtLeast H f k) :
    ∃ l : N.functor.obj X ⟶
        (SyntheticCategory.biShift (0, -(k : ℤ))).obj (N.functor.obj Y),
      l ≫ lambdaPow k (N.functor.obj Y) = N.functor.map f := by
  obtain ⟨L⟩ := input.lift f k hf
  exact ⟨L.map, L.factorization⟩

example (input : SyntheticInterface H N) (T : Triangle C)
    (hT : T ∈ distTriang C) (hf : AdamsFiltrationAtLeast H T.mor₃ 1)
    (hSES : HomologyShortExact H T) :
    ∃ D : SyntheticTriangleLift N T,
      D.connecting ≫ SyntheticCategory.lam.app (N.functor.obj (T.obj₁⟦(1 : ℤ)⟧)) =
        N.functor.map T.mor₃ ∧
      Triangle.mk (N.functor.map T.mor₁) (N.functor.map T.mor₂)
        (D.connecting ≫ (N.boundaryLandingIso T.obj₁).hom) ∈ distTriang Syn ∧
      D.FullLiftComparison N := by
  obtain ⟨D, hD⟩ := input.triangle_lift T hT hf hSES
  exact ⟨D, D.factorization, D.distinguished, hD⟩

open Lean Elab Command in
run_cmd do
  for name in [``NuCofiberCriterion, ``SyntheticLiftComparison,
      ``SyntheticTriangleLiftComparison] do
    let axioms ← liftCoreM (collectAxioms name)
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected synthetic-interface assumption: {name}: {axiomName}"
  for moduleName in (← getEnv).allImportedModuleNames do
    if (`KIPBase).isPrefixOf moduleName ||
        (`KIP126.Interface).isPrefixOf moduleName ||
        (`KIP126.Main).isPrefixOf moduleName then
      throwError "synthetic interface depends on an admitted fixed model: {moduleName}"
