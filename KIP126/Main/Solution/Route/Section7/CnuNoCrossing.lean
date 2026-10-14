module

public import KIP126.Main.Solution.Route.Section7.Common

@[expose] public section

namespace KIP126.Main.Solution.Route.Section7
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Main.StageInput
noncomputable section

local notation "D" => routeModel
local notation "M" => standardMilnorCooperations
local notation "L" => routeLabels
local notation "I" => routeComputation
local notation "η" => routeEta
local notation "h₀" => routeLiterature.toda.h0

section CnuNoCrossing
open KIP126.Computation.Route
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M' : MilnorCooperations H}
  {D' : Model H M' Syn} {L' : Labels H} {G : TmfLabels H}
local notation "E" => sequence D' KIP126.Computation.Route.Raw.Spectrum.nuCofiber

private theorem cnu_d2_zero_of_reaches (r : ℤ) (hr : 3 ≤ r)
    (x : (E).Page 2 (9,135)) (hx : ReachesPage E r (9,135) x) :
    (E).d 2 (9,135) x = 0 := by
  obtain ⟨xr, hr', z, hz, _⟩ := hx
  change x ∈ LinearMap.ker ((E).d 2 (9,135)).hom
  rw [← subobjectModule_kernel, (E).Z_succ 2 (9,135) (by change (2 : ℤ) ≤ 2; omega), subobjectModule_image]
  let A := (E).ssData (9,135)
  have hle : (1 : WithTop ℕ) ≤ ↑(r-2).toNat := by
    exact_mod_cast (show 1 ≤ (r-2).toNat by omega)
  refine ⟨(Subobject.ofLE (A.Z ↑(r-2).toNat) (A.Z 1) (A.Z_anti hle)) z, ?_⟩
  change (Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0)
    ((Subobject.ofLE (A.Z ↑(r-2).toNat) (A.Z 1) _) z) = x
  rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  exact hz

private theorem cnu_d2_zero (input : Inputs D' L' G) : (E).d 2 (9,135) = 0 := by
  have hdecode (i : Fin 5) : input.realization.decode .nuCofiber 9 135 [i.val] =
      some (input.realization.basis .nuCofiber 9 135 i.val) := by
    have hv : Raw.coordinatesValid Raw.degrees .nuCofiber 9 135 [i.val] = true := by
      fin_cases i <;> decide
    simp [Realization.decode, hv]
  have h0 : (E).d 2 (9,135) (input.realization.basis .nuCofiber 9 135 0) = 0 := by
    have hrow := input.results _ (List.getElem_mem (l := Raw.claims) (n := 51) (by decide))
    obtain ⟨x, hx, y, hy, h⟩ := hrow
    have hx' : x = input.realization.basis .nuCofiber 9 135 0 :=
      Option.some.inj (hx.symm.trans (hdecode ⟨0, by decide⟩))
    subst x
    obtain ⟨_, xr, yr, hxr, _, _⟩ := h
    exact cnu_d2_zero_of_reaches 3 (by decide) _ ⟨xr, hxr⟩
  have h1 : (E).d 2 (9,135) (input.realization.basis .nuCofiber 9 135 1) = 0 := by
    have hrow := input.results _ (List.getElem_mem (l := Raw.claims) (n := 49) (by decide))
    obtain ⟨x, hx, h⟩ := hrow
    have hx' : x = input.realization.basis .nuCofiber 9 135 1 :=
      Option.some.inj (hx.symm.trans (hdecode ⟨1, by decide⟩))
    subst x
    exact cnu_d2_zero_of_reaches 16 (by decide) _ h
  have h2 : (E).d 2 (9,135) (input.realization.basis .nuCofiber 9 135 2) = 0 := by
    have hrow := input.results _ (List.getElem_mem (l := Raw.claims) (n := 50) (by decide))
    obtain ⟨x, hx, y, hy, h⟩ := hrow
    have hx' : x = input.realization.basis .nuCofiber 9 135 2 :=
      Option.some.inj (hx.symm.trans (hdecode ⟨2, by decide⟩))
    subst x
    obtain ⟨_, xr, yr, hxr, _, _⟩ := h
    exact cnu_d2_zero_of_reaches 4 (by decide) _ ⟨xr, hxr⟩
  have htarget (p q : ℤ × ℤ) (x : (E).Page 2 p) (y : (E).Page 2 q)
      (h : HasDifferential E 2 p q x y) : (E).d 2 q y = 0 := by
    obtain ⟨rfl, hd⟩ := h.eq_on_page_two
    have hd' : (E).d 2 p x = y := by
      simpa only [eqToHom_refl, Category.comp_id] using hd
    exact IsPageBoundary.d_eq_zero (r := 2) (p := p) ⟨x, hd'⟩
  have h3 : (E).d 2 (9,135) (input.realization.basis .nuCofiber 9 135 3) = 0 := by
    have hrow := input.results _ (List.getElem_mem (l := Raw.claims) (n := 47) (by decide))
    obtain ⟨x, hx, y, hy, h⟩ := hrow
    have hy' : y = input.realization.basis .nuCofiber 9 135 3 :=
      Option.some.inj (hy.symm.trans (hdecode ⟨3, by decide⟩))
    subst y
    exact htarget (7,134) (9,135) x _ h
  have h4 : (E).d 2 (9,135) (input.realization.basis .nuCofiber 9 135 4) = 0 := by
    have hrow := input.results _ (List.getElem_mem (l := Raw.claims) (n := 48) (by decide))
    obtain ⟨x, hx, y, hy, h⟩ := hrow
    have hy' : y = input.realization.basis .nuCofiber 9 135 4 :=
      Option.some.inj (hy.symm.trans (hdecode ⟨4, by decide⟩))
    subst y
    exact htarget (7,134) (9,135) x _ h
  have hb := input.basis _ (List.getElem_mem (l := Raw.degrees) (n := 34) (by decide))
  obtain ⟨e, he⟩ := hb
  change (E).Page 2 (9,135) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = input.realization.basis .nuCofiber 9 135 i.val at he
  have hone (i : Fin 5) : (E).d 2 (9,135) (e.symm (Finsupp.single i 1)) = 0 := by
    rw [he i]
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hall (f : Fin 5 →₀ KIP126.Core.Algebra.F2) : (E).d 2 (9,135) (e.symm f) = 0 := by
    induction f using Finsupp.induction with
    | zero => simp
    | @single_add i a f hi ha ih =>
      rw [map_add, map_add, ih, add_zero]
      fin_cases a
      · simp
      · exact hone i
  ext x
  simpa only [LinearEquiv.symm_apply_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hall (e x)

end CnuNoCrossing

/-- The second no-crossing alternative checked in `lem:nuext125`.
For exponents (1,0,0) and lengths (3,0,0), the Mahowald parameters are
r=r'=3 at (8,134). The only crossing candidate is the full Cnu d2 from
(9,135) to (11,136); I's complete source basis and staircase kill it.
The zero-length q-extension supplies the other alternative independently;
neither alternative is a new C premise, or a Moss crossing condition. -/
theorem cnu_d3_no_crossing :
    let F := KIP126.Def.fixedImplementation.foundationInput
    @PageRepresentatives.NoCrossingOn F.Spectrum F.stable F.cofiber F.hf2
      (letI := F.stable; letI := F.cofiber;
        HasFunctorialCofiber.cofib (D).auxiliary.nuMap) 3 3 (8,134) := by
  set_option backward.isDefEq.respectTransparency false in
    change PageRepresentatives.NoCrossingOn standardFoundation.hf2
      (HasFunctorialCofiber.cofib (D).auxiliary.nuMap) 3 3 (8,134)
    refine ⟨by decide, le_rfl, ?_⟩
    rintro ⟨a, b, ha, ha', hb, hb', x, y, h⟩
    have ha1 : a = 1 := by omega
    have hb0 : b = 0 := by omega
    subst a b
    exact h.d_ne_zero (cnu_d2_zero I)


end
end KIP126.Main.Solution.Route.Section7
