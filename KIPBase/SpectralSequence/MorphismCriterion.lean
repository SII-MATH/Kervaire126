import KIPBase.SpectralSequence.Basic

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-- A criterion stated using representatives, with no page map as input.
The zero-differential clause says that a representative of zero remains zero
modulo target indeterminacy; it is the `x = 0` case of the differential
comparison. The remaining clause compares the induced differentials once
the quotient maps have been constructed. -/
structure DifferentialMorphismCriterion
    (E E' : SpectralSequence C ι)
    (f : UnderlyingMorphism ι E.ssData E'.ssData) where
  r₀_eq : E.r₀ = E'.r₀
  diffDeg_eq : E.diffDeg = E'.diffDeg
  survives : ∀ (k : ι) (n : WithTop ℕ),
    ∃ zLift : Subobject.underlying.obj ((E.ssData k).Z n) ⟶
        Subobject.underlying.obj ((E'.ssData k).Z n),
      zLift ≫ ((E'.ssData k).Z n).arrow =
        ((E.ssData k).Z n).arrow ≫ f.φ k
  zero_differential : ∀ (k : ι) (n : WithTop ℕ),
    let β := Subobject.ofLE ((E.ssData k).B n)
      ((E.ssData k).Z n) ((E.ssData k).B_le_Z n)
    β ≫ (survives k n).choose ≫ (E'.ssData k).pageπ n = 0
  differential : ∀ (r : ℤ) (k : ι),
      let n : WithTop ℕ := ↑(r - E.r₀).toNat
      let n' : WithTop ℕ := ↑(r - E'.r₀).toNat
      let hn : n = n' := congrArg
        (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) r₀_eq
      let hk : k + E.diffDeg r = k + E'.diffDeg r :=
        congrArg (fun d => k + d) (congrFun diffDeg_eq r)
      ∀ (T : C)
        (x : T ⟶ Subobject.underlying.obj ((E.ssData k).Z n))
        (y : T ⟶ Subobject.underlying.obj
          ((E.ssData (k + E.diffDeg r)).Z n)),
        x ≫ (E.ssData k).pageπ n ≫ E.d r k =
          y ≫ (E.ssData (k + E.diffDeg r)).pageπ n →
        x ≫ (survives k n).choose ≫ (E'.ssData k).pageπ n ≫
          eqToHom (by rw [hn]) ≫ E'.d r k =
        y ≫ (survives (k + E.diffDeg r) n).choose ≫
          (E'.ssData (k + E.diffDeg r)).pageπ n ≫
          eqToHom (by rw [hk, hn])

/-- The zero-differential clause yields preservation of boundaries by
exactness of the cokernel. Hence the induced page map is constructed from
the underlying map and is not part of the criterion's data. -/
noncomputable def DifferentialMorphismCriterion.toSSDataMorphism
    {E E' : SpectralSequence C ι}
    {f : UnderlyingMorphism ι E.ssData E'.ssData}
    (H : DifferentialMorphismCriterion E E' f) :
    SSDataMorphism ι E.ssData E'.ssData := {
  φ := f.φ
  preserves_Z := H.survives
  preserves_B := by
    intro k n
    let D := E.ssData k
    let D' := E'.ssData k
    let β := Subobject.ofLE (D.B n) (D.Z n) (D.B_le_Z n)
    let β' := Subobject.ofLE (D'.B n) (D'.Z n) (D'.B_le_Z n)
    let zLift := (H.survives k n).choose
    have hz : zLift ≫ (D'.Z n).arrow = (D.Z n).arrow ≫ f.φ k :=
      (H.survives k n).choose_spec
    have hzero : (β ≫ zLift) ≫ D'.pageπ n = 0 := by
      simpa only [Category.assoc] using H.zero_differential k n
    let bLift := (ShortComplex.exact_cokernel β').lift (β ≫ zLift) hzero
    refine ⟨bLift, ?_⟩
    calc
      bLift ≫ (D'.B n).arrow =
          (bLift ≫ β') ≫ (D'.Z n).arrow := by
            rw [Category.assoc, Subobject.ofLE_arrow]
      _ = (β ≫ zLift) ≫ (D'.Z n).arrow := by
            rw [ShortComplex.Exact.lift_f]
      _ = (D.B n).arrow ≫ f.φ k := by
            rw [Category.assoc, hz, ← Category.assoc,
              Subobject.ofLE_arrow]
}

/-- The representative criterion constructs the spectral-sequence
morphism with the prescribed underlying map. -/
noncomputable def DifferentialMorphismCriterion.toMorphism
    {E E' : SpectralSequence C ι}
    {f : UnderlyingMorphism ι E.ssData E'.ssData}
    (H : DifferentialMorphismCriterion E E' f) :
    SpectralSequenceMorphism E E' := by
  let F := H.toSSDataMorphism
  let P : PreSSMorphism E.toPreSS E'.toPreSS := {
    toSSDataMorphism := F
    r₀_eq := H.r₀_eq
    diffDeg_eq := H.diffDeg_eq
    comm_d := by
      intro r k
      let n : WithTop ℕ := ↑(r - E.r₀).toNat
      let hn : n = (↑(r - E'.r₀).toNat : WithTop ℕ) :=
        congrArg (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) H.r₀_eq
      let hk : k + E.diffDeg r = k + E'.diffDeg r :=
        congrArg (fun d => k + d) (congrFun H.diffDeg_eq r)
      let p := (E.ssData k).pageπ n
      let q := (E.ssData (k + E.diffDeg r)).pageπ n
      haveI : Epi p := by dsimp only [p, SSData.pageπ]; infer_instance
      haveI : Epi q := by dsimp only [q, SSData.pageπ]; infer_instance
      let g := p ≫ E.d r k
      let P := pullback g q
      haveI : Epi (pullback.fst g q) := inferInstance
      have hrep := H.differential r k P (pullback.fst g q) (pullback.snd g q)
        (pullback.condition)
      have hπ (j : ι) :
          (F.preserves_Z j n).choose = (H.survives j n).choose := rfl
      apply (cancel_epi p).mp
      apply (cancel_epi (pullback.fst g q)).mp
      dsimp only [P, g, p, q] at hrep ⊢
      simp only [SSDataMorphism.pageMapOfEq] at ⊢
      simp only [← Category.assoc] at ⊢
      rw [Category.assoc (pullback.fst g q) p (E.d r k)] at ⊢
      rw [pullback.condition] at ⊢
      rw [Category.assoc (pullback.fst g q) p (F.pageMap k n)] at ⊢
      rw [Category.assoc (pullback.snd g q) q
        (F.pageMap (k + E.diffDeg r) n)] at ⊢
      rw [F.pageπ_pageMap, F.pageπ_pageMap] at ⊢
      rw [hπ k, hπ (k + E.diffDeg r)] at ⊢
      convert hrep using 1 <;> simp only [Category.assoc] <;>
        dsimp only [g, q, p, n]
  }
  exact { toPreSSMorphism := P }

theorem DifferentialMorphismCriterion.exists_morphism
    {E E' : SpectralSequence C ι}
    {f : UnderlyingMorphism ι E.ssData E'.ssData}
    (H : DifferentialMorphismCriterion E E' f) :
    ∃ F : SpectralSequenceMorphism E E', ∀ k, F.φ k = f.φ k := by
  exact ⟨H.toMorphism, fun _ => rfl⟩

end KIPBase.SpectralSequence
