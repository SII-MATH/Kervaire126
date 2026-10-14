module

public import KIP126.Def.Steenrod.MilnorCoalgebra.Antipode.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Proofs

@[expose] public section

/-! Exact compatibility of the constructed graded map with its polynomial
formula and the existing coalgebra operations. No Hopf structure or module
duality is asserted by these property statements. -/

namespace KIP126.Steenrod.Milnor.Coalgebra.Antipode

open CategoryTheory MonoidalCategory KIP126.Core.Algebra

theorem polynomial_map (n : ℤ) (x : Carrier n) :
    polynomial n ((map n).hom x) = polynomialMap (polynomial n x) := by
  classical
  have he (d : (Fin 1 × ℕ) →₀ ℕ) :
      (slotExponentsEquiv 1).symm (fun _ => slotExponentsEquiv 1 d 0) = d := by
    apply (slotExponentsEquiv 1).injective
    simp only [Equiv.apply_symm_apply]
    funext i
    rw [show i = 0 from Subsingleton.elim _ _]
  have hs (m : MilnorMonomial n) : polynomial n (monomial m) = monomialImage m := by
    unfold monomial
    simp only [map_sum, map_smul]
    simp only [polynomial, Finsupp.linearCombination_single, one_smul,
      monomialPolynomial, he, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    exact (Finset.sum_attach _ (fun d => MvPolynomial.monomial d
      (MvPolynomial.coeff d (monomialImage m)))).trans
        (MvPolynomial.support_sum_monomial_coeff (monomialImage m))
  have h : (polynomial n).comp (map n).hom = polynomialMap.toLinearMap.comp (polynomial n) := by
    apply Finsupp.lhom_ext
    intro m r
    change polynomial n ((Finsupp.linearCombination F2 monomial) (Finsupp.single m r)) =
      polynomialMap (polynomial n (Finsupp.single m r))
    simp only [Finsupp.linearCombination_single, map_smul, hs]
    simp [polynomial, Finsupp.linearCombination_single, monomialImage]
  exact LinearMap.congr_fun h x

theorem map_involutive : map ≫ map = 𝟙 dualSteenrod.X := by
  have hi (n : ℤ) : Function.Injective (polynomial n) := by
    have he : Function.Injective (fun m : MilnorMonomial n =>
        (slotExponentsEquiv 1).symm (fun _ => m.val)) := by
      intro a b h
      apply Subtype.ext
      have hp := (slotExponentsEquiv 1).symm.injective h
      exact congrFun hp 0
    exact ((MvPolynomial.basisMonomials (Fin 1 × ℕ) F2).linearIndependent.comp _ he).finsuppLinearCombination_injective
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply hi n
  change polynomial n ((map n).hom ((map n).hom x)) = polynomial n x
  rw [polynomial_map, polynomial_map, polynomialMap_involutive]

theorem map_counit : map ≫ counit = counit := by
  have hi : Function.Injective (polynomial 0) := by
    have he : Function.Injective (fun m : MilnorMonomial 0 =>
        (slotExponentsEquiv 1).symm (fun _ => m.val)) := by
      intro a b h
      apply Subtype.ext
      exact congrFun ((slotExponentsEquiv 1).symm.injective h) 0
    exact ((MvPolynomial.basisMonomials (Fin 1 × ℕ) F2).linearIndependent.comp _ he).finsuppLinearCombination_injective
  have hm : (map 0).hom = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro m r
    apply hi
    change polynomial 0 ((map 0).hom (Finsupp.single m r)) = polynomial 0 (Finsupp.single m r)
    rw [polynomial_map, milnorMonomial_zero_eq m]
    have he : (slotExponentsEquiv 1).symm (fun _ => (0 : ℕ →₀ ℕ)) = 0 := by
      apply (slotExponentsEquiv 1).injective
      rw [Equiv.apply_symm_apply]
      rfl
    simp [polynomial, Finsupp.linearCombination_single, monomialPolynomial,
      zeroMilnorMonomial, he]
  funext n
  change map n ≫ counit n = counit n
  by_cases hn : n = 0
  · subst n
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, hm, LinearMap.comp_id]
  · simp only [counit, hn, ↓reduceDIte]
    exact Limits.comp_zero

theorem coaugmentation_map : coaugmentationMap ≫ map = coaugmentationMap := by
  have hi : Function.Injective (polynomial 0) := by
    have he : Function.Injective (fun m : MilnorMonomial 0 =>
        (slotExponentsEquiv 1).symm (fun _ => m.val)) := by
      intro a b h
      apply Subtype.ext
      exact congrFun ((slotExponentsEquiv 1).symm.injective h) 0
    exact ((MvPolynomial.basisMonomials (Fin 1 × ℕ) F2).linearIndependent.comp _ he).finsuppLinearCombination_injective
  have hm : (map 0).hom = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro m r
    apply hi
    change polynomial 0 ((map 0).hom (Finsupp.single m r)) = polynomial 0 (Finsupp.single m r)
    rw [polynomial_map, milnorMonomial_zero_eq m]
    have he : (slotExponentsEquiv 1).symm (fun _ => (0 : ℕ →₀ ℕ)) = 0 := by
      apply (slotExponentsEquiv 1).injective
      rw [Equiv.apply_symm_apply]
      rfl
    simp [polynomial, Finsupp.linearCombination_single, monomialPolynomial,
      zeroMilnorMonomial, he]
  funext n
  change coaugmentationMap n ≫ map n = coaugmentationMap n
  by_cases hn : n = 0
  · subst n
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp]
    erw [hm]
    rfl
  · simp only [coaugmentationMap, hn, ↓reduceDIte]
    exact Limits.zero_comp

private theorem polynomialMap_anti_split (p : TensorPower 1) :
    splitSlot (s:=1) 0 (polynomialMap p) =
      (MvPolynomial.aeval (R:=F2) (fun a : Fin 2 × ℕ =>
        if a.1=0 then MvPolynomial.rename (fun b : Fin 1 × ℕ => ((1 : Fin 2),b.2)) (generatorImage (a.2+1))
        else MvPolynomial.rename (fun b : Fin 1 × ℕ => ((0 : Fin 2),b.2)) (generatorImage (a.2+1))))
          (splitSlot (s:=1) 0 p) := by
  classical
  let T (N : ℕ) (q : ℕ → TensorPower 2) : Matrix (Fin (N+1)) (Fin (N+1)) (TensorPower 2) :=
    fun i j => if i ≤ j then q (j.val-i.val) ^ (2^i.val) else 0
  have hprod (N : ℕ) (q r : ℕ → TensorPower 2) (i j : Fin (N+1)) :
      (T N q * T N r) i j = if i ≤ j then
        (∑ a ∈ Finset.range (j.val-i.val+1), q a * r (j.val-i.val-a) ^ (2^a)) ^ (2^i.val)
        else 0 := by
    by_cases hij : i ≤ j
    · rw [if_pos hij, sum_pow_char_pow]
      change (∑ k, T N q i k * T N r k j) = _
      calc
        _ = ∑ k ∈ Finset.univ.filter (fun k : Fin (N+1) => i ≤ k ∧ k ≤ j),
            T N q i k * T N r k j := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro k _ hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hk
          by_cases hik : i ≤ k
          · simp [T, hik, hk hik]
          · simp [T, hik]
        _ = _ := by
          apply Finset.sum_bij (fun k _ => k.val-i.val)
          · intro k hk
            have hk' := (Finset.mem_filter.mp hk).2
            simp only [Finset.mem_range]
            omega
          · intro k hk l hl hkl
            have hk' := (Finset.mem_filter.mp hk).2
            have hl' := (Finset.mem_filter.mp hl).2
            apply Fin.ext
            omega
          · intro a ha
            have ha' := Finset.mem_range.mp ha
            refine ⟨⟨i.val+a,by omega⟩,?_,?_⟩
            · simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.le_def]
              omega
            · simp
          · intro k hk
            obtain ⟨hik,hkj⟩ := (Finset.mem_filter.mp hk).2
            have hsub : j.val-i.val-(k.val-i.val)=j.val-k.val := by omega
            have hpow : 2^k.val=2^(k.val-i.val)*2^i.val := by
              rw [← pow_add]
              congr 1
              omega
            simp only [T, if_pos hik, if_pos hkj, mul_pow, ← pow_mul, hsub, hpow]
    · rw [if_neg hij, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : i ≤ k
      · have hkj : ¬k ≤ j := by omega
        simp [T,hkj]
      · simp [T,hik]
  have hr (n : ℕ) :
      ∑ i ∈ Finset.range (n+1), xi (0 : Fin 1) (n-i) ^ (2^i) * generatorImage i =
        if n=0 then 1 else 0 := by
    cases n with
    | zero => simp [xi,generatorImage_zero]
    | succ n =>
      have h := rightConvolution_split (xi (0 : Fin 1) (n+1))
      have hz (k : ℕ) : rightConvolution (xi (0 : Fin 2) k) = xi 0 k := by
        cases k <;> simp [xi,rightConvolution]
      have ho (k : ℕ) : rightConvolution (xi (1 : Fin 2) k) = generatorImage k := by
        cases k <;> simp [xi,rightConvolution,generatorImage_zero]
      simp only [xi,splitSlot,MvPolynomial.aeval_X,if_true,polynomialAugmentation] at h
      simp only [coproductGenerator,map_sum,map_mul,map_pow] at h
      change (∑ i ∈ Finset.range (n+2), rightConvolution (xi (0 : Fin 2) (n+1-i)) ^ (2^i) *
        rightConvolution (xi (1 : Fin 2) i)) = 0 at h
      simpa only [hz,ho,Nat.succ_ne_zero,if_false] using h
  have hinv (N : ℕ) (f : TensorPower 1 →ₐ[F2] TensorPower 2) :
      T N (fun n => f (generatorImage n)) * T N (fun n => f (xi 0 n)) = 1 := by
    apply Matrix.ext
    intro i j
    refine (hprod N (fun n => f (generatorImage n)) (fun n => f (xi 0 n)) i j).trans ?_
    have hs (d : ℕ) :
        ∑ a ∈ Finset.range (d+1), f (generatorImage a) * f (xi 0 (d-a)) ^ (2^a) =
          if d=0 then 1 else 0 := by
      have h := congrArg f (hr d)
      by_cases hd : d = 0 <;> simpa [hd, map_sum, map_mul, map_pow, mul_comm] using h
    by_cases hij : i ≤ j
    · rw [if_pos hij, hs]
      by_cases he : i=j
      · subst j
        simp
      · have hn : j.val-i.val ≠ 0 := by
          intro h
          apply he
          apply Fin.ext
          omega
        simp [hn,he]
    · simp [hij,show i ≠ j from fun h => hij h.le]
  let fL : TensorPower 1 →ₐ[F2] TensorPower 2 :=
    MvPolynomial.rename (fun b : Fin 1 × ℕ => ((0 : Fin 2),b.2))
  let fR : TensorPower 1 →ₐ[F2] TensorPower 2 :=
    MvPolynomial.rename (fun b : Fin 1 × ℕ => ((1 : Fin 2),b.2))
  let D : TensorPower 1 →ₐ[F2] TensorPower 2 := splitSlot (s:=1) 0
  let Q : TensorPower 2 →ₐ[F2] TensorPower 2 := MvPolynomial.aeval fun a =>
    if a.1=0 then fR (generatorImage (a.2+1)) else fL (generatorImage (a.2+1))
  have hL (n : ℕ) : fL (xi 0 n) = xi 0 n := by cases n <;> simp [fL,xi]
  have hR (n : ℕ) : fR (xi 0 n) = xi 1 n := by cases n <;> simp [fR,xi]
  have hD (n : ℕ) : D (xi 0 n) =
      ∑ a ∈ Finset.range (n+1), xi (0 : Fin 2) (n-a) ^ (2^a) * xi 1 a := by
    cases n with
    | zero => simp [xi,D]
    | succ n => simp [D,xi,splitSlot,coproductGenerator]
  have hΔ (N : ℕ) : T N (fun n => D (xi 0 n)) =
      T N (fun n => fR (xi 0 n)) * T N (fun n => fL (xi 0 n)) := by
    apply Matrix.ext
    intro i j
    symm
    refine (hprod N (fun n => fR (xi 0 n)) (fun n => fL (xi 0 n)) i j).trans ?_
    simp only [T,hD,hL,hR,mul_comm]
  have hS (N : ℕ) : T N (fun n => D (generatorImage n)) =
      T N (fun n => fL (generatorImage n)) * T N (fun n => fR (generatorImage n)) := by
    let A := T N (fun n => D (generatorImage n))
    let B := T N (fun n => D (xi 0 n))
    let C := T N (fun n => fL (generatorImage n)) * T N (fun n => fR (generatorImage n))
    have hab : A*B=1 := hinv N D
    have hbc : B*C=1 := by
      dsimp [B,C]
      rw [hΔ]
      rw [mul_assoc, ← mul_assoc (T N (fun n => fL (xi 0 n)))]
      rw [mul_eq_one_comm.mp (hinv N fL),one_mul,mul_eq_one_comm.mp (hinv N fR)]
    exact (left_inv_eq_right_inv hab hbc)
  have hgen (n : ℕ) : D (generatorImage n) = Q (D (xi 0 n)) := by
    have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) (TensorPower 2) =>
      M 0 (Fin.last n)) (hS n)
    change T n (fun k => D (generatorImage k)) 0 (Fin.last n) =
      (T n (fun k => fL (generatorImage k)) * T n (fun k => fR (generatorImage k))) 0 (Fin.last n) at h
    rw [hprod n (fun k => fL (generatorImage k)) (fun k => fR (generatorImage k)) 0 (Fin.last n)] at h
    simp only [T,Fin.le_last,if_true,Fin.val_zero,Fin.val_last,Nat.sub_zero,pow_zero,pow_one] at h
    have hQ0 (m : ℕ) : Q (xi (0 : Fin 2) m) = fR (generatorImage m) := by
      cases m <;> simp [Q,xi,generatorImage_zero]
    have hQ1 (m : ℕ) : Q (xi (1 : Fin 2) m) = fL (generatorImage m) := by
      cases m <;> simp [Q,xi,generatorImage_zero]
    rw [h,hD]
    simp only [map_sum,map_mul,map_pow,hQ0,hQ1,mul_comm]
  have hhom : D.comp polynomialMap = Q.comp D := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a,n⟩
    have ha : a=0 := Subsingleton.elim _ _
    subst a
    change D (polynomialMap (xi 0 (n+1))) = Q (D (xi 0 (n+1)))
    rw [polynomialMap_xi,hgen]
  exact AlgHom.congr_fun hhom p

/-- Anti-comultiplicativity states the necessary braiding explicitly; it
does not replace the original comultiplication by a swapped convention. -/
theorem map_comultiplication :
    map ≫ comultiplication =
      comultiplication ≫ (map ⊗ₘ map) ≫ (β_ dualSteenrod.X dualSteenrod.X).hom := by
  classical
  have hpoly := polynomialMap_anti_split
  let r (i : Fin 2) : TensorPower 1 →ₐ[F2] TensorPower 2 :=
    MvPolynomial.rename fun a => (i,a.2)
  let Q : TensorPower 2 →ₐ[F2] TensorPower 2 := MvPolynomial.aeval fun a =>
    if a.1=0 then r 1 (generatorImage (a.2+1)) else r 0 (generatorImage (a.2+1))
  have hQ : ∀ p : TensorPower 1, splitSlot (s:=1) 0 (polynomialMap p) = Q (splitSlot (s:=1) 0 p) := hpoly
  have hconstr {M : Type} [AddCommGroup M] [Module F2 M]
      (v : ((Fin 2 × ℕ) →₀ ℕ) → M) (d : (Fin 2 × ℕ) →₀ ℕ) (c : F2) :
      ((MvPolynomial.basisMonomials (Fin 2 × ℕ) F2).constr F2) v (MvPolynomial.monomial d c) = c • v d := by
    rw [show MvPolynomial.monomial d c = c • (MvPolynomial.basisMonomials (Fin 2 × ℕ) F2) d from by
      simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    simp only [map_smul, Module.Basis.constr_basis]
  let R (n : ℤ) : TensorPower 2 →ₗ[F2] ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded n) :=
    ((MvPolynomial.basisMonomials (Fin 2 × ℕ) F2).constr F2) fun d =>
      if h : (slotWeight (slotExponentsEquiv 2 d 0) : ℤ) +
          (slotWeight (slotExponentsEquiv 2 d 1) : ℤ) = n then
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded
          (slotWeight (slotExponentsEquiv 2 d 0) : ℤ)
          (slotWeight (slotExponentsEquiv 2 d 1) : ℤ) n h).hom
          ((Finsupp.single ⟨slotExponentsEquiv 2 d 0,rfl⟩ 1 : Carrier _) ⊗ₜ[F2]
            (Finsupp.single ⟨slotExponentsEquiv 2 d 1,rfl⟩ 1 : Carrier _))
      else 0
  have hR {n : ℤ} (m : MilnorMonomial n) :
      R n (splitMonomial m) = comultiplicationMonomial m := by
    have hsum := (Finset.sum_attach (splitMonomial m).support
      (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d (splitMonomial m)))).trans
      (MvPolynomial.support_sum_monomial_coeff (splitMonomial m))
    rw [← hsum]
    simp only [map_sum]
    unfold comultiplicationMonomial
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [R]
    rw [hconstr, dif_pos (splitMonomial_support_degree m d.val d.property)]
    rfl
  have hΔ {n : ℤ} (x : Carrier n) :
      R n (splitSlot (s:=1) 0 (polynomial n x)) = (comultiplication n).hom x := by
    have hh : (R n).comp ((splitSlot (s:=1) 0).toLinearMap.comp (polynomial n)) =
        (comultiplication n).hom := by
      apply Finsupp.lhom_ext
      intro m c
      change R n (splitSlot (s:=1) 0 ((Finsupp.linearCombination F2 monomialPolynomial)
        (Finsupp.single m c))) =
        (Finsupp.linearCombination F2 comultiplicationMonomial) (Finsupp.single m c)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul, map_smul]
      exact congrArg (c • ·) (hR m)
    exact LinearMap.congr_fun hh x
  let f (i : Fin 2) : ℕ → Fin 2 × ℕ := fun j => (i,j)
  have hf (i : Fin 2) : Function.Injective (f i) := fun _ _ h => congrArg Prod.snd h
  let u : ℕ → Fin 1 × ℕ := fun j => (0,j)
  have hu : Function.Injective u := fun _ _ h => congrArg Prod.snd h
  have hmono {n : ℤ} (m : MilnorMonomial n) :
      monomialPolynomial m = MvPolynomial.rename u (MvPolynomial.monomial m.val 1) := by
    simp only [monomialPolynomial, MvPolynomial.rename_monomial]
    apply congrArg (fun d : (Fin 1 × ℕ) →₀ ℕ => MvPolynomial.monomial d (1 : F2))
    apply (slotExponentsEquiv 1).injective
    rw [Equiv.apply_symm_apply]
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    ext j
    exact (Finsupp.mapDomain_apply hu m.val j).symm
  have hrmono {n : ℤ} (m : MilnorMonomial n) (i : Fin 2) :
      r i (monomialPolynomial m) = MvPolynomial.rename (f i) (MvPolynomial.monomial m.val 1) := by
    rw [hmono]
    simp only [r, MvPolynomial.rename_rename]
    rfl
  let join (d e : ℕ →₀ ℕ) := d.mapDomain (f 0) + e.mapDomain (f 1)
  have hjoin0 (d e : ℕ →₀ ℕ) : slotExponentsEquiv 2 (join d e) 0 = d := by
    ext j
    change (d.mapDomain (f 0) + e.mapDomain (f 1)) (0,j) = d j
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply (hf 0) _ j,
      Finsupp.mapDomain_notin_range _ _ (by simp [f]), add_zero]
  have hjoin1 (d e : ℕ →₀ ℕ) : slotExponentsEquiv 2 (join d e) 1 = e := by
    ext j
    change (d.mapDomain (f 0) + e.mapDomain (f 1)) (1,j) = e j
    rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ (by simp [f]),
      Finsupp.mapDomain_apply (hf 1) _ j, zero_add]
  have hRprod {a b n : ℤ} (h : a + b = n) (m0 : MilnorMonomial a) (m1 : MilnorMonomial b) :
      R n (r 0 (monomialPolynomial m0) * r 1 (monomialPolynomial m1)) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          (Finsupp.single m0 1 ⊗ₜ[F2] Finsupp.single m1 1) := by
    rw [hrmono, hrmono]
    simp only [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, one_mul]
    change R n (MvPolynomial.monomial (join m0.val m1.val) 1) = _
    rcases m0 with ⟨d0,rfl⟩
    rcases m1 with ⟨d1,rfl⟩
    have he0 := hjoin0 d0 d1
    have he1 := hjoin1 d0 d1
    dsimp only [R]
    rw [hconstr, one_smul]
    generalize hx0 : slotExponentsEquiv 2 (join d0 d1) 0 = a0 at he0 ⊢
    generalize hx1 : slotExponentsEquiv 2 (join d0 d1) 1 = a1 at he1 ⊢
    clear hx0 hx1
    subst a0 a1
    rw [dif_pos h]
  have hprod {a b n : ℤ} (h : a + b = n) (x : Carrier a) (y : Carrier b) :
      R n (r 0 (polynomial a x) * r 1 (polynomial b y)) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          (x ⊗ₜ[F2] y) := by
    let B : Carrier a →ₗ[F2] Carrier b →ₗ[F2]
        ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded n) :=
      (TensorProduct.mk F2 (Carrier a) (Carrier b)).compr₂ₛₗ
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
    change _ = B x y
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' =>
      simp only [map_add, add_mul, LinearMap.add_apply]
      rw [hx, hx']
    | single m0 c =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' =>
        simp only [map_add, mul_add]
        rw [hy, hy']
      | single m1 d =>
        have h0 : Finsupp.single m0 c = c • Finsupp.single m0 (1 : F2) := by simp
        have h1 : Finsupp.single m1 d = d • Finsupp.single m1 (1 : F2) := by simp
        rw [h0, h1]
        simp only [map_smul, LinearMap.smul_apply, smul_mul_smul]
        simp only [polynomial, Finsupp.linearCombination_single, one_smul]
        have hb : R n (r 0 (monomialPolynomial m0) * r 1 (monomialPolynomial m1)) =
          B (Finsupp.single m0 1) (Finsupp.single m1 1) := hRprod h m0 m1
        rw [hb, smul_smul, mul_comm c d]
  have hQr0 : Q.comp (r 0) = (r 1).comp polynomialMap := by
    ext a : 1
    simp [AlgHom.comp_apply, Q, r, polynomialMap]
  have hQr1 : Q.comp (r 1) = (r 0).comp polynomialMap := by
    ext a : 1
    simp [AlgHom.comp_apply, Q, r, polynomialMap]
  have hjoin (d : (Fin 2 × ℕ) →₀ ℕ) :
      join (slotExponentsEquiv 2 d 0) (slotExponentsEquiv 2 d 1) = d := by
    apply (slotExponentsEquiv 2).injective
    funext i
    fin_cases i
    · exact hjoin0 _ _
    · exact hjoin1 _ _
  have hfactor (d : (Fin 2 × ℕ) →₀ ℕ) :
      MvPolynomial.monomial d (1 : F2) =
        r 0 (monomialPolynomial (slotMonomial d 0)) *
          r 1 (monomialPolynomial (slotMonomial d 1)) := by
    rw [hrmono, hrmono]
    simp only [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, one_mul]
    exact congrArg (fun d : (Fin 2 × ℕ) →₀ ℕ => MvPolynomial.monomial d (1 : F2)) (hjoin d).symm
  have hmon {n : ℤ} (m : MilnorMonomial n) :
      polynomial n (monomial m) = polynomialMap (monomialPolynomial m) := by
    have hh := polynomial_map n (Finsupp.single m 1)
    change polynomial n ((Finsupp.linearCombination F2 monomial) (Finsupp.single m 1)) =
      polynomialMap ((Finsupp.linearCombination F2 monomialPolynomial) (Finsupp.single m 1)) at hh
    simpa only [Finsupp.linearCombination_single, one_smul] using hh
  have hQmon {n : ℤ} (d : (Fin 2 × ℕ) →₀ ℕ)
      (hd : (slotWeight (slotExponentsEquiv 2 d 0) : ℤ) +
        (slotWeight (slotExponentsEquiv 2 d 1) : ℤ) = n) :
      R n (Q (MvPolynomial.monomial d 1)) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded
          (slotWeight (slotExponentsEquiv 2 d 1) : ℤ)
          (slotWeight (slotExponentsEquiv 2 d 0) : ℤ) n (by omega)).hom
          (monomial (slotMonomial d 1) ⊗ₜ[F2] monomial (slotMonomial d 0)) := by
    rw [hfactor, map_mul]
    have h0 := AlgHom.congr_fun hQr0 (monomialPolynomial (slotMonomial d 0))
    have h1 := AlgHom.congr_fun hQr1 (monomialPolynomial (slotMonomial d 1))
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at h0 h1
    rw [h0, h1, mul_comm, ← hmon, ← hmon]
    exact hprod (by omega) _ _
  have hB (a b n : ℤ) (h : a + b = n) (x : Carrier a) (y : Carrier b) :
      ((β_ dualSteenrod.X dualSteenrod.X).hom n).hom
        ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          (x ⊗ₜ[F2] y)) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded b a n (by omega)).hom
          (y ⊗ₜ[F2] x) := by
    have hh : GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h ≫
        (GradedObject.Monoidal.braiding dualSteenrodGraded dualSteenrodGraded).hom n =
        (β_ (dualSteenrodGraded a) (dualSteenrodGraded b)).hom ≫
          GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded b a n (by omega) := by
      exact GradedObject.Monoidal.ι_tensorObjDesc
        (X₁ := dualSteenrodGraded) (X₂ := dualSteenrodGraded)
        (fun i j hij => (β_ (dualSteenrodGraded i) (dualSteenrodGraded j)).hom ≫
          GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded j i n (by omega)) a b h
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hh) (x ⊗ₜ[F2] y)
  have htensor {A B C D : ModuleCat F2} (f : A ⟶ B) (g : C ⟶ D) (x : A) (y : C) :
      (f ⊗ₘ g).hom (x ⊗ₜ[F2] y) = f.hom x ⊗ₜ[F2] g.hom y :=
    TensorProduct.map_tmul _ _ _ _
  have hT (a b n : ℤ) (h : a + b = n) (x : Carrier a) (y : Carrier b) :
      ((map ⊗ₘ map) n).hom
        ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          (x ⊗ₜ[F2] y)) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          ((map a).hom x ⊗ₜ[F2] (map b).hom y) := by
    have hh := GradedObject.Monoidal.ι_tensorHom map map a b n h
    have hh' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hh) (x ⊗ₜ[F2] y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh'
    refine hh'.trans ?_
    exact congrArg (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
      (htensor (map a) (map b) x y)
  have hm {n : ℤ} (m : MilnorMonomial n) : (map n).hom (Finsupp.single m 1) = monomial m := by
    change (Finsupp.linearCombination F2 monomial) (Finsupp.single m 1) = _
    rw [Finsupp.linearCombination_single, one_smul]
  have hBT (a b n : ℤ) (h : a + b = n) (m0 : MilnorMonomial a) (m1 : MilnorMonomial b) :
      ((β_ dualSteenrod.X dualSteenrod.X).hom n).hom
        (((map ⊗ₘ map) n).hom
          ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
            (Finsupp.single m0 1 ⊗ₜ[F2] Finsupp.single m1 1))) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded b a n (by omega)).hom
          (monomial m1 ⊗ₜ[F2] monomial m0) := by
    rw [hT, hB, hm, hm]
  have hright {n : ℤ} (m : MilnorMonomial n) :
      R n (Q (splitMonomial m)) =
        ((β_ dualSteenrod.X dualSteenrod.X).hom n).hom
          (((map ⊗ₘ map) n).hom (comultiplicationMonomial m)) := by
    let T : ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded n) →ₗ[F2]
        ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded n) :=
      ((β_ dualSteenrod.X dualSteenrod.X).hom n).hom.comp (((map ⊗ₘ map) n).hom)
    change _ = T (comultiplicationMonomial m)
    have hs := (Finset.sum_attach (splitMonomial m).support
      (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d (splitMonomial m)))).trans
      (MvPolynomial.support_sum_monomial_coeff (splitMonomial m))
    conv_lhs => rw [← hs]
    simp only [map_sum]
    unfold comultiplicationMonomial
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [show MvPolynomial.monomial d.val (MvPolynomial.coeff d.val (splitMonomial m)) =
        MvPolynomial.coeff d.val (splitMonomial m) • MvPolynomial.monomial d.val 1 from by
      simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    rw [map_smul, map_smul]
    exact congrArg (MvPolynomial.coeff d.val (splitMonomial m) • ·)
      ((hQmon d.val (splitMonomial_support_degree m d.val d.property)).trans
        (hBT _ _ _ (splitMonomial_support_degree m d.val d.property)
          (slotMonomial d.val 0) (slotMonomial d.val 1)).symm)
  have hb {n : ℤ} (m : MilnorMonomial n) :
      (comultiplication n).hom (monomial m) =
        ((β_ dualSteenrod.X dualSteenrod.X).hom n).hom
          (((map ⊗ₘ map) n).hom (comultiplicationMonomial m)) := by
    rw [← hΔ, hmon, hQ]
    exact hright m
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro m c
  change (comultiplication n).hom
      ((Finsupp.linearCombination F2 monomial) (Finsupp.single m c)) =
    ((β_ dualSteenrod.X dualSteenrod.X).hom n).hom
      (((map ⊗ₘ map) n).hom
        ((Finsupp.linearCombination F2 comultiplicationMonomial) (Finsupp.single m c)))
  rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  let T : ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded n) →ₗ[F2]
      ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded n) :=
    ((β_ dualSteenrod.X dualSteenrod.X).hom n).hom.comp (((map ⊗ₘ map) n).hom)
  exact ((comultiplication n).hom.map_smul c (monomial m)).trans
    ((congrArg (c • ·) (hb m)).trans (T.map_smul c (comultiplicationMonomial m)).symm)

end KIP126.Steenrod.Milnor.Coalgebra.Antipode
