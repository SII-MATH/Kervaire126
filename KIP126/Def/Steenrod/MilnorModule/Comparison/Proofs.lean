import KIP126.Def.Steenrod.MilnorModule.Comparison.Predicates
import Mathlib.Algebra.Module.ZMod

/-!
The prescribed Ext comparison is induced by the actual transpose on the fixed
cofree resolution. Its all-cocycle representative condition determines it
uniquely; no comparison is introduced as additional data or an assumption.
-/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory KIP126.Core.Algebra

open CategoryTheory.Limits MonoidalCategory KIP126.Algebra
open GradedVectorSpace GradedDual GradedObject.Monoidal
open CochainComplex.HomComplex
open scoped DirectSum TensorProduct BigOperators

/-- The canonical Cauchy pairing identifies the finite tensor basis with its dual basis. -/
private theorem comparison_pairing_bijective (X Y : GrVect F2) (I J : ℤ → Type)
    (bX : ∀ i, Module.Basis (I i) F2 (X i))
    (bY : ∀ i, Module.Basis (J i) F2 (Y i))
    [∀ i, Finite (I i)] [∀ i, Finite (J i)] (n : ℤ)
    [Finite (Σ q : {p : ℤ × ℤ // p.1+p.2=n}, I q.val.1 × J q.val.2)] :
    Function.Bijective
      ((GradedObject.Monoidal.tensorObjDesc
        (X₁ := degreewiseDual X) (X₂ := degreewiseDual Y) (k := n)
        (fun i j h => ModuleCat.ofHom ((tensorProjection X Y i j).hom.dualMap.comp
          (TensorProduct.dualDistrib F2 (X i) (Y j))) ≫
            eqToHom (congrArg (degreewiseDual (X ⊗ Y)) h))).hom) := by
  let P (X Y : GrVect F2) (n : ℤ) :
      (degreewiseDual X ⊗ degreewiseDual Y) n ⟶ degreewiseDual (X ⊗ Y) n :=
    GradedObject.Monoidal.tensorObjDesc (fun i j h =>
      ModuleCat.ofHom ((tensorProjection X Y i j).hom.dualMap.comp
        (TensorProduct.dualDistrib F2 (X i) (Y j))) ≫
        eqToHom (congrArg (degreewiseDual (X ⊗ Y)) h))
  change Function.Bijective (P X Y n).hom
  have same (X Y : GrVect F2) (n : ℤ)
      (q : {p : ℤ × ℤ // p.1+p.2=n})
      (φ : Module.Dual F2 (X q.val.1)) (ψ : Module.Dual F2 (Y q.val.2))
      (x : X q.val.1) (y : Y q.val.2) :
      (show Module.Dual F2 ((X ⊗ Y) n) from (P X Y n).hom
        ((GradedObject.Monoidal.ιTensorObj (degreewiseDual X) (degreewiseDual Y)
          q.val.1 q.val.2 n q.property).hom (φ ⊗ₜ[F2] ψ)))
        ((GradedObject.Monoidal.ιTensorObj X Y q.val.1 q.val.2 n q.property).hom
          (x ⊗ₜ[F2] y)) = φ x * ψ y := by
    classical
    rcases q with ⟨⟨i,j⟩,rfl⟩
    have h := GradedObject.Monoidal.ι_tensorObjDesc
      (X₁ := degreewiseDual X) (X₂ := degreewiseDual Y)
      (fun i j h => ModuleCat.ofHom ((tensorProjection X Y i j).hom.dualMap.comp
        (TensorProduct.dualDistrib F2 (X i) (Y j))) ≫
        eqToHom (congrArg (degreewiseDual (X ⊗ Y)) h)) i j rfl
    have h' := congrArg (fun f => f.hom (φ ⊗ₜ[F2] ψ)) h
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply ] at h'
    change (P X Y (i+j)).hom
        ((GradedObject.Monoidal.ιTensorObj (degreewiseDual X) (degreewiseDual Y) i j (i+j) rfl).hom (φ ⊗ₜ[F2] ψ)) =
      (tensorProjection X Y i j).hom.dualMap (TensorProduct.dualDistrib F2 (X i) (Y j) (φ ⊗ₜ[F2] ψ)) at h'
    refine (congrArg (fun f : Module.Dual F2 ((X ⊗ Y) (i+j)) =>
      f ((GradedObject.Monoidal.ιTensorObj X Y i j (i+j) rfl).hom (x ⊗ₜ[F2] y))) h').trans ?_
    change TensorProduct.dualDistrib F2 (X i) (Y j) (φ ⊗ₜ[F2] ψ)
      (((GradedObject.Monoidal.ιTensorObj X Y i j (i+j) rfl) ≫ tensorProjection X Y i j).hom (x ⊗ₜ[F2] y)) = _
    simp only [tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc,
      and_self, dite_true, eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply]
    rfl

  have different (X Y : GrVect F2) (n : ℤ)
      (q p : {p : ℤ × ℤ // p.1+p.2=n}) (hqp : p ≠ q)
      (φ : Module.Dual F2 (X q.val.1)) (ψ : Module.Dual F2 (Y q.val.2))
      (x : X p.val.1) (y : Y p.val.2) :
      (show Module.Dual F2 ((X ⊗ Y) n) from (P X Y n).hom
        ((GradedObject.Monoidal.ιTensorObj (degreewiseDual X) (degreewiseDual Y)
          q.val.1 q.val.2 n q.property).hom (φ ⊗ₜ[F2] ψ)))
        ((GradedObject.Monoidal.ιTensorObj X Y p.val.1 p.val.2 n p.property).hom
          (x ⊗ₜ[F2] y)) = 0 := by
    classical
    rcases q with ⟨⟨i,j⟩,rfl⟩
    have h := GradedObject.Monoidal.ι_tensorObjDesc
      (X₁ := degreewiseDual X) (X₂ := degreewiseDual Y)
      (fun i j h => ModuleCat.ofHom ((tensorProjection X Y i j).hom.dualMap.comp
        (TensorProduct.dualDistrib F2 (X i) (Y j))) ≫
        eqToHom (congrArg (degreewiseDual (X ⊗ Y)) h)) i j rfl
    have h' := congrArg (fun f => f.hom (φ ⊗ₜ[F2] ψ)) h
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply ] at h'
    change (P X Y (i+j)).hom
        ((GradedObject.Monoidal.ιTensorObj (degreewiseDual X) (degreewiseDual Y) i j (i+j) rfl).hom (φ ⊗ₜ[F2] ψ)) =
      (tensorProjection X Y i j).hom.dualMap (TensorProduct.dualDistrib F2 (X i) (Y j) (φ ⊗ₜ[F2] ψ)) at h'
    refine (congrArg (fun f : Module.Dual F2 ((X ⊗ Y) (i+j)) =>
      f ((GradedObject.Monoidal.ιTensorObj X Y p.val.1 p.val.2 (i+j) p.property).hom (x ⊗ₜ[F2] y))) h').trans ?_
    change TensorProduct.dualDistrib F2 (X i) (Y j) (φ ⊗ₜ[F2] ψ)
      (((GradedObject.Monoidal.ιTensorObj X Y p.val.1 p.val.2 (i+j) p.property) ≫
        tensorProjection X Y i j).hom (x ⊗ₜ[F2] y)) = _
    have hp : ¬(p.val.1 = i ∧ p.val.2 = j) := by
      intro h
      apply hqp
      exact Subtype.ext (Prod.ext h.1 h.2)
    simp only [tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc, hp, dite_false,
      ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]

  have dsbasis {Q : Type} [DecidableEq Q] {M : Q → Type}
      [∀ q, AddCommGroup (M q)] [∀ q, Module F2 (M q)]
      {I : Q → Type} (b : ∀ q, Module.Basis (I q) F2 (M q)) (q : Q) (i : I q) :
      DFinsupp.basis b ⟨q,i⟩ = DirectSum.lof F2 Q M q (b q i) := by
    classical
    simp [DFinsupp.basis, DirectSum.lof, DFinsupp.lsingle]
    rfl
  classical
  let Q := {p : ℤ × ℤ // p.1+p.2=n}
  let D := Σ q : Q, I q.val.1 × J q.val.2
  let Z : Q → ModuleCat F2 := fun q => X q.val.1 ⊗ Y q.val.2
  let W : Q → ModuleCat F2 := fun q => degreewiseDual X q.val.1 ⊗ degreewiseDual Y q.val.2
  let b (q : Q) : Module.Basis (I q.val.1 × J q.val.2) F2 (Z q) :=
    (bX q.val.1).tensorProduct (bY q.val.2)
  let c (q : Q) : Module.Basis (I q.val.1 × J q.val.2) F2 (W q) :=
    by
      change Module.Basis (I q.val.1 × J q.val.2) F2
        (Module.Dual F2 (X q.val.1) ⊗[F2] Module.Dual F2 (Y q.val.2))
      exact (bX q.val.1).dualBasis.tensorProduct (bY q.val.2).dualBasis
  let eZ : (X ⊗ Y) n ≅ ModuleCat.of F2 (⨁ q : Q, Z q) := ModuleCat.coprodIsoDirectSum Z
  let eW : (degreewiseDual X ⊗ degreewiseDual Y) n ≅ ModuleCat.of F2 (⨁ q : Q, W q) :=
    ModuleCat.coprodIsoDirectSum W
  let B : Module.Basis D F2 ((X ⊗ Y) n) := (DFinsupp.basis b).map eZ.toLinearEquiv.symm
  let C : Module.Basis D F2 ((degreewiseDual X ⊗ degreewiseDual Y) n) :=
    (DFinsupp.basis c).map eW.toLinearEquiv.symm
  have hB (q : Q) (a : I q.val.1) (b' : J q.val.2) :
      B ⟨q,a,b'⟩ = (GradedObject.Monoidal.ιTensorObj X Y q.val.1 q.val.2 n q.property).hom
        (bX q.val.1 a ⊗ₜ[F2] bY q.val.2 b') := by
    simp only [B, Module.Basis.map_apply]
    rw [dsbasis b q (a,b')]
    have he := congrArg (fun f => f.hom (b q (a,b'))) (ModuleCat.lof_coprodIsoDirectSum_inv Z q)
    change eZ.inv.hom (DirectSum.lof F2 Q (fun q => Z q) q (b q (a,b'))) = _
    have hbq : b q (a,b') = bX q.val.1 a ⊗ₜ[F2] bY q.val.2 b' :=
      Module.Basis.tensorProduct_apply _ _ _ _
    rw [← hbq]
    exact he
  have hC (q : Q) (a : I q.val.1) (b' : J q.val.2) :
      C ⟨q,a,b'⟩ = (GradedObject.Monoidal.ιTensorObj (degreewiseDual X) (degreewiseDual Y)
        q.val.1 q.val.2 n q.property).hom
          ((bX q.val.1).dualBasis a ⊗ₜ[F2] (bY q.val.2).dualBasis b') := by
    simp only [C, Module.Basis.map_apply]
    rw [dsbasis c q (a,b')]
    have he := congrArg (fun f => f.hom (c q (a,b'))) (ModuleCat.lof_coprodIsoDirectSum_inv W q)
    change eW.inv.hom (DirectSum.lof F2 Q (fun q => W q) q (c q (a,b'))) = _
    have hcq : c q (a,b') = (bX q.val.1).dualBasis a ⊗ₜ[F2] (bY q.val.2).dualBasis b' :=
      Module.Basis.tensorProduct_apply _ _ _ _
    exact he.trans (congrArg (Sigma.ι W q).hom hcq)
  let E := C.equiv B.dualBasis (Equiv.refl D)
  have h : (P X Y n).hom = E.toLinearMap := by
    apply C.ext
    intro d
    change (P X Y n).hom (C d) = E (C d)
    rw [Module.Basis.equiv_apply]
    change (P X Y n).hom (C d) = B.dualBasis d
    apply B.ext
    intro e
    rw [Module.Basis.dualBasis_apply_self]
    rcases d with ⟨q,a,b'⟩
    rcases e with ⟨p,a',b''⟩
    rw [hC,hB]
    by_cases hp : p=q
    · subst p
      rw [same]
      simp only [Module.Basis.dualBasis_apply_self]
      have he : (⟨q,a',b''⟩ : D) = ⟨q,a,b'⟩ ↔ a'=a ∧ b''=b' := by
        constructor
        · intro h
          exact Prod.mk.inj (eq_of_heq (Sigma.mk.inj h).2)
        · rintro ⟨rfl,rfl⟩
          rfl
      simp only [he]
      by_cases ha : a' = a <;> by_cases hb : b'' = b' <;> simp [ha,hb]
    · rw [different X Y n q p hp]
      simp [show (⟨p,a',b''⟩ : D) ≠ ⟨q,a,b'⟩ from fun h => hp (congrArg Sigma.fst h)]
  rw [h]
  exact E.bijective

/-- The free extension of the transposed cofree counit has the prescribed conjugation pairing. -/
private theorem comparison_free_eval (W : GrVect F2) (i j : ℤ)
    (a : Module.Dual F2 (Coalgebra.dualSteenrod.X i))
    (φ : Module.Dual F2 (W j)) (x : (W ⊗ Coalgebra.dualSteenrod.X) (i+j)) :
    (show Module.Dual F2 ((W ⊗ Coalgebra.dualSteenrod.X) (i+j)) from
      ((((GradedModule.leftTensorMonad steenrod).adj.homEquiv (degreewiseDual W)
        (dualLeftModule ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).cofree.obj W))).symm
      (degreewiseDualMap ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).ε.app W))).f (i+j)).hom
        ((ιTensorObj steenrod.X (degreewiseDual W) i j (i+j) rfl).hom (a ⊗ₜ[F2] φ))) x =
    TensorProduct.dualDistrib F2 (W j) (Coalgebra.dualSteenrod.X i)
      (φ ⊗ₜ[F2] (conjugation i).hom a)
      ((tensorProjection W Coalgebra.dualSteenrod.X j i).hom
        ((eqToHom (congrArg (show GrVect F2 from W ⊗ Coalgebra.dualSteenrod.X) (add_comm i j))).hom x)) := by
  have projection_naturality (X Y X' Y' : GrVect F2)
      (g : X ⟶ X') (h : Y ⟶ Y') (i j : ℤ) :
      GradedObject.Monoidal.tensorHom g h (i+j) ≫ tensorProjection X' Y' i j =
        tensorProjection X Y i j ≫ (g i ⊗ₘ h j) := by
    classical
    apply tensorObj_ext
    intro a b hab
    erw [ι_tensorHom_assoc]
    simp only [tensorProjection, ι_tensorObjDesc, ι_tensorObjDesc_assoc]
    by_cases he : a=i ∧ b=j
    · rcases he with ⟨rfl,rfl⟩
      simp only [and_self,dite_true,eqToHom_refl,Category.id_comp,Category.comp_id]
    · simp only [he,dite_false,Limits.zero_comp,Limits.comp_zero]

  have cofree_counit_projection (W : GrVect F2) (i j : ℤ) :
      coactionComponent ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).cofree.obj W) i j ≫
        ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).ε.app W i ⊗ₘ 𝟙 (Coalgebra.dualSteenrod.X j)) =
          tensorProjection W Coalgebra.dualSteenrod.X i j := by
    let G := GradedComodule.rightTensorComonad Coalgebra.dualSteenrod
    change G.δ.app W (i+j) ≫ tensorProjection (W ⊗ Coalgebra.dualSteenrod.X) Coalgebra.dualSteenrod.X i j ≫
      (G.ε.app W i ⊗ₘ (𝟙 Coalgebra.dualSteenrod.X) j) = _
    erw [← projection_naturality _ _ _ _ (G.ε.app W) (𝟙 Coalgebra.dualSteenrod.X) i j]
    erw [← Category.assoc]
    have h := congrFun (G.right_counit W) (i+j)
    change G.δ.app W (i+j) ≫ GradedObject.Monoidal.tensorHom (G.ε.app W) (𝟙 Coalgebra.dualSteenrod.X) (i+j) = 𝟙 _ at h
    erw [h, Category.id_comp]
    rfl

  let freeToDualCofree (W : GrVect F2) :
      (GradedModule.leftTensorMonad steenrod).free.obj (degreewiseDual W) ⟶
        dualLeftModule ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).cofree.obj W) :=
    ((GradedModule.leftTensorMonad steenrod).adj.homEquiv _ _).symm
      (degreewiseDualMap ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).ε.app W))

  have dual_transport (X : GrVect F2) {i j : ℤ} (h : i=j)
      (φ : Module.Dual F2 (X i)) (x : X j) :
      (show Module.Dual F2 (X j) from
        (eqToHom (congrArg (degreewiseDual X) h)).hom φ) x =
      φ ((eqToHom (congrArg X h.symm)).hom x) := by
    subst j
    rfl
  let G := GradedComodule.rightTensorComonad Coalgebra.dualSteenrod
  let M := G.cofree.obj W
  let e : (W ⊗ Coalgebra.dualSteenrod.X) ⟶ W := G.ε.app W
  have hf : (freeToDualCofree W).f =
      (GradedModule.leftTensorMonad steenrod).map (degreewiseDualMap e) ≫ (dualLeftModule M).a := by
    dsimp only [freeToDualCofree]
    rw [Adjunction.homEquiv_symm_apply, Monad.adj_counit]
    rfl
  rw [hf]
  change (show Module.Dual F2 (M.A (i+j)) from
    ((GradedObject.Monoidal.tensorHom (𝟙 steenrod.X) (degreewiseDualMap e) (i+j) ≫ dualLeftAction M (i+j)).hom)
      ((ιTensorObj steenrod.X (degreewiseDual W) i j (i+j) rfl).hom (a ⊗ₜ[F2] φ))) x = _
  have hc := ι_tensorHom (𝟙 steenrod.X) (degreewiseDualMap e) i j (i+j) rfl
  have hcomp := congrArg (fun k => k.hom (a ⊗ₜ[F2] φ)) hc
  change _ = _ at hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [hcomp]
  have hact := ι_tensorObjDesc
    (fun i j h => dualLeftPairing M i j ≫ eqToHom (congrArg (degreewiseDual M.A) h)) i j rfl
  have hact' := congrArg (fun k => k.hom
    (a ⊗ₜ[F2] (e j).hom.dualMap φ)) hact
  change _ = _ at hact'
  simp only [eqToHom_refl, Category.comp_id, ModuleCat.hom_comp, LinearMap.comp_apply] at hact'
  change (show Module.Dual F2 (M.A (i+j)) from
    (dualLeftAction M (i+j)).hom ((ιTensorObj steenrod.X (degreewiseDual M.A) i j (i+j) rfl).hom
      (a ⊗ₜ[F2] (e j).hom.dualMap φ))) x = _
  erw [hact']
  simp only [dualLeftPairing, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [dual_transport M.A (add_comm j i)]
  change TensorProduct.dualDistrib F2 (M.A j) (Coalgebra.dualSteenrod.X i)
    ((e j).hom.dualMap φ ⊗ₜ[F2] (conjugation i).hom a)
    ((coactionComponent M j i).hom
      ((eqToHom (congrArg M.A (add_comm j i).symm)).hom x)) = _
  have heval (z : TensorProduct F2 (M.A j) (Coalgebra.dualSteenrod.X i)) :
      TensorProduct.dualDistrib F2 (M.A j) (Coalgebra.dualSteenrod.X i)
        ((e j).hom.dualMap φ ⊗ₜ[F2] (conjugation i).hom a) z =
      TensorProduct.dualDistrib F2 (W j) (Coalgebra.dualSteenrod.X i)
        (φ ⊗ₜ[F2] (conjugation i).hom a)
        ((e j ⊗ₘ 𝟙 (Coalgebra.dualSteenrod.X i)).hom z) := by
    let p : TensorProduct F2 (M.A j) (Coalgebra.dualSteenrod.X i) →ₗ[F2]
        TensorProduct F2 (W j) (Coalgebra.dualSteenrod.X i) :=
      (e j ⊗ₘ 𝟙 (Coalgebra.dualSteenrod.X i)).hom
    change _ = TensorProduct.dualDistrib F2 (W j) (Coalgebra.dualSteenrod.X i)
      (φ ⊗ₜ[F2] (conjugation i).hom a) (p z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul y z => rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [heval]
  have he := cofree_counit_projection W j i
  have hex := congrArg (fun f => f.hom
    ((eqToHom (congrArg M.A (add_comm j i).symm)).hom x)) he
  exact congrArg (TensorProduct.dualDistrib F2 (W j) (Coalgebra.dualSteenrod.X i)
    (φ ⊗ₜ[F2] (conjugation i).hom a)) hex


/-- When the Cauchy pairing is invertible, that actual free extension is an isomorphism. -/
private theorem comparison_free_iso (W : GrVect F2)
    (hP : IsIso (show degreewiseDual W ⊗ degreewiseDual Coalgebra.dualSteenrod.X ⟶
        degreewiseDual (W ⊗ Coalgebra.dualSteenrod.X) from
      fun _n => tensorObjDesc (fun i j h =>
        ModuleCat.ofHom ((tensorProjection W Coalgebra.dualSteenrod.X i j).hom.dualMap.comp
          (TensorProduct.dualDistrib F2 (W i) (Coalgebra.dualSteenrod.X j))) ≫
            eqToHom (congrArg (degreewiseDual (W ⊗ Coalgebra.dualSteenrod.X)) h)))) :
    IsIso (((GradedModule.leftTensorMonad steenrod).adj.homEquiv (degreewiseDual W)
      (dualLeftModule ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).cofree.obj W))).symm
        (degreewiseDualMap ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).ε.app W))) := by
  let freeToDualCofree (W : GrVect F2) :
      (GradedModule.leftTensorMonad steenrod).free.obj (degreewiseDual W) ⟶
        dualLeftModule ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).cofree.obj W) :=
    ((GradedModule.leftTensorMonad steenrod).adj.homEquiv _ _).symm
      (degreewiseDualMap ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).ε.app W))
  have dual_transport (X : GrVect F2) {i j : ℤ} (h : i=j)
      (φ : Module.Dual F2 (X i)) (x : X j) :
      (show Module.Dual F2 (X j) from
        (eqToHom (congrArg (degreewiseDual X) h)).hom φ) x =
      φ ((eqToHom (congrArg X h.symm)).hom x) := by
    subst j
    rfl
  have freeToDualCofree_eval (W : GrVect F2) (i j : ℤ)
      (a : Module.Dual F2 (Coalgebra.dualSteenrod.X i))
      (φ : Module.Dual F2 (W j)) (x : (W ⊗ Coalgebra.dualSteenrod.X) (i+j)) :
      (show Module.Dual F2 ((W ⊗ Coalgebra.dualSteenrod.X) (i+j)) from
        ((freeToDualCofree W).f (i+j)).hom
          ((ιTensorObj steenrod.X (degreewiseDual W) i j (i+j) rfl).hom (a ⊗ₜ[F2] φ))) x =
      TensorProduct.dualDistrib F2 (W j) (Coalgebra.dualSteenrod.X i)
        (φ ⊗ₜ[F2] (conjugation i).hom a)
        ((tensorProjection W Coalgebra.dualSteenrod.X j i).hom
          ((eqToHom (congrArg (show GrVect F2 from W ⊗ Coalgebra.dualSteenrod.X) (add_comm i j))).hom x)) := by
    exact comparison_free_eval W i j a φ x
  let cauchyDualPairing (X Y : GrVect F2) :
      degreewiseDual X ⊗ degreewiseDual Y ⟶ degreewiseDual (X ⊗ Y) :=
    fun _n => tensorObjDesc (fun i j h =>
      ModuleCat.ofHom ((tensorProjection X Y i j).hom.dualMap.comp
        (TensorProduct.dualDistrib F2 (X i) (Y j))) ≫
          eqToHom (congrArg (degreewiseDual (X ⊗ Y)) h))
  have freeToDualCofree_factorization (W : GrVect F2) :
      (freeToDualCofree W).f =
        (conjugation ⊗ₘ 𝟙 (degreewiseDual W)) ≫
          (β_ steenrod.X (degreewiseDual W)).hom ≫
            cauchyDualPairing W Coalgebra.dualSteenrod.X := by
    funext n
    apply tensorObj_ext
    intro i j hij
    subst n
    change ιTensorObj steenrod.X (degreewiseDual W) i j (i+j) rfl ≫ (freeToDualCofree W).f (i+j) =
      ιTensorObj steenrod.X (degreewiseDual W) i j (i+j) rfl ≫
        GradedObject.Monoidal.tensorHom conjugation (𝟙 (degreewiseDual W)) (i+j) ≫
          tensorObjDesc (fun a b h =>
            (β_ (steenrod.X a) (degreewiseDual W b)).hom ≫
              ιTensorObj (degreewiseDual W) steenrod.X b a (i+j) (by omega)) ≫
          cauchyDualPairing W Coalgebra.dualSteenrod.X (i+j)
    erw [ι_tensorHom_assoc conjugation (𝟙 (degreewiseDual W)) i j (i+j) rfl]
    erw [ι_tensorObjDesc_assoc]
    simp only [Category.assoc]
    erw [ι_tensorObjDesc]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change (show Module.Dual F2 ((W ⊗ Coalgebra.dualSteenrod.X) (i+j)) from
        ((freeToDualCofree W).f (i+j)).hom
          ((ιTensorObj steenrod.X (degreewiseDual W) i j (i+j) rfl).hom (a ⊗ₜ[F2] φ))) x = _
    rw [freeToDualCofree_eval]
    change _ = (show Module.Dual F2 ((W ⊗ Coalgebra.dualSteenrod.X) (i+j)) from
      (eqToHom (congrArg (degreewiseDual (W ⊗ Coalgebra.dualSteenrod.X)) (add_comm j i))).hom
        ((tensorProjection W Coalgebra.dualSteenrod.X j i).hom.dualMap
          (TensorProduct.dualDistrib F2 (W j) (Coalgebra.dualSteenrod.X i)
            (φ ⊗ₜ[F2] (conjugation i).hom a)))) x
    rw [dual_transport]
    rfl
    all_goals omega
  classical
  have hχ : conjugation ≫ conjugation = 𝟙 steenrod.X := by
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change Module.Dual F2 (Coalgebra.Carrier n) at φ
    apply LinearMap.ext
    intro x
    change φ ((Coalgebra.Antipode.map n).hom ((Coalgebra.Antipode.map n).hom x)) = φ x
    exact congrArg φ (congrArg (fun f => f.hom x) (congrFun Coalgebra.Antipode.map_involutive n))
  letI : IsIso conjugation := ⟨⟨conjugation, hχ, hχ⟩⟩
  let pIso : degreewiseDual W ⊗ degreewiseDual Coalgebra.dualSteenrod.X ≅
      degreewiseDual (W ⊗ Coalgebra.dualSteenrod.X) :=
    @asIso _ _ _ _ (cauchyDualPairing W Coalgebra.dualSteenrod.X) hP
  letI : IsIso (freeToDualCofree W).f := by
    rw [freeToDualCofree_factorization]
    change IsIso (((asIso conjugation ⊗ᵢ Iso.refl (degreewiseDual W)) ≪≫
      (β_ steenrod.X (degreewiseDual W)) ≪≫ pIso).hom)
    infer_instance
  have hfi : IsIso (freeToDualCofree W) :=
    Monad.algebra_iso_of_iso (GradedModule.leftTensorMonad steenrod) (freeToDualCofree W)
  exact hfi

/-- The finite Milnor word bases and the two adjunctions make the actual transpose bijective on each resolution Hom space. -/
private theorem comparison_term_duality (R : Ext.CobarResolution) (s : ℕ) (t : ℤ) :
    Function.Bijective (fun f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s =>
      dualLeftMap f ≫ (trivialDualIso t).hom) :=
  set_option backward.isDefEq.respectTransparency false in by
  classical
  have dual_hom_bijective (V W : GrVect F2)
      (hW : ∀ n, Module.Finite F2 (W n)) :
      Function.Bijective (fun f : V ⟶ W => degreewiseDualMap f) := by
    classical
    constructor
    · intro f g h
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Module.eval_apply_injective F2
      apply LinearMap.ext
      intro φ
      exact congrArg (fun q : degreewiseDual W ⟶ degreewiseDual V => (show Module.Dual F2 (V n) from (q n).hom φ) x) h
    · intro g
      letI (n : ℤ) : Module.Finite F2 (W n) := hW n
      let f : V ⟶ W := fun n => ModuleCat.ofHom
        ((Module.evalEquiv F2 (W n)).symm.toLinearMap.comp
          ((g n).hom.dualMap.comp (Module.Dual.eval F2 (V n))))
      refine ⟨f, ?_⟩
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      change (show Module.Dual F2 (W n) from φ) ((Module.evalEquiv F2 (W n)).symm ((g n).hom.dualMap
        (Module.Dual.eval F2 (V n) x))) = (show Module.Dual F2 (V n) from (g n).hom φ) x
      rw [Module.apply_evalEquiv_symm_apply]
      rfl
  let freeMap (W : GrVect F2) :
      (GradedModule.leftTensorMonad steenrod).free.obj (degreewiseDual W) ⟶
        dualLeftModule ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).cofree.obj W) :=
    ((GradedModule.leftTensorMonad steenrod).adj.homEquiv _ _).symm
      (degreewiseDualMap ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).ε.app W))

  have cofree_hom_bijective (W : GrVect F2) (t : ℤ)
      (hW : ∀ n, Module.Finite F2 (W n)) [IsIso (freeMap W)] :
      Function.Bijective (fun f : Ext.trivialAt t ⟶
          (GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).cofree.obj W =>
        dualLeftMap f ≫ (trivialDualIso t).hom) := by
    let G := GradedComodule.rightTensorComonad Coalgebra.dualSteenrod
    let T := GradedModule.leftTensorMonad steenrod
    let A := (G.adj.homEquiv (Ext.trivialAt t) W).symm
    let B := (Iso.homCongr (asIso (freeMap W)).symm (Iso.refl (trivialAt t))).trans
      (T.adj.homEquiv (degreewiseDual W) (trivialAt t))
    let U : ((Ext.trivialAt t).A ⟶ W) → (degreewiseDual W ⟶ (trivialAt t).A) :=
      fun f => degreewiseDualMap f ≫ (trivialDualIso t).hom.f
    have hU : Function.Bijective U := by
      let E : (degreewiseDual W ⟶ (dualLeftModule (Ext.trivialAt t)).A) ≃
          (degreewiseDual W ⟶ (trivialAt t).A) :=
        Iso.homCongr (Iso.refl _) ((Monad.forget T).mapIso (trivialDualIso t))
      exact E.bijective.comp (dual_hom_bijective _ W hW)
    have hcompat (f : Ext.trivialAt t ⟶ G.cofree.obj W) :
        B (dualLeftMap f ≫ (trivialDualIso t).hom) = U (A f) := by
      change T.adj.homEquiv _ _ (freeMap W ≫ (dualLeftMap f ≫ (trivialDualIso t).hom)) = _
      rw [T.adj.homEquiv_naturality_right]
      change T.adj.homEquiv _ _ ((T.adj.homEquiv _ _).symm _) ≫ _ = _
      rw [Equiv.apply_symm_apply]
      funext n
      apply ModuleCat.hom_ext
      rfl
    constructor
    · intro f g h
      apply A.injective
      apply hU.injective
      rw [← hcompat, ← hcompat]
      exact congrArg B h
    · intro f
      obtain ⟨g, hg⟩ := hU.surjective (B f)
      obtain ⟨g, rfl⟩ := A.surjective g
      exact ⟨g, B.injective ((hcompat g).trans hg)⟩
  have term_hom_bijective (R : Ext.CobarResolution) (s : ℕ) (t : ℤ)
      (hC : Function.Bijective (fun f : Ext.trivialAt t ⟶ Ext.Cofree.term s =>
        dualLeftMap f ≫ (trivialDualIso t).hom)) :
      Function.Bijective (fun f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s =>
        dualLeftMap f ≫ (trivialDualIso t).hom) := by
    let A := Iso.homCongr (Iso.refl (Ext.trivialAt t)) (R.termIso s)
    let I := dualToLeftModule.mapIso (R.termIso s).op
    let B := Iso.homCongr I.symm (Iso.refl (trivialAt t))
    have hc (f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s) :
        B (dualLeftMap f ≫ (trivialDualIso t).hom) =
          dualLeftMap (A f) ≫ (trivialDualIso t).hom := by
      apply Monad.Algebra.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      rfl
    constructor
    · intro f g h
      apply A.injective
      apply hC.injective
      exact (hc f).symm.trans ((congrArg B h).trans (hc g))
    · intro f
      obtain ⟨g, hg⟩ := hC.surjective (B f)
      obtain ⟨g, rfl⟩ := A.surjective g
      exact ⟨g, B.injective ((hc g).trans hg)⟩
  have comparison_cofree_duality (s : ℕ) :
      (∀ n : ℤ, Module.Finite F2 (Ext.Cofree.wordSpace s n)) ∧
      IsIso (((GradedModule.leftTensorMonad steenrod).adj.homEquiv
        (degreewiseDual (Ext.Cofree.wordSpace s)) (dualLeftModule (Ext.Cofree.term s))).symm
          (degreewiseDualMap ((GradedComodule.rightTensorComonad Coalgebra.dualSteenrod).ε.app
            (Ext.Cofree.wordSpace s)))) := by
    classical
    have boundedWeight_finite (n : ℕ) :
        Finite {d : ℕ →₀ ℕ // slotWeight d ≤ n} := by
      classical
      have hpos (j : ℕ) : 2 ^ (j + 1) - 1 ≠ 0 := by
        have h := (Nat.lt_two_pow_self (n := j + 1))
        omega
      let f : {d : ℕ →₀ ℕ // slotWeight d ≤ n} → (Fin (n+1) → Fin (n+1)) :=
        fun d j => ⟨d.val j.val, Nat.lt_succ_of_le
          ((Finsupp.le_weight (fun j => 2 ^ (j+1)-1) (hpos j) d.val).trans d.property)⟩
      apply Finite.of_injective f
      intro d e h
      apply Subtype.ext
      apply Finsupp.ext
      intro j
      by_cases hj : j < n + 1
      · exact congrArg Fin.val (congrFun h ⟨j,hj⟩)
      · have hz (a : {d : ℕ →₀ ℕ // slotWeight d ≤ n}) : a.val j = 0 := by
          by_contra hne
          have hw := (Finsupp.le_weight_of_ne_zero'
            (fun k : ℕ => 2 ^ (k+1)-1) hne).trans a.property
          have hp := (Nat.lt_two_pow_self (n := j+1))
          omega
        rw [hz d, hz e]
    have monomialFinite (n : ℤ) : Finite (MilnorMonomial n) := by
      let f : MilnorMonomial n → {d : ℕ →₀ ℕ // slotWeight d ≤ n.toNat} :=
        fun d => ⟨d.val, by omega⟩
      letI := boundedWeight_finite n.toNat
      apply Finite.of_injective f
      intro d e h
      exact Subtype.ext (congrArg (fun a : {d : ℕ →₀ ℕ // slotWeight d ≤ n.toNat} => a.val) h)
    have wordFinite (n : ℤ) : Finite (MilnorWord s n) := by
      classical
      let f : MilnorWord s n → (Fin s → {d : ℕ →₀ ℕ // slotWeight d ≤ n.toNat}) :=
        fun d i => ⟨d.val i, by
          have hle : (slotWeight (d.val i) : ℤ) ≤ wordDegree d.val := by
            exact Finset.single_le_sum (fun j _ => Int.natCast_nonneg _) (Finset.mem_univ i)
          have hdeg := d.property.1
          omega⟩
      letI := boundedWeight_finite n.toNat
      apply Finite.of_injective f
      intro d e h
      apply Subtype.ext
      funext i
      exact congrArg Subtype.val (congrFun h i)
    letI (n : ℤ) : Finite (MilnorMonomial n) := monomialFinite n
    letI (n : ℤ) : Finite (MilnorWord s n) := wordFinite n
    have totalFinite (n : ℤ) :
        Finite (Σ q : {p : ℤ × ℤ // p.1+p.2=n}, MilnorWord s q.val.1 × MilnorMonomial q.val.2) := by
      let Q := {p : ℤ × ℤ // p.1+p.2=n}
      let D := Σ q : Q, MilnorWord s q.val.1 × MilnorMonomial q.val.2
      let B := {d : ℕ →₀ ℕ // slotWeight d ≤ n.toNat}
      have hi (d : D) : 0 ≤ d.1.val.1 := by
        rw [← d.2.1.property.1]
        exact Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
      have hj (d : D) : 0 ≤ d.1.val.2 := by
        rw [← d.2.2.property]
        exact Int.natCast_nonneg _
      let f : D → (Fin s → B) × B := fun d =>
        (fun i => ⟨d.2.1.val i, by
          have hle : (slotWeight (d.2.1.val i) : ℤ) ≤ wordDegree d.2.1.val :=
            Finset.single_le_sum (fun j _ => Int.natCast_nonneg _) (Finset.mem_univ i)
          have hdeg := d.2.1.property.1
          have hsum := d.1.property
          have hnonneg := hj d
          omega⟩,
        ⟨d.2.2.val, by
          have hdeg := d.2.2.property
          have hsum := d.1.property
          have hnonneg := hi d
          omega⟩)
      have hf : Function.Injective f := by
        rintro ⟨⟨⟨i,j⟩,hij⟩,w,m⟩ ⟨⟨⟨i',j'⟩,hij'⟩,w',m'⟩ h
        have hw : w.val = w'.val := by
          funext a
          exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) a)
        have hm : m.val = m'.val := congrArg (fun x => x.2.val) h
        have hii : i=i' := w.property.1.symm.trans ((congrArg wordDegree hw).trans w'.property.1)
        have hjj : j=j' := m.property.symm.trans ((congrArg (fun d => (slotWeight d : ℤ)) hm).trans m'.property)
        subst i'
        subst j'
        have hw' : w=w' := Subtype.ext hw
        have hm' : m=m' := Subtype.ext hm
        subst w'
        subst m'
        rfl
      letI : Finite B := boundedWeight_finite n.toNat
      exact Finite.of_injective f hf
    let W := Ext.Cofree.wordSpace s
    let P : degreewiseDual W ⊗ degreewiseDual Coalgebra.dualSteenrod.X ⟶
        degreewiseDual (W ⊗ Coalgebra.dualSteenrod.X) :=
      fun _n => tensorObjDesc (fun i j h =>
        ModuleCat.ofHom ((tensorProjection W Coalgebra.dualSteenrod.X i j).hom.dualMap.comp
          (TensorProduct.dualDistrib F2 (W i) (Coalgebra.dualSteenrod.X j))) ≫
            eqToHom (congrArg (degreewiseDual (W ⊗ Coalgebra.dualSteenrod.X)) h))
    have hp (n : ℤ) : IsIso (P n) := by
      letI := totalFinite n
      rw [ConcreteCategory.isIso_iff_bijective]
      exact comparison_pairing_bijective W Coalgebra.dualSteenrod.X
        (MilnorWord s) MilnorMonomial
        (fun _ => Finsupp.basisSingleOne) (fun _ => Finsupp.basisSingleOne) n
    letI (n : ℤ) : IsIso (P n) := hp n
    have hP : IsIso P := GradedObject.isIso_of_isIso_apply P
    refine ⟨?_, comparison_free_iso W hP⟩
    intro n
    exact Module.Finite.of_basis (Finsupp.basisSingleOne (R := F2) (ι := MilnorWord s n))
  obtain ⟨hW, hI⟩ := comparison_cofree_duality s
  apply term_hom_bijective R s t
  letI : IsIso (freeMap (Ext.Cofree.wordSpace s)) := hI
  exact cofree_hom_bijective (Ext.Cofree.wordSpace s) t hW

/-- Compatible Hom equivalences descend through the two extMk quotient presentations, including cohomological degree zero. -/
private theorem comparison_ext_transfer (R : Ext.CobarResolution) (t : ℤ)
    (E : ∀ s : ℕ, (Ext.trivialAt t ⟶ R.resolution.cocomplex.X s) ≃ₗ[F2]
      ((dualCobarResolution R).complex.X s ⟶ trivialAt t))
    (hE : ∀ s (f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s),
      E (s + 1) (f ≫ R.resolution.cocomplex.d s (s + 1)) =
        (dualCobarResolution R).complex.d (s + 1) s ≫ E s f) :
    ∃ e : ∀ s : ℕ, Ext.SphereExt s t ≃ₗ[F2] SphereExt s t,
      ∀ s (f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s)
        (hf : f ≫ R.resolution.cocomplex.d s (s + 1) = 0),
        ∃ hf' : (dualCobarResolution R).complex.d (s + 1) s ≫ E s f = 0,
          e s (R.resolution.extMk f (s + 1) rfl hf) =
            (dualCobarResolution R).extMk (E s f) (s + 1) rfl hf' :=
  set_option backward.isDefEq.respectTransparency false in by
  classical
  have source_zero (R : Ext.CobarResolution) (t : ℤ)
      (f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X 0)
      (hf : f ≫ R.resolution.cocomplex.d 0 1 = 0) :
      R.resolution.extMk f 1 rfl hf = 0 ↔ f = 0 := by
    rw [← R.resolution.extEquivCohomologyClass.apply_eq_iff_eq,
      R.resolution.extEquivCohomologyClass_extMk,
      R.resolution.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
    rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by omega)]
    constructor
    · rintro ⟨g, hg⟩
      have hz := CochainComplex.isZero_of_isStrictlyGE R.resolution.cochainComplex 0 (-1) (by omega)
      have hg0 : g = 0 := hz.eq_of_tgt _ _
      rw [hg0, zero_comp] at hg
      exact (cancel_mono (R.resolution.cochainComplexXIso 0 0 rfl).inv).mp (by simpa using hg.symm)
    · intro h
      subst f
      exact ⟨0, by simp⟩
  have target_zero (R : Ext.CobarResolution) (t : ℤ)
      (f : (dualCobarResolution R).complex.X 0 ⟶ trivialAt t)
      (hf : (dualCobarResolution R).complex.d 1 0 ≫ f = 0) :
      (dualCobarResolution R).extMk f 1 rfl hf = 0 ↔ f = 0 := by
    let P := dualCobarResolution R
    rw [← P.extEquivCohomologyClass.apply_eq_iff_eq,
      P.extEquivCohomologyClass_extMk,
      P.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
    rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by omega)]
    constructor
    · rintro ⟨g, hg⟩
      have hz := CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 1 (by omega)
      have hg0 : g = 0 := hz.eq_of_src _ _
      rw [hg0, comp_zero] at hg
      exact (cancel_epi (P.cochainComplexXIso 0 0 rfl).hom).mp (by simpa using hg.symm)
    · intro h
      subst f
      exact ⟨0, by simp⟩

  let P := dualCobarResolution R
  have cyc (s : ℕ) (f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s) :
      f ≫ R.resolution.cocomplex.d s (s + 1) = 0 ↔
        P.complex.d (s + 1) s ≫ E s f = 0 := by
    rw [← hE, ← (E (s + 1)).map_zero, (E (s + 1)).injective.eq_iff]
  let C (s : ℕ) := LinearMap.ker
    (Linear.rightComp F2 (Ext.trivialAt t) (R.resolution.cocomplex.d s (s + 1)))
  let a (s : ℕ) : C s →ₗ[F2] Ext.SphereExt s t :=
    AddMonoidHom.toZModLinearMap 2 {
      toFun := fun f => R.resolution.extMk f.val (s + 1) rfl f.property
      map_zero' := R.resolution.extMk_zero (s + 1) rfl
      map_add' := fun f g => (R.resolution.add_extMk f.val g.val (s + 1) rfl
        f.property g.property).symm }
  let b (s : ℕ) : C s →ₗ[F2] SphereExt s t :=
    AddMonoidHom.toZModLinearMap 2 {
      toFun := fun f => P.extMk (E s f.val) (s + 1) rfl ((cyc s f.val).mp f.property)
      map_zero' := by simp
      map_add' := fun f g => by
        simpa using (P.add_extMk (E s f.val) (E s g.val) (s + 1) rfl
          ((cyc s f.val).mp f.property) ((cyc s g.val).mp g.property)).symm }
  have ha (s : ℕ) : Function.Surjective (a s) := by
    intro x
    obtain ⟨f, hf, h⟩ := R.resolution.extMk_surjective x (s + 1) rfl
    exact ⟨⟨f, hf⟩, h⟩
  have hb (s : ℕ) : Function.Surjective (b s) := by
    intro x
    obtain ⟨f, hf, h⟩ := P.extMk_surjective x (s + 1) rfl
    obtain ⟨g, rfl⟩ := (E s).surjective f
    exact ⟨⟨g, (cyc s g).mpr hf⟩, h⟩
  have hk (s : ℕ) : LinearMap.ker (a s) = LinearMap.ker (b s) := by
    ext f
    change R.resolution.extMk f.val (s + 1) rfl f.property = 0 ↔
      P.extMk (E s f.val) (s + 1) rfl ((cyc s f.val).mp f.property) = 0
    cases s with
    | zero =>
      rw [source_zero R t, target_zero R t, ← (E 0).map_zero, (E 0).injective.eq_iff]
    | succ s =>
      rw [R.resolution.extMk_eq_zero_iff _ _ _ _ s rfl,
        P.extMk_eq_zero_iff _ _ _ _ s rfl]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨E s g, (hE s g).symm.trans (congrArg (E (s + 1)) hg)⟩
      · rintro ⟨g, hg⟩
        obtain ⟨g, rfl⟩ := (E s).surjective g
        refine ⟨g, (E (s + 1)).injective ?_⟩
        exact (hE s g).trans hg
  let e (s : ℕ) := ((a s).quotKerEquivOfSurjective (ha s)).symm |>.trans
    ((Submodule.quotEquivOfEq _ _ (hk s)).trans
      ((b s).quotKerEquivOfSurjective (hb s)))
  refine ⟨e, fun s f hf => ⟨(cyc s f).mp hf, ?_⟩⟩
  change e s (a s ⟨f, hf⟩) = b s ⟨f, hf⟩
  simp [e]

/-- Same-degree dualization of the fixed cofree resolution induces the
left-module Ext comparison, with its exact representative formula. -/
theorem exists_dualCobarComparison (R : Ext.CobarResolution) :
    ∃ e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t,
      PreservesDualCobarRepresentatives R e := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    let dual_hom_linear (M : SourceComodule) (t : ℤ) :
        (Ext.trivialAt t ⟶ M) →ₗ[F2] (dualLeftModule M ⟶ trivialAt t) :=
      AddMonoidHom.toZModLinearMap 2 {
        toFun := fun f => dualLeftMap f ≫ (trivialDualIso t).hom
        map_zero' := by
          have h : dualLeftMap (0 : Ext.trivialAt t ⟶ M) = 0 := by
            apply Monad.Algebra.Hom.ext
            funext n
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro φ
            apply LinearMap.ext
            intro x
            change (show Module.Dual F2 (M.A n) from φ) 0 = 0
            exact map_zero _
          rw [h, zero_comp]
        map_add' := fun f g => by
          have h : dualLeftMap (f + g) = dualLeftMap f + dualLeftMap g := by
            apply Monad.Algebra.Hom.ext
            funext n
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro φ
            apply LinearMap.ext
            intro x
            change (show Module.Dual F2 (M.A n) from φ) ((f.f n).hom x + (g.f n).hom x) = _
            exact map_add _ _ _
          rw [h, Preadditive.add_comp] }
    have hb (s : ℕ) (t : ℤ) : Function.Bijective
        (dual_hom_linear (R.resolution.cocomplex.X s) t) := by
      exact comparison_term_duality R s t
    let E (t : ℤ) (s : ℕ) := LinearEquiv.ofBijective
      (dual_hom_linear (R.resolution.cocomplex.X s) t) (hb s t)
    have hc (t : ℤ) (s : ℕ) (f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s) :
        E t (s + 1) (f ≫ R.resolution.cocomplex.d s (s + 1)) =
          (dualCobarResolution R).complex.d (s + 1) s ≫ E t s f := by
      apply Monad.Algebra.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      rfl
    choose e he using fun t => comparison_ext_transfer R t (E t) (hc t)
    exact ⟨fun s t => e t s, fun s t f hf => he t s f hf⟩


/-- Agreement on all actual resolution cocycles leaves no freedom to choose
an unrelated linear equivalence. This also covers cohomological degree zero. -/
theorem dualCobarComparison_unique (R : Ext.CobarResolution)
    {e e' : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t}
    (he : PreservesDualCobarRepresentatives R e)
    (he' : PreservesDualCobarRepresentatives R e') : e = e' := by
  funext s t
  apply LinearEquiv.ext
  intro x
  obtain ⟨f, hf, rfl⟩ := R.resolution.extMk_surjective x (s + 1) rfl
  obtain ⟨_, h⟩ := he s t f hf
  obtain ⟨_, h'⟩ := he' s t f hf
  exact h.trans h'.symm

end KIP126.Steenrod.Milnor.Module
