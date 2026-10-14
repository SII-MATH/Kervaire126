module

public import KIP126.Def.Algebra.Module.Basis.Coproduct.Data

@[expose] public section

namespace KIP126.Foundation
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- The original basis cofan is a coproduct in actual abelian groups.
Its universal map sums the finitely supported original basis coordinates. -/
noncomputable def basisAdditiveCofan_isColimit {R V J : Type u} [Ring R]
    [AddCommGroup V] [Module R V] (b : Module.Basis J R V) :
    IsColimit (basisAdditiveCofan b) := by
  classical
  refine Cofan.IsColimit.mk _ (fun c => AddCommGrpCat.ofHom
    ((Finsupp.liftAddHom (fun j => (c.inj j).hom)).comp b.repr.toAddMonoidHom)) ?_ ?_
  · intro c j
    apply AddCommGrpCat.ext
    intro r
    change Finsupp.liftAddHom (fun j => (c.inj j).hom) (b.repr (r • b j)) = c.inj j r
    rw [map_smul,b.repr_self,Finsupp.smul_single,smul_eq_mul,mul_one,
      Finsupp.liftAddHom_apply_single]
  · intro c m hm
    apply AddCommGrpCat.ext
    intro x
    obtain ⟨v,rfl⟩ := b.repr.symm.surjective x
    change m (b.repr.symm v) = Finsupp.liftAddHom (fun j => (c.inj j).hom)
      (b.repr (b.repr.symm v))
    rw [b.repr.apply_symm_apply]
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add,hv,hw]
    | single j r =>
      rw [b.repr_symm_single,Finsupp.liftAddHom_apply_single]
      exact ConcreteCategory.congr_hom (hm j) r

end KIP126.Foundation
