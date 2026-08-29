/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Adjoint quadruples

This file concerns adjoint quadruples `L ⊣ F ⊣ G ⊣ R` of functors `L G : C ⥤ D`, `F R : D ⥤ C`.
We bundle the adjunctions in a structure `Quadruple L F G R` and make the two triples `Triple L F G`
and `Triple F G R` accessible as `Quadruple.leftTriple` and `Quadruple.rightTriple`.

Currently the only two results are the following:
* When `F` and `R` are fully faithful, the components of the induced natural transformation `G ⟶ L`
  are epimorphisms iff the components of the natural transformation `F ⟶ R` are monomorphisms.
* When `L` and `G` are fully faithful, the components of the induced natural transformation `L ⟶ G`
  are epimorphisms iff the components of the natural transformation `R ⟶ F` are monomorphisms.

This is in particular relevant for the adjoint quadruples `π₀ ⊣ disc ⊣ Γ ⊣ codisc` that appear in
cohesive topoi, and can be found e.g. as proposition 2.7
[here](https://ncatlab.org/nlab/show/cohesive+topos).

Note that by `Triple.fullyFaithfulEquiv`, in an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` `L` is fully
faithful iff `G` is and `F` is fully faithful iff `R` is; these lemmas thus cover all cases in which
some of the functors are fully faithful. We opt to include only those typeclass assumptions that are
needed for the theorem statements, so some lemmas require only e.g. `F` to be fully faithful when
really this means `F` and `R` both must be.
-/

@[expose] public section

open CategoryTheory Limits Functor Adjunction Triple

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (L : C ⥤ D) (F : D ⥤ C) (G : C ⥤ D) (R : D ⥤ C)

/--
Definition of `CategoryTheory.Adjunction.Quadruple` / `CategoryTheory.Adjunction.Quadruple` 的定义

English:
structure CategoryTheory.Adjunction.Quadruple
  parameters: where
  axioms and operations (3):
    - adj₁ : L ⊣ F
    - adj₂ : F ⊣ G
    - adj₃ : G ⊣ R

中文:
结构 范畴论.伴随.四元组
  参数: where
  公理与运算 (3 个):
    - adj₁ : L ⊣ F
    - adj₂ : F ⊣ G
    - adj₃ : G ⊣ R
-/
structure CategoryTheory.Adjunction.Quadruple where
  /-- Adjunction `L ⊣ F` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
  adj₁ : L ⊣ F
  /-- Adjunction `F ⊣ G` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
  adj₂ : F ⊣ G
  /-- Adjunction `G ⊣ R` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
  adj₃ : G ⊣ R

namespace CategoryTheory.Adjunction.Quadruple

variable {L F G R} (q : Quadruple L F G R)

/-- The left part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
/--
Definition of `leftTriple` / `leftTriple` 的定义

English:
definition leftTriple
  signature: : Triple L F G where
  body: q.adj₁
  adj₂ := q.adj₂

中文:
定义 leftTriple
  签名: : 三元组 L F G where
  定义体: q.adj₁
  adj₂ := q.adj₂

Depends on / 依赖: q.adj
-/
def leftTriple : Triple L F G where
  adj₁ := q.adj₁
  adj₂ := q.adj₂

/-- The right part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
/--
Definition of `rightTriple` / `rightTriple` 的定义

English:
definition rightTriple
  signature: : Triple F G R where
  body: q.adj₂
  adj₂ := q.adj₃

中文:
定义 rightTriple
  签名: : 三元组 F G R where
  定义体: q.adj₂
  adj₂ := q.adj₃

Depends on / 依赖: q.adj
-/
def rightTriple : Triple F G R where
  adj₁ := q.adj₂
  adj₂ := q.adj₃

/-- The adjoint quadruple `R.op ⊣ G.op ⊣ F.op ⊣ L.op` dual to an
adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : Quadruple R.op G.op F.op L.op where
  body: q.adj₃.op
  adj₂ := q.adj₂.op
  adj₃ := q.adj₁.op

@[simp]

中文:
定义 op
  签名: : 四元组 R.op G.op F.op L.op where
  定义体: q.adj₃.op
  adj₂ := q.adj₂.op
  adj₃ := q.adj₁.op

@[simp]
-/
protected def op : Quadruple R.op G.op F.op L.op where
  adj₁ := q.adj₃.op
  adj₂ := q.adj₂.op
  adj₃ := q.adj₁.op

@[simp]
/--
lemma `op_leftTriple` / 引理 `op_leftTriple`

English:
lemma op_leftTriple
  statement: q.op.leftTriple = q.rightTriple.op
  proof: rfl

@[simp]

中文:
引理 op_leftTriple
  结论: q.op.leftTriple = q.rightTriple.op
  证明: rfl

@[simp]
-/
lemma op_leftTriple : q.op.leftTriple = q.rightTriple.op := rfl

@[simp]
/--
lemma `op_rightTriple` / 引理 `op_rightTriple`

English:
lemma op_rightTriple
  statement: q.op.rightTriple = q.leftTriple.op
  proof: rfl

中文:
引理 op_rightTriple
  结论: q.op.rightTriple = q.leftTriple.op
  证明: rfl
-/
lemma op_rightTriple : q.op.rightTriple = q.leftTriple.op := rfl

section RightFullyFaithful

variable [F.Full] [F.Faithful]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app` / 引理 `epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app`

English:
lemma epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app
  proof: by
  simp_rw [mono_leftToRight_app_iff_mono_adj₂_unit_app, rightToLeft_eq_counits]
  dsimp
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj,
    whiskerLeft_app, Category.comp_id, Category.id_comp]
  simp_rw [epi_comp_iff_of_epi, epi_iff_forall_injective, mono_iff_forall_injective

中文:
引理 epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app
  证明: by
  simp_rw [mono_leftToRight_app_iff_mono_adj₂_unit_app, rightToLeft_eq_counits]
  dsimp
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj,
    whiskerLeft_app, Category.comp_id, Category.id_comp]
  simp_rw [epi_comp_iff_of_epi, epi_iff_forall_injective, mono_iff_forall_injective

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Function, Function.comp_def, Functor, Functor.comp_obj, Functor.id_obj, NatIso, NatIso.isIso_inv_app, comp_def, comp_id, comp_injective, comp_obj, epi_comp_iff_of_epi, epi_iff_forall_injective, forall_comm, forall_congr, homEquiv, homEquiv_naturality_left
-/
lemma epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app :
    (forall X, Epi (q.leftTriple.rightToLeft.app X)) ↔ forall X, Mono (q.rightTriple.leftToRight.app X) := by
  simp_rw [mono_leftToRight_app_iff_mono_adj₂_unit_app, rightToLeft_eq_counits]
  dsimp
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj,
    whiskerLeft_app, Category.comp_id, Category.id_comp]
  simp_rw [epi_comp_iff_of_epi, epi_iff_forall_injective, mono_iff_forall_injective]
  rw [forall_comm]
  refine forall_congr' fun X => forall_congr' fun Y => ?_
  rw [← (q.adj₁.homEquiv _ _).comp_injective _]
  simp_rw [Function.comp_def, q.adj₁.homEquiv_naturality_left]
  refine ((q.adj₁.homEquiv _ _).injective_comp fun f => _).trans ?_
  rw [← ((q.adj₂.homEquiv _ _).trans (q.adj₃.homEquiv _ _)).comp_injective _]
  simp [Function.comp_def, ← q.adj₂.homEquiv_symm_id, ← q.adj₂.homEquiv_naturality_right_symm,
    ← q.adj₃.homEquiv_id, ← q.adj₃.homEquiv_naturality_left]

/--
lemma `epi_leftTriple_rightToLeft_iff_mono_rightTriple_leftToRight` / 引理 `epi_leftTriple_rightToLeft_iff_mono_rightTriple_leftToRight`

English:
lemma epi_leftTriple_rightToLeft_iff_mono_rightTriple_leftToRight
  given: [HasPullbacks C] [HasPushouts D]
  proof: by
  rw [NatTrans.epi_iff_epi_app]; rw [NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app

中文:
引理 epi_leftTriple_rightToLeft_iff_mono_rightTriple_leftToRight
  条件: [有Pullbacks C] [有Pushouts D]
  证明: by
  rw [NatTrans.epi_iff_epi_app]; rw [NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app

Depends on / 依赖: NatTrans, NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app, epi_iff_epi_app, epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app, mono_iff_mono_app, q.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app
-/
lemma epi_leftTriple_rightToLeft_iff_mono_rightTriple_leftToRight [HasPullbacks C] [HasPushouts D] :
    Epi q.leftTriple.rightToLeft ↔ Mono q.rightTriple.leftToRight := by
  rw [NatTrans.epi_iff_epi_app]; rw [NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app

end RightFullyFaithful

section LeftFullyFaithful

variable [L.Full] [L.Faithful] [G.Full] [G.Faithful]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app` / 引理 `epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app`

English:
lemma epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app
  proof: by
  have h := q.op.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app
  rw [← (Opposite.equivToOpposite (α := C)).forall_congr_right] at h
  rw [← (Opposite.equivToOpposite (α := D)).forall_congr_right] at h
  simpa using h.symm

中文:
引理 epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app
  证明: by
  have h := q.op.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app
  rw [← (Opposite.equivToOpposite (α := C)).forall_congr_right] at h
  rw [← (Opposite.equivToOpposite (α := D)).forall_congr_right] at h
  simpa using h.symm

Depends on / 依赖: Opposite, Opposite.equivToOpposite, epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app, equivToOpposite, forall_congr_right, h.symm, q.op.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app
-/
lemma epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app :
    (forall X, Epi (q.leftTriple.leftToRight.app X)) ↔ forall X, Mono (q.rightTriple.rightToLeft.app X) := by
  have h := q.op.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app
  rw [← (Opposite.equivToOpposite (α := C)).forall_congr_right] at h
  rw [← (Opposite.equivToOpposite (α := D)).forall_congr_right] at h
  simpa using h.symm

/--
lemma `epi_leftTriple_leftToRight_iff_mono_rightTriple_rightToLeft` / 引理 `epi_leftTriple_leftToRight_iff_mono_rightTriple_rightToLeft`

English:
lemma epi_leftTriple_leftToRight_iff_mono_rightTriple_rightToLeft
  given: [HasPullbacks C] [HasPushouts D]
  proof: by
  rw [NatTrans.epi_iff_epi_app]; rw [NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app

中文:
引理 epi_leftTriple_leftToRight_iff_mono_rightTriple_rightToLeft
  条件: [有Pullbacks C] [有Pushouts D]
  证明: by
  rw [NatTrans.epi_iff_epi_app]; rw [NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app

Depends on / 依赖: NatTrans, NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app, epi_iff_epi_app, epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app, mono_iff_mono_app, q.epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app
-/
lemma epi_leftTriple_leftToRight_iff_mono_rightTriple_rightToLeft [HasPullbacks C] [HasPushouts D] :
    Epi q.leftTriple.leftToRight ↔ Mono q.rightTriple.rightToLeft := by
  rw [NatTrans.epi_iff_epi_app]; rw [NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app

end LeftFullyFaithful

end CategoryTheory.Adjunction.Quadruple
