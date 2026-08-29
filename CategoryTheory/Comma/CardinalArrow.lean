/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Cardinal of Arrow

We obtain various results about the cardinality of `Arrow C`. For example,
if `C` is a (small) category, `Arrow C` is finite iff `FinCategory C` holds.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

/--
lemma `Arrow.finite_iff` / 引理 `Arrow.finite_iff`

English:
lemma Arrow.finite_iff
  given: (C : Type u) [SmallCategory C]
  proof: by
  constructor
  · intro
    refine ⟨?_, fun a b => ?_⟩
    · have := Finite.of_injective (fun (a : C) => Arrow.mk (𝟙 a))
        (fun _ _ => congr_arg Comma.left)
      apply Fintype.ofFinite
    · have := Finite.of_injective (fun (f : a ⟶ b) => Arrow.mk f)
        (fun f g h => by
          chan

中文:
引理 箭头.finite_iff
  条件: (C : 类型u) [小范畴 C]
  证明: by
  constructor
  · intro
    refine ⟨?_, fun a b => ?_⟩
    · have := Finite.of_injective (fun (a : C) => Arrow.mk (𝟙 a))
        (fun _ _ => congr_arg Comma.left)
      apply Fintype.ofFinite
    · have := Finite.of_injective (fun (f : a ⟶ b) => Arrow.mk f)
        (fun f g h => by
          chan

Depends on / 依赖: Arrow.equivSigma, Arrow.mk, Comma.left, Finite, Finite.of_injective, Fintype, Fintype.ofEquiv, Fintype.ofFinite, congr_arg, equivSigma, infer_instance, ofEquiv, ofFinite, of_injective
-/
lemma Arrow.finite_iff (C : Type u) [SmallCategory C] :
    Finite (Arrow C) ↔ Nonempty (FinCategory C) := by
  constructor
  · intro
    refine ⟨?_, fun a b => ?_⟩
    · have := Finite.of_injective (fun (a : C) => Arrow.mk (𝟙 a))
        (fun _ _ => congr_arg Comma.left)
      apply Fintype.ofFinite
    · have := Finite.of_injective (fun (f : a ⟶ b) => Arrow.mk f)
        (fun f g h => by
          change (Arrow.mk f).hom = (Arrow.mk g).hom
          congr)
      apply Fintype.ofFinite
  · rintro ⟨_⟩
    have := Fintype.ofEquiv _ (Arrow.equivSigma C).symm
    infer_instance

/--
Instance `Arrow.finite` / 实例 `Arrow.finite`

English:
instance Arrow.finite
  signature: {C : Type u} [SmallCategory C] [FinCategory C]
  body: by
  rw [Arrow.finite_iff]
  exact ⟨inferInstance⟩

中文:
实例 箭头.finite
  签名: {C : 类型u} [小范畴 C] [有限范畴 C]
  定义体: by
  rw [Arrow.finite_iff]
  exact ⟨inferInstance⟩

Depends on / 依赖: Arrow.finite_iff, finite_iff
-/
instance Arrow.finite {C : Type u} [SmallCategory C] [FinCategory C] :
    Finite (Arrow C) := by
  rw [Arrow.finite_iff]
  exact ⟨inferInstance⟩

/--
Definition of `Arrow.opEquiv` / `Arrow.opEquiv` 的定义

English:
definition Arrow.opEquiv
  signature: (C : Type u) [Category.{v} C]
  body: Arrow.mk f.hom.unop
  invFun g := Arrow.mk g.hom.op

@[simp]

中文:
定义 箭头.opEquiv
  签名: (C : 类型u) [范畴.{v} C]
  定义体: Arrow.mk f.hom.unop
  invFun g := Arrow.mk g.hom.op

@[simp]

Depends on / 依赖: Arrow.mk, f.hom.unop
-/
def Arrow.opEquiv (C : Type u) [Category.{v} C] : Arrow Cᵒᵖ ≃ Arrow C where
  toFun f := Arrow.mk f.hom.unop
  invFun g := Arrow.mk g.hom.op

@[simp]
/--
lemma `hasCardinalLT_arrow_op_iff` / 引理 `hasCardinalLT_arrow_op_iff`

English:
lemma hasCardinalLT_arrow_op_iff
  given: (C : Type u) [Category.{v} C] (κ : Cardinal.{w})
  proof: hasCardinalLT_iff_of_equiv (Arrow.opEquiv C) κ

@[simp]

中文:
引理 hasCardinalLT_arrow_op_iff
  条件: (C : 类型u) [范畴.{v} C] (κ : 基数.{w})
  证明: hasCardinalLT_iff_of_equiv (Arrow.opEquiv C) κ

@[simp]

Depends on / 依赖: Arrow.opEquiv, hasCardinalLT_iff_of_equiv, opEquiv
-/
lemma hasCardinalLT_arrow_op_iff (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow Cᵒᵖ) κ ↔ HasCardinalLT (Arrow C) κ :=
  hasCardinalLT_iff_of_equiv (Arrow.opEquiv C) κ

@[simp]
/--
lemma `hasCardinalLT_arrow_discrete_iff` / 引理 `hasCardinalLT_arrow_discrete_iff`

English:
lemma hasCardinalLT_arrow_discrete_iff
  given: {X : Type u} (κ : Cardinal.{w})
  proof: hasCardinalLT_iff_of_equiv (Arrow.discreteEquiv X) κ

中文:
引理 hasCardinalLT_arrow_discrete_iff
  条件: {X : 类型u} (κ : 基数.{w})
  证明: hasCardinalLT_iff_of_equiv (Arrow.discreteEquiv X) κ

Depends on / 依赖: Arrow.discreteEquiv, discreteEquiv, hasCardinalLT_iff_of_equiv
-/
lemma hasCardinalLT_arrow_discrete_iff {X : Type u} (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow (Discrete X)) κ ↔ HasCardinalLT X κ :=
  hasCardinalLT_iff_of_equiv (Arrow.discreteEquiv X) κ

instance (X : Type u) [Finite X] : Finite (Arrow (Discrete X)) :=
  Finite.of_equiv _ (Arrow.discreteEquiv X).symm

/--
lemma `small_of_small_arrow` / 引理 `small_of_small_arrow`

English:
lemma small_of_small_arrow
  given: (C : Type u) [Category.{v} C] [Small.{w} (Arrow C)]
  proof: small_of_injective (f := fun X => Arrow.mk (𝟙 X)) (fun _ _ h => congr_arg Comma.left h)

中文:
引理 small_of_small_arrow
  条件: (C : 类型u) [范畴.{v} C] [Small.{w} (箭头 C)]
  证明: small_of_injective (f := fun X => Arrow.mk (𝟙 X)) (fun _ _ h => congr_arg Comma.left h)

Depends on / 依赖: Arrow.mk, Comma.left, congr_arg, small_of_injective
-/
lemma small_of_small_arrow (C : Type u) [Category.{v} C] [Small.{w} (Arrow C)] :
    Small.{w} C :=
  small_of_injective (f := fun X => Arrow.mk (𝟙 X)) (fun _ _ h => congr_arg Comma.left h)

/--
lemma `locallySmall_of_small_arrow` / 引理 `locallySmall_of_small_arrow`

English:
lemma locallySmall_of_small_arrow
  given: (C : Type u) [Category.{v} C] [Small.{w} (Arrow C)]
  proof: small_of_injective (f := fun f => Arrow.mk f) (fun f g h => by
      change (Arrow.mk f).hom = (Arrow.mk g).hom
      congr)

中文:
引理 locallySmall_of_small_arrow
  条件: (C : 类型u) [范畴.{v} C] [Small.{w} (箭头 C)]
  证明: small_of_injective (f := fun f => Arrow.mk f) (fun f g h => by
      change (Arrow.mk f).hom = (Arrow.mk g).hom
      congr)

Depends on / 依赖: Arrow.mk, small_of_injective
-/
lemma locallySmall_of_small_arrow (C : Type u) [Category.{v} C] [Small.{w} (Arrow C)] :
    LocallySmall.{w} C where
  hom_small X Y :=
    small_of_injective (f := fun f => Arrow.mk f) (fun f g h => by
      change (Arrow.mk f).hom = (Arrow.mk g).hom
      congr)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Arrow.shrinkHomsEquiv` / `Arrow.shrinkHomsEquiv` 的定义

English:
definition Arrow.shrinkHomsEquiv
  signature: (C : Type u) [Category.{v} C] [LocallySmall.{w} C]
  body: (ShrinkHoms.equivalence C).inverse.mapArrow.obj
  invFun := (ShrinkHoms.equivalence C).functor.mapArrow.obj
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 箭头.shrinkHomsEquiv
  签名: (C : 类型u) [范畴.{v} C] [LocallySmall.{w} C]
  定义体: (ShrinkHoms.equivalence C).inverse.mapArrow.obj
  invFun := (ShrinkHoms.equivalence C).functor.mapArrow.obj
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: ShrinkHoms, ShrinkHoms.equivalence, equivalence, inverse, inverse.mapArrow.obj, mapArrow
-/
noncomputable def Arrow.shrinkHomsEquiv (C : Type u) [Category.{v} C] [LocallySmall.{w} C] :
    Arrow.{w} (ShrinkHoms C) ≃ Arrow C where
  toFun := (ShrinkHoms.equivalence C).inverse.mapArrow.obj
  invFun := (ShrinkHoms.equivalence C).functor.mapArrow.obj
  left_inv _ := by simp
  right_inv _ := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Arrow.shrinkEquiv` / `Arrow.shrinkEquiv` 的定义

English:
definition Arrow.shrinkEquiv
  signature: (C : Type u) [Category.{v} C] [Small.{w} C]
  body: (Shrink.equivalence C).inverse.mapArrow.obj
  invFun := (Shrink.equivalence C).functor.mapArrow.obj
  left_inv _ := Arrow.ext (Equiv.apply_symm_apply _ _)
      ((Equiv.apply_symm_apply _ _)) (by simp; rfl)
  right_inv _ := Arrow.ext (by simp [Shrink.equivalence])
    (by simp [Shrink.equivalence]) 

中文:
定义 箭头.shrinkEquiv
  签名: (C : 类型u) [范畴.{v} C] [Small.{w} C]
  定义体: (Shrink.equivalence C).inverse.mapArrow.obj
  invFun := (Shrink.equivalence C).functor.mapArrow.obj
  left_inv _ := Arrow.ext (Equiv.apply_symm_apply _ _)
      ((Equiv.apply_symm_apply _ _)) (by simp; rfl)
  right_inv _ := Arrow.ext (by simp [Shrink.equivalence])
    (by simp [Shrink.equivalence]) 

Depends on / 依赖: Shrink, Shrink.equivalence, equivalence, inverse, inverse.mapArrow.obj, mapArrow
-/
noncomputable def Arrow.shrinkEquiv (C : Type u) [Category.{v} C] [Small.{w} C] :
    Arrow (Shrink.{w} C) ≃ Arrow C where
  toFun := (Shrink.equivalence C).inverse.mapArrow.obj
  invFun := (Shrink.equivalence C).functor.mapArrow.obj
  left_inv _ := Arrow.ext (Equiv.apply_symm_apply _ _)
      ((Equiv.apply_symm_apply _ _)) (by simp; rfl)
  right_inv _ := Arrow.ext (by simp [Shrink.equivalence])
    (by simp [Shrink.equivalence]) (by simp [Shrink.equivalence])

@[simp]
/--
lemma `hasCardinalLT_arrow_shrinkHoms_iff` / 引理 `hasCardinalLT_arrow_shrinkHoms_iff`

English:
lemma hasCardinalLT_arrow_shrinkHoms_iff
  statement: (C : Type u) [Category.{v} C] [LocallySmall.{w'} C]
  proof: hasCardinalLT_iff_of_equiv (Arrow.shrinkHomsEquiv C) κ

@[simp]

中文:
引理 hasCardinalLT_arrow_shrinkHoms_iff
  结论: (C : 类型u) [范畴.{v} C] [LocallySmall.{w'} C]
  证明: hasCardinalLT_iff_of_equiv (Arrow.shrinkHomsEquiv C) κ

@[simp]

Depends on / 依赖: Arrow.shrinkHomsEquiv, hasCardinalLT_iff_of_equiv, shrinkHomsEquiv
-/
lemma hasCardinalLT_arrow_shrinkHoms_iff (C : Type u) [Category.{v} C] [LocallySmall.{w'} C]
    (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow.{w'} (ShrinkHoms C)) κ ↔ HasCardinalLT (Arrow C) κ :=
  hasCardinalLT_iff_of_equiv (Arrow.shrinkHomsEquiv C) κ

@[simp]
/--
lemma `hasCardinalLT_arrow_shrink_iff` / 引理 `hasCardinalLT_arrow_shrink_iff`

English:
lemma hasCardinalLT_arrow_shrink_iff
  statement: (C : Type u) [Category.{v} C] [Small.{w'} C]
  proof: hasCardinalLT_iff_of_equiv (Arrow.shrinkEquiv C) κ

中文:
引理 hasCardinalLT_arrow_shrink_iff
  结论: (C : 类型u) [范畴.{v} C] [Small.{w'} C]
  证明: hasCardinalLT_iff_of_equiv (Arrow.shrinkEquiv C) κ

Depends on / 依赖: Arrow.shrinkEquiv, hasCardinalLT_iff_of_equiv, shrinkEquiv
-/
lemma hasCardinalLT_arrow_shrink_iff (C : Type u) [Category.{v} C] [Small.{w'} C]
    (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow (Shrink.{w'} C)) κ ↔ HasCardinalLT (Arrow C) κ :=
  hasCardinalLT_iff_of_equiv (Arrow.shrinkEquiv C) κ

/--
lemma `hasCardinalLT_of_hasCardinalLT_arrow` / 引理 `hasCardinalLT_of_hasCardinalLT_arrow`

English:
lemma hasCardinalLT_of_hasCardinalLT_arrow
  proof: h.of_injective (fun X => Arrow.mk (𝟙 X)) (fun _ _ h => congr_arg Comma.left h)

中文:
引理 hasCardinalLT_of_hasCardinalLT_arrow
  证明: h.of_injective (fun X => Arrow.mk (𝟙 X)) (fun _ _ h => congr_arg Comma.left h)

Depends on / 依赖: Arrow.mk, Comma.left, congr_arg, h.of_injective, of_injective
-/
lemma hasCardinalLT_of_hasCardinalLT_arrow
    {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} (h : HasCardinalLT (Arrow C) κ) :
    HasCardinalLT C κ :=
  h.of_injective (fun X => Arrow.mk (𝟙 X)) (fun _ _ h => congr_arg Comma.left h)

end CategoryTheory
