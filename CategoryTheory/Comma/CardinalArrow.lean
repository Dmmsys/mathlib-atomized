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

/-
**CategoryTheory.Arrow.finite_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arro
w`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.SmallCategory C],   Finite (Category
Theory.Arrow C) ↔ Nonempty (CategoryTheory.FinCategory C)
参数：C : Type u；CategoryTheory.Arrow C；CategoryTheory.FinCategory C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma Arrow.finite_iff (C : Type u) [SmallCategory C] :
    Finite (Arrow C) ↔ Nonempty (FinCategory C) := by
  constructor
  · intro
    refine ⟨?_, fun a b ↦ ?_⟩
    · have := Finite.of_injective (fun (a : C) ↦ Arrow.mk (𝟙 a))
        (fun _ _ ↦ congr_arg Comma.left)
      apply Fintype.ofFinite
    · have := Finite.of_injective (fun (f : a ⟶ b) ↦ Arrow.mk f)
        (fun f g h ↦ by
          change (Arrow.mk f).hom = (Arrow.mk g).hom
          congr)
      apply Fintype.ofFinite
  · rintro ⟨_⟩
    have := Fintype.ofEquiv _ (Arrow.equivSigma C).symm
    infer_instance
/-
**CategoryTheory.Arrow.finite** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.SmallCategory C] [CategoryTheory.Fin
Category C], Finite (CategoryTheory.Arrow C)
参数：CategoryTheory.Arrow C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.finite_iff`：∀ (C : Type u) [inst : CategoryTheory.S
mallCategory C],   Finite (CategoryTheory.Arrow C) ↔ Nonempty (CategoryTheory.Fi
nCategory C)
-/
instance Arrow.finite {C : Type u} [SmallCategory C] [FinCategory C] :
    Finite (Arrow C) := by
  rw [Arrow.finite_iff]
  exact ⟨inferInstance⟩

/-- The bijection `Arrow Cᵒᵖ ≃ Arrow C`. -/
/-
**CategoryTheory.Arrow.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Arrow Cᵒᵖ ≃ CategoryTheory.Arrow C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `Arrow Cᵒᵖ ≃ Arrow C`.
-/
def Arrow.opEquiv (C : Type u) [Category.{v} C] : Arrow Cᵒᵖ ≃ Arrow C where
  toFun f := Arrow.mk f.hom.unop
  invFun g := Arrow.mk g.hom.op

@[simp]
/-
**CategoryTheory.hasCardinalLT_arrow_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：hasCardinalLT_arrow_op_iff (C : Type u) [Category.{v} C] (κ : Cardinal.{w}
) : HasCardinalLT (Arrow Cᵒᵖ) κ ↔ HasCardinalLT (Arrow C) κ
参数：C : Type u；κ : Cardinal.{w}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
-/
lemma hasCardinalLT_arrow_op_iff (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow Cᵒᵖ) κ ↔ HasCardinalLT (Arrow C) κ :=
  hasCardinalLT_iff_of_equiv (Arrow.opEquiv C) κ

@[simp]
/-
**CategoryTheory.hasCardinalLT_arrow_discrete_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：hasCardinalLT_arrow_discrete_iff {X : Type u} (κ : Cardinal.{w}) : HasCard
inalLT (Arrow (Discrete X)) κ ↔ HasCardinalLT X κ
参数：κ : Cardinal.{w}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
-/
lemma hasCardinalLT_arrow_discrete_iff {X : Type u} (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow (Discrete X)) κ ↔ HasCardinalLT X κ :=
  hasCardinalLT_iff_of_equiv (Arrow.discreteEquiv X) κ
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type u) [Finite X] : Finite (Arrow (Discrete X)) :=
  Finite.of_equiv _ (Arrow.discreteEquiv X).symm
/-
**CategoryTheory.small_of_small_arrow** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：small_of_small_arrow (C : Type u) [Category.{v} C] [Small.{w} (Arrow C)] :
 Small.{w} C
参数：C : Type u；Arrow C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma small_of_small_arrow (C : Type u) [Category.{v} C] [Small.{w} (Arrow C)] :
    Small.{w} C :=
  small_of_injective (f := fun X ↦ Arrow.mk (𝟙 X)) (fun _ _ h ↦ congr_arg Comma.left h)
/-
**CategoryTheory.locallySmall_of_small_arrow** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：locallySmall_of_small_arrow (C : Type u) [Category.{v} C] [Small.{w} (Arro
w C)] : LocallySmall.{w} C where hom_small X Y
参数：C : Type u；Arrow C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
lemma locallySmall_of_small_arrow (C : Type u) [Category.{v} C] [Small.{w} (Arrow C)] :
    LocallySmall.{w} C where
  hom_small X Y :=
    small_of_injective (f := fun f ↦ Arrow.mk f) (fun f g h ↦ by
      change (Arrow.mk f).hom = (Arrow.mk g).hom
      congr)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection `Arrow.{w} (ShrinkHoms C) ≃ Arrow C`. -/
/-
**CategoryTheory.Arrow.shrinkHomsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Arrow`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.LocallySmall.{w, v, u} C] →       CategoryTheory.Arrow (Category
Theory.ShrinkHoms.{u} C) ≃ CategoryTheory.Arrow C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `Arrow.{w} (ShrinkHoms C) ≃ Arrow C`.
-/
noncomputable def Arrow.shrinkHomsEquiv (C : Type u) [Category.{v} C] [LocallySmall.{w} C] :
    Arrow.{w} (ShrinkHoms C) ≃ Arrow C where
  toFun := (ShrinkHoms.equivalence C).inverse.mapArrow.obj
  invFun := (ShrinkHoms.equivalence C).functor.mapArrow.obj
  left_inv _ := by simp
  right_inv _ := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The bijection `Arrow (Shrink C) ≃ Arrow C`. -/
/-
**CategoryTheory.Arrow.shrinkEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arr
ow`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 Small.{w, u} C] → CategoryTheory.Arrow (Shrink.{w, u} C) ≃ CategoryTheory.Arrow
 C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `Arrow (Shrink C) ≃ Arrow C`.
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
/-
**CategoryTheory.hasCardinalLT_arrow_shrinkHoms_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：hasCardinalLT_arrow_shrinkHoms_iff (C : Type u) [Category.{v} C] [LocallyS
mall.{w'} C] (κ : Cardinal.{w}) : HasCardinalLT (Arrow.{w'} (ShrinkHoms C)) κ ↔ 
HasCardinalLT (Arrow C) κ
参数：C : Type u；κ : Cardinal.{w}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
-/
lemma hasCardinalLT_arrow_shrinkHoms_iff (C : Type u) [Category.{v} C] [LocallySmall.{w'} C]
    (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow.{w'} (ShrinkHoms C)) κ ↔ HasCardinalLT (Arrow C) κ :=
  hasCardinalLT_iff_of_equiv (Arrow.shrinkHomsEquiv C) κ

@[simp]
/-
**CategoryTheory.hasCardinalLT_arrow_shrink_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：hasCardinalLT_arrow_shrink_iff (C : Type u) [Category.{v} C] [Small.{w'} C
] (κ : Cardinal.{w}) : HasCardinalLT (Arrow (Shrink.{w'} C)) κ ↔ HasCardinalLT (
Arrow C) κ
参数：C : Type u；κ : Cardinal.{w}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
-/
lemma hasCardinalLT_arrow_shrink_iff (C : Type u) [Category.{v} C] [Small.{w'} C]
    (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow (Shrink.{w'} C)) κ ↔ HasCardinalLT (Arrow C) κ :=
  hasCardinalLT_iff_of_equiv (Arrow.shrinkEquiv C) κ
/-
**CategoryTheory.hasCardinalLT_of_hasCardinalLT_arrow** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：hasCardinalLT_of_hasCardinalLT_arrow {C : Type u} [Category.{v} C] {κ : Ca
rdinal.{w}} (h : HasCardinalLT (Arrow C) κ) : HasCardinalLT C κ
参数：h : HasCardinalLT (Arrow C) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.of_injective`：of_injective (f : Y -> X) (hf : Function.Inj
ective f) : HasCardinalLT Y κ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma hasCardinalLT_of_hasCardinalLT_arrow
    {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} (h : HasCardinalLT (Arrow C) κ) :
    HasCardinalLT C κ :=
  h.of_injective (fun X ↦ Arrow.mk (𝟙 X)) (fun _ _ h ↦ congr_arg Comma.left h)

end CategoryTheory

