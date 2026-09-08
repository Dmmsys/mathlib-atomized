/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The comma category is preadditive

If we have additive functors `L : A ⥤ T` and `R : B ⥤ T` between preadditive categories,
then there is a structure of preadditive category on `Comma L R` such that addition commutes
with the left and right projections.

We then apply this to `Arrow T` for `T` a preadditive category.

## Tags

comma, arrow, preadditive
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable {T : Type u₃} [Category.{v₃} T] [Preadditive T]
variable (L : A ⥤ T) [L.Additive] (R : B ⥤ T) [R.Additive]
variable {u v : Comma L R}

section Comma

namespace CommaMorphism

@[simps!]
/-
**CategoryTheory.CommaMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommaM
orphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (u ⟶ v) where
  add α β := CommaMorphism.mk (α.left + β.left) (α.right + β.right) (by simp)

@[simps!]
/-
**CategoryTheory.CommaMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommaM
orphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (u ⟶ v) where
  sub α β := CommaMorphism.mk (α.left - β.left) (α.right - β.right) (by simp)

@[simps!]
/-
**CategoryTheory.CommaMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommaM
orphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (u ⟶ v) where
  zero := CommaMorphism.mk 0 0

@[simps!]
/-
**CategoryTheory.CommaMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommaM
orphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (u ⟶ v) where
  neg α := CommaMorphism.mk (-α.left) (-α.right)

end CommaMorphism

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (u ⟶ v) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero_add _ := by cat_disch
  add_zero _ := by cat_disch
  add_comm _ _ := by ext <;> simp [add_comm]
  neg_add_cancel _ := by cat_disch
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]
  nsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_nsmul, Preadditive.comp_nsmul, Preadditive.nsmul_comp])
  zsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp])
  nsmul_zero := by simp_rw [HSMul.hSMul, SMul.smul]; cat_disch
  nsmul_succ _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; ext <;> dsimp <;> simp [add_nsmul]
  zsmul_zero' := by simp_rw [HSMul.hSMul, SMul.smul]; cat_disch
  zsmul_succ' _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; ext <;> dsimp <;> simp [add_zsmul]
  zsmul_neg' _ _ := by
    simp_rw [HSMul.hSMul, SMul.smul]
    ext <;> dsimp <;> simp [add_nsmul, add_zsmul]

/-- If we have additive functors `L : A ⥤ T` and `R : B ⥤ T` between preadditive categories,
then the category `Comma L R` is preadditive.
-/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have additive functors `L : A ⥤ T` and `R : B ⥤ T` between preadditive cat
egories,
then the category `Comma L R` is preadditive.
-/
instance : Preadditive (Comma L R) where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Comma.fst L R).Additive where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Comma.snd L R).Additive where

end Comma

section Arrow

/-- If a category `T` is preadditive, then so is its category of arrows.
-/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a category `T` is preadditive, then so is its category of arrows.
-/
instance : Preadditive (Arrow T) := inferInstanceAs (Preadditive (Comma (𝟭 T) (𝟭 T)))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Arrow.leftFunc (C := T)).Additive :=
  inferInstanceAs ((Comma.fst (𝟭 T) (𝟭 T))).Additive
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Arrow.rightFunc (C := T)).Additive :=
  inferInstanceAs ((Comma.snd (𝟭 T) (𝟭 T))).Additive

variable {u v : Arrow T}

@[simp]
/-
**CategoryTheory.Arrow.Hom.add_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ar
row.Hom`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] [inst_1 : Cate
goryTheory.Preadditive T]   {u v : CategoryTheory.Arrow T} (α β : u ⟶ v),   Cate
goryTheory.Arrow.Hom.left (α + β) = CategoryTheory.Arrow.Hom.left α + CategoryTh
eory.Arrow.Hom.left β
参数：α β : u ⟶ v；α + β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.Hom.add_left (α β : u ⟶ v) : (α + β).left = α.left + β.left := rfl

@[simp]
/-
**CategoryTheory.Arrow.Hom.add_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.A
rrow.Hom`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] [inst_1 : Cate
goryTheory.Preadditive T]   {u v : CategoryTheory.Arrow T} (α β : u ⟶ v),   Cate
goryTheory.Arrow.Hom.right (α + β) = CategoryTheory.Arrow.Hom.right α + Category
Theory.Arrow.Hom.right β
参数：α β : u ⟶ v；α + β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.Hom.add_right (α β : u ⟶ v) : (α + β).right = α.right + β.right := rfl

@[simp]
/-
**CategoryTheory.Arrow.Hom.sub_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ar
row.Hom`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] [inst_1 : Cate
goryTheory.Preadditive T]   {u v : CategoryTheory.Arrow T} (α β : u ⟶ v),   Cate
goryTheory.Arrow.Hom.left (α - β) = CategoryTheory.Arrow.Hom.left α - CategoryTh
eory.Arrow.Hom.left β
参数：α β : u ⟶ v；α - β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.Hom.sub_left (α β : u ⟶ v) : (α - β).left = α.left - β.left := rfl

@[simp]
/-
**CategoryTheory.Arrow.Hom.sub_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.A
rrow.Hom`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] [inst_1 : Cate
goryTheory.Preadditive T]   {u v : CategoryTheory.Arrow T} (α β : u ⟶ v),   Cate
goryTheory.Arrow.Hom.right (α - β) = CategoryTheory.Arrow.Hom.right α - Category
Theory.Arrow.Hom.right β
参数：α β : u ⟶ v；α - β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.Hom.sub_right (α β : u ⟶ v) : (α - β).right = α.right - β.right := rfl

@[simp]
/-
**CategoryTheory.Arrow.Hom.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.A
rrow.Hom`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] [inst_1 : Cate
goryTheory.Preadditive T]   {u v : CategoryTheory.Arrow T}, CategoryTheory.Arrow
.Hom.left 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.Hom.zero_left : (0 : u ⟶ v).left = 0 := rfl

@[simp]
/-
**CategoryTheory.Arrow.Hom.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Arrow.Hom`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] [inst_1 : Cate
goryTheory.Preadditive T]   {u v : CategoryTheory.Arrow T}, CategoryTheory.Arrow
.Hom.right 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.Hom.zero_right : (0 : u ⟶ v).right = 0 := rfl

@[simp]
/-
**CategoryTheory.Arrow.Hom.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ar
row.Hom`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] [inst_1 : Cate
goryTheory.Preadditive T]   {u v : CategoryTheory.Arrow T} (α : u ⟶ v), Category
Theory.Arrow.Hom.left (-α) = -CategoryTheory.Arrow.Hom.left α
参数：α : u ⟶ v；-α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.Hom.neg_left (α : u ⟶ v) : (-α).left = -α.left := rfl

@[simp]
/-
**CategoryTheory.Arrow.Hom.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.A
rrow.Hom`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] [inst_1 : Cate
goryTheory.Preadditive T]   {u v : CategoryTheory.Arrow T} (α : u ⟶ v), Category
Theory.Arrow.Hom.right (-α) = -CategoryTheory.Arrow.Hom.right α
参数：α : u ⟶ v；-α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.Hom.neg_right (α : u ⟶ v) : (-α).right = -α.right := rfl

end Arrow

end CategoryTheory

