/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.Data.Set.Finite.Lattice

/-! # The Finite Pretopology

In this file we define the finite pretopology on a category, which consists of presieves that
contain only finitely many arrows.

## Main Definitions

- `CategoryTheory.Precoverage.finite`: The finite precoverage on a category.
- `CategoryTheory.Pretopology.finite`: The finite pretopology on a category.
-/

@[expose] public section

universe v v₁ u u₁

namespace CategoryTheory

open Presieve

namespace Precoverage

/-- The finite precoverage on a category consists of finite presieves, i.e. a presieve with finitely
many maps after uncurrying. -/
/-
**CategoryTheory.Precoverage.finite** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pr
ecoverage`。
形式化陈述：finite (C : Type u) [Category.{v} C] : Precoverage C where coverings X
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite precoverage on a category consists of finite presieves, i.e. a presie
ve with finitely
many maps after uncurrying.
-/
def finite (C : Type u) [Category.{v} C] : Precoverage C where
  coverings X := { s : Presieve X | s.uncurry.Finite }

variable {C : Type u} [Category.{v} C]
/-
**CategoryTheory.Precoverage.mem_finite_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Precoverage`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} {s : Cate
goryTheory.Presieve X},   s ∈ (CategoryTheory.Precoverage.finite C).coverings X 
↔ s.uncurry.Finite
参数：CategoryTheory.Precoverage.finite C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_finite_iff {X : C} {s : Presieve X} :
    s ∈ finite C X ↔ s.uncurry.Finite := Iff.rfl
/-
**CategoryTheory.Precoverage.ofArrows_mem_finite** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Precoverage`。
形式化陈述：ofArrows_mem_finite {X : C} {ι : Type*} [Finite ι] (Y : ι -> C) (f : (i : 
ι) -> Y i ⟶ X) : ofArrows Y f in finite C X
参数：Y : ι -> C；f : (i : ι) -> Y i ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.uncurry_ofArrows`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X : C} {ι : Type u_1} (Y : ι → C) (f : (i : ι) → 
Y i ⟶ X),   (CategoryTheory.Pr…
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
-/
theorem ofArrows_mem_finite {X : C} {ι : Type*} [Finite ι] (Y : ι → C) (f : (i : ι) → Y i ⟶ X) :
    ofArrows Y f ∈ finite C X := by
  simpa using Set.finite_range _
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (finite C).HasIsos where
  mem_coverings_of_isIso := by simp

end Precoverage

namespace Pretopology

open Limits

/-- The finite pretopology on a category consists of finite presieves, i.e. a presieve with finitely
many maps after uncurrying. -/
@[simps toPrecoverage]
/-
**CategoryTheory.Pretopology.finite** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pr
etopology`。
形式化陈述：finite (C : Type u) [Category.{v} C] [HasPullbacks C] : Pretopology C wher
e __
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite pretopology on a category consists of finite presieves, i.e. a presie
ve with finitely
many maps after uncurrying.
-/
def finite (C : Type u) [Category.{v} C] [HasPullbacks C] : Pretopology C where
  __ := Precoverage.finite C
  has_isos _ _ _ := Precoverage.mem_coverings_of_isIso _
  pullbacks X Y u s hs := by simpa using hs.image _
  transitive X s t hs ht := by simpa using hs.biUnion' fun _ _ ↦ (ht _ _).image _

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
/-
**CategoryTheory.Pretopology.ofArrows_mem_finite** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Pretopology`。
形式化陈述：ofArrows_mem_finite {X : C} {ι : Type*} [Finite ι] (Y : ι -> C) (f : (i : 
ι) -> Y i ⟶ X) : ofArrows Y f in (finite C).coverings X
参数：Y : ι -> C；f : (i : ι) -> Y i ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ofArrows_mem_finite`：ofArrows_mem_finite {X :
 C} {ι : Type*} [Finite ι] (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X) : ofArrows Y f 
in finite C X
-/
theorem ofArrows_mem_finite {X : C} {ι : Type*} [Finite ι] (Y : ι → C) (f : (i : ι) → Y i ⟶ X) :
    ofArrows Y f ∈ (finite C).coverings X :=
  Precoverage.ofArrows_mem_finite _ _

end Pretopology

end CategoryTheory

