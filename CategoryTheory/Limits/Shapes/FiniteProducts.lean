/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Categories with finite (co)products

Typeclasses representing categories with (co)products over finite indexing types.
-/

public section


universe w v u

open CategoryTheory

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/-- A category has finite products if there exists a limit for every diagram
with shape `Discrete J`, where we have `[Finite J]`.

We require this condition only for `J = Fin n` in the definition, then deduce a version for any
`J : Type*` as a corollary of this definition.
-/
/-
**CategoryTheory.Limits.HasFiniteProducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has finite products if there exists a limit for every diagram
with shape `Discrete J`, where we have `[Finite J]`.

We require this condition only for `J = Fin n` in the definition, then deduce a 
version for any
`J : Type*` as a corollary of this definition.
-/
class HasFiniteProducts : Prop where
  /-- `C` has finite products -/
  out (n : ℕ) : HasLimitsOfShape (Discrete (Fin n)) C

/-- If `C` has finite limits then it has finite products. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has finite limits then it has finite products.
-/
instance (priority := 10) hasFiniteProducts_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteProducts C :=
  ⟨fun _ => inferInstance⟩
/-
**CategoryTheory.Limits.hasLimitsOfShape_discrete** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_discrete [HasFiniteProducts C] (ι : Type w) [Finite ι] : 
HasLimitsOfShape (Discrete ι) C
参数：ι : Type w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `CategoryTheory.Limits.HasFiniteProducts.out`：∀ {C : Type u} {inst : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasFiniteProducts C]
 (n : ℕ),   CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance hasLimitsOfShape_discrete [HasFiniteProducts C] (ι : Type w) [Finite ι] :
    HasLimitsOfShape (Discrete ι) C := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have : HasLimitsOfShape (Discrete (Fin n)) C := HasFiniteProducts.out n
  exact hasLimitsOfShape_of_equivalence (Discrete.equivalence e.symm)

/-- We can now write this for powers. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can now write this for powers.
-/
noncomputable example [HasFiniteProducts C] (X : C) : C :=
  ∏ᶜ fun _ : Fin 5 => X

/-- If a category has all products then in particular it has finite products.
-/
/-
**CategoryTheory.Limits.hasFiniteProducts_of_hasProducts** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteProducts_of_hasProducts [HasProducts.{w} C] : HasFiniteProducts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C

--- 原说明 ---
If a category has all products then in particular it has finite products.
-/
theorem hasFiniteProducts_of_hasProducts [HasProducts.{w} C] : HasFiniteProducts C :=
  ⟨fun _ => hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

/-- A category has finite coproducts if there exists a colimit for every diagram
with shape `Discrete J`, where we have `[Fintype J]`.

We require this condition only for `J = Fin n` in the definition, then deduce a version for any
`J : Type*` as a corollary of this definition.
-/
/-
**CategoryTheory.Limits.HasFiniteCoproducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has finite coproducts if there exists a colimit for every diagram
with shape `Discrete J`, where we have `[Fintype J]`.

We require this condition only for `J = Fin n` in the definition, then deduce a 
version for any
`J : Type*` as a corollary of this definition.
-/
class HasFiniteCoproducts : Prop where
  /-- `C` has all finite coproducts -/
  out (n : ℕ) : HasColimitsOfShape (Discrete (Fin n)) C
/-
**CategoryTheory.Limits.hasColimitsOfShape_discrete** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_discrete [HasFiniteCoproducts C] (ι : Type w) [Finite ι
] : HasColimitsOfShape (Discrete ι) C
参数：ι : Type w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `CategoryTheory.Limits.HasFiniteCoproducts.out`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasFiniteCoproduct
s C] (n : ℕ),   CategoryTheory.Limi…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance hasColimitsOfShape_discrete [HasFiniteCoproducts C] (ι : Type w) [Finite ι] :
    HasColimitsOfShape (Discrete ι) C := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have : HasColimitsOfShape (Discrete (Fin n)) C := HasFiniteCoproducts.out n
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence e.symm)

/-- If `C` has finite colimits then it has finite coproducts. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has finite colimits then it has finite coproducts.
-/
instance (priority := 10) hasFiniteCoproducts_of_hasFiniteColimits [HasFiniteColimits C] :
    HasFiniteCoproducts C :=
  ⟨fun J => by infer_instance⟩

/-- If a category has all coproducts then in particular it has finite coproducts.
-/
/-
**CategoryTheory.Limits.hasFiniteCoproducts_of_hasCoproducts** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteCoproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasFiniteCopr
oducts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C

--- 原说明 ---
If a category has all coproducts then in particular it has finite coproducts.
-/
theorem hasFiniteCoproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasFiniteCoproducts C :=
  ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

end CategoryTheory.Limits

