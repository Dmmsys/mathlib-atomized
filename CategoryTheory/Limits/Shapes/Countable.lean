/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Data.Countable.Defs
/-!
# Countable limits and colimits

A typeclass for categories with all countable (co)limits.

We also prove that all cofiltered limits over countable preorders are isomorphic to sequential
limits, see `sequentialFunctor_initial`.

## Projects

* There is a series of `proof_wanted` at the bottom of this file, implying that all cofiltered
  limits over countable categories are isomorphic to sequential limits.

* Prove the dual result for filtered colimits.

-/

@[expose] public section

open CategoryTheory Opposite CountableCategory

variable (C : Type*) [Category* C] (J : Type*) [Countable J]

namespace CategoryTheory.Limits

/--
A category has all countable limits if every functor `J ⥤ C` with a `CountableCategory J`
instance and `J : Type` has a limit.
-/
/-
**CategoryTheory.Limits.HasCountableLimits** 是 Mathlib 中的一个类，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：HasCountableLimits : Prop where /-- `C` has all limits over any type `J` w
hose objects and morphisms lie in the same universe and which has countably many
 objects and morphisms -/ out (J : Type) [SmallCategory J] [CountableCategory J]
 : HasLimitsOfShape J C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has all countable limits if every functor `J ⥤ C` with a `CountableCa
tegory J`
instance and `J : Type` has a limit.
-/
class HasCountableLimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms -/
  out (J : Type) [SmallCategory J] [CountableCategory J] : HasLimitsOfShape J C := by infer_instance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteLimits_of_hasCountableLimits [HasCountableLimits C] :
    HasFiniteLimits C where
  out J := HasCountableLimits.out J
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCountableLimits_of_hasLimits [HasLimits C] :
    HasCountableLimits C where
  out := inferInstance

universe v in
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasCountableLimits C] [Category.{v} J] [CountableCategory J] : HasLimitsOfShape J C :=
  have : HasLimitsOfShape (HomAsType J) C := HasCountableLimits.out (HomAsType J)
  hasLimitsOfShape_of_equivalence (homAsTypeEquiv J)

/-- A category has countable products if it has all products indexed by countable types. -/
/-
**CategoryTheory.Limits.HasCountableProducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：(C : Type u_1) → [CategoryTheory.Category.{v_1, u_1} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has countable products if it has all products indexed by countable ty
pes.
-/
class HasCountableProducts where
  out (J : Type) [Countable J] : HasProductsOfShape J C
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasCountableProducts C] (J : Type*) [Countable J] : HasProductsOfShape J C :=
  have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasLimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableProducts.out _
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCountableProducts_of_hasProducts [HasProducts C] :
    HasCountableProducts C where
  out _ :=
    have : HasProducts.{0} C := has_smallest_products_of_hasProducts
    inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCountableProducts_of_hasCountableLimits [HasCountableLimits C] :
    HasCountableProducts C where
  out _ := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteProducts_of_hasCountableProducts [HasCountableProducts C] :
    HasFiniteProducts C where
  out _ := inferInstance

/--
A category has all countable colimits if every functor `J ⥤ C` with a `CountableCategory J`
instance and `J : Type` has a colimit.
-/
/-
**CategoryTheory.Limits.HasCountableColimits** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：(C : Type u_1) → [CategoryTheory.Category.{v_1, u_1} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has all countable colimits if every functor `J ⥤ C` with a `Countable
Category J`
instance and `J : Type` has a colimit.
-/
class HasCountableColimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms -/
  out (J : Type) [SmallCategory J] [CountableCategory J] : HasColimitsOfShape J C
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteColimits_of_hasCountableColimits [HasCountableColimits C] :
    HasFiniteColimits C where
  out J := HasCountableColimits.out J
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCountableColimits_of_hasColimits [HasColimits C] :
    HasCountableColimits C where
  out := inferInstance

-- See note [instance argument order]
universe v in
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasCountableColimits C] (J : Type*) [Category.{v} J] [CountableCategory J] :
    HasColimitsOfShape J C :=
  have : HasColimitsOfShape (HomAsType J) C := HasCountableColimits.out (HomAsType J)
  hasColimitsOfShape_of_equivalence (homAsTypeEquiv J)

/-- A category has countable coproducts if it has all coproducts indexed by countable types. -/
/-
**CategoryTheory.Limits.HasCountableCoproducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：(C : Type u_1) → [CategoryTheory.Category.{v_1, u_1} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has countable coproducts if it has all coproducts indexed by countabl
e types.
-/
class HasCountableCoproducts where
  out (J : Type) [Countable J] : HasCoproductsOfShape J C
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCountableCoproducts_of_hasCoproducts [HasCoproducts C] :
    HasCountableCoproducts C where
  out _ :=
    have : HasCoproducts.{0} C := has_smallest_coproducts_of_hasCoproducts
    inferInstance

-- See note [instance argument order]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasCountableCoproducts C] (J : Type*) [Countable J] : HasCoproductsOfShape J C :=
  have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasColimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableCoproducts.out _
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCountableCoproducts_of_hasCountableColimits [HasCountableColimits C] :
    HasCountableCoproducts C where
  out _ := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteCoproducts_of_hasCountableCoproducts
    [HasCountableCoproducts C] : HasFiniteCoproducts C where
  out _ := inferInstance

section Preorder

namespace IsFiltered

attribute [local instance] IsFiltered.nonempty

variable {C} [Preorder J] [IsFiltered J]

/-- The object part of the initial functor `ℕᵒᵖ ⥤ J` -/
/-
**CategoryTheory.Limits.IsFiltered.sequentialFunctor_obj** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.IsFiltered`。
形式化陈述：sequentialFunctor_obj : Nat -> J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object part of the initial functor `ℕᵒᵖ ⥤ J`
-/
noncomputable def sequentialFunctor_obj : ℕ → J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose
/-
**CategoryTheory.Limits.IsFiltered.sequentialFunctor_map** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.IsFiltered`。
形式化陈述：sequentialFunctor_map : Monotone (sequentialFunctor_obj J)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `exists_surjective_nat`：exists_surjective_nat (α : Sort u) [Nonempty α] [
Countable α] : exists f : Nat -> α, Surjective f
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.cocone_objs`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFilteredOrEmpty C] (X Y 
: C),   ∃ Z x x, True
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem sequentialFunctor_map : Monotone (sequentialFunctor_obj J) :=
  monotone_nat_of_le_succ fun n ↦
    leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

/--
The initial functor `ℕᵒᵖ ⥤ J`, which allows us to turn cofiltered limits over countable preorders
into sequential limits.
-/
/-
**CategoryTheory.Limits.IsFiltered.sequentialFunctor** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.IsFiltered`。
形式化陈述：sequentialFunctor : Nat ⥤ J where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial functor `ℕᵒᵖ ⥤ J`, which allows us to turn cofiltered limits over co
untable preorders
into sequential limits.
-/
noncomputable def sequentialFunctor : ℕ ⥤ J where
  obj n := sequentialFunctor_obj J n
  map h := homOfLE (sequentialFunctor_map J (leOfHom h))
/-
**CategoryTheory.Limits.IsFiltered.sequentialFunctor_final_aux** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.IsFiltered`。
形式化陈述：sequentialFunctor_final_aux (j : J) : exists (n : Nat), j <= sequentialFun
ctor_obj J n
参数：j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_surjective_nat`：exists_surjective_nat (α : Sort u) [Nonempty α] [
Countable α] : exists f : Nat -> α, Surjective f
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.cocone_objs`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFilteredOrEmpty C] (X Y 
: C),   ∃ Z x x, True
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
-/
theorem sequentialFunctor_final_aux (j : J) : ∃ (n : ℕ), j ≤ sequentialFunctor_obj J n := by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using! leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose
/-
**CategoryTheory.Limits.IsFiltered.sequentialFunctor_final** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits.IsFiltered`。
形式化陈述：sequentialFunctor_final : (sequentialFunctor J).Final where out d
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsFiltered.sequentialFunctor_final_aux`：sequential
Functor_final_aux (j : J) : exists (n : Nat), j <= sequentialFunctor_obj J n
· 使用定理 `CategoryTheory.isConnected_of_zigzag`：isConnected_of_zigzag [Nonempty J]
 (h : forall j₁ j₂ : J, exists l, List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ 
:: l) (List.cons_ne_nil _ …
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
instance sequentialFunctor_final : (sequentialFunctor J).Final where
  out d := by
    obtain ⟨n, (g : d ≤ (sequentialFunctor J).obj n)⟩ := sequentialFunctor_final_aux J d
    have : Nonempty (StructuredArrow d (sequentialFunctor J)) :=
      ⟨StructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j ↦ ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog! h : j.right ≤ i.right
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt h))
    · right
      exact ⟨StructuredArrow.homMk (homOfLE h) rfl⟩

end IsFiltered

namespace IsCofiltered

attribute [local instance] IsCofiltered.nonempty

variable {C} [Preorder J] [IsCofiltered J]

/-- The object part of the initial functor `ℕᵒᵖ ⥤ J` -/
/-
**CategoryTheory.Limits.IsCofiltered.sequentialFunctor_obj** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.IsCofiltered`。
形式化陈述：sequentialFunctor_obj : Nat -> J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object part of the initial functor `ℕᵒᵖ ⥤ J`
-/
noncomputable def sequentialFunctor_obj : ℕ → J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose
/-
**CategoryTheory.Limits.IsCofiltered.sequentialFunctor_map** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.IsCofiltered`。
形式化陈述：sequentialFunctor_map : Antitone (sequentialFunctor_obj J)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `exists_surjective_nat`：exists_surjective_nat (α : Sort u) [Nonempty α] [
Countable α] : exists f : Nat -> α, Surjective f
· 使用定理 `CategoryTheory.IsCofiltered.nonempty`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C], Nonempty C
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.cone_objs`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofilteredOrEmpty C] (X 
Y : C),   ∃ W x x, True
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem sequentialFunctor_map : Antitone (sequentialFunctor_obj J) :=
  antitone_nat_of_succ_le fun n ↦
    leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

/--
The initial functor `ℕᵒᵖ ⥤ J`, which allows us to turn cofiltered limits over countable preorders
into sequential limits.

TODO: redefine this as `(IsFiltered.sequentialFunctor Jᵒᵖ).leftOp`. This would need API for initial/
final functors of the form `leftOp`/`rightOp`.
-/
/-
**CategoryTheory.Limits.IsCofiltered.sequentialFunctor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.IsCofiltered`。
形式化陈述：sequentialFunctor : Natᵒᵖ ⥤ J where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial functor `ℕᵒᵖ ⥤ J`, which allows us to turn cofiltered limits over co
untable preorders
into sequential limits.

TODO: redefine this as `(IsFiltered.sequentialFunctor Jᵒᵖ).leftOp`. This would n
eed API for initial/
final functors of the form `leftOp`/`rightOp`.
-/
noncomputable def sequentialFunctor : ℕᵒᵖ ⥤ J where
  obj n := sequentialFunctor_obj J (unop n)
  map h := homOfLE (sequentialFunctor_map J (leOfHom h.unop))
/-
**CategoryTheory.Limits.IsCofiltered.sequentialFunctor_initial_aux** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Limits.IsCofiltered`。
形式化陈述：sequentialFunctor_initial_aux (j : J) : exists (n : Nat), sequentialFuncto
r_obj J n <= j
参数：j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_surjective_nat`：exists_surjective_nat (α : Sort u) [Nonempty α] [
Countable α] : exists f : Nat -> α, Surjective f
· 使用定理 `CategoryTheory.IsCofiltered.nonempty`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C], Nonempty C
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.cone_objs`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofilteredOrEmpty C] (X 
Y : C),   ∃ W x x, True
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
-/
theorem sequentialFunctor_initial_aux (j : J) : ∃ (n : ℕ), sequentialFunctor_obj J n ≤ j := by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using! leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose
/-
**CategoryTheory.Limits.IsCofiltered.sequentialFunctor_initial** 是 Mathlib 中的一个实
例，位于命名空间 `CategoryTheory.Limits.IsCofiltered`。
形式化陈述：sequentialFunctor_initial : (sequentialFunctor J).Initial where out d
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsCofiltered.sequentialFunctor_initial_aux`：sequen
tialFunctor_initial_aux (j : J) : exists (n : Nat), sequentialFunctor_obj J n <=
 j
· 使用定理 `CategoryTheory.isConnected_of_zigzag`：isConnected_of_zigzag [Nonempty J]
 (h : forall j₁ j₂ : J, exists l, List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ 
:: l) (List.cons_ne_nil _ …
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
instance sequentialFunctor_initial : (sequentialFunctor J).Initial where
  out d := by
    obtain ⟨n, (g : (sequentialFunctor J).obj ⟨n⟩ ≤ d)⟩ := sequentialFunctor_initial_aux J d
    have : Nonempty (CostructuredArrow (sequentialFunctor J) d) :=
      ⟨CostructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j ↦ ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog! h : (unop i.left) ≤ (unop j.left)
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt h))
    · right
      exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

@[stacks 0032]
proof_wanted preorder_of_cofiltered (J : Type*) [Category* J] [IsCofiltered J] :
    ∃ (I : Type*) (_ : Preorder I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

/--
The proof of `preorder_of_cofiltered` should give a countable `I` in the case that `J` is a
countable category.
-/
proof_wanted preorder_of_cofiltered_countable
    (J : Type*) [SmallCategory J] [IsCofiltered J] [CountableCategory J] :
    ∃ (I : Type) (_ : Preorder I) (_ : Countable I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

/--
Put together `sequentialFunctor_initial` and `preorder_of_cofiltered_countable`.
-/
proof_wanted hasCofilteredCountableLimits_of_hasSequentialLimits [HasLimitsOfShape ℕᵒᵖ C] :
    ∀ (J : Type) [SmallCategory J] [IsCofiltered J] [CountableCategory J], HasLimitsOfShape J C

/--
This is the countable version of `CategoryTheory.Limits.has_limits_of_finite_and_cofiltered`, given
all of the above.
-/
proof_wanted hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits [HasFiniteLimits C]
  [HasLimitsOfShape ℕᵒᵖ C] : HasCountableLimits C

/--
For this we need to dualize this whole section.
-/
proof_wanted hasCountableColimits_of_hasFiniteColimits_and_hasSequentialColimits
  [HasFiniteColimits C] [HasLimitsOfShape ℕ C] : HasCountableColimits C

end IsCofiltered

end Preorder

end CategoryTheory.Limits

