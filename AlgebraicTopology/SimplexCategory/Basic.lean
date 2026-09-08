/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Order.Category.NonemptyFinLinOrd
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-! # Basic properties of the simplex category

In `Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean`, we define the simplex
category with objects `ℕ` and morphisms `n ⟶ m` the monotone maps from
`Fin (n + 1)` to `Fin (m + 1)`.

In this file, we define the generating maps for the simplex category, show that
this category is equivalent to `NonemptyFinLinOrd`, and establish basic
properties of its epimorphisms and monomorphisms.
-/

@[expose] public section

universe u

open Simplicial CategoryTheory Limits

namespace SimplexCategory

/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a b : SimplexCategory} : Finite (a ⟶ b) :=
  Finite.of_injective (fun f ↦ f.toOrderHom.toFun)
    (fun _ _ _ ↦ by aesop)
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n m : SimplexCategory} : DecidableEq (n ⟶ m) := fun a b =>
  decidable_of_iff (a.toOrderHom = b.toOrderHom) SimplexCategory.Hom.ext_iff.symm

section Init

/-
**SimplexCategory.congr_toOrderHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCateg
ory`。
形式化陈述：congr_toOrderHom_apply {a b : SimplexCategory} {f g : a ⟶ b} (h : f = g) (
x : Fin (a.len + 1)) : f.toOrderHom x = g.toOrderHom x
参数：h : f = g；x : Fin (a.len + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma congr_toOrderHom_apply {a b : SimplexCategory} {f g : a ⟶ b} (h : f = g)
    (x : Fin (a.len + 1)) : f.toOrderHom x = g.toOrderHom x := by rw [h]

/-- The constant morphism from ⦋0⦌. -/
/-
**SimplexCategory.const** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：const (x y : SimplexCategory) (i : Fin (y.len + 1)) : x ⟶ y
参数：x y : SimplexCategory；i : Fin (y.len + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant morphism from ⦋0⦌.
-/
def const (x y : SimplexCategory) (i : Fin (y.len + 1)) : x ⟶ y :=
  Hom.mk <| ⟨fun _ => i, by tauto⟩

@[simp]
/-
**SimplexCategory.const_eq_id** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：const_eq_id : const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma const_eq_id : const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := by aesop

@[simp]
/-
**SimplexCategory.const_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：const_apply (x y : SimplexCategory) (i : Fin (y.len + 1)) (a : Fin (x.len 
+ 1)) : (const x y i).toOrderHom a = i
参数：x y : SimplexCategory；i : Fin (y.len + 1)；a : Fin (x.len + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_apply (x y : SimplexCategory) (i : Fin (y.len + 1)) (a : Fin (x.len + 1)) :
    (const x y i).toOrderHom a = i := rfl

@[simp]
/-
**SimplexCategory.const_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：const_comp (x : SimplexCategory) {y z : SimplexCategory} (f : y ⟶ z) (i : 
Fin (y.len + 1)) : const x y i ≫ f = const x z (f.toOrderHom i)
参数：x : SimplexCategory；f : y ⟶ z；i : Fin (y.len + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_comp (x : SimplexCategory) {y z : SimplexCategory}
    (f : y ⟶ z) (i : Fin (y.len + 1)) :
    const x y i ≫ f = const x z (f.toOrderHom i) :=
  rfl
/-
**SimplexCategory.const_fac_thru_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory
`。
形式化陈述：const_fac_thru_zero (n m : SimplexCategory) (i : Fin (m.len + 1)) : const 
n m i = const n ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ m i
参数：n m : SimplexCategory；i : Fin (m.len + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimplexCategory.const_comp`：const_comp (x : SimplexCategory) {y z : Simp
lexCategory} (f : y ⟶ z) (i : Fin (y.len + 1)) : const x y i ≫ f = const x z (f.
toOrderHom i)
-/
theorem const_fac_thru_zero (n m : SimplexCategory) (i : Fin (m.len + 1)) :
    const n m i = const n ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ m i := by
  rw [const_comp]; rfl
/-
**SimplexCategory.Hom.ext_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.H
om`。
形式化陈述：∀ {n : SimplexCategory} (f g : { len := 0 } ⟶ n),   autoParam ((SimplexCat
egory.Hom.toOrderHom f) 0 = (SimplexCategory.Hom.toOrderHom g) 0)       SimplexC
ategory.Hom.ext_zero_left._auto_1 →     f = g
参数：f g : { len := 0 } ⟶ n；(SimplexCategory.Hom.toOrderHom f) 0 = (SimplexCategor
y.Hom.toOrderHom g) 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
-/
theorem Hom.ext_zero_left {n : SimplexCategory} (f g : ⦋0⦌ ⟶ n)
    (h0 : f.toOrderHom 0 = g.toOrderHom 0 := by rfl) : f = g := by
  ext i; match i with | 0 => exact h0 ▸ rfl
/-
**SimplexCategory.eq_const_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：eq_const_of_zero {n : SimplexCategory} (f : ⦋0⦌ ⟶ n) : f = const _ n (f.to
OrderHom 0)
参数：f : ⦋0⦌ ⟶ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
-/
theorem eq_const_of_zero {n : SimplexCategory} (f : ⦋0⦌ ⟶ n) :
    f = const _ n (f.toOrderHom 0) := by
  ext x; match x with | 0 => rfl
/-
**SimplexCategory.exists_eq_const_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCate
gory`。
形式化陈述：exists_eq_const_of_zero {n : SimplexCategory} (f : ⦋0⦌ ⟶ n) : exists a, f 
= const _ n a
参数：f : ⦋0⦌ ⟶ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimplexCategory.eq_const_of_zero`：eq_const_of_zero {n : SimplexCategory}
 (f : ⦋0⦌ ⟶ n) : f = const _ n (f.toOrderHom 0)
-/
theorem exists_eq_const_of_zero {n : SimplexCategory} (f : ⦋0⦌ ⟶ n) :
    ∃ a, f = const _ n a := ⟨_, eq_const_of_zero _⟩
/-
**SimplexCategory.eq_const_to_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：eq_const_to_zero {n : SimplexCategory} (f : n ⟶ ⦋0⦌) : f = const n _ 0
参数：f : n ⟶ ⦋0⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
-/
theorem eq_const_to_zero {n : SimplexCategory} (f : n ⟶ ⦋0⦌) :
    f = const n _ 0 := by
  ext : 3
  apply @Subsingleton.elim (Fin 1)
/-
**SimplexCategory.Hom.ext_one_left** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.Ho
m`。
形式化陈述：∀ {n : SimplexCategory} (f g : { len := 1 } ⟶ n),   autoParam ((SimplexCat
egory.Hom.toOrderHom f) 0 = (SimplexCategory.Hom.toOrderHom g) 0)       SimplexC
ategory.Hom.ext_one_left._auto_1 →     autoParam ((SimplexCategory.Hom.toOrderHo
m f) 1 = (SimplexCategory.Hom.toOrderHom g) 1)         SimplexCategory.Hom.ext_o
ne_left._auto_3 →       f = g
参数：f g : { len := 1 } ⟶ n；(SimplexCategory.Hom.toOrderHom f) 0 = (SimplexCategor
y.Hom.toOrderHom g) 0；(SimplexCategory.Hom.toOrderHom f) 1 = (SimplexCategory.Ho
m.toOrderHom g) 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
-/
theorem Hom.ext_one_left {n : SimplexCategory} (f g : ⦋1⦌ ⟶ n)
    (h0 : f.toOrderHom 0 = g.toOrderHom 0 := by rfl)
    (h1 : f.toOrderHom 1 = g.toOrderHom 1 := by rfl) : f = g := by
  ext i
  match i with
  | 0 => exact h0 ▸ rfl
  | 1 => exact h1 ▸ rfl
/-
**SimplexCategory.eq_of_one_to_one** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：eq_of_one_to_one (f : ⦋1⦌ ⟶ ⦋1⦌) : (exists a, f = const ⦋1⦌ _ a) ∨ f = 𝟙 _
参数：f : ⦋1⦌ ⟶ ⦋1⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem eq_of_one_to_one (f : ⦋1⦌ ⟶ ⦋1⦌) :
    (∃ a, f = const ⦋1⦌ _ a) ∨ f = 𝟙 _ := by
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 0, 0 | 1, 1 =>
    refine .inl ⟨f.toOrderHom 0, ?_⟩
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 0, 1 =>
    right
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 1, 0 =>
    have := f.toOrderHom.monotone (by decide : (0 : Fin 2) ≤ 1)
    rw [e0, e1] at this
    exact Not.elim (by decide) this

/-- Make a morphism `⦋n⦌ ⟶ ⦋m⦌` from a monotone map between fin's.
This is useful for constructing morphisms between `⦋n⦌` directly
without identifying `n` with `⦋n⦌.len`.
-/
@[simp]
/-
**SimplexCategory.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：mkHom {n m : Nat} (f : Fin (n + 1) ->o Fin (m + 1)) : ⦋n⦌ ⟶ ⦋m⦌
参数：f : Fin (n + 1) ->o Fin (m + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a morphism `⦋n⦌ ⟶ ⦋m⦌` from a monotone map between fin's.
This is useful for constructing morphisms between `⦋n⦌` directly
without identifying `n` with `⦋n⦌.len`.
-/
def mkHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) : ⦋n⦌ ⟶ ⦋m⦌ :=
  SimplexCategory.Hom.mk f

/-- The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out a specified `h : i ≤ j` in `Fin (n+1)`. -/
/-
**SimplexCategory.mkOfLe** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：mkOfLe {n} (i j : Fin (n + 1)) (h : i <= j) : ⦋1⦌ ⟶ ⦋n⦌
参数：i j : Fin (n + 1)；h : i <= j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out a specified `h : i ≤ j` in `Fin (n+1)`.
-/
def mkOfLe {n} (i j : Fin (n + 1)) (h : i ≤ j) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => h
  }

@[simp]
/-
**SimplexCategory.mkOfLe_refl** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：mkOfLe_refl {n} (j : Fin (n + 1)) : mkOfLe j j (by lia) = ⦋1⦌.const ⦋n⦌ j
参数：j : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext_one_left`：∀ {n : SimplexCategory} (f g : { len :
= 1 } ⟶ n),   autoParam ((SimplexCategory.Hom.toOrderHom f) 0 = (SimplexCategory
.Hom.toOrderHom g) 0) …
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma mkOfLe_refl {n} (j : Fin (n + 1)) :
    mkOfLe j j (by lia) = ⦋1⦌.const ⦋n⦌ j := Hom.ext_one_left _ _

/-- The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out the "diagonal composite" edge -/
/-
**SimplexCategory.diag** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：diag (n : Nat) : ⦋1⦌ ⟶ ⦋n⦌
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out the "diagonal composite" edge
-/
def diag (n : ℕ) : ⦋1⦌ ⟶ ⦋n⦌ :=
  mkOfLe 0 (Fin.last n) (Fin.zero_le _)

/-- The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out the edge spanning the interval from `j` to `j + l`. -/
/-
**SimplexCategory.intervalEdge** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：intervalEdge {n} (j l : Nat) (hjl : j + l <= n) : ⦋1⦌ ⟶ ⦋n⦌
参数：j l : Nat；hjl : j + l <= n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k

--- 原说明 ---
The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out the edge spanning the interval from `j` 
to `j + l`.
-/
def intervalEdge {n} (j l : ℕ) (hjl : j + l ≤ n) : ⦋1⦌ ⟶ ⦋n⦌ :=
  mkOfLe ⟨j, (by lia)⟩ ⟨j + l, (by lia)⟩ (Nat.le_add_right j l)

/-- The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out the arrow `i ⟶ i+1` in `Fin (n+1)`. -/
/-
**SimplexCategory.mkOfSucc** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：mkOfSucc {n} (i : Fin n) : ⦋1⦌ ⟶ ⦋n⦌
参数：i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out the arrow `i ⟶ i+1` in `Fin (n+1)`.
-/
def mkOfSucc {n} (i : Fin n) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i.castSucc | 1 => i.succ
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => Fin.castSucc_le_succ i
  }

@[simp]
/-
**SimplexCategory.mkOfSucc_homToOrderHom_zero** 是 Mathlib 中的一个引理，位于命名空间 `Simplex
Category`。
形式化陈述：mkOfSucc_homToOrderHom_zero {n} (i : Fin n) : DFunLike.coe (F
参数：i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma mkOfSucc_homToOrderHom_zero {n} (i : Fin n) :
    DFunLike.coe (F := Fin 2 →o Fin (n + 1)) (Hom.toOrderHom (mkOfSucc i)) 0 = i.castSucc := rfl

@[simp]
/-
**SimplexCategory.mkOfSucc_homToOrderHom_one** 是 Mathlib 中的一个引理，位于命名空间 `SimplexC
ategory`。
形式化陈述：mkOfSucc_homToOrderHom_one {n} (i : Fin n) : DFunLike.coe (F
参数：i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma mkOfSucc_homToOrderHom_one {n} (i : Fin n) :
    DFunLike.coe (F := Fin 2 →o Fin (n + 1)) (Hom.toOrderHom (mkOfSucc i)) 1 = i.succ := rfl

@[simp]
/-
**SimplexCategory.mkOfSucc_eq_id** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：mkOfSucc_eq_id : mkOfSucc (0 : Fin 1) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma mkOfSucc_eq_id : mkOfSucc (0 : Fin 1) = 𝟙 _ := by decide

/-- The morphism `⦋2⦌ ⟶ ⦋n⦌` that picks out a specified composite of morphisms in `Fin (n+1)`. -/
/-
**SimplexCategory.mkOfLeComp** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：mkOfLeComp {n} (i j k : Fin (n + 1)) (h₁ : i <= j) (h₂ : j <= k) : ⦋2⦌ ⟶ ⦋
n⦌
参数：i j k : Fin (n + 1)；h₁ : i <= j；h₂ : j <= k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `⦋2⦌ ⟶ ⦋n⦌` that picks out a specified composite of morphisms in `F
in (n+1)`.
-/
def mkOfLeComp {n} (i j k : Fin (n + 1)) (h₁ : i ≤ j) (h₂ : j ≤ k) :
    ⦋2⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j | 2 => k
    monotone' := fun
      | 0, 0, _ | 1, 1, _ | 2, 2, _ => le_rfl
      | 0, 1, _ => h₁
      | 1, 2, _ => h₂
      | 0, 2, _ => Fin.le_trans h₁ h₂
  }

/-- The "inert" morphism associated to a subinterval `j ≤ i ≤ j + l` of `Fin (n + 1)`. -/
/-
**SimplexCategory.subinterval** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：subinterval {n} (j l : Nat) (hjl : j + l <= n) : ⦋l⦌ ⟶ ⦋n⦌
参数：j l : Nat；hjl : j + l <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "inert" morphism associated to a subinterval `j ≤ i ≤ j + l` of `Fin (n + 1)
`.
-/
def subinterval {n} (j l : ℕ) (hjl : j + l ≤ n) :
    ⦋l⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun i => ⟨i.1 + j, (by lia)⟩
    monotone' := fun i i' hii' => by simpa only [Fin.mk_le_mk, add_le_add_iff_right] using! hii'
  }

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimplexCategory.const_subinterval_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategor
y`。
形式化陈述：const_subinterval_eq {n} (j l : Nat) (hjl : j + l <= n) (i : Fin (l + 1)) 
: ⦋0⦌.const ⦋l⦌ i ≫ subinterval j l hjl = ⦋0⦌.const ⦋n⦌ ⟨j + i.1, lt_add_of_lt_a
dd_right (Nat.add_lt_add_left i.2 j) hjl⟩
参数：j l : Nat；hjl : j + l <= n；i : Fin (l + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_add_of_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddRightMono α] {a b c d : α}, a < b + c → b ≤ d → a < d + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimplexCategory.const_comp`：const_comp (x : SimplexCategory) {y z : Simp
lexCategory} (f : y ⟶ z) (i : Fin (y.len + 1)) : const x y i ≫ f = const x z (f.
toOrderHom i)
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma const_subinterval_eq {n} (j l : ℕ) (hjl : j + l ≤ n) (i : Fin (l + 1)) :
    ⦋0⦌.const ⦋l⦌ i ≫ subinterval j l hjl =
    ⦋0⦌.const ⦋n⦌ ⟨j + i.1, lt_add_of_lt_add_right (Nat.add_lt_add_left i.2 j) hjl⟩  := by
  rw [const_comp]
  congr
  ext
  dsimp [subinterval]
  rw [add_comm]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SimplexCategory.mkOfSucc_subinterval_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCate
gory`。
形式化陈述：mkOfSucc_subinterval_eq {n} (j l : Nat) (hjl : j + l <= n) (i : Fin l) : m
kOfSucc i ≫ subinterval j l hjl = mkOfSucc ⟨j + i.1, Nat.lt_of_lt_of_le (Nat.add
_lt_add_left i.2 j) hjl⟩
参数：j l : Nat；hjl : j + l <= n；i : Fin l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma mkOfSucc_subinterval_eq {n} (j l : ℕ) (hjl : j + l ≤ n) (i : Fin l) :
    mkOfSucc i ≫ subinterval j l hjl =
    mkOfSucc ⟨j + i.1, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.2 j) hjl⟩ := by
  unfold subinterval mkOfSucc
  ext (i : Fin 2)
  match i with | 0 | 1 => simp; lia

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SimplexCategory.diag_subinterval_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory
`。
形式化陈述：diag_subinterval_eq {n} (j l : Nat) (hjl : j + l <= n) : diag l ≫ subinter
val j l hjl = intervalEdge j l hjl
参数：j l : Nat；hjl : j + l <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma diag_subinterval_eq {n} (j l : ℕ) (hjl : j + l ≤ n) :
    diag l ≫ subinterval j l hjl = intervalEdge j l hjl := by
  unfold subinterval intervalEdge diag mkOfLe
  ext (i : Fin 2)
  match i with | 0 | 1 => simp <;> lia
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Δ : SimplexCategory) : Subsingleton (Δ ⟶ ⦋0⦌) where
  allEq f g := by ext : 3; apply Subsingleton.elim (α := Fin 1)
/-
**SimplexCategory.hom_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：hom_zero_zero (f : ⦋0⦌ ⟶ ⦋0⦌) : f = 𝟙 _
参数：f : ⦋0⦌ ⟶ ⦋0⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SimplexCategory.instSubsingletonHomMkOfNatNat`：∀ (Δ : SimplexCategory), 
Subsingleton (Δ ⟶ { len := 0 })
-/
theorem hom_zero_zero (f : ⦋0⦌ ⟶ ⦋0⦌) : f = 𝟙 _ := by
  apply Subsingleton.elim

@[simp]
/-
**SimplexCategory.eqToHom_toOrderHom** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`
。
形式化陈述：eqToHom_toOrderHom {x y : SimplexCategory} (h : x = y) : SimplexCategory.H
om.toOrderHom (eqToHom h) = (Fin.castOrderIso (congrArg (fun t => t.len + 1) h))
.toOrderEmbedding.toOrderHom
参数：h : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma eqToHom_toOrderHom {x y : SimplexCategory} (h : x = y) :
  SimplexCategory.Hom.toOrderHom (eqToHom h) =
    (Fin.castOrderIso (congrArg (fun t ↦ t.len + 1) h)).toOrderEmbedding.toOrderHom := by
  subst h
  rfl

end Init

section Generators

/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/

/-- The `i`-th face map from `⦋n⦌` to `⦋n+1⦌` -/
/-
**SimplexCategory.** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th face map from `⦋n⦌` to `⦋n+1⦌`
-/
def δ {n} (i : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋n + 1⦌ :=
  mkHom (Fin.succAboveOrderEmb i).toOrderHom

/-- The `i`-th degeneracy map from `⦋n+1⦌` to `⦋n⦌` -/
/-
**SimplexCategory.** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th degeneracy map from `⦋n+1⦌` to `⦋n⦌`
-/
def σ {n} (i : Fin (n + 1)) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  mkHom i.predAboveOrderHom

set_option backward.defeqAttrib.useBackward true in
/-- The generic case of the first simplicial identity -/
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generic case of the first simplicial identity
-/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc := by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> lia
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.castSucc < j) :
    δ i ≫ δ j =
      δ (j.pred H.ne_zero) ≫
        δ (Fin.castSucc i) := by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_def] using! H
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ δ j.succ =
      δ j ≫ δ i := by
  rw [δ_comp_δ]
  · rfl
  · exact H

/-- The special case of the first simplicial identity -/
@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The special case of the first simplicial identity
-/
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : δ i ≫ δ i.castSucc = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_refl i)).symm

@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = i.castSucc) :
    δ i ≫ δ j = δ i ≫ δ i.succ := by
  subst H
  rw [δ_comp_δ_self]

set_option backward.defeqAttrib.useBackward true in
/-- The second simplicial identity -/
@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second simplicial identity
-/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) :
    δ i.castSucc ≫ σ j.succ = σ j ≫ δ i := by
  ext k : 3
  dsimp [σ, δ]
  rcases le_or_gt i k with (hik | hik)
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hik),
    Fin.succ_predAbove_succ, Fin.succAbove_of_le_castSucc]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rwa [Fin.predAbove_of_le_castSucc _ _ hjk, Fin.castSucc_castPred]
    · rw [Fin.le_castSucc_iff, Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.succ_pred]
      exact H.trans_lt hjk
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hik)]
    have hjk := H.trans_lt' hik
    rw [Fin.predAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr
      (hjk.trans Fin.castSucc_lt_succ).le),
      Fin.predAbove_of_le_castSucc _ _ hjk.le, Fin.castPred_castSucc, Fin.succAbove_of_castSucc_lt,
      Fin.castSucc_castPred]
    rwa [Fin.castSucc_castPred]

set_option backward.defeqAttrib.useBackward true in
/-- The first part of the third simplicial identity -/
@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first part of the third simplicial identity
-/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ (Fin.castSucc i) ≫ σ i = 𝟙 ⦋n⦌ := by
  rcases i with ⟨i, hi⟩
  ext ⟨j, hj⟩
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_def, Fin.dite_val, Fin.ite_val, Fin.val_pred]
  split_ifs
  any_goals simp
  all_goals lia

@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.castSucc) :
    δ j ≫ σ i = 𝟙 ⦋n⦌ := by
  subst H
  rw [δ_comp_σ_self]

set_option backward.defeqAttrib.useBackward true in
/-- The second part of the third simplicial identity -/
@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second part of the third simplicial identity
-/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 ⦋n⦌ := by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  split_ifs <;> simp <;> simp at * <;> lia

@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    δ j ≫ σ i = 𝟙 ⦋n⦌ := by
  subst H
  rw [δ_comp_σ_succ]

set_option backward.defeqAttrib.useBackward true in
/-- The fourth simplicial identity -/
@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fourth simplicial identity
-/
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) :
    δ i.succ ≫ σ j.castSucc = σ j ≫ δ i := by
  ext k : 3
  dsimp [δ, σ]
  rcases le_or_gt k i with (hik | hik)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hik)]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rw [Fin.predAbove_of_le_castSucc _ _
      (Fin.castSucc_le_castSucc_iff.mpr hjk), Fin.castPred_castSucc,
      Fin.predAbove_of_le_castSucc _ _ hjk, Fin.succAbove_of_castSucc_lt, Fin.castSucc_castPred]
      rw [Fin.castSucc_castPred]
      exact hjk.trans_lt H
    · rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hjk),
      Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.succAbove_of_castSucc_lt,
      Fin.castSucc_pred_eq_pred_castSucc]
      rwa [Fin.castSucc_lt_iff_succ_le, Fin.succ_pred]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr hik)]
    have hjk := H.trans hik
    rw [Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.predAbove_of_castSucc_lt _ _
      (Fin.castSucc_lt_succ_iff.mpr hjk.le),
    Fin.pred_succ, Fin.succAbove_of_le_castSucc, Fin.succ_pred]
    rwa [Fin.le_castSucc_pred_iff]

@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    δ i ≫ σ j = σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
      δ (i.pred H.ne_zero) := by
  rw [← δ_comp_σ_of_gt]
  · simp
  · rw [Fin.castSucc_castLT, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact H

set_option backward.defeqAttrib.useBackward true in
/-- The fifth simplicial identity -/
@[reassoc]
/-
**SimplexCategory.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fifth simplicial identity
-/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ (Fin.castSucc i) ≫ σ j = σ j.succ ≫ σ i := by
  ext k : 3
  dsimp [σ]
  cases k using Fin.lastCases with
  | last => simp only [len_mk, Fin.predAbove_right_last]
  | cast k =>
    cases k using Fin.cases with
    | zero =>
      simp
    | succ k =>
      rcases le_or_gt i k with (h | h)
      · simp_rw [Fin.predAbove_of_castSucc_lt i.castSucc _ (Fin.castSucc_lt_castSucc_iff.mpr
        (Fin.castSucc_lt_succ_iff.mpr h)), ← Fin.succ_castSucc, Fin.pred_succ,
        Fin.succ_predAbove_succ]
        rw [Fin.predAbove_of_castSucc_lt i _ (Fin.castSucc_lt_succ_iff.mpr _), Fin.pred_succ]
        rcases le_or_gt k j with (hkj | hkj)
        · rwa [Fin.predAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hkj),
          Fin.castPred_castSucc]
        · rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hkj),
          Fin.le_pred_iff,
          Fin.succ_le_castSucc_iff]
          exact H.trans_lt hkj
      · simp_rw [Fin.predAbove_of_le_castSucc i.castSucc _ (Fin.castSucc_le_castSucc_iff.mpr
        (Fin.succ_le_castSucc_iff.mpr h)), Fin.castPred_castSucc, ← Fin.succ_castSucc,
        Fin.succ_predAbove_succ]
        rw [Fin.predAbove_of_le_castSucc _ k.castSucc
        (Fin.castSucc_le_castSucc_iff.mpr (h.le.trans H)),
        Fin.castPred_castSucc, Fin.predAbove_of_le_castSucc _ k.succ
        (Fin.succ_le_castSucc_iff.mpr (H.trans_lt' h)), Fin.predAbove_of_le_castSucc _ k.succ
        (Fin.succ_le_castSucc_iff.mpr h)]
/-
**SimplexCategory.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_zero_eq_const : δ (0 : Fin 2) = const _ _ 1 := by decide
/-
**SimplexCategory.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_one_eq_const : δ (1 : Fin 2) = const _ _ 0 := by decide

/--
If `f : ⦋m⦌ ⟶ ⦋n+1⦌` is a morphism and `j` is not in the range of `f`,
then `factor_δ f j` is a morphism `⦋m⦌ ⟶ ⦋n⦌` such that
`factor_δ f j ≫ δ j = f` (as witnessed by `factor_δ_spec`).
-/
/-
**SimplexCategory.factor_** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : ⦋m⦌ ⟶ ⦋n+1⦌` is a morphism and `j` is not in the range of `f`,
then `factor_δ f j` is a morphism `⦋m⦌ ⟶ ⦋n⦌` such that
`factor_δ f j ≫ δ j = f` (as witnessed by `factor_δ_spec`).
-/
def factor_δ {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2)) : ⦋m⦌ ⟶ ⦋n⦌ :=
  f ≫ σ (Fin.predAbove 0 j)
/-
**SimplexCategory.factor_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma factor_δ_spec {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2))
    (hj : ∀ (k : Fin (m + 1)), f.toOrderHom k ≠ j) :
    factor_δ f j ≫ δ j = f := by
  ext k : 3
  cases j using Fin.cases <;> simp_all [factor_δ, δ, σ]

@[simp]
/-
**SimplexCategory.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_zero_mkOfSucc {n : ℕ} (i : Fin n) :
    δ 0 ≫ mkOfSucc i = SimplexCategory.const _ ⦋n⦌ i.succ := by
  ext x
  fin_cases x
  rfl

@[simp]
/-
**SimplexCategory.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_one_mkOfSucc {n : ℕ} (i : Fin n) :
    δ 1 ≫ mkOfSucc i = SimplexCategory.const _ ⦋n⦌ i.castSucc := by
  ext x
  fin_cases x
  rfl

/-- If `i + 1 < j`, `mkOfSucc i ≫ δ j` is the morphism `⦋1⦌ ⟶ ⦋n⦌` that
sends `0` and `1` to `i` and `i + 1`, respectively. -/
/-
**SimplexCategory.mkOfSucc_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i + 1 < j`, `mkOfSucc i ≫ δ j` is the morphism `⦋1⦌ ⟶ ⦋n⦌` that
sends `0` and `1` to `i` and `i + 1`, respectively.
-/
lemma mkOfSucc_δ_lt {n : ℕ} {i : Fin n} {j : Fin (n + 2)}
    (h : i.succ.castSucc < j) :
    mkOfSucc i ≫ δ j = mkOfSucc i.castSucc := by
  ext x
  fin_cases x
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ (Nat.lt_trans _ h)]
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ h]

/-- If `i + 1 > j`, `mkOfSucc i ≫ δ j` is the morphism `⦋1⦌ ⟶ ⦋n⦌` that
sends `0` and `1` to `i + 1` and `i + 2`, respectively. -/
/-
**SimplexCategory.mkOfSucc_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i + 1 > j`, `mkOfSucc i ≫ δ j` is the morphism `⦋1⦌ ⟶ ⦋n⦌` that
sends `0` and `1` to `i + 1` and `i + 2`, respectively.
-/
lemma mkOfSucc_δ_gt {n : ℕ} {i : Fin n} {j : Fin (n + 2)}
    (h : j < i.succ.castSucc) :
    mkOfSucc i ≫ δ j = mkOfSucc i.succ := by
  ext x
  simp only [δ, len_mk, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply]
  fin_cases x <;> rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · exact Nat.le_of_lt_succ h
  · rfl
  · exact Nat.le_of_lt h

/-- If `i + 1 = j`, `mkOfSucc i ≫ δ j` is the morphism `⦋1⦌ ⟶ ⦋n⦌` that
sends `0` and `1` to `i` and `i + 2`, respectively. -/
/-
**SimplexCategory.mkOfSucc_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i + 1 = j`, `mkOfSucc i ≫ δ j` is the morphism `⦋1⦌ ⟶ ⦋n⦌` that
sends `0` and `1` to `i` and `i + 2`, respectively.
-/
lemma mkOfSucc_δ_eq {n : ℕ} {i : Fin n} {j : Fin (n + 2)}
    (h : j = i.succ.castSucc) :
    mkOfSucc i ≫ δ j = intervalEdge i 2 (by lia) := by
  ext x
  fin_cases x
  · subst h
    simp only [δ, len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk,
      Fin.zero_eta, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      mkOfSucc_homToOrderHom_zero, Fin.succAboveOrderEmb_apply,
      Fin.castSucc_succAbove_castSucc, Fin.succAbove_succ_self]
    rfl
  · simp only [δ, len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, Fin.mk_one,
      OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      mkOfSucc_homToOrderHom_one, Fin.succAboveOrderEmb_apply]
    subst h
    rw [Fin.succAbove_castSucc_self]
    rfl
/-
**SimplexCategory.mkOfSucc_one_eq_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkOfSucc_one_eq_δ : mkOfSucc (1 : Fin 2) = δ 0 := by decide
/-
**SimplexCategory.mkOfSucc_zero_eq_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkOfSucc_zero_eq_δ : mkOfSucc (0 : Fin 2) = δ 2 := by decide
/-
**SimplexCategory.eq_of_one_to_two** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：eq_of_one_to_two (f : ⦋1⦌ ⟶ ⦋2⦌) : (exists i, f = (δ (n
参数：f : ⦋1⦌ ⟶ ⦋2⦌。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem eq_of_one_to_two (f : ⦋1⦌ ⟶ ⦋2⦌) :
    (∃ i, f = (δ (n := 1) i)) ∨ ∃ a, f = SimplexCategory.const _ _ a := by
  have : f.toOrderHom 0 ≤ f.toOrderHom 1 := f.toOrderHom.monotone (by decide : (0 : Fin 2) ≤ 1)
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 1, 2 =>
    refine .inl ⟨0, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 2 =>
    refine .inl ⟨1, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 1 =>
    refine .inl ⟨2, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 0 | 1, 1 | 2, 2 =>
    refine .inr ⟨f.toOrderHom 0, ?_⟩
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 1, 0 | 2, 0 | 2, 1 =>
    rw [e0, e1] at this
    exact Not.elim (by decide) this
/-
**SimplexCategory.eq_of_one_to_two'** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：eq_of_one_to_two' (f : ⦋1⦌ ⟶ ⦋2⦌) : f = (δ (n
参数：f : ⦋1⦌ ⟶ ⦋2⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimplexCategory.eq_of_one_to_two`：eq_of_one_to_two (f : ⦋1⦌ ⟶ ⦋2⦌) : (ex
ists i, f = (δ (n
-/
theorem eq_of_one_to_two' (f : ⦋1⦌ ⟶ ⦋2⦌) :
    f = (δ (n := 1) 0) ∨ f = (δ (n := 1) 1) ∨ f = (δ (n := 1) 2) ∨
      ∃ a, f = SimplexCategory.const _ _ a :=
  match eq_of_one_to_two f with
  | .inl ⟨0, h⟩ => .inl h
  | .inl ⟨1, h⟩ => .inr (.inl h)
  | .inl ⟨2, h⟩ => .inr (.inr (.inl h))
  | .inr h => .inr (.inr (.inr h))

end Generators

section Skeleton

/-- The functor that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
/-
**SimplexCategory.skeletalFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrd where obj a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd`
-/
def skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrd where
  obj a := NonemptyFinLinOrd.of (Fin (a.len + 1))
  map f := NonemptyFinLinOrd.ofHom f.toOrderHom
/-
**SimplexCategory.skeletalFunctor.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCate
gory.skeletalFunctor`。
形式化陈述：∀ {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂),   LinOrd.Hom.hom (SimplexCatego
ry.skeletalFunctor.map f).hom = SimplexCategory.Hom.toOrderHom f
参数：f : Δ₁ ⟶ Δ₂；SimplexCategory.skeletalFunctor.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    ↑(skeletalFunctor.map f).hom.hom = f.toOrderHom :=
  rfl
/-
**SimplexCategory.skeletal** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：skeletal : Skeletal SimplexCategory
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `SimplexCategory.ext`：∀ {x y : SimplexCategory}, x.len = y.len → x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem skeletal : Skeletal SimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1)) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget NonemptyFinLinOrd).mapIso I).toEquiv

namespace SkeletalFunctor

/-
**SimplexCategory.SkeletalFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory.Sk
eletalFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : skeletalFunctor.Full where
  map_surjective f := ⟨SimplexCategory.Hom.mk f.hom.hom, rfl⟩
/-
**SimplexCategory.SkeletalFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory.Sk
eletalFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : skeletalFunctor.Faithful where
  map_injective {_ _ f g} h := by
    ext : 3
    exact CategoryTheory.congr_fun h _
/-
**SimplexCategory.SkeletalFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory.Sk
eletalFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : skeletalFunctor.EssSurj where
  mem_essImage X :=
    ⟨⦋(Fintype.card X - 1 : ℕ)⦌,
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| Fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (Finset.univ.orderEmbOfFin aux).strictMono
        refine
          { hom := InducedCategory.homMk (LinOrd.ofHom ⟨f, hf.monotone⟩)
            inv := InducedCategory.homMk (LinOrd.ofHom ⟨f.symm, ?_⟩)
            hom_inv_id := by ext; apply f.symm_apply_apply
            inv_hom_id := by ext; apply f.apply_symm_apply }
        intro i j h
        change f.symm i ≤ f.symm j
        rw [← hf.le_iff_le]
        change f (f.symm i) ≤ f (f.symm j)
        simpa only [OrderIso.apply_symm_apply]⟩⟩
/-
**SimplexCategory.SkeletalFunctor.isEquivalence** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
exCategory.SkeletalFunctor`。
形式化陈述：SimplexCategory.skeletalFunctor.IsEquivalence
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.SkeletalFunctor.instFaithfulNonemptyFinLinOrdSkeletalFun
ctor`：SimplexCategory.skeletalFunctor.Faithful
· 使用定理 `SimplexCategory.SkeletalFunctor.instFullNonemptyFinLinOrdSkeletalFunctor
`：SimplexCategory.skeletalFunctor.Full
· 使用定理 `SimplexCategory.SkeletalFunctor.instEssSurjNonemptyFinLinOrdSkeletalFunc
tor`：SimplexCategory.skeletalFunctor.EssSurj
-/
noncomputable instance isEquivalence : skeletalFunctor.IsEquivalence where

end SkeletalFunctor

/-- The equivalence that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
/-
**SimplexCategory.skeletalEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory
`。
形式化陈述：skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrd
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.SkeletalFunctor.isEquivalence`：SimplexCategory.skeletalF
unctor.IsEquivalence

--- 原说明 ---
The equivalence that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd`
-/
noncomputable def skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrd :=
  Functor.asEquivalence skeletalFunctor

end Skeleton

/-- `SimplexCategory` is a skeleton of `NonemptyFinLinOrd`.
-/
/-
**SimplexCategory.isSkeletonOf** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：isSkeletonOf : IsSkeletonOf NonemptyFinLinOrd SimplexCategory skeletalFunc
tor where skel
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.skeletal`：skeletal : Skeletal SimplexCategory
· 使用定理 `SimplexCategory.SkeletalFunctor.isEquivalence`：SimplexCategory.skeletalF
unctor.IsEquivalence

--- 原说明 ---
`SimplexCategory` is a skeleton of `NonemptyFinLinOrd`.
-/
lemma isSkeletonOf :
    IsSkeletonOf NonemptyFinLinOrd SimplexCategory skeletalFunctor where
  skel := skeletal
  eqv := SkeletalFunctor.isEquivalence

section Concrete

/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory SimplexCategory (fun i j => Fin (i.len + 1) →o Fin (j.len + 1)) where
  hom := Hom.toOrderHom
  ofHom f := Hom.mk f
/-
**SimplexCategory.toType_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：toType_apply (x : SimplexCategory) : ToType x = Fin (x.len + 1)
参数：x : SimplexCategory。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toType_apply (x : SimplexCategory) : ToType x = Fin (x.len + 1) := rfl

@[simp]
/-
**SimplexCategory.concreteCategoryHom_id** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCateg
ory`。
形式化陈述：concreteCategoryHom_id (n : SimplexCategory) : ConcreteCategory.hom (𝟙 n) 
= .id
参数：n : SimplexCategory。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma concreteCategoryHom_id (n : SimplexCategory) : ConcreteCategory.hom (𝟙 n) = .id := rfl
/-
**SimplexCategory.coe_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_δ {n : ℕ} (i : Fin (n + 2)) :
    dsimp% ⇑(δ i) = Fin.succAbove i := rfl
/-
**SimplexCategory.coe_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_σ {n : ℕ} (i : Fin (n + 1)) :
    dsimp% ⇑(σ i) = Fin.predAbove i := rfl

end Concrete

section EpiMono

set_option backward.defeqAttrib.useBackward true in
/-- A morphism in `SimplexCategory` is a monomorphism precisely when it is an injective function
-/
/-
**SimplexCategory.mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`
。
形式化陈述：mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} : Mono f ↔ Function
.Injective f.toOrderHom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.mono_map_iff_mono`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A morphism in `SimplexCategory` is a monomorphism precisely when it is an inject
ive function
-/
theorem mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} :
    Mono f ↔ Function.Injective f.toOrderHom := by
  rw [← Functor.mono_map_iff_mono skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.mono_iff_injective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

set_option backward.defeqAttrib.useBackward true in
/-- A morphism in `SimplexCategory` is an epimorphism if and only if it is a surjective function
-/
/-
**SimplexCategory.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`
。
形式化陈述：epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} : Epi f ↔ Function.
Surjective f.toOrderHom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.epi_map_iff_epi`：epi_map_iff_epi [hF₁ : Preserves
Epimorphisms F] [hF₂ : ReflectsEpimorphisms F] : Epi (F.map f) ↔ Epi f
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape`：∀ {C : T
ype u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A morphism in `SimplexCategory` is an epimorphism if and only if it is a surject
ive function
-/
theorem epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} :
    Epi f ↔ Function.Surjective f.toOrderHom := by
  rw [← Functor.epi_map_iff_epi skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.epi_iff_surjective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

/-- A monomorphism in `SimplexCategory` must increase lengths -/
/-
**SimplexCategory.len_le_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：len_le_of_mono {x y : SimplexCategory} (f : x ⟶ y) [Mono f] : x.len <= y.l
en
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimplexCategory.mono_iff_injective`：mono_iff_injective {n m : SimplexCat
egory} {f : n ⟶ m} : Mono f ↔ Function.Injective f.toOrderHom

--- 原说明 ---
A monomorphism in `SimplexCategory` must increase lengths
-/
theorem len_le_of_mono {x y : SimplexCategory} (f : x ⟶ y) [Mono f] : x.len ≤ y.len := by
  simpa using Fintype.card_le_of_injective f.toOrderHom.toFun
    (by dsimp; rwa [← mono_iff_injective])
/-
**SimplexCategory.le_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：le_of_mono {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Mono f] : n <= m
参数：f : ⦋n⦌ ⟶ ⦋m⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.len_le_of_mono`：len_le_of_mono {x y : SimplexCategory} (
f : x ⟶ y) [Mono f] : x.len <= y.len
-/
theorem le_of_mono {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [Mono f] : n ≤ m :=
  len_le_of_mono f

/-- An epimorphism in `SimplexCategory` must decrease lengths -/
/-
**SimplexCategory.len_le_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：len_le_of_epi {x y : SimplexCategory} (f : x ⟶ y) [Epi f] : y.len <= x.len
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Fintype.card_le_of_surjective`：card_le_of_surjective (f : α -> β) (h : F
unction.Surjective f) : card β <= card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimplexCategory.epi_iff_surjective`：epi_iff_surjective {n m : SimplexCat
egory} {f : n ⟶ m} : Epi f ↔ Function.Surjective f.toOrderHom

--- 原说明 ---
An epimorphism in `SimplexCategory` must decrease lengths
-/
theorem len_le_of_epi {x y : SimplexCategory} (f : x ⟶ y) [Epi f] : y.len ≤ x.len := by
  simpa using Fintype.card_le_of_surjective f.toOrderHom.toFun
    (by dsimp; rwa [← epi_iff_surjective])
/-
**SimplexCategory.le_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：le_of_epi {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] : m <= n
参数：f : ⦋n⦌ ⟶ ⦋m⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.len_le_of_epi`：len_le_of_epi {x y : SimplexCategory} (f 
: x ⟶ y) [Epi f] : y.len <= x.len
-/
theorem le_of_epi {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] : m ≤ n := len_le_of_epi f
/-
**SimplexCategory.len_eq_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：len_eq_of_isIso {x y : SimplexCategory} (f : x ⟶ y) [IsIso f] : x.len = y.
len
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimplexCategory.len_le_of_mono`：len_le_of_mono {x y : SimplexCategory} (
f : x ⟶ y) [Mono f] : x.len <= y.len
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `SimplexCategory.len_le_of_epi`：len_le_of_epi {x y : SimplexCategory} (f 
: x ⟶ y) [Epi f] : y.len <= x.len
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
lemma len_eq_of_isIso {x y : SimplexCategory} (f : x ⟶ y) [IsIso f] : x.len = y.len :=
  le_antisymm (len_le_of_mono f) (len_le_of_epi f)
/-
**SimplexCategory.eq_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：eq_of_isIso {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [IsIso f] : n = m
参数：f : ⦋n⦌ ⟶ ⦋m⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimplexCategory.len_eq_of_isIso`：len_eq_of_isIso {x y : SimplexCategory}
 (f : x ⟶ y) [IsIso f] : x.len = y.len
-/
lemma eq_of_isIso {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [IsIso f] : n = m :=
  len_eq_of_isIso f
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} {i : Fin (n + 1)} : Epi (σ i) := by
  simpa only [epi_iff_surjective] using! Fin.predAbove_surjective i
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget SimplexCategory).ReflectsIsomorphisms :=
  ⟨fun f hf =>
    Iso.isIso_hom
      { hom := f
        inv := Hom.mk
            { toFun := inv ((forget SimplexCategory).map f)
              monotone' := fun y₁ y₂ h => by
                by_cases h' : y₁ < y₂
                · by_contra h''
                  apply not_le.mpr h'
                  convert! f.toOrderHom.monotone (le_of_not_ge h'')
                  all_goals
                    exact (ConcreteCategory.congr_hom (Iso.inv_hom_id
                      (asIso ((forget SimplexCategory).map f))) _).symm
                · rw [eq_of_le_of_not_lt h h'] }
        hom_inv_id := by
          ext x : 3
          exact Iso.hom_inv_id_apply (asIso ((forget _).map f)) x
        inv_hom_id := by
          ext x : 3
          exact Iso.inv_hom_id_apply (asIso ((forget _).map f)) x }⟩
/-
**SimplexCategory.isIso_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`
。
形式化陈述：isIso_of_bijective {x y : SimplexCategory} {f : x ⟶ y} (hf : Function.Bije
ctive f.toOrderHom.toFun) : IsIso f
参数：hf : Function.Bijective f.toOrderHom.toFun。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `SimplexCategory.instReflectsIsomorphismsForgetOrderHomFinHAddNatLenOfNat
`：(CategoryTheory.forget SimplexCategory).ReflectsIsomorphisms
-/
theorem isIso_of_bijective {x y : SimplexCategory} {f : x ⟶ y}
    (hf : Function.Bijective f.toOrderHom.toFun) : IsIso f :=
  haveI : IsIso ((forget SimplexCategory).map f) := (isIso_iff_bijective _).mpr hf
  isIso_of_reflects_iso f (forget SimplexCategory)
/-
**SimplexCategory.isIso_iff_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：isIso_iff_of_mono {n m : SimplexCategory} (f : n ⟶ m) [hf : Mono f] : IsIs
o f ↔ n.len = m.len
参数：f : n ⟶ m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimplexCategory.len_eq_of_isIso`：len_eq_of_isIso {x y : SimplexCategory}
 (f : x ⟶ y) [IsIso f] : x.len = y.len
· 使用定理 `SimplexCategory.isIso_of_bijective`：isIso_of_bijective {x y : SimplexCat
egory} {f : x ⟶ y} (hf : Function.Bijective f.toOrderHom.toFun) : IsIso f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimplexCategory.mono_iff_injective`：mono_iff_injective {n m : SimplexCat
egory} {f : n ⟶ m} : Mono f ↔ Function.Injective f.toOrderHom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SimplexCategory.ext`：∀ {x y : SimplexCategory}, x.len = y.len → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIso_iff_of_mono {n m : SimplexCategory} (f : n ⟶ m) [hf : Mono f] :
    IsIso f ↔ n.len = m.len := by
  refine ⟨fun _ ↦ len_eq_of_isIso f, fun h ↦ ?_⟩
  obtain rfl : n = m := by aesop
  rw [mono_iff_injective] at hf
  exact isIso_of_bijective ⟨hf, by rwa [← Finite.injective_iff_surjective]⟩
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} {i : Fin (n + 2)} : Mono (δ i) := by
  rw [mono_iff_injective]
  exact Fin.succAbove_right_injective
/-
**SimplexCategory.isIso_iff_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：isIso_iff_of_epi {n m : SimplexCategory} (f : n ⟶ m) [hf : Epi f] : IsIso 
f ↔ n.len = m.len
参数：f : n ⟶ m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimplexCategory.len_eq_of_isIso`：len_eq_of_isIso {x y : SimplexCategory}
 (f : x ⟶ y) [IsIso f] : x.len = y.len
· 使用定理 `SimplexCategory.isIso_of_bijective`：isIso_of_bijective {x y : SimplexCat
egory} {f : x ⟶ y} (hf : Function.Bijective f.toOrderHom.toFun) : IsIso f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SimplexCategory.epi_iff_surjective`：epi_iff_surjective {n m : SimplexCat
egory} {f : n ⟶ m} : Epi f ↔ Function.Surjective f.toOrderHom
· 使用定理 `SimplexCategory.ext`：∀ {x y : SimplexCategory}, x.len = y.len → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIso_iff_of_epi {n m : SimplexCategory} (f : n ⟶ m) [hf : Epi f] :
    IsIso f ↔ n.len = m.len := by
  refine ⟨fun _ ↦ len_eq_of_isIso f, fun h ↦ ?_⟩
  obtain rfl : n = m := by aesop
  rw [epi_iff_surjective] at hf
  exact isIso_of_bijective ⟨by rwa [Finite.injective_iff_surjective], hf⟩
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Balanced SimplexCategory where
  isIso_of_mono_of_epi f _ _ := by
    rw [isIso_iff_of_epi]
    exact le_antisymm (len_le_of_mono f) (len_le_of_epi f)

/-- An isomorphism in `SimplexCategory` induces an `OrderIso`. -/
@[simp]
/-
**SimplexCategory.orderIsoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：orderIsoOfIso {x y : SimplexCategory} (e : x ≅ y) : Fin (x.len + 1) ≃o Fin
 (y.len + 1)
参数：e : x ≅ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism in `SimplexCategory` induces an `OrderIso`.
-/
def orderIsoOfIso {x y : SimplexCategory} (e : x ≅ y) : Fin (x.len + 1) ≃o Fin (y.len + 1) :=
  Equiv.toOrderIso
    { toFun := e.hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using! congr_arg (fun φ => (Hom.toOrderHom φ) i) e.hom_inv_id
      right_inv := fun i => by
        simpa only using! congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_hom_id }
    e.hom.toOrderHom.monotone e.inv.toOrderHom.monotone
/-
**SimplexCategory.iso_eq_iso_refl** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x
参数：e : x ≅ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `Finset.orderEmbOfFin_unique'`：orderEmbOfFin_unique' {s : Finset α} {k : 
Nat} (h : s.card = k) {f : Fin k ↪o α} (hfs : forall x, f x in s) : f = s.orderE
mbOfFin h
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x := by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso e) i)
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso (Iso.refl x)) i)
  ext : 4
  exact DFunLike.congr_fun (eq₁.trans eq₂.symm) _
/-
**SimplexCategory.eq_id_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：eq_id_of_isIso {x : SimplexCategory} (f : x ⟶ x) [IsIso f] : f = 𝟙 _
参数：f : x ⟶ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SimplexCategory.iso_eq_iso_refl`：iso_eq_iso_refl {x : SimplexCategory} (
e : x ≅ x) : e = Iso.refl x
-/
theorem eq_id_of_isIso {x : SimplexCategory} (f : x ⟶ x) [IsIso f] : f = 𝟙 _ :=
  congr_arg (fun φ : _ ≅ _ => φ.hom) (iso_eq_iso_refl (asIso f))

set_option backward.defeqAttrib.useBackward true in
/-
**SimplexCategory.eq_** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_σ_comp_of_not_injective' {n : ℕ} {Δ' : SimplexCategory} (θ : ⦋n + 1⦌ ⟶ Δ')
    (i : Fin (n + 1)) (hi : θ.toOrderHom (Fin.castSucc i) = θ.toOrderHom i.succ) :
    ∃ θ' : ⦋n⦌ ⟶ Δ', θ = σ i ≫ θ' := by
  use δ i.succ ≫ θ
  ext x : 3
  simp only [len_mk, σ, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    Function.comp_apply, Fin.predAboveOrderHom_coe]
  by_cases h' : x ≤ Fin.castSucc i
  · rw [Fin.predAbove_of_le_castSucc i x h']
    dsimp [δ]
    rw [Fin.succAbove_of_castSucc_lt]
    · rw [Fin.castSucc_castPred]
    · exact (Fin.castSucc_lt_succ_iff.mpr h')
  · simp only [not_le] at h'
    let y := x.pred <| by rintro (rfl : x = 0); simp at h'
    have hy : x = y.succ := (Fin.succ_pred x _).symm
    rw [hy] at h' ⊢
    rw [Fin.predAbove_of_castSucc_lt i y.succ h', Fin.pred_succ]
    by_cases h'' : y = i
    · rw [h'']
      refine hi.symm.trans ?_
      congr 1
      dsimp [δ]
      rw [Fin.succAbove_of_castSucc_lt i.succ]
      exact Fin.castSucc_lt_succ
    · dsimp [δ]
      rw [Fin.succAbove_of_le_castSucc i.succ _]
      simp only [Fin.lt_def, Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc,
        Nat.lt_succ_iff, Fin.ext_iff] at h' h'' ⊢
      lia
/-
**SimplexCategory.eq_** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_σ_comp_of_not_injective {n : ℕ} {Δ' : SimplexCategory} (θ : ⦋n + 1⦌ ⟶ Δ')
    (hθ : ¬Function.Injective θ.toOrderHom) :
    ∃ (i : Fin (n + 1)) (θ' : ⦋n⦌ ⟶ Δ'), θ = σ i ≫ θ' := by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : ∃ x y : Fin (n + 2), (Hom.toOrderHom θ) x = (Hom.toOrderHom θ) y ∧ x < y := by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩
    by_cases h : x < y
    · exact ⟨x, y, ⟨h₁, h⟩⟩
    · refine ⟨y, x, ⟨h₁.symm, ?_⟩⟩
      lia
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩
  use x.castPred ((Fin.le_last _).trans_lt' h₂).ne
  apply eq_σ_comp_of_not_injective'
  apply le_antisymm
  · exact θ.toOrderHom.monotone (le_of_lt Fin.castSucc_lt_succ)
  · rw [Fin.castSucc_castPred, h₁]
    exact θ.toOrderHom.monotone ((Fin.succ_castPred_le_iff _).mpr h₂)
/-
**SimplexCategory.eq_comp_** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_comp_δ_of_not_surjective' {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n + 1⦌)
    (i : Fin (n + 2)) (hi : ∀ x, θ.toOrderHom x ≠ i) : ∃ θ' : Δ ⟶ ⦋n⦌, θ = θ' ≫ δ i := by
  use θ ≫ σ (.predAbove (.last n) i)
  ext x : 3
  suffices ∀ j ≠ i, i.succAbove (((Fin.last n).predAbove i).predAbove j) = j by
    dsimp [δ, σ]
    exact .symm <| this _ (hi _)
  intro j hj
  cases i using Fin.lastCases <;> simp [hj]
/-
**SimplexCategory.eq_comp_** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_comp_δ_of_not_surjective {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n + 1⦌)
    (hθ : ¬Function.Surjective θ.toOrderHom) :
    ∃ (i : Fin (n + 2)) (θ' : Δ ⟶ ⦋n⦌), θ = θ' ≫ δ i := by
  obtain ⟨i, hi⟩ := not_forall.mp hθ
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)
/-
**SimplexCategory.eq_id_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _
参数：i : x ⟶ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimplexCategory.isIso_iff_of_mono`：isIso_iff_of_mono {n m : SimplexCateg
ory} (f : n ⟶ m) [hf : Mono f] : IsIso f ↔ n.len = m.len
· 使用定理 `SimplexCategory.eq_id_of_isIso`：eq_id_of_isIso {x : SimplexCategory} (f 
: x ⟶ x) [IsIso f] : f = 𝟙 _
-/
theorem eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _ :=
  have := (isIso_iff_of_mono i).mpr rfl
  eq_id_of_isIso _
/-
**SimplexCategory.eq_id_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _
参数：i : x ⟶ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimplexCategory.isIso_iff_of_epi`：isIso_iff_of_epi {n m : SimplexCategor
y} (f : n ⟶ m) [hf : Epi f] : IsIso f ↔ n.len = m.len
· 使用定理 `SimplexCategory.eq_id_of_isIso`：eq_id_of_isIso {x : SimplexCategory} (f 
: x ⟶ x) [IsIso f] : f = 𝟙 _
-/
theorem eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _ :=
  have := (isIso_iff_of_epi i).mpr rfl
  eq_id_of_isIso _
/-
**SimplexCategory.eq_** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_σ_of_epi {n : ℕ} (θ : ⦋n + 1⦌ ⟶ ⦋n⦌) [Epi θ] : ∃ i : Fin (n + 1), θ = σ i := by
  obtain ⟨i, θ', h⟩ := eq_σ_comp_of_not_injective θ (by
    rw [← mono_iff_injective]
    grind [→ le_of_mono])
  use i
  have : Epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  have := CategoryTheory.epi_of_epi (σ i) θ'
  rw [h, eq_id_of_epi θ', Category.comp_id]
/-
**SimplexCategory.eq_** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_δ_of_mono {n : ℕ} (θ : ⦋n⦌ ⟶ ⦋n + 1⦌) [Mono θ] : ∃ i : Fin (n + 2), θ = δ i := by
  obtain ⟨i, θ', h⟩ := eq_comp_δ_of_not_surjective θ (by
    rw [← epi_iff_surjective]
    grind [→ le_of_epi])
  use i
  have : Mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  have := CategoryTheory.mono_of_mono θ' (δ i)
  rw [h, eq_id_of_mono θ', Category.id_comp]
/-
**SimplexCategory.len_lt_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：len_lt_of_mono {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] (hi' : Δ != 
Δ') : Δ'.len < Δ.len
参数：i : Δ' ⟶ Δ；hi' : Δ != Δ'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem len_lt_of_mono {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] (hi' : Δ ≠ Δ') :
    Δ'.len < Δ.len := by
  grind [→ len_le_of_mono, SimplexCategory.ext]
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SplitEpiCategory SimplexCategory :=
  skeletalEquivalence.inverse.splitEpiCategoryImpOfIsEquivalence
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasStrongEpiMonoFactorisations SimplexCategory :=
  Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence
    SimplexCategory.skeletalEquivalence.inverse
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasStrongEpiImages SimplexCategory :=
  Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Δ Δ' : SimplexCategory) (θ : Δ ⟶ Δ') : Epi (factorThruImage θ) :=
  StrongEpi.epi
/-
**SimplexCategory.image_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：image_eq {Δ Δ' Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ Δ'} [Epi e] {
i : Δ' ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : image φ = Δ'
参数：fac : e ≫ i = φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.strongEpi_of_epi`：strongEpi_of_epi [StrongEpiCategory C] 
(f : P ⟶ Q) [Epi f] : StrongEpi f
· 使用定理 `CategoryTheory.strongEpiCategory_of_regularEpiCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularEpiCategory
 C],   CategoryTheory.StrongEpiCategory C
· 使用定理 `CategoryTheory.regularEpiCategoryOfSplitEpiCategory`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.SplitEpiCategory C],   
CategoryTheory.IsRegularEpiCategory C
· 使用定理 `SimplexCategory.instSplitEpiCategory`：CategoryTheory.SplitEpiCategory Si
mplexCategory
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `SimplexCategory.instHasStrongEpiMonoFactorisations`：CategoryTheory.Limit
s.HasStrongEpiMonoFactorisations SimplexCategory
· 使用定理 `SimplexCategory.ext`：∀ {x y : SimplexCategory}, x.len = y.len → x = y
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimplexCategory.len_le_of_epi`：len_le_of_epi {x y : SimplexCategory} (f 
: x ⟶ y) [Epi f] : y.len <= x.len
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `SimplexCategory.len_le_of_mono`：len_le_of_mono {x y : SimplexCategory} (
f : x ⟶ y) [Mono f] : x.len <= y.len
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
-/
theorem image_eq {Δ Δ' Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ Δ''}
    [Mono i] (fac : e ≫ i = φ) : image φ = Δ' := by
  have := strongEpi_of_epi e
  let e := image.isoStrongEpiMono e i fac
  ext
  exact le_antisymm (len_le_of_epi e.hom) (len_le_of_mono e.hom)
/-
**SimplexCategory.image_** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_ι_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : image.ι φ = i := by
  have := strongEpi_of_epi e
  rw [← image.isoStrongEpiMono_hom_comp_ι e i fac,
    SimplexCategory.eq_id_of_isIso (image.isoStrongEpiMono e i fac).hom, Category.id_comp]
/-
**SimplexCategory.factorThruImage_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`
。
形式化陈述：factorThruImage_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image 
φ} [Epi e] {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : factorThruImage φ = 
e
参数：fac : e ≫ i = φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `SimplexCategory.instHasStrongEpiMonoFactorisations`：CategoryTheory.Limit
s.HasStrongEpiMonoFactorisations SimplexCategory
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `SimplexCategory.image_ι_eq`：image_ι_eq {Δ Δ'' : SimplexCategory} {φ : Δ 
⟶ Δ''} {e : Δ ⟶ image φ} [Epi e] {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) 
: image.ι φ = i
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
-/
theorem factorThruImage_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : factorThruImage φ = e := by
  rw [← cancel_mono i, fac, ← image_ι_eq fac, image.fac]

end EpiMono

/-- The functor which sends `⦋n⦌ : SimplexCategory` to the partially ordered
type `{0, 1, ..., n}` (ulifted to `Type u`). -/
/-
**SimplexCategory.toPartOrd** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：toPartOrd : SimplexCategory ⥤ PartOrd.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends `⦋n⦌ : SimplexCategory` to the partially ordered
type `{0, 1, ..., n}` (ulifted to `Type u`).
-/
def toPartOrd : SimplexCategory ⥤ PartOrd.{u} :=
  skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ⋙
    forget₂ FinPartOrd PartOrd ⋙ PartOrd.uliftFunctor

@[simp]
/-
**SimplexCategory.toPartOrd_obj** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：toPartOrd_obj (n : SimplexCategory) : toPartOrd.{u}.obj n = .of (ULift.{u}
 (Fin (n.len + 1)))
参数：n : SimplexCategory。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPartOrd_obj (n : SimplexCategory) :
    toPartOrd.{u}.obj n = .of (ULift.{u} (Fin (n.len + 1))) := rfl

@[simp]
/-
**SimplexCategory.toPartOrd_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory
`。
形式化陈述：toPartOrd_map_apply {n m : SimplexCategory} (f : n ⟶ m) (i : (Fin (n.len +
 1))) : dsimp% toPartOrd.{u}.map f (ULift.up i) = ULift.up (f i)
参数：f : n ⟶ m；i : (Fin (n.len + 1))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPartOrd_map_apply {n m : SimplexCategory} (f : n ⟶ m) (i : (Fin (n.len + 1))) :
    dsimp% toPartOrd.{u}.map f (ULift.up i) = ULift.up (f i) := rfl

/-- This functor `SimplexCategory ⥤ Cat` sends `⦋n⦌` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}` -/
@[simps! obj map]
/-
**SimplexCategory.toCat** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：toCat : SimplexCategory ⥤ Cat.{0}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This functor `SimplexCategory ⥤ Cat` sends `⦋n⦌` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}`
-/
def toCat : SimplexCategory ⥤ Cat.{0} :=
  SimplexCategory.skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd LinOrd ⋙
      forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd ⋙
      forget₂ PartOrd Preord ⋙ preordToCat
/-
**SimplexCategory.toCat.obj_eq_Fin** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.to
Cat`。
形式化陈述：∀ (n : ℕ), ↑(SimplexCategory.toCat.obj { len := n }) = Fin (n + 1)
参数：n : ℕ；SimplexCategory.toCat.obj { len := n }；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCat.obj_eq_Fin (n : ℕ) : toCat.obj ⦋n⦌ = Fin (n + 1) := rfl
/-
**SimplexCategory.uniqueHomToZero** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
形式化陈述：uniqueHomToZero {Δ : SimplexCategory} : Unique (Δ ⟶ ⦋0⦌) where default
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.eq_const_to_zero`：eq_const_to_zero {n : SimplexCategory}
 (f : n ⟶ ⦋0⦌) : f = const n _ 0
-/
instance uniqueHomToZero {Δ : SimplexCategory} : Unique (Δ ⟶ ⦋0⦌) where
  default := Δ.const _ 0
  uniq := eq_const_to_zero

/-- The object `⦋0⦌` is terminal in `SimplexCategory`. -/
/-
**SimplexCategory.isTerminalZero** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：isTerminalZero : IsTerminal (⦋0⦌ : SimplexCategory)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object `⦋0⦌` is terminal in `SimplexCategory`.
-/
def isTerminalZero : IsTerminal (⦋0⦌ : SimplexCategory) :=
  IsTerminal.ofUnique ⦋0⦌
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTerminal SimplexCategory :=
  IsTerminal.hasTerminal isTerminalZero

/-- The isomorphism between the terminal object in `SimplexCategory` and `⦋0⦌`. -/
/-
**SimplexCategory.topIsoZero** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：topIsoZero : ⊤_ SimplexCategory ≅ ⦋0⦌
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.instHasTerminal`：CategoryTheory.Limits.HasTerminal Simpl
exCategory

--- 原说明 ---
The isomorphism between the terminal object in `SimplexCategory` and `⦋0⦌`.
-/
noncomputable def topIsoZero : ⊤_ SimplexCategory ≅ ⦋0⦌ :=
  terminalIsoIsTerminal isTerminalZero
/-
**SimplexCategory.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_injective {n : ℕ} : Function.Injective (δ (n := n)) := by
  intro i j hij
  rw [← Fin.succAbove_left_inj]
  ext k : 1
  exact congr($hij k)
/-
**SimplexCategory.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_injective {n : ℕ} : Function.Injective (σ (n := n)) := by
  intro i j hij
  rw [← Fin.predAbove_left_inj]
  ext k : 1
  exact congr($hij k)

end SimplexCategory

