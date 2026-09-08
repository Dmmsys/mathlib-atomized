/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Hom.Basic

/-!

# Tropical algebraic structures

This file defines algebraic structures of the (min-)tropical numbers, up to the tropical semiring.
Some basic lemmas about conversion from the base type `R` to `Tropical R` are provided, as
well as the expected implementations of tropical addition and tropical multiplication.

## Main declarations

* `Tropical R`: The type synonym of the tropical interpretation of `R`.
    If `[LinearOrder R]`, then addition on `R` is via `min`.
* `Semiring (Tropical R)`: A `LinearOrderedAddCommMonoidWithTop R`
    induces a `Semiring (Tropical R)`. If one solely has `[LinearOrderedAddCommMonoid R]`,
    then the "tropicalization of `R`" would be `Tropical (WithTop R)`.

## Implementation notes

The tropical structure relies on `Top` and `min`. For the max-tropical numbers, use
`OrderDual R`.

Inspiration was drawn from the implementation of `Additive`/`Multiplicative`/`Opposite`,
where a type synonym is created with some barebones API, and quickly made irreducible.

Algebraic structures are provided with as few typeclass assumptions as possible, even though
most references rely on `Semiring (Tropical R)` for building up the whole theory.

## References followed

* https://arxiv.org/pdf/math/0408099.pdf
* https://www.mathenjeans.fr/sites/default/files/sujets/tropical_geometry_-_casagrande.pdf

-/

@[expose] public section

assert_not_exists Nat.instMulOneClass

universe u v

variable (R : Type u)

/-- The tropicalization of a type `R`. -/
/-
**Tropical** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Tropical : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tropicalization of a type `R`.
-/
def Tropical : Type u :=
  R

variable {R}

namespace Tropical

/-- Reinterpret `x : R` as an element of `Tropical R`.
See `Tropical.tropEquiv` for the equivalence.
-/
/-
**Tropical.trop** 是 Mathlib 中的一个定义，位于命名空间 `Tropical`。
形式化陈述：trop : R -> Tropical R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `x : R` as an element of `Tropical R`.
See `Tropical.tropEquiv` for the equivalence.
-/
def trop : R → Tropical R :=
  id

/-- Reinterpret `x : Tropical R` as an element of `R`.
See `Tropical.tropEquiv` for the equivalence. -/
@[pp_nodot]
/-
**Tropical.untrop** 是 Mathlib 中的一个定义，位于命名空间 `Tropical`。
形式化陈述：untrop : Tropical R -> R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `x : Tropical R` as an element of `R`.
See `Tropical.tropEquiv` for the equivalence.
-/
def untrop : Tropical R → R :=
  id
/-
**Tropical.trop_injective** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_injective : Function.Injective (trop : R -> Tropical R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_injective : Function.Injective (trop : R → Tropical R) := fun _ _ => id
/-
**Tropical.untrop_injective** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_injective : Function.Injective (untrop : Tropical R -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_injective : Function.Injective (untrop : Tropical R → R) := fun _ _ => id

@[simp]
/-
**Tropical.trop_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_inj_iff (x y : R) : trop x = trop y ↔ x = y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem trop_inj_iff (x y : R) : trop x = trop y ↔ x = y :=
  Iff.rfl

@[simp]
/-
**Tropical.untrop_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_inj_iff (x y : Tropical R) : untrop x = untrop y ↔ x = y
参数：x y : Tropical R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem untrop_inj_iff (x y : Tropical R) : untrop x = untrop y ↔ x = y :=
  Iff.rfl

@[simp]
/-
**Tropical.trop_untrop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_untrop (x : Tropical R) : trop (untrop x) = x
参数：x : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_untrop (x : Tropical R) : trop (untrop x) = x :=
  rfl

@[simp]
/-
**Tropical.untrop_trop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_trop (x : R) : untrop (trop x) = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_trop (x : R) : untrop (trop x) = x :=
  rfl

attribute [irreducible] Tropical
/-
**Tropical.leftInverse_trop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：leftInverse_trop : Function.LeftInverse (trop : R -> Tropical R) untrop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tropical.trop_untrop`：trop_untrop (x : Tropical R) : trop (untrop x) = x
-/
theorem leftInverse_trop : Function.LeftInverse (trop : R → Tropical R) untrop :=
  trop_untrop
/-
**Tropical.rightInverse_trop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：rightInverse_trop : Function.RightInverse (trop : R -> Tropical R) untrop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tropical.untrop_trop`：untrop_trop (x : R) : untrop (trop x) = x
-/
theorem rightInverse_trop : Function.RightInverse (trop : R → Tropical R) untrop :=
  untrop_trop

/-- Reinterpret `x : R` as an element of `Tropical R`.
See `Tropical.tropOrderIso` for the order-preserving equivalence. -/
/-
**Tropical.tropEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Tropical`。
形式化陈述：tropEquiv : R ≃ Tropical R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Tropical.untrop_trop`：untrop_trop (x : R) : untrop (trop x) = x
· 使用定理 `Tropical.trop_untrop`：trop_untrop (x : Tropical R) : trop (untrop x) = x

--- 原说明 ---
Reinterpret `x : R` as an element of `Tropical R`.
See `Tropical.tropOrderIso` for the order-preserving equivalence.
-/
def tropEquiv : R ≃ Tropical R where
  toFun := trop
  invFun := untrop
  left_inv := untrop_trop
  right_inv := trop_untrop

@[simp]
/-
**Tropical.tropEquiv_coe_fn** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：tropEquiv_coe_fn : (tropEquiv : R -> Tropical R) = trop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tropEquiv_coe_fn : (tropEquiv : R → Tropical R) = trop :=
  rfl

@[simp]
/-
**Tropical.tropEquiv_symm_coe_fn** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：tropEquiv_symm_coe_fn : (tropEquiv.symm : Tropical R -> R) = untrop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem tropEquiv_symm_coe_fn : (tropEquiv.symm : Tropical R → R) = untrop :=
  rfl
/-
**Tropical.trop_eq_iff_eq_untrop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_eq_iff_eq_untrop {x : R} {y} : trop x = y ↔ x = untrop y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem trop_eq_iff_eq_untrop {x : R} {y} : trop x = y ↔ x = untrop y :=
  tropEquiv.eq_symm_apply.symm
/-
**Tropical.untrop_eq_iff_eq_trop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_eq_iff_eq_trop {x} {y : R} : untrop x = y ↔ x = trop y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem untrop_eq_iff_eq_trop {x} {y : R} : untrop x = y ↔ x = trop y :=
  tropEquiv.symm.eq_symm_apply.symm
/-
**Tropical.injective_trop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：injective_trop : Function.Injective (trop : R -> Tropical R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem injective_trop : Function.Injective (trop : R → Tropical R) :=
  tropEquiv.injective
/-
**Tropical.injective_untrop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：injective_untrop : Function.Injective (untrop : Tropical R -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem injective_untrop : Function.Injective (untrop : Tropical R → R) :=
  tropEquiv.symm.injective
/-
**Tropical.surjective_trop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：surjective_trop : Function.Surjective (trop : R -> Tropical R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem surjective_trop : Function.Surjective (trop : R → Tropical R) :=
  tropEquiv.surjective
/-
**Tropical.surjective_untrop** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：surjective_untrop : Function.Surjective (untrop : Tropical R -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem surjective_untrop : Function.Surjective (untrop : Tropical R → R) :=
  tropEquiv.symm.surjective
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited R] : Inhabited (Tropical R) :=
  ⟨trop default⟩

/-- Recursing on an `x' : Tropical R` is the same as recursing on an `x : R` reinterpreted
as a term of `Tropical R` via `trop x`. -/
@[simp]
/-
**Tropical.tropRec** 是 Mathlib 中的一个定义，位于命名空间 `Tropical`。
形式化陈述：tropRec {F : Tropical R -> Sort v} (h : forall X, F (trop X)) : forall X, 
F X
参数：h : forall X, F (trop X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursing on an `x' : Tropical R` is the same as recursing on an `x : R` reinter
preted
as a term of `Tropical R` via `trop x`.
-/
def tropRec {F : Tropical R → Sort v} (h : ∀ X, F (trop X)) : ∀ X, F X := fun X => h (untrop X)
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq R] : DecidableEq (Tropical R) := fun _ _ =>
  decidable_of_iff _ injective_untrop.eq_iff

section Order

/-
**Tropical.instLETropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instLETropical [LE R] : LE (Tropical R) where le x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLETropical [LE R] : LE (Tropical R) where le x y := untrop x ≤ untrop y

@[simp]
/-
**Tropical.untrop_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_le_iff [LE R] {x y : Tropical R} : untrop x <= untrop y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem untrop_le_iff [LE R] {x y : Tropical R} : untrop x ≤ untrop y ↔ x ≤ y :=
  Iff.rfl
/-
**Tropical.decidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：decidableLE [LE R] [DecidableLE R] : DecidableLE (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLE [LE R] [DecidableLE R] : DecidableLE (Tropical R) := fun x y =>
  ‹DecidableLE R› (untrop x) (untrop y)
/-
**Tropical.instLTTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instLTTropical [LT R] : LT (Tropical R) where lt x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLTTropical [LT R] : LT (Tropical R) where lt x y := untrop x < untrop y

@[simp]
/-
**Tropical.untrop_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_lt_iff [LT R] {x y : Tropical R} : untrop x < untrop y ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem untrop_lt_iff [LT R] {x y : Tropical R} : untrop x < untrop y ↔ x < y :=
  Iff.rfl
/-
**Tropical.decidableLT** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：decidableLT [LT R] [DecidableLT R] : DecidableLT (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLT [LT R] [DecidableLT R] : DecidableLT (Tropical R) := fun x y =>
  ‹DecidableLT R› (untrop x) (untrop y)
/-
**Tropical.instPreorderTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instPreorderTropical [Preorder R] : Preorder (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPreorderTropical [Preorder R] : Preorder (Tropical R) :=
  { instLETropical, instLTTropical with
    le_refl := fun x => le_refl (untrop x)
    le_trans := fun _ _ _ h h' => le_trans (α := R) h h'
    lt_iff_le_not_ge := fun _ _ => lt_iff_le_not_ge (α := R) }

/-- Reinterpret `x : R` as an element of `Tropical R`, preserving the order. -/
/-
**Tropical.tropOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Tropical`。
形式化陈述：tropOrderIso [Preorder R] : R ≃o Tropical R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `x : R` as an element of `Tropical R`, preserving the order.
-/
def tropOrderIso [Preorder R] : R ≃o Tropical R :=
  { tropEquiv with map_rel_iff' := untrop_le_iff }

@[simp]
/-
**Tropical.tropOrderIso_coe_fn** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：tropOrderIso_coe_fn [Preorder R] : (tropOrderIso : R -> Tropical R) = trop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tropOrderIso_coe_fn [Preorder R] : (tropOrderIso : R → Tropical R) = trop :=
  rfl

@[simp]
/-
**Tropical.tropOrderIso_symm_coe_fn** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：tropOrderIso_symm_coe_fn [Preorder R] : (tropOrderIso.symm : Tropical R ->
 R) = untrop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tropOrderIso_symm_coe_fn [Preorder R] : (tropOrderIso.symm : Tropical R → R) = untrop :=
  rfl
/-
**Tropical.trop_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_monotone [Preorder R] : Monotone (trop : R -> Tropical R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_monotone [Preorder R] : Monotone (trop : R → Tropical R) := fun _ _ => id
/-
**Tropical.untrop_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_monotone [Preorder R] : Monotone (untrop : Tropical R -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_monotone [Preorder R] : Monotone (untrop : Tropical R → R) := fun _ _ => id
/-
**Tropical.instPartialOrderTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instPartialOrderTropical [PartialOrder R] : PartialOrder (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrderTropical [PartialOrder R] : PartialOrder (Tropical R) :=
  { instPreorderTropical with le_antisymm := fun _ _ h h' => untrop_injective (le_antisymm h h') }
/-
**Tropical.instZeroTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instZeroTropical [Top R] : Zero (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZeroTropical [Top R] : Zero (Tropical R) :=
  ⟨trop ⊤⟩
/-
**Tropical.instTopTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instTopTropical [Top R] : Top (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopTropical [Top R] : Top (Tropical R) :=
  ⟨0⟩

@[simp]
/-
**Tropical.untrop_zero** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_zero [Top R] : untrop (0 : Tropical R) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_zero [Top R] : untrop (0 : Tropical R) = ⊤ :=
  rfl

@[simp]
/-
**Tropical.trop_top** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_top [Top R] : trop (⊤ : R) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_top [Top R] : trop (⊤ : R) = 0 :=
  rfl

@[simp]
/-
**Tropical.trop_coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_coe_ne_zero (x : R) : trop (x : WithTop R) != 0
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_coe_ne_zero (x : R) : trop (x : WithTop R) ≠ 0 :=
  nofun

@[simp]
/-
**Tropical.zero_ne_trop_coe** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：zero_ne_trop_coe (x : R) : 0 != (trop x : Tropical (WithTop R))
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_ne_trop_coe (x : R) : 0 ≠ (trop x : Tropical (WithTop R)) :=
  nofun

@[simp]
/-
**Tropical.le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：le_zero [LE R] [OrderTop R] (x : Tropical R) : x <= 0
参数：x : Tropical R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem le_zero [LE R] [OrderTop R] (x : Tropical R) : x ≤ 0 :=
  le_top (α := R)
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE R] [OrderTop R] : OrderTop (Tropical R) :=
  { instTopTropical with le_top := fun _ => le_top (α := R) }

variable [LinearOrder R]

/-- Tropical addition is the minimum of two underlying elements of `R`. -/
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tropical addition is the minimum of two underlying elements of `R`.
-/
instance : Add (Tropical R) :=
  ⟨fun x y => trop (min (untrop x) (untrop y))⟩
/-
**Tropical.instAddCommSemigroupTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instAddCommSemigroupTropical : AddCommSemigroup (Tropical R) where add_ass
oc _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommSemigroupTropical : AddCommSemigroup (Tropical R) where
  add_assoc _ _ _ := untrop_injective (min_assoc _ _ _)
  add_comm _ _ := untrop_injective (min_comm _ _)

@[simp]
/-
**Tropical.untrop_add** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_add (x y : Tropical R) : untrop (x + y) = min (untrop x) (untrop y)
参数：x y : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_add (x y : Tropical R) : untrop (x + y) = min (untrop x) (untrop y) :=
  rfl

@[simp]
/-
**Tropical.trop_min** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_min (x y : R) : trop (min x y) = trop x + trop y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_min (x y : R) : trop (min x y) = trop x + trop y :=
  rfl

@[simp]
/-
**Tropical.trop_inf** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_inf (x y : R) : trop (x ⊓ y) = trop x + trop y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_inf (x y : R) : trop (x ⊓ y) = trop x + trop y :=
  rfl
/-
**Tropical.trop_add_def** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_add_def (x y : Tropical R) : x + y = trop (min (untrop x) (untrop y))
参数：x y : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_add_def (x y : Tropical R) : x + y = trop (min (untrop x) (untrop y)) :=
  rfl
/-
**Tropical.instLinearOrderTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instLinearOrderTropical : LinearOrder (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLinearOrderTropical : LinearOrder (Tropical R) :=
  { instPartialOrderTropical with
    le_total := fun a b => le_total (untrop a) (untrop b)
    toDecidableLE := Tropical.decidableLE
    toDecidableEq := Tropical.instDecidableEq
    toDecidableLT := Tropical.decidableLT
    max := fun a b => trop (max (untrop a) (untrop b))
    max_def := fun a b => untrop_injective (by
      simp only [max_def, untrop_le_iff, untrop_trop]; split_ifs <;> simp)
    min := (· + ·)
    min_def := fun a b => untrop_injective (by
      simp only [untrop_add, min_def, untrop_le_iff]; split_ifs <;> simp) }

@[simp]
/-
**Tropical.untrop_sup** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_sup (x y : Tropical R) : untrop (x ⊔ y) = untrop x ⊔ untrop y
参数：x y : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_sup (x y : Tropical R) : untrop (x ⊔ y) = untrop x ⊔ untrop y :=
  rfl

@[simp]
/-
**Tropical.untrop_max** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_max (x y : Tropical R) : untrop (max x y) = max (untrop x) (untrop 
y)
参数：x y : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_max (x y : Tropical R) : untrop (max x y) = max (untrop x) (untrop y) :=
  rfl

@[simp]
/-
**Tropical.min_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：min_eq_add : (min : Tropical R -> Tropical R -> Tropical R) = (· + ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem min_eq_add : (min : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl

@[simp]
/-
**Tropical.inf_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：inf_eq_add : ((· ⊓ ·) : Tropical R -> Tropical R -> Tropical R) = (· + ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_eq_add : ((· ⊓ ·) : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl
/-
**Tropical.trop_max_def** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_max_def (x y : Tropical R) : max x y = trop (max (untrop x) (untrop y
))
参数：x y : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_max_def (x y : Tropical R) : max x y = trop (max (untrop x) (untrop y)) :=
  rfl
/-
**Tropical.trop_sup_def** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_sup_def (x y : Tropical R) : x ⊔ y = trop (untrop x ⊔ untrop y)
参数：x y : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_sup_def (x y : Tropical R) : x ⊔ y = trop (untrop x ⊔ untrop y) :=
  rfl

@[simp]
/-
**Tropical.add_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：add_eq_left ⦃x y : Tropical R⦄ (h : x <= y) : x + y = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tropical.untrop_injective`：untrop_injective : Function.Injective (untrop
 : Tropical R -> R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem add_eq_left ⦃x y : Tropical R⦄ (h : x ≤ y) : x + y = x :=
  untrop_injective (by simpa using h)

@[simp]
/-
**Tropical.add_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：add_eq_right ⦃x y : Tropical R⦄ (h : y <= x) : x + y = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tropical.untrop_injective`：untrop_injective : Function.Injective (untrop
 : Tropical R -> R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem add_eq_right ⦃x y : Tropical R⦄ (h : y ≤ x) : x + y = y :=
  untrop_injective (by simpa using h)
/-
**Tropical.add_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：add_eq_left_iff {x y : Tropical R} : x + y = x ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tropical.trop_add_def`：trop_add_def (x y : Tropical R) : x + y = trop (m
in (untrop x) (untrop y))
· 使用定理 `Tropical.trop_eq_iff_eq_untrop`：trop_eq_iff_eq_untrop {x : R} {y} : trop
 x = y ↔ x = untrop y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tropical.untrop_le_iff`：untrop_le_iff [LE R] {x y : Tropical R} : untrop
 x <= untrop y ↔ x <= y
· 使用定理 `min_eq_left_iff`：min_eq_left_iff : min a b = a ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_eq_left_iff {x y : Tropical R} : x + y = x ↔ x ≤ y := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_left_iff]
/-
**Tropical.add_eq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：add_eq_right_iff {x y : Tropical R} : x + y = y ↔ y <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tropical.trop_add_def`：trop_add_def (x y : Tropical R) : x + y = trop (m
in (untrop x) (untrop y))
· 使用定理 `Tropical.trop_eq_iff_eq_untrop`：trop_eq_iff_eq_untrop {x : R} {y} : trop
 x = y ↔ x = untrop y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tropical.untrop_le_iff`：untrop_le_iff [LE R] {x y : Tropical R} : untrop
 x <= untrop y ↔ x <= y
· 使用定理 `min_eq_right_iff`：min_eq_right_iff : min a b = b ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_eq_right_iff {x y : Tropical R} : x + y = y ↔ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_right_iff]
/-
**Tropical.add_self** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：add_self (x : Tropical R) : x + x = x
参数：x : Tropical R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tropical.untrop_injective`：untrop_injective : Function.Injective (untrop
 : Tropical R -> R)
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem add_self (x : Tropical R) : x + x = x :=
  untrop_injective (min_eq_right le_rfl)
/-
**Tropical.add_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：add_eq_iff {x y z : Tropical R} : x + y = z ↔ x = z ∧ x <= y ∨ y = z ∧ y <
= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tropical.trop_add_def`：trop_add_def (x y : Tropical R) : x + y = trop (m
in (untrop x) (untrop y))
· 使用定理 `Tropical.trop_eq_iff_eq_untrop`：trop_eq_iff_eq_untrop {x : R} {y} : trop
 x = y ↔ x = untrop y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_eq_iff {x y z : Tropical R} : x + y = z ↔ x = z ∧ x ≤ y ∨ y = z ∧ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop]
  simp [min_eq_iff]

@[simp]
/-
**Tropical.add_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：add_eq_zero_iff {a b : Tropical (WithTop R)} : a + b = 0 ↔ a = 0 ∧ b = 0
参数：WithTop R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tropical.add_eq_iff`：add_eq_iff {x y z : Tropical R} : x + y = z ↔ x = z
 ∧ x <= y ∨ y = z ∧ y <= x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Tropical.le_zero`：le_zero [LE R] [OrderTop R] (x : Tropical R) : x <= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem add_eq_zero_iff {a b : Tropical (WithTop R)} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymm (le_zero _) h⟩
    · exact ⟨le_antisymm (le_zero _) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp
/-
**Tropical.instAddCommMonoidTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instAddCommMonoidTropical [OrderTop R] : AddCommMonoid (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoidTropical [OrderTop R] : AddCommMonoid (Tropical R) :=
  { instZeroTropical, instAddCommSemigroupTropical with
    zero_add := fun _ => untrop_injective (min_top_left _)
    add_zero := fun _ => untrop_injective (min_top_right _)
    nsmul := nsmulRec }

end Order

section Monoid

/-- Tropical multiplication is the addition in the underlying `R`. -/
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tropical multiplication is the addition in the underlying `R`.
-/
instance [Add R] : Mul (Tropical R) :=
  ⟨fun x y => trop (untrop x + untrop y)⟩

@[simp]
/-
**Tropical.trop_add** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_add [Add R] (x y : R) : trop (x + y) = trop x * trop y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_add [Add R] (x y : R) : trop (x + y) = trop x * trop y :=
  rfl

@[simp]
/-
**Tropical.untrop_mul** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_mul [Add R] (x y : Tropical R) : untrop (x * y) = untrop x + untrop
 y
参数：x y : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_mul [Add R] (x y : Tropical R) : untrop (x * y) = untrop x + untrop y :=
  rfl
/-
**Tropical.trop_mul_def** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_mul_def [Add R] (x y : Tropical R) : x * y = trop (untrop x + untrop 
y)
参数：x y : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_mul_def [Add R] (x y : Tropical R) : x * y = trop (untrop x + untrop y) :=
  rfl
/-
**Tropical.instOneTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instOneTropical [Zero R] : One (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOneTropical [Zero R] : One (Tropical R) :=
  ⟨trop 0⟩

@[simp]
/-
**Tropical.trop_zero** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_zero [Zero R] : trop (0 : R) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_zero [Zero R] : trop (0 : R) = 1 :=
  rfl

@[simp]
/-
**Tropical.untrop_one** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_one [Zero R] : untrop (1 : Tropical R) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_one [Zero R] : untrop (1 : Tropical R) = 0 :=
  rfl
/-
**Tropical.instAddMonoidWithOneTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instAddMonoidWithOneTropical [LinearOrder R] [OrderTop R] [Zero R] : AddMo
noidWithOne (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOneTropical [LinearOrder R] [OrderTop R] [Zero R] :
    AddMonoidWithOne (Tropical R) :=
  { instOneTropical, instAddCommMonoidTropical with
    natCast := fun n => if n = 0 then 0 else 1
    natCast_zero := rfl
    natCast_succ := fun n => (untrop_inj_iff _ _).1 (by cases n <;> simp) }
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] : Nontrivial (Tropical (WithTop R)) :=
  ⟨⟨0, 1, trop_injective.ne WithTop.top_ne_coe⟩⟩
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Neg R] : Inv (Tropical R) :=
  ⟨fun x => trop (-untrop x)⟩

@[simp]
/-
**Tropical.untrop_inv** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_inv [Neg R] (x : Tropical R) : untrop x⁻¹ = -untrop x
参数：x : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_inv [Neg R] (x : Tropical R) : untrop x⁻¹ = -untrop x :=
  rfl
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Sub R] : Div (Tropical R) :=
  ⟨fun x y => trop (untrop x - untrop y)⟩

@[simp]
/-
**Tropical.untrop_div** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_div [Sub R] (x y : Tropical R) : untrop (x / y) = untrop x - untrop
 y
参数：x y : Tropical R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_div [Sub R] (x y : Tropical R) : untrop (x / y) = untrop x - untrop y :=
  rfl
/-
**Tropical.instSemigroupTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instSemigroupTropical [AddSemigroup R] : Semigroup (Tropical R) where mul_
assoc _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupTropical [AddSemigroup R] : Semigroup (Tropical R) where
  mul_assoc _ _ _ := untrop_injective (add_assoc _ _ _)
/-
**Tropical.instCommSemigroupTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instCommSemigroupTropical [AddCommSemigroup R] : CommSemigroup (Tropical R
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroupTropical [AddCommSemigroup R] : CommSemigroup (Tropical R) :=
  { instSemigroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [SMul α R] : Pow (Tropical R) α where pow x n := trop <| n • untrop x

@[simp]
/-
**Tropical.untrop_pow** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_pow {α : Type*} [SMul α R] (x : Tropical R) (n : α) : untrop (x ^ n
) = n • untrop x
参数：x : Tropical R；n : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_pow {α : Type*} [SMul α R] (x : Tropical R) (n : α) :
    untrop (x ^ n) = n • untrop x :=
  rfl

@[simp]
/-
**Tropical.trop_smul** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_smul {α : Type*} [SMul α R] (x : R) (n : α) : trop (n • x) = trop x ^
 n
参数：x : R；n : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_smul {α : Type*} [SMul α R] (x : R) (n : α) : trop (n • x) = trop x ^ n :=
  rfl
/-
**Tropical.instMulOneClassTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instMulOneClassTropical [AddZeroClass R] : MulOneClass (Tropical R) where 
one_mul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulOneClassTropical [AddZeroClass R] : MulOneClass (Tropical R) where
  one_mul _ := untrop_injective <| zero_add _
  mul_one _ := untrop_injective <| add_zero _
/-
**Tropical.instMonoidTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instMonoidTropical [AddMonoid R] : Monoid (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidTropical [AddMonoid R] : Monoid (Tropical R) :=
  { instMulOneClassTropical, instSemigroupTropical with
    npow := fun n x => x ^ n
    npow_zero := fun _ => untrop_injective <| by simp
    npow_succ := fun _ _ => untrop_injective <| succ_nsmul _ _ }

@[simp]
/-
**Tropical.trop_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_nsmul [AddMonoid R] (x : R) (n : Nat) : trop (n • x) = trop x ^ n
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_nsmul [AddMonoid R] (x : R) (n : ℕ) : trop (n • x) = trop x ^ n :=
  rfl
/-
**Tropical.instCommMonoidTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instCommMonoidTropical [AddCommMonoid R] : CommMonoid (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoidTropical [AddCommMonoid R] : CommMonoid (Tropical R) :=
  { instMonoidTropical, instCommSemigroupTropical with }
/-
**Tropical.instGroupTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instGroupTropical [AddGroup R] : Group (Tropical R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroupTropical [AddGroup R] : Group (Tropical R) :=
  { instMonoidTropical with
    div_eq_mul_inv := fun _ _ => untrop_injective <| by simp [sub_eq_add_neg]
    inv_mul_cancel := fun _ => untrop_injective <| neg_add_cancel _
    zpow := fun n x => trop <| n • untrop x
    zpow_zero' := fun _ => untrop_injective <| zero_zsmul _
    zpow_succ' := fun _ _ => untrop_injective <| SubNegMonoid.zsmul_succ' _ _
    zpow_neg' := fun _ _ => untrop_injective <| SubNegMonoid.zsmul_neg' _ _ }
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup R] : CommGroup (Tropical R) :=
  { instGroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

@[simp]
/-
**Tropical.untrop_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：untrop_zpow [AddGroup R] (x : Tropical R) (n : Int) : untrop (x ^ n) = n •
 untrop x
参数：x : Tropical R；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untrop_zpow [AddGroup R] (x : Tropical R) (n : ℤ) : untrop (x ^ n) = n • untrop x :=
  rfl

@[simp]
/-
**Tropical.trop_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：trop_zsmul [AddGroup R] (x : R) (n : Int) : trop (n • x) = trop x ^ n
参数：x : R；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trop_zsmul [AddGroup R] (x : R) (n : ℤ) : trop (n • x) = trop x ^ n :=
  rfl

end Monoid

section Distrib

/-
**Tropical.mulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：mulLeftMono [LE R] [Add R] [AddLeftMono R] : MulLeftMono (Tropical R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
instance mulLeftMono [LE R] [Add R] [AddLeftMono R] :
    MulLeftMono (Tropical R) :=
  ⟨fun _ y z h => add_le_add_right (show untrop y ≤ untrop z from h) _⟩
/-
**Tropical.mulRightMono** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：mulRightMono [LE R] [Add R] [AddRightMono R] : MulRightMono (Tropical R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
-/
instance mulRightMono [LE R] [Add R] [AddRightMono R] :
    MulRightMono (Tropical R) :=
  ⟨fun _ y z h => add_le_add_left (show untrop y ≤ untrop z from h) _⟩
/-
**Tropical.addLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：addLeftMono [LinearOrder R] : AddLeftMono (Tropical R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tropical.add_eq_left`：add_eq_left ⦃x y : Tropical R⦄ (h : x <= y) : x + 
y = x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Tropical.add_eq_right`：add_eq_right ⦃x y : Tropical R⦄ (h : y <= x) : x 
+ y = y
-/
instance addLeftMono [LinearOrder R] : AddLeftMono (Tropical R) :=
  ⟨fun x y z h => by
    rcases le_total x y with hx | hy
    · rw [add_eq_left hx, add_eq_left (hx.trans h)]
    · rw [add_eq_right hy]
      rcases le_total x z with hx | hx
      · rwa [add_eq_left hx]
      · rwa [add_eq_right hx]⟩
/-
**Tropical.mulLeftStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：mulLeftStrictMono [LT R] [Add R] [AddLeftStrictMono R] : MulLeftStrictMono
 (Tropical R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Tropical.untrop_lt_iff`：untrop_lt_iff [LT R] {x y : Tropical R} : untrop
 x < untrop y ↔ x < y
-/
instance mulLeftStrictMono [LT R] [Add R] [AddLeftStrictMono R] :
    MulLeftStrictMono (Tropical R) :=
  ⟨fun _ _ _ h => add_lt_add_right (untrop_lt_iff.2 h) _⟩
/-
**Tropical.mulRightStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：mulRightStrictMono [Preorder R] [Add R] [AddRightStrictMono R] : MulRightS
trictMono (Tropical R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
-/
instance mulRightStrictMono [Preorder R] [Add R] [AddRightStrictMono R] :
    MulRightStrictMono (Tropical R) :=
  ⟨fun _ y z h => add_lt_add_left (show untrop y < untrop z from h) _⟩
/-
**Tropical.instDistribTropical** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
形式化陈述：instDistribTropical [LinearOrder R] [Add R] [AddLeftMono R] [AddRightMono 
R] : Distrib (Tropical R) where left_distrib _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribTropical [LinearOrder R] [Add R] [AddLeftMono R] [AddRightMono R] :
    Distrib (Tropical R) where
  left_distrib _ _ _ := untrop_injective (min_add_add_left _ _ _).symm
  right_distrib _ _ _ := untrop_injective (min_add_add_right _ _ _).symm

@[simp]
/-
**Tropical.add_pow** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：add_pow [LinearOrder R] [AddMonoid R] [AddLeftMono R] [AddRightMono R] (x 
y : Tropical R) (n : Nat) : (x + y) ^ n = x ^ n + y ^ n
参数：x y : Tropical R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tropical.add_eq_left`：add_eq_left ⦃x y : Tropical R⦄ (h : x <= y) : x + 
y = x
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `Tropical.add_eq_right`：add_eq_right ⦃x y : Tropical R⦄ (h : y <= x) : x 
+ y = y
-/
theorem add_pow [LinearOrder R] [AddMonoid R] [AddLeftMono R] [AddRightMono R]
    (x y : Tropical R) (n : ℕ) :
    (x + y) ^ n = x ^ n + y ^ n := by
  rcases le_total x y with h | h
  · rw [add_eq_left h, add_eq_left (pow_le_pow_left' h _)]
  · rw [add_eq_right h, add_eq_right (pow_le_pow_left' h _)]

end Distrib

section Semiring

variable [LinearOrderedAddCommMonoidWithTop R]

/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring (Tropical R) :=
  { instAddMonoidWithOneTropical,
    instDistribTropical,
    instAddCommMonoidTropical,
    instCommMonoidTropical with
    zero_mul := fun _ => untrop_injective (by simp [top_add])
    mul_zero := fun _ => untrop_injective (by simp [add_top]) }

@[simp]
/-
**Tropical.succ_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：succ_nsmul {R} [LinearOrder R] [OrderTop R] (x : Tropical R) (n : Nat) : (
n + 1) • x = x
参数：x : Tropical R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用定理 `Tropical.add_self`：add_self (x : Tropical R) : x + x = x
-/
theorem succ_nsmul {R} [LinearOrder R] [OrderTop R] (x : Tropical R) (n : ℕ) : (n + 1) • x = x := by
  induction n with
  | zero => simp [one_nsmul]
  | succ n IH => rw [add_nsmul, IH, one_nsmul, add_self]

-- TODO: find/create the right classes to make this hold (for enat, ennreal, etc)
-- Requires `zero_eq_bot` to be true
-- lemma add_eq_zero_iff {a b : tropical R} :
--   a + b = 1 ↔ a = 1 ∨ b = 1 := sorry
/-
**Tropical.mul_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tropical`。
形式化陈述：mul_eq_zero_iff {R : Type*} [AddCommMonoid R] {a b : Tropical (WithTop R)}
 : a * b = 0 ↔ a = 0 ∨ b = 0
参数：WithTop R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_eq_zero_iff {R : Type*} [AddCommMonoid R]
    {a b : Tropical (WithTop R)} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  simp [← untrop_inj_iff, WithTop.add_eq_top]
/-
**Tropical.** 是 Mathlib 中的一个实例，位于命名空间 `Tropical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [AddCommMonoid R] :
    NoZeroDivisors (Tropical (WithTop R)) :=
  ⟨mul_eq_zero_iff.mp⟩

end Semiring

end Tropical

