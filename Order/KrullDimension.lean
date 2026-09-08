/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Joachim Breitner
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.SuccPred.WithBot
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.Atoms
public import Mathlib.Order.RelSeries
public import Mathlib.Tactic.FinCases

/-!
# Krull dimension of a preordered set and height of an element

If `α` is a preordered set, then `krullDim α : WithBot ℕ∞` is defined to be
`sup {n | a₀ < a₁ < ... < aₙ}`.

In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to be
positive infinity.

For `a : α`, its height (in `ℕ∞`) is defined to be `sup {n | a₀ < a₁ < ... < aₙ ≤ a}`, while its
coheight is defined to be `sup {n | a ≤ a₀ < a₁ < ... < aₙ}` .

## Main results

* The Krull dimension is the same as that of the dual order (`krullDim_orderDual`).

* The Krull dimension is the supremum of the heights of the elements (`krullDim_eq_iSup_height`),
  or their coheights (`krullDim_eq_iSup_coheight`), or their sums of height and coheight
  (`krullDim_eq_iSup_height_add_coheight_of_nonempty`)

* The height in the dual order equals the coheight, and vice versa.

* The height is monotone (`height_mono`), and strictly monotone if finite (`height_strictMono`).

* The coheight is antitone (`coheight_anti`), and strictly antitone if finite
  (`coheight_strictAnti`).

* The height is the supremum of the successor of the height of all smaller elements
  (`height_eq_iSup_lt_height`).

* The elements of height zero are the minimal elements (`height_eq_zero`), and the elements of
  height `n` are minimal among those of height `≥ n` (`height_eq_coe_iff_minimal_le_height`).

* Concrete calculations for the height, coheight and Krull dimension in `ℕ`, `ℤ`, `WithTop`,
  `WithBot` and `ℕ∞`.

## Design notes

Krull dimensions are defined to take value in `WithBot ℕ∞` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.

We could generalize the notion of Krull dimension to an arbitrary binary relation; many results
in this file would generalize as well. But we don't think it would be useful, so we only define
Krull dimension of a preorder.
-/

@[expose] public section

assert_not_exists Field

namespace Order

section definitions

/--
The **Krull dimension** of a preorder `α` is the supremum of the rightmost index of all relation
series of `α` ordered by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull
dimension is defined to be negative infinity; if the length of all series `a₀ < a₁ < ... < aₙ` is
unbounded, its Krull dimension is defined to be positive infinity.
-/
/-
**Order.krullDim** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：krullDim (α : Type*) [Preorder α] : WithBot Nat∞
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Krull dimension** of a preorder `α` is the supremum of the rightmost index
 of all relation
series of `α` ordered by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`,
 then its Krull
dimension is defined to be negative infinity; if the length of all series `a₀ < 
a₁ < ... < aₙ` is
unbounded, its Krull dimension is defined to be positive infinity.
-/
noncomputable def krullDim (α : Type*) [Preorder α] : WithBot ℕ∞ :=
  ⨆ (p : LTSeries α), p.length

/--
The **height** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and ending below or at `a`. In other words, it is
the largest `n` such that there's a series `a₀ < a₁ < ... < aₙ = a` (or `∞` if there is
no largest `n`).
-/
/-
**Order.height** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：height {α : Type*} [Preorder α] (a : α) : Nat∞
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **height** of an element `a` in a preorder `α` is the supremum of the rightm
ost index of all
relation series of `α` ordered by `<` and ending below or at `a`. In other words
, it is
the largest `n` such that there's a series `a₀ < a₁ < ... < aₙ = a` (or `∞` if t
here is
no largest `n`).
-/
noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : LTSeries α) (_ : p.last ≤ a), p.length

/--
The **coheight** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and beginning with `a`. In other words, it is
the largest `n` such that there's a series `a = a₀ < a₁ < ... < aₙ` (or `∞` if there is
no largest `n`).

The definition of `coheight` is via the `height` in the dual order, in order to easily transfer
theorems between `height` and `coheight`. See `coheight_eq` for the definition with a
series ordered by `<` and beginning with `a`.
-/
/-
**Order.coheight** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：coheight {α : Type*} [Preorder α] (a : α) : Nat∞
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **coheight** of an element `a` in a preorder `α` is the supremum of the righ
tmost index of all
relation series of `α` ordered by `<` and beginning with `a`. In other words, it
 is
the largest `n` such that there's a series `a = a₀ < a₁ < ... < aₙ` (or `∞` if t
here is
no largest `n`).

The definition of `coheight` is via the `height` in the dual order, in order to 
easily transfer
theorems between `height` and `coheight`. See `coheight_eq` for the definition w
ith a
series ordered by `<` and beginning with `a`.
-/
noncomputable def coheight {α : Type*} [Preorder α] (a : α) : ℕ∞ := height (α := αᵒᵈ) a

end definitions

/-!
## Height
-/

section height

variable {α β : Type*}

variable [Preorder α] [Preorder β]

/-
**Order.height_toDual** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (x : α), Order.height (OrderDual.toDu
al x) = Order.coheight x
参数：x : α；OrderDual.toDual x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma height_toDual (x : α) : height (OrderDual.toDual x) = coheight x := rfl
/-
**Order.height_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (x : αᵒᵈ), Order.height (OrderDual.of
Dual x) = Order.coheight x
参数：x : αᵒᵈ；OrderDual.ofDual x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma height_ofDual (x : αᵒᵈ) : height (OrderDual.ofDual x) = coheight x := rfl
/-
**Order.coheight_toDual** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (x : α), Order.coheight (OrderDual.to
Dual x) = Order.height x
参数：x : α；OrderDual.toDual x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coheight_toDual (x : α) : coheight (OrderDual.toDual x) = height x := rfl
/-
**Order.coheight_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (x : αᵒᵈ), Order.coheight (OrderDual.
ofDual x) = Order.height x
参数：x : αᵒᵈ；OrderDual.ofDual x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coheight_ofDual (x : αᵒᵈ) : coheight (OrderDual.ofDual x) = height x := rfl

/--
The **coheight** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and beginning with `a`.

This is not the definition of `coheight`. The definition of `coheight` is via the `height` in the
dual order, in order to easily transfer theorems between `height` and `coheight`.
-/
/-
**Order.coheight_eq** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_eq (a : α) : coheight a = ⨆ (p : LTSeries α) (_ : a <= p.head), (
p.length : Nat∞)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: SupSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨆ x,…
· 使用定理 `RelSeries.reverse_reverse`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSer
ies r), p.reverse.reverse = p
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)

--- 原说明 ---
The **coheight** of an element `a` in a preorder `α` is the supremum of the righ
tmost index of all
relation series of `α` ordered by `<` and beginning with `a`.

This is not the definition of `coheight`. The definition of `coheight` is via th
e `height` in the
dual order, in order to easily transfer theorems between `height` and `coheight`
.
-/
lemma coheight_eq (a : α) :
    coheight a = ⨆ (p : LTSeries α) (_ : a ≤ p.head), (p.length : ℕ∞) := by
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ ↦ RelSeries.reverse_reverse _,
    fun _ ↦ RelSeries.reverse_reverse _⟩
  congr! 1
/-
**Order.height_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_le_iff {a : α} {n : Nat∞} : height a <= n ↔ forall ⦃p : LTSeries α⦄
, p.last <= a -> p.length <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.height.eq_1`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Order.h
eight a = ⨆ p, ⨆ (_ : RelSeries.last p ≤ a), ↑p.length
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma height_le_iff {a : α} {n : ℕ∞} :
    height a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.last ≤ a → p.length ≤ n := by
  rw [height, iSup₂_le_iff]
/-
**Order.coheight_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_le_iff {a : α} {n : Nat∞} : coheight a <= n ↔ forall ⦃p : LTSerie
s α⦄, a <= p.head -> p.length <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.coheight_eq`：coheight_eq (a : α) : coheight a = ⨆ (p : LTSeries α)
 (_ : a <= p.head), (p.length : Nat∞)
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma coheight_le_iff {a : α} {n : ℕ∞} :
    coheight a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, a ≤ p.head → p.length ≤ n := by
  rw [coheight_eq, iSup₂_le_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**Order.height_le** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_le {a : α} {n : Nat∞} (h : forall (p : LTSeries α), p.last = a -> p
.length <= n) : height a <= n
参数：h : forall (p : LTSeries α), p.last = a -> p.length <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.height_le_iff`：height_le_iff {a : α} {n : Nat∞} : height a <= n ↔ 
forall ⦃p : LTSeries α⦄, p.last <= a -> p.length <= n
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `RelSeries.eraseLast_last_rel_last`：eraseLast_last_rel_last (p : RelSerie
s r) (h : p.length != 0) : p.eraseLast.last ~[r] p.last
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `RelSeries.snoc_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).length = 
p.length + …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelSeries.eraseLast_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSe
ries r), p.eraseLast.length = p.length - 1
· 使用定理 `RelSeries.last_snoc`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).last = newL
ast
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma height_le {a : α} {n : ℕ∞} (h : ∀ (p : LTSeries α), p.last = a → p.length ≤ n) :
    height a ≤ n := by
  apply height_le_iff.mpr
  intro p hlast
  wlog hlenpos : p.length ≠ 0
  · simp_all
  -- We replace the last element in the series with `a`
  let p' := p.eraseLast.snoc a (lt_of_lt_of_le (p.eraseLast_last_rel_last (by simp_all)) hlast)
  rw [show p.length = p'.length by simp [p']; lia]
  apply h
  simp [p']

/--
Variant of `height_le_iff` ranging only over those series that end exactly on `a`.
-/
/-
**Order.height_le_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_le_iff' {a : α} {n : Nat∞} : height a <= n ↔ forall ⦃p : LTSeries α
⦄, p.last = a -> p.length <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.height_le_iff`：height_le_iff {a : α} {n : Nat∞} : height a <= n ↔ 
forall ⦃p : LTSeries α⦄, p.last <= a -> p.length <= n
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Order.height_le`：height_le {a : α} {n : Nat∞} (h : forall (p : LTSeries 
α), p.last = a -> p.length <= n) : height a <= n

--- 原说明 ---
Variant of `height_le_iff` ranging only over those series that end exactly on `a
`.
-/
lemma height_le_iff' {a : α} {n : ℕ∞} :
    height a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.last = a → p.length ≤ n := by
  constructor
  · rw [height_le_iff]
    exact fun h p hlast => h (le_of_eq hlast)
  · exact height_le

/--
Alternative definition of height, with the supremum ranging only over those series that end at `a`.
-/
/-
**Order.height_eq_iSup_last_eq** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_eq_iSup_last_eq (a : α) : height a = ⨆ (p : LTSeries α) (_ : p.last
 = a), ↑(p.length)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.height_le_iff'`：height_le_iff' {a : α} {n : Nat∞} : height a <= n 
↔ forall ⦃p : LTSeries α⦄, p.last = a -> p.length <= n
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Alternative definition of height, with the supremum ranging only over those seri
es that end at `a`.
-/
lemma height_eq_iSup_last_eq (a : α) :
    height a = ⨆ (p : LTSeries α) (_ : p.last = a), ↑(p.length) := by
  apply eq_of_forall_ge_iff
  intro n
  rw [height_le_iff', iSup₂_le_iff]

set_option backward.isDefEq.respectTransparency false in
/--
Alternative definition of coheight, with the supremum only ranging over those series
that begin at `a`.
-/
/-
**Order.coheight_eq_iSup_head_eq** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_eq_iSup_head_eq (a : α) : coheight a = ⨆ (p : LTSeries α) (_ : p.
head = a), ↑(p.length)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.height_eq_iSup_last_eq`：height_eq_iSup_last_eq (a : α) : height a 
= ⨆ (p : LTSeries α) (_ : p.last = a), ↑(p.length)
· 使用定理 `Equiv.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: SupSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨆ x,…
· 使用定理 `RelSeries.reverse_reverse`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSer
ies r), p.reverse.reverse = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelSeries.head_reverse`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries
 r), p.reverse.head = p.last
· 使用定理 `RelSeries.reverse_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeri
es r), p.reverse.length = p.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Alternative definition of coheight, with the supremum only ranging over those se
ries
that begin at `a`.
-/
lemma coheight_eq_iSup_head_eq (a : α) :
    coheight a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length) := by
  change height (α := αᵒᵈ) a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length)
  rw [height_eq_iSup_last_eq]
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ ↦ RelSeries.reverse_reverse _,
    fun _ ↦ RelSeries.reverse_reverse _⟩
  simp

/--
Variant of `coheight_le_iff` ranging only over those series that begin exactly on `a`.
-/
/-
**Order.coheight_le_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_le_iff' {a : α} {n : Nat∞} : coheight a <= n ↔ forall ⦃p : LTSeri
es α⦄, p.head = a -> p.length <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.coheight_eq_iSup_head_eq`：coheight_eq_iSup_head_eq (a : α) : cohei
ght a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length)
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Variant of `coheight_le_iff` ranging only over those series that begin exactly o
n `a`.
-/
lemma coheight_le_iff' {a : α} {n : ℕ∞} :
    coheight a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.head = a → p.length ≤ n := by
  rw [coheight_eq_iSup_head_eq, iSup₂_le_iff]
/-
**Order.coheight_le** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_le {a : α} {n : Nat∞} (h : forall (p : LTSeries α), p.head = a ->
 p.length <= n) : coheight a <= n
参数：h : forall (p : LTSeries α), p.head = a -> p.length <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.coheight_le_iff'`：coheight_le_iff' {a : α} {n : Nat∞} : coheight a
 <= n ↔ forall ⦃p : LTSeries α⦄, p.head = a -> p.length <= n
-/
lemma coheight_le {a : α} {n : ℕ∞} (h : ∀ (p : LTSeries α), p.head = a → p.length ≤ n) :
    coheight a ≤ n :=
  coheight_le_iff'.mpr h

set_option backward.isDefEq.respectTransparency false in
/-
**Order.length_le_height** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：length_le_height {p : LTSeries α} {x : α} (hlast : p.last <= x) : p.length
 <= height x
参数：hlast : p.last <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.last_snoc`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).last = newL
ast
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `RelSeries.snoc_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).length = 
p.length + …
· 使用定理 `RelSeries.eraseLast_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSe
ries r), p.eraseLast.length = p.length - 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma length_le_height {p : LTSeries α} {x : α} (hlast : p.last ≤ x) :
    p.length ≤ height x := by
  by_cases hlen0 : p.length ≠ 0
  · let p' := p.eraseLast.snoc x (by
      apply lt_of_lt_of_le
      · apply p.step ⟨p.length - 1, by lia⟩
      · convert! hlast
        simp only [Fin.succ_mk, RelSeries.last, Fin.last]
        congr; lia)
    suffices p'.length ≤ height x by
      simp only [RelSeries.snoc_length, RelSeries.eraseLast_length, Nat.cast_add, ENat.natCast_sub,
        Nat.cast_one, p'] at this
      convert! this
      norm_cast
      lia
    refine le_iSup₂_of_le p' ?_ le_rfl
    simp [p']
  · simp_all

set_option backward.isDefEq.respectTransparency false in
/-
**Order.length_le_coheight** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：length_le_coheight {x : α} {p : LTSeries α} (hhead : x <= p.head) : p.leng
th <= coheight x
参数：hhead : x <= p.head。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.length_le_height`：length_le_height {p : LTSeries α} {x : α} (hlast
 : p.last <= x) : p.length <= height x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.last_reverse`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries
 r), p.reverse.last = p.head
-/
lemma length_le_coheight {x : α} {p : LTSeries α} (hhead : x ≤ p.head) :
    p.length ≤ coheight x :=
  length_le_height (α := αᵒᵈ) (p := p.reverse) (by simpa)

/--
The height of the last element in a series is larger or equal to the length of the series.
-/
/-
**Order.length_le_height_last** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：length_le_height_last {p : LTSeries α} : p.length <= height p.last
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.length_le_height`：length_le_height {p : LTSeries α} {x : α} (hlast
 : p.last <= x) : p.length <= height x
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The height of the last element in a series is larger or equal to the length of t
he series.
-/
lemma length_le_height_last {p : LTSeries α} : p.length ≤ height p.last :=
  length_le_height le_rfl

/--
The coheight of the first element in a series is larger or equal to the length of the series.
-/
/-
**Order.length_le_coheight_head** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：length_le_coheight_head {p : LTSeries α} : p.length <= coheight p.head
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.length_le_coheight`：length_le_coheight {x : α} {p : LTSeries α} (h
head : x <= p.head) : p.length <= coheight x
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The coheight of the first element in a series is larger or equal to the length o
f the series.
-/
lemma length_le_coheight_head {p : LTSeries α} : p.length ≤ coheight p.head :=
  length_le_coheight le_rfl

/--
The height of an element in a series is larger or equal to its index in the series.
-/
/-
**Order.index_le_height** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：index_le_height (p : LTSeries α) (i : Fin (p.length + 1)) : i <= height (p
 i)
参数：p : LTSeries α；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.length_le_height_last`：length_le_height_last {p : LTSeries α} : p.
length <= height p.last

--- 原说明 ---
The height of an element in a series is larger or equal to its index in the seri
es.
-/
lemma index_le_height (p : LTSeries α) (i : Fin (p.length + 1)) : i ≤ height (p i) :=
  length_le_height_last (p := p.take i)

/--
The coheight of an element in a series is larger or equal to its reverse index in the series.
-/
/-
**Order.rev_index_le_coheight** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：rev_index_le_coheight (p : LTSeries α) (i : Fin (p.length + 1)) : i.rev <=
 coheight (p i)
参数：p : LTSeries α；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用引理 `Order.index_le_height`：index_le_height (p : LTSeries α) (i : Fin (p.leng
th + 1)) : i <= height (p i)

--- 原说明 ---
The coheight of an element in a series is larger or equal to its reverse index i
n the series.
-/
lemma rev_index_le_coheight (p : LTSeries α) (i : Fin (p.length + 1)) : i.rev ≤ coheight (p i) := by
  simpa using! index_le_height (α := αᵒᵈ) p.reverse i.rev

/--
In a maximally long series, i.e one as long as the height of the last element, the height of each
element is its index in the series.
-/
/-
**Order.height_eq_index_of_length_eq_height_last** 是 Mathlib 中的一个引理，位于命名空间 `Orde
r`。
形式化陈述：height_eq_index_of_length_eq_height_last {p : LTSeries α} (h : p.length = 
height p.last) (i : Fin (p.length + 1)) : height (p i) = i
参数：h : p.length = height p.last；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Order.height_le`：height_le {a : α} {n : Nat∞} (h : forall (p : LTSeries 
α), p.last = a -> p.length <= n) : height a <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.head_drop`：head_drop (p : RelSeries r) (i : Fin (p.length + 1)
) : (p.drop i).head = p.toFun i
· 使用引理 `Order.length_le_height_last`：length_le_height_last {p : LTSeries α} : p.
length <= height p.last
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RelSeries.smash_length`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSeri
es r) (connect : p.last = q.head),   (p.smash q connect).length = p.length + q.l
ength
· 使用定理 `RelSeries.drop_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (i : Fin (p.length + 1)), (p.drop i).length = p.length - ↑i
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `RelSeries.last_smash`：∀ {α : Type u_1} {r : SetRel α α} {p q : RelSeries
 r} (h : p.last = q.head), (p.smash q h).last = q.last
· 使用引理 `RelSeries.last_drop`：last_drop (p : RelSeries r) (i : Fin (p.length + 1)
) : (p.drop i).last = p.last
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.index_le_height`：index_le_height (p : LTSeries α) (i : Fin (p.leng
th + 1)) : i <= height (p i)

--- 原说明 ---
In a maximally long series, i.e one as long as the height of the last element, t
he height of each
element is its index in the series.
-/
lemma height_eq_index_of_length_eq_height_last {p : LTSeries α} (h : p.length = height p.last)
    (i : Fin (p.length + 1)) : height (p i) = i := by
  refine le_antisymm (height_le ?_) (index_le_height p i)
  intro p' hp'
  have hp'' := length_le_height_last (p := p'.smash (p.drop i) (by simpa))
  simp [← h] at hp''; clear h
  norm_cast at *
  lia

set_option backward.isDefEq.respectTransparency false in
/--
In a maximally long series, i.e one as long as the coheight of the first element, the coheight of
each element is its reverse index in the series.
-/
/-
**Order.coheight_eq_index_of_length_eq_head_coheight** 是 Mathlib 中的一个引理，位于命名空间 `
Order`。
形式化陈述：coheight_eq_index_of_length_eq_head_coheight {p : LTSeries α} (h : p.lengt
h = coheight p.head) (i : Fin (p.length + 1)) : coheight (p i) = i.rev
参数：h : p.length = coheight p.head；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelSeries.reverse_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeri
es r), p.reverse.length = p.length
· 使用引理 `Order.height_eq_index_of_length_eq_height_last`：height_eq_index_of_lengt
h_eq_height_last {p : LTSeries α} (h : p.length = height p.last) (i : Fin (p.len
gth + 1)) : height (p i) = i
· 使用定理 `RelSeries.last_reverse`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries
 r), p.reverse.last = p.head

--- 原说明 ---
In a maximally long series, i.e one as long as the coheight of the first element
, the coheight of
each element is its reverse index in the series.
-/
lemma coheight_eq_index_of_length_eq_head_coheight {p : LTSeries α} (h : p.length = coheight p.head)
    (i : Fin (p.length + 1)) : coheight (p i) = i.rev := by
  simpa using! height_eq_index_of_length_eq_height_last (α := αᵒᵈ) (p := p.reverse) (by simpa) i.rev

@[gcongr]
/-
**Order.height_mono** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_mono : Monotone (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma height_mono : Monotone (α := α) height :=
  fun _ _ hab ↦ biSup_mono (fun _ hla => hla.trans hab)

@[gcongr]
/-
**Order.coheight_anti** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_anti : Antitone (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Monotone f → Antitone (f ∘ ⇑OrderDual.ofDual)
· 使用引理 `Order.height_mono`：height_mono : Monotone (α
-/
lemma coheight_anti : Antitone (α := α) coheight :=
  (height_mono (α := αᵒᵈ)).dual_left
/-
**Order.height_add_const** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma height_add_const (a : α) (n : ℕ∞) :
    height a + n = ⨆ (p : LTSeries α) (_ : p.last = a), p.length + n := by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  rw [height_eq_iSup_last_eq, iSup_subtype', iSup_subtype', ENat.iSup_add]

/-- For elements of finite height, `height` is strictly monotone. -/
/-
**Order.height_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x y : α}, x < y → Order.height x < ⊤
 → Order.height x < Order.height y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `_private.Mathlib.Order.KrullDimension.0.Order.height_add_const`：∀ {α : T
ype u_1} [inst : Preorder α] (a : α) (n : ℕ∞),   Order.height a + n = ⨆ p, ⨆ (_ 
: RelSeries.last p = a), ↑p.length + n
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Order.length_le_height_last`：length_le_height_last {p : LTSeries α} : p.
length <= height p.last
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RelSeries.snoc_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).length = 
p.length + …
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `RelSeries.last_snoc`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).last = newL
ast

--- 原说明 ---
For elements of finite height, `height` is strictly monotone.
-/
@[gcongr] lemma height_strictMono {x y : α} (hxy : x < y) (hfin : height x < ⊤) :
    height x < height y := by
  rw [← ENat.add_one_le_iff hfin.ne, height_add_const, iSup₂_le_iff]
  intro p hlast
  have := length_le_height_last (p := p.snoc y (by simp [*]))
  simpa using this
/-
**Order.height_add_one_le** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_add_one_le {a b : α} (hab : a < b) : height a + 1 <= height b
参数：hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.height_mono`：height_mono : Monotone (α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y
· 使用定理 `Order.height_strictMono`：∀ {α : Type u_1} [inst : Preorder α] {x y : α},
 x < y → Order.height x < ⊤ → Order.height x < Order.height y
-/
lemma height_add_one_le {a b : α} (hab : a < b) : height a + 1 ≤ height b := by
  cases hfin : height a with
  | top =>
    have : ⊤ ≤ height b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]

/-- For elements of finite height, `coheight` is strictly antitone. -/
/-
**Order.coheight_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x y : α}, y < x → Order.coheight x <
 ⊤ → Order.coheight x < Order.coheight y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.height_strictMono`：∀ {α : Type u_1} [inst : Preorder α] {x y : α},
 x < y → Order.height x < ⊤ → Order.height x < Order.height y

--- 原说明 ---
For elements of finite height, `coheight` is strictly antitone.
-/
@[gcongr] lemma coheight_strictAnti {x y : α} (hyx : y < x) (hfin : coheight x < ⊤) :
    coheight x < coheight y :=
  height_strictMono (α := αᵒᵈ) hyx hfin
/-
**Order.coheight_add_one_le** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_add_one_le {a b : α} (hab : b < a) : coheight a + 1 <= coheight b
参数：hab : b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.coheight_anti`：coheight_anti : Antitone (α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y
· 使用定理 `Order.coheight_strictAnti`：∀ {α : Type u_1} [inst : Preorder α] {x y : α
}, y < x → Order.coheight x < ⊤ → Order.coheight x < Order.coheight y
-/
lemma coheight_add_one_le {a b : α} (hab : b < a) : coheight a + 1 ≤ coheight b := by
  cases hfin : coheight a with
  | top =>
    have : ⊤ ≤ coheight b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]
/-
**Order.height_le_height_apply_of_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_le_height_apply_of_strictMono (f : α -> β) (hf : StrictMono f) (x :
 α) : height x <= height (f x)
参数：f : α -> β；hf : StrictMono f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Order.height_eq_iSup_last_eq`：height_eq_iSup_last_eq (a : α) : height a 
= ⨆ (p : LTSeries α) (_ : p.last = a), ↑(p.length)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LTSeries.map_length`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] (p : LTSeries α) (f : α → β)   (hf : StrictMono f), (p.ma
p f hf).l…
-/
lemma height_le_height_apply_of_strictMono (f : α → β) (hf : StrictMono f) (x : α) :
    height x ≤ height (f x) := by
  simp only [height_eq_iSup_last_eq]
  apply iSup₂_le
  intro p hlast
  apply le_iSup₂_of_le (p.map f hf) (by simp [hlast]) (by simp)
/-
**Order.coheight_le_coheight_apply_of_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Orde
r`。
形式化陈述：coheight_le_coheight_apply_of_strictMono (f : α -> β) (hf : StrictMono f) 
(x : α) : coheight x <= coheight (f x)
参数：f : α -> β；hf : StrictMono f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.height_le_height_apply_of_strictMono`：height_le_height_apply_of_st
rictMono (f : α -> β) (hf : StrictMono f) (x : α) : height x <= height (f x)
-/
lemma coheight_le_coheight_apply_of_strictMono (f : α → β) (hf : StrictMono f) (x : α) :
    coheight x ≤ coheight (f x) := by
  apply height_le_height_apply_of_strictMono (α := αᵒᵈ)
  exact fun _ _ h ↦ hf h
/-
**Order.coheight_eq_of_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_eq_of_strictMono (f : α -> β) (hf : StrictMono f) (h : forall a :
 α, forall b : β, f a < b -> exists (a' : α), a < a' ∧ f a' = b) (a : α) : cohei
ght a = coheight (f a)
参数：f : α -> β；hf : StrictMono f；h : forall a : α, forall b : β, f a < b -> exist
s (a' : α), a < a' ∧ f a' = b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Order.coheight_le_coheight_apply_of_strictMono`：coheight_le_coheight_app
ly_of_strictMono (f : α -> β) (hf : StrictMono f) (x : α) : coheight x <= coheig
ht (f x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.coheight_le_iff'`：coheight_le_iff' {a : α} {n : Nat∞} : coheight a
 <= n ↔ forall ⦃p : LTSeries α⦄, p.head = a -> p.length <= n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.singleton_length`：∀ {α : Type u_1} (r : SetRel α α) (a : α), (
RelSeries.singleton r a).length = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `RelSeries.cons_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newHead : α) (rel : (newHead, p.head) ∈ r),   (p.cons newHead rel).length = 
p.length + …
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Order.coheight_add_one_le`：coheight_add_one_le {a b : α} (hab : b < a) :
 coheight a + 1 <= coheight b
-/
lemma coheight_eq_of_strictMono (f : α → β) (hf : StrictMono f)
    (h : ∀ a : α, ∀ b : β, f a < b → ∃ (a' : α), a < a' ∧ f a' = b) (a : α) :
    coheight a = coheight (f a) := by
  refine le_antisymm (Order.coheight_le_coheight_apply_of_strictMono _ hf _) ?_
  refine coheight_le_iff'.mpr fun p hp ↦ ?_
  induction p using RelSeries.inductionOn generalizing a with
  | singleton x => simp
  | cons p x hx ih =>
    simp only [RelSeries.head_cons] at hp
    obtain ⟨a', haa', ha'⟩ := h a p.head (by grind)
    grw [RelSeries.cons_length, Nat.cast_add, Nat.cast_one, ih a' ha'.symm]
    exact coheight_add_one_le haa'
/-
**Order.height_eq_of_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_eq_of_strictMono (f : α -> β) (hf : StrictMono f) (h : forall a : α
, forall b : β, b < f a -> exists (a' : α), a' < a ∧ f a' = b) (a : α) : height 
a = height (f a)
参数：f : α -> β；hf : StrictMono f；h : forall a : α, forall b : β, b < f a -> exist
s (a' : α), a' < a ∧ f a' = b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.coheight_eq_of_strictMono`：coheight_eq_of_strictMono (f : α -> β) 
(hf : StrictMono f) (h : forall a : α, forall b : β, f a < b -> exists (a' : α),
 a < a' ∧ f a' = b) (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `strictMono_dual_iff`：strictMono_dual_iff : StrictMono (toDual ∘ f ∘ ofDu
al : αᵒᵈ -> βᵒᵈ) ↔ StrictMono f
-/
lemma height_eq_of_strictMono (f : α → β) (hf : StrictMono f)
    (h : ∀ a : α, ∀ b : β, b < f a → ∃ (a' : α), a' < a ∧ f a' = b) (a : α) :
    height a = height (f a) := by
  have : coheight (OrderDual.toDual a) = coheight (OrderDual.toDual (f a)) :=
    coheight_eq_of_strictMono (α := αᵒᵈ) (β := βᵒᵈ) (f := OrderDual.toDual ∘ f ∘ OrderDual.toDual)
    (strictMono_dual_iff.mp hf) (fun a b hab ↦ h a b hab) _
  simpa [Order.coheight_toDual] using this

@[simp]
/-
**Order.height_orderIso** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_orderIso (f : α ≃o β) (x : α) : height (f x) = height x
参数：f : α ≃o β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用引理 `Order.height_le_height_apply_of_strictMono`：height_le_height_apply_of_st
rictMono (f : α -> β) (hf : StrictMono f) (x : α) : height x <= height (f x)
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
lemma height_orderIso (f : α ≃o β) (x : α) : height (f x) = height x := by
  apply le_antisymm
  · simpa using height_le_height_apply_of_strictMono _ f.symm.strictMono (f x)
  · exact height_le_height_apply_of_strictMono _ f.strictMono x
/-
**Order.coheight_orderIso** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_orderIso (f : α ≃o β) (x : α) : coheight (f x) = coheight x
参数：f : α ≃o β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.height_orderIso`：height_orderIso (f : α ≃o β) (x : α) : height (f 
x) = height x
-/
lemma coheight_orderIso (f : α ≃o β) (x : α) : coheight (f x) = coheight x :=
  height_orderIso (α := αᵒᵈ) f.dual x
/-
**Order.exists_eq_iSup_of_iSup_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_eq_iSup_of_iSup_eq_coe {α : Type*} [Nonempty α] {f : α → ℕ∞} {n : ℕ}
    (h : (⨆ x, f x) = n) : ∃ x, f x = n := by
  obtain ⟨x, hx⟩ := ENat.sSup_mem_of_nonempty_of_lt_top (h ▸ ENat.natCast_lt_top _)
  use x
  simpa [hx] using! h

/-- There exists a series ending in an element for any length up to the element’s height. -/
/-
**Order.exists_series_of_le_height** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：exists_series_of_le_height (a : α) {n : Nat} (h : n <= height a) : exists 
p : LTSeries α, p.last = a ∧ p.length = n
参数：a : α；h : n <= height a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.last_drop`：last_drop (p : RelSeries r) (i : Fin (p.length + 1)
) : (p.drop i).last = p.last
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RelSeries.drop_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (i : Fin (p.length + 1)), (p.drop i).length = p.length - ↑i
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用引理 `ENat.iSup_natCast_eq_top`：iSup_natCast_eq_top : ⨆ i, (f i : Nat∞) = ⊤ ↔ 
¬ BddAbove (range f)
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用引理 `Order.height_eq_iSup_last_eq`：height_eq_iSup_last_eq (a : α) : height a 
= ⨆ (p : LTSeries α) (_ : p.last = a), ↑(p.length)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Order.KrullDimension.0.Order.exists_eq_iSup_of_iSup_eq_
coe`：∀ {α : Type u_3} [Nonempty α] {f : α → ℕ∞} {n : ℕ}, ⨆ x, f x = ↑n → ∃ x, f 
x = ↑n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
There exists a series ending in an element for any length up to the element’s he
ight.
-/
lemma exists_series_of_le_height (a : α) {n : ℕ} (h : n ≤ height a) :
    ∃ p : LTSeries α, p.last = a ∧ p.length = n := by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  cases ha : height a with
  | top =>
    clear h
    rw [height_eq_iSup_last_eq, iSup_subtype', ENat.iSup_natCast_eq_top, bddAbove_def] at ha
    contrapose! ha
    use n
    rintro m ⟨⟨p, rfl⟩, hp⟩
    simp only at hp
    by_contra! hnm
    apply ha (p.drop ⟨m-n, by lia⟩) (by simp) (by simp; lia)
  | coe m =>
    rw [ha, Nat.cast_le] at h
    rw [height_eq_iSup_last_eq, iSup_subtype'] at ha
    obtain ⟨⟨p, hlast⟩, hlen⟩ := exists_eq_iSup_of_iSup_eq_coe ha
    simp only [Nat.cast_inj] at hlen
    use p.drop ⟨m-n, by lia⟩
    constructor
    · simp [hlast]
    · simp [hlen]; lia
/-
**Order.exists_series_of_le_coheight** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：exists_series_of_le_coheight (a : α) {n : Nat} (h : n <= coheight a) : exi
sts p : LTSeries α, p.head = a ∧ p.length = n
参数：a : α；h : n <= coheight a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.exists_series_of_le_height`：exists_series_of_le_height (a : α) {n 
: Nat} (h : n <= height a) : exists p : LTSeries α, p.last = a ∧ p.length = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.reverse_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeri
es r), p.reverse.length = p.length
-/
lemma exists_series_of_le_coheight (a : α) {n : ℕ} (h : n ≤ coheight a) :
    ∃ p : LTSeries α, p.head = a ∧ p.length = n := by
  obtain ⟨p, hp, hl⟩ := exists_series_of_le_height (α := αᵒᵈ) a h
  exact ⟨p.reverse, by simpa, by simpa⟩

/-- For an element of finite height there exists a series ending in that element of that height. -/
/-
**Order.exists_series_of_height_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：exists_series_of_height_eq_coe (a : α) {n : Nat} (h : height a = n) : exis
ts p : LTSeries α, p.last = a ∧ p.length = n
参数：a : α；h : height a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.exists_series_of_le_height`：exists_series_of_le_height (a : α) {n 
: Nat} (h : n <= height a) : exists p : LTSeries α, p.last = a ∧ p.length = n
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
For an element of finite height there exists a series ending in that element of 
that height.
-/
lemma exists_series_of_height_eq_coe (a : α) {n : ℕ} (h : height a = n) :
    ∃ p : LTSeries α, p.last = a ∧ p.length = n :=
  exists_series_of_le_height a (le_of_eq h.symm)
/-
**Order.exists_series_of_coheight_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：exists_series_of_coheight_eq_coe (a : α) {n : Nat} (h : coheight a = n) : 
exists p : LTSeries α, p.head = a ∧ p.length = n
参数：a : α；h : coheight a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.exists_series_of_le_coheight`：exists_series_of_le_coheight (a : α)
 {n : Nat} (h : n <= coheight a) : exists p : LTSeries α, p.head = a ∧ p.length 
= n
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_series_of_coheight_eq_coe (a : α) {n : ℕ} (h : coheight a = n) :
    ∃ p : LTSeries α, p.head = a ∧ p.length = n :=
  exists_series_of_le_coheight a (le_of_eq h.symm)

/-- Another characterization of height, based on the supremum of the heights of elements below. -/
/-
**Order.height_eq_iSup_lt_height** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_eq_iSup_lt_height (x : α) : height x = ⨆ y < x, height y + 1
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Order.height_le`：height_le {a : α} {n : Nat∞} (h : forall (p : LTSeries 
α), p.last = a -> p.length <= n) : height a <= n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `RelSeries.eraseLast_last_rel_last`：eraseLast_last_rel_last (p : RelSerie
s r) (h : p.length != 0) : p.eraseLast.last ~[r] p.last
· 使用定理 `_private.Mathlib.Order.KrullDimension.0.Order.height_add_const`：∀ {α : T
ype u_1} [inst : Preorder α] (a : α) (n : ℕ∞),   Order.height a + n = ⨆ p, ⨆ (_ 
: RelSeries.last p = a), ↑p.length + n
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `RelSeries.eraseLast_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSe
ries r), p.eraseLast.length = p.length - 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `RelSeries.last_snoc`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).last = newL
ast
· 使用定理 `RelSeries.snoc_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).length = 
p.length + …

--- 原说明 ---
Another characterization of height, based on the supremum of the heights of elem
ents below.
-/
lemma height_eq_iSup_lt_height (x : α) : height x = ⨆ y < x, height y + 1 := by
  apply le_antisymm
  · apply height_le
    intro p hp
    cases hlen : p.length with
    | zero => simp
    | succ n =>
      apply le_iSup_of_le p.eraseLast.last
      apply le_iSup_of_le (by rw [← hp]; exact p.eraseLast_last_rel_last (by lia))
      rw [height_add_const]
      apply le_iSup₂_of_le p.eraseLast (by rfl) (by simp [hlen])
  · apply iSup₂_le; intro y hyx
    rw [height_add_const]
    apply iSup₂_le; intro p hp
    apply le_iSup₂_of_le (p.snoc x (hp ▸ hyx)) (by simp) (by simp)

/--
Another characterization of coheight, based on the supremum of the coheights of elements above.
-/
/-
**Order.coheight_eq_iSup_gt_coheight** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_eq_iSup_gt_coheight (x : α) : coheight x = ⨆ y > x, coheight y + 
1
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.height_eq_iSup_lt_height`：height_eq_iSup_lt_height (x : α) : heigh
t x = ⨆ y < x, height y + 1

--- 原说明 ---
Another characterization of coheight, based on the supremum of the coheights of 
elements above.
-/
lemma coheight_eq_iSup_gt_coheight (x : α) : coheight x = ⨆ y > x, coheight y + 1 :=
  height_eq_iSup_lt_height (α := αᵒᵈ) x
/-
**Order.height_le_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_le_coe_iff {x : α} {n : Nat} : height x <= n ↔ forall y < x, height
 y < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.height_eq_iSup_lt_height`：height_eq_iSup_lt_height (x : α) : heigh
t x = ⨆ y < x, height y + 1
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma height_le_coe_iff {x : α} {n : ℕ} : height x ≤ n ↔ ∀ y < x, height y < n := by
  conv_lhs => rw [height_eq_iSup_lt_height, iSup₂_le_iff]
  congr! 2 with y _
  cases height y
  · simp
  · norm_cast
/-
**Order.coheight_le_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_le_coe_iff {x : α} {n : Nat} : coheight x <= n ↔ forall y > x, co
height y < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.height_le_coe_iff`：height_le_coe_iff {x : α} {n : Nat} : height x 
<= n ↔ forall y < x, height y < n
-/
lemma coheight_le_coe_iff {x : α} {n : ℕ} : coheight x ≤ n ↔ ∀ y > x, coheight y < n :=
  height_le_coe_iff (α := αᵒᵈ)

/--
The height of an element is infinite iff there exist series of arbitrary length ending in that
element.
-/
/-
**Order.height_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_eq_top_iff {x : α} : height x = ⊤ ↔ forall n, exists p : LTSeries α
, p.last = x ∧ p.length = n where mp h n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.exists_series_of_le_height`：exists_series_of_le_height (a : α) {n 
: Nat} (h : n <= height a) : exists p : LTSeries α, p.last = a ∧ p.length = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.height_eq_iSup_last_eq`：height_eq_iSup_last_eq (a : α) : height a 
= ⨆ (p : LTSeries α) (_ : p.last = a), ↑(p.length)
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用引理 `ENat.iSup_natCast_eq_top`：iSup_natCast_eq_top : ⨆ i, (f i : Nat∞) = ⊤ ↔ 
¬ BddAbove (range f)
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
The height of an element is infinite iff there exist series of arbitrary length 
ending in that
element.
-/
lemma height_eq_top_iff {x : α} :
    height x = ⊤ ↔ ∀ n, ∃ p : LTSeries α, p.last = x ∧ p.length = n where
  mp h n := by
    apply exists_series_of_le_height x (n := n)
    simp [h]
  mpr h := by
    rw [height_eq_iSup_last_eq, iSup_subtype', ENat.iSup_natCast_eq_top, bddAbove_def]
    push Not
    intro n
    obtain ⟨p, hlast, hp⟩ := h (n + 1)
    exact ⟨p.length, ⟨⟨⟨p, hlast⟩, by simp [hp]⟩, by simp [hp]⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
The coheight of an element is infinite iff there exist series of arbitrary length ending in that
element.
-/
/-
**Order.coheight_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_eq_top_iff {x : α} : coheight x = ⊤ ↔ forall n, exists p : LTSeri
es α, p.head = x ∧ p.length = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.last_reverse`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries
 r), p.reverse.last = p.head
· 使用定理 `RelSeries.reverse_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeri
es r), p.reverse.length = p.length
· 使用定理 `RelSeries.head_reverse`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries
 r), p.reverse.head = p.last
· 使用引理 `Order.height_eq_top_iff`：height_eq_top_iff {x : α} : height x = ⊤ ↔ fora
ll n, exists p : LTSeries α, p.last = x ∧ p.length = n where mp h n

--- 原说明 ---
The coheight of an element is infinite iff there exist series of arbitrary lengt
h ending in that
element.
-/
lemma coheight_eq_top_iff {x : α} :
    coheight x = ⊤ ↔ ∀ n, ∃ p : LTSeries α, p.head = x ∧ p.length = n := by
  convert! height_eq_top_iff (α := αᵒᵈ) (x := x) using 2 with n
  constructor <;> (intro ⟨p, hp, hl⟩; use p.reverse; constructor <;> simpa)

/-- The elements of height zero are the minimal elements. -/
/-
**Order.height_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x : α}, Order.height x = 0 ↔ IsMin x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Order.height_le_coe_iff`：height_le_coe_iff {x : α} {n : Nat} : height x 
<= n ↔ forall y < x, height y < n

--- 原说明 ---
The elements of height zero are the minimal elements.
-/
@[simp] lemma height_eq_zero {x : α} : height x = 0 ↔ IsMin x := by
  simpa [isMin_iff_forall_not_lt] using height_le_coe_iff (x := x) (n := 0)

protected alias ⟨_, IsMin.height_eq_zero⟩ := height_eq_zero

/-- The elements of coheight zero are the maximal elements. -/
/-
**Order.coheight_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x : α}, Order.coheight x = 0 ↔ IsMax
 x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.height_eq_zero`：∀ {α : Type u_1} [inst : Preorder α] {x : α}, Orde
r.height x = 0 ↔ IsMin x

--- 原说明 ---
The elements of coheight zero are the maximal elements.
-/
@[simp] lemma coheight_eq_zero {x : α} : coheight x = 0 ↔ IsMax x :=
  height_eq_zero (α := αᵒᵈ)

protected alias ⟨_, IsMax.coheight_eq_zero⟩ := coheight_eq_zero
/-
**Order.height_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_ne_zero {x : α} : height x != 0 ↔ ¬ IsMin x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Order.height_eq_zero`：∀ {α : Type u_1} [inst : Preorder α] {x : α}, Orde
r.height x = 0 ↔ IsMin x
-/
lemma height_ne_zero {x : α} : height x ≠ 0 ↔ ¬ IsMin x := height_eq_zero.not
/-
**Order.height_pos** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x : α}, 0 < Order.height x ↔ ¬IsMin 
x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma height_pos {x : α} : 0 < height x ↔ ¬ IsMin x := by
  simp [pos_iff_ne_zero]
/-
**Order.coheight_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_ne_zero {x : α} : coheight x != 0 ↔ ¬ IsMax x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Order.coheight_eq_zero`：∀ {α : Type u_1} [inst : Preorder α] {x : α}, Or
der.coheight x = 0 ↔ IsMax x
-/
lemma coheight_ne_zero {x : α} : coheight x ≠ 0 ↔ ¬ IsMax x := coheight_eq_zero.not
/-
**Order.coheight_pos** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x : α}, 0 < Order.coheight x ↔ ¬IsMa
x x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma coheight_pos {x : α} : 0 < coheight x ↔ ¬ IsMax x := by
  simp [pos_iff_ne_zero]
/-
**Order.height_bot** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ (α : Type u_3) [inst : Preorder α] [inst_1 : OrderBot α], Order.height ⊥
 = 0
参数：α : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma height_bot (α : Type*) [Preorder α] [OrderBot α] : height (⊥ : α) = 0 := by simp
/-
**Order.coheight_top** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ (α : Type u_3) [inst : Preorder α] [inst_1 : OrderTop α], Order.coheight
 ⊤ = 0
参数：α : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma coheight_top (α : Type*) [Preorder α] [OrderTop α] : coheight (⊤ : α) = 0 := by simp
/-
**Order.height_pos_of_bot_lt** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_pos_of_bot_lt {x : α} [OrderBot α] (h : ⊥ < x) : 0 < height x
参数：h : ⊥ < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.height_pos`：∀ {α : Type u_1} [inst : Preorder α] {x : α}, 0 < Orde
r.height x ↔ ¬IsMin x
-/
lemma height_pos_of_bot_lt {x : α} [OrderBot α] (h : ⊥ < x) : 0 < height x := by
  rw [height_pos]
  grind [not_isMin_iff]
/-
**Order.coheight_pos_of_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_pos_of_lt_top {x : α} [OrderTop α] (h : x < ⊤) : 0 < coheight x
参数：h : x < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.coheight_pos`：∀ {α : Type u_1} [inst : Preorder α] {x : α}, 0 < Or
der.coheight x ↔ ¬IsMax x
-/
lemma coheight_pos_of_lt_top {x : α} [OrderTop α] (h : x < ⊤) : 0 < coheight x := by
  rw [coheight_pos]
  grind [not_isMax_iff]
/-
**Order.coe_lt_height_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coe_lt_height_iff {x : α} {n : Nat} (hfin : height x < ⊤) : n < height x ↔
 exists y < x, height y = n where mp h
参数：hfin : height x < ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用引理 `Order.exists_series_of_height_eq_coe`：exists_series_of_height_eq_coe (a 
: α) {n : Nat} (h : height a = n) : exists p : LTSeries α, p.last = a ∧ p.length
 = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LTSeries.strictMono`：strictMono (x : LTSeries α) : StrictMono x
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用引理 `Order.height_eq_index_of_length_eq_height_last`：height_eq_index_of_lengt
h_eq_height_last {p : LTSeries α} (h : p.length = height p.last) (i : Fin (p.len
gth + 1)) : height (p i) = i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Order.height_strictMono`：∀ {α : Type u_1} [inst : Preorder α] {x y : α},
 x < y → Order.height x < ⊤ → Order.height x < Order.height y
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Order.height_mono`：height_mono : Monotone (α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma coe_lt_height_iff {x : α} {n : ℕ} (hfin : height x < ⊤) :
    n < height x ↔ ∃ y < x, height y = n where
  mp h := by
    obtain ⟨m, hx : height x = m⟩ := Option.ne_none_iff_exists'.mp hfin.ne_top
    rw [hx] at h; norm_cast at h
    obtain ⟨p, hp, hlen⟩ := exists_series_of_height_eq_coe x hx
    use p ⟨n, by lia⟩
    constructor
    · rw [← hp]
      apply LTSeries.strictMono
      simp [Fin.last]; lia
    · exact height_eq_index_of_length_eq_height_last (by simp [hlen, hp, hx]) ⟨n, by lia⟩
  mpr := fun ⟨y, hyx, hy⟩ =>
    hy ▸ height_strictMono hyx (lt_of_le_of_lt (height_mono hyx.le) hfin)
/-
**Order.coe_lt_coheight_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coe_lt_coheight_iff {x : α} {n : Nat} (hfin : coheight x < ⊤) : n < coheig
ht x ↔ exists y > x, coheight y = n
参数：hfin : coheight x < ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.coe_lt_height_iff`：coe_lt_height_iff {x : α} {n : Nat} (hfin : hei
ght x < ⊤) : n < height x ↔ exists y < x, height y = n where mp h
-/
lemma coe_lt_coheight_iff {x : α} {n : ℕ} (hfin : coheight x < ⊤) :
    n < coheight x ↔ ∃ y > x, coheight y = n :=
  coe_lt_height_iff (α := αᵒᵈ) hfin
/-
**Order.height_eq_coe_add_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_eq_coe_add_one_iff {x : α} {n : Nat} : height x = n + 1 ↔ height x 
< ⊤ ∧ (exists y < x, height y = n) ∧ (forall y < x, height y <= n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.coe_lt_height_iff`：coe_lt_height_iff {x : α} {n : Nat} (hfin : hei
ght x < ⊤) : n < height x ↔ exists y < x, height y = n where mp h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Order.height_le_coe_iff`：height_le_coe_iff {x : α} {n : Nat} : height x 
<= n ↔ forall y < x, height y < n
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
lemma height_eq_coe_add_one_iff {x : α} {n : ℕ} :
    height x = n + 1 ↔ height x < ⊤ ∧ (∃ y < x, height y = n) ∧ (∀ y < x, height y ≤ n) := by
  wlog hfin : height x < ⊤
  · simp_all [← Nat.cast_add_one, -Nat.cast_add]
  simp only [hfin, true_and]
  trans n < height x ∧ height x ≤ n + 1
  · rw [le_antisymm_iff, and_comm]
    simp [ENat.add_one_le_iff]
  · congr! 1
    · exact coe_lt_height_iff hfin
    · simpa [hfin, ENat.lt_add_one_iff] using height_le_coe_iff (x := x) (n := n + 1)
/-
**Order.coheight_eq_coe_add_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_eq_coe_add_one_iff {x : α} {n : Nat} : coheight x = n + 1 ↔ cohei
ght x < ⊤ ∧ (exists y > x, coheight y = n) ∧ (forall y > x, coheight y <= n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.height_eq_coe_add_one_iff`：height_eq_coe_add_one_iff {x : α} {n : 
Nat} : height x = n + 1 ↔ height x < ⊤ ∧ (exists y < x, height y = n) ∧ (forall 
y < x, height y <= n)
-/
lemma coheight_eq_coe_add_one_iff {x : α} {n : ℕ} :
    coheight x = n + 1 ↔
      coheight x < ⊤ ∧ (∃ y > x, coheight y = n) ∧ (∀ y > x, coheight y ≤ n) :=
  height_eq_coe_add_one_iff (α := αᵒᵈ)
/-
**Order.height_eq_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_eq_coe_iff {x : α} {n : Nat} : height x = n ↔ height x < ⊤ ∧ (n = 0
 ∨ exists y < x, height y = n - 1) ∧ (forall y < x, height y < n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用引理 `Order.height_eq_coe_add_one_iff`：height_eq_coe_add_one_iff {x : α} {n : 
Nat} : height x = n + 1 ↔ height x < ⊤ ∧ (exists y < x, height y = n) ∧ (forall 
y < x, height y <= n)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
（共 36 条，此处仅展示前 30 条）
-/
lemma height_eq_coe_iff {x : α} {n : ℕ} :
    height x = n ↔
      height x < ⊤ ∧ (n = 0 ∨ ∃ y < x, height y = n - 1) ∧ (∀ y < x, height y < n) := by
  wlog hfin : height x < ⊤
  · simp_all
  simp only [hfin, true_and]
  cases n
  case zero => simp [isMin_iff_forall_not_lt]
  case succ n =>
    simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
    rw [height_eq_coe_add_one_iff]
    simp only [hfin, true_and]
    congr! 3
    rename_i y _
    cases height y <;> simp; norm_cast; lia
/-
**Order.coheight_eq_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_eq_coe_iff {x : α} {n : Nat} : coheight x = n ↔ coheight x < ⊤ ∧ 
(n = 0 ∨ exists y > x, coheight y = n - 1) ∧ (forall y > x, coheight y < n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.height_eq_coe_iff`：height_eq_coe_iff {x : α} {n : Nat} : height x 
= n ↔ height x < ⊤ ∧ (n = 0 ∨ exists y < x, height y = n - 1) ∧ (forall y < x, h
eight y < n)
-/
lemma coheight_eq_coe_iff {x : α} {n : ℕ} :
    coheight x = n ↔
      coheight x < ⊤ ∧ (n = 0 ∨ ∃ y > x, coheight y = n - 1) ∧ (∀ y > x, coheight y < n) :=
  height_eq_coe_iff (α := αᵒᵈ)

/-- The elements of finite height `n` are the minimal elements among those of height `≥ n`. -/
/-
**Order.height_eq_coe_iff_minimal_le_height** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_eq_coe_iff_minimal_le_height {a : α} {n : Nat} : height a = n ↔ Min
imal (fun y => n <= height y) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `RelSeries.eraseLast_last_rel_last`：eraseLast_last_rel_last (p : RelSerie
s r) (h : p.length != 0) : p.eraseLast.last ~[r] p.last
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `RelSeries.eraseLast_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSe
ries r), p.eraseLast.length = p.length - 1
· 使用引理 `Order.length_le_height_last`：length_le_height_last {p : LTSeries α} : p.
length <= height p.last
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The elements of finite height `n` are the minimal elements among those of height
 `≥ n`.
-/
lemma height_eq_coe_iff_minimal_le_height {a : α} {n : ℕ} :
    height a = n ↔ Minimal (fun y => n ≤ height y) a := by
  by_cases! hfin : height a < ⊤
  · cases hn : n with
    | zero => simp
    | succ => simp [minimal_iff_forall_lt, height_eq_coe_add_one_iff, ENat.add_one_le_iff,
        coe_lt_height_iff, *]
  · suffices ∃ x < a, ↑n ≤ height x by
      simp_all [minimal_iff_forall_lt]
    simp only [top_le_iff, height_eq_top_iff] at hfin
    obtain ⟨p, rfl, hp⟩ := hfin (n + 1)
    use p.eraseLast.last, p.eraseLast_last_rel_last (by lia)
    simpa [hp] using length_le_height_last (p := p.eraseLast)

/-- The elements of finite coheight `n` are the maximal elements among those of coheight `≥ n`. -/
/-
**Order.coheight_eq_coe_iff_maximal_le_coheight** 是 Mathlib 中的一个引理，位于命名空间 `Order
`。
形式化陈述：coheight_eq_coe_iff_maximal_le_coheight {a : α} {n : Nat} : coheight a = n
 ↔ Maximal (fun y => n <= coheight y) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.height_eq_coe_iff_minimal_le_height`：height_eq_coe_iff_minimal_le_
height {a : α} {n : Nat} : height a = n ↔ Minimal (fun y => n <= height y) a

--- 原说明 ---
The elements of finite coheight `n` are the maximal elements among those of cohe
ight `≥ n`.
-/
lemma coheight_eq_coe_iff_maximal_le_coheight {a : α} {n : ℕ} :
    coheight a = n ↔ Maximal (fun y => n ≤ coheight y) a :=
  height_eq_coe_iff_minimal_le_height (α := αᵒᵈ)
/-
**Order.one_lt_height_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：one_lt_height_iff {x : α} : 1 < Order.height x ↔ exists y z, z < y ∧ y < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用引理 `Order.exists_series_of_le_height`：exists_series_of_le_height (a : α) {n 
: Nat} (h : n <= height a) : exists p : LTSeries α, p.last = a ∧ p.length = n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `RelSeries.rel_of_lt`：rel_of_lt [r.IsTrans] (x : RelSeries r) {i j : Fin 
(x.length + 1)} (h : i < j) : x i ~[r] x j
· 使用定理 `SetRel.instIsTransOfPredProdMatch_1PropOfIsTrans`：∀ {α : Type u_1} {R : 
α → α → Prop} [IsTrans α R], SetRel.IsTrans {(a, b) | R a b}
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.isChain_pair`：isChain_pair {x y} : IsChain R [x, y] ↔ R x y
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `RelSeries.toList_fromListIsChain`：toList_fromListIsChain (l : List α) (l
_ne_nil : l != []) (hl : l.IsChain (· ~[r] ·)) : (fromListIsChain l l_ne_nil hl)
.toList = l
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用引理 `Order.length_le_height`：length_le_height {p : LTSeries α} {x : α} (hlast
 : p.last <= x) : p.length <= height x
（共 31 条，此处仅展示前 30 条）
-/
lemma one_lt_height_iff {x : α} : 1 < Order.height x ↔ ∃ y z, z < y ∧ y < x := by
  rw [← ENat.add_one_le_iff ENat.one_ne_top, one_add_one_eq_two]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨p, hp, hlen⟩ := Order.exists_series_of_le_height x (n := 2) h
    refine ⟨p 1, p 0, p.rel_of_lt ?_, hp ▸ p.rel_of_lt ?_⟩ <;> simp [Fin.lt_def, hlen]
  · rintro ⟨y, z, hzy, hyx⟩
    let p : LTSeries α := RelSeries.fromListIsChain [z, y, x] (List.cons_ne_nil z [y, x])
      (List.IsChain.cons_cons hzy <| List.isChain_pair.mpr hyx)
    have : p.last = x := by simp [p, ← RelSeries.getLast_toList]
    exact Order.length_le_height this.le

end height

/-!
## Krull dimension
-/

section krullDim

variable {α β : Type*}

variable [Preorder α] [Preorder β]

/-
**Order.LTSeries.length_le_krullDim** 是 Mathlib 中的一个定理，位于命名空间 `Order.LTSeries`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (p : LTSeries α), ↑p.length ≤ Order.k
rullDim α
参数：p : LTSeries α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
lemma LTSeries.length_le_krullDim (p : LTSeries α) : p.length ≤ krullDim α := le_sSup ⟨_, rfl⟩

@[simp]
/-
**Order.krullDim_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_bot_iff : krullDim α = ⊥ ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Order.krullDim.eq_1`：∀ (α : Type u_1) [inst : Preorder α], Order.krullDi
m α = ⨆ p, ↑p.length
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma krullDim_eq_bot_iff : krullDim α = ⊥ ↔ IsEmpty α := by
  rw [eq_bot_iff, krullDim, iSup_le_iff]
  simp only [le_bot_iff, WithBot.natCast_ne_bot, isEmpty_iff]
  exact ⟨fun H x ↦ H ⟨0, fun _ ↦ x, by simp⟩, (· <| · 1)⟩
/-
**Order.krullDim_nonneg_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_nonneg_iff : 0 <= krullDim α ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.krullDim_eq_bot_iff`：krullDim_eq_bot_iff : krullDim α = ⊥ ↔ IsEmpt
y α
· 使用定理 `WithBot.lt_coe_bot`：lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `WithBot.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma krullDim_nonneg_iff : 0 ≤ krullDim α ↔ Nonempty α := by
  contrapose!
  rw [← krullDim_eq_bot_iff, ← WithBot.lt_coe_bot, bot_eq_zero, WithBot.coe_zero]
/-
**Order.krullDim_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.krullDim_eq_bot_iff`：krullDim_eq_bot_iff : krullDim α = ⊥ ↔ IsEmpt
y α
-/
lemma krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥ := krullDim_eq_bot_iff.mpr ‹_›
/-
**Order.krullDim_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_nonneg [Nonempty α] : 0 <= krullDim α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.krullDim_nonneg_iff`：krullDim_nonneg_iff : 0 <= krullDim α ↔ Nonem
pty α
-/
lemma krullDim_nonneg [Nonempty α] : 0 ≤ krullDim α := krullDim_nonneg_iff.mpr ‹_›
/-
**Order.krullDim_ne_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：krullDim_ne_bot_iff : krullDim α != ⊥ ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Order.krullDim_eq_bot_iff`：krullDim_eq_bot_iff : krullDim α = ⊥ ↔ IsEmpt
y α
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem krullDim_ne_bot_iff : krullDim α ≠ ⊥ ↔ Nonempty α := by
  rw [ne_eq, krullDim_eq_bot_iff, not_isEmpty_iff]
/-
**Order.bot_lt_krullDim_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：bot_lt_krullDim_iff : ⊥ < krullDim α ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Order.krullDim_ne_bot_iff`：krullDim_ne_bot_iff : krullDim α != ⊥ ↔ Nonem
pty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot_lt_krullDim_iff : ⊥ < krullDim α ↔ Nonempty α := by
  rw [bot_lt_iff_ne_bot, krullDim_ne_bot_iff]
/-
**Order.bot_lt_krullDim** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：bot_lt_krullDim [Nonempty α] : ⊥ < krullDim α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.bot_lt_krullDim_iff`：bot_lt_krullDim_iff : ⊥ < krullDim α ↔ Nonemp
ty α
-/
theorem bot_lt_krullDim [Nonempty α] : ⊥ < krullDim α :=
  bot_lt_krullDim_iff.mpr ‹_›
/-
**Order.krullDim_nonpos_iff_forall_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_nonpos_iff_forall_isMax : krullDim α <= 0 ↔ forall x : α, IsMax x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
-/
lemma krullDim_nonpos_iff_forall_isMax : krullDim α ≤ 0 ↔ ∀ x : α, IsMax x := by
  simp only [krullDim, iSup_le_iff, isMax_iff_forall_not_lt]
  refine ⟨fun H x y h ↦ (H ⟨1, ![x, y],
    fun i ↦ by obtain rfl := Subsingleton.elim i 0; simpa⟩).not_gt (by simp), ?_⟩
  · rintro H ⟨_ | n, l, h⟩
    · simp
    · cases H (l 0) (l 1) (h 0)
/-
**Order.krullDim_nonpos_iff_forall_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_nonpos_iff_forall_isMin : krullDim α <= 0 ↔ forall x : α, IsMin x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
lemma krullDim_nonpos_iff_forall_isMin : krullDim α ≤ 0 ↔ ∀ x : α, IsMin x := by
  simp only [krullDim_nonpos_iff_forall_isMax, IsMax, IsMin]
  exact forall_comm
/-
**Order.krullDim_le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_le_one_iff : krullDim α <= 1 ↔ forall x : α, IsMin x ∨ IsMax x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma krullDim_le_one_iff : krullDim α ≤ 1 ↔ ∀ x : α, IsMin x ∨ IsMax x := by
  simp_rw [isMax_iff_forall_not_lt, isMin_iff_forall_not_lt, krullDim, iSup_le_iff]
  contrapose!
  constructor
  · rintro ⟨⟨_ | _ | n, l, hl⟩, hl'⟩
    iterate 2 · cases hl'.not_ge (by simp)
    exact ⟨l 1, ⟨l 0, hl 0⟩, l 2, hl 1⟩
  · rintro ⟨x, ⟨y, hxy⟩, z, hzx⟩
    exact ⟨⟨2, ![y, x, z], fun i ↦ by fin_cases i <;> simpa⟩, by simp⟩
/-
**Order.krullDim_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_pos_iff : 0 < krullDim α ↔ exists x y : α, x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma krullDim_pos_iff : 0 < krullDim α ↔ ∃ x y : α, x < y := by
  contrapose!
  simp_rw [← isMax_iff_forall_not_lt, ← krullDim_nonpos_iff_forall_isMax]
/-
**Order.one_le_krullDim_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：one_le_krullDim_iff : 1 <= krullDim α ↔ exists x y : α, x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.krullDim_pos_iff`：krullDim_pos_iff : 0 < krullDim α ↔ exists x y :
 α, x < y
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `ENat.WithBot.add_one_le_iff`：add_one_le_iff {n : Nat} {m : WithBot Nat∞}
 : n + 1 <= m ↔ n < m
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_le_krullDim_iff : 1 ≤ krullDim α ↔ ∃ x y : α, x < y := by
  rw [← krullDim_pos_iff, ← Nat.cast_zero, ← ENat.WithBot.add_one_le_iff, Nat.cast_zero, zero_add]
/-
**Order.krullDim_nonpos_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_nonpos_of_subsingleton [Subsingleton α] : krullDim α <= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_nonpos_iff_forall_isMax`：krullDim_nonpos_iff_forall_isMax
 : krullDim α <= 0 ↔ forall x : α, IsMax x
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma krullDim_nonpos_of_subsingleton [Subsingleton α] : krullDim α ≤ 0 := by
  rw [krullDim_nonpos_iff_forall_isMax]
  exact fun x y h ↦ (Subsingleton.elim x y).ge
/-
**Order.krullDim_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_zero [Nonempty α] [Subsingleton α] : krullDim α = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Order.krullDim_nonpos_of_subsingleton`：krullDim_nonpos_of_subsingleton [
Subsingleton α] : krullDim α <= 0
· 使用引理 `Order.krullDim_nonneg`：krullDim_nonneg [Nonempty α] : 0 <= krullDim α
-/
lemma krullDim_eq_zero [Nonempty α] [Subsingleton α] :
    krullDim α = 0 :=
  le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg
/-
**Order.krullDim_eq_zero_of_unique** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_zero_of_unique [Unique α] : krullDim α = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Order.krullDim_nonpos_of_subsingleton`：krullDim_nonpos_of_subsingleton [
Subsingleton α] : krullDim α <= 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `Order.krullDim_nonneg`：krullDim_nonneg [Nonempty α] : 0 <= krullDim α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma krullDim_eq_zero_of_unique [Unique α] : krullDim α = 0 :=
  le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg

section PartialOrder

variable {α : Type*} [PartialOrder α]

/-
**Order.krullDim_le_one_iff_forall_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_le_one_iff_forall_isMax [OrderBot α] : krullDim α <= 1 ↔ forall x
 : α, x != ⊥ -> IsMax x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma krullDim_le_one_iff_forall_isMax [OrderBot α] :
    krullDim α ≤ 1 ↔ ∀ x : α, x ≠ ⊥ → IsMax x := by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_left]
/-
**Order.krullDim_eq_zero_iff_of_orderBot** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_zero_iff_of_orderBot [OrderBot α] : krullDim α = 0 ↔ Subsingle
ton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用引理 `Order.krullDim_nonpos_iff_forall_isMax`：krullDim_nonpos_iff_forall_isMax
 : krullDim α <= 0 ↔ forall x : α, IsMax x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `Order.krullDim_eq_zero`：krullDim_eq_zero [Nonempty α] [Subsingleton α] :
 krullDim α = 0
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
-/
lemma krullDim_eq_zero_iff_of_orderBot [OrderBot α] :
    krullDim α = 0 ↔ Subsingleton α :=
  ⟨fun H ↦ subsingleton_of_forall_eq ⊥ fun _ ↦ le_bot_iff.mp
    (krullDim_nonpos_iff_forall_isMax.mp H.le ⊥ bot_le), fun _ ↦ Order.krullDim_eq_zero⟩
/-
**Order.krullDim_pos_iff_of_orderBot** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_pos_iff_of_orderBot [OrderBot α] : 0 < krullDim α ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用引理 `Order.krullDim_eq_zero_iff_of_orderBot`：krullDim_eq_zero_iff_of_orderBot
 [OrderBot α] : krullDim α = 0 ↔ Subsingleton α
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma krullDim_pos_iff_of_orderBot [OrderBot α] :
    0 < krullDim α ↔ Nontrivial α := by
  rw [← not_subsingleton_iff_nontrivial, ← Order.krullDim_eq_zero_iff_of_orderBot,
    ← ne_eq, ← lt_or_lt_iff_ne, or_iff_right]
  simp [Order.krullDim_nonneg]
/-
**Order.krullDim_le_one_iff_forall_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_le_one_iff_forall_isMin [OrderTop α] : krullDim α <= 1 ↔ forall x
 : α, x != ⊤ -> IsMin x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma krullDim_le_one_iff_forall_isMin [OrderTop α] :
    krullDim α ≤ 1 ↔ ∀ x : α, x ≠ ⊤ → IsMin x := by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_right]
/-
**Order.krullDim_eq_zero_iff_of_orderTop** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_zero_iff_of_orderTop [OrderTop α] : krullDim α = 0 ↔ Subsingle
ton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `Order.krullDim_nonpos_iff_forall_isMin`：krullDim_nonpos_iff_forall_isMin
 : krullDim α <= 0 ↔ forall x : α, IsMin x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `Order.krullDim_eq_zero`：krullDim_eq_zero [Nonempty α] [Subsingleton α] :
 krullDim α = 0
· 使用定理 `top_nonempty`：∀ (α : Type u_1) [Top α], Nonempty α
-/
lemma krullDim_eq_zero_iff_of_orderTop [OrderTop α] :
    krullDim α = 0 ↔ Subsingleton α :=
  ⟨fun H ↦ subsingleton_of_forall_eq ⊤ fun _ ↦ top_le_iff.mp
    (krullDim_nonpos_iff_forall_isMin.mp H.le ⊤ le_top), fun _ ↦ Order.krullDim_eq_zero⟩
/-
**Order.krullDim_pos_iff_of_orderTop** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_pos_iff_of_orderTop [OrderTop α] : 0 < krullDim α ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用引理 `Order.krullDim_eq_zero_iff_of_orderTop`：krullDim_eq_zero_iff_of_orderTop
 [OrderTop α] : krullDim α = 0 ↔ Subsingleton α
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `top_nonempty`：∀ (α : Type u_1) [Top α], Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma krullDim_pos_iff_of_orderTop [OrderTop α] :
    0 < krullDim α ↔ Nontrivial α := by
  rw [← not_subsingleton_iff_nontrivial, ← Order.krullDim_eq_zero_iff_of_orderTop,
    ← ne_eq, ← lt_or_lt_iff_ne, or_iff_right]
  simp [Order.krullDim_nonneg]
/-
**Order.krullDim_le_one_iff_of_boundedOrder** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_le_one_iff_of_boundedOrder [BoundedOrder α] : krullDim α <= 1 ↔ f
orall x : α, x = ⊥ ∨ x = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma krullDim_le_one_iff_of_boundedOrder [BoundedOrder α] :
    krullDim α ≤ 1 ↔ ∀ x : α, x = ⊥ ∨ x = ⊤ := by
  simp [Order.krullDim_le_one_iff]

end PartialOrder

/-
**Order.krullDim_eq_length_of_finiteDimensionalOrder** 是 Mathlib 中的一个引理，位于命名空间 `
Order`。
形式化陈述：krullDim_eq_length_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : 
krullDim α = (LTSeries.longestOf α).length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用引理 `RelSeries.length_le_length_longestOf`：length_le_length_longestOf [r.Fini
teDimensional] (x : RelSeries r) : x.length <= (RelSeries.longestOf r).length
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma krullDim_eq_length_of_finiteDimensionalOrder [FiniteDimensionalOrder α] :
    krullDim α = (LTSeries.longestOf α).length :=
  le_antisymm
    (iSup_le <| fun _ ↦ WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <|
      RelSeries.length_le_length_longestOf _ _) <|
    le_iSup (fun (i : LTSeries _) ↦ (i.length : WithBot (WithTop ℕ))) <| LTSeries.longestOf _
/-
**Order.krullDim_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_top [InfiniteDimensionalOrder α] : krullDim α = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `ENat.WithBot.eq_top_iff_forall_ge`：eq_top_iff_forall_ge {n : WithBot Nat
∞} : n = ⊤ ↔ forall m : Nat, m <= n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LTSeries.length_withLength`：∀ (α : Type u_1) [inst : Preorder α] [inst_1
 : InfiniteDimensionalOrder α] (n : ℕ), (LTSeries.withLength α n).length = n
-/
lemma krullDim_eq_top [InfiniteDimensionalOrder α] :
    krullDim α = ⊤ :=
  le_antisymm le_top <| le_iSup_iff.mpr <| fun m hm ↦ match m, hm with
  | ⊥, hm => False.elim <| by
    have : Inhabited α := ⟨LTSeries.withLength _ 0 0⟩
    exact not_le_of_gt (WithBot.bot_lt_coe _ : ⊥ < (0 : WithBot (WithTop ℕ))) <| hm default
  | ⊤, _ => le_refl _
  | m, hm => by
    rw [top_le_iff, ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    simpa using hm (LTSeries.withLength _ n)
/-
**Order.krullDim_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_top_iff : krullDim α = ⊤ ↔ InfiniteDimensionalOrder α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_bot`：krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `finiteDimensionalOrder_or_infiniteDimensionalOrder`：finiteDimensionalOrd
er_or_infiniteDimensionalOrder [Preorder α] [Nonempty α] : FiniteDimensionalOrde
r α ∨ InfiniteDimensionalOrder α
· 使用引理 `Order.krullDim_eq_length_of_finiteDimensionalOrder`：krullDim_eq_length_o
f_finiteDimensionalOrder [FiniteDimensionalOrder α] : krullDim α = (LTSeries.lon
gestOf α).length
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Order.krullDim_eq_top`：krullDim_eq_top [InfiniteDimensionalOrder α] : kr
ullDim α = ⊤
-/
lemma krullDim_eq_top_iff : krullDim α = ⊤ ↔ InfiniteDimensionalOrder α := by
  refine ⟨fun h ↦ ?_, fun _ ↦ krullDim_eq_top⟩
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot] at h
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder] at h
    cases h
  · infer_instance
/-
**Order.le_krullDim_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：le_krullDim_iff {n : Nat} : n <= krullDim α ↔ exists l : LTSeries α, l.len
gth = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_bot`：krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥
· 使用定理 `RelSeries.instIsEmpty`：∀ {α : Type u_1} (r : SetRel α α) [IsEmpty α], Is
Empty (RelSeries r)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `finiteDimensionalOrder_or_infiniteDimensionalOrder`：finiteDimensionalOrd
er_or_infiniteDimensionalOrder [Preorder α] [Nonempty α] : FiniteDimensionalOrde
r α ∨ InfiniteDimensionalOrder α
· 使用引理 `Order.krullDim_eq_length_of_finiteDimensionalOrder`：krullDim_eq_length_o
f_finiteDimensionalOrder [FiniteDimensionalOrder α] : krullDim α = (LTSeries.lon
gestOf α).length
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用引理 `LTSeries.longestOf_is_longest`：longestOf_is_longest [FiniteDimensionalOr
der α] (x : LTSeries α) : x.length <= (LTSeries.longestOf α).length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Order.krullDim_eq_top`：krullDim_eq_top [InfiniteDimensionalOrder α] : kr
ullDim α = ⊤
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `SetRel.InfiniteDimensional.exists_relSeries_with_length`：∀ {α : Type u_1
} {r : SetRel α α} [self : r.InfiniteDimensional] (n : ℕ), ∃ x, x.length = n
-/
lemma le_krullDim_iff {n : ℕ} : n ≤ krullDim α ↔ ∃ l : LTSeries α, l.length = n := by
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot]
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder, Nat.cast_le]
    constructor
    · exact fun H ↦ ⟨(LTSeries.longestOf α).take ⟨_, Nat.lt_succ_of_le H⟩, rfl⟩
    · exact fun ⟨l, hl⟩ ↦ hl ▸ l.longestOf_is_longest
  · simpa [krullDim_eq_top] using SetRel.InfiniteDimensional.exists_relSeries_with_length n

/-- A definition of krullDim for nonempty `α` that avoids `WithBot` -/
/-
**Order.krullDim_eq_iSup_length** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_iSup_length [Nonempty α] : krullDim α = ⨆ (p : LTSeries α), (p
.length : Nat∞)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.coe_iSup`：WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι -> α} 
(hf : BddAbove (range f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithBot α)
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s
· 使用定理 `RelSeries.instNonempty`：∀ {α : Type u_1} (r : SetRel α α) [Nonempty α], 
Nonempty (RelSeries r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A definition of krullDim for nonempty `α` that avoids `WithBot`
-/
lemma krullDim_eq_iSup_length [Nonempty α] :
    krullDim α = ⨆ (p : LTSeries α), (p.length : ℕ∞) := by
  simp [krullDim, WithBot.coe_iSup (OrderTop.bddAbove _), WithBot.coe_natCast]
/-
**Order.krullDim_lt_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_lt_coe_iff {n : Nat} : krullDim α < n ↔ forall l : LTSeries α, l.
length < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.krullDim.eq_1`：∀ (α : Type u_1) [inst : Preorder α], Order.krullDi
m α = ⨆ p, ↑p.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ),
 ↑↑n = ↑n
· 使用定理 `ENat.natCast_zero`：natCast_zero : ((0 : Nat) : Nat∞) = 0
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `WithBot.lt_coe_bot`：lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma krullDim_lt_coe_iff {n : ℕ} : krullDim α < n ↔ ∀ l : LTSeries α, l.length < n := by
  rw [krullDim, ← WithBot.coe_natCast]
  rcases n with - | n
  · rw [ENat.natCast_zero, ← bot_eq_zero, WithBot.lt_coe_bot]
    simp
  · simp [ENat.WithBot.lt_add_one_iff, WithBot.coe_natCast]
/-
**Order.krullDim_le_of_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_le_of_strictMono (f : α -> β) (hf : StrictMono f) : krullDim α <=
 krullDim β
参数：f : α -> β；hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
lemma krullDim_le_of_strictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β :=
  iSup_le fun p ↦ le_sSup ⟨p.map f hf, rfl⟩
/-
**Order.krullDim_le_of_strictComono_and_surj** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_le_of_strictComono_and_surj (f : α -> β) (hf : forall ⦃a b⦄, f a 
< f b -> a < b) (hf' : Function.Surjective f) : krullDim β <= krullDim α
参数：f : α -> β；hf : forall ⦃a b⦄, f a < f b -> a < b；hf' : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
lemma krullDim_le_of_strictComono_and_surj
    (f : α → β) (hf : ∀ ⦃a b⦄, f a < f b → a < b) (hf' : Function.Surjective f) :
    krullDim β ≤ krullDim α :=
  iSup_le fun p ↦ le_sSup ⟨p.comap _ hf hf', rfl⟩
/-
**Order.krullDim_eq_of_orderIso** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_of_orderIso (f : α ≃o β) : krullDim α = krullDim β
参数：f : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Order.krullDim_le_of_strictMono`：krullDim_le_of_strictMono (f : α -> β) 
(hf : StrictMono f) : krullDim α <= krullDim β
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
lemma krullDim_eq_of_orderIso (f : α ≃o β) : krullDim α = krullDim β :=
  le_antisymm (krullDim_le_of_strictMono _ f.strictMono) <|
    krullDim_le_of_strictMono _ f.symm.strictMono
/-
**Order.krullDim_orderDual** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α], Order.krullDim αᵒᵈ = Order.krullDim 
α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
@[simp] lemma krullDim_orderDual : krullDim αᵒᵈ = krullDim α :=
  le_antisymm (iSup_le fun i ↦ le_sSup ⟨i.reverse, rfl⟩) <|
    iSup_le fun i ↦ le_sSup ⟨i.reverse, rfl⟩
/-
**Order.height_le_krullDim** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_le_krullDim (a : α) : height a <= krullDim α
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_iSup_length`：krullDim_eq_iSup_length [Nonempty α] : kr
ullDim α = ⨆ (p : LTSeries α), (p.length : Nat∞)
· 使用引理 `Order.height_le`：height_le {a : α} {n : Nat∞} (h : forall (p : LTSeries 
α), p.last = a -> p.length <= n) : height a <= n
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma height_le_krullDim (a : α) : height a ≤ krullDim α := by
  have : Nonempty α := ⟨a⟩
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_le_coe]
  exact height_le fun p _ ↦ le_iSup_of_le p le_rfl
/-
**Order.coheight_le_krullDim** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_le_krullDim (a : α) : coheight a <= krullDim α
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.krullDim_orderDual`：∀ {α : Type u_1} [inst : Preorder α], Order.kr
ullDim αᵒᵈ = Order.krullDim α
· 使用引理 `Order.height_le_krullDim`：height_le_krullDim (a : α) : height a <= krull
Dim α
-/
lemma coheight_le_krullDim (a : α) : coheight a ≤ krullDim α := by
  simpa using! height_le_krullDim (α := αᵒᵈ) a

@[simp]
/-
**Order._root_.LTSeries.height_last_longestOf** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LTSeries.height_last_longestOf [FiniteDimensionalOrder α] :
    height (LTSeries.longestOf α).last = krullDim α := by
  refine le_antisymm (height_le_krullDim _) ?_
  rw [krullDim_eq_length_of_finiteDimensionalOrder, height]
  norm_cast
  exact le_iSup_iff.mpr <| fun _ h ↦ iSup_le_iff.mp (h _) le_rfl

/--
The Krull dimension is the supremum of the elements' heights.

This version of the lemma assumes that `α` is nonempty. In this case, the coercion from `ℕ∞` to
`WithBot ℕ∞` is on the outside of the right-hand side, which is usually more convenient.

If `α` were empty, then `krullDim α = ⊥`. See `krullDim_eq_iSup_height` for the more general
version, with the coercion under the supremum.
-/
/-
**Order.krullDim_eq_iSup_height_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_iSup_height_of_nonempty [Nonempty α] : krullDim α = ↑(⨆ (a : α
), height a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `Order.length_le_height_last`：length_le_height_last {p : LTSeries α} : p.
length <= height p.last
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.unbotD_le_iff`：unbotD_le_iff (hx : x = ⊥ -> a <= b) : x.unbotD a
 <= b ↔ x <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.coe_iSup`：WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι -> α} 
(hf : BddAbove (range f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithBot α)
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s
· 使用引理 `Order.height_le_krullDim`：height_le_krullDim (a : α) : height a <= krull
Dim α

--- 原说明 ---
The Krull dimension is the supremum of the elements' heights.

This version of the lemma assumes that `α` is nonempty. In this case, the coerci
on from `ℕ∞` to
`WithBot ℕ∞` is on the outside of the right-hand side, which is usually more con
venient.

If `α` were empty, then `krullDim α = ⊥`. See `krullDim_eq_iSup_height` for the 
more general
version, with the coercion under the supremum.
-/
lemma krullDim_eq_iSup_height_of_nonempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), height a) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    suffices p.length ≤ ⨆ (a : α), height a from (WithBot.unbotD_le_iff fun _ => this).mp this
    apply le_iSup_of_le p.last (length_le_height_last (p := p))
  · rw [WithBot.coe_iSup (by bddDefault)]
    apply iSup_le
    apply height_le_krullDim

/--
The Krull dimension is the supremum of the elements' coheights.

This version of the lemma assumes that `α` is nonempty. In this case, the coercion from `ℕ∞` to
`WithBot ℕ∞` is on the outside of the right-hand side, which is usually more convenient.

If `α` were empty, then `krullDim α = ⊥`. See `krullDim_eq_iSup_coheight` for the more general
version, with the coercion under the supremum.
-/
/-
**Order.krullDim_eq_iSup_coheight_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_iSup_coheight_of_nonempty [Nonempty α] : krullDim α = ↑(⨆ (a :
 α), coheight a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.krullDim_orderDual`：∀ {α : Type u_1} [inst : Preorder α], Order.kr
ullDim αᵒᵈ = Order.krullDim α
· 使用引理 `Order.krullDim_eq_iSup_height_of_nonempty`：krullDim_eq_iSup_height_of_no
nempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), height a)
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ

--- 原说明 ---
The Krull dimension is the supremum of the elements' coheights.

This version of the lemma assumes that `α` is nonempty. In this case, the coerci
on from `ℕ∞` to
`WithBot ℕ∞` is on the outside of the right-hand side, which is usually more con
venient.

If `α` were empty, then `krullDim α = ⊥`. See `krullDim_eq_iSup_coheight` for th
e more general
version, with the coercion under the supremum.
-/
lemma krullDim_eq_iSup_coheight_of_nonempty [Nonempty α] :
    krullDim α = ↑(⨆ (a : α), coheight a) := by
  simpa using! krullDim_eq_iSup_height_of_nonempty (α := αᵒᵈ)

/--
The Krull dimension is the supremum of the elements' height plus coheight.
-/
/-
**Order.krullDim_eq_iSup_height_add_coheight_of_nonempty** 是 Mathlib 中的一个引理，位于命名
空间 `Order`。
形式化陈述：krullDim_eq_iSup_height_add_coheight_of_nonempty [Nonempty α] : krullDim α
 = ↑(⨆ (a : α), height a + coheight a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_iSup_height_of_nonempty`：krullDim_eq_iSup_height_of_no
nempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), height a)
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `ciSup_mono`：ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : fora
ll x, f x <= g x) : iSup f <= iSup g
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `Order.krullDim_eq_iSup_length`：krullDim_eq_iSup_length [Nonempty α] : kr
ullDim α = ⨆ (p : LTSeries α), (p.length : Nat∞)
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Order.height_le_krullDim`：height_le_krullDim (a : α) : height a <= krull
Dim α
· 使用引理 `Order.coheight_le_krullDim`：coheight_le_krullDim (a : α) : coheight a <=
 krullDim α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.exists_series_of_height_eq_coe`：exists_series_of_height_eq_coe (a 
: α) {n : Nat} (h : height a = n) : exists p : LTSeries α, p.last = a ∧ p.length
 = n
· 使用引理 `Order.exists_series_of_coheight_eq_coe`：exists_series_of_coheight_eq_coe
 (a : α) {n : Nat} (h : coheight a = n) : exists p : LTSeries α, p.head = a ∧ p.
length = n
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RelSeries.smash_length`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSeri
es r) (connect : p.last = q.head),   (p.smash q connect).length = p.length + q.l
ength
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n

--- 原说明 ---
The Krull dimension is the supremum of the elements' height plus coheight.
-/
lemma krullDim_eq_iSup_height_add_coheight_of_nonempty [Nonempty α] :
    krullDim α = ↑(⨆ (a : α), height a + coheight a) := by
  apply le_antisymm
  · rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_le_coe]
    apply ciSup_mono (by bddDefault) (by simp)
  · wlog hnottop : krullDim α < ⊤
    · simp_all
    rw [krullDim_eq_iSup_length, WithBot.coe_le_coe]
    apply iSup_le
    intro a
    have : height a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (height_le_krullDim a) hnottop)
    have : coheight a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (coheight_le_krullDim a) hnottop)
    cases hh : height a with
    | top => simp_all
    | coe n =>
      cases hch : coheight a with
      | top => simp_all
      | coe m =>
        obtain ⟨p₁, hlast, hlen₁⟩ := exists_series_of_height_eq_coe a hh
        obtain ⟨p₂, hhead, hlen₂⟩ := exists_series_of_coheight_eq_coe a hch
        apply le_iSup_of_le ((p₁.smash p₂) (by simp [*])) (by simp [*])

/--
The Krull dimension is the supremum of the elements' heights.

If `α` is `Nonempty`, then `krullDim_eq_iSup_height_of_nonempty`, with the coercion from
`ℕ∞` to `WithBot ℕ∞` outside the supremum, can be more convenient.
-/
/-
**Order.krullDim_eq_iSup_height** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_iSup_height : krullDim α = ⨆ (a : α), ↑(height a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_bot`：krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用引理 `Order.krullDim_eq_iSup_height_of_nonempty`：krullDim_eq_iSup_height_of_no
nempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), height a)
· 使用定理 `WithBot.coe_iSup`：WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι -> α} 
(hf : BddAbove (range f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithBot α)
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s

--- 原说明 ---
The Krull dimension is the supremum of the elements' heights.

If `α` is `Nonempty`, then `krullDim_eq_iSup_height_of_nonempty`, with the coerc
ion from
`ℕ∞` to `WithBot ℕ∞` outside the supremum, can be more convenient.
-/
lemma krullDim_eq_iSup_height : krullDim α = ⨆ (a : α), ↑(height a) := by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

/--
The Krull dimension is the supremum of the elements' coheights.

If `α` is `Nonempty`, then `krullDim_eq_iSup_coheight_of_nonempty`, with the coercion from
`ℕ∞` to `WithBot ℕ∞` outside the supremum, can be more convenient.
-/
/-
**Order.krullDim_eq_iSup_coheight** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_iSup_coheight : krullDim α = ⨆ (a : α), ↑(coheight a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_bot`：krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用引理 `Order.krullDim_eq_iSup_coheight_of_nonempty`：krullDim_eq_iSup_coheight_o
f_nonempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), coheight a)
· 使用定理 `WithBot.coe_iSup`：WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι -> α} 
(hf : BddAbove (range f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithBot α)
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s

--- 原说明 ---
The Krull dimension is the supremum of the elements' coheights.

If `α` is `Nonempty`, then `krullDim_eq_iSup_coheight_of_nonempty`, with the coe
rcion from
`ℕ∞` to `WithBot ℕ∞` outside the supremum, can be more convenient.
-/
lemma krullDim_eq_iSup_coheight : krullDim α = ⨆ (a : α), ↑(coheight a) := by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_coheight_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left
/-
**Order.height_top_eq_krullDim** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_top_eq_krullDim [OrderTop α] : height (⊤ : α) = krullDim α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_iSup_length`：krullDim_eq_iSup_length [Nonempty α] : kr
ullDim α = ⨆ (p : LTSeries α), (p.length : Nat∞)
· 使用定理 `top_nonempty`：∀ (α : Type u_1) [Top α], Nonempty α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Order.height_le`：height_le {a : α} {n : Nat∞} (h : forall (p : LTSeries 
α), p.last = a -> p.length <= n) : height a <= n
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `Order.length_le_height`：length_le_height {p : LTSeries α} {x : α} (hlast
 : p.last <= x) : p.length <= height x
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma height_top_eq_krullDim [OrderTop α] : height (⊤ : α) = krullDim α := by
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_inj]
  apply le_antisymm
  · exact height_le fun p _ ↦ le_iSup_of_le p le_rfl
  · exact iSup_le fun _ => length_le_height le_top

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left
/-
**Order.coheight_bot_eq_krullDim** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_bot_eq_krullDim [OrderBot α] : coheight (⊥ : α) = krullDim α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.krullDim_orderDual`：∀ {α : Type u_1} [inst : Preorder α], Order.kr
ullDim αᵒᵈ = Order.krullDim α
· 使用引理 `Order.height_top_eq_krullDim`：height_top_eq_krullDim [OrderTop α] : heig
ht (⊤ : α) = krullDim α
-/
lemma coheight_bot_eq_krullDim [OrderBot α] : coheight (⊥ : α) = krullDim α := by
  rw [← krullDim_orderDual]
  exact height_top_eq_krullDim (α := αᵒᵈ)
/-
**Order.height_eq_krullDim_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_eq_krullDim_Iic (x : α) : (height x : Nat∞) = krullDim (Set.Iic x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.height_top_eq_krullDim`：height_top_eq_krullDim [OrderTop α] : heig
ht (⊤ : α) = krullDim α
· 使用定理 `Order.height.eq_1`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Order.h
eight a = ⨆ p, ⨆ (_ : RelSeries.last p ≤ a), ↑p.length
· 使用定理 `WithBot.coe_inj`：coe_inj : (a : WithBot α) = b ↔ a = b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `LTSeries.monotone`：monotone (x : LTSeries α) : Monotone x
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用引理 `LTSeries.strictMono`：strictMono (x : LTSeries α) : StrictMono x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `LTSeries.map_length`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] (p : LTSeries α) (f : α → β)   (hf : StrictMono f), (p.ma
p f hf).l…
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma height_eq_krullDim_Iic (x : α) : (height x : ℕ∞) = krullDim (Set.Iic x) := by
  rw [← height_top_eq_krullDim, height, height, WithBot.coe_inj]
  apply le_antisymm
  · apply iSup_le; intro p; apply iSup_le; intro hp
    let q := LTSeries.mk p.length (fun i ↦ (⟨p.toFun i, le_trans (p.monotone (Fin.le_last _)) hp⟩
     : Set.Iic x)) (fun _ _ h ↦ p.strictMono h)
    simp only [le_top, iSup_pos, ge_iff_le]
    exact le_iSup (fun p ↦ (p.length : ℕ∞)) q
  · apply iSup_le; intro p; apply iSup_le; intro _
    have mono : StrictMono (fun (y : Set.Iic x) ↦ y.1) := fun _ _ h ↦ h
    rw [← LTSeries.map_length p (fun x ↦ x.1) mono, ]
    refine le_iSup₂ (f := fun p hp ↦ (p.length : ℕ∞)) (p.map (fun x ↦ x.1) mono) ?_
    exact (p.toFun (Fin.last p.length)).2
/-
**Order.coheight_eq_krullDim_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_eq_krullDim_Ici {α : Type*} [Preorder α] (x : α) : (coheight x : 
Nat∞) = krullDim (Set.Ici x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.coheight.eq_1`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Order
.coheight a = Order.height a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.krullDim_orderDual`：∀ {α : Type u_1} [inst : Preorder α], Order.kr
ullDim αᵒᵈ = Order.krullDim α
· 使用引理 `Order.krullDim_eq_of_orderIso`：krullDim_eq_of_orderIso (f : α ≃o β) : kr
ullDim α = krullDim β
· 使用引理 `Order.height_eq_krullDim_Iic`：height_eq_krullDim_Iic (x : α) : (height x
 : Nat∞) = krullDim (Set.Iic x)
-/
lemma coheight_eq_krullDim_Ici {α : Type*} [Preorder α] (x : α) :
    (coheight x : ℕ∞) = krullDim (Set.Ici x) := by
  rw [coheight, ← krullDim_orderDual, Order.krullDim_eq_of_orderIso (OrderIso.refl _)]
  exact height_eq_krullDim_Iic _

end krullDim

section finiteDimensional

variable {α : Type*} [Preorder α]

/-
**Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top** 是 Mathlib 中的一个引理，位于
命名空间 `Order`。
形式化陈述：finiteDimensionalOrder_iff_krullDim_ne_bot_and_top : FiniteDimensionalOrde
r α ↔ krullDim α != ⊥ ∧ krullDim α != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `LTSeries.nonempty_of_finiteDimensionalOrder`：nonempty_of_finiteDimension
alOrder [FiniteDimensionalOrder α] : Nonempty α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.krullDim_eq_bot_iff`：krullDim_eq_bot_iff : krullDim α = ⊥ ↔ IsEmpt
y α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
-/
lemma finiteDimensionalOrder_iff_krullDim_ne_bot_and_top :
    FiniteDimensionalOrder α ↔ krullDim α ≠ ⊥ ∧ krullDim α ≠ ⊤ := by
  by_cases h : Nonempty α
  · simp [← not_infiniteDimensionalOrder_iff, ← krullDim_eq_top_iff]
  · constructor
    · exact (fun h1 ↦ False.elim (h (LTSeries.nonempty_of_finiteDimensionalOrder α)))
    · exact (fun h1 ↦ False.elim (h1.1 (krullDim_eq_bot_iff.mpr (not_nonempty_iff.mp h))))
/-
**Order.krullDim_ne_bot_of_finiteDimensionalOrder** 是 Mathlib 中的一个引理，位于命名空间 `Ord
er`。
形式化陈述：krullDim_ne_bot_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : kru
llDim α != ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top`：finiteDimensio
nalOrder_iff_krullDim_ne_bot_and_top : FiniteDimensionalOrder α ↔ krullDim α != 
⊥ ∧ krullDim α != ⊤
-/
lemma krullDim_ne_bot_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : krullDim α ≠ ⊥ :=
  (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).1
/-
**Order.krullDim_ne_top_of_finiteDimensionalOrder** 是 Mathlib 中的一个引理，位于命名空间 `Ord
er`。
形式化陈述：krullDim_ne_top_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : kru
llDim α != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top`：finiteDimensio
nalOrder_iff_krullDim_ne_bot_and_top : FiniteDimensionalOrder α ↔ krullDim α != 
⊥ ∧ krullDim α != ⊤
-/
lemma krullDim_ne_top_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : krullDim α ≠ ⊤ :=
  (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).2
/-
**Order.coheight_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_lt_top [FiniteDimensionalOrder α] (x : α) : coheight x < ⊤
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Order.coheight_le_krullDim`：coheight_le_krullDim (a : α) : coheight a <=
 krullDim α
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用引理 `Order.krullDim_ne_top_of_finiteDimensionalOrder`：krullDim_ne_top_of_fini
teDimensionalOrder [FiniteDimensionalOrder α] : krullDim α != ⊤
-/
lemma coheight_lt_top [FiniteDimensionalOrder α] (x : α) : coheight x < ⊤ := by
  rw [← WithBot.coe_lt_coe]
  apply lt_of_le_of_lt (coheight_le_krullDim x)
  simpa using krullDim_ne_top_of_finiteDimensionalOrder.lt_top

end finiteDimensional

section typeclass

/-- Typeclass for orders with krull dimension at most `n`. -/
@[mk_iff]
/-
**Order.KrullDimLE** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order`。
形式化陈述：ℕ → (α : Type u_1) → [Preorder α] → Prop
参数：α : Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for orders with krull dimension at most `n`.
-/
class KrullDimLE (n : ℕ) (α : Type*) [Preorder α] : Prop where
  krullDim_le : krullDim α ≤ n
/-
**Order.KrullDimLE.mono** 是 Mathlib 中的一个定理，位于命名空间 `Order.KrullDimLE`。
形式化陈述：∀ {n m : ℕ}, n ≤ m → ∀ (α : Type u_1) [inst : Preorder α] [Order.KrullDimL
E n α], Order.KrullDimLE m α
参数：α : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.KrullDimLE.krullDim_le`：∀ {n : ℕ} {α : Type u_1} {inst : Preorder 
α} [self : Order.KrullDimLE n α], Order.krullDim α ≤ ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma KrullDimLE.mono {n m : ℕ} (e : n ≤ m) (α : Type*) [Preorder α] [KrullDimLE n α] :
    KrullDimLE m α :=
  ⟨KrullDimLE.krullDim_le (n := n).trans (Nat.cast_le.mpr e)⟩
/-
**Order.** 是 Mathlib 中的一个实例，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [Preorder α] [Subsingleton α] : KrullDimLE 0 α := ⟨krullDim_nonpos_of_subsingleton⟩

end typeclass

/-!
## Concrete calculations
-/

section calculations

/-
**Order.krullDim_eq_one_iff_of_boundedOrder** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_eq_one_iff_of_boundedOrder {α : Type*} [PartialOrder α] [BoundedO
rder α] : krullDim α = 1 ↔ IsSimpleOrder α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用引理 `Order.krullDim_le_one_iff_of_boundedOrder`：krullDim_le_one_iff_of_bounde
dOrder [BoundedOrder α] : krullDim α <= 1 ↔ forall x : α, x = ⊥ ∨ x = ⊤
· 使用引理 `WithBot.one_le_iff_pos`：one_le_iff_pos {α : Type*} [PartialOrder α] [Add
MonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)] [SuccAddOrder α] (a : WithB
ot α) : 1 <=…
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用引理 `Order.krullDim_pos_iff_of_orderBot`：krullDim_pos_iff_of_orderBot [OrderB
ot α] : 0 < krullDim α ↔ Nontrivial α
· 使用定理 `isSimpleOrder_iff`：∀ (α : Type u_4) [inst : LE α] [inst_1 : BoundedOrder
 α], IsSimpleOrder α ↔ Nontrivial α ∧ ∀ (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma krullDim_eq_one_iff_of_boundedOrder {α : Type*} [PartialOrder α] [BoundedOrder α] :
    krullDim α = 1 ↔ IsSimpleOrder α := by
  rw [le_antisymm_iff, krullDim_le_one_iff_of_boundedOrder, WithBot.one_le_iff_pos,
    Order.krullDim_pos_iff_of_orderBot, isSimpleOrder_iff, and_comm]
/-
**Order.krullDim_of_isSimpleOrder** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : BoundedOrder α] [IsSimp
leOrder α], Order.krullDim α = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.krullDim_eq_one_iff_of_boundedOrder`：krullDim_eq_one_iff_of_bounde
dOrder {α : Type*} [PartialOrder α] [BoundedOrder α] : krullDim α = 1 ↔ IsSimple
Order α
-/
@[simp] lemma krullDim_of_isSimpleOrder {α : Type*} [PartialOrder α] [BoundedOrder α]
    [IsSimpleOrder α] : krullDim α = 1 :=
  krullDim_eq_one_iff_of_boundedOrder.mpr ‹_›

variable {α : Type*} [Preorder α]

/-
These two lemmas could possibly be used to simplify the subsequent calculations,
especially once the `Set.encard` api is richer.

(Commented out to avoid importing modules purely for `proof_wanted`.)
proof_wanted height_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  height a = (Set.Iio a).encard

proof_wanted coheight_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  coheight a = (Set.Ioi a).encard
-/

/-
**Order.height_nat** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ (n : ℕ), Order.height n = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.height_le_coe_iff`：height_le_coe_iff {x : α} {n : Nat} : height x 
<= n ↔ forall y < x, height y < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Order.length_le_height_last`：length_le_height_last {p : LTSeries α} : p.
length <= height p.last

--- 原说明 ---
These two lemmas could possibly be used to simplify the subsequent calculations,
especially once the `Set.encard` api is richer.

(Commented out to avoid importing modules purely for `proof_wanted`.)
proof_wanted height_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  height a = (Set.Iio a).encard

proof_wanted coheight_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  coheight a = (Set.Ioi a).encard
-/
@[simp] lemma height_nat (n : ℕ) : height n = n := by
  induction n using Nat.strongRecOn with | ind n ih =>
  apply le_antisymm
  · apply height_le_coe_iff.mpr
    simp +contextual only [ih, Nat.cast_lt, implies_true]
  · exact length_le_height_last (p := LTSeries.range n)
/-
**Order.coheight_of_noMaxOrder** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), Order.coheigh
t a = ⊤
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_strictMono`：exists_strictMono [Nonempty α] [NoMaxOrder α] : e
xists f : Nat -> α, StrictMono f
· 使用定理 `Set.nonempty_Ioi_subtype`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [
NoMaxOrder α], Nonempty ↑(Set.Ioi a)
· 使用定理 `Set.instNoMaxOrderElemIoi`：∀ {α : Type u_1} [inst : Preorder α] {a : α} 
[NoMaxOrder α], NoMaxOrder ↑(Set.Ioi a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.coheight_eq_top_iff`：coheight_eq_top_iff {x : α} : coheight x = ⊤ 
↔ forall n, exists p : LTSeries α, p.head = x ∧ p.length = n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coheight_of_noMaxOrder [NoMaxOrder α] (a : α) : coheight a = ⊤ := by
  obtain ⟨f, hstrictmono⟩ := Nat.exists_strictMono ↑(Set.Ioi a)
  apply coheight_eq_top_iff.mpr
  intro m
  use { length := m, toFun := fun i => if i = 0 then a else f i, step := ?step }
  case h => simp [RelSeries.head]
  case step =>
    intro ⟨i, hi⟩
    by_cases hzero : i = 0
    · subst i
      exact (f 1).prop
    · suffices f i < f (i + 1) by simp [Fin.ext_iff, hzero, this]
      apply hstrictmono
      lia
/-
**Order.height_of_noMinOrder** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [NoMinOrder α] (a : α), Order.height 
a = ⊤
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.coheight_of_noMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMa
xOrder α] (a : α), Order.coheight a = ⊤
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
@[simp] lemma height_of_noMinOrder [NoMinOrder α] (a : α) : height a = ⊤ :=
  -- Implementation note: Here it's a bit easier to define the coheight variant first
  coheight_of_noMaxOrder (α := αᵒᵈ) a
/-
**Order.krullDim_of_noMaxOrder** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Nonempty α] [NoMaxOrder α], Order.kr
ullDim α = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_iSup_coheight`：krullDim_eq_iSup_coheight : krullDim α 
= ⨆ (a : α), ↑(coheight a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Order.coheight_of_noMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMa
xOrder α] (a : α), Order.coheight a = ⊤
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma krullDim_of_noMaxOrder [Nonempty α] [NoMaxOrder α] : krullDim α = ⊤ := by
  simp [krullDim_eq_iSup_coheight, coheight_of_noMaxOrder]
/-
**Order.krullDim_of_noMinOrder** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Nonempty α] [NoMinOrder α], Order.kr
ullDim α = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_iSup_height`：krullDim_eq_iSup_height : krullDim α = ⨆ 
(a : α), ↑(height a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Order.height_of_noMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α] (a : α), Order.height a = ⊤
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma krullDim_of_noMinOrder [Nonempty α] [NoMinOrder α] : krullDim α = ⊤ := by
  simp [krullDim_eq_iSup_height, height_of_noMinOrder]
/-
**Order.coheight_nat** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_nat (n : Nat) : coheight n = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.coheight_of_noMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMa
xOrder α] (a : α), Order.coheight a = ⊤
-/
lemma coheight_nat (n : ℕ) : coheight n = ⊤ := coheight_of_noMaxOrder ..
/-
**Order.krullDim_nat** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_nat : krullDim Nat = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.krullDim_of_noMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [None
mpty α] [NoMaxOrder α], Order.krullDim α = ⊤
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma krullDim_nat : krullDim ℕ = ⊤ := krullDim_of_noMaxOrder ..
/-
**Order.height_int** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_int (n : Int) : height n = ⊤
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.height_of_noMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α] (a : α), Order.height a = ⊤
· 使用定理 `LinearOrderedAddCommGroup.to_noMinOrder`：∀ {α : Type u} [inst : AddCommG
roup α] [inst_1 : LinearOrder α] [IsOrderedAddMonoid α] [Nontrivial α], NoMinOrd
er α
-/
lemma height_int (n : ℤ) : height n = ⊤ := height_of_noMinOrder ..
/-
**Order.coheight_int** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_int (n : Int) : coheight n = ⊤
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.coheight_of_noMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMa
xOrder α] (a : α), Order.coheight a = ⊤
· 使用定理 `LinearOrderedAddCommGroup.to_noMaxOrder`：∀ {α : Type u} [inst : AddCommG
roup α] [inst_1 : LinearOrder α] [IsOrderedAddMonoid α] [Nontrivial α], NoMaxOrd
er α
-/
lemma coheight_int (n : ℤ) : coheight n = ⊤ := coheight_of_noMaxOrder ..
/-
**Order.krullDim_int** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_int : krullDim Int = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.krullDim_of_noMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [None
mpty α] [NoMaxOrder α], Order.krullDim α = ⊤
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LinearOrderedAddCommGroup.to_noMaxOrder`：∀ {α : Type u} [inst : AddCommG
roup α] [inst_1 : LinearOrder α] [IsOrderedAddMonoid α] [Nontrivial α], NoMaxOrd
er α
-/
lemma krullDim_int : krullDim ℤ = ⊤ := krullDim_of_noMaxOrder ..

set_option backward.isDefEq.respectTransparency false in
/-
**Order.height_coe_withBot** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (x : α), Order.height ↑x = Order.heig
ht x + 1
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Order.height_le`：height_le {a : α} {n : Nat∞} (h : forall (p : LTSeries 
α), p.last = a -> p.length <= n) : height a <= n
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用引理 `LTSeries.strictMono`：strictMono (x : LTSeries α) : StrictMono x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `compare_gt_iff_gt`：compare_gt_iff_gt : compare a b = .gt ↔ b < a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.length_le_height_last`：length_le_height_last {p : LTSeries α} : p.
length <= height p.last
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `_private.Mathlib.Order.KrullDimension.0.Order.height_add_const`：∀ {α : T
ype u_1} [inst : Preorder α] (a : α) (n : ℕ∞),   Order.height a + n = ⨆ p, ⨆ (_ 
: RelSeries.last p = a), ↑p.length + n
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `WithBot.coe_strictMono`：coe_strictMono : StrictMono (fun (a : α) => (a :
 WithBot α))
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `RelSeries.last_cons`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newHead : α) (rel : (newHead, p.head) ∈ r),   (p.cons newHead rel).last = p.la
st
· 使用定理 `RelSeries.cons_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newHead : α) (rel : (newHead, p.head) ∈ r),   (p.cons newHead rel).length = 
p.length + …
· 使用定理 `LTSeries.map_length`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] (p : LTSeries α) (f : α → β)   (hf : StrictMono f), (p.ma
p f hf).l…
（共 31 条，此处仅展示前 30 条）
-/
@[simp] lemma height_coe_withBot (x : α) : height (x : WithBot α) = height x + 1 := by
  apply le_antisymm
  · apply height_le
    intro p hlast
    wlog hlenpos : p.length ≠ 0
    · simp_all
    -- essentially p' := (p.drop 1).map unbot
    let p' : LTSeries α := {
      length := p.length - 1
      toFun := fun ⟨i, hi⟩ => (p ⟨i+1, by lia⟩).unbot (by
        apply ne_bot_of_gt (b := p.head)
        apply p.strictMono
        exact compare_gt_iff_gt.mp rfl)
      step := fun i => by simpa [WithBot.unbot_lt_iff] using! p.step ⟨i + 1, by lia⟩ }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithBot.unbot_eq_iff, ← hlast, Fin.last]
      congr
      lia
    suffices p'.length ≤ height p'.last by
      simpa [p', hlast'] using! this
    apply length_le_height_last
  · rw [height_add_const]
    apply iSup₂_le
    intro p hlast
    let p' := (p.map _ WithBot.coe_strictMono).cons ⊥ (by simp)
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])
/-
**Order.coheight_coe_withTop** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (x : α), Order.coheight ↑x = Order.co
height x + 1
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.height_coe_withBot`：∀ {α : Type u_1} [inst : Preorder α] (x : α), 
Order.height ↑x = Order.height x + 1
-/
@[simp] lemma coheight_coe_withTop (x : α) : coheight (x : WithTop α) = coheight x + 1 :=
  height_coe_withBot (α := αᵒᵈ) x
/-
**Order.height_coe_withTop** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (x : α), Order.height ↑x = Order.heig
ht x
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Order.height_le`：height_le {a : α} {n : Nat∞} (h : forall (p : LTSeries 
α), p.last = a -> p.length <= n) : height a <= n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.lt_top_iff_ne_top`：∀ {α : Type u_1} [inst : LT α] {x : WithTop α
}, x < ⊤ ↔ x ≠ ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `LTSeries.monotone`：monotone (x : LTSeries α) : Monotone x
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.last.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (x : RelSeries r)
, x.last = x.toFun (Fin.last x.length)
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Order.length_le_height_last`：length_le_height_last {p : LTSeries α} : p.
length <= height p.last
· 使用定理 `WithTop.coe_strictMono`：∀ {α : Type u_1} [inst : Preorder α], StrictMono
 fun a => ↑a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `LTSeries.map_length`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] (p : LTSeries α) (f : α → β)   (hf : StrictMono f), (p.ma
p f hf).l…
-/
@[simp] lemma height_coe_withTop (x : α) : height (x : WithTop α) = height x := by
  apply le_antisymm
  · apply height_le
    intro p hlast
    -- essentially p' := p.map untop
    let p' : LTSeries α := {
      length := p.length
      toFun := fun i => (p i).untop (by
        apply WithTop.lt_top_iff_ne_top.mp
        apply lt_of_le_of_lt
        · exact p.monotone (Fin.le_last _)
        · rw [RelSeries.last] at hlast
          simp [hlast])
      step := fun i => by simpa [WithTop.untop_lt_iff, WithTop.coe_untop] using p.step i }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithTop.untop_eq_iff, ← hlast]
    suffices p'.length ≤ height p'.last by
      rw [hlast'] at this
      simpa [p'] using this
    apply length_le_height_last
  · apply height_le
    intro p hlast
    let p' := p.map _ WithTop.coe_strictMono
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])
/-
**Order.coheight_coe_withBot** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (x : α), Order.coheight ↑x = Order.co
height x
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.height_coe_withTop`：∀ {α : Type u_1} [inst : Preorder α] (x : α), 
Order.height ↑x = Order.height x
-/
@[simp] lemma coheight_coe_withBot (x : α) : coheight (x : WithBot α) = coheight x :=
  height_coe_withTop (α := αᵒᵈ) x
/-
**Order.krullDim_WithTop** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Nonempty α], Order.krullDim (WithTop
 α) = Order.krullDim α + 1
参数：WithTop α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.height_top_eq_krullDim`：height_top_eq_krullDim [OrderTop α] : heig
ht (⊤ : α) = krullDim α
· 使用引理 `Order.krullDim_eq_iSup_height_of_nonempty`：krullDim_eq_iSup_height_of_no
nempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), height a)
· 使用引理 `Order.height_eq_iSup_lt_height`：height_eq_iSup_lt_height (x : α) : heigh
t x = ⨆ y < x, height y + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENat.iSup_add`：iSup_add [Nonempty ι] (f : ι -> Nat∞) : (⨆ i, f i) + a = 
⨆ i, f i + a
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Equiv.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: SupSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨆ x,…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.withTopSubtypeNe_symm_apply_coe`：∀ {α : Type u_1} (x : α), ↑(Equiv
.withTopSubtypeNe.symm x) = ↑x
· 使用定理 `Order.height_coe_withTop`：∀ {α : Type u_1} [inst : Preorder α] (x : α), 
Order.height ↑x = Order.height x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma krullDim_WithTop [Nonempty α] : krullDim (WithTop α) = krullDim α + 1 := by
  rw [← height_top_eq_krullDim, krullDim_eq_iSup_height_of_nonempty, height_eq_iSup_lt_height]
  norm_cast
  simp_rw [WithTop.lt_top_iff_ne_top]
  rw [ENat.iSup_add, iSup_subtype']
  symm
  apply Equiv.withTopSubtypeNe.symm.iSup_congr
  simp
/-
**Order.krullDim_withBot** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Nonempty α], Order.krullDim (WithBot
 α) = Order.krullDim α + 1
参数：WithBot α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.krullDim_orderDual`：∀ {α : Type u_1} [inst : Preorder α], Order.kr
ullDim αᵒᵈ = Order.krullDim α
· 使用定理 `Order.krullDim_WithTop`：∀ {α : Type u_1} [inst : Preorder α] [Nonempty α
], Order.krullDim (WithTop α) = Order.krullDim α + 1
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
-/
@[simp] lemma krullDim_withBot [Nonempty α] : krullDim (WithBot α) = krullDim α + 1 := by
  conv_lhs => rw [← krullDim_orderDual]
  conv_rhs => rw [← krullDim_orderDual]
  exact krullDim_WithTop (α := αᵒᵈ)

@[simp]
/-
**Order.krullDim_enat** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_enat : krullDim Nat∞ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.krullDim_WithTop`：∀ {α : Type u_1} [inst : Preorder α] [Nonempty α
], Order.krullDim (WithTop α) = Order.krullDim α + 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Order.krullDim_of_noMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [None
mpty α] [NoMaxOrder α], Order.krullDim α = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma krullDim_enat : krullDim ℕ∞ = ⊤ := by
  change (krullDim (WithTop ℕ) = ⊤)
  simp [← WithBot.coe_top, ← WithBot.coe_one, ← WithBot.coe_add]

@[simp]
/-
**Order.height_enat** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_enat (n : Nat∞) : height n = n
参数：n : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.height_top_eq_krullDim`：height_top_eq_krullDim [OrderTop α] : heig
ht (⊤ : α) = krullDim α
· 使用引理 `Order.krullDim_enat`：krullDim_enat : krullDim Nat∞ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.height_coe_withTop`：∀ {α : Type u_1} [inst : Preorder α] (x : α), 
Order.height ↑x = Order.height x
· 使用定理 `Order.height_nat`：∀ (n : ℕ), Order.height n = ↑n
-/
lemma height_enat (n : ℕ∞) : height n = n := by
  cases n with
  | top => simp only [← WithBot.coe_eq_coe, height_top_eq_krullDim, krullDim_enat, WithBot.coe_top]
  | coe n => exact (height_coe_withTop _).trans (height_nat _)

@[simp]
/-
**Order.coheight_coe_enat** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_coe_enat (n : Nat) : coheight (n : Nat∞) = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Order.coheight_coe_withTop`：∀ {α : Type u_1} [inst : Preorder α] (x : α)
, Order.coheight ↑x = Order.coheight x + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.coheight_nat`：coheight_nat (n : Nat) : coheight n = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coheight_coe_enat (n : ℕ) : coheight (n : ℕ∞) = ⊤ := by
  apply (coheight_coe_withTop _).trans
  simp only [coheight_nat, top_add]

end calculations

section orderHom

variable {α β : Type*} [Preorder α] [PartialOrder β]
variable {m : ℕ} (f : α →o β) (h : ∀ (x : β), Order.krullDim (f ⁻¹' {x}) ≤ m)

include h in
/-
**Order.height_le_of_krullDim_preimage_le** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：height_le_of_krullDim_preimage_le (x : α) : Order.height x <= (m + 1) * Or
der.height (f x) + m
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENat.mul_top`：∀ {m : ℕ∞}, m ≠ 0 → m * ⊤ = ⊤
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.height_le_iff`：height_le_iff {a : α} {n : Nat∞} : height a <= n ↔ 
forall ⦃p : LTSeries α⦄, p.last <= a -> p.length <= n
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Nat.sub_lt_succ`：∀ (a b : ℕ), a - b < a.succ
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `LTSeries.monotone`：monotone (x : LTSeries α) : Monotone x
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `RelSeries.last_drop`：last_drop (p : RelSeries r) (i : Fin (p.length + 1)
) : (p.drop i).last = p.last
· 使用引理 `RelSeries.head_drop`：head_drop (p : RelSeries r) (i : Fin (p.length + 1)
) : (p.drop i).head = p.toFun i
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
（共 68 条，此处仅展示前 30 条）
-/
lemma height_le_of_krullDim_preimage_le (x : α) :
    Order.height x ≤ (m + 1) * Order.height (f x) + m := by
  generalize h' : Order.height (f x) = n
  cases n with | top => simp | coe n =>
    induction n using Nat.strong_induction_on generalizing x with | h n ih =>
    refine height_le_iff.mpr fun p hp ↦ le_of_not_gt fun h_len ↦ ?_
    let i : Fin (p.length + 1) := ⟨p.length - (m + 1), Nat.sub_lt_succ p.length _⟩
    suffices h'' : f (p i) < f x by
      obtain ⟨n', hn'⟩ : ∃ (n' : ℕ), n' = height (f (p i)) := ENat.ne_top_iff_exists.mp
        ((height_mono h''.le).trans_lt (h' ▸ ENat.natCast_lt_top _)).ne
      have h_lt : n' < n := ENat.natCast_lt_natCast.mp
        (h' ▸ hn' ▸ height_strictMono h'' (hn' ▸ ENat.natCast_lt_top _))
      have := (length_le_height_last (p := p.take i)).trans <| ih n' h_lt (p i) hn'.symm
      rw [RelSeries.take_length, ENat.natCast_sub, Nat.cast_add, Nat.cast_one, tsub_le_iff_right,
        add_assoc, add_comm _ (_ + 1), ← add_assoc, ← mul_add_one] at this
      refine not_lt_of_ge ?_ (h_len.trans_le this)
      gcongr
      rwa [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast]
    refine (f.monotone ((p.monotone (Fin.le_last _)).trans hp)).lt_of_not_ge fun h'' ↦ ?_
    let q' : LTSeries α := p.drop i
    let q : LTSeries (f ⁻¹' {f x}) := ⟨q'.length, fun j ↦ ⟨q' j, le_antisymm
      (f.monotone (le_trans (b := q'.last) (q'.monotone (Fin.le_last _)) (p.last_drop _ ▸ hp)))
      (le_trans (b := f q'.head) (p.head_drop _ ▸ h'')
        (f.monotone (q'.monotone (Fin.zero_le _))))⟩, fun i ↦ q'.step i⟩
    have := (LTSeries.length_le_krullDim q).trans (h (f x))
    simp only [RelSeries.drop_length, Nat.cast_le, tsub_le_iff_right, q', i, q] at this
    have : p.length > m := ENat.natCast_lt_natCast.mp ((le_add_left le_rfl).trans_lt h_len)
    lia

include h in
/-
**Order.coheight_le_of_krullDim_preimage_le** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：coheight_le_of_krullDim_preimage_le (x : α) : Order.coheight x <= (m + 1) 
* Order.coheight (f x) + m
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.coheight.eq_1`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Order
.coheight a = Order.height a
· 使用引理 `Order.height_le_of_krullDim_preimage_le`：height_le_of_krullDim_preimage_
le (x : α) : Order.height x <= (m + 1) * Order.height (f x) + m
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Order.krullDim_orderDual`：∀ {α : Type u_1} [inst : Preorder α], Order.kr
ullDim αᵒᵈ = Order.krullDim α
-/
lemma coheight_le_of_krullDim_preimage_le (x : α) :
    Order.coheight x ≤ (m + 1) * Order.coheight (f x) + m := by
  rw [Order.coheight, Order.coheight]
  apply height_le_of_krullDim_preimage_le (f := f.dual)
  exact fun x ↦ le_of_eq_of_le (krullDim_orderDual (α := f ⁻¹' {x})) (h x)

include f h in
/-
**Order.krullDim_le_of_krullDim_preimage_le** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_le_of_krullDim_preimage_le : Order.krullDim α <= (m + 1) * Order.
krullDim β + m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.krullDim_eq_iSup_height`：krullDim_eq_iSup_height : krullDim α = ⨆ 
(a : α), ↑(height a)
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `WithBot.coe_mono`：coe_mono : Monotone (fun (a : α) => (a : WithBot α))
· 使用引理 `Order.height_le_of_krullDim_preimage_le`：height_le_of_krullDim_preimage_
le (x : α) : Order.height x <= (m + 1) * Order.height (f x) + m
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `WithBot.instPosMulMono`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 
: MulZeroClass α] [inst_2 : Preorder α] [PosMulMono α],   PosMulMono (WithBot α)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `right_eq_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b = a 
⊓ b ↔ b ≤ a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma krullDim_le_of_krullDim_preimage_le :
    Order.krullDim α ≤ (m + 1) * Order.krullDim β + m := by
  rw [Order.krullDim_eq_iSup_height, Order.krullDim_eq_iSup_height, iSup_le_iff]
  refine fun x ↦ (WithBot.coe_mono (height_le_of_krullDim_preimage_le f h x)).trans ?_
  push_cast
  gcongr
  exacts [right_eq_inf.mp rfl, le_iSup_iff.mpr fun b a ↦ a (f x)]

/-- Another version when the `OrderHom` is unbundled -/
/-
**Order.krullDim_le_of_krullDim_preimage_le'** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_le_of_krullDim_preimage_le' (f : α -> β) (h_mono : Monotone f) (h
 : forall (x : β), Order.krullDim (f ⁻¹' {x}) <= m) : Order.krullDim α <= (m + 1
) * Order.krullDim β + m
参数：f : α -> β；h_mono : Monotone f；h : forall (x : β), Order.krullDim (f ⁻¹' {x})
 <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_le_of_krullDim_preimage_le`：krullDim_le_of_krullDim_preim
age_le : Order.krullDim α <= (m + 1) * Order.krullDim β + m

--- 原说明 ---
Another version when the `OrderHom` is unbundled
-/
lemma krullDim_le_of_krullDim_preimage_le' (f : α → β) (h_mono : Monotone f)
    (h : ∀ (x : β), Order.krullDim (f ⁻¹' {x}) ≤ m) :
    Order.krullDim α ≤ (m + 1) * Order.krullDim β + m :=
  Order.krullDim_le_of_krullDim_preimage_le ⟨f, h_mono⟩ h
/-
**Order.krullDim_le_of_orderEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：krullDim_le_of_orderEmbedding (e : α ↪o β) : Order.krullDim α <= Order.kru
llDim β
参数：e : α ↪o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.coe_sort`：∀ {α : Type u} {s : Set α}, s.Subsingleton → 
Subsingleton ↑s
· 使用定理 `Set.Subsingleton.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
s : Set β}, s.Subsingleton → Function.Injective f → (f ⁻¹' s).Subsingleton
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Order.krullDim_le_of_krullDim_preimage_le'`：krullDim_le_of_krullDim_prei
mage_le' (f : α -> β) (h_mono : Monotone f) (h : forall (x : β), Order.krullDim 
(f ⁻¹' {x}) <= m) : Order.krullD…
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
· 使用引理 `Order.krullDim_nonpos_of_subsingleton`：krullDim_nonpos_of_subsingleton [
Subsingleton α] : krullDim α <= 0
-/
lemma krullDim_le_of_orderEmbedding (e : α ↪o β) : Order.krullDim α ≤ Order.krullDim β := by
  have (b : β) : Subsingleton (e ⁻¹' {b}) := Set.Subsingleton.coe_sort <|
    Set.Subsingleton.preimage Set.subsingleton_singleton e.injective
  simpa using Order.krullDim_le_of_krullDim_preimage_le' e e.monotone fun _ ↦
    Order.krullDim_nonpos_of_subsingleton

end orderHom

end Order

