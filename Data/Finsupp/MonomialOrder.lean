/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.Data.List.TFAE
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-! # Monomial orders

## Monomial orders

A *monomial order* is well ordering relation on a type of the form `σ →₀ ℕ` which
is compatible with addition and for which `0` is the smallest element.
Since several monomial orders may have to be used simultaneously, one cannot
get them as instances.

In this formalization, they are presented as a structure `MonomialOrder` which encapsulates
`MonomialOrder.toSyn`, an additive and monotone isomorphism to a linearly ordered cancellative
additive commutative monoid.
The entry `MonomialOrder.wellFoundedLT_syn` asserts that `MonomialOrder.syn` is well founded.

The terminology comes from commutative algebra and algebraic geometry, especially Gröbner bases,
where `c : σ →₀ ℕ` are exponents of monomials.

Given a monomial order `m : MonomialOrder σ`, we provide the notation
`c ≼[m] d` and `c ≺[m] d` to compare `c d : σ →₀ ℕ` with respect to `m`.
It is activated using `open scoped MonomialOrder`.

## Examples

Commutative algebra defines many monomial orders, with different usefulness ranges.
In this file, we provide the basic example of lexicographic ordering.
For the graded lexicographic ordering, see `Mathlib/Data/Finsupp/MonomialOrder/DegLex.lean`

* `MonomialOrder.lex` : the lexicographic ordering on `σ →₀ ℕ`.
  For this, `σ` needs to be embedded with an ordering relation which satisfies `WellFoundedGT σ`.
  (This last property is automatic when `σ` is finite).

The type synonym is `Lex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.lex_le_iff`
and `MonomialOrder.lex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

## Note

In algebraic geometry, when the finitely many variables are indexed by integers,
it is customary to order them using the opposite order : `MvPolynomial.X 0 > MvPolynomial.X 1 > … `

-/

@[expose] public section

/-- Monomial orders : equivalence of `σ →₀ ℕ` with a well-ordered type -/
/-
**MonomialOrder** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：MonomialOrder (σ : Type*) where /-- The synonym type -/ syn : Type* /-- `s
yn` is an additive commutative monoid -/ addCommMonoidSyn : AddCommMonoid syn
参数：σ : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monomial orders : equivalence of `σ →₀ ℕ` with a well-ordered type
-/
structure MonomialOrder (σ : Type*) where
  /-- The synonym type -/
  syn : Type*
  /-- `syn` is an additive commutative monoid -/
  addCommMonoidSyn : AddCommMonoid syn := by infer_instance
  /-- `syn` is linearly ordered -/
  linearOrderSyn : LinearOrder syn := by infer_instance
  /-- `syn` is a linearly ordered cancellative additive commutative monoid -/
  isOrderedAddMonoid_syn : IsOrderedAddMonoid syn := by infer_instance
  /-- the additive equivalence from `σ →₀ ℕ` to `syn` -/
  toSyn : (σ →₀ ℕ) ≃+ syn
  /-- `toSyn` is monotone -/
  toSyn_monotone : Monotone toSyn
  /-- `syn` is a well ordering -/
  wellFoundedLT_syn : WellFoundedLT syn := by infer_instance

attribute [instance] MonomialOrder.addCommMonoidSyn MonomialOrder.linearOrderSyn
  MonomialOrder.isOrderedAddMonoid_syn MonomialOrder.wellFoundedLT_syn

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ)

@[deprecated (since := "2026-07-07")] alias acm := MonomialOrder.addCommMonoidSyn

@[deprecated (since := "2026-07-07")] alias lo := MonomialOrder.linearOrderSyn

@[deprecated (since := "2026-07-07")] alias wf := MonomialOrder.wellFoundedLT_syn

/-
**MonomialOrder.** 是 Mathlib 中的一个实例，位于命名空间 `MonomialOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCancelCommMonoid m.syn where
  add_left_cancel := m.toSyn.symm.injective.isLeftCancelAdd _ (map_add _) |>.add_left_cancel
/-
**MonomialOrder.isOrderedCancelAddMonoid_syn** 是 Mathlib 中的一个实例，位于命名空间 `Monomial
Order`。
形式化陈述：isOrderedCancelAddMonoid_syn : IsOrderedCancelAddMonoid m.syn
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid'`：∀ {α : Type u} [inst : A
ddCancelCommMonoid α] [inst_1 : LinearOrder α] [IsOrderedAddMonoid α],   IsOrder
edCancelAddMonoid α
· 使用定理 `MonomialOrder.isOrderedAddMonoid_syn`：∀ {σ : Type u_1} (self : MonomialO
rder σ), IsOrderedAddMonoid self.syn
-/
instance isOrderedCancelAddMonoid_syn : IsOrderedCancelAddMonoid m.syn :=
  IsOrderedAddMonoid.toIsOrderedCancelAddMonoid'

@[deprecated (since := "2026-07-07")] alias iocam := MonomialOrder.isOrderedCancelAddMonoid_syn

/-- A `WithBot m.syn` version of `m.toSyn`. -/
/-
**MonomialOrder.toWithBotSyn** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：toWithBotSyn : WithBot (σ ->₀ Nat) ≃+ WithBot m.syn
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WithBot m.syn` version of `m.toSyn`.
-/
noncomputable def toWithBotSyn : WithBot (σ →₀ ℕ) ≃+ WithBot m.syn := m.toSyn.withBotCongr
/-
**MonomialOrder.le_add_right** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：le_add_right (a b : σ ->₀ Nat) : m.toSyn a <= m.toSyn a + m.toSyn b
参数：a b : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `MonomialOrder.toSyn_monotone`：∀ {σ : Type u_1} (self : MonomialOrder σ),
 Monotone ⇑self.toSyn
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma le_add_right (a b : σ →₀ ℕ) :
    m.toSyn a ≤ m.toSyn a + m.toSyn b := by
  rw [← map_add]
  exact m.toSyn_monotone le_self_add
/-
**MonomialOrder.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `MonomialOrder`。
形式化陈述：orderBot : OrderBot (m.syn) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderBot : OrderBot (m.syn) where
  bot := 0
  bot_le a := by
    have := m.le_add_right 0 (m.toSyn.symm a)
    simpa [map_add, zero_add]

@[simp]
/-
**MonomialOrder.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：bot_eq_zero : (⊥ : m.syn) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_zero : (⊥ : m.syn) = 0 := rfl

@[simp]
/-
**MonomialOrder.zero_le** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：zero_le (a : m.syn) : 0 <= a
参数：a : m.syn。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma zero_le (a : m.syn) : 0 ≤ a := bot_le
/-
**MonomialOrder.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：eq_zero_iff {a : m.syn} : a = 0 ↔ a <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
-/
theorem eq_zero_iff {a : m.syn} : a = 0 ↔ a ≤ 0 := eq_bot_iff
/-
**MonomialOrder.toSyn_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：toSyn_eq_zero_iff (a : σ ->₀ Nat) : m.toSyn a = 0 ↔ a = 0
参数：a : σ ->₀ Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZer
oClass M] [inst_1 : AddZeroClass N] (h : M ≃+ N) {x : M}, h x = 0 ↔ x = 0
-/
lemma toSyn_eq_zero_iff (a : σ →₀ ℕ) :
    m.toSyn a = 0 ↔ a = 0 := AddEquiv.map_eq_zero_iff m.toSyn
/-
**MonomialOrder.toSyn_lt_iff_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：toSyn_lt_iff_ne_zero {a : m.syn} : 0 < a ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
-/
lemma toSyn_lt_iff_ne_zero {a : m.syn} :
    0 < a ↔ a ≠ 0 := bot_lt_iff_ne_bot
/-
**MonomialOrder.toSyn_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：toSyn_strictMono : StrictMono (m.toSyn)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `MonomialOrder.toSyn_monotone`：∀ {σ : Type u_1} (self : MonomialOrder σ),
 Monotone ⇑self.toSyn
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
-/
lemma toSyn_strictMono : StrictMono (m.toSyn) := by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective

@[simp]
/-
**MonomialOrder.toWithBotSyn_apply_bot** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`
。
形式化陈述：toWithBotSyn_apply_bot : m.toWithBotSyn ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toWithBotSyn_apply_bot : m.toWithBotSyn ⊥ = ⊥ := rfl

@[simp]
/-
**MonomialOrder.toWithBotSyn_symm_apply_bot** 是 Mathlib 中的一个引理，位于命名空间 `MonomialO
rder`。
形式化陈述：toWithBotSyn_symm_apply_bot : m.toWithBotSyn.symm ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toWithBotSyn_symm_apply_bot : m.toWithBotSyn.symm ⊥ = ⊥ := rfl

@[simp]
/-
**MonomialOrder.toWithBotSyn_apply_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Monomia
lOrder`。
形式化陈述：toWithBotSyn_apply_eq_bot_iff (a) : m.toWithBotSyn a = ⊥ ↔ a = ⊥
参数：a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddEquiv.eq_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, y = e.symm x ↔ e y = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toWithBotSyn_apply_eq_bot_iff (a) : m.toWithBotSyn a = ⊥ ↔ a = ⊥ := by
  simp [← m.toWithBotSyn.eq_symm_apply]
/-
**MonomialOrder.toWithBotSyn_apply_le_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Monomia
lOrder`。
形式化陈述：toWithBotSyn_apply_le_bot_iff (a) : m.toWithBotSyn a <= ⊥ ↔ a = ⊥
参数：a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toWithBotSyn_apply_le_bot_iff (a) : m.toWithBotSyn a ≤ ⊥ ↔ a = ⊥ := by
  simp

@[simp]
/-
**MonomialOrder.toWithBotSyn_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`
。
形式化陈述：toWithBotSyn_apply_coe (a : σ ->₀ Nat) : m.toWithBotSyn a = m.toSyn a
参数：a : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toWithBotSyn_apply_coe (a : σ →₀ ℕ) : m.toWithBotSyn a = m.toSyn a := rfl

@[simp]
/-
**MonomialOrder.bot_lt_toWithBotSyn_apply_iff** 是 Mathlib 中的一个引理，位于命名空间 `Monomia
lOrder`。
形式化陈述：bot_lt_toWithBotSyn_apply_iff (a) : ⊥ < m.toWithBotSyn a ↔ ⊥ < a
参数：a。
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
lemma bot_lt_toWithBotSyn_apply_iff (a) : ⊥ < m.toWithBotSyn a ↔ ⊥ < a := by
  simp [bot_lt_iff_ne_bot]

@[simp]
/-
**MonomialOrder.toWithBotSyn_symm_apply_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Monomi
alOrder`。
形式化陈述：toWithBotSyn_symm_apply_eq_bot (a) : m.toWithBotSyn.symm a = ⊥ ↔ a = ⊥
参数：a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.symm_apply_eq`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, e.symm x = y ↔ x = e y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toWithBotSyn_symm_apply_eq_bot (a) : m.toWithBotSyn.symm a = ⊥ ↔ a = ⊥ := by
  simp [m.toWithBotSyn.symm_apply_eq]
/-
**MonomialOrder.toWithBotSyn_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：toWithBotSyn_apply (a : WithBot (σ ->₀ Nat)) : m.toWithBotSyn a = a.map m.
toSyn
参数：a : WithBot (σ ->₀ Nat)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toWithBotSyn_apply (a : WithBot (σ →₀ ℕ)) : m.toWithBotSyn a = a.map m.toSyn := rfl

/-- Given a monomial order, notation for the corresponding strict order relation on `σ →₀ ℕ` -/
scoped
notation:50 c " ≺[" m:25 "] " d:50 => (MonomialOrder.toSyn m c < MonomialOrder.toSyn m d)

/-- Given a monomial order, notation for the corresponding order relation on `σ →₀ ℕ` -/
scoped
notation:50 c " ≼[" m:25 "] " d:50 => (MonomialOrder.toSyn m c ≤ MonomialOrder.toSyn m d)

/-- Given a monomial order with bot, notation for the corresponding strict order relation on
`WithBot (σ →₀ ℕ)` -/
scoped
notation:50 c " ≺'[" m:25 "] " d:50 =>
  (MonomialOrder.toWithBotSyn m c < MonomialOrder.toWithBotSyn m d)

/-- Given a monomial order with bot, notation for the corresponding order relation on
`WithBot (σ →₀ ℕ)` -/
scoped
notation:50 c " ≼'[" m:25 "] " d:50 =>
  (MonomialOrder.toWithBotSyn m c ≤ MonomialOrder.toWithBotSyn m d)

end MonomialOrder

section Lex

open Finsupp

open scoped MonomialOrder

-- The linear order on `Finsupp`s obtained by the lexicographic ordering. -/
noncomputable instance {α N : Type*} [LinearOrder α]
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] :
    IsOrderedCancelAddMonoid (Lex (α →₀ N)) where
  le_of_add_le_add_left a b c h := by simpa only [add_le_add_iff_left] using h
  add_le_add_left a b h c := by simpa using h

/-- for the lexicographic ordering, X 0 * X 1 < X 0 ^ 2 -/
example : toLex (Finsupp.single 0 2) > toLex (Finsupp.single 0 1 + Finsupp.single 1 1) := by
  use 0; simp

/-- for the lexicographic ordering, X 1 < X 0 -/
example : toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 1) := by
  use 0; simp

/-- for the lexicographic ordering, X 1 < X 0 ^ 2 -/
example : toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 2) := by
  use 0; simp

variable {σ : Type*} [LinearOrder σ]

/-- The lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
noncomputable def MonomialOrder.lex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := Lex (σ →₀ ℕ)
  toSyn :=
  { toEquiv := toLex
    map_add' := toLex_add }
  toSyn_monotone := Finsupp.toLex_monotone

theorem MonomialOrder.lex_le_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≼[lex] d ↔ toLex c ≤ toLex d := Iff.rfl

theorem MonomialOrder.lex_lt_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≺[lex] d ↔ toLex c < toLex d := Iff.rfl

theorem MonomialOrder.lex_lt_iff_of_unique [Unique σ] {c d : σ →₀ ℕ} :
    c ≺[lex] d ↔ c default < d default := by
  simp only [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff_of_unique, ofLex_toLex]

theorem MonomialOrder.lex_le_iff_of_unique [Unique σ] {c d : σ →₀ ℕ} :
    c ≼[lex] d ↔ c default ≤ d default := by
  simp only [MonomialOrder.lex_le_iff, Finsupp.Lex.le_iff_of_unique, ofLex_toLex]

end Lex

