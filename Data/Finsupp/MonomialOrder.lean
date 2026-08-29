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

/--
Definition of `MonomialOrder` / `MonomialOrder` 的定义

English:
structure MonomialOrder
  parameters: (σ : Type*)
  axioms and operations (7):
    - syn : Type*
    - addCommMonoidSyn : AddCommMonoid syn  [default: by infer_instance]
    - linearOrderSyn : LinearOrder syn  [default: by infer_instance]
    - isOrderedAddMonoid_syn : IsOrderedAddMonoid syn  [default: by infer_instance]
    - toSyn : (σ ->₀ Nat) ≃+ syn
    - toSyn_monotone : Monotone toSyn
    - wellFoundedLT_syn : WellFoundedLT syn  [default: by infer_instance]

中文:
结构 MonomialOrder
  参数: (σ : 类型)
  公理与运算 (7 个):
    - syn : 类型
    - addCommMonoidSyn : AddCommMonoid syn  [默认: by infer_instance]
    - linearOrderSyn : LinearOrder syn  [默认: by infer_instance]
    - isOrderedAddMonoid_syn : IsOrderedAddMonoid syn  [默认: by infer_instance]
    - toSyn : (σ ->₀ 自然数) ≃+ syn
    - toSyn_monotone : Monotone toSyn
    - wellFoundedLT_syn : WellFoundedLT syn  [默认: by infer_instance]

Depends on / 依赖: infer_instance
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
  toSyn : (σ ->₀ Nat) ≃+ syn
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCancelCommMonoid m.syn
  body: m.toSyn.symm.injective.isLeftCancelAdd _ (map_add _)

中文:
实例 :
  签名: AddCancelCommMonoid m.syn
  定义体: m.toSyn.symm.injective.isLeftCancelAdd _ (map_add _)

Depends on / 依赖: injective, isLeftCancelAdd, m.toSyn.symm.injective.isLeftCancelAdd, map_add
-/
instance : AddCancelCommMonoid m.syn where
.add_left_cancel add_left_cancel := m.toSyn.symm.injective.isLeftCancelAdd _ (map_add _)

/--
Instance `isOrderedCancelAddMonoid_syn` / 实例 `isOrderedCancelAddMonoid_syn`

English:
instance isOrderedCancelAddMonoid_syn
  signature: : IsOrderedCancelAddMonoid m.syn
  body: IsOrderedAddMonoid.toIsOrderedCancelAddMonoid'

@[deprecated (since := "2026-07-07")] alias iocam := MonomialOrder.isOrderedCancelAddMonoid_syn

中文:
实例 isOrderedCancelAddMonoid_syn
  签名: : IsOrderedCancelAddMonoid m.syn
  定义体: IsOrderedAddMonoid.toIsOrderedCancelAddMonoid'

@[deprecated (since := "2026-07-07")] alias iocam := MonomialOrder.isOrderedCancelAddMonoid_syn

Depends on / 依赖: IsOrderedAddMonoid, IsOrderedAddMonoid.toIsOrderedCancelAddMonoid, toIsOrderedCancelAddMonoid
-/
instance isOrderedCancelAddMonoid_syn : IsOrderedCancelAddMonoid m.syn :=
  IsOrderedAddMonoid.toIsOrderedCancelAddMonoid'

@[deprecated (since := "2026-07-07")] alias iocam := MonomialOrder.isOrderedCancelAddMonoid_syn

/--
Definition of `toWithBotSyn` / `toWithBotSyn` 的定义

English:
definition toWithBotSyn
  signature: : WithBot (σ ->₀ Nat) ≃+ WithBot m.syn
  body: m.toSyn.withBotCongr

中文:
定义 toWithBotSyn
  签名: : WithBot (σ ->₀ 自然数) ≃+ WithBot m.syn
  定义体: m.toSyn.withBotCongr

Depends on / 依赖: m.toSyn.withBotCongr, withBotCongr
-/
noncomputable def toWithBotSyn : WithBot (σ ->₀ Nat) ≃+ WithBot m.syn := m.toSyn.withBotCongr

/--
lemma `le_add_right` / 引理 `le_add_right`

English:
lemma le_add_right
  given: (a b : σ ->₀ Nat)
  proof: by
  rw [← map_add]
  exact m.toSyn_monotone le_self_add

中文:
引理 le_add_right
  条件: (a b : σ ->₀ 自然数)
  证明: by
  rw [← map_add]
  exact m.toSyn_monotone le_self_add

Depends on / 依赖: le_self_add, m.toSyn_monotone, map_add, toSyn_monotone
-/
lemma le_add_right (a b : σ ->₀ Nat) :
    m.toSyn a <= m.toSyn a + m.toSyn b := by
  rw [← map_add]
  exact m.toSyn_monotone le_self_add

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: : OrderBot (m.syn) where
  body: 0
  bot_le a := by
    have := m.le_add_right 0 (m.toSyn.symm a)
    simpa [map_add, zero_add]

@[simp]

中文:
实例 orderBot
  签名: : OrderBot (m.syn) where
  定义体: 0
  bot_le a := by
    have := m.le_add_right 0 (m.toSyn.symm a)
    simpa [map_add, zero_add]

@[simp]
-/
instance orderBot : OrderBot (m.syn) where
  bot := 0
  bot_le a := by
    have := m.le_add_right 0 (m.toSyn.symm a)
    simpa [map_add, zero_add]

@[simp]
/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  statement: (⊥ : m.syn) = 0
  proof: rfl

@[simp]

中文:
定理 bot_eq_zero
  结论: (⊥ : m.syn) = 0
  证明: rfl

@[simp]
-/
theorem bot_eq_zero : (⊥ : m.syn) = 0 := rfl

@[simp]
/--
lemma `zero_le` / 引理 `zero_le`

English:
lemma zero_le
  given: (a : m.syn)
  statement: 0 <= a
  proof: bot_le

中文:
引理 zero_le
  条件: (a : m.syn)
  结论: 0 <= a
  证明: bot_le

Depends on / 依赖: bot_le
-/
lemma zero_le (a : m.syn) : 0 <= a := bot_le

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: {a : m.syn}
  statement: a = 0 ↔ a <= 0
  proof: eq_bot_iff

中文:
定理 eq_zero_iff
  条件: {a : m.syn}
  结论: a = 0 ↔ a <= 0
  证明: eq_bot_iff

Depends on / 依赖: eq_bot_iff
-/
theorem eq_zero_iff {a : m.syn} : a = 0 ↔ a <= 0 := eq_bot_iff

/--
lemma `toSyn_eq_zero_iff` / 引理 `toSyn_eq_zero_iff`

English:
lemma toSyn_eq_zero_iff
  given: (a : σ ->₀ Nat)
  proof: AddEquiv.map_eq_zero_iff m.toSyn

中文:
引理 toSyn_eq_zero_iff
  条件: (a : σ ->₀ 自然数)
  证明: AddEquiv.map_eq_zero_iff m.toSyn

Depends on / 依赖: AddEquiv, AddEquiv.map_eq_zero_iff, m.toSyn, map_eq_zero_iff
-/
lemma toSyn_eq_zero_iff (a : σ ->₀ Nat) :
    m.toSyn a = 0 ↔ a = 0 := AddEquiv.map_eq_zero_iff m.toSyn

/--
lemma `toSyn_lt_iff_ne_zero` / 引理 `toSyn_lt_iff_ne_zero`

English:
lemma toSyn_lt_iff_ne_zero
  given: {a : m.syn}
  proof: bot_lt_iff_ne_bot

中文:
引理 toSyn_lt_iff_ne_zero
  条件: {a : m.syn}
  证明: bot_lt_iff_ne_bot

Depends on / 依赖: bot_lt_iff_ne_bot
-/
lemma toSyn_lt_iff_ne_zero {a : m.syn} :
    0 < a ↔ a != 0 := bot_lt_iff_ne_bot

/--
lemma `toSyn_strictMono` / 引理 `toSyn_strictMono`

English:
lemma toSyn_strictMono
  statement: StrictMono (m.toSyn)
  proof: by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective

@[simp]

中文:
引理 toSyn_strictMono
  结论: StrictMono (m.toSyn)
  证明: by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective

@[simp]

Depends on / 依赖: injective, m.toSyn.injective, m.toSyn_monotone.strictMono_of_injective, strictMono_of_injective, toSyn_monotone
-/
lemma toSyn_strictMono : StrictMono (m.toSyn) := by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective

@[simp]
/--
lemma `toWithBotSyn_apply_bot` / 引理 `toWithBotSyn_apply_bot`

English:
lemma toWithBotSyn_apply_bot
  statement: m.toWithBotSyn ⊥ = ⊥
  proof: rfl

@[simp]

中文:
引理 toWithBotSyn_apply_bot
  结论: m.toWithBotSyn ⊥ = ⊥
  证明: rfl

@[simp]
-/
lemma toWithBotSyn_apply_bot : m.toWithBotSyn ⊥ = ⊥ := rfl

@[simp]
/--
lemma `toWithBotSyn_symm_apply_bot` / 引理 `toWithBotSyn_symm_apply_bot`

English:
lemma toWithBotSyn_symm_apply_bot
  statement: m.toWithBotSyn.symm ⊥ = ⊥
  proof: rfl

@[simp]

中文:
引理 toWithBotSyn_symm_apply_bot
  结论: m.toWithBotSyn.symm ⊥ = ⊥
  证明: rfl

@[simp]
-/
lemma toWithBotSyn_symm_apply_bot : m.toWithBotSyn.symm ⊥ = ⊥ := rfl

@[simp]
/--
lemma `toWithBotSyn_apply_eq_bot_iff` / 引理 `toWithBotSyn_apply_eq_bot_iff`

English:
lemma toWithBotSyn_apply_eq_bot_iff
  given: (a)
  statement: m.toWithBotSyn a = ⊥ ↔ a = ⊥
  proof: by
  simp [← m.toWithBotSyn.eq_symm_apply]

中文:
引理 toWithBotSyn_apply_eq_bot_iff
  条件: (a)
  结论: m.toWithBotSyn a = ⊥ ↔ a = ⊥
  证明: by
  simp [← m.toWithBotSyn.eq_symm_apply]

Depends on / 依赖: eq_symm_apply, m.toWithBotSyn.eq_symm_apply, toWithBotSyn
-/
lemma toWithBotSyn_apply_eq_bot_iff (a) : m.toWithBotSyn a = ⊥ ↔ a = ⊥ := by
  simp [← m.toWithBotSyn.eq_symm_apply]

/--
lemma `toWithBotSyn_apply_le_bot_iff` / 引理 `toWithBotSyn_apply_le_bot_iff`

English:
lemma toWithBotSyn_apply_le_bot_iff
  given: (a)
  statement: m.toWithBotSyn a <= ⊥ ↔ a = ⊥
  proof: by
  simp

@[simp]

中文:
引理 toWithBotSyn_apply_le_bot_iff
  条件: (a)
  结论: m.toWithBotSyn a <= ⊥ ↔ a = ⊥
  证明: by
  simp

@[simp]
-/
lemma toWithBotSyn_apply_le_bot_iff (a) : m.toWithBotSyn a <= ⊥ ↔ a = ⊥ := by
  simp

@[simp]
/--
lemma `toWithBotSyn_apply_coe` / 引理 `toWithBotSyn_apply_coe`

English:
lemma toWithBotSyn_apply_coe
  given: (a : σ ->₀ Nat)
  statement: m.toWithBotSyn a = m.toSyn a
  proof: rfl

@[simp]

中文:
引理 toWithBotSyn_apply_coe
  条件: (a : σ ->₀ 自然数)
  结论: m.toWithBotSyn a = m.toSyn a
  证明: rfl

@[simp]
-/
lemma toWithBotSyn_apply_coe (a : σ ->₀ Nat) : m.toWithBotSyn a = m.toSyn a := rfl

@[simp]
/--
lemma `bot_lt_toWithBotSyn_apply_iff` / 引理 `bot_lt_toWithBotSyn_apply_iff`

English:
lemma bot_lt_toWithBotSyn_apply_iff
  given: (a)
  statement: ⊥ < m.toWithBotSyn a ↔ ⊥ < a
  proof: by
  simp [bot_lt_iff_ne_bot]

@[simp]

中文:
引理 bot_lt_toWithBotSyn_apply_iff
  条件: (a)
  结论: ⊥ < m.toWithBotSyn a ↔ ⊥ < a
  证明: by
  simp [bot_lt_iff_ne_bot]

@[simp]

Depends on / 依赖: bot_lt_iff_ne_bot
-/
lemma bot_lt_toWithBotSyn_apply_iff (a) : ⊥ < m.toWithBotSyn a ↔ ⊥ < a := by
  simp [bot_lt_iff_ne_bot]

@[simp]
/--
lemma `toWithBotSyn_symm_apply_eq_bot` / 引理 `toWithBotSyn_symm_apply_eq_bot`

English:
lemma toWithBotSyn_symm_apply_eq_bot
  given: (a)
  statement: m.toWithBotSyn.symm a = ⊥ ↔ a = ⊥
  proof: by
  simp [m.toWithBotSyn.symm_apply_eq]

中文:
引理 toWithBotSyn_symm_apply_eq_bot
  条件: (a)
  结论: m.toWithBotSyn.symm a = ⊥ ↔ a = ⊥
  证明: by
  simp [m.toWithBotSyn.symm_apply_eq]

Depends on / 依赖: m.toWithBotSyn.symm_apply_eq, symm_apply_eq, toWithBotSyn
-/
lemma toWithBotSyn_symm_apply_eq_bot (a) : m.toWithBotSyn.symm a = ⊥ ↔ a = ⊥ := by
  simp [m.toWithBotSyn.symm_apply_eq]

/--
lemma `toWithBotSyn_apply` / 引理 `toWithBotSyn_apply`

English:
lemma toWithBotSyn_apply
  given: (a : WithBot (σ ->₀ Nat))
  statement: m.toWithBotSyn a = a.map m.toSyn
  proof: rfl

中文:
引理 toWithBotSyn_apply
  条件: (a : WithBot (σ ->₀ 自然数))
  结论: m.toWithBotSyn a = a.map m.toSyn
  证明: rfl
-/
lemma toWithBotSyn_apply (a : WithBot (σ ->₀ Nat)) : m.toWithBotSyn a = a.map m.toSyn := rfl

/-- Given a monomial order, notation for the corresponding strict order relation on `σ →₀ ℕ` -/
scoped
notation:50 c " ≺[" m:25 "] " d:50 => (MonomialOrder.toSyn m c < MonomialOrder.toSyn m d)

/-- Given a monomial order, notation for the corresponding order relation on `σ →₀ ℕ` -/
scoped
notation:50 c " ≼[" m:25 "] " d:50 => (MonomialOrder.toSyn m c <= MonomialOrder.toSyn m d)

/-- Given a monomial order with bot, notation for the corresponding strict order relation on
`WithBot (σ →₀ ℕ)` -/
scoped
notation:50 c " ≺'[" m:25 "] " d:50 =>
  (MonomialOrder.toWithBotSyn m c < MonomialOrder.toWithBotSyn m d)

/-- Given a monomial order with bot, notation for the corresponding order relation on
`WithBot (σ →₀ ℕ)` -/
scoped
notation:50 c " ≼'[" m:25 "] " d:50 =>
  (MonomialOrder.toWithBotSyn m c <= MonomialOrder.toWithBotSyn m d)

end MonomialOrder

section Lex

open Finsupp

open scoped MonomialOrder

-- The linear order on `Finsupp`s obtained by the lexicographic ordering. -/
noncomputable instance {α N : Type*} [LinearOrder α]
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] :
    IsOrderedCancelAddMonoid (Lex (α ->₀ N)) where
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

/--
Definition of `MonomialOrder.lex` / `MonomialOrder.lex` 的定义

English:
definition MonomialOrder.lex
  signature: [WellFoundedGT σ]
  body: Lex (σ ->₀ Nat)
  toSyn :=
  { toEquiv := toLex
    map_add' := toLex_add }
  toSyn_monotone := Finsupp.toLex_monotone

中文:
定义 MonomialOrder.lex
  签名: [WellFoundedGT σ]
  定义体: Lex (σ ->₀ Nat)
  toSyn :=
  { toEquiv := toLex
    map_add' := toLex_add }
  toSyn_monotone := Finsupp.toLex_monotone
-/
noncomputable def MonomialOrder.lex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := Lex (σ ->₀ Nat)
  toSyn :=
  { toEquiv := toLex
    map_add' := toLex_add }
  toSyn_monotone := Finsupp.toLex_monotone

/--
theorem `MonomialOrder.lex_le_iff` / 定理 `MonomialOrder.lex_le_iff`

English:
theorem MonomialOrder.lex_le_iff
  given: [WellFoundedGT σ] {c d : σ ->₀ Nat}
  proof: Iff.rfl

中文:
定理 MonomialOrder.lex_le_iff
  条件: [WellFoundedGT σ] {c d : σ ->₀ 自然数}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem MonomialOrder.lex_le_iff [WellFoundedGT σ] {c d : σ ->₀ Nat} :
    c ≼[lex] d ↔ toLex c <= toLex d := Iff.rfl

/--
theorem `MonomialOrder.lex_lt_iff` / 定理 `MonomialOrder.lex_lt_iff`

English:
theorem MonomialOrder.lex_lt_iff
  given: [WellFoundedGT σ] {c d : σ ->₀ Nat}
  proof: Iff.rfl

中文:
定理 MonomialOrder.lex_lt_iff
  条件: [WellFoundedGT σ] {c d : σ ->₀ 自然数}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem MonomialOrder.lex_lt_iff [WellFoundedGT σ] {c d : σ ->₀ Nat} :
    c ≺[lex] d ↔ toLex c < toLex d := Iff.rfl

/--
theorem `MonomialOrder.lex_lt_iff_of_unique` / 定理 `MonomialOrder.lex_lt_iff_of_unique`

English:
theorem MonomialOrder.lex_lt_iff_of_unique
  given: [Unique σ] {c d : σ ->₀ Nat}
  proof: by
  simp only [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff_of_unique, ofLex_toLex]

中文:
定理 MonomialOrder.lex_lt_iff_of_unique
  条件: [Unique σ] {c d : σ ->₀ 自然数}
  证明: by
  simp only [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff_of_unique, ofLex_toLex]

Depends on / 依赖: Finsupp, Finsupp.Lex.lt_iff_of_unique, MonomialOrder, MonomialOrder.lex_lt_iff, lex_lt_iff, lt_iff_of_unique, ofLex_toLex
-/
theorem MonomialOrder.lex_lt_iff_of_unique [Unique σ] {c d : σ ->₀ Nat} :
    c ≺[lex] d ↔ c default < d default := by
  simp only [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff_of_unique, ofLex_toLex]

/--
theorem `MonomialOrder.lex_le_iff_of_unique` / 定理 `MonomialOrder.lex_le_iff_of_unique`

English:
theorem MonomialOrder.lex_le_iff_of_unique
  given: [Unique σ] {c d : σ ->₀ Nat}
  proof: by
  simp only [MonomialOrder.lex_le_iff, Finsupp.Lex.le_iff_of_unique, ofLex_toLex]

中文:
定理 MonomialOrder.lex_le_iff_of_unique
  条件: [Unique σ] {c d : σ ->₀ 自然数}
  证明: by
  simp only [MonomialOrder.lex_le_iff, Finsupp.Lex.le_iff_of_unique, ofLex_toLex]

Depends on / 依赖: Finsupp, Finsupp.Lex.le_iff_of_unique, MonomialOrder, MonomialOrder.lex_le_iff, le_iff_of_unique, lex_le_iff, ofLex_toLex
-/
theorem MonomialOrder.lex_le_iff_of_unique [Unique σ] {c d : σ ->₀ Nat} :
    c ≼[lex] d ↔ c default <= d default := by
  simp only [MonomialOrder.lex_le_iff, Finsupp.Lex.le_iff_of_unique, ofLex_toLex]

end Lex
