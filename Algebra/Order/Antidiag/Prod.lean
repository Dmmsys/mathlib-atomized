/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs

/-! # Antidiagonal with values in general types

We define a type class `Finset.HasAntidiagonal A` which contains a function
`antidiagonal : A → Finset (A × A)` such that `antidiagonal n`
is the finset of all pairs adding to `n`, as witnessed by `mem_antidiagonal`.

Analogously, the type class `Finset.HasMulAntidiagonal A` contains a function
`mulAntidiagonal : A → Finset (A × A)` such that `mulAntidiagonal n`
is the finset of all pairs multiplying to `n`, as witnessed by `mem_mulAntidiagonal`.

When `A` is a canonically ordered additive monoid with locally finite order
this typeclass can be instantiated with `Finset.antidiagonalOfLocallyFinite`.
This applies in particular when `A` is `ℕ`, more generally or `σ →₀ ℕ`,
or even `ι →₀ A`  under the additional assumption `OrderedSub A`
that make it a canonically ordered additive monoid.
(In fact, we would just need an `AddMonoid` with a compatible order,
finite `Iic`, such that if `a + b = n`, then `a, b ≤ n`,
and any finiteness condition would be OK.)

For computational reasons it is better to manually provide instances for `ℕ`
and `σ →₀ ℕ`, to avoid quadratic runtime performance.
These instances are provided as `Finset.Nat.instHasAntidiagonal` and
`Finsupp.instHasAntidiagonal`.
This is why `Finset.mulAntidiagonalOfLocallyFinite` is an `abbrev` and not an `instance`.

This definition does not exactly match with that of `Multiset.antidiagonal`
defined in `Mathlib/Data/Multiset/Antidiagonal.lean`, because of the multiplicities.
Indeed, by counting multiplicities, `Multiset α` is equivalent to `α →₀ ℕ`,
but `Finset.antidiagonal` and `Multiset.antidiagonal` will return different objects.
For example, for `s : Multiset ℕ := {0,0,0}`, `Multiset.antidiagonal s` has 8 elements
but `Finset.antidiagonal s` has only 4.

```lean
def s : Multiset ℕ := {0, 0, 0}
#eval (Finset.antidiagonal s).card -- 4
#eval Multiset.card (Multiset.antidiagonal s) -- 8
```

## TODO

* For `PNat`, `HasMulAntidiagonal` will recover the set of divisors of a strictly positive integer.
-/

@[expose] public section

open Function

namespace Finset

/-- The class of additive monoids with an antidiagonal. -/
/-
**Finset.HasAntidiagonal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Finset`。
形式化陈述：(A : Type u_1) → [AddMonoid A] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of additive monoids with an antidiagonal.
-/
class HasAntidiagonal (A : Type*) [AddMonoid A] where
  /-- The antidiagonal of an element `n` is the finset of pairs `(i, j)` such that
  `i + j = n`. -/
  antidiagonal : A → Finset (A × A)
  /-- A pair belongs to `antidiagonal n` iff the sum of its components is equal to `n`. -/
  mem_antidiagonal {n} {a} : a ∈ antidiagonal n ↔ a.fst + a.snd = n

export HasAntidiagonal (antidiagonal mem_antidiagonal)

attribute [simp] mem_antidiagonal

/-- The class of (multiplicative) monoids with a mulAntidiagonal. -/
/-
**Finset.HasMulAntidiagonal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Finset`。
形式化陈述：(A : Type u_1) → [Monoid A] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of (multiplicative) monoids with a mulAntidiagonal.
-/
class HasMulAntidiagonal (A : Type*) [Monoid A] where
  /-- The mulAntidiagonal of an element `n` is the finset of pairs `(i, j)` such that
  `i * j = n`. -/
  mulAntidiagonal : A → Finset (A × A)
  /-- A pair belongs to `mulAntidiagonal n` iff the product of its components is equal to `n`. -/
  mem_mulAntidiagonal {n} {a} : a ∈ mulAntidiagonal n ↔ a.fst * a.snd = n

attribute [to_additive] HasMulAntidiagonal

export HasMulAntidiagonal (mulAntidiagonal mem_mulAntidiagonal)

attribute [simp] HasMulAntidiagonal.mem_mulAntidiagonal

variable {A : Type*}

namespace HasMulAntidiagonal

/-- All `HasMulAntidiagonal` instances are equal -/
@[to_additive /-- All `HasAntidiagonal` instances are equal -/]
/-
**Finset.HasMulAntidiagonal.** 是 Mathlib 中的一个实例，位于命名空间 `Finset.HasMulAntidiagona
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All `HasMulAntidiagonal` instances are equal
-/
instance [Monoid A] : Subsingleton (HasMulAntidiagonal A) where
  allEq := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    congr with n xy
    rw [ha, hb]

@[to_additive]
/-
**Finset.HasMulAntidiagonal.nonempty_antidiagonal** 是 Mathlib 中的一个引理，位于命名空间 `Fin
set.HasMulAntidiagonal`。
形式化陈述：nonempty_antidiagonal {M : Type*} [Monoid M] [Finset.HasMulAntidiagonal M]
 (a : M) : (Finset.mulAntidiagonal a).Nonempty
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nonempty_antidiagonal {M : Type*} [Monoid M] [Finset.HasMulAntidiagonal M] (a : M) :
    (Finset.mulAntidiagonal a).Nonempty :=
  ⟨(1, a), by simp⟩

-- The goal of this lemma is to allow to rewrite mulAntidiagonal/antidiagonal
-- when the decidability instances obfuscate Lean
set_option linter.overlappingInstances false in
@[to_additive]
/-
**Finset.HasMulAntidiagonal.congr** 是 Mathlib 中的一个引理，位于命名空间 `Finset.HasMulAntidi
agonal`。
形式化陈述：congr (A : Type*) [Monoid A] [H1 : HasMulAntidiagonal A] [H2 : HasMulAntid
iagonal A] : H1.mulAntidiagonal = H2.mulAntidiagonal
参数：A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Finset.HasMulAntidiagonal.instSubsingleton`：∀ {A : Type u_1} [inst : Mon
oid A], Subsingleton (Finset.HasMulAntidiagonal A)
-/
lemma congr (A : Type*) [Monoid A]
    [H1 : HasMulAntidiagonal A] [H2 : HasMulAntidiagonal A] :
    H1.mulAntidiagonal = H2.mulAntidiagonal := by congr!; subsingleton

@[to_additive]
/-
**Finset.HasMulAntidiagonal.swap_mem_mulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `
Finset.HasMulAntidiagonal`。
形式化陈述：swap_mem_mulAntidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A} {xy
 : A × A} : xy.swap in mulAntidiagonal n ↔ xy in mulAntidiagonal n
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem swap_mem_mulAntidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A} {xy : A × A} :
    xy.swap ∈ mulAntidiagonal n ↔ xy ∈ mulAntidiagonal n := by
  simp [mul_comm]

@[to_additive (attr := simp) map_prodComm_antidiagonal]
/-
**Finset.HasMulAntidiagonal.map_prodComm_mulAntidiagonal** 是 Mathlib 中的一个定理，位于命名
空间 `Finset.HasMulAntidiagonal`。
形式化陈述：map_prodComm_mulAntidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A}
 : (mulAntidiagonal n).map (Equiv.prodComm A A) = mulAntidiagonal n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_prodComm_mulAntidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A} :
    (mulAntidiagonal n).map (Equiv.prodComm A A) = mulAntidiagonal n :=
  Finset.ext fun ⟨a, b⟩ => by simp [mul_comm]

/-- See also `Finset.map_prodComm_mulAntidiagonal`. -/
@[to_additive (attr := simp)]
/-
**Finset.HasMulAntidiagonal.map_swap_mulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `
Finset.HasMulAntidiagonal`。
形式化陈述：map_swap_mulAntidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A} : (
mulAntidiagonal n).map ⟨Prod.swap, Prod.swap_injective⟩ = mulAntidiagonal n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.HasMulAntidiagonal.map_prodComm_mulAntidiagonal`：map_prodComm_mul
Antidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A} : (mulAntidiagonal n)
.map (Equiv.prodComm A A) = mulAntidiagonal …

--- 原说明 ---
See also `Finset.map_prodComm_mulAntidiagonal`.
-/
theorem map_swap_mulAntidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A} :
    (mulAntidiagonal n).map ⟨Prod.swap, Prod.swap_injective⟩ = mulAntidiagonal n :=
  map_prodComm_mulAntidiagonal

section CancelMonoid

variable [CancelMonoid A] [HasMulAntidiagonal A] {p q : A × A} {n : A}

/-- A point in the mulAntidiagonal is determined by its first coordinate.

See also `Finset.mulAntidiagonal_congr'`. -/
@[to_additive
/-- A point in the antidiagonal is determined by its first coordinate.

See also `Finset.antidiagonal_congr'`. -/]
/-
**Finset.HasMulAntidiagonal.mulAntidiagonal_congr** 是 Mathlib 中的一个定理，位于命名空间 `Fin
set.HasMulAntidiagonal`。
形式化陈述：mulAntidiagonal_congr (hp : p in mulAntidiagonal n) (hq : q in mulAntidiag
onal n) : p = q ↔ p.1 = q.1
参数：hp : p in mulAntidiagonal n；hq : q in mulAntidiagonal n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_right_inj`：mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.HasMulAntidiagonal.mem_mulAntidiagonal`：∀ {A : Type u_1} {inst : 
Monoid A} [self : Finset.HasMulAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset
.HasMulAntidiagonal.mulAntidiagonal…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mulAntidiagonal_congr (hp : p ∈ mulAntidiagonal n) (hq : q ∈ mulAntidiagonal n) :
    p = q ↔ p.1 = q.1 := by
  refine ⟨congr_arg Prod.fst, fun h ↦ Prod.ext h ((mul_right_inj q.fst).mp ?_)⟩
  rw [mem_mulAntidiagonal] at hp hq
  rw [hq, ← h, hp]

/-- A point in the mulAntidiagonal is determined by its first co-ordinate (subtype version of
`Finset.mulAntidiagonal_congr`). This lemma is used by the `ext` tactic. -/
@[to_additive (attr := ext)
/-- A point in the antidiagonal is determined by its first co-ordinate (subtype version of
`Finset.antidiagonal_congr`). This lemma is used by the `ext` tactic. -/]
/-
**Finset.HasMulAntidiagonal.mulAntidiagonal_subtype_ext** 是 Mathlib 中的一个定理，位于命名空
间 `Finset.HasMulAntidiagonal`。
形式化陈述：mulAntidiagonal_subtype_ext {p q : mulAntidiagonal n} (h : p.val.1 = q.val
.1) : p = q
参数：h : p.val.1 = q.val.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.HasMulAntidiagonal.mulAntidiagonal_congr`：mulAntidiagonal_congr (
hp : p in mulAntidiagonal n) (hq : q in mulAntidiagonal n) : p = q ↔ p.1 = q.1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem mulAntidiagonal_subtype_ext {p q : mulAntidiagonal n} (h : p.val.1 = q.val.1) : p = q :=
  Subtype.ext ((mulAntidiagonal_congr p.prop q.prop).mpr h)

end CancelMonoid

section CancelCommMonoid
variable [CancelCommMonoid A] [HasMulAntidiagonal A] {p q : A × A} {n : A}

/-- A point in the mulAntidiagonal is determined by its second coordinate.

See also `Finset.mulAntidiagonal_congr`. -/
@[to_additive /-- A point in the antidiagonal is determined by its second coordinate.

See also `Finset.antidiagonal_congr`. -/]
/-
**Finset.HasMulAntidiagonal.mulAntidiagonal_congr'** 是 Mathlib 中的一个引理，位于命名空间 `Fi
nset.HasMulAntidiagonal`。
形式化陈述：mulAntidiagonal_congr' (hp : p in mulAntidiagonal n) (hq : q in mulAntidia
gonal n) : p = q ↔ p.2 = q.2
参数：hp : p in mulAntidiagonal n；hq : q in mulAntidiagonal n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.swap_inj`：∀ {α : Type u_1} {β : Type u_2} {p q : α × β}, p.swap = q
.swap ↔ p = q
· 使用定理 `Finset.HasMulAntidiagonal.mulAntidiagonal_congr`：mulAntidiagonal_congr (
hp : p in mulAntidiagonal n) (hq : q in mulAntidiagonal n) : p = q ↔ p.1 = q.1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.HasMulAntidiagonal.swap_mem_mulAntidiagonal`：swap_mem_mulAntidiag
onal [CommMonoid A] [HasMulAntidiagonal A] {n : A} {xy : A × A} : xy.swap in mul
Antidiagonal n ↔ xy in mulAntidiagonal n
-/
lemma mulAntidiagonal_congr' (hp : p ∈ mulAntidiagonal n) (hq : q ∈ mulAntidiagonal n) :
    p = q ↔ p.2 = q.2 := by
  rw [← Prod.swap_inj]
  exact mulAntidiagonal_congr (swap_mem_mulAntidiagonal.2 hp) (swap_mem_mulAntidiagonal.2 hq)

end CancelCommMonoid

section CanonicallyOrderedMul

variable [CommMonoid A] [PartialOrder A] [CanonicallyOrderedMul A] [HasMulAntidiagonal A]

@[to_additive (attr := simp)]
/-
**Finset.HasMulAntidiagonal.mulAntidiagonal_one** 是 Mathlib 中的一个定理，位于命名空间 `Finse
t.HasMulAntidiagonal`。
形式化陈述：mulAntidiagonal_one : mulAntidiagonal (1 : A) = {(1, 1)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mulAntidiagonal_one : mulAntidiagonal (1 : A) = {(1, 1)} := by
  ext ⟨x, y⟩
  simp

@[to_additive]
/-
**Finset.HasMulAntidiagonal.mulAntidiagonal.fst_le** 是 Mathlib 中的一个定理，位于命名空间 `Fi
nset.HasMulAntidiagonal.mulAntidiagonal`。
形式化陈述：∀ {A : Type u_1} [inst : CommMonoid A] [inst_1 : PartialOrder A] [Canonica
llyOrderedMul A]   [inst_3 : Finset.HasMulAntidiagonal A] {n : A} {kl : A × A}, 
  kl ∈ Finset.HasMulAntidiagonal.mulAntidiagonal n → kl.1 ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_exists_mul`：le_iff_exists_mul : a <= b ↔ exists c, b = a * c
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.HasMulAntidiagonal.mem_mulAntidiagonal`：∀ {A : Type u_1} {inst : 
Monoid A} [self : Finset.HasMulAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset
.HasMulAntidiagonal.mulAntidiagonal…
-/
theorem mulAntidiagonal.fst_le {n : A} {kl : A × A} (hlk : kl ∈ mulAntidiagonal n) : kl.1 ≤ n := by
  rw [le_iff_exists_mul]
  use kl.2
  rwa [mem_mulAntidiagonal, eq_comm] at hlk

@[to_additive]
/-
**Finset.HasMulAntidiagonal.mulAntidiagonal.snd_le** 是 Mathlib 中的一个定理，位于命名空间 `Fi
nset.HasMulAntidiagonal.mulAntidiagonal`。
形式化陈述：∀ {A : Type u_1} [inst : CommMonoid A] [inst_1 : PartialOrder A] [Canonica
llyOrderedMul A]   [inst_3 : Finset.HasMulAntidiagonal A] {n : A} {kl : A × A}, 
  kl ∈ Finset.HasMulAntidiagonal.mulAntidiagonal n → kl.2 ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_exists_mul`：le_iff_exists_mul : a <= b ↔ exists c, b = a * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.HasMulAntidiagonal.mem_mulAntidiagonal`：∀ {A : Type u_1} {inst : 
Monoid A} [self : Finset.HasMulAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset
.HasMulAntidiagonal.mulAntidiagonal…
-/
theorem mulAntidiagonal.snd_le {n : A} {kl : A × A} (hlk : kl ∈ mulAntidiagonal n) : kl.2 ≤ n := by
  rw [le_iff_exists_mul]
  use kl.1
  rwa [mem_mulAntidiagonal, eq_comm, mul_comm] at hlk

end CanonicallyOrderedMul

end HasMulAntidiagonal

namespace HasAntidiagonal
section OrderedSub

variable [AddCommMonoid A] [PartialOrder A] [CanonicallyOrderedAdd A] [Sub A] [OrderedSub A]
variable [AddLeftReflectLE A]
variable [HasAntidiagonal A]

/-
**Finset.HasAntidiagonal.filter_fst_eq_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `F
inset.HasAntidiagonal`。
形式化陈述：filter_fst_eq_antidiagonal (n m : A) [DecidablePred (· = m)] [Decidable (m
 <= n)] : {x in antidiagonal n | x.fst = m} = if m <= n then {(m, n - m)} else ∅
参数：n m : A；· = m；m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
· 使用定理 `ite_prop_iff_or`：ite_prop_iff_or : (if P then Q else R) ↔ (P ∧ Q ∨ ¬P ∧ 
R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_right_comm`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem filter_fst_eq_antidiagonal (n m : A) [DecidablePred (· = m)] [Decidable (m ≤ n)] :
    {x ∈ antidiagonal n | x.fst = m} = if m ≤ n then {(m, n - m)} else ∅ := by
  ext ⟨a, b⟩
  suffices a = m → (a + b = n ↔ m ≤ n ∧ b = n - m) by
    rw [mem_filter, mem_antidiagonal, apply_ite (fun n ↦ (a, b) ∈ n), mem_singleton,
      Prod.mk_inj, ite_prop_iff_or]
    simpa [← and_assoc, @and_right_comm _ (a = _), and_congr_left_iff]
  rintro rfl
  constructor
  · rintro rfl
    exact ⟨le_add_right le_rfl, (add_tsub_cancel_left _ _).symm⟩
  · rintro ⟨h, rfl⟩
    exact add_tsub_cancel_of_le h
/-
**Finset.HasAntidiagonal.filter_snd_eq_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `F
inset.HasAntidiagonal`。
形式化陈述：filter_snd_eq_antidiagonal (n m : A) [DecidablePred (· = m)] [Decidable (m
 <= n)] : {x in antidiagonal n | x.snd = m} = if m <= n then {(n - m, m)} else ∅
参数：n m : A；· = m；m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.swap_injective`：swap_injective : Function.Injective (@swap α β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.HasAntidiagonal.map_swap_antidiagonal`：∀ {A : Type u_1} [inst : A
ddCommMonoid A] [inst_1 : Finset.HasAntidiagonal A] {n : A},   Finset.map { toFu
n := Prod.swap, inj' := ⋯ } (Finse…
· 使用定理 `Finset.filter_map`：filter_map {p : β -> Prop} [DecidablePred p] : (s.map
 f).filter p = (s.filter (p ∘ f)).map f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.HasAntidiagonal.filter_fst_eq_antidiagonal`：filter_fst_eq_antidia
gonal (n m : A) [DecidablePred (· = m)] [Decidable (m <= n)] : {x in antidiagona
l n | x.fst = m} = if m <= n then {(m, …
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Finset.map_singleton`：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f
 a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_snd_eq_antidiagonal (n m : A) [DecidablePred (· = m)] [Decidable (m ≤ n)] :
    {x ∈ antidiagonal n | x.snd = m} = if m ≤ n then {(n - m, m)} else ∅ := by
  rw [← map_swap_antidiagonal, filter_map]
  simp [filter_fst_eq_antidiagonal, apply_ite (Finset.map _)]

end OrderedSub

end HasAntidiagonal

namespace HasMulAntidiagonal

/-- The disjoint union of mulAntidiagonals `Σ (n : A), mulAntidiagonal n` is equivalent to the
  product `A × A`. This is such an equivalence, obtained by mapping `(n, (k, l))` to `(k, l)`. -/
@[to_additive (attr := simps) sigmaAntidiagonalEquivProd
/-- The disjoint union of antidiagonals `Σ (n : A), antidiagonal n` is equivalent to the
  product `A × A`. This is such an equivalence, obtained by mapping `(n, (k, l))` to `(k, l)`. -/]
/-
**Finset.HasMulAntidiagonal.sigmaMulAntidiagonalEquivProd** 是 Mathlib 中的一个定义，位于命
名空间 `Finset.HasMulAntidiagonal`。
形式化陈述：sigmaMulAntidiagonalEquivProd [Monoid A] [HasMulAntidiagonal A] : (Σ n : A
, mulAntidiagonal n) ≃ A × A where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def sigmaMulAntidiagonalEquivProd [Monoid A] [HasMulAntidiagonal A] :
    (Σ n : A, mulAntidiagonal n) ≃ A × A where
  toFun x := x.2
  invFun x := ⟨x.1 * x.2, x, mem_mulAntidiagonal.mpr rfl⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [mem_mulAntidiagonal] at h
    exact Sigma.subtype_ext h rfl

section

variable {A : Type*}
  [CommMonoid A] [PartialOrder A] [CanonicallyOrderedMul A]
  [LocallyFiniteOrderBot A] [DecidableEq A]

/-- In a canonically ordered multiplicative monoid, the mulAntidiagonal can be constructed by
filtering.

Note that this is not an instance, as for sometimes a more efficient algorithm is available. -/
@[to_additive
/-- In a canonically ordered additive monoid, the antidiagonal can be construct by filtering.

Note that this is not an instance, as for some times a more efficient algorithm is available. -/]
/-
**Finset.HasMulAntidiagonal.mulAntidiagonalOfLocallyFinite** 是 Mathlib 中的一个缩写定义，
位于命名空间 `Finset.HasMulAntidiagonal`。
形式化陈述：mulAntidiagonalOfLocallyFinite : HasMulAntidiagonal A where mulAntidiagona
l n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev mulAntidiagonalOfLocallyFinite : HasMulAntidiagonal A where
  mulAntidiagonal n := {uv ∈ Iic n ×ˢ Iic n | uv.fst * uv.snd = n}
  mem_mulAntidiagonal {n} {a} := by
    simp only [mem_filter, and_iff_right_iff_imp]
    intro h
    simp [← h]

end

section Multiplicative

open Multiplicative

variable {A : Type*} [AddMonoid A] [HasAntidiagonal A]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Finset.HasMulAntidiagonal.** 是 Mathlib 中的一个实例，位于命名空间 `Finset.HasMulAntidiagona
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasMulAntidiagonal (Multiplicative A) where
  mulAntidiagonal a :=
    (antidiagonal (toAdd a)).map ⟨fun p ↦ (ofAdd p.1 , ofAdd p.2), fun _ _ h ↦ by aesop⟩
  mem_mulAntidiagonal {a p} := by aesop
/-
**Finset.HasMulAntidiagonal.mem_mulAntidiagonal_ofAdd_iff_toAdd_mem_antidiagonal
** 是 Mathlib 中的一个引理，位于命名空间 `Finset.HasMulAntidiagonal`。
形式化陈述：mem_mulAntidiagonal_ofAdd_iff_toAdd_mem_antidiagonal {a : A} {p : Multipli
cative A × Multiplicative A} : p in mulAntidiagonal (ofAdd a) ↔ (toAdd p.1, toAd
d p.2) in antidiagonal a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiplicative.ext_iff`：∀ {α : Type u} {a b : Multiplicative α}, a = b ↔
 Multiplicative.toAdd a = Multiplicative.toAdd b
· 使用定理 `toAdd_mul`：toAdd_mul [Add α] (x y : Multiplicative α) : (x * y).toAdd = 
x.toAdd + y.toAdd
· 使用定理 `toAdd_ofAdd`：toAdd_ofAdd (x : α) : (ofAdd x).toAdd = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_mulAntidiagonal_ofAdd_iff_toAdd_mem_antidiagonal {a : A}
    {p : Multiplicative A × Multiplicative A} :
    p ∈ mulAntidiagonal (ofAdd a) ↔ (toAdd p.1, toAdd p.2) ∈ antidiagonal a := by
  simp only [mem_mulAntidiagonal, mem_antidiagonal]
  rw [Multiplicative.ext_iff, toAdd_mul, toAdd_ofAdd]

end Multiplicative

end HasMulAntidiagonal

end Finset

