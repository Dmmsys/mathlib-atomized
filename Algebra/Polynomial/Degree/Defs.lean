/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Degree
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Nat.Cast.WithTop
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.SuccPred.WithBot

/-!
# Degree of univariate polynomials

## Main definitions

* `Polynomial.degree`: the degree of a polynomial, where `0` has degree `⊥`
* `Polynomial.natDegree`: the degree of a polynomial, where `0` has degree `0`
* `Polynomial.leadingCoeff`: the leading coefficient of a polynomial
* `Polynomial.Monic`: a polynomial is monic if its leading coefficient is 1
* `Polynomial.nextCoeff`: the next coefficient after the leading coefficient

## Main results

* `Polynomial.degree_eq_natDegree`: the degree and natDegree coincide for nonzero polynomials
-/

@[expose] public section

open Finset

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
/-
**Polynomial.degree** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：degree (p : R[X]) : WithBot Nat
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in
 `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appear
s in `p`, otherwise
`degree 0 = ⊥`.
-/
def degree (p : R[X]) : WithBot ℕ :=
  p.support.max

/-- `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`. -/
/-
**Polynomial.natDegree** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：natDegree (p : R[X]) : Nat
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
-/
def natDegree (p : R[X]) : ℕ :=
  (degree p).unbotD 0

/-- `leadingCoeff p` gives the coefficient of the highest power of `X` in `p`. -/
/-
**Polynomial.leadingCoeff** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff (p : R[X]) : R
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`leadingCoeff p` gives the coefficient of the highest power of `X` in `p`.
-/
def leadingCoeff (p : R[X]) : R :=
  coeff p (natDegree p)

/-- a polynomial is `Monic` if its leading coefficient is 1 -/
/-
**Polynomial.Monic** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：Monic (p : R[X])
参数：p : R[X]。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
a polynomial is `Monic` if its leading coefficient is 1
-/
def Monic (p : R[X]) :=
  leadingCoeff p = (1 : R)
/-
**Polynomial.Monic.def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic ↔ p.leading
Coeff = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Monic.def : Monic p ↔ leadingCoeff p = 1 :=
  Iff.rfl
/-
**Polynomial.Monic.decidable** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Monic`。
形式化陈述：{R : Type u} → [inst : Semiring R] → {p : Polynomial R} → [DecidableEq R] 
→ Decidable p.Monic
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Monic.decidable [DecidableEq R] : Decidable (Monic p) :=
  inferInstanceAs <| Decidable (p.leadingCoeff = 1)

@[simp]
/-
**Polynomial.Monic.leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → p.leading
Coeff = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monic.leadingCoeff {p : R[X]} (hp : p.Monic) : leadingCoeff p = 1 :=
  hp
/-
**Polynomial.Monic.coeff_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → p.coeff p
.natDegree = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monic.coeff_natDegree {p : R[X]} (hp : p.Monic) : p.coeff p.natDegree = 1 :=
  hp

@[simp, grind =]
/-
**Polynomial.degree_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_zero : degree (0 : R[X]) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem degree_zero : degree (0 : R[X]) = ⊥ :=
  rfl

@[simp, grind =]
/-
**Polynomial.natDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_zero : natDegree (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natDegree_zero : natDegree (0 : R[X]) = 0 :=
  rfl

@[simp]
/-
**Polynomial.coeff_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_natDegree : coeff p (natDegree p) = leadingCoeff p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_natDegree : coeff p (natDegree p) = leadingCoeff p :=
  rfl

@[simp]
/-
**Polynomial.degree_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_eq_bot : degree p = ⊥ ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.support_eq_empty`：support_eq_empty : p.support = ∅ ↔ p = 0
· 使用定理 `Finset.max_eq_bot`：max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩
/-
**Polynomial.degree_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_ne_bot : degree p != ⊥ ↔ p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
-/
theorem degree_ne_bot : degree p ≠ ⊥ ↔ p ≠ 0 := degree_eq_bot.not
/-
**Polynomial.degree_eq_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_eq_natDegree (hp : p != 0) : degree p = (natDegree p : WithBot Nat)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.eq_none_iff_forall_not_mem`：∀ {α : Type u_1} {o : Option α}, o = 
none ↔ ∀ (a : α), a ∉ o
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
-/
theorem degree_eq_natDegree (hp : p ≠ 0) : degree p = (natDegree p : WithBot ℕ) := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  have hn : degree p = some n := Classical.not_not.1 hn
  rw [natDegree, hn]; rfl
/-
**Polynomial.degree_eq_iff_natDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_eq_iff_natDegree_eq {p : R[X]} {n : Nat} (hp : p != 0) : p.degree =
 n ↔ p.natDegree = n
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
-/
theorem degree_eq_iff_natDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.degree = n ↔ p.natDegree = n := by rw [degree_eq_natDegree hp]; exact WithBot.coe_eq_coe
/-
**Polynomial.degree_eq_iff_natDegree_eq_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：degree_eq_iff_natDegree_eq_of_pos {p : R[X]} {n : Nat} (hn : 0 < n) : p.de
gree = n ↔ p.natDegree = n
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq`：degree_eq_iff_natDegree_eq {p : R
[X]} {n : Nat} (hp : p != 0) : p.degree = n ↔ p.natDegree = n
-/
theorem degree_eq_iff_natDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.degree = n ↔ p.natDegree = n := by
  obtain rfl | h := eq_or_ne p 0
  · simp [hn.ne]
  · exact degree_eq_iff_natDegree_eq h
/-
**Polynomial.natDegree_eq_of_degree_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：natDegree_eq_of_degree_eq_some {p : R[X]} {n : Nat} (h : degree p = n) : n
atDegree p = n
参数：h : degree p = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `WithBot.unbotD_coe`：unbotD_coe {α} (d x : α) : unbotD d x = x
-/
theorem natDegree_eq_of_degree_eq_some {p : R[X]} {n : ℕ} (h : degree p = n) : natDegree p = n := by
  rw [natDegree, h, Nat.cast_withBot, WithBot.unbotD_coe]
/-
**Polynomial.degree_ne_of_natDegree_ne** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_ne_of_natDegree_ne {n : Nat} : p.natDegree != n -> degree p != n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
-/
theorem degree_ne_of_natDegree_ne {n : ℕ} : p.natDegree ≠ n → degree p ≠ n :=
  mt natDegree_eq_of_degree_eq_some

@[simp]
/-
**Polynomial.degree_le_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_le_natDegree : degree p <= natDegree p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem degree_le_natDegree : degree p ≤ natDegree p :=
  WithBot.giUnbotDBot.gc.le_u_l _
/-
**Polynomial.natDegree_eq_of_degree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_eq_of_degree_eq [Semiring S] {q : S[X]} (h : degree p = degree q
) : natDegree p = natDegree q
参数：h : degree p = degree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem natDegree_eq_of_degree_eq [Semiring S] {q : S[X]} (h : degree p = degree q) :
    natDegree p = natDegree q := by unfold natDegree; rw [h]
/-
**Polynomial.le_degree_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_degree_of_ne_zero (h : coeff p n != 0) : (n : WithBot Nat) <= degree p
参数：h : coeff p n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
-/
theorem le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : WithBot ℕ) ≤ degree p := by
  rw [Nat.cast_withBot]
  exact Finset.le_sup (mem_support_iff.2 h)
/-
**Polynomial.degree_mono** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_mono [Semiring S] {f : R[X]} {g : S[X]} (h : f.support subseteq g.s
upport) : f.degree <= g.degree
参数：h : f.support subseteq g.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
-/
theorem degree_mono [Semiring S] {f : R[X]} {g : S[X]} (h : f.support ⊆ g.support) :
    f.degree ≤ g.degree :=
  Finset.sup_mono h
/-
**Polynomial.degree_le_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_le_degree (h : coeff q (natDegree p) != 0) : degree p <= degree q
参数：h : coeff q (natDegree p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.le_degree_of_ne_zero`：le_degree_of_ne_zero (h : coeff p n != 
0) : (n : WithBot Nat) <= degree p
-/
theorem degree_le_degree (h : coeff q (natDegree p) ≠ 0) : degree p ≤ degree q := by
  by_cases hp : p = 0
  · rw [hp, degree_zero]
    exact bot_le
  · rw [degree_eq_natDegree hp]
    exact le_degree_of_ne_zero h
/-
**Polynomial.natDegree_le_iff_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_le_iff_degree_le {n : Nat} : natDegree p <= n ↔ degree p <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.unbotD_le_iff`：unbotD_le_iff (hx : x = ⊥ -> a <= b) : x.unbotD a
 <= b ↔ x <= b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem natDegree_le_iff_degree_le {n : ℕ} : natDegree p ≤ n ↔ degree p ≤ n :=
  WithBot.unbotD_le_iff (fun _ ↦ bot_le)
/-
**Polynomial.natDegree_lt_iff_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_lt_iff_degree_lt (hp : p != 0) : p.natDegree < n ↔ p.degree < ↑n
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.unbotD_lt_iff`：unbotD_lt_iff (hx : x = ⊥ -> a < b) : x.unbotD a 
< b ↔ x < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
-/
theorem natDegree_lt_iff_degree_lt (hp : p ≠ 0) : p.natDegree < n ↔ p.degree < ↑n :=
  WithBot.unbotD_lt_iff (absurd · (degree_eq_bot.not.mpr hp))

alias ⟨degree_le_of_natDegree_le, natDegree_le_of_degree_le⟩ := natDegree_le_iff_degree_le
/-
**Polynomial.natDegree_le_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_le_natDegree [Semiring S] {q : S[X]} (hpq : p.degree <= q.degree
) : p.natDegree <= q.natDegree
参数：hpq : p.degree <= q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem natDegree_le_natDegree [Semiring S] {q : S[X]} (hpq : p.degree ≤ q.degree) :
    p.natDegree ≤ q.natDegree :=
  WithBot.giUnbotDBot.gc.monotone_l hpq

@[simp]
/-
**Polynomial.degree_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_C (ha : a != 0) : degree (C a) = (0 : WithBot Nat)
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R), p.degree = p.support.max
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.monomial_zero_left`：monomial_zero_left ⦃a : R⦄ : monomial 0 a
 = C a
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
· 使用定理 `Finset.max_eq_sup_coe`：max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑)
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `WithBot.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
-/
theorem degree_C (ha : a ≠ 0) : degree (C a) = (0 : WithBot ℕ) := by
  rw [degree, ← monomial_zero_left, support_monomial 0 ha, max_eq_sup_coe, sup_singleton,
    WithBot.coe_zero]
/-
**Polynomial.degree_C_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_le : degree (C a) <= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem degree_C_le : degree (C a) ≤ 0 := by
  by_cases h : a = 0
  · rw [h, C_0]
    exact bot_le
  · rw [degree_C h]
/-
**Polynomial.degree_C_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_lt : degree (C a) < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem degree_C_lt : degree (C a) < 1 :=
  degree_C_le.trans_lt <| WithBot.coe_lt_coe.mpr zero_lt_one
/-
**Polynomial.degree_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_one_le : degree (1 : R[X]) <= (0 : WithBot Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
-/
theorem degree_one_le : degree (1 : R[X]) ≤ (0 : WithBot ℕ) := by rw [← C_1]; exact degree_C_le

@[simp, grind =]
/-
**Polynomial.natDegree_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_C (a : R) : natDegree (C a) = 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `WithBot.unbotD_bot`：unbotD_bot {α} (d : α) : unbotD d ⊥ = d
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `WithBot.unbotD_zero`：∀ {α : Type u} [inst : Zero α] (d : α), WithBot.unb
otD d 0 = 0
-/
theorem natDegree_C (a : R) : natDegree (C a) = 0 := by
  by_cases ha : a = 0
  · have : C a = 0 := by rw [ha, C_0]
    rw [natDegree, degree_eq_bot.2 this, WithBot.unbotD_bot]
  · rw [natDegree, degree_C ha, WithBot.unbotD_zero]

@[simp, grind =]
/-
**Polynomial.natDegree_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_one : natDegree (1 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
-/
theorem natDegree_one : natDegree (1 : R[X]) = 0 :=
  natDegree_C 1

@[simp, grind =]
/-
**Polynomial.natDegree_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_natCast (n : Nat) : natDegree (n : R[X]) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_natCast (n : ℕ) : natDegree (n : R[X]) = 0 := by
  simp only [← C_eq_natCast, natDegree_C]

@[simp]
/-
**Polynomial.natDegree_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_ofNat (n : Nat) [Nat.AtLeastTwo n] : natDegree (ofNat(n) : R[X])
 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_natCast`：natDegree_natCast (n : Nat) : natDegree (n
 : R[X]) = 0
-/
theorem natDegree_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
    natDegree (ofNat(n) : R[X]) = 0 :=
  natDegree_natCast _
/-
**Polynomial.degree_natCast_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_natCast_le (n : Nat) : degree (n : R[X]) <= 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_le_of_natDegree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.natDegree ≤ n → p.degree ≤ ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_natCast`：natDegree_natCast (n : Nat) : natDegree (n
 : R[X]) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem degree_natCast_le (n : ℕ) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

@[simp]
/-
**Polynomial.degree_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_monomial (n : Nat) (ha : a != 0) : degree (monomial n a) = n
参数：n : Nat；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R), p.degree = p.support.max
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
· 使用定理 `Finset.max_singleton`：max_singleton {a : α} : Finset.max {a} = (a : With
Bot α)
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
-/
theorem degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n := by
  rw [degree, support_monomial n ha, max_singleton, Nat.cast_withBot]

@[simp]
/-
**Polynomial.degree_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_mul_X_pow (n : Nat) (ha : a != 0) : degree (C a * X ^ n) = n
参数：n : Nat；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.degree_monomial`：degree_monomial (n : Nat) (ha : a != 0) : de
gree (monomial n a) = n
-/
theorem degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : degree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, degree_monomial n ha]
/-
**Polynomial.degree_C_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_mul_X (ha : a != 0) : degree (C a * X) = 1
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.degree_C_mul_X_pow`：degree_C_mul_X_pow (n : Nat) (ha : a != 0
) : degree (C a * X ^ n) = n
-/
theorem degree_C_mul_X (ha : a ≠ 0) : degree (C a * X) = 1 := by
  simpa only [pow_one] using! degree_C_mul_X_pow 1 ha
/-
**Polynomial.degree_monomial_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_monomial_le (n : Nat) (a : R) : degree (monomial n a) <= n
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.degree_monomial`：degree_monomial (n : Nat) (ha : a != 0) : de
gree (monomial n a) = n
-/
theorem degree_monomial_le (n : ℕ) (a : R) : degree (monomial n a) ≤ n :=
  letI := Classical.decEq R
  if h : a = 0 then by rw [h, (monomial n).map_zero, degree_zero]; exact bot_le
  else le_of_eq (degree_monomial n h)
/-
**Polynomial.degree_C_mul_X_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_mul_X_pow_le (n : Nat) (a : R) : degree (C a * X ^ n) <= n
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.degree_monomial_le`：degree_monomial_le (n : Nat) (a : R) : de
gree (monomial n a) <= n
-/
theorem degree_C_mul_X_pow_le (n : ℕ) (a : R) : degree (C a * X ^ n) ≤ n := by
  rw [C_mul_X_pow_eq_monomial]
  apply degree_monomial_le
/-
**Polynomial.degree_C_mul_X_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_mul_X_le (a : R) : degree (C a * X) <= 1
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.degree_C_mul_X_pow_le`：degree_C_mul_X_pow_le (n : Nat) (a : R
) : degree (C a * X ^ n) <= n
-/
theorem degree_C_mul_X_le (a : R) : degree (C a * X) ≤ 1 := by
  simpa only [pow_one] using! degree_C_mul_X_pow_le 1 a

@[simp, grind =]
/-
**Polynomial.natDegree_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_C_mul_X_pow (n : Nat) (a : R) (ha : a != 0) : natDegree (C a * X
 ^ n) = n
参数：n : Nat；a : R；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.degree_C_mul_X_pow`：degree_C_mul_X_pow (n : Nat) (ha : a != 0
) : degree (C a * X ^ n) = n
-/
theorem natDegree_C_mul_X_pow (n : ℕ) (a : R) (ha : a ≠ 0) : natDegree (C a * X ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[simp, grind =]
/-
**Polynomial.natDegree_C_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_C_mul_X (a : R) (ha : a != 0) : natDegree (C a * X) = 1
参数：a : R；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.natDegree_C_mul_X_pow`：natDegree_C_mul_X_pow (n : Nat) (a : R
) (ha : a != 0) : natDegree (C a * X ^ n) = n
-/
theorem natDegree_C_mul_X (a : R) (ha : a ≠ 0) : natDegree (C a * X) = 1 := by
  simpa only [pow_one] using natDegree_C_mul_X_pow 1 a ha

@[simp]
/-
**Polynomial.natDegree_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_monomial [DecidableEq R] (i : Nat) (r : R) : natDegree (monomial
 i r) = if r = 0 then 0 else i
参数：i : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.natDegree_C_mul_X_pow`：natDegree_C_mul_X_pow (n : Nat) (a : R
) (ha : a != 0) : natDegree (C a * X ^ n) = n
-/
theorem natDegree_monomial [DecidableEq R] (i : ℕ) (r : R) :
    natDegree (monomial i r) = if r = 0 then 0 else i := by
  split_ifs with hr
  · simp [hr]
  · rw [← C_mul_X_pow_eq_monomial, natDegree_C_mul_X_pow i r hr]
/-
**Polynomial.natDegree_monomial_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_monomial_le (a : R) {m : Nat} : (monomial m a).natDegree <= m
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_monomial`：natDegree_monomial [DecidableEq R] (i : N
at) (r : R) : natDegree (monomial i r) = if r = 0 then 0 else i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem natDegree_monomial_le (a : R) {m : ℕ} : (monomial m a).natDegree ≤ m := by
  classical
  rw [Polynomial.natDegree_monomial]
  split_ifs
  exacts [Nat.zero_le _, le_rfl]
/-
**Polynomial.natDegree_monomial_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_monomial_eq (i : Nat) {r : R} (r0 : r != 0) : (monomial i r).nat
Degree = i
参数：i : Nat；r0 : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.natDegree_monomial`：natDegree_monomial [DecidableEq R] (i : N
at) (r : R) : natDegree (monomial i r) = if r = 0 then 0 else i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem natDegree_monomial_eq (i : ℕ) {r : R} (r0 : r ≠ 0) : (monomial i r).natDegree = i :=
  letI := Classical.decEq R
  Eq.trans (natDegree_monomial _ _) (if_neg r0)
/-
**Polynomial.coeff_ne_zero_of_eq_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_ne_zero_of_eq_degree (hn : degree p = n) : coeff p n != 0
参数：hn : degree p = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `Finset.mem_of_max`：mem_of_max {s : Finset α} : forall {a : α}, s.max = a
 -> a in s
-/
theorem coeff_ne_zero_of_eq_degree (hn : degree p = n) : coeff p n ≠ 0 := fun h =>
  mem_support_iff.mp (mem_of_max hn) h
/-
**Polynomial.degree_X_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_X_pow_le (n : Nat) : degree (X ^ n : R[X]) <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.degree_C_mul_X_pow_le`：degree_C_mul_X_pow_le (n : Nat) (a : R
) : degree (C a * X ^ n) <= n
-/
theorem degree_X_pow_le (n : ℕ) : degree (X ^ n : R[X]) ≤ n := by
  simpa only [C_1, one_mul] using degree_C_mul_X_pow_le n (1 : R)
/-
**Polynomial.degree_X_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_X_le : degree (X : R[X]) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_monomial_le`：degree_monomial_le (n : Nat) (a : R) : de
gree (monomial n a) <= n
-/
theorem degree_X_le : degree (X : R[X]) ≤ 1 :=
  degree_monomial_le _ _
/-
**Polynomial.natDegree_X_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_X_le : (X : R[X]).natDegree <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
· 使用定理 `Polynomial.degree_X_le`：degree_X_le : degree (X : R[X]) <= 1
-/
theorem natDegree_X_le : (X : R[X]).natDegree ≤ 1 :=
  natDegree_le_of_degree_le degree_X_le
/-
**Polynomial.withBotSucc_degree_eq_natDegree_add_one** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：withBotSucc_degree_eq_natDegree_add_one (h : p != 0) : p.degree.succ = p.n
atDegree + 1
参数：h : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `WithBot.succ_coe`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBo
t α] [inst_2 : SuccOrder α] (a : α), (↑a).succ = Order.succ a
-/
theorem withBotSucc_degree_eq_natDegree_add_one (h : p ≠ 0) : p.degree.succ = p.natDegree + 1 := by
  rw [degree_eq_natDegree h]
  exact WithBot.succ_coe p.natDegree

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
/-
**Polynomial.degree_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_one : degree (1 : R[X]) = (0 : WithBot Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem degree_one : degree (1 : R[X]) = (0 : WithBot ℕ) :=
  degree_C one_ne_zero

@[simp]
/-
**Polynomial.degree_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_X : degree (X : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_monomial`：degree_monomial (n : Nat) (ha : a != 0) : de
gree (monomial n a) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem degree_X : degree (X : R[X]) = 1 :=
  degree_monomial _ one_ne_zero

@[simp]
/-
**Polynomial.natDegree_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_X : (X : R[X]).natDegree = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.degree_X`：degree_X : degree (X : R[X]) = 1
-/
theorem natDegree_X : (X : R[X]).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some degree_X

end NonzeroSemiring

section Ring

variable [Ring R]

@[simp]
/-
**Polynomial.degree_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_neg (p : R[X]) : degree (-p) = degree p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_neg`：support_neg {p : R[X]} : (-p).support = p.suppor
t
-/
theorem degree_neg (p : R[X]) : degree (-p) = degree p := by unfold degree; rw [support_neg]
/-
**Polynomial.degree_neg_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_neg_le_of_le {a : WithBot Nat} {p : R[X]} (hp : degree p <= a) : de
gree (-p) <= a
参数：hp : degree p <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
-/
theorem degree_neg_le_of_le {a : WithBot ℕ} {p : R[X]} (hp : degree p ≤ a) : degree (-p) ≤ a :=
  p.degree_neg.le.trans hp

@[simp]
/-
**Polynomial.natDegree_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_neg (p : R[X]) : natDegree (-p) = natDegree p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_neg (p : R[X]) : natDegree (-p) = natDegree p := by simp [natDegree]
/-
**Polynomial.natDegree_neg_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_neg_le_of_le {p : R[X]} (hp : natDegree p <= m) : natDegree (-p)
 <= m
参数：hp : natDegree p <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
-/
theorem natDegree_neg_le_of_le {p : R[X]} (hp : natDegree p ≤ m) : natDegree (-p) ≤ m :=
  (natDegree_neg p).le.trans hp

@[simp]
/-
**Polynomial.natDegree_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_intCast (n : Int) : natDegree (n : R[X]) = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_eq_intCast`：C_eq_intCast (n : Int) : C (n : R) = n
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
-/
theorem natDegree_intCast (n : ℤ) : natDegree (n : R[X]) = 0 := by
  rw [← C_eq_intCast, natDegree_C]
/-
**Polynomial.degree_intCast_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_intCast_le (n : Int) : degree (n : R[X]) <= 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_le_of_natDegree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.natDegree ≤ n → p.degree ≤ ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_intCast`：natDegree_intCast (n : Int) : natDegree (n
 : R[X]) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem degree_intCast_le (n : ℤ) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

@[simp]
/-
**Polynomial.leadingCoeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_neg (p : R[X]) : (-p).leadingCoeff = -p.leadingCoeff
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Polynomial.coeff_neg`：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -c
oeff p n
-/
theorem leadingCoeff_neg (p : R[X]) : (-p).leadingCoeff = -p.leadingCoeff := by
  rw [leadingCoeff, leadingCoeff, natDegree_neg, coeff_neg]

end Ring

section Semiring

variable [Semiring R] {p : R[X]}

/-- The second-highest coefficient, or 0 for constants -/
/-
**Polynomial.nextCoeff** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff (p : R[X]) : R
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second-highest coefficient, or 0 for constants
-/
def nextCoeff (p : R[X]) : R :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)
/-
**Polynomial.nextCoeff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_eq_zero : p.nextCoeff = 0 ↔ p.natDegree = 0 ∨ 0 < p.natDegree ∧ 
p.coeff (p.natDegree - 1) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nextCoeff_eq_zero :
    p.nextCoeff = 0 ↔ p.natDegree = 0 ∨ 0 < p.natDegree ∧ p.coeff (p.natDegree - 1) = 0 := by
  simp [nextCoeff, or_iff_not_imp_left, pos_iff_ne_zero]; simp_all
/-
**Polynomial.nextCoeff_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_ne_zero : p.nextCoeff != 0 ↔ p.natDegree != 0 ∧ p.coeff (p.natDe
gree - 1) != 0
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
lemma nextCoeff_ne_zero : p.nextCoeff ≠ 0 ↔ p.natDegree ≠ 0 ∧ p.coeff (p.natDegree - 1) ≠ 0 := by
  simp [nextCoeff]

@[simp]
/-
**Polynomial.nextCoeff_C_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_C_eq_zero (c : R) : nextCoeff (C c) = 0
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nextCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R),   p.nextCoeff = if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 
1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nextCoeff_C_eq_zero (c : R) : nextCoeff (C c) = 0 := by
  rw [nextCoeff]
  simp
/-
**Polynomial.nextCoeff_of_natDegree_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_of_natDegree_pos (hp : 0 < p.natDegree) : nextCoeff p = p.coeff 
(p.natDegree - 1)
参数：hp : 0 < p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nextCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R),   p.nextCoeff = if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 
1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem nextCoeff_of_natDegree_pos (hp : 0 < p.natDegree) :
    nextCoeff p = p.coeff (p.natDegree - 1) := by
  rw [nextCoeff, if_neg]
  contrapose! hp
  simpa

variable {p q : R[X]} {ι : Type*}
/-
**Polynomial.degree_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_add_le (p q : R[X]) : degree (p + q) <= max (degree p) (degree q)
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.toFinsupp_add`：toFinsupp_add (a b : R[X]) : (a + b).toFinsupp
 = a.toFinsupp + b.toFinsupp
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_add_le`：sup_support_coeff_add_le : (f
 + g).coeff.support.sup degb <= f.coeff.support.sup degb ⊔ g.coeff.support.sup d
egb
-/
theorem degree_add_le (p q : R[X]) : degree (p + q) ≤ max (degree p) (degree q) := by
  simpa only [degree, ← support_toFinsupp, toFinsupp_add]
    using! AddMonoidAlgebra.sup_support_coeff_add_le _ _ _
/-
**Polynomial.degree_add_le_of_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_add_le_of_degree_le {p q : R[X]} {n : Nat} (hp : degree p <= n) (hq
 : degree q <= n) : degree (p + q) <= n
参数：hp : degree p <= n；hq : degree q <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
-/
theorem degree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : degree p ≤ n) (hq : degree q ≤ n) :
    degree (p + q) ≤ n :=
  (degree_add_le p q).trans <| max_le hp hq
/-
**Polynomial.degree_add_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_add_le_of_le {a b : WithBot Nat} (hp : degree p <= a) (hq : degree 
q <= b) : degree (p + q) <= max a b
参数：hp : degree p <= a；hq : degree q <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
-/
theorem degree_add_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p + q) ≤ max a b :=
  (p.degree_add_le q).trans <| max_le_max ‹_› ‹_›
/-
**Polynomial.natDegree_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_add_le (p q : R[X]) : natDegree (p + q) <= max (natDegree p) (na
tDegree q)
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem natDegree_add_le (p q : R[X]) : natDegree (p + q) ≤ max (natDegree p) (natDegree q) := by
  rcases le_max_iff.1 (degree_add_le p q) with h | h <;> simp [natDegree_le_natDegree h]
/-
**Polynomial.natDegree_add_le_of_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：natDegree_add_le_of_degree_le {p q : R[X]} {n : Nat} (hp : natDegree p <= 
n) (hq : natDegree q <= n) : natDegree (p + q) <= n
参数：hp : natDegree p <= n；hq : natDegree q <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_add_le`：natDegree_add_le (p q : R[X]) : natDegree (
p + q) <= max (natDegree p) (natDegree q)
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
-/
theorem natDegree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : natDegree p ≤ n)
    (hq : natDegree q ≤ n) : natDegree (p + q) ≤ n :=
  (natDegree_add_le p q).trans <| max_le hp hq
/-
**Polynomial.natDegree_add_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_add_le_of_le (hp : natDegree p <= m) (hq : natDegree q <= n) : n
atDegree (p + q) <= max m n
参数：hp : natDegree p <= m；hq : natDegree q <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_add_le`：natDegree_add_le (p q : R[X]) : natDegree (
p + q) <= max (natDegree p) (natDegree q)
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
-/
theorem natDegree_add_le_of_le (hp : natDegree p ≤ m) (hq : natDegree q ≤ n) :
    natDegree (p + q) ≤ max m n :=
  (p.natDegree_add_le q).trans <| max_le_max ‹_› ‹_›

@[simp]
/-
**Polynomial.leadingCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_zero : leadingCoeff (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leadingCoeff_zero : leadingCoeff (0 : R[X]) = 0 :=
  rfl

@[simp]
/-
**Polynomial.leadingCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_eq_zero : leadingCoeff p = 0 ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.by_contradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Finset.mem_of_max`：mem_of_max {s : Finset α} : forall {a : α}, s.max = a
 -> a in s
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R[X]
) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem leadingCoeff_eq_zero : leadingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩
/-
**Polynomial.leadingCoeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_ne_zero : leadingCoeff p != 0 ↔ p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem leadingCoeff_ne_zero : leadingCoeff p ≠ 0 ↔ p ≠ 0 := by rw [Ne, leadingCoeff_eq_zero]
/-
**Polynomial.leadingCoeff_eq_zero_iff_deg_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：leadingCoeff_eq_zero_iff_deg_eq_bot : leadingCoeff p = 0 ↔ degree p = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem leadingCoeff_eq_zero_iff_deg_eq_bot : leadingCoeff p = 0 ↔ degree p = ⊥ := by
  rw [leadingCoeff_eq_zero, degree_eq_bot]
/-
**Polynomial.natDegree_C_mul_X_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_C_mul_X_pow_le (a : R) (n : Nat) : natDegree (C a * X ^ n) <= n
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_le_iff_degree_le`：natDegree_le_iff_degree_le {n : N
at} : natDegree p <= n ↔ degree p <= n
· 使用定理 `Polynomial.degree_C_mul_X_pow_le`：degree_C_mul_X_pow_le (n : Nat) (a : R
) : degree (C a * X ^ n) <= n
-/
theorem natDegree_C_mul_X_pow_le (a : R) (n : ℕ) : natDegree (C a * X ^ n) ≤ n :=
  natDegree_le_iff_degree_le.2 <| degree_C_mul_X_pow_le _ _

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.degree_erase_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_erase_le (p : R[X]) (n : Nat) : degree (p.erase n) <= degree p
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_erase`：support_erase (p : R[X]) (n : Nat) : support (
p.erase n) = (support p).erase n
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
-/
theorem degree_erase_le (p : R[X]) (n : ℕ) : degree (p.erase n) ≤ degree p := by
  apply sup_mono
  simpa using Finset.erase_subset ..
/-
**Polynomial.degree_erase_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_erase_lt (hp : p != 0) : degree (p.erase (natDegree p)) < degree p
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Polynomial.degree_erase_le`：degree_erase_le (p : R[X]) (n : Nat) : degre
e (p.erase n) <= degree p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.degree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R), p.degree = p.support.max
· 使用定理 `Polynomial.support_erase`：support_erase (p : R[X]) (n : Nat) : support (
p.erase n) = (support p).erase n
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.mem_of_max`：mem_of_max {s : Finset α} : forall {a : α}, s.max = a
 -> a in s
-/
theorem degree_erase_lt (hp : p ≠ 0) : degree (p.erase (natDegree p)) < degree p := by
  apply lt_of_le_of_ne (degree_erase_le _ _)
  rw [degree_eq_natDegree hp, degree, support_erase]
  exact fun h => notMem_erase _ _ (mem_of_max h)
/-
**Polynomial.degree_update_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_update_le (p : R[X]) (n : Nat) (a : R) : degree (p.update n a) <= m
ax (degree p) n
参数：p : R[X]；n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R), p.degree = p.support.max
· 使用定理 `Polynomial.support_update`：support_update (p : R[X]) (n : Nat) (a : R) [
Decidable (a = 0)] : support (p.update n a) = if a = 0 then p.support.erase n el
se insert n p.s…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.max_mono`：max_mono {s t : Finset α} (st : s subseteq t) : s.max <
= t.max
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.max_insert`：max_insert {a : α} {s : Finset α} : (insert a s).max 
= max ↑a s.max
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem degree_update_le (p : R[X]) (n : ℕ) (a : R) : degree (p.update n a) ≤ max (degree p) n := by
  classical
  rw [degree, support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
  · rw [max_insert, max_comm]
    exact le_rfl
/-
**Polynomial.degree_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_sum_le (s : Finset ι) (f : ι -> R[X]) : degree (∑ i in s, f i) <= s
.sup fun b => degree (f b)
参数：s : Finset ι；f : ι -> R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem degree_sum_le (s : Finset ι) (f : ι → R[X]) :
    degree (∑ i ∈ s, f i) ≤ s.sup fun b => degree (f b) :=
  Finset.cons_induction_on s (by simp)
    fun a s has ih =>
    calc
      degree (∑ i ∈ cons a s has, f i) ≤ max (degree (f a)) (degree (∑ i ∈ s, f i)) := by
        rw [Finset.sum_cons]; exact degree_add_le _ _
      _ ≤ _ := by rw [sup_cons]; exact max_le_max le_rfl ih
/-
**Polynomial.degree_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_mul_le (p q : R[X]) : degree (p * q) <= degree p + degree q
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toFinsupp_mul`：toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp
 = a.toFinsupp * b.toFinsupp
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_mul_le`：sup_support_coeff_mul_le {deg
b : A -> B} (degbm : forall a b, degb (a + b) <= degb a + degb b) (f g : R[A]) :
 (f * g).coeff.support.sup degb…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem degree_mul_le (p q : R[X]) : degree (p * q) ≤ degree p + degree q := by
  simpa [degree, ← support_toFinsupp] using! AddMonoidAlgebra.sup_support_coeff_mul_le (by simp) ..
/-
**Polynomial.degree_mul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_mul_le_of_le {a b : WithBot Nat} (hp : degree p <= a) (hq : degree 
q <= b) : degree (p * q) <= a + b
参数：hp : degree p <= a；hq : degree q <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Polynomial.degree_mul_le`：degree_mul_le (p q : R[X]) : degree (p * q) <=
 degree p + degree q
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem degree_mul_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p * q) ≤ a + b := by grw [degree_mul_le, hp, hq]
/-
**Polynomial.degree_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] (p : Polynomial R) (n : ℕ), (p ^ n).deg
ree ≤ n • p.degree
参数：p : Polynomial R；n : ℕ；p ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem degree_pow_le (p : R[X]) : ∀ n : ℕ, degree (p ^ n) ≤ n • degree p
  | 0 => by rw [pow_zero, zero_nsmul]; exact degree_one_le
  | n + 1 => by grw [pow_succ, succ_nsmul, degree_mul_le, degree_pow_le]
/-
**Polynomial.degree_pow_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_pow_le_of_le {a : WithBot Nat} (b : Nat) (hp : degree p <= a) : deg
ree (p ^ b) <= b * a
参数：b : Nat；hp : degree p <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Polynomial.degree_mul_le_of_le`：degree_mul_le_of_le {a b : WithBot Nat} 
(hp : degree p <= a) (hq : degree q <= b) : degree (p * q) <= a + b
-/
theorem degree_pow_le_of_le {a : WithBot ℕ} (b : ℕ) (hp : degree p ≤ a) :
    degree (p ^ b) ≤ b * a := by
  induction b with
  | zero => simp [degree_one_le]
  | succ n hn =>
      rw [Nat.cast_succ, add_mul, one_mul, pow_succ]
      exact degree_mul_le_of_le hn hp

@[simp]
/-
**Polynomial.leadingCoeff_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_monomial (a : R) (n : Nat) : leadingCoeff (monomial n a) = a
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_monomial`：natDegree_monomial [DecidableEq R] (i : N
at) (r : R) : natDegree (monomial i r) = if r = 0 then 0 else i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
theorem leadingCoeff_monomial (a : R) (n : ℕ) : leadingCoeff (monomial n a) = a := by
  classical
  by_cases ha : a = 0
  · simp only [ha, (monomial n).map_zero, leadingCoeff_zero]
  · rw [leadingCoeff, natDegree_monomial, if_neg ha, coeff_monomial]
    simp
/-
**Polynomial.leadingCoeff_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_C_mul_X_pow (a : R) (n : Nat) : leadingCoeff (C a * X ^ n) = 
a
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.leadingCoeff_monomial`：leadingCoeff_monomial (a : R) (n : Nat
) : leadingCoeff (monomial n a) = a
-/
theorem leadingCoeff_C_mul_X_pow (a : R) (n : ℕ) : leadingCoeff (C a * X ^ n) = a := by
  rw [C_mul_X_pow_eq_monomial, leadingCoeff_monomial]
/-
**Polynomial.leadingCoeff_C_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_C_mul_X (a : R) : leadingCoeff (C a * X) = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.leadingCoeff_C_mul_X_pow`：leadingCoeff_C_mul_X_pow (a : R) (n
 : Nat) : leadingCoeff (C a * X ^ n) = a
-/
theorem leadingCoeff_C_mul_X (a : R) : leadingCoeff (C a * X) = a := by
  simpa only [pow_one] using leadingCoeff_C_mul_X_pow a 1

@[simp]
/-
**Polynomial.leadingCoeff_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_C (a : R) : leadingCoeff (C a) = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_monomial`：leadingCoeff_monomial (a : R) (n : Nat
) : leadingCoeff (monomial n a) = a
-/
theorem leadingCoeff_C (a : R) : leadingCoeff (C a) = a :=
  leadingCoeff_monomial a 0
/-
**Polynomial.leadingCoeff_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_X_pow (n : Nat) : leadingCoeff ((X : R[X]) ^ n) = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.leadingCoeff_C_mul_X_pow`：leadingCoeff_C_mul_X_pow (a : R) (n
 : Nat) : leadingCoeff (C a * X ^ n) = a
-/
theorem leadingCoeff_X_pow (n : ℕ) : leadingCoeff ((X : R[X]) ^ n) = 1 := by
  simpa only [C_1, one_mul] using leadingCoeff_C_mul_X_pow (1 : R) n
/-
**Polynomial.leadingCoeff_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_X : leadingCoeff (X : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.leadingCoeff_X_pow`：leadingCoeff_X_pow (n : Nat) : leadingCoe
ff ((X : R[X]) ^ n) = 1
-/
theorem leadingCoeff_X : leadingCoeff (X : R[X]) = 1 := by
  simpa only [pow_one] using @leadingCoeff_X_pow R _ 1

@[simp]
/-
**Polynomial.monic_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_X_pow (n : Nat) : Monic (X ^ n : R[X])
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_X_pow`：leadingCoeff_X_pow (n : Nat) : leadingCoe
ff ((X : R[X]) ^ n) = 1
-/
theorem monic_X_pow (n : ℕ) : Monic (X ^ n : R[X]) :=
  leadingCoeff_X_pow n

@[simp]
/-
**Polynomial.monic_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_X : Monic (X : R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_X`：leadingCoeff_X : leadingCoeff (X : R[X]) = 1
-/
theorem monic_X : Monic (X : R[X]) :=
  leadingCoeff_X
/-
**Polynomial.leadingCoeff_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_one : leadingCoeff (1 : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
-/
theorem leadingCoeff_one : leadingCoeff (1 : R[X]) = 1 :=
  leadingCoeff_C 1

@[simp]
/-
**Polynomial.monic_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_one : Monic (1 : R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
-/
theorem monic_one : Monic (1 : R[X]) :=
  leadingCoeff_C _
/-
**Polynomial.Monic.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] [Nontrivial R] {p : Polynomial R}, p.Mo
nic → p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Monic.ne_zero [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    p ≠ 0 := by
  rintro rfl
  simp [Monic] at hp
/-
**Polynomial.Monic.ne_zero_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R], 0 ≠ 1 → ∀ {p : Polynomial R}, p.Monic 
→ p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
-/
theorem Monic.ne_zero_of_ne (h : (0 : R) ≠ 1) {p : R[X]} (hp : p.Monic) : p ≠ 0 := by
  nontriviality R
  exact hp.ne_zero
/-
**Polynomial.Monic.ne_zero_of_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] [Nontrivial R] {c : R}, (Polynomial.C c
).Monic → c ≠ 0
参数：Polynomial.C c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Monic.ne_zero_of_C [Nontrivial R] {c : R} (hc : Monic (C c)) : c ≠ 0 := by
  rintro rfl
  simp [Monic] at hc
/-
**Polynomial.Monic.ne_zero_of_polynomial_ne** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p q r : Polynomial R}, p.Monic → q ≠ r
 → p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
-/
theorem Monic.ne_zero_of_polynomial_ne {r} (hp : Monic p) (hne : q ≠ r) : p ≠ 0 :=
  haveI := Nontrivial.of_polynomial_ne hne
  hp.ne_zero
/-
**Polynomial.natDegree_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_mul_le {p q : R[X]} : natDegree (p * q) <= natDegree p + natDegr
ee q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_mul_le`：degree_mul_le (p q : R[X]) : degree (p * q) <=
 degree p + degree q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
-/
theorem natDegree_mul_le {p q : R[X]} : natDegree (p * q) ≤ natDegree p + natDegree q := by
  apply natDegree_le_of_degree_le
  apply le_trans (degree_mul_le p q)
  rw [Nat.cast_add]
  apply add_le_add <;> apply degree_le_natDegree
/-
**Polynomial.natDegree_mul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_mul_le_of_le (hp : natDegree p <= m) (hg : natDegree q <= n) : n
atDegree (p * q) <= m + n
参数：hp : natDegree p <= m；hg : natDegree q <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem natDegree_mul_le_of_le (hp : natDegree p ≤ m) (hg : natDegree q ≤ n) :
    natDegree (p * q) ≤ m + n :=
natDegree_mul_le.trans <| add_le_add ‹_› ‹_›
/-
**Polynomial.natDegree_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_pow_le {p : R[X]} {n : Nat} : (p ^ n).natDegree <= n * p.natDegr
ee
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem natDegree_pow_le {p : R[X]} {n : ℕ} : (p ^ n).natDegree ≤ n * p.natDegree := by
  induction n with
  | zero => simp
  | succ n ih => grw [pow_succ, Nat.succ_mul, natDegree_mul_le, ih]
/-
**Polynomial.natDegree_pow_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_pow_le_of_le (n : Nat) (hp : natDegree p <= m) : natDegree (p ^ 
n) <= n * m
参数：n : Nat；hp : natDegree p <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_pow_le`：natDegree_pow_le {p : R[X]} {n : Nat} : (p 
^ n).natDegree <= n * p.natDegree
· 使用定理 `Nat.mul_le_mul`：∀ {n₁ m₁ n₂ m₂ : ℕ}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁ * m₁ ≤ n₂ * 
m₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem natDegree_pow_le_of_le (n : ℕ) (hp : natDegree p ≤ m) :
    natDegree (p ^ n) ≤ n * m :=
  natDegree_pow_le.trans (Nat.mul_le_mul le_rfl ‹_›)
/-
**Polynomial.natDegree_eq_zero_iff_degree_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：natDegree_eq_zero_iff_degree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Polynomial.natDegree_le_iff_degree_le`：natDegree_le_iff_degree_le {n : N
at} : natDegree p <= n ↔ degree p <= n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natDegree_eq_zero_iff_degree_le_zero : p.natDegree = 0 ↔ p.degree ≤ 0 := by
  rw [← nonpos_iff_eq_zero, natDegree_le_iff_degree_le, Nat.cast_zero]
/-
**Polynomial.degree_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_zero_le : degree (0 : R[X]) <= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
-/
theorem degree_zero_le : degree (0 : R[X]) ≤ 0 := natDegree_eq_zero_iff_degree_le_zero.mp rfl
/-
**Polynomial.degree_le_iff_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_le_iff_coeff_zero (f : R[X]) (n : WithBot Nat) : degree f <= n ↔ fo
rall m : Nat, n < m -> coeff f m = 0
参数：f : R[X]；n : WithBot Nat。
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem degree_le_iff_coeff_zero (f : R[X]) (n : WithBot ℕ) :
    degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 := by
  simp only [degree, Finset.max, Finset.sup_le_iff, mem_support_iff, Ne, ← not_le,
    not_imp_comm, Nat.cast_withBot]
/-
**Polynomial.degree_lt_iff_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_lt_iff_coeff_zero (f : R[X]) (n : Nat) : degree f < n ↔ forall m : 
Nat, n <= m -> coeff f m = 0
参数：f : R[X]；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem degree_lt_iff_coeff_zero (f : R[X]) (n : ℕ) :
    degree f < n ↔ ∀ m : ℕ, n ≤ m → coeff f m = 0 := by
  simp only [degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff,
    WithBot.coe_lt_coe, ← @not_le ℕ, max_eq_sup_coe, Nat.cast_withBot, Ne, not_imp_not]
/-
**Polynomial.natDegree_pos_iff_degree_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：natDegree_pos_iff_degree_pos : 0 < natDegree p ↔ 0 < degree p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Polynomial.natDegree_le_iff_degree_le`：natDegree_le_iff_degree_le {n : N
at} : natDegree p <= n ↔ degree p <= n
-/
theorem natDegree_pos_iff_degree_pos : 0 < natDegree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

@[simp]
/-
**Polynomial.degree_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_X_pow : degree ((X : R[X]) ^ n) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用定理 `Polynomial.degree_monomial`：degree_monomial (n : Nat) (ha : a != 0) : de
gree (monomial n a) = n
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
-/
theorem degree_X_pow : degree ((X : R[X]) ^ n) = n := by
  rw [X_pow_eq_monomial, degree_monomial _ (one_ne_zero' R)]

@[simp]
/-
**Polynomial.natDegree_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_X_pow : natDegree ((X : R[X]) ^ n) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
-/
theorem natDegree_X_pow : natDegree ((X : R[X]) ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_X_pow n)

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

/-
**Polynomial.degree_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_sub_le (p q : R[X]) : degree (p - q) <= max (degree p) (degree q)
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
-/
theorem degree_sub_le (p q : R[X]) : degree (p - q) ≤ max (degree p) (degree q) := by
  simpa only [degree_neg q] using! degree_add_le p (-q)
/-
**Polynomial.degree_sub_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_sub_le_of_le {a b : WithBot Nat} (hp : degree p <= a) (hq : degree 
q <= b) : degree (p - q) <= max a b
参数：hp : degree p <= a；hq : degree q <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_sub_le`：degree_sub_le (p q : R[X]) : degree (p - q) <=
 max (degree p) (degree q)
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
-/
theorem degree_sub_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p - q) ≤ max a b :=
  (p.degree_sub_le q).trans <| max_le_max ‹_› ‹_›
/-
**Polynomial.natDegree_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_sub_le (p q : R[X]) : natDegree (p - q) <= max (natDegree p) (na
tDegree q)
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Polynomial.natDegree_add_le`：natDegree_add_le (p q : R[X]) : natDegree (
p + q) <= max (natDegree p) (natDegree q)
-/
theorem natDegree_sub_le (p q : R[X]) : natDegree (p - q) ≤ max (natDegree p) (natDegree q) := by
  simpa only [← natDegree_neg q] using! natDegree_add_le p (-q)
/-
**Polynomial.natDegree_sub_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_sub_le_of_le (hp : natDegree p <= m) (hq : natDegree q <= n) : n
atDegree (p - q) <= max m n
参数：hp : natDegree p <= m；hq : natDegree q <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_sub_le`：natDegree_sub_le (p q : R[X]) : natDegree (
p - q) <= max (natDegree p) (natDegree q)
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
-/
theorem natDegree_sub_le_of_le (hp : natDegree p ≤ m) (hq : natDegree q ≤ n) :
    natDegree (p - q) ≤ max m n :=
  (p.natDegree_sub_le q).trans <| max_le_max ‹_› ‹_›
/-
**Polynomial.degree_sub_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_sub_lt_left (hd : degree p = degree q) (hp0 : p != 0) (hlc : leadin
gCoeff p = leadingCoeff q) : degree (p - q) < degree p
参数：hd : degree p = degree q；hp0 : p != 0；hlc : leadingCoeff p = leadingCoeff q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monomial_add_erase`：monomial_add_erase (p : R[X]) (n : Nat) :
 monomial n (coeff p n) + p.erase n = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `Polynomial.degree_erase_lt`：degree_erase_lt (hp : p != 0) : degree (p.er
ase (natDegree p)) < degree p
-/
theorem degree_sub_lt_left (hd : degree p = degree q) (hp0 : p ≠ 0)
    (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < degree p :=
  have hp : monomial (natDegree p) (leadingCoeff p) + p.erase (natDegree p) = p :=
    monomial_add_erase _ _
  have hq : monomial (natDegree q) (leadingCoeff q) + q.erase (natDegree q) = q :=
    monomial_add_erase _ _
  have hd' : natDegree p = natDegree q := by unfold natDegree; rw [hd]
  have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc
    degree (p - q) = degree (erase (natDegree q) p + -erase (natDegree q) q) := by
      conv =>
        lhs
        rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]
    _ ≤ max (degree (erase (natDegree q) p)) (degree (erase (natDegree q) q)) :=
      (degree_neg (erase (natDegree q) q) ▸ degree_add_le _ _)
    _ < degree p := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩

@[deprecated (since := "2026-06-30")] alias degree_sub_lt := degree_sub_lt_left
/-
**Polynomial.degree_sub_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_sub_lt_right (hd : degree p = degree q) (hq0 : q != 0) (hlc : p.lea
dingCoeff = q.leadingCoeff) : degree (p - q) < degree q
参数：hd : degree p = degree q；hq0 : q != 0；hlc : p.leadingCoeff = q.leadingCoeff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Polynomial.degree_sub_lt_left`：degree_sub_lt_left (hd : degree p = degre
e q) (hp0 : p != 0) (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < d
egree p
-/
theorem degree_sub_lt_right (hd : degree p = degree q) (hq0 : q ≠ 0)
    (hlc : p.leadingCoeff = q.leadingCoeff) : degree (p - q) < degree q := by
  rw [← degree_neg, neg_sub]
  exact degree_sub_lt_left hd.symm hq0 hlc.symm
/-
**Polynomial.degree_X_sub_C_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_X_sub_C_le (r : R) : (X - C r).degree <= 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_sub_le`：degree_sub_le (p q : R[X]) : degree (p - q) <=
 max (degree p) (degree q)
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Polynomial.degree_X_le`：degree_X_le : degree (X : R[X]) <= 1
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem degree_X_sub_C_le (r : R) : (X - C r).degree ≤ 1 :=
  (degree_sub_le _ _).trans (max_le degree_X_le (degree_C_le.trans zero_le_one))
/-
**Polynomial.natDegree_X_sub_C_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_X_sub_C_le (r : R) : (X - C r).natDegree <= 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_le_iff_degree_le`：natDegree_le_iff_degree_le {n : N
at} : natDegree p <= n ↔ degree p <= n
· 使用定理 `Polynomial.degree_X_sub_C_le`：degree_X_sub_C_le (r : R) : (X - C r).degr
ee <= 1
-/
theorem natDegree_X_sub_C_le (r : R) : (X - C r).natDegree ≤ 1 :=
  natDegree_le_iff_degree_le.2 <| degree_X_sub_C_le r

end Ring

end Polynomial

