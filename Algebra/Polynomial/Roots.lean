/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Order.Filter.TendstoCofinite

/-!
# Theory of univariate polynomials

We define the multiset of roots of a polynomial, and prove basic results about it.

## Main definitions

* `Polynomial.roots p`: The multiset containing all the roots of `p`, including their
  multiplicities.
* `Polynomial.rootSet p E`: The set of distinct roots of `p` in an algebra `E`.

## Main statements

* `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.

-/

@[expose] public section

assert_not_exists Ideal

open Multiset Finset

noncomputable section

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] [IsDomain R] {p q : R[X]}

section Roots

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
/-
**Polynomial.roots** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：roots (p : R[X]) : Multiset R
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities.
-/
noncomputable def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)
/-
**Polynomial.roots_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_def [DecidableEq R] (p : R[X]) [Decidable (p = 0)] : p.roots = if h 
: p = 0 then ∅ else Classical.choose (exists_multiset_roots h)
参数：p : R[X]；p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_multiset_roots`：exists_multiset_roots [DecidableEq R] 
: forall {p : R[X]} (_ : p != 0), exists s : Multiset R, (Multiset.card s : With
Bot Nat) <= degree p ∧…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
-/
theorem roots_def [DecidableEq R] (p : R[X]) [Decidable (p = 0)] :
    p.roots = if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h) := by
  rename_i iR ip0
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  rfl

@[simp]
/-
**Polynomial.roots_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_zero : (0 : R[X]).roots = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem roots_zero : (0 : R[X]).roots = 0 :=
  dif_pos rfl
/-
**Polynomial.card_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots (hp0 : p != 0) : (Multiset.card (roots p) : WithBot Nat) <= deg
ree p
参数：hp0 : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.exists_multiset_roots`：exists_multiset_roots [DecidableEq R] 
: forall {p : R[X]} (_ : p != 0), exists s : Multiset R, (Multiset.card s : With
Bot Nat) <= degree p ∧…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem card_roots (hp0 : p ≠ 0) : (Multiset.card (roots p) : WithBot ℕ) ≤ degree p := by
  classical
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1
/-
**Polynomial.card_roots'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots' (p : R[X]) : Multiset.card p.roots <= natDegree p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.card_roots`：card_roots (hp0 : p != 0) : (Multiset.card (roots
 p) : WithBot Nat) <= degree p
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
-/
theorem card_roots' (p : R[X]) : Multiset.card p.roots ≤ natDegree p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact WithBot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq <| degree_eq_natDegree hp0))
/-
**Polynomial.card_roots_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) : (Multiset.card 
(p - C a).roots : WithBot Nat) <= degree p
参数：hp0 : 0 < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.card_roots`：card_roots (hp0 : p != 0) : (Multiset.card (roots
 p) : WithBot Nat) <= degree p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.degree_add_C`：degree_add_C (hp : 0 < degree p) : degree (p + 
C a) = degree p
-/
theorem card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree p :=
  calc
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree (p - C a) :=
      card_roots <| mt sub_eq_zero.1 fun h => not_le_of_gt hp0 <| h.symm ▸ degree_C_le
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0
/-
**Polynomial.card_roots_sub_C'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) : Multiset.card 
(p - C a).roots <= natDegree p
参数：hp0 : 0 < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.card_roots_sub_C`：card_roots_sub_C {p : R[X]} {a : R} (hp0 : 
0 < degree p) : (Multiset.card (p - C a).roots : WithBot Nat) <= degree p
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    Multiset.card (p - C a).roots ≤ natDegree p :=
  WithBot.coe_le_coe.1
    (le_trans (card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_natDegree fun h => by simp_all))

@[simp]
/-
**Polynomial.count_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：count_roots [DecidableEq R] (p : R[X]) : p.roots.count a = rootMultiplicit
y a p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.exists_multiset_roots`：exists_multiset_roots [DecidableEq R] 
: forall {p : R[X]} (_ : p != 0), exists s : Multiset R, (Multiset.card s : With
Bot Nat) <= degree p ∧…
· 使用定理 `Polynomial.roots_def`：roots_def [DecidableEq R] (p : R[X]) [Decidable (p
 = 0)] : p.roots = if h : p = 0 then ∅ else Classical.choose (exists_multiset_ro
ots h)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem count_roots [DecidableEq R] (p : R[X]) : p.roots.count a = rootMultiplicity a p := by
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_def, dif_neg hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a

@[simp]
/-
**Polynomial.mem_roots'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_roots' : a in p.roots ↔ p != 0 ∧ IsRoot p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.rootMultiplicity_pos'`：rootMultiplicity_pos' {p : R[X]} {x : 
R} : 0 < rootMultiplicity x p ↔ p != 0 ∧ IsRoot p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_roots' : a ∈ p.roots ↔ p ≠ 0 ∧ IsRoot p a := by
  classical
  rw [← count_pos, count_roots p, rootMultiplicity_pos']
/-
**Polynomial.mem_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p a
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.mem_roots'`：mem_roots' : a in p.roots ↔ p != 0 ∧ IsRoot p a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
-/
theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ IsRoot p a :=
  mem_roots'.trans <| and_iff_right hp
/-
**Polynomial.ne_zero_of_mem_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ne_zero_of_mem_roots (h : a in p.roots) : p != 0
参数：h : a in p.roots。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_roots'`：mem_roots' : a in p.roots ↔ p != 0 ∧ IsRoot p a
-/
theorem ne_zero_of_mem_roots (h : a ∈ p.roots) : p ≠ 0 :=
  (mem_roots'.1 h).1
/-
**Polynomial.isRoot_of_mem_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isRoot_of_mem_roots (h : a in p.roots) : IsRoot p a
参数：h : a in p.roots。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_roots'`：mem_roots' : a in p.roots ↔ p != 0 ∧ IsRoot p a
-/
theorem isRoot_of_mem_roots (h : a ∈ p.roots) : IsRoot p a :=
  (mem_roots'.1 h).2
/-
**Polynomial.roots_eq_zero_iff_isRoot_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：roots_eq_zero_iff_isRoot_eq_bot (hp0 : p != 0) : p.roots = 0 ↔ p.IsRoot = 
⊥
参数：hp0 : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
-/
theorem roots_eq_zero_iff_isRoot_eq_bot (hp0 : p ≠ 0) : p.roots = 0 ↔ p.IsRoot = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ eq_zero_of_forall_notMem fun x hx ↦ h ▸ mem_roots hp0 |>.mp hx⟩
  ext a
  simp only [Pi.bot_apply, Prop.bot_eq_false, mem_roots hp0 |>.not.mp <| by simp [h]]
/-
**Polynomial.roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot : p.roots = 0 ↔ p = 0 ∨ p.IsRoo
t = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.roots_eq_zero_iff_isRoot_eq_bot`：roots_eq_zero_iff_isRoot_eq_
bot (hp0 : p != 0) : p.roots = 0 ↔ p.IsRoot = ⊥
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot : p.roots = 0 ↔ p = 0 ∨ p.IsRoot = ⊥ := by
  rcases eq_or_ne p 0 with rfl | hp0; · simp
  simp [roots_eq_zero_iff_isRoot_eq_bot hp0, hp0]
/-
**Polynomial.mem_roots_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_roots_map_of_injective [Semiring S] {p : S[X]} {f : S ->+* R} (hf : Fu
nction.Injective f) {x : R} (hp : p != 0) : x in (p.map f).roots ↔ p.eval₂ f x =
 0
参数：hf : Function.Injective f；hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_roots_map_of_injective [Semiring S] {p : S[X]} {f : S →+* R}
    (hf : Function.Injective f) {x : R} (hp : p ≠ 0) : x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 := by
  rw [mem_roots ((Polynomial.map_ne_zero_iff hf).mpr hp), IsRoot, eval_map]
/-
**Polynomial.mem_roots_iff_aeval_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mem_roots_iff_aeval_eq_zero {x : R} (w : p != 0) : x in roots p ↔ aeval x 
p = 0
参数：w : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_roots_map_of_injective`：mem_roots_map_of_injective [Semir
ing S] {p : S[X]} {f : S ->+* R} (hf : Function.Injective f) {x : R} (hp : p != 
0) : x in (p.map f).roots ↔…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R
· 使用定理 `Algebra.algebraMap_self`：∀ {R : Type u} [inst : CommSemiring R], algebra
Map R R = RingHom.id R
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_roots_iff_aeval_eq_zero {x : R} (w : p ≠ 0) : x ∈ roots p ↔ aeval x p = 0 := by
  rw [aeval_def, ← mem_roots_map_of_injective (FaithfulSMul.algebraMap_injective _ _) w,
    Algebra.algebraMap_self, map_id]
/-
**Polynomial.card_le_degree_of_subset_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} (h : Z.val subset
eq p.roots) : #Z <= p.natDegree
参数：h : Z.val subseteq p.roots。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.val_le_iff_val_subset`：val_le_iff_val_subset {a : Finset α} {b : 
Multiset α} : a.val <= b ↔ a.val subseteq b
· 使用定理 `Polynomial.card_roots'`：card_roots' (p : R[X]) : Multiset.card p.roots <
= natDegree p
-/
theorem card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} (h : Z.val ⊆ p.roots) :
    #Z ≤ p.natDegree :=
  (Multiset.card_le_card (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)
/-
**Polynomial.finite_setOfPred_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：finite_setOfPred_isRoot {p : R[X]} (hp : p != 0) : Set.Finite { x | IsRoot
 p x }
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem finite_setOfPred_isRoot {p : R[X]} (hp : p ≠ 0) : Set.Finite { x | IsRoot p x } := by
  classical
  simpa only [← Finset.setOfPred_mem, Multiset.mem_toFinset, mem_roots hp]
    using p.roots.toFinset.finite_toSet

@[deprecated (since := "2026-07-09")] alias finite_setOf_isRoot := finite_setOfPred_isRoot
/-
**Polynomial.eq_zero_of_infinite_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_zero_of_infinite_isRoot (p : R[X]) (h : Set.Infinite { x | IsRoot p x }
) : p = 0
参数：p : R[X]；h : Set.Infinite { x | IsRoot p x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Polynomial.finite_setOfPred_isRoot`：finite_setOfPred_isRoot {p : R[X]} (
hp : p != 0) : Set.Finite { x | IsRoot p x }
-/
theorem eq_zero_of_infinite_isRoot (p : R[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0 :=
  not_imp_comm.mp finite_setOfPred_isRoot h
/-
**Polynomial.exists_max_root** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_max_root [LinearOrder R] (p : R[X]) (hp : p != 0) : exists x₀, fora
ll x, p.IsRoot x -> x <= x₀
参数：p : R[X]；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_upper_bound_image`：exists_upper_bound_image [Nonempty α] [Lin
earOrder β] (s : Set α) (f : α -> β) (h : s.Finite) : exists a : α, forall b in 
s, f b <= f a
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.finite_setOfPred_isRoot`：finite_setOfPred_isRoot {p : R[X]} (
hp : p != 0) : Set.Finite { x | IsRoot p x }
-/
theorem exists_max_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x ≤ x₀ :=
  Set.exists_upper_bound_image _ _ <| finite_setOfPred_isRoot hp
/-
**Polynomial.exists_min_root** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_min_root [LinearOrder R] (p : R[X]) (hp : p != 0) : exists x₀, fora
ll x, p.IsRoot x -> x₀ <= x
参数：p : R[X]；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_lower_bound_image`：exists_lower_bound_image [Nonempty α] [Lin
earOrder β] (s : Set α) (f : α -> β) (h : s.Finite) : exists a : α, forall b in 
s, f a <= f b
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.finite_setOfPred_isRoot`：finite_setOfPred_isRoot {p : R[X]} (
hp : p != 0) : Set.Finite { x | IsRoot p x }
-/
theorem exists_min_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x₀ ≤ x :=
  Set.exists_lower_bound_image _ _ <| finite_setOfPred_isRoot hp
/-
**Polynomial.eq_of_infinite_eval_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_of_infinite_eval_eq (p q : R[X]) (h : Set.Infinite { x | eval x p = eva
l x q }) : p = q
参数：p q : R[X]；h : Set.Infinite { x | eval x p = eval x q }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.eq_zero_of_infinite_isRoot`：eq_zero_of_infinite_isRoot (p : R
[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
-/
theorem eq_of_infinite_eval_eq (p q : R[X]) (h : Set.Infinite { x | eval x p = eval x q }) :
    p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_isRoot
  simpa only [IsRoot, eval_sub, sub_eq_zero]

/-- Non-constant polynomials have finite fibres, provided the coefficients are a domain. -/
/-
**Polynomial.tendstoCofinite_of_natDegree_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial`。
形式化陈述：tendstoCofinite_of_natDegree_ne_zero {R : Type} [CommRing R] [IsDomain R] 
(p : R[X]) (hp : p.natDegree != 0) : Filter.TendstoCofinite p.eval
参数：p : R[X]；hp : p.natDegree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendstoCofinite_iff_finite_preimage_singleton`：tendstoCofinite_if
f_finite_preimage_singleton : TendstoCofinite f ↔ forall b : β, Set.Finite (f ⁻¹
' {b})
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Polynomial.eq_of_infinite_eval_eq`：eq_of_infinite_eval_eq (p q : R[X]) (
h : Set.Infinite { x | eval x p = eval x q }) : p = q
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
Non-constant polynomials have finite fibres, provided the coefficients are a dom
ain.
-/
lemma tendstoCofinite_of_natDegree_ne_zero {R : Type} [CommRing R] [IsDomain R] (p : R[X])
    (hp : p.natDegree ≠ 0) : Filter.TendstoCofinite p.eval := by
  rw [Filter.tendstoCofinite_iff_finite_preimage_singleton]
  intro x
  by_contra! hx
  obtain ⟨rfl⟩ : p = C x := p.eq_of_infinite_eval_eq (C x) (by simpa)
  simp at hp
/-
**Polynomial.roots_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q).roots = p.roots + q.ro
ots
参数：hpq : p * q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.ext`：ext {s t : Multiset α} : s = t ↔ forall a, count a s = cou
nt a t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.rootMultiplicity_mul`：rootMultiplicity_mul {p q : R[X]} {x : 
R} (hpq : p * q != 0) : rootMultiplicity x (p * q) = rootMultiplicity x p + root
Multiplicity x q
-/
theorem roots_mul {p q : R[X]} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots := by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add, count_roots, count_roots, count_roots, rootMultiplicity_mul hpq]
/-
**Polynomial.roots.le_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.roots`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [inst_1 : IsDomain R] {p q : Polynomial
 R}, q ≠ 0 → p ∣ q → p.roots ≤ q.roots
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_exists_add`：le_iff_exists_add {s t : Multiset α} : s <= 
t ↔ exists u, t = s + u
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem roots.le_of_dvd (h : q ≠ 0) : p ∣ q → roots p ≤ roots q := by
  rintro ⟨k, rfl⟩
  exact Multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩
/-
**Polynomial.mem_roots_sub_C'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_roots_sub_C' {p : R[X]} {a x : R} : x in (p - C a).roots ↔ p != C a ∧ 
p.eval x = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_roots'`：mem_roots' : a in p.roots ↔ p != 0 ∧ IsRoot p a
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_roots_sub_C' {p : R[X]} {a x : R} : x ∈ (p - C a).roots ↔ p ≠ C a ∧ p.eval x = a := by
  rw [mem_roots', IsRoot.def, sub_ne_zero, eval_sub, sub_eq_zero, eval_C]
/-
**Polynomial.mem_roots_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) : x in (p - C a)
.roots ↔ p.eval x = a
参数：hp0 : 0 < degree p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.mem_roots_sub_C'`：mem_roots_sub_C' {p : R[X]} {a x : R} : x i
n (p - C a).roots ↔ p != C a ∧ p.eval x = a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) :
    x ∈ (p - C a).roots ↔ p.eval x = a :=
  mem_roots_sub_C'.trans <| and_iff_right fun hp => hp0.not_ge <| hp.symm ▸ degree_C_le

@[simp]
/-
**Polynomial.roots_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_X_sub_C (r : R) : roots (X - C r) = {r}
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.rootMultiplicity_X_sub_C`：rootMultiplicity_X_sub_C [Nontrivia
l R] [DecidableEq R] {x y : R} : rootMultiplicity x (X - C y) = if x = y then 1 
else 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Multiset.count_singleton`：count_singleton (a b : α) : count a ({b} : Mul
tiset α) = if a = b then 1 else 0
-/
theorem roots_X_sub_C (r : R) : roots (X - C r) = {r} := by
  classical
  ext s
  rw [count_roots, rootMultiplicity_X_sub_C, count_singleton]

@[simp]
/-
**Polynomial.roots_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_X_add_C (r : R) : roots (X + C r) = {-r}
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
-/
theorem roots_X_add_C (r : R) : roots (X + C r) = {-r} := by simpa using roots_X_sub_C (-r)

@[simp]
/-
**Polynomial.roots_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_X : roots (X : R[X]) = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem roots_X : roots (X : R[X]) = {0} := by rw [← roots_X_sub_C, C_0, sub_zero]

@[simp]
/-
**Polynomial.roots_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_C (x : R) : (C x).roots = 0
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.ext`：ext {s t : Multiset α} : s = t ↔ forall a, count a s = cou
nt a t
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Multiset.count_zero`：count_zero (a : α) : count a 0 = 0
· 使用定理 `Polynomial.rootMultiplicity_eq_zero`：rootMultiplicity_eq_zero {p : R[X]}
 {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0
· 使用定理 `Polynomial.not_isRoot_C`：not_isRoot_C (r a : R) (hr : r != 0) : ¬IsRoot 
(C r) a
-/
theorem roots_C (x : R) : (C x).roots = 0 := by
  classical exact
  if H : x = 0 then by rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr fun r => (by
      rw [count_roots, count_zero, rootMultiplicity_eq_zero (not_isRoot_C _ _ H)])

@[simp]
/-
**Polynomial.roots_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_one : (1 : R[X]).roots = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_C`：roots_C (x : R) : (C x).roots = 0
-/
theorem roots_one : (1 : R[X]).roots = ∅ :=
  roots_C 1

@[simp]
/-
**Polynomial.roots_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_C_mul (p : R[X]) (ha : a != 0) : (C a * p).roots = p.roots
参数：p : R[X]；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.roots_C`：roots_C (x : R) : (C x).roots = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem roots_C_mul (p : R[X]) (ha : a ≠ 0) : (C a * p).roots = p.roots := by
  by_cases hp : p = 0 <;>
    simp only [roots_mul, *, Ne, mul_eq_zero, C_eq_zero, or_self_iff, not_false_iff, roots_C,
      zero_add, mul_zero]
/-
**Polynomial._root_.Associated.roots_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Associated.roots_eq {p q : R[X]} (h : Associated p q) : p.roots = q.roots := by
  obtain ⟨u, rfl⟩ := h
  rw [eq_C_of_degree_eq_zero <| degree_coe_units u, mul_comm,
    roots_C_mul _ <| coeff_coe_units_zero_ne_zero u]

@[simp]
/-
**Polynomial.roots_smul_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_smul_nonzero (p : R[X]) (ha : a != 0) : (a • p).roots = p.roots
参数：p : R[X]；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smul_eq_C_mul`：smul_eq_C_mul (a : R) : a • p = C a * p
· 使用定理 `Polynomial.roots_C_mul`：roots_C_mul (p : R[X]) (ha : a != 0) : (C a * p)
.roots = p.roots
-/
theorem roots_smul_nonzero (p : R[X]) (ha : a ≠ 0) : (a • p).roots = p.roots := by
  rw [smul_eq_C_mul, roots_C_mul _ ha]

@[simp]
/-
**Polynomial.roots_neg** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：roots_neg (p : R[X]) : (-p).roots = p.roots
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `Polynomial.roots_smul_nonzero`：roots_smul_nonzero (p : R[X]) (ha : a != 
0) : (a • p).roots = p.roots
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
lemma roots_neg (p : R[X]) : (-p).roots = p.roots := by
  rw [← neg_one_smul R p, roots_smul_nonzero p (neg_ne_zero.mpr one_ne_zero)]

@[simp]
/-
**Polynomial.map_roots_comp_C_mul_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：map_roots_comp_C_mul_X_add_C (p : R[X]) (a b : R) (ha : IsUnit a) : (p.com
p (C a * X + C b)).roots.map (fun x => a * x + b) = p.roots
参数：p : R[X]；a b : R；ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `AddGroup.addRight_bijective`：∀ {G : Type u_5} [inst : AddGroup G] (a : G
), Function.Bijective fun x => x + a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.isUnit_iff_mulLeft_bijective`：isUnit_iff_mulLeft_bijective {a : M
} : IsUnit a ↔ Function.Bijective (a * ·)
· 使用定理 `Multiset.ext`：ext {s t : Multiset α} : s = t ↔ forall a, count a s = cou
nt a t
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Multiset.count_map_eq_count'`：count_map_eq_count' [DecidableEq β] (f : α
 -> β) (s : Multiset α) (hf : Function.Injective f) (x : α) : (s.map f).count (f
 x) = s.count x
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Polynomial.rootMultiplicity_comp_C_mul_X_add_C`：rootMultiplicity_comp_C_
mul_X_add_C (p : R[X]) (a b c : R) (ha : IsUnit a) : (p.comp (C a * X + C b)).ro
otMultiplicity c = p.rootMultiplicit…
-/
theorem map_roots_comp_C_mul_X_add_C (p : R[X]) (a b : R) (ha : IsUnit a) :
    (p.comp (C a * X + C b)).roots.map (fun x ↦ a * x + b) = p.roots := by
  classical
  set f := fun x ↦ a * x + b
  have hf : Function.Bijective f :=
    (AddGroup.addRight_bijective b).comp (IsUnit.isUnit_iff_mulLeft_bijective.mp ha)
  rw [Multiset.ext]
  intro x
  obtain ⟨x, rfl⟩ := hf.surjective x
  rw [count_roots, count_map_eq_count' f _ hf.injective, count_roots,
    rootMultiplicity_comp_C_mul_X_add_C p a b x ha]

open scoped Ring in
/-
**Polynomial.roots_comp_C_mul_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_comp_C_mul_X_add_C (p : R[X]) (a b : R) (ha : IsUnit a) : (p.comp (C
 a * X + C b)).roots = p.roots.map (fun x => a⁻¹ʳ * (x - b))
参数：p : R[X]；a b : R；ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_roots_comp_C_mul_X_add_C`：map_roots_comp_C_mul_X_add_C (p
 : R[X]) (a b : R) (ha : IsUnit a) : (p.comp (C a * X + C b)).roots.map (fun x =
> a * x + b) = p.roots
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.inverse_mul_cancel`：inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻
¹ʳ * x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem roots_comp_C_mul_X_add_C (p : R[X]) (a b : R) (ha : IsUnit a) :
    (p.comp (C a * X + C b)).roots = p.roots.map (fun x ↦ a⁻¹ʳ * (x - b)) := by
  conv_rhs => rw [← p.map_roots_comp_C_mul_X_add_C a b ha]
  simp [← mul_assoc, Ring.inverse_mul_cancel a ha]

@[simp]
/-
**Polynomial.roots_comp_neg_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_comp_neg_X (p : R[X]) : (p.comp (-X)).roots = p.roots.map fun x => -
x
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_roots_comp_C_mul_X_add_C`：map_roots_comp_C_mul_X_add_C (p
 : R[X]) (a b : R) (ha : IsUnit a) : (p.comp (C a * X + C b)).roots.map (fun x =
> a * x + b) = p.roots
· 使用定理 `isUnit_neg_one`：isUnit_neg_one [Monoid α] [HasDistribNeg α] : IsUnit (-1
 : α)
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem roots_comp_neg_X (p : R[X]) : (p.comp (-X)).roots = p.roots.map fun x ↦ -x := by
  simp [← map_roots_comp_C_mul_X_add_C p (-1) 0 isUnit_neg_one]

@[simp]
/-
**Polynomial.roots_C_mul_X_sub_C_of_IsUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：roots_C_mul_X_sub_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X - C b).roo
ts = {a⁻¹ * b}
参数：b : R；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.roots_C_mul`：roots_C_mul (p : R[X]) (ha : a != 0) : (C a * p)
.roots = p.roots
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
-/
theorem roots_C_mul_X_sub_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X - C b).roots =
    {a⁻¹ * b} := by
  rw [← roots_C_mul _ (Units.ne_zero a⁻¹), mul_sub, ← mul_assoc, ← C_mul, ← C_mul,
    Units.inv_mul, C_1, one_mul]
  exact roots_X_sub_C (a⁻¹ * b)

@[simp]
/-
**Polynomial.roots_C_mul_X_add_C_of_IsUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：roots_C_mul_X_add_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X + C b).roo
ts = {-(a⁻¹ * b)}
参数：b : R；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.roots_C_mul_X_sub_C_of_IsUnit`：roots_C_mul_X_sub_C_of_IsUnit 
(b : R) (a : Rˣ) : (C (a : R) * X - C b).roots = {a⁻¹ * b}
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
theorem roots_C_mul_X_add_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X + C b).roots =
    {-(a⁻¹ * b)} := by
  rw [← sub_neg_eq_add, ← C_neg, roots_C_mul_X_sub_C_of_IsUnit, mul_neg]
/-
**Polynomial.roots_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_list_prod (L : List R[X]) : (0 : R[X]) ∉ L -> L.prod.roots = (L : Mu
ltiset R[X]).bind roots
参数：L : List R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_one`：roots_one : (1 : R[X]).roots = ∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用引理 `List.prod_ne_zero`：prod_ne_zero (hL : (0 : M₀) ∉ l) : l.prod != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_coe`：cons_coe (a : α) (l : List α) : (a ::ₘ l : Multiset α
) = (a :: l : List α)
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
-/
theorem roots_list_prod (L : List R[X]) :
    (0 : R[X]) ∉ L → L.prod.roots = (L : Multiset R[X]).bind roots :=
  List.recOn L (fun _ => roots_one) fun hd tl ih H => by
    rw [List.mem_cons, not_or] at H
    rw [List.prod_cons, roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2), ←
      Multiset.cons_coe, Multiset.cons_bind, ih H.2]
/-
**Polynomial.roots_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_multiset_prod (m : Multiset R[X]) : (0 : R[X]) ∉ m -> m.prod.roots =
 m.bind roots
参数：m : Multiset R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_list_prod`：roots_list_prod (L : List R[X]) : (0 : R[X])
 ∉ L -> L.prod.roots = (L : Multiset R[X]).bind roots
-/
theorem roots_multiset_prod (m : Multiset R[X]) : (0 : R[X]) ∉ m → m.prod.roots = m.bind roots := by
  rcases m with ⟨L⟩
  simpa only [Multiset.prod_coe, quot_mk_to_coe''] using! roots_list_prod L
/-
**Polynomial.roots_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_prod {ι : Type*} (f : ι -> R[X]) (s : Finset ι) : s.prod f != 0 -> (
s.prod f).roots = s.val.bind fun i => roots (f i)
参数：f : ι -> R[X]；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Multiset.bind_map`：bind_map (m : Multiset α) (n : β -> Multiset γ) (f : 
α -> β) : bind (map f m) n = bind m fun a => n (f a)
· 使用定理 `Polynomial.roots_multiset_prod`：roots_multiset_prod (m : Multiset R[X]) 
: (0 : R[X]) ∉ m -> m.prod.roots = m.bind roots
-/
theorem roots_prod {ι : Type*} (f : ι → R[X]) (s : Finset ι) :
    s.prod f ≠ 0 → (s.prod f).roots = s.val.bind fun i => roots (f i) := by
  rcases s with ⟨m, hm⟩
  simpa [Multiset.prod_eq_zero_iff, Multiset.bind_map] using roots_multiset_prod (m.map f)

@[simp]
/-
**Polynomial.roots_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_pow (p : R[X]) (n : Nat) : (p ^ n).roots = n • p.roots
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.roots_one`：roots_one : (1 : R[X]).roots = ∅
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Multiset.empty_eq_zero`：empty_eq_zero : (∅ : Multiset α) = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem roots_pow (p : R[X]) (n : ℕ) : (p ^ n).roots = n • p.roots := by
  induction n with
  | zero => rw [pow_zero, roots_one, zero_smul, empty_eq_zero]
  | succ n ihn =>
    rcases eq_or_ne p 0 with (rfl | hp)
    · rw [zero_pow n.succ_ne_zero, roots_zero, smul_zero]
    · rw [pow_succ, roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, add_smul, one_smul]
/-
**Polynomial.roots_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_X_pow (n : Nat) : (X ^ n : R[X]).roots = n • ({0} : Multiset R)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots_pow`：roots_pow (p : R[X]) (n : Nat) : (p ^ n).roots = n
 • p.roots
· 使用定理 `Polynomial.roots_X`：roots_X : roots (X : R[X]) = {0}
-/
theorem roots_X_pow (n : ℕ) : (X ^ n : R[X]).roots = n • ({0} : Multiset R) := by
  rw [roots_pow, roots_X]
/-
**Polynomial.roots_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_C_mul_X_pow (ha : a != 0) (n : Nat) : Polynomial.roots (C a * X ^ n)
 = n • ({0} : Multiset R)
参数：ha : a != 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots_C_mul`：roots_C_mul (p : R[X]) (ha : a != 0) : (C a * p)
.roots = p.roots
· 使用定理 `Polynomial.roots_X_pow`：roots_X_pow (n : Nat) : (X ^ n : R[X]).roots = n
 • ({0} : Multiset R)
-/
theorem roots_C_mul_X_pow (ha : a ≠ 0) (n : ℕ) :
    Polynomial.roots (C a * X ^ n) = n • ({0} : Multiset R) := by
  rw [roots_C_mul _ ha, roots_X_pow]

@[simp]
/-
**Polynomial.roots_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_monomial (ha : a != 0) (n : Nat) : (monomial n a).roots = n • ({0} :
 Multiset R)
参数：ha : a != 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.roots_C_mul_X_pow`：roots_C_mul_X_pow (ha : a != 0) (n : Nat) 
: Polynomial.roots (C a * X ^ n) = n • ({0} : Multiset R)
-/
theorem roots_monomial (ha : a ≠ 0) (n : ℕ) : (monomial n a).roots = n • ({0} : Multiset R) := by
  rw [← C_mul_X_pow_eq_monomial, roots_C_mul_X_pow ha]
/-
**Polynomial.roots_prod_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.va
l
参数：s : Finset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.roots_prod`：roots_prod {ι : Type*} (f : ι -> R[X]) (s : Finse
t ι) : s.prod f != 0 -> (s.prod f).roots = s.val.bind fun i => roots (f i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
· 使用定理 `Multiset.bind_singleton`：bind_singleton (f : α -> β) : (s.bind fun x => 
({f x} : Multiset β)) = map f s
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
-/
theorem roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.val := by
  apply (roots_prod (fun a => X - C a) s ?_).trans
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · refine prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)

@[simp]
/-
**Polynomial.roots_multiset_prod_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_multiset_prod_X_sub_C (s : Multiset R) : (s.map fun a => X - C a).pr
od.roots = s
参数：s : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots_multiset_prod`：roots_multiset_prod (m : Multiset R[X]) 
: (0 : R[X]) ∉ m -> m.prod.roots = m.bind roots
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Multiset.bind_map`：bind_map (m : Multiset α) (n : β -> Multiset γ) (f : 
α -> β) : bind (map f m) n = bind m fun a => n (f a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
· 使用定理 `Multiset.bind_singleton`：bind_singleton (f : α -> β) : (s.bind fun x => 
({f x} : Multiset β)) = map f s
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
-/
theorem roots_multiset_prod_X_sub_C (s : Multiset R) : (s.map fun a => X - C a).prod.roots = s := by
  rw [roots_multiset_prod, Multiset.bind_map]
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · rw [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact X_sub_C_ne_zero a h
/-
**Polynomial.roots_ofMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_ofMultiset (s : Multiset R) : (ofMultiset s).roots = s
参数：s : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.ofMultiset_apply`：∀ {R : Type u} [inst : CommRing R] (s : Mul
tiset R),   Polynomial.ofMultiset s = (Multiset.map (fun a => Polynomial.X - Pol
ynomial.C a) s).p…
· 使用定理 `Polynomial.roots_multiset_prod_X_sub_C`：roots_multiset_prod_X_sub_C (s :
 Multiset R) : (s.map fun a => X - C a).prod.roots = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem roots_ofMultiset (s : Multiset R) : (ofMultiset s).roots = s := by
  simp

variable (R) in
/-
**Polynomial.rightInverse_ofMultiset_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：rightInverse_ofMultiset_roots : Function.RightInverse (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_ofMultiset`：roots_ofMultiset (s : Multiset R) : (ofMult
iset s).roots = s
-/
theorem rightInverse_ofMultiset_roots : Function.RightInverse (α := R[X]) ofMultiset roots :=
  roots_ofMultiset

variable (R) in
/-
**Polynomial.ofMultiset_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofMultiset_injective : Function.Injective (ofMultiset (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `Polynomial.rightInverse_ofMultiset_roots`：rightInverse_ofMultiset_roots 
: Function.RightInverse (α
-/
theorem ofMultiset_injective : Function.Injective (ofMultiset (R := R)) :=
  rightInverse_ofMultiset_roots R |>.injective
/-
**Polynomial.card_roots_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots_X_pow_sub_C {n : Nat} (hn : 0 < n) (a : R) : Multiset.card (roo
ts ((X : R[X]) ^ n - C a)) <= n
参数：hn : 0 < n；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Polynomial.card_roots`：card_roots (hp0 : p != 0) : (Multiset.card (roots
 p) : WithBot Nat) <= degree p
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
-/
theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
    Multiset.card (roots ((X : R[X]) ^ n - C a)) ≤ n :=
  WithBot.coe_le_coe.1 <|
    calc
      (Multiset.card (roots ((X : R[X]) ^ n - C a)) : WithBot ℕ) ≤ degree ((X : R[X]) ^ n - C a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a
/-
**Polynomial.roots_eq_of_degree_le_card_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：roots_eq_of_degree_le_card_of_ne_zero {S : Finset R} (hS : forall x in S, 
p.eval x = 0) (hcard : p.degree <= S.card) (hp : p != 0) : p.roots = S.val
参数：hS : forall x in S, p.eval x = 0；hcard : p.degree <= S.card；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.val_le_iff_val_subset`：val_le_iff_val_subset {a : Finset α} {b : 
Multiset α} : a.val <= b ↔ a.val subseteq b
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.card_roots`：card_roots (hp0 : p != 0) : (Multiset.card (roots
 p) : WithBot Nat) <= degree p
-/
theorem roots_eq_of_degree_le_card_of_ne_zero {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : p.degree ≤ S.card) (hp : p ≠ 0) : p.roots = S.val := by
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · exact (Finset.val_le_iff_val_subset.mpr (fun x hx ↦ (p.mem_roots hp).mpr (hS x hx)))
  · simpa using (p.card_roots hp).trans hcard
/-
**Polynomial.roots_eq_of_degree_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_eq_of_degree_eq_card {S : Finset R} (hS : forall x in S, p.eval x = 
0) (hcard : S.card = p.degree) : p.roots = S.val
参数：hS : forall x in S, p.eval x = 0；hcard : S.card = p.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_eq_of_degree_le_card_of_ne_zero`：roots_eq_of_degree_le_
card_of_ne_zero {S : Finset R} (hS : forall x in S, p.eval x = 0) (hcard : p.deg
ree <= S.card) (hp : p != 0) : p.roots…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem roots_eq_of_degree_eq_card {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : S.card = p.degree) : p.roots = S.val :=
  roots_eq_of_degree_le_card_of_ne_zero hS (by grind) (by contrapose! hcard; simp [hcard])
/-
**Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：roots_eq_of_natDegree_le_card_of_ne_zero {S : Finset R} (hS : forall x in 
S, p.eval x = 0) (hcard : p.natDegree <= S.card) (hp : p != 0) : p.roots = S.val
参数：hS : forall x in S, p.eval x = 0；hcard : p.natDegree <= S.card；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_eq_of_degree_le_card_of_ne_zero`：roots_eq_of_degree_le_
card_of_ne_zero {S : Finset R} (hS : forall x in S, p.eval x = 0) (hcard : p.deg
ree <= S.card) (hp : p != 0) : p.roots…
· 使用定理 `Polynomial.degree_le_of_natDegree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.natDegree ≤ n → p.degree ≤ ↑n
-/
theorem roots_eq_of_natDegree_le_card_of_ne_zero {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : p.natDegree ≤ S.card) (hp : p ≠ 0) : p.roots = S.val :=
  roots_eq_of_degree_le_card_of_ne_zero hS (degree_le_of_natDegree_le hcard) hp

section NthRoots

/-- `nthRoots n a` noncomputably returns the solutions to `x ^ n = a`. -/
/-
**Polynomial.nthRoots** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：nthRoots (n : Nat) (a : R) : Multiset R
参数：n : Nat；a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`nthRoots n a` noncomputably returns the solutions to `x ^ n = a`.
-/
def nthRoots (n : ℕ) (a : R) : Multiset R :=
  roots ((X : R[X]) ^ n - C a)

@[simp]
/-
**Polynomial.mem_nthRoots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_nthRoots {n : Nat} (hn : 0 < n) {a x : R} : x in nthRoots n a ↔ x ^ n 
= a
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nthRoots.eq_1`：∀ {R : Type u} [inst : CommRing R] [inst_1 : I
sDomain R] (n : ℕ) (a : R),   Polynomial.nthRoots n a = (Polynomial.X ^ n - Poly
nomial.C a).ro…
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nthRoots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ nthRoots n a ↔ x ^ n = a := by
  rw [nthRoots, mem_roots (X_pow_sub_C_ne_zero hn a), IsRoot.def, eval_sub, eval_C, eval_pow,
    eval_X, sub_eq_zero]

@[simp]
/-
**Polynomial.nthRoots_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nthRoots_zero (r : R) : nthRoots 0 r = 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.roots_C`：roots_C (x : R) : (C x).roots = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nthRoots_zero (r : R) : nthRoots 0 r = 0 := by
  simp only [pow_zero, nthRoots, ← C_1, ← C_sub, roots_C]

@[simp]
/-
**Polynomial.nthRoots_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nthRoots_zero_right {R} [CommRing R] [IsDomain R] (n : Nat) : nthRoots n (
0 : R) = Multiset.replicate n 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nthRoots.eq_1`：∀ {R : Type u} [inst : CommRing R] [inst_1 : I
sDomain R] (n : ℕ) (a : R),   Polynomial.nthRoots n a = (Polynomial.X ^ n - Poly
nomial.C a).ro…
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Polynomial.roots_pow`：roots_pow (p : R[X]) (n : Nat) : (p ^ n).roots = n
 • p.roots
· 使用定理 `Polynomial.roots_X`：roots_X : roots (X : R[X]) = {0}
· 使用引理 `Multiset.nsmul_singleton`：nsmul_singleton (a : α) (n) : n • ({a} : Multi
set α) = replicate n a
-/
theorem nthRoots_zero_right {R} [CommRing R] [IsDomain R] (n : ℕ) :
    nthRoots n (0 : R) = Multiset.replicate n 0 := by
  rw [nthRoots, C.map_zero, sub_zero, roots_pow, roots_X, Multiset.nsmul_singleton]
/-
**Polynomial.card_nthRoots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_nthRoots (n : Nat) (a : R) : Multiset.card (nthRoots n a) <= n
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.card_roots`：card_roots (hp0 : p != 0) : (Multiset.card (roots
 p) : WithBot Nat) <= degree p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
-/
theorem card_nthRoots (n : ℕ) (a : R) : Multiset.card (nthRoots n a) ≤ n := by
  classical exact
  (if hn : n = 0 then
    if h : (X : R[X]) ^ n - C a = 0 then by
      simp [nthRoots, roots, h, empty_eq_zero, Multiset.card_zero]
    else
      WithBot.coe_le_coe.1
        (le_trans (card_roots h)
          (by
            rw [hn, pow_zero, ← C_1, ← map_sub]
            exact degree_C_le))
  else by
    rw [← Nat.cast_le (α := WithBot ℕ)]
    rw [← degree_X_pow_sub_C (Nat.pos_of_ne_zero hn) a]
    exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) a))

@[simp]
/-
**Polynomial.nthRoots_two_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nthRoots_two_eq_zero_iff {r : R} : nthRoots 2 r = 0 ↔ ¬IsSquare r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Polynomial.mem_nthRoots`：mem_nthRoots {n : Nat} (hn : 0 < n) {a x : R} :
 x in nthRoots n a ↔ x ^ n = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nthRoots_two_eq_zero_iff {r : R} : nthRoots 2 r = 0 ↔ ¬IsSquare r := by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_notMem, mem_nthRoots (by simp : 0 < 2),
    ← not_exists, eq_comm]

/-- The multiset `nthRoots ↑n a` as a Finset. Previously `nthRootsFinset n` was defined to be
`nthRoots n (1 : R)` as a Finset. That situation can be recovered by setting `a` to be `(1 : R)` -/
/-
**Polynomial.nthRootsFinset** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：nthRootsFinset (n : Nat) {R : Type*} (a : R) [CommRing R] [IsDomain R] : F
inset R
参数：n : Nat；a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset `nthRoots ↑n a` as a Finset. Previously `nthRootsFinset n` was defi
ned to be
`nthRoots n (1 : R)` as a Finset. That situation can be recovered by setting `a`
 to be `(1 : R)`
-/
def nthRootsFinset (n : ℕ) {R : Type*} (a : R) [CommRing R] [IsDomain R] : Finset R :=
  haveI := Classical.decEq R
  Multiset.toFinset (nthRoots n a)
/-
**Polynomial.nthRootsFinset_def** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：nthRootsFinset_def (n : Nat) {R : Type*} (a : R) [CommRing R] [IsDomain R]
 [DecidableEq R] : nthRootsFinset n a = Multiset.toFinset (nthRoots n a)
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
lemma nthRootsFinset_def (n : ℕ) {R : Type*} (a : R) [CommRing R] [IsDomain R] [DecidableEq R] :
    nthRootsFinset n a = Multiset.toFinset (nthRoots n a) := by
  unfold nthRootsFinset
  convert! rfl

@[simp]
/-
**Polynomial.mem_nthRootsFinset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_nthRootsFinset {n : Nat} (h : 0 < n) (a : R) {x : R} : x in nthRootsFi
nset n a ↔ x ^ (n : Nat) = a
参数：h : 0 < n；a : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.nthRootsFinset_def`：nthRootsFinset_def (n : Nat) {R : Type*} 
(a : R) [CommRing R] [IsDomain R] [DecidableEq R] : nthRootsFinset n a = Multise
t.toFinset (nthRoot…
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Polynomial.mem_nthRoots`：mem_nthRoots {n : Nat} (hn : 0 < n) {a x : R} :
 x in nthRoots n a ↔ x ^ n = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nthRootsFinset {n : ℕ} (h : 0 < n) (a : R) {x : R} :
    x ∈ nthRootsFinset n a ↔ x ^ (n : ℕ) = a := by
  classical
  rw [nthRootsFinset_def, mem_toFinset, mem_nthRoots h]

@[simp]
/-
**Polynomial.nthRootsFinset_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nthRootsFinset_zero (a : R) : nthRootsFinset 0 a = ∅
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.nthRootsFinset_def`：nthRootsFinset_def (n : Nat) {R : Type*} 
(a : R) [CommRing R] [IsDomain R] [DecidableEq R] : nthRootsFinset n a = Multise
t.toFinset (nthRoot…
· 使用定理 `Polynomial.nthRoots_zero`：nthRoots_zero (r : R) : nthRoots 0 r = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nthRootsFinset_zero (a : R) : nthRootsFinset 0 a = ∅ := by
  classical simp [nthRootsFinset_def]
/-
**Polynomial.map_mem_nthRootsFinset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_mem_nthRootsFinset {S F : Type*} [CommRing S] [IsDomain S] [FunLike F 
R S] [MonoidHomClass F R S] {a : R} {x : R} (hx : x in nthRootsFinset n a) (f : 
F) : f x in nthRootsFinset n (f a)
参数：hx : x in nthRootsFinset n a；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nthRootsFinset.congr_simp`：∀ (n n_1 : ℕ),   n = n_1 →     ∀ {
R : Type u_1} (a a_1 : R),       a = a_1 →         ∀ [inst : CommRing R] [inst_1
 : IsDomain R], Polynomial…
· 使用定理 `Polynomial.nthRootsFinset_zero`：nthRootsFinset_zero (a : R) : nthRootsFi
nset 0 a = ∅
· 使用定理 `Polynomial.mem_nthRootsFinset`：mem_nthRootsFinset {n : Nat} (h : 0 < n) 
(a : R) {x : R} : x in nthRootsFinset n a ↔ x ^ (n : Nat) = a
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem map_mem_nthRootsFinset {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [MonoidHomClass F R S] {a : R} {x : R} (hx : x ∈ nthRootsFinset n a) (f : F) :
    f x ∈ nthRootsFinset n (f a) := by
  by_cases hn : n = 0
  · simp [hn] at hx
  · rw [mem_nthRootsFinset <| Nat.pos_of_ne_zero hn, ← map_pow, (mem_nthRootsFinset
      (Nat.pos_of_ne_zero hn) a).1 hx]
/-
**Polynomial.map_mem_nthRootsFinset_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_mem_nthRootsFinset_one {S F : Type*} [CommRing S] [IsDomain S] [FunLik
e F R S] [RingHomClass F R S] {x : R} (hx : x in nthRootsFinset n 1) (f : F) : f
 x in nthRootsFinset n 1
参数：hx : x in nthRootsFinset n 1；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_mem_nthRootsFinset`：map_mem_nthRootsFinset {S F : Type*} 
[CommRing S] [IsDomain S] [FunLike F R S] [MonoidHomClass F R S] {a : R} {x : R}
 (hx : x in nthRootsFin…
-/
theorem map_mem_nthRootsFinset_one {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [RingHomClass F R S] {x : R} (hx : x ∈ nthRootsFinset n 1) (f : F) :
    f x ∈ nthRootsFinset n 1 := by
  rw [← (map_one f)]
  exact map_mem_nthRootsFinset hx _
/-
**Polynomial.mul_mem_nthRootsFinset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mul_mem_nthRootsFinset {η₁ η₂ : R} {a₁ a₂ : R} (hη₁ : η₁ in nthRootsFinset
 n a₁) (hη₂ : η₂ in nthRootsFinset n a₂) : η₁ * η₂ in nthRootsFinset n (a₁ * a₂)
参数：hη₁ : η₁ in nthRootsFinset n a₁；hη₂ : η₂ in nthRootsFinset n a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nthRootsFinset_zero`：nthRootsFinset_zero (a : R) : nthRootsFi
nset 0 a = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_nthRootsFinset`：mem_nthRootsFinset {n : Nat} (h : 0 < n) 
(a : R) {x : R} : x in nthRootsFinset n a ↔ x ^ (n : Nat) = a
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
-/
theorem mul_mem_nthRootsFinset
    {η₁ η₂ : R} {a₁ a₂ : R} (hη₁ : η₁ ∈ nthRootsFinset n a₁) (hη₂ : η₂ ∈ nthRootsFinset n a₂) :
    η₁ * η₂ ∈ nthRootsFinset n (a₁ * a₂) := by
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη₁
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos] at hη₁ hη₂ ⊢
    rw [mul_pow, hη₁, hη₂]
/-
**Polynomial.ne_zero_of_mem_nthRootsFinset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：ne_zero_of_mem_nthRootsFinset {η : R} {a : R} (ha : a != 0) (hη : η in nth
RootsFinset n a) : η != 0
参数：ha : a != 0；hη : η in nthRootsFinset n a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nthRootsFinset_zero`：nthRootsFinset_zero (a : R) : nthRootsFi
nset 0 a = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Polynomial.mem_nthRootsFinset`：mem_nthRootsFinset {n : Nat} (h : 0 < n) 
(a : R) {x : R} : x in nthRootsFinset n a ↔ x ^ (n : Nat) = a
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem ne_zero_of_mem_nthRootsFinset {η : R} {a : R} (ha : a ≠ 0) (hη : η ∈ nthRootsFinset n a) :
    η ≠ 0 := by
  rintro rfl
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos, zero_pow n.succ_ne_zero] at hη
    exact ha hη.symm
/-
**Polynomial.one_mem_nthRootsFinset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：one_mem_nthRootsFinset (hn : 0 < n) : 1 in nthRootsFinset n (1 : R)
参数：hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_nthRootsFinset`：mem_nthRootsFinset {n : Nat} (h : 0 < n) 
(a : R) {x : R} : x in nthRootsFinset n a ↔ x ^ (n : Nat) = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem one_mem_nthRootsFinset (hn : 0 < n) : 1 ∈ nthRootsFinset n (1 : R) := by
  rw [mem_nthRootsFinset hn, one_pow]
/-
**Polynomial.nthRoots_two_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：nthRoots_two_one : Polynomial.nthRoots 2 (1 : R) = {-1,1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.nthRoots.eq_1`：∀ {R : Type u} [inst : CommRing R] [inst_1 : I
sDomain R] (n : ℕ) (a : R),   Polynomial.nthRoots n a = (Polynomial.X ^ n - Poly
nomial.C a).ro…
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `Polynomial.roots_X_add_C`：roots_X_add_C (r : R) : roots (X + C r) = {-r}
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
-/
lemma nthRoots_two_one : Polynomial.nthRoots 2 (1 : R) = {-1,1} := by
  have h₁ : (X ^ 2 - C 1 : R[X]) = (X + C 1) * (X - C 1) := by simp [← sq_sub_sq]
  have h₂ : (X ^ 2 - C 1 : R[X]) ≠ 0 := fun h ↦ by simpa using congrArg (coeff · 0) h
  rw [nthRoots, h₁, roots_mul (h₁ ▸ h₂), roots_X_add_C, roots_X_sub_C]; rfl

end NthRoots

/-
**Polynomial.zero_of_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：zero_of_eval_zero [Infinite R] (p : R[X]) (h : forall x, p.eval x = 0) : p
 = 0
参数：p : R[X]；h : forall x, p.eval x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Fintype.false`：∀ {α : Type u_1} [Infinite α] (_h : Fintype α), False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
-/
theorem zero_of_eval_zero [Infinite R] (p : R[X]) (h : ∀ x, p.eval x = 0) : p = 0 := by
  classical
  by_contra hp
  refine @Fintype.false R _ ?_
  exact ⟨p.roots.toFinset, fun x => Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _))⟩
/-
**Polynomial.funext** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：funext [Infinite R] {p q : R[X]} (ext : forall r : R, p.eval r = q.eval r)
 : p = q
参数：ext : forall r : R, p.eval r = q.eval r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.zero_of_eval_zero`：zero_of_eval_zero [Infinite R] (p : R[X]) 
(h : forall x, p.eval x = 0) : p = 0
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
-/
theorem funext [Infinite R] {p q : R[X]} (ext : ∀ r : R, p.eval r = q.eval r) : p = q := by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub, sub_eq_zero, ext]

variable [CommRing T]

/-- Given a polynomial `p` with coefficients in a ring `T` and a `T`-algebra `S`, `aroots p S` is
the multiset of roots of `p` regarded as a polynomial over `S`. -/
/-
**Polynomial.aroots** 是 Mathlib 中的一个缩写定义，位于命名空间 `Polynomial`。
形式化陈述：aroots (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Multiset S
参数：p : T[X]；S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a polynomial `p` with coefficients in a ring `T` and a `T`-algebra `S`, `a
roots p S` is
the multiset of roots of `p` regarded as a polynomial over `S`.
-/
noncomputable abbrev aroots (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Multiset S :=
  (p.map (algebraMap T S)).roots
/-
**Polynomial.aroots_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : p.aroo
ts S = (p.map (algebraMap T S)).roots
参数：p : T[X]；S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aroots_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    p.aroots S = (p.map (algebraMap T S)).roots :=
  rfl
/-
**Polynomial.mem_aroots'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_aroots' [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {a : S} : a
 in p.aroots S ↔ p.map (algebraMap T S) != 0 ∧ aeval a p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_roots'`：mem_roots' : a in p.roots ↔ p != 0 ∧ IsRoot p a
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_aroots' [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {a : S} :
    a ∈ p.aroots S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_roots', IsRoot.def, ← eval₂_eq_eval_map, aeval_def]
/-
**Polynomial.mem_aroots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_aroots [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.Is
TorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔ p != 0 ∧ aeval a p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_aroots'`：mem_aroots' [CommRing S] [IsDomain S] [Algebra T
 S] {p : T[X]} {a : S} : a in p.aroots S ↔ p.map (algebraMap T S) != 0 ∧ aeval a
 p = 0
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_aroots [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a ∈ p.aroots S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_aroots', Polynomial.map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S
/-
**Polynomial.aroots_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.Is
TorsionFree T S] {p q : T[X]} (hpq : p * q != 0) : (p * q).aroots S = p.aroots S
 + q.aroots S
参数：hpq : p * q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
-/
theorem aroots_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {p q : T[X]} (hpq : p * q ≠ 0) :
    (p * q).aroots S = p.aroots S + q.aroots S := by
  suffices map (algebraMap T S) p * map (algebraMap T S) q ≠ 0 by
    rw [aroots_def, Polynomial.map_mul, roots_mul this]
  rwa [← Polynomial.map_mul, Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective T S)]

@[simp]
/-
**Polynomial.aroots_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_X_sub_C [CommRing S] [IsDomain S] [Algebra T S] (r : T) : aroots (X
 - C r) S = {algebraMap T S r}
参数：r : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
-/
theorem aroots_X_sub_C [CommRing S] [IsDomain S] [Algebra T S]
    (r : T) : aroots (X - C r) S = {algebraMap T S r} := by
  rw [aroots_def, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]

@[simp]
/-
**Polynomial.aroots_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_X [CommRing S] [IsDomain S] [Algebra T S] : aroots (X : T[X]) S = {
0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.roots_X`：roots_X : roots (X : R[X]) = {0}
-/
theorem aroots_X [CommRing S] [IsDomain S] [Algebra T S] :
    aroots (X : T[X]) S = {0} := by
  rw [aroots_def, map_X, roots_X]

@[simp]
/-
**Polynomial.aroots_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).aroots S 
= 0
参数：a : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.roots_C`：roots_C (x : R) : (C x).roots = 0
-/
theorem aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).aroots S = 0 := by
  rw [aroots_def, map_C, roots_C]

@[simp]
/-
**Polynomial.aroots_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).aroot
s S = 0
参数：S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.aroots_C`：aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a
 : T) : (C a).aroots S = 0
-/
theorem aroots_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).aroots S = 0 := by
  rw [← C_0, aroots_C]

@[simp]
/-
**Polynomial.aroots_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_one [CommRing S] [IsDomain S] [Algebra T S] : (1 : T[X]).aroots S =
 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.aroots_C`：aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a
 : T) : (C a).aroots S = 0
-/
theorem aroots_one [CommRing S] [IsDomain S] [Algebra T S] :
    (1 : T[X]).aroots S = 0 :=
  aroots_C 1

@[simp]
/-
**Polynomial.aroots_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_neg [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) : (-p).aroot
s S = p.aroots S
参数：p : T[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynomi
al T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Alg
ebra T S], p…
· 使用定理 `Polynomial.map_neg`：∀ {R : Type u} [inst : Ring R] {p : Polynomial R} {S
 : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (-p) = -Polynom
ial.map …
· 使用引理 `Polynomial.roots_neg`：roots_neg (p : R[X]) : (-p).roots = p.roots
-/
theorem aroots_neg [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) :
    (-p).aroots S = p.aroots S := by
  rw [aroots, Polynomial.map_neg, roots_neg]

@[simp]
/-
**Polynomial.aroots_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_C_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.
IsTorsionFree T S] {a : T} (p : T[X]) (ha : a != 0) : (C a * p).aroots S = p.aro
ots S
参数：p : T[X]；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.roots_C_mul`：roots_C_mul (p : R[X]) (ha : a != 0) : (C a * p)
.roots = p.roots
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem aroots_C_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a ≠ 0) :
    (C a * p).aroots S = p.aroots S := by
  rw [aroots_def, Polynomial.map_mul, map_C, roots_C_mul]
  rwa [map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

@[simp]
/-
**Polynomial.aroots_smul_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_smul_nonzero [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [
Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a != 0) : (a • p).aroots S = 
p.aroots S
参数：p : T[X]；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smul_eq_C_mul`：smul_eq_C_mul (a : R) : a • p = C a * p
· 使用定理 `Polynomial.aroots_C_mul`：aroots_C_mul [IsDomain T] [CommRing S] [IsDomai
n S] [Algebra T S] [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a != 0) :
 (C a * p).ar…
-/
theorem aroots_smul_nonzero [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a ≠ 0) :
    (a • p).aroots S = p.aroots S := by
  rw [smul_eq_C_mul, aroots_C_mul _ ha]

@[simp]
/-
**Polynomial.aroots_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_pow [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) (n : Nat) : 
(p ^ n).aroots S = n • p.aroots S
参数：p : T[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.roots_pow`：roots_pow (p : R[X]) (n : Nat) : (p ^ n).roots = n
 • p.roots
-/
theorem aroots_pow [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) (n : ℕ) :
    (p ^ n).aroots S = n • p.aroots S := by
  rw [aroots_def, Polynomial.map_pow, roots_pow]
/-
**Polynomial.aroots_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_X_pow [CommRing S] [IsDomain S] [Algebra T S] (n : Nat) : (X ^ n : 
T[X]).aroots S = n • ({0} : Multiset S)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_pow`：aroots_pow [CommRing S] [IsDomain S] [Algebra T S
] (p : T[X]) (n : Nat) : (p ^ n).aroots S = n • p.aroots S
· 使用定理 `Polynomial.aroots_X`：aroots_X [CommRing S] [IsDomain S] [Algebra T S] : 
aroots (X : T[X]) S = {0}
-/
theorem aroots_X_pow [CommRing S] [IsDomain S] [Algebra T S] (n : ℕ) :
    (X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_pow, aroots_X]
/-
**Polynomial.aroots_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_C_mul_X_pow [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [M
odule.IsTorsionFree T S] {a : T} (ha : a != 0) (n : Nat) : (C a * X ^ n : T[X]).
aroots S = n • ({0} : Multiset S)
参数：ha : a != 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_C_mul`：aroots_C_mul [IsDomain T] [CommRing S] [IsDomai
n S] [Algebra T S] [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a != 0) :
 (C a * p).ar…
· 使用定理 `Polynomial.aroots_X_pow`：aroots_X_pow [CommRing S] [IsDomain S] [Algebra
 T S] (n : Nat) : (X ^ n : T[X]).aroots S = n • ({0} : Multiset S)
-/
theorem aroots_C_mul_X_pow [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (ha : a ≠ 0) (n : ℕ) :
    (C a * X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_C_mul _ ha, aroots_X_pow]

@[simp]
/-
**Polynomial.aroots_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_monomial [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Modu
le.IsTorsionFree T S] {a : T} (ha : a != 0) (n : Nat) : (monomial n a).aroots S 
= n • ({0} : Multiset S)
参数：ha : a != 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.aroots_C_mul_X_pow`：aroots_C_mul_X_pow [IsDomain T] [CommRing
 S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : T} (ha : a != 0) 
(n : Nat) : (C a * …
-/
theorem aroots_monomial [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (ha : a ≠ 0) (n : ℕ) :
    (monomial n a).aroots S = n • ({0} : Multiset S) := by
  rw [← C_mul_X_pow_eq_monomial, aroots_C_mul_X_pow ha]

variable (R S) in
@[simp]
/-
**Polynomial.aroots_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aroots_map (p : T[X]) [CommRing S] [Algebra T S] [Algebra S R] [Algebra T 
R] [IsScalarTower T S R] : (p.map (algebraMap T S)).aroots R = p.aroots R
参数：p : T[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
-/
theorem aroots_map (p : T[X]) [CommRing S] [Algebra T S] [Algebra S R] [Algebra T R]
    [IsScalarTower T S R] :
    (p.map (algebraMap T S)).aroots R = p.aroots R := by
  rw [aroots_def, aroots_def, map_map, IsScalarTower.algebraMap_eq T S R]

/-- The set of distinct roots of `p` in `S`.

If you have a non-separable polynomial, use `Polynomial.aroots` for the multiset
where multiple roots have the appropriate multiplicity. -/
/-
**Polynomial.rootSet** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S
参数：p : T[X]；S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of distinct roots of `p` in `S`.

If you have a non-separable polynomial, use `Polynomial.aroots` for the multiset
where multiple roots have the appropriate multiplicity.
-/
def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S :=
  haveI := Classical.decEq S
  (p.aroots S).toFinset
/-
**Polynomial.rootSet_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] [Decida
bleEq S] : p.rootSet S = (p.aroots S).toFinset
参数：p : T[X]；S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynom
ial T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Al
gebra T S], p…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
theorem rootSet_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] [DecidableEq S] :
    p.rootSet S = (p.aroots S).toFinset := by
  rw [rootSet]
  convert! rfl

@[simp]
/-
**Polynomial.rootSet_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).rootSet 
S = ∅
参数：a : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Polynomial.aroots_C`：aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a
 : T) : (C a).aroots S = 0
· 使用定理 `Multiset.toFinset_zero`：toFinset_zero : toFinset (0 : Multiset α) = ∅
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
-/
theorem rootSet_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).rootSet S = ∅ := by
  classical
  rw [rootSet_def, aroots_C, Multiset.toFinset_zero, Finset.coe_empty]

@[simp]
/-
**Polynomial.rootSet_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).root
Set S = ∅
参数：S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.rootSet_C`：rootSet_C [CommRing S] [IsDomain S] [Algebra T S] 
(a : T) : (C a).rootSet S = ∅
-/
theorem rootSet_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).rootSet S = ∅ := by
  rw [← C_0, rootSet_C]

@[simp]
/-
**Polynomial.rootSet_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_one (S) [CommRing S] [IsDomain S] [Algebra T S] : (1 : T[X]).rootS
et S = ∅
参数：S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.rootSet_C`：rootSet_C [CommRing S] [IsDomain S] [Algebra T S] 
(a : T) : (C a).rootSet S = ∅
-/
theorem rootSet_one (S) [CommRing S] [IsDomain S] [Algebra T S] : (1 : T[X]).rootSet S = ∅ := by
  rw [← C_1, rootSet_C]

@[simp]
/-
**Polynomial.rootSet_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_neg (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : (-p).
rootSet S = p.rootSet S
参数：p : T[X]；S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynom
ial T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Al
gebra T S], p…
· 使用定理 `Polynomial.aroots_neg`：aroots_neg [CommRing S] [IsDomain S] [Algebra T S
] (p : T[X]) : (-p).aroots S = p.aroots S
-/
theorem rootSet_neg (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    (-p).rootSet S = p.rootSet S := by
  rw [rootSet, aroots_neg, rootSet]
/-
**Polynomial.rootSetFintype** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：rootSetFintype (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T
 S] : Fintype (p.rootSet S)
参数：p : T[X]；S : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rootSetFintype (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    Fintype (p.rootSet S) :=
  FinsetCoe.fintype _
/-
**Polynomial.rootSet_finite** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_finite (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T
 S] : (p.rootSet S).Finite
参数：p : T[X]；S : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem rootSet_finite (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    (p.rootSet S).Finite :=
  Set.toFinite _

/-- The set of roots of all polynomials of bounded degree and having coefficients in a finite set
is finite. -/
/-
**Polynomial.bUnion_roots_finite** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：bUnion_roots_finite {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [
DecidableEq S] (m : R ->+* S) (d : Nat) {U : Set R} (h : U.Finite) : (⋃ (f : R[X
]) (_ : f.natDegree <= d ∧ forall i, f.coeff i in U), ((f.map m).roots.toFinset 
: Set S)).Finite
参数：m : R ->+* S；d : Nat；h : U.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.pi`：∀ {ι : Type u_3} [Finite ι] {κ : ι → Type u_4} {t : (i : 
ι) → Set (κ i)},   (∀ (i : ι), (t i).Finite) → (Set.univ.pi t).Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.ext_iff_natDegree_le`：ext_iff_natDegree_le {p q : R[X]} {n : 
Nat} (hp : p.natDegree <= n) (hq : q.natDegree <= n) : p = q ↔ forall i <= n, p.
coeff i = q.coeff i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
The set of roots of all polynomials of bounded degree and having coefficients in
 a finite set
is finite.
-/
theorem bUnion_roots_finite {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [DecidableEq S]
    (m : R →+* S) (d : ℕ) {U : Set R} (h : U.Finite) :
    (⋃ (f : R[X]) (_ : f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U),
        ((f.map m).roots.toFinset : Set S)).Finite :=
  Set.Finite.biUnion
    (by
      -- We prove that the set of polynomials under consideration is finite because its
      -- image by the injective map `π` is finite
      let π : R[X] → Fin (d + 1) → R := fun f i => f.coeff i
      refine ((Set.Finite.pi fun _ => h).subset <| ?_).of_finite_image (?_ : Set.InjOn π _)
      · exact Set.image_subset_iff.2 fun f hf i _ => hf.2 i
      · refine fun x hx y hy hxy => (ext_iff_natDegree_le hx.1 hy.1).2 fun i hi => ?_
        exact id congr_fun hxy ⟨i, Nat.lt_succ_of_le hi⟩)
    fun _ _ => Finset.finite_toSet _

/-- A version of `mem_rootSet` that requires the polynomial to be non-zero after mapping
instead of requiring it to be non-zero and `NoZeroSMulDivisors`. -/
/-
**Polynomial.mem_rootSet'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_rootSet' {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S
] {a : S} : a in p.rootSet S ↔ p.map (algebraMap T S) != 0 ∧ aeval a p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Polynomial.mem_aroots'`：mem_aroots' [CommRing S] [IsDomain S] [Algebra T
 S] {p : T[X]} {a : S} : a in p.aroots S ↔ p.map (algebraMap T S) != 0 ∧ aeval a
 p = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A version of `mem_rootSet` that requires the polynomial to be non-zero after map
ping
instead of requiring it to be non-zero and `NoZeroSMulDivisors`.
-/
theorem mem_rootSet' {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S] {a : S} :
    a ∈ p.rootSet S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  classical
  rw [rootSet_def, Finset.mem_coe, mem_toFinset, mem_aroots']

/-- A version of `mem_rootSet'` that requires `Module.IsTorsionFree` and for the polynomial to be
non-zero instead of requiring it to be non-zero after mapping. -/
/-
**Polynomial.mem_rootSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] 
[Algebra T S] [Module.IsTorsionFree T S] {a : S} : a in p.rootSet S ↔ p != 0 ∧ a
eval a p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_rootSet'`：mem_rootSet' {p : T[X]} {S : Type*} [CommRing S
] [IsDomain S] [Algebra T S] {a : S} : a in p.rootSet S ↔ p.map (algebraMap T S)
 != 0 ∧ aeval…
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A version of `mem_rootSet'` that requires `Module.IsTorsionFree` and for the pol
ynomial to be
non-zero instead of requiring it to be non-zero after mapping.
-/
theorem mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : S} : a ∈ p.rootSet S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_rootSet', Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective T S)]
/-
**Polynomial.mem_rootSet_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mem_rootSet_of_ne {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDoma
in S] [Algebra T S] [Module.IsTorsionFree T S] (hp : p != 0) {a : S} : a in p.ro
otSet S ↔ aeval a p = 0
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.mem_rootSet`：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] 
[CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : S} : a i
n p.rootSet …
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
-/
lemma mem_rootSet_of_ne {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] (hp : p ≠ 0) {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 :=
  mem_rootSet.trans <| and_iff_right hp
/-
**Polynomial.preimage_eval_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：preimage_eval_singleton (hp : p != C a) : p.eval ⁻¹' {a} = (p - C a).rootS
et R
参数：hp : p != C a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.mem_rootSet_of_ne`：mem_rootSet_of_ne {p : T[X]} {S : Type*} [
IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] (
hp : p != 0) {a : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_eval_singleton (hp : p ≠ C a) : p.eval ⁻¹' {a} = (p - C a).rootSet R := by
  ext; simp [mem_rootSet_of_ne (sub_ne_zero.mpr hp), sub_eq_zero]
/-
**Polynomial.Monic.mem_rootSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {T : Type w} [inst : CommRing T] {p : Polynomial T},   p.Monic →     ∀ {
S : Type u_1} [inst_1 : CommRing S] [inst_2 : IsDomain S] [inst_3 : Algebra T S]
 {a : S},       a ∈ p.rootSet S ↔ (Polynomial.aeval a) p = 0
参数：Polynomial.aeval a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Monic.mem_rootSet {p : T[X]} (hp : Monic p) {S : Type*} [CommRing S] [IsDomain S]
    [Algebra T S] {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 := by
  simp [Polynomial.mem_rootSet', (hp.map (algebraMap T S)).ne_zero]
/-
**Polynomial.rootSet_maps_to'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_maps_to' {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S]
 [CommRing S'] [IsDomain S'] [Algebra T S'] (hp : p.map (algebraMap T S') = 0 ->
 p.map (algebraMap T S) = 0) (f : S ->ₐ[T] S') : (p.rootSet S).MapsTo f (p.rootS
et S')
参数：hp : p.map (algebraMap T S') = 0 -> p.map (algebraMap T S) = 0；f : S ->ₐ[T] S
'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_rootSet'`：mem_rootSet' {p : T[X]} {S : Type*} [CommRing S
] [IsDomain S] [Algebra T S] {a : S} : a in p.rootSet S ↔ p.map (algebraMap T S)
 != 0 ∧ aeval…
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem rootSet_maps_to' {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] (hp : p.map (algebraMap T S') = 0 → p.map (algebraMap T S) = 0)
    (f : S →ₐ[T] S') : (p.rootSet S).MapsTo f (p.rootSet S') := fun x hx => by
  rw [mem_rootSet'] at hx ⊢
  rw [aeval_algHom, AlgHom.comp_apply, hx.2, _root_.map_zero]
  exact ⟨mt hp hx.1, rfl⟩
/-
**Polynomial.ne_zero_of_mem_rootSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ne_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] 
{a : S} (h : a in p.rootSet S) : p != 0
参数：h : a in p.rootSet S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet_zero`：rootSet_zero (S) [CommRing S] [IsDomain S] [Alg
ebra T S] : (0 : T[X]).rootSet S = ∅
-/
theorem ne_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (h : a ∈ p.rootSet S) : p ≠ 0 := fun hf => by rwa [hf, rootSet_zero] at h
/-
**Polynomial.aeval_eq_zero_of_mem_rootSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：aeval_eq_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra
 T S] {a : S} (hx : a in p.rootSet S) : aeval a p = 0
参数：hx : a in p.rootSet S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_rootSet'`：mem_rootSet' {p : T[X]} {S : Type*} [CommRing S
] [IsDomain S] [Algebra T S] {a : S} : a in p.rootSet S ↔ p.map (algebraMap T S)
 != 0 ∧ aeval…
-/
theorem aeval_eq_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (hx : a ∈ p.rootSet S) : aeval a p = 0 :=
  (mem_rootSet'.1 hx).2
/-
**Polynomial.rootSet_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：rootSet_mapsTo {p : T[X]} [IsDomain T] {S S' : Type*} [CommRing S] [IsDoma
in S] [Algebra T S] [CommRing S'] [IsDomain S'] [Algebra T S'] [Module.IsTorsion
Free T S'] (f : S ->ₐ[T] S') : (p.rootSet S).MapsTo f (p.rootSet S')
参数：f : S ->ₐ[T] S'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.rootSet_maps_to'`：rootSet_maps_to' {p : T[X]} {S S'} [CommRin
g S] [IsDomain S] [Algebra T S] [CommRing S'] [IsDomain S'] [Algebra T S'] (hp :
 p.map (algebraMa…
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma rootSet_mapsTo {p : T[X]} [IsDomain T] {S S' : Type*} [CommRing S] [IsDomain S] [Algebra T S]
    [CommRing S'] [IsDomain S'] [Algebra T S'] [Module.IsTorsionFree T S'] (f : S →ₐ[T] S') :
    (p.rootSet S).MapsTo f (p.rootSet S') := by
  refine rootSet_maps_to' (fun h₀ => ?_) f
  obtain rfl : p = 0 :=
    map_injective _ (FaithfulSMul.algebraMap_injective T S') (by rwa [Polynomial.map_zero])
  exact Polynomial.map_zero _
/-
**Polynomial.mem_rootSet_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_rootSet_of_injective [CommRing S] {p : S[X]} [Algebra S R] (h : Functi
on.Injective (algebraMap S R)) {x : R} (hp : p != 0) : x in p.rootSet R ↔ aeval 
x p = 0
参数：h : Function.Injective (algebraMap S R)；hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Polynomial.mem_roots_map_of_injective`：mem_roots_map_of_injective [Semir
ing S] {p : S[X]} {f : S ->+* R} (hf : Function.Injective f) {x : R} (hp : p != 
0) : x in (p.map f).roots ↔…
-/
theorem mem_rootSet_of_injective [CommRing S] {p : S[X]} [Algebra S R]
    (h : Function.Injective (algebraMap S R)) {x : R} (hp : p ≠ 0) :
    x ∈ p.rootSet R ↔ aeval x p = 0 := by
  classical
  exact Multiset.mem_toFinset.trans (mem_roots_map_of_injective h hp)

@[simp]
/-
**Polynomial.nthRootsFinset_toSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nthRootsFinset_toSet {n : Nat} (h : 0 < n) (a : R) : nthRootsFinset n a = 
{r | r ^ n = a}
参数：h : 0 < n；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nthRootsFinset_toSet {n : ℕ} (h : 0 < n) (a : R) :
    nthRootsFinset n a = {r | r ^ n = a} := by
  ext x
  simp_all
/-
**Polynomial.smul_mem_rootSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_mem_rootSet [CommRing S] [Algebra S R] {G : Type*} [Monoid G] [MulSem
iringAction G R] [SMulCommClass G S R] {f : S[X]} (g : G) {x : R} (hx : x in f.r
ootSet R) : g • x in f.rootSet R
参数：g : G；hx : x in f.rootSet R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_rootSet'`：mem_rootSet' {p : T[X]} {S : Type*} [CommRing S
] [IsDomain S] [Algebra T S] {a : S} : a in p.rootSet S ↔ p.map (algebraMap T S)
 != 0 ∧ aeval…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_smul`：aeval_smul (f : R[X]) {G : Type*} [Monoid G] [Mul
SemiringAction G A] [SMulCommClass G R A] (g : G) (x : A) : f.aeval (g • x) = g 
• (f.aeval …
· 使用定理 `Polynomial.aeval_eq_zero_of_mem_rootSet`：aeval_eq_zero_of_mem_rootSet {p
 : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S} (hx : a in p.rootSet S)
 : aeval a p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem smul_mem_rootSet [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    (g : G) {x : R} (hx : x ∈ f.rootSet R) : g • x ∈ f.rootSet R := by
  simp [mem_rootSet', aeval_smul, aeval_eq_zero_of_mem_rootSet hx, (mem_rootSet'.mp hx).1]
/-
**Polynomial.smul_mem_rootSet_iff_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：smul_mem_rootSet_iff_of_isUnit [CommRing S] [Algebra S R] {G : Type*} [Mon
oid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]} {g : G} (hg : Is
Unit g) {x : R} : g • x in f.rootSet R ↔ x in f.rootSet R
参数：hg : IsUnit g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.smul_mem_rootSet`：smul_mem_rootSet [CommRing S] [Algebra S R]
 {G : Type*} [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
 (g : G) {x : R} …
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem smul_mem_rootSet_iff_of_isUnit [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {g : G} (hg : IsUnit g) {x : R} : g • x ∈ f.rootSet R ↔ x ∈ f.rootSet R := by
  refine ⟨?_, smul_mem_rootSet g⟩
  obtain ⟨g, rfl⟩ := hg
  exact fun hx ↦ inv_smul_smul g x ▸ smul_mem_rootSet _ hx
/-
**Polynomial.smul_mem_rootSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_mem_rootSet_iff [CommRing S] [Algebra S R] {G : Type*} [Group G] [Mul
SemiringAction G R] [SMulCommClass G S R] {f : S[X]} {g : G} {x : R} : g • x in 
f.rootSet R ↔ x in f.rootSet R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.smul_mem_rootSet_iff_of_isUnit`：smul_mem_rootSet_iff_of_isUni
t [CommRing S] [Algebra S R] {G : Type*} [Monoid G] [MulSemiringAction G R] [SMu
lCommClass G S R] {f : S[X]} {g…
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
-/
theorem smul_mem_rootSet_iff [CommRing S] [Algebra S R] {G : Type*}
    [Group G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {g : G} {x : R} : g • x ∈ f.rootSet R ↔ x ∈ f.rootSet R :=
  smul_mem_rootSet_iff_of_isUnit (Group.isUnit g)
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing S] [Algebra S R] (G : Type*)
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] (f : S[X]) :
    MulAction G (f.rootSet R) where
  smul g x := ⟨g • x.1, smul_mem_rootSet g x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

@[simp]
/-
**Polynomial.rootSet.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.rootSet`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : IsDomain R] [ins
t_2 : CommRing S] [inst_3 : Algebra S R]   {G : Type u_1} [inst_4 : Monoid G] [i
nst_5 : MulSemiringAction G R] [inst_6 : SMulCommClass G S R] {f : Polynomial S}
   (g : G) (x : ↑(f.rootSet R)), ↑(g • x) = g • ↑x
参数：g : G；x : ↑(f.rootSet R)；g • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rootSet.coe_smul [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    (g : G) (x : f.rootSet R) : (g • x : f.rootSet R) = g • (x : R) :=
  rfl
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing S] [Algebra S R] (G H : Type*)
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R]
    [Monoid H] [MulSemiringAction H R] [SMulCommClass H S R]
    [SMulCommClass G H R] (f : S[X]) : SMulCommClass G H (f.rootSet R) where
  smul_comm _ _ _ := Subtype.ext <| smul_comm _ _ _
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing S] [Algebra S R] (G H : Type*)
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R]
    [Monoid H] [MulSemiringAction H R] [SMulCommClass H S R]
    [SMul G H] [IsScalarTower G H R] (f : S[X]) : IsScalarTower G H (f.rootSet R) where
  smul_assoc _ _ _ := Subtype.ext <| smul_assoc _ _ _

end Roots

/-
**Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero** 是 Mathlib 中的一个引理，位于命
名空间 `Polynomial`。
形式化陈述：eq_zero_of_natDegree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R]
 (p : R[X]) {ι} [Fintype ι] {f : ι -> R} (hf : Function.Injective f) (heval : fo
rall i, p.eval (f i) = 0) (hcard : natDegree p < Fintype.card ι) : p = 0
参数：p : R[X]；hf : Function.Injective f；heval : forall i, p.eval (f i) = 0；hcard :
 natDegree p < Fintype.card ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Multiset.toFinset_card_le`：Multiset.toFinset_card_le : #m.toFinset <= Mu
ltiset.card m
· 使用定理 `Polynomial.card_roots'`：card_roots' (p : R[X]) : Multiset.card p.roots <
= natDegree p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.card_range_of_injective`：card_range_of_injective [Fintype α] {f : α 
-> β} (hf : Injective f) [Fintype (range f)] : Fintype.card (range f) = Fintype.
card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Set.toFinset_range`：toFinset_range [DecidableEq α] [Fintype β] (f : β ->
 α) [Fintype (Set.range f)] : (Set.range f).toFinset = Finset.univ.image f
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R]
    (p : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i, p.eval (f i) = 0) (hcard : natDegree p < Fintype.card ι) : p = 0 := by
  classical
  by_contra hp
  refine lt_irrefl #p.roots.toFinset ?_
  calc
    #p.roots.toFinset ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ natDegree p := Polynomial.card_roots' p
    _ < Fintype.card ι := hcard
    _ = Fintype.card (Set.range f) := (Set.card_range_of_injective hf).symm
    _ = #(Finset.univ.image f) := by rw [← Set.toFinset_card, Set.toFinset_range]
    _ ≤ #p.roots.toFinset := Finset.card_mono ?_
  intro _
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset, mem_roots', ne_eq,
    IsRoot.def, forall_exists_index, hp, not_false_eq_true]
  rintro x rfl
  exact heval _
/-
**Polynomial.eq_of_natDegree_lt_card_of_eval_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polyn
omial`。
形式化陈述：eq_of_natDegree_lt_card_of_eval_eq {R} [CommRing R] [IsDomain R] (p q : R[
X]) {ι} [Fintype ι] {f : ι -> R} (hf : Function.Injective f) (heval : forall i :
 ι, eval (f i) p = eval (f i) q) (hcard : max p.natDegree q.natDegree < Fintype.
card ι) : p = q
参数：p q : R[X]；hf : Function.Injective f；heval : forall i : ι, eval (f i) p = eva
l (f i) q；hcard : max p.natDegree q.natDegree < Fintype.card ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`：eq_zero_of_natD
egree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R] (p : R[X]) {ι} [Fint
ype ι] {f : ι -> R} (hf : Function.Injective …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
-/
lemma eq_of_natDegree_lt_card_of_eval_eq {R} [CommRing R] [IsDomain R]
    (p q : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i : ι, eval (f i) p = eval (f i) q)
    (hcard : max p.natDegree q.natDegree < Fintype.card ι) : p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
  · simpa [sub_eq_zero]
  · grind [natDegree_sub_le]
/-
**Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'** 是 Mathlib 中的一个引理，位于
命名空间 `Polynomial`。
形式化陈述：eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {R} [CommRing R] [IsDomain R
] (p : R[X]) (s : Finset R) (heval : forall i in s, p.eval i = 0) (hcard : natDe
gree p < #s) : p = 0
参数：p : R[X]；s : Finset R；heval : forall i in s, p.eval i = 0；hcard : natDegree p
 < #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`：eq_zero_of_natD
egree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R] (p : R[X]) {ι} [Fint
ype ι] {f : ι -> R} (hf : Function.Injective …
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
-/
lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {R} [CommRing R] [IsDomain R]
    (p : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = 0) (hcard : natDegree p < #s) :
    p = 0 :=
  eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Subtype.val_injective
    (fun i : s ↦ heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)
/-
**Polynomial.eq_of_natDegree_lt_card_of_eval_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Poly
nomial`。
形式化陈述：eq_of_natDegree_lt_card_of_eval_eq' {R} [CommRing R] [IsDomain R] (p q : R
[X]) (s : Finset R) (heval : forall i in s, p.eval i = q.eval i) (hcard : max p.
natDegree q.natDegree < #s) : p = q
参数：p q : R[X]；s : Finset R；heval : forall i in s, p.eval i = q.eval i；hcard : ma
x p.natDegree q.natDegree < #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`：eq_of_natDegree_lt_card_o
f_eval_eq {R} [CommRing R] [IsDomain R] (p q : R[X]) {ι} [Fintype ι] {f : ι -> R
} (hf : Function.Injective f) (heva…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
-/
lemma eq_of_natDegree_lt_card_of_eval_eq' {R} [CommRing R] [IsDomain R]
    (p q : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = q.eval i)
    (hcard : max p.natDegree q.natDegree < #s) : p = q :=
  eq_of_natDegree_lt_card_of_eval_eq p q Subtype.val_injective
    (fun i : s ↦ heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

open Cardinal in
/-
**Polynomial.eq_zero_of_forall_eval_zero_of_natDegree_lt_card** 是 Mathlib 中的一个引理
，位于命名空间 `Polynomial`。
形式化陈述：eq_zero_of_forall_eval_zero_of_natDegree_lt_card (f : R[X]) (hf : forall r
, f.eval r = 0) (hfR : f.natDegree < #R) : f = 0
参数：f : R[X]；hf : forall r, f.eval r = 0；hfR : f.natDegree < #R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用引理 `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`：eq_zero_of_natD
egree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R] (p : R[X]) {ι} [Fint
ype ι] {f : ι -> R} (hf : Function.Injective …
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Polynomial.zero_of_eval_zero`：zero_of_eval_zero [Infinite R] (p : R[X]) 
(h : forall x, p.eval x = 0) : p = 0
-/
lemma eq_zero_of_forall_eval_zero_of_natDegree_lt_card
    (f : R[X]) (hf : ∀ r, f.eval r = 0) (hfR : f.natDegree < #R) : f = 0 := by
  obtain hR | hR := finite_or_infinite R
  · have := Fintype.ofFinite R
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero f Function.injective_id hf
    simpa only [mk_fintype, Nat.cast_lt] using hfR
  · exact zero_of_eval_zero _ hf

open Cardinal in
/-
**Polynomial.exists_eval_ne_zero_of_natDegree_lt_card** 是 Mathlib 中的一个引理，位于命名空间 
`Polynomial`。
形式化陈述：exists_eval_ne_zero_of_natDegree_lt_card (f : R[X]) (hf : f != 0) (hfR : f
.natDegree < #R) : exists r, f.eval r != 0
参数：f : R[X]；hf : f != 0；hfR : f.natDegree < #R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Polynomial.eq_zero_of_forall_eval_zero_of_natDegree_lt_card`：eq_zero_of_
forall_eval_zero_of_natDegree_lt_card (f : R[X]) (hf : forall r, f.eval r = 0) (
hfR : f.natDegree < #R) : f = 0
-/
lemma exists_eval_ne_zero_of_natDegree_lt_card (f : R[X]) (hf : f ≠ 0) (hfR : f.natDegree < #R) :
    ∃ r, f.eval r ≠ 0 := by
  contrapose! hf
  exact eq_zero_of_forall_eval_zero_of_natDegree_lt_card f hf hfR

section

omit [IsDomain R]

/-
**Polynomial.monic_multisetProd_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_multisetProd_X_sub_C (s : Multiset R) : Monic (s.map fun a => X - C 
a).prod
参数：s : Multiset R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_multiset_prod_of_monic`：monic_multiset_prod_of_monic (t
 : Multiset ι) (f : ι -> R[X]) (ht : forall i in t, Monic (f i)) : Monic (t.map 
f).prod
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem monic_multisetProd_X_sub_C (s : Multiset R) : Monic (s.map fun a => X - C a).prod :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
/-
**Polynomial.monic_prod_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_prod_X_sub_C {α : Type*} (b : α -> R) (s : Finset α) : Monic (∏ a in
 s, (X - C (b a)))
参数：b : α -> R；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem monic_prod_X_sub_C {α : Type*} (b : α → R) (s : Finset α) :
    Monic (∏ a ∈ s, (X - C (b a))) :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C (b a)
/-
**Polynomial.monic_finprod_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_finprod_X_sub_C {α : Type*} (b : α -> R) : Monic (∏ᶠ k, (X - C (b k)
))
参数：b : α -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_finprod_of_monic`：monic_finprod_of_monic (α : Type*) (f
 : α -> R[X]) (hf : forall i in Function.mulSupport f, Monic (f i)) : Monic (fin
prod f)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem monic_finprod_X_sub_C {α : Type*} (b : α → R) : Monic (∏ᶠ k, (X - C (b k))) :=
  monic_finprod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

end

/-
**Polynomial.prod_multiset_root_eq_finset_root** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：prod_multiset_root_eq_finset_root [DecidableEq R] : (p.roots.map fun a => 
X - C a).prod = p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_multiset_map_count`：prod_multiset_map_count [DecidableEq ι] 
(s : Multiset ι) {M : Type*} [CommMonoid M] (f : ι -> M) : (s.map f).prod = ∏ m 
in s.toFinset, f m ^…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_multiset_root_eq_finset_root [DecidableEq R] :
    (p.roots.map fun a => X - C a).prod =
      p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p := by
  simp only [count_roots, Finset.prod_multiset_map_count]

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
/-
**Polynomial.prod_multiset_X_sub_C_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map fun a => X - C a).prod
 ∣ p
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_dvd_map`：map_dvd_map [Ring S] (f : R ->+* S) (hf : Functi
on.Injective f) {x y : R[X]} (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Polynomial.monic_multisetProd_X_sub_C`：monic_multisetProd_X_sub_C (s : M
ultiset R) : Monic (s.map fun a => X - C a).prod
· 使用定理 `Polynomial.prod_multiset_root_eq_finset_root`：prod_multiset_root_eq_fins
et_root [DecidableEq R] : (p.roots.map fun a => X - C a).prod = p.roots.toFinset
.prod fun a => (X - C a) ^ rootMul…
· 使用定理 `Polynomial.map_prod`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R)
 (s : Fin…
· 使用定理 `Finset.prod_dvd_of_coprime`：Finset.prod_dvd_of_coprime (Hs : (t : Set I)
.Pairwise (IsCoprime on s)) (Hs1 : (forall i in t, s i ∣ z)) : (∏ x in t, s x) ∣
 z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `IsCoprime.pow`：IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y 
^ n)
· 使用定理 `Polynomial.pairwise_coprime_X_sub_C`：pairwise_coprime_X_sub_C {K} [Field
 K] {I : Type v} {s : I -> K} (H : Function.Injective s) : Pairwise (IsCoprime o
n fun i : I => X - C (s i…
· 使用定理 `Polynomial.map_dvd`：map_dvd (f : R ->+* S) {x y : R[X]} : x ∣ y -> x.map
 f ∣ y.map f
· 使用定理 `Polynomial.pow_rootMultiplicity_dvd`：pow_rootMultiplicity_dvd (p : R[X])
 (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p

--- 原说明 ---
The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`.
-/
theorem prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map fun a => X - C a).prod ∣ p := by
  classical
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R)
    (monic_multisetProd_X_sub_C p.roots)]
  rw [prod_multiset_root_eq_finset_root, Polynomial.map_prod]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ h => ?_) fun a _ => ?_
  · simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
    exact (pairwise_coprime_X_sub_C (IsFractionRing.injective R <| FractionRing R) h).pow
  · exact Polynomial.map_dvd _ (pow_rootMultiplicity_dvd p a)

/-- A Galois connection. -/
/-
**Polynomial._root_.Multiset.prod_X_sub_C_dvd_iff_le_roots** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Galois connection.
-/
theorem _root_.Multiset.prod_X_sub_C_dvd_iff_le_roots {p : R[X]} (hp : p ≠ 0) (s : Multiset R) :
    (s.map fun a => X - C a).prod ∣ p ↔ s ≤ p.roots := by
  classical exact
  ⟨fun h =>
    Multiset.le_iff_count.2 fun r => by
      rw [count_roots, le_rootMultiplicity_iff hp, ← Multiset.prod_replicate, ←
        Multiset.map_replicate fun a => X - C a, ← Multiset.filter_eq]
      exact (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| s.filter_le _).trans h,
    fun h =>
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map h).trans p.prod_multiset_X_sub_C_dvd⟩
/-
**Polynomial.exists_prod_multiset_X_sub_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：exists_prod_multiset_X_sub_C_mul (p : R[X]) : exists q, (p.roots.map fun a
 => X - C a).prod * q = p ∧ Multiset.card p.roots + q.natDegree = p.natDegree ∧ 
q.roots = 0
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.prod_multiset_X_sub_C_dvd`：prod_multiset_X_sub_C_dvd (p : R[X
]) : (p.roots.map fun a => X - C a).prod ∣ p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.Monic.natDegree_mul'`：∀ {R : Type u} [inst : Semiring R] {p q
 : Polynomial R}, p.Monic → q ≠ 0 → (p * q).natDegree = p.natDegree + q.natDegre
e
· 使用定理 `Polynomial.monic_multisetProd_X_sub_C`：monic_multisetProd_X_sub_C (s : M
ultiset R) : Monic (s.map fun a => X - C a).prod
· 使用引理 `Polynomial.natDegree_multiset_prod_X_sub_C_eq_card`：natDegree_multiset_p
rod_X_sub_C_eq_card (s : Multiset R) : (s.map (X - C ·)).prod.natDegree = Multis
et.card s
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `Polynomial.roots_multiset_prod_X_sub_C`：roots_multiset_prod_X_sub_C (s :
 Multiset R) : (s.map fun a => X - C a).prod.roots = s
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
-/
theorem exists_prod_multiset_X_sub_C_mul (p : R[X]) :
    ∃ q,
      (p.roots.map fun a => X - C a).prod * q = p ∧
        Multiset.card p.roots + q.natDegree = p.natDegree ∧ q.roots = 0 := by
  obtain ⟨q, he⟩ := p.prod_multiset_X_sub_C_dvd
  use q, he.symm
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero] at he
    subst he
    simp
  constructor
  · conv_rhs => rw [he]
    rw [(monic_multisetProd_X_sub_C p.roots).natDegree_mul' hq,
      natDegree_multiset_prod_X_sub_C_eq_card]
  · replace he := congr_arg roots he.symm
    rw [roots_mul, roots_multiset_prod_X_sub_C] at he
    exacts [add_eq_left.1 he, mul_ne_zero (monic_multisetProd_X_sub_C p.roots).ne_zero hq]

/-- A polynomial `p` that has as many roots as its degree
can be written `p = p.leadingCoeff * ∏(X - a)`, for `a` in `p.roots`. -/
/-
**Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：C_leadingCoeff_mul_prod_multiset_X_sub_C (hroots : Multiset.card p.roots =
 p.natDegree) : C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p
参数：hroots : Multiset.card p.roots = p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le`：eq_leadi
ngCoeff_mul_of_monic_of_dvd_of_natDegree_le {R} [CommSemiring R] {p q : R[X]} (h
p : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree <= p…
· 使用定理 `Polynomial.monic_multisetProd_X_sub_C`：monic_multisetProd_X_sub_C (s : M
ultiset R) : Monic (s.map fun a => X - C a).prod
· 使用定理 `Polynomial.prod_multiset_X_sub_C_dvd`：prod_multiset_X_sub_C_dvd (p : R[X
]) : (p.roots.map fun a => X - C a).prod ∣ p
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Polynomial.natDegree_multiset_prod_X_sub_C_eq_card`：natDegree_multiset_p
rod_X_sub_C_eq_card (s : Multiset R) : (s.map (X - C ·)).prod.natDegree = Multis
et.card s
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
A polynomial `p` that has as many roots as its degree
can be written `p = p.leadingCoeff * ∏(X - a)`, for `a` in `p.roots`.
-/
theorem C_leadingCoeff_mul_prod_multiset_X_sub_C (hroots : Multiset.card p.roots = p.natDegree) :
    C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
  (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (monic_multisetProd_X_sub_C p.roots)
      p.prod_multiset_X_sub_C_dvd
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm

/-- A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
/-
**Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic) (hroots : M
ultiset.card p.roots = p.natDegree) : (p.roots.map fun a => X - C a).prod = p
参数：hp : p.Monic；hroots : Multiset.card p.roots = p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`：C_leadingCoeff_mul_
prod_multiset_X_sub_C (hroots : Multiset.card p.roots = p.natDegree) : C p.leadi
ngCoeff * (p.roots.map fun a => X - C a).…

--- 原说明 ---
A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`.
-/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) : (p.roots.map fun a => X - C a).prod = p := by
  convert! C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leadingCoeff, C_1, one_mul]
/-
**Polynomial.Monic.isUnit_leadingCoeff_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [IsDomain R] {a p : Polynomial R}, p.Mo
nic → a ∣ p → IsUnit a.leadingCoeff
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用引理 `Polynomial.leadingCoeff_dvd_leadingCoeff`：leadingCoeff_dvd_leadingCoeff 
{a p : R[X]} (hap : a ∣ p) : a.leadingCoeff ∣ p.leadingCoeff
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem Monic.isUnit_leadingCoeff_of_dvd {a p : R[X]} (hp : Monic p) (hap : a ∣ p) :
    IsUnit a.leadingCoeff :=
  isUnit_of_dvd_one (by simpa only [hp.leadingCoeff] using leadingCoeff_dvd_leadingCoeff hap)
/-
**Polynomial.card_roots_le_one_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：card_roots_le_one_of_irreducible (hirr : Irreducible p) : p.roots.card <= 
1
参数：hirr : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.empty_or_exists_mem`：empty_or_exists_mem (s : Multiset α) : s =
 0 ∨ exists a, a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用引理 `Polynomial.degree_eq_one_of_irreducible_of_root`：degree_eq_one_of_irredu
cible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) : degree p = 1
· 使用定理 `Polynomial.isRoot_of_mem_roots`：isRoot_of_mem_roots (h : a in p.roots) :
 IsRoot p a
· 使用定理 `Polynomial.card_roots'`：card_roots' (p : R[X]) : Multiset.card p.roots <
= natDegree p
-/
theorem card_roots_le_one_of_irreducible (hirr : Irreducible p) : p.roots.card ≤ 1 := by
  obtain hp | ⟨x, hx⟩ := p.roots.empty_or_exists_mem
  · simp [hp]
  convert! p.card_roots'
  exact (natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root hirr <|
    isRoot_of_mem_roots hx).symm
/-
**Polynomial.roots_eq_zero_of_irreducible_of_natDegree_ne_one** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：roots_eq_zero_of_irreducible_of_natDegree_ne_one (hirr : Irreducible p) (h
deg : p.natDegree != 1) : p.roots = 0
参数：hirr : Irreducible p；hdeg : p.natDegree != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用引理 `Polynomial.degree_eq_one_of_irreducible_of_root`：degree_eq_one_of_irredu
cible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) : degree p = 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_roots'`：mem_roots' : a in p.roots ↔ p != 0 ∧ IsRoot p a
-/
theorem roots_eq_zero_of_irreducible_of_natDegree_ne_one (hirr : Irreducible p)
    (hdeg : p.natDegree ≠ 1) : p.roots = 0 := by
  by_contra hroots
  have ⟨x, hx⟩ := exists_mem_of_ne_zero hroots
  exact hdeg <| natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hirr (mem_roots'.mp hx).right

/-- To check a monic polynomial is irreducible, it suffices to check only for
divisors that have smaller degree.

See also: `Polynomial.Monic.irreducible_iff_natDegree`.
-/
/-
**Polynomial.Monic.irreducible_iff_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [IsDomain R] {p : Polynomial R},   p.Mo
nic → p ≠ 1 → (Irreducible p ↔ ∀ (q : Polynomial R), q.degree ≤ ↑(p.natDegree / 
2) → q ∣ p → IsUnit q)
参数：Irreducible p ↔ ∀ (q : Polynomial R), q.degree ≤ ↑(p.natDegree / 2) → q ∣ p →
 IsUnit q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Monic.irreducible_iff_lt_natDegree_lt`：∀ {R : Type u} [inst :
 CommSemiring R] [NoZeroDivisors R] {p : Polynomial R},   p.Monic →     p ≠ 1 → 
(Irreducible p ↔ ∀ (q : Polynomial R),…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Polynomial.degree_pos_of_not_isUnit_of_dvd_monic`：degree_pos_of_not_isUn
it_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < degree a
· 使用定理 `Polynomial.Monic.isUnit_leadingCoeff_of_dvd`：∀ {R : Type u} [inst : Comm
Ring R] [IsDomain R] {a p : Polynomial R}, p.Monic → a ∣ p → IsUnit a.leadingCoe
ff
· 使用定理 `Polynomial.monic_of_isUnit_leadingCoeff_inv_smul`：monic_of_isUnit_leadin
gCoeff_inv_smul (h : IsUnit p.leadingCoeff) : Monic (h.unit⁻¹ • p)
· 使用定理 `Polynomial.degree_smul_of_smul_regular`：degree_smul_of_smul_regular {S :
 Type*} [SMulZeroClass S R] {k : S} (p : R[X]) (h : IsSMulRegular R k) : (k • p)
.degree = p.degree
· 使用定理 `isSMulRegular_of_group`：isSMulRegular_of_group [MulAction G R] (g : G) :
 IsSMulRegular R g
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Polynomial.smul_eq_C_mul`：smul_eq_C_mul (a : R) : a • p = C a * p
· 使用定理 `IsUnit.mul_left_dvd`：mul_left_dvd (hu : IsUnit u) : u * a ∣ b ↔ a ∣ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
To check a monic polynomial is irreducible, it suffices to check only for
divisors that have smaller degree.

See also: `Polynomial.Monic.irreducible_iff_natDegree`.
-/
theorem Monic.irreducible_iff_degree_lt (p_monic : Monic p) (p_1 : p ≠ 1) :
    Irreducible p ↔ ∀ q, degree q ≤ ↑(p.natDegree / 2) → q ∣ p → IsUnit q := by
  simp only [p_monic.irreducible_iff_lt_natDegree_lt p_1, Finset.mem_Ioc, and_imp,
    natDegree_pos_iff_degree_pos, natDegree_le_iff_degree_le]
  constructor
  · rintro h q deg_le dvd
    by_contra q_unit
    have := degree_pos_of_not_isUnit_of_dvd_monic p_monic q_unit dvd
    have hu := p_monic.isUnit_leadingCoeff_of_dvd dvd
    refine (h _ (monic_of_isUnit_leadingCoeff_inv_smul hu) ?_ ?_ (dvd_trans ?_ dvd)).elim
    · rwa [degree_smul_of_smul_regular _ (isSMulRegular_of_group _)]
    · rwa [degree_smul_of_smul_regular _ (isSMulRegular_of_group _)]
    · rw [Units.smul_def, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (Units.isUnit _)).mul_left_dvd]
  · rintro h q _ deg_pos deg_le dvd
    exact deg_pos.ne' <| degree_eq_zero_of_isUnit (h q deg_le dvd)

end CommRing

section

variable {A B : Type*} [CommRing A] [CommRing B]

/-
**Polynomial.le_rootMultiplicity_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_rootMultiplicity_map {p : A[X]} {f : A ->+* B} (hmap : map f p != 0) (a
 : A) : rootMultiplicity a p <= rootMultiplicity (f a) (p.map f)
参数：hmap : map f p != 0；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.le_rootMultiplicity_iff`：le_rootMultiplicity_iff (p0 : p != 0
) {a : R} {n : Nat} : n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Polynomial.pow_rootMultiplicity_dvd`：pow_rootMultiplicity_dvd (p : R[X])
 (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p
-/
theorem le_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (a : A) :
    rootMultiplicity a p ≤ rootMultiplicity (f a) (p.map f) := by
  rw [le_rootMultiplicity_iff hmap]
  refine _root_.trans ?_ (_root_.map_dvd (mapRingHom f) (pow_rootMultiplicity_dvd p a))
  rw [map_pow, map_sub, coe_mapRingHom, map_X, map_C]
/-
**Polynomial.eq_rootMultiplicity_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_rootMultiplicity_map {p : A[X]} {f : A ->+* B} (hf : Function.Injective
 f) (a : A) : rootMultiplicity a p = rootMultiplicity (f a) (p.map f)
参数：hf : Function.Injective f；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.le_rootMultiplicity_map`：le_rootMultiplicity_map {p : A[X]} {
f : A ->+* B} (hmap : map f p != 0) (a : A) : rootMultiplicity a p <= rootMultip
licity (f a) (p.map f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用引理 `Polynomial.le_rootMultiplicity_iff`：le_rootMultiplicity_iff (p0 : p != 0
) {a : R} {n : Nat} : n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_dvd_map`：map_dvd_map [Ring S] (f : R ->+* S) (hf : Functi
on.Injective f) {x y : R[X]} (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.pow_rootMultiplicity_dvd`：pow_rootMultiplicity_dvd (p : R[X])
 (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p
-/
theorem eq_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hf : Function.Injective f) (a : A) :
    rootMultiplicity a p = rootMultiplicity (f a) (p.map f) := by
  by_cases hp0 : p = 0; · simp only [hp0, rootMultiplicity_zero, Polynomial.map_zero]
  apply le_antisymm (le_rootMultiplicity_map ((Polynomial.map_ne_zero_iff hf).mpr hp0) a)
  rw [le_rootMultiplicity_iff hp0, ← map_dvd_map f hf ((monic_X_sub_C a).pow _),
    Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  apply pow_rootMultiplicity_dvd
/-
**Polynomial.count_map_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：count_map_roots [IsDomain A] [DecidableEq B] {p : A[X]} {f : A ->+* B} (hm
ap : map f p != 0) (b : B) : (p.roots.map f).count b <= rootMultiplicity b (p.ma
p f)
参数：hmap : map f p != 0；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.le_rootMultiplicity_iff`：le_rootMultiplicity_iff (p0 : p != 0
) {a : R} {n : Nat} : n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `Multiset.map_replicate`：map_replicate (f : α -> β) (k : Nat) (a : α) : (
replicate k a).map f = replicate k (f a)
· 使用定理 `Multiset.filter_eq`：filter_eq (s : Multiset α) (b : α) : s.filter (Eq b)
 = replicate (count b s) b
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Multiset.prod_dvd_prod_of_le`：prod_dvd_prod_of_le (h : s <= t) : s.prod 
∣ t.prod
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
· 使用定理 `Multiset.filter_le`：filter_le (s : Multiset α) : filter p s <= s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.map_multiset_prod`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : CommSemiring S] (f : R →+* S)   (m : Multiset (Polynomial R)
), Polynomial.map …
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.map_dvd`：map_dvd (f : R ->+* S) {x y : R[X]} : x ∣ y -> x.map
 f ∣ y.map f
· 使用定理 `Polynomial.prod_multiset_X_sub_C_dvd`：prod_multiset_X_sub_C_dvd (p : R[X
]) : (p.roots.map fun a => X - C a).prod ∣ p
-/
theorem count_map_roots [IsDomain A] [DecidableEq B] {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0)
    (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  rw [le_rootMultiplicity_iff hmap, ← Multiset.prod_replicate, ←
    Multiset.map_replicate fun a => X - C a]
  rw [← Multiset.filter_eq]
  refine
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le (Eq b) _).trans ?_
  convert! Polynomial.map_dvd f p.prod_multiset_X_sub_C_dvd
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_apply,
    Polynomial.map_sub, map_X, map_C]
/-
**Polynomial.count_map_roots_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：count_map_roots_of_injective [IsDomain A] [DecidableEq B] (p : A[X]) {f : 
A ->+* B} (hf : Function.Injective f) (b : B) : (p.roots.map f).count b <= rootM
ultiplicity b (p.map f)
参数：p : A[X]；hf : Function.Injective f；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `Polynomial.count_map_roots`：count_map_roots [IsDomain A] [DecidableEq B]
 {p : A[X]} {f : A ->+* B} (hmap : map f p != 0) (b : B) : (p.roots.map f).count
 b <= rootMultip…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
-/
theorem count_map_roots_of_injective [IsDomain A] [DecidableEq B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Multiset.count_zero, Polynomial.map_zero,
      rootMultiplicity_zero, le_refl]
  · exact count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp0) b
/-
**Polynomial.map_roots_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_roots_le [IsDomain A] [IsDomain B] {p : A[X]} {f : A ->+* B} (h : p.ma
p f != 0) : p.roots.map f <= (p.map f).roots
参数：h : p.map f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.count_map_roots`：count_map_roots [IsDomain A] [DecidableEq B]
 {p : A[X]} {f : A ->+* B} (hmap : map f p != 0) (b : B) : (p.roots.map f).count
 b <= rootMultip…
-/
theorem map_roots_le [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    p.roots.map f ≤ (p.map f).roots := by
  classical
  exact Multiset.le_iff_count.2 fun b => by
    rw [count_roots]
    apply count_map_roots h
/-
**Polynomial.map_roots_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_roots_le_of_injective [IsDomain A] [IsDomain B] (p : A[X]) {f : A ->+*
 B} (hf : Function.Injective f) : p.roots.map f <= (p.map f).roots
参数：p : A[X]；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.map_roots_le`：map_roots_le [IsDomain A] [IsDomain B] {p : A[X
]} {f : A ->+* B} (h : p.map f != 0) : p.roots.map f <= (p.map f).roots
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
-/
theorem map_roots_le_of_injective [IsDomain A] [IsDomain B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) : p.roots.map f ≤ (p.map f).roots := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Polynomial.map_zero, le_rfl]
  exact map_roots_le ((Polynomial.map_ne_zero_iff hf).mpr hp0)
/-
**Polynomial.card_roots_map_le_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots_map_le_degree {A B : Type*} [Semiring A] [CommRing B] [IsDomain
 B] {f : A ->+* B} (p : A[X]) (hp0 : p != 0) : (p.map f).roots.card <= p.degree
参数：p : A[X]；hp0 : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.card_roots`：card_roots (hp0 : p != 0) : (Multiset.card (roots
 p) : WithBot Nat) <= degree p
· 使用引理 `Polynomial.degree_map_le`：degree_map_le : degree (p.map f) <= degree p
-/
theorem card_roots_map_le_degree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A →+* B} (p : A[X]) (hp0 : p ≠ 0) : (p.map f).roots.card ≤ p.degree := by
  by_cases hpm0 : p.map f = 0
  · simp [hp0, hpm0, zero_le_degree_iff]
  exact card_roots hpm0 |>.trans degree_map_le
/-
**Polynomial.card_roots_map_le_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots_map_le_natDegree {A B : Type*} [Semiring A] [CommRing B] [IsDom
ain B] {f : A ->+* B} (p : A[X]) : (p.map f).roots.card <= p.natDegree
参数：p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.card_roots'`：card_roots' (p : R[X]) : Multiset.card p.roots <
= natDegree p
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p
-/
theorem card_roots_map_le_natDegree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A →+* B} (p : A[X]) : (p.map f).roots.card ≤ p.natDegree :=
  card_roots' _ |>.trans natDegree_map_le
/-
**Polynomial.ncard_rootSet_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ncard_rootSet_le (p : A[X]) (B : Type*) [CommRing B] [IsDomain B] [Algebra
 A B] : Set.ncard (p.rootSet B) <= p.natDegree
参数：p : A[X]；B : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynom
ial T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Al
gebra T S], p…
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Multiset.toFinset_card_le`：Multiset.toFinset_card_le : #m.toFinset <= Mu
ltiset.card m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.card_roots_map_le_natDegree`：card_roots_map_le_natDegree {A B
 : Type*} [Semiring A] [CommRing B] [IsDomain B] {f : A ->+* B} (p : A[X]) : (p.
map f).roots.card <= p.natDe…
-/
theorem ncard_rootSet_le (p : A[X]) (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] :
    Set.ncard (p.rootSet B) ≤ p.natDegree := by
  classical
  grw [rootSet, Set.ncard_coe_finset, Multiset.toFinset_card_le]
  exact p.card_roots_map_le_natDegree
/-
**Polynomial.filter_roots_map_range_eq_map_roots** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：filter_roots_map_range_eq_map_roots [IsDomain A] [IsDomain B] {f : A ->+* 
B} [DecidablePred (· in f.range)] (hf : Function.Injective f) (p : A[X]) : (p.ma
p f).roots.filter (· in f.range) = p.roots.map f
参数：· in f.range；hf : Function.Injective f；p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_filter`：count_filter {p} [DecidablePred p] {a} {s : Multi
set α} : count a (filter p s) = if p a then count a s else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Multiset.count_map_eq_count'`：count_map_eq_count' [DecidableEq β] (f : α
 -> β) (s : Multiset α) (hf : Function.Injective f) (x : α) : (s.map f).count (f
 x) = s.count x
· 使用定理 `Polynomial.eq_rootMultiplicity_map`：eq_rootMultiplicity_map {p : A[X]} {
f : A ->+* B} (hf : Function.Injective f) (a : A) : rootMultiplicity a p = rootM
ultiplicity (f a) (p.map…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.count_eq_zero`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Mul
tiset α} {a : α}, Multiset.count a s = 0 ↔ a ∉ s
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem filter_roots_map_range_eq_map_roots [IsDomain A] [IsDomain B] {f : A →+* B}
    [DecidablePred (· ∈ f.range)] (hf : Function.Injective f)
    (p : A[X]) : (p.map f).roots.filter (· ∈ f.range) = p.roots.map f := by
  classical
  ext b
  rw [Multiset.count_filter]
  split_ifs with h
  · obtain ⟨a, rfl⟩ := h
    simp [hf, Multiset.count_map_eq_count', eq_rootMultiplicity_map hf]
  · refine (Multiset.count_eq_zero.mpr fun h' ↦ h ?_).symm
    exact Exists.imp (fun _ ↦ And.right) <| Multiset.mem_map.mp h'
/-
**Polynomial.card_roots_le_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots_le_map [IsDomain A] [IsDomain B] {p : A[X]} {f : A ->+* B} (h :
 p.map f != 0) : Multiset.card p.roots <= Multiset.card (p.map f).roots
参数：h : p.map f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
· 使用定理 `Polynomial.map_roots_le`：map_roots_le [IsDomain A] [IsDomain B] {p : A[X
]} {f : A ->+* B} (h : p.map f != 0) : p.roots.map f <= (p.map f).roots
-/
theorem card_roots_le_map [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  rw [← p.roots.card_map f]
  exact Multiset.card_le_card (map_roots_le h)
/-
**Polynomial.card_roots_le_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：card_roots_le_map_of_injective [IsDomain A] [IsDomain B] {p : A[X]} {f : A
 ->+* B} (hf : Function.Injective f) : Multiset.card p.roots <= Multiset.card (p
.map f).roots
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.card_roots_le_map`：card_roots_le_map [IsDomain A] [IsDomain B
] {p : A[X]} {f : A ->+* B} (h : p.map f != 0) : Multiset.card p.roots <= Multis
et.card (p.map f).…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
-/
theorem card_roots_le_map_of_injective [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B}
    (hf : Function.Injective f) : Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Polynomial.map_zero, Multiset.card_zero, le_rfl]
  exact card_roots_le_map ((Polynomial.map_ne_zero_iff hf).mpr hp0)
/-
**Polynomial.roots_map_of_injective_of_card_eq_natDegree** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial`。
形式化陈述：roots_map_of_injective_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p :
 A[X]} {f : A ->+* B} (hf : Function.Injective f) (hroots : Multiset.card p.root
s = p.natDegree) : p.roots.map f = (p.map f).roots
参数：hf : Function.Injective f；hroots : Multiset.card p.roots = p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `Polynomial.map_roots_le_of_injective`：map_roots_le_of_injective [IsDomai
n A] [IsDomain B] (p : A[X]) {f : A ->+* B} (hf : Function.Injective f) : p.root
s.map f <= (p.map f).roots
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Polynomial.card_roots_map_le_natDegree`：card_roots_map_le_natDegree {A B
 : Type*} [Semiring A] [CommRing B] [IsDomain B] {f : A ->+* B} (p : A[X]) : (p.
map f).roots.card <= p.natDe…
-/
theorem roots_map_of_injective_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    {f : A →+* B} (hf : Function.Injective f) (hroots : Multiset.card p.roots = p.natDegree) :
    p.roots.map f = (p.map f).roots := by
  apply Multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf)
  simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p
/-
**Polynomial.roots_map_of_map_ne_zero_of_card_eq_natDegree** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：roots_map_of_map_ne_zero_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p
 : A[X]} (f : A ->+* B) (h : p.map f != 0) (hroots : p.roots.card = p.natDegree)
 : p.roots.map f = (p.map f).roots
参数：f : A ->+* B；h : p.map f != 0；hroots : p.roots.card = p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `Polynomial.map_roots_le`：map_roots_le [IsDomain A] [IsDomain B] {p : A[X
]} {f : A ->+* B} (h : p.map f != 0) : p.roots.map f <= (p.map f).roots
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Polynomial.card_roots_map_le_natDegree`：card_roots_map_le_natDegree {A B
 : Type*} [Semiring A] [CommRing B] [IsDomain B] {f : A ->+* B} (p : A[X]) : (p.
map f).roots.card <= p.natDe…
-/
theorem roots_map_of_map_ne_zero_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    (f : A →+* B) (h : p.map f ≠ 0) (hroots : p.roots.card = p.natDegree) :
    p.roots.map f = (p.map f).roots :=
  eq_of_le_of_card_le (map_roots_le h) <| by
    simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p
/-
**Polynomial.Monic.roots_map_of_card_eq_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial.Monic`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [inst : CommRing A] [inst_1 : CommRing B] 
[inst_2 : IsDomain A] [inst_3 : IsDomain B]   {p : Polynomial A},   p.Monic → ∀ 
(f : A →+* B), p.roots.card = p.natDegree → Multiset.map (⇑f) p.roots = (Polynom
ial.map f p).roots
参数：f : A →+* B；⇑f；Polynomial.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_map_of_map_ne_zero_of_card_eq_natDegree`：roots_map_of_m
ap_ne_zero_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]} (f : A ->+*
 B) (h : p.map f != 0) (hroots : p.roots.card …
· 使用定理 `Polynomial.map_monic_ne_zero`：map_monic_ne_zero (hp : p.Monic) [Nontrivi
al S] : p.map f != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem Monic.roots_map_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]} (hm : p.Monic)
    (f : A →+* B) (hroots : p.roots.card = p.natDegree) : p.roots.map f = (p.map f).roots :=
  roots_map_of_map_ne_zero_of_card_eq_natDegree f (map_monic_ne_zero hm) hroots

end

end Polynomial

