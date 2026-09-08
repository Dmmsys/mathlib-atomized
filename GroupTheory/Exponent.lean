/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.Factorization.LCM
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Peel

/-!
# Exponent of a group

This file defines the exponent of a group, or more generally a monoid. For a group `G` it is defined
to be the minimal `n≥1` such that `g ^ n = 1` for all `g ∈ G`. For a finite group `G`,
it is equal to the lowest common multiple of the order of all elements of the group `G`.

## Main definitions

* `Monoid.ExponentExists` is a predicate on a monoid `G` saying that there is some positive `n`
  such that `g ^ n = 1` for all `g ∈ G`.
* `Monoid.exponent` defines the exponent of a monoid `G` as the minimal positive `n` such that
  `g ^ n = 1` for all `g ∈ G`, by convention it is `0` if no such `n` exists.
* `AddMonoid.ExponentExists` the additive version of `Monoid.ExponentExists`.
* `AddMonoid.exponent` the additive version of `Monoid.exponent`.

## Main results

* `Monoid.lcm_order_eq_exponent`: For a finite left cancel monoid `G`, the exponent is equal to the
  `Finset.lcm` of the order of its elements.
* `Monoid.exponent_eq_iSup_orderOf(')`: For a commutative cancel monoid, the exponent is
  equal to `⨆ g : G, orderOf g` (or zero if it has any order-zero elements).
* `Monoid.exponent_pi` and `Monoid.exponent_prod`: The exponent of a finite product of monoids is
  the least common multiple (`Finset.lcm` and `lcm`, respectively) of the exponents of the
  constituent monoids.
* `MonoidHom.exponent_dvd`: If `f : M₁ →⋆ M₂` is surjective, then the exponent of `M₂` divides the
  exponent of `M₁`.

## TODO
* Refactor the characteristic of a ring to be the exponent of its underlying additive group.
-/

@[expose] public section


universe u

variable {G : Type u}

namespace Monoid

section Monoid

variable (G) [Monoid G]

/-- A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
for all `g`. -/
@[to_additive
/-- A predicate on an additive monoid saying that there is a positive integer `n` such that
`n • g = 0` for all `g`. -/]
/-
**Monoid.ExponentExists** 是 Mathlib 中的一个定义，位于命名空间 `Monoid`。
形式化陈述：ExponentExists
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ExponentExists :=
  ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1

open scoped Classical in
/-- The exponent of a group is the smallest positive integer `n` such that `g ^ n = 1` for all
`g ∈ G` if it exists, otherwise it is zero by convention. -/
@[to_additive
/-- The exponent of an additive group is the smallest positive integer `n` such that
`n • g = 0` for all `g ∈ G` if it exists, otherwise it is zero by convention. -/]
/-
**Monoid.exponent** 是 Mathlib 中的一个定义，位于命名空间 `Monoid`。
形式化陈述：exponent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def exponent :=
  if h : ExponentExists G then Nat.find h else 0

variable {G}

@[simp]
/-
**Monoid._root_.AddMonoid.exponent_additive** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddMonoid.exponent_additive :
    AddMonoid.exponent (Additive G) = exponent G := rfl

@[simp]
/-
**Monoid.exponent_multiplicative** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_multiplicative {G : Type*} [AddMonoid G] : exponent (Multiplicati
ve G) = AddMonoid.exponent G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exponent_multiplicative {G : Type*} [AddMonoid G] :
    exponent (Multiplicative G) = AddMonoid.exponent G := rfl

set_option backward.isDefEq.respectTransparency false in
open MulOpposite in
@[to_additive (attr := simp)]
/-
**Monoid._root_.MulOpposite.exponent** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulOpposite.exponent : exponent (MulOpposite G) = exponent G := by
  simp only [Monoid.exponent, ExponentExists]
  congr!
  all_goals exact ⟨(op_injective <| · <| op ·), (unop_injective <| · <| unop ·)⟩

@[to_additive]
/-
**Monoid.ExponentExists.isOfFinOrder** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.ExponentE
xists`。
形式化陈述：∀ {G : Type u} [inst : Monoid G], Monoid.ExponentExists G → ∀ {g : G}, IsO
fFinOrder g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `Mathlib.Tactic.Peel.and_imp_left_of_imp_imp`：and_imp_left_of_imp_imp {p 
q r : Prop} (h : r -> p -> q) : r ∧ p -> r ∧ q
-/
theorem ExponentExists.isOfFinOrder (h : ExponentExists G) {g : G} : IsOfFinOrder g :=
  isOfFinOrder_iff_pow_eq_one.mpr <| by peel 2 h; exact this g

@[to_additive]
/-
**Monoid.ExponentExists.orderOf_pos** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.ExponentEx
ists`。
形式化陈述：∀ {G : Type u} [inst : Monoid G], Monoid.ExponentExists G → ∀ (g : G), 0 <
 orderOf g
参数：g : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用定理 `Monoid.ExponentExists.isOfFinOrder`：∀ {G : Type u} [inst : Monoid G], Mo
noid.ExponentExists G → ∀ {g : G}, IsOfFinOrder g
-/
theorem ExponentExists.orderOf_pos (h : ExponentExists G) (g : G) : 0 < orderOf g :=
  h.isOfFinOrder.orderOf_pos

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**Monoid.exponent_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_ne_zero : exponent G != 0 ↔ ExponentExists G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.exponent.eq_1`：∀ (G : Type u) [inst : Monoid G], Monoid.exponent 
G = if h : Monoid.ExponentExists G then Nat.find h else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem exponent_ne_zero : exponent G ≠ 0 ↔ ExponentExists G := by
  rw [exponent]
  split_ifs with h
  · simp [h]
  --if this isn't done this way, `to_additive` freaks
  · tauto

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_ne_zero⟩ := exponent_ne_zero

@[to_additive]
/-
**Monoid.exponent_pos** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_pos : 0 < exponent G ↔ ExponentExists G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Monoid.exponent_ne_zero`：exponent_ne_zero : exponent G != 0 ↔ ExponentEx
ists G
-/
theorem exponent_pos : 0 < exponent G ↔ ExponentExists G :=
  pos_iff_ne_zero.trans exponent_ne_zero

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_pos⟩ := exponent_pos

@[to_additive]
/-
**Monoid.exponent_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_eq_zero_iff : exponent G = 0 ↔ ¬ExponentExists G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用定理 `Monoid.exponent_ne_zero`：exponent_ne_zero : exponent G != 0 ↔ ExponentEx
ists G
-/
theorem exponent_eq_zero_iff : exponent G = 0 ↔ ¬ExponentExists G :=
  exponent_ne_zero.not_right

@[to_additive exponent_eq_zero_addOrder_zero]
/-
**Monoid.exponent_eq_zero_of_order_zero** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_eq_zero_of_order_zero {g : G} (hg : orderOf g = 0) : exponent G =
 0
参数：hg : orderOf g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.exponent_eq_zero_iff`：exponent_eq_zero_iff : exponent G = 0 ↔ ¬Ex
ponentExists G
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Monoid.ExponentExists.orderOf_pos`：∀ {G : Type u} [inst : Monoid G], Mon
oid.ExponentExists G → ∀ (g : G), 0 < orderOf g
-/
theorem exponent_eq_zero_of_order_zero {g : G} (hg : orderOf g = 0) : exponent G = 0 :=
  exponent_eq_zero_iff.mpr fun h ↦ h.orderOf_pos g |>.ne' hg

@[to_additive]
/-
**Monoid.exponent_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_eq_sInf : Monoid.exponent G = sInf {d : Nat | 0 < d ∧ forall x : 
G, x ^ d = 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.exponent.eq_1`：∀ (G : Type u) [inst : Monoid G], Monoid.exponent 
G = if h : Monoid.ExponentExists G then Nat.find h else 0
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.exponent_eq_zero_iff`：exponent_eq_zero_iff : exponent G = 0 ↔ ¬Ex
ponentExists G
· 使用定理 `Nat.sInf_empty`：sInf_empty : sInf ∅ = 0
-/
theorem exponent_eq_sInf :
    Monoid.exponent G = sInf {d : ℕ | 0 < d ∧ ∀ x : G, x ^ d = 1} := by
  by_cases h : Monoid.ExponentExists G
  · have h' : {d : ℕ | 0 < d ∧ ∀ x : G, x ^ d = 1}.Nonempty := h
    rw [Monoid.exponent, dif_pos h, Nat.sInf_def h']
    congr
  · have : {d | 0 < d ∧ ∀ (x : G), x ^ d = 1} = ∅ :=
      Set.eq_empty_of_forall_notMem fun n hn ↦ h ⟨n, hn⟩
    rw [Monoid.exponent_eq_zero_iff.mpr h, this, Nat.sInf_empty]

/-- The exponent is zero iff for all nonzero `n`, one can find a `g` such that `g ^ n ≠ 1`. -/
@[to_additive /-- The exponent is zero iff for all nonzero `n`, one can find a `g` such that
`n • g ≠ 0`. -/]
/-
**Monoid.exponent_eq_zero_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_eq_zero_iff_forall : exponent G = 0 ↔ forall n > 0, exists g : G,
 g ^ n != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.exponent_eq_zero_iff`：exponent_eq_zero_iff : exponent G = 0 ↔ ¬Ex
ponentExists G
· 使用定理 `Monoid.ExponentExists.eq_1`：∀ (G : Type u) [inst : Monoid G], Monoid.Exp
onentExists G = ∃ n, 0 < n ∧ ∀ (g : G), g ^ n = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exponent_eq_zero_iff_forall : exponent G = 0 ↔ ∀ n > 0, ∃ g : G, g ^ n ≠ 1 := by
  rw [exponent_eq_zero_iff, ExponentExists]
  push Not
  rfl

@[to_additive exponent_nsmul_eq_zero]
/-
**Monoid.pow_exponent_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：pow_exponent_eq_one (g : G) : g ^ exponent G = 1
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_exponent_eq_one (g : G) : g ^ exponent G = 1 := by
  classical
  by_cases h : ExponentExists G
  · simp_rw [exponent, dif_pos h]
    exact (Nat.find_spec h).2 g
  · simp_rw [exponent, dif_neg h, pow_zero]

@[to_additive]
/-
**Monoid.pow_eq_mod_exponent** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：pow_eq_mod_exponent {n : Nat} (g : G) : g ^ n = g ^ (n % exponent G)
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_eq_mod_exponent {n : ℕ} (g : G) : g ^ n = g ^ (n % exponent G) :=
  calc
    g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) := by rw [Nat.mod_add_div]
    _ = g ^ (n % exponent G) := by simp [pow_add, pow_mul, pow_exponent_eq_one]

@[to_additive]
/-
**Monoid.exponent_pos_of_exists** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_pos_of_exists (n : Nat) (hpos : 0 < n) (hG : forall g : G, g ^ n 
= 1) : 0 < exponent G
参数：n : Nat；hpos : 0 < n；hG : forall g : G, g ^ n = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.ExponentExists.exponent_pos`：∀ {G : Type u} [inst : Monoid G], Mo
noid.ExponentExists G → 0 < Monoid.exponent G
-/
theorem exponent_pos_of_exists (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) :
    0 < exponent G :=
  ExponentExists.exponent_pos ⟨n, hpos, hG⟩

@[to_additive]
/-
**Monoid.exponent_min'** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_min' (n : Nat) (hpos : 0 < n) (hG : forall g : G, g ^ n = 1) : ex
ponent G <= n
参数：n : Nat；hpos : 0 < n；hG : forall g : G, g ^ n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.exponent.eq_1`：∀ (G : Type u) [inst : Monoid G], Monoid.exponent 
G = if h : Monoid.ExponentExists G then Nat.find h else 0
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
-/
theorem exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) : exponent G ≤ n := by
  classical
  rw [exponent, dif_pos]
  · apply Nat.find_min'
    exact ⟨hpos, hG⟩
  · exact ⟨n, hpos, hG⟩

@[to_additive]
/-
**Monoid.exponent_min** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_min (m : Nat) (hpos : 0 < m) (hm : m < exponent G) : exists g : G
, g ^ m != 1
参数：m : Nat；hpos : 0 < m；hm : m < exponent G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Monoid.exponent_min'`：exponent_min' (n : Nat) (hpos : 0 < n) (hG : foral
l g : G, g ^ n = 1) : exponent G <= n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem exponent_min (m : ℕ) (hpos : 0 < m) (hm : m < exponent G) : ∃ g : G, g ^ m ≠ 1 := by
  by_contra! h
  have hcon : exponent G ≤ m := exponent_min' m hpos h
  lia

@[to_additive AddMonoid.exp_eq_one_iff]
/-
**Monoid.exp_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exp_eq_one_iff : exponent G = 1 ↔ Subsingleton G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Monoid.exponent_min'`：exponent_min' (n : Nat) (hpos : 0 < n) (hG : foral
l g : G, g ^ n = 1) : exponent G <= n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Monoid.exponent_pos_of_exists`：exponent_pos_of_exists (n : Nat) (hpos : 
0 < n) (hG : forall g : G, g ^ n = 1) : 0 < exponent G
-/
theorem exp_eq_one_iff : exponent G = 1 ↔ Subsingleton G := by
  refine ⟨fun eq_one => ⟨fun a b => ?a_eq_b⟩, fun h => le_antisymm ?le ?ge⟩
  · rw [← pow_one a, ← pow_one b, ← eq_one, Monoid.pow_exponent_eq_one, Monoid.pow_exponent_eq_one]
  · apply exponent_min' _ Nat.one_pos
    simp [eq_iff_true_of_subsingleton]
  · apply Nat.succ_le_of_lt
    apply exponent_pos_of_exists 1 Nat.one_pos
    simp [eq_iff_true_of_subsingleton]

@[to_additive (attr := simp) AddMonoid.exp_eq_one_of_subsingleton]
/-
**Monoid.exp_eq_one_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exp_eq_one_of_subsingleton [hs : Subsingleton G] : exponent G = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.exp_eq_one_iff`：exp_eq_one_iff : exponent G = 1 ↔ Subsingleton G
-/
theorem exp_eq_one_of_subsingleton [hs : Subsingleton G] : exponent G = 1 :=
  exp_eq_one_iff.mpr hs

@[to_additive addOrder_dvd_exponent]
/-
**Monoid.order_dvd_exponent** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：order_dvd_exponent (g : G) : orderOf g ∣ exponent G
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
-/
theorem order_dvd_exponent (g : G) : orderOf g ∣ exponent G :=
  orderOf_dvd_of_pow_eq_one <| pow_exponent_eq_one g

@[to_additive]
/-
**Monoid.orderOf_le_exponent** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：orderOf_le_exponent (h : ExponentExists G) (g : G) : orderOf g <= exponent
 G
参数：h : ExponentExists G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Monoid.ExponentExists.exponent_pos`：∀ {G : Type u} [inst : Monoid G], Mo
noid.ExponentExists G → 0 < Monoid.exponent G
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G
-/
theorem orderOf_le_exponent (h : ExponentExists G) (g : G) : orderOf g ≤ exponent G :=
  Nat.le_of_dvd h.exponent_pos (order_dvd_exponent g)

@[to_additive]
/-
**Monoid.exponent_dvd_iff_forall_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_dvd_iff_forall_pow_eq_one {n : Nat} : exponent G ∣ n ↔ forall g :
 G, g ^ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
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
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.pow_eq_mod_exponent`：pow_eq_mod_exponent {n : Nat} (g : G) : g ^ 
n = g ^ (n % exponent G)
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Monoid.exponent_pos_of_exists`：exponent_pos_of_exists (n : Nat) (hpos : 
0 < n) (hG : forall g : G, g ^ n = 1) : 0 < exponent G
· 使用定理 `Monoid.exponent_min'`：exponent_min' (n : Nat) (hpos : 0 < n) (hG : foral
l g : G, g ^ n = 1) : exponent G <= n
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem exponent_dvd_iff_forall_pow_eq_one {n : ℕ} : exponent G ∣ n ↔ ∀ g : G, g ^ n = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  constructor
  · intro h g
    rw [Nat.dvd_iff_mod_eq_zero] at h
    rw [pow_eq_mod_exponent, h, pow_zero]
  · intro hG
    by_contra h
    rw [Nat.dvd_iff_mod_eq_zero, ← Ne, ← pos_iff_ne_zero] at h
    have h₂ : n % exponent G < exponent G := Nat.mod_lt _ (exponent_pos_of_exists n hpos hG)
    have h₃ : exponent G ≤ n % exponent G := by
      apply exponent_min' _ h
      simp_rw [← pow_eq_mod_exponent]
      exact hG
    exact h₂.not_ge h₃

@[to_additive]
alias ⟨_, exponent_dvd_of_forall_pow_eq_one⟩ := exponent_dvd_iff_forall_pow_eq_one

@[to_additive]
/-
**Monoid.exponent_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_dvd {n : Nat} : exponent G ∣ n ↔ forall g : G, orderOf g ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exponent_dvd {n : ℕ} : exponent G ∣ n ↔ ∀ g : G, orderOf g ∣ n := by
  simp_rw [exponent_dvd_iff_forall_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

variable (G)

@[to_additive]
/-
**Monoid.lcm_orderOf_dvd_exponent** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：lcm_orderOf_dvd_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderO
f ∣ exponent G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.lcm_dvd`：lcm_dvd {a : α} : (forall b in s, f b ∣ a) -> s.lcm f ∣ 
a
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G
-/
theorem lcm_orderOf_dvd_exponent [Fintype G] :
    (Finset.univ : Finset G).lcm orderOf ∣ exponent G := by
  apply Finset.lcm_dvd
  intro g _
  exact order_dvd_exponent g

@[to_additive exists_addOrderOf_eq_pow_padic_val_nat_add_exponent]
/-
**Monoid._root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent** 是 Mathl
ib 中的一个定理，位于命名空间 `Monoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent {p : ℕ} (hp : p.Prime) :
    ∃ g : G, orderOf g = p ^ (exponent G).factorization p := by
  have := Fact.mk hp
  rcases eq_or_ne ((exponent G).factorization p) 0 with (h | h)
  · refine ⟨1, by rw [h, pow_zero, orderOf_one]⟩
  have he : 0 < exponent G :=
    Ne.bot_lt fun ht => by
      rw [ht] at h
      apply h
      rw [bot_eq_zero, Nat.factorization_zero, Finsupp.zero_apply]
  rw [← Finsupp.mem_support_iff] at h
  obtain ⟨g, hg⟩ : ∃ g : G, g ^ (exponent G / p) ≠ 1 := by
    suffices key : ¬exponent G ∣ exponent G / p by
      rwa [exponent_dvd_iff_forall_pow_eq_one, not_forall] at key
    exact fun hd =>
      hp.one_lt.not_ge
        ((mul_le_iff_le_one_left he).mp <|
          Nat.le_of_dvd he <| Nat.mul_dvd_of_dvd_div (Nat.dvd_of_mem_primeFactors h) hd)
  obtain ⟨k, hk : exponent G = p ^ _ * k⟩ := Nat.ordProj_dvd _ _
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp h)
  refine ⟨g ^ k, ?_⟩
  rw [ht]
  apply orderOf_eq_prime_pow
  · rwa [hk, mul_comm, ht, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ hp.pos, pow_mul] at hg
  · rw [← Nat.succ_eq_add_one, ← ht, ← pow_mul, mul_comm, ← hk]
    exact pow_exponent_eq_one g

variable {G} in
open Nat in
/-- If two commuting elements `x` and `y` of a monoid have order `n` and `m`, there is an element
of order `lcm n m`. The result actually gives an explicit (computable) element, written as the
product of a power of `x` and a power of `y`. See also the result below if you don't need the
explicit formula. -/
@[to_additive /-- If two commuting elements `x` and `y` of an additive monoid have order `n` and
`m`, there is an element of order `lcm n m`. The result actually gives an explicit (computable)
element, written as the sum of a multiple of `x` and a multiple of `y`. See also the result below
if you don't need the explicit formula. -/]
/-
**Monoid._root_.Commute.orderOf_mul_pow_eq_lcm** 是 Mathlib 中的一个引理，位于命名空间 `Monoid
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Commute.orderOf_mul_pow_eq_lcm {x y : G} (h : Commute x y) (hx : orderOf x ≠ 0)
    (hy : orderOf y ≠ 0) :
    orderOf (x ^ (orderOf x / (factorizationLCMLeft (orderOf x) (orderOf y))) *
      y ^ (orderOf y / factorizationLCMRight (orderOf x) (orderOf y))) =
      Nat.lcm (orderOf x) (orderOf y) := by
  rw [(h.pow_pow _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
  all_goals iterate 2 rw [orderOf_pow_orderOf_div]; try rw [Coprime]
  all_goals simp [factorizationLCMLeft_mul_factorizationLCMRight, factorizationLCMLeft_dvd_left,
    factorizationLCMRight_dvd_right, coprime_factorizationLCMLeft_factorizationLCMRight, hx, hy]

open Submonoid in
/-- If two commuting elements `x` and `y` of a monoid have order `n` and `m`, then there is an
element of order `lcm n m` that lies in the subgroup generated by `x` and `y`. -/
@[to_additive /-- If two commuting elements `x` and `y` of an additive monoid have order `n` and
`m`, then there is an element of order `lcm n m` that lies in the additive subgroup generated by `x`
and `y`. -/]
/-
**Monoid._root_.Commute.exists_orderOf_eq_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Commute.exists_orderOf_eq_lcm {x y : G} (h : Commute x y) :
    ∃ z ∈ closure {x, y}, orderOf z = Nat.lcm (orderOf x) (orderOf y) := by
  by_cases hx : orderOf x = 0 <;> by_cases hy : orderOf y = 0
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨y, subset_closure (by simp), by simp [hy]⟩
  · exact ⟨_, mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _),
      h.orderOf_mul_pow_eq_lcm hx hy⟩

/-- A nontrivial monoid has prime exponent `p` if and only if every non-identity element has
order `p`. -/
@[to_additive]
/-
**Monoid.exponent_eq_prime_iff** 是 Mathlib 中的一个引理，位于命名空间 `Monoid`。
形式化陈述：exponent_eq_prime_iff {G : Type*} [Monoid G] [Nontrivial G] {p : Nat} (hp 
: p.Prime) : Monoid.exponent G = p ↔ forall g : G, g != 1 -> orderOf g = p
参数：hp : p.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_iff_eq`：∀ {p a : ℕ}, Nat.Prime p → a ≠ 1 → (a ∣ p ↔ p = a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_eq_one_iff`：orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Monoid.exponent_dvd`：exponent_dvd {n : Nat} : exponent G ∣ n ↔ forall g 
: G, orderOf g ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x

--- 原说明 ---
A nontrivial monoid has prime exponent `p` if and only if every non-identity ele
ment has
order `p`.
-/
lemma exponent_eq_prime_iff {G : Type*} [Monoid G] [Nontrivial G] {p : ℕ} (hp : p.Prime) :
    Monoid.exponent G = p ↔ ∀ g : G, g ≠ 1 → orderOf g = p := by
  refine ⟨fun hG g hg ↦ ?_, fun h ↦ dvd_antisymm ?_ ?_⟩
  · rw [Ne, ← orderOf_eq_one_iff] at hg
    exact Eq.symm <| (hp.dvd_iff_eq hg).mp <| hG ▸ Monoid.order_dvd_exponent g
  · rw [exponent_dvd]
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · rw [h g hg]
  · obtain ⟨g, hg⟩ := exists_ne (1 : G)
    simpa [h g hg] using Monoid.order_dvd_exponent g

variable {G}

@[to_additive]
/-
**Monoid.exponent_ne_zero_iff_range_orderOf_finite** 是 Mathlib 中的一个定理，位于命名空间 `Mo
noid`。
形式化陈述：exponent_ne_zero_iff_range_orderOf_finite (h : forall g : G, 0 < orderOf g
) : exponent G != 0 ↔ (Set.range (orderOf : G -> Nat)).Finite
参数：h : forall g : G, 0 < orderOf g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Infinite.exists_gt`：∀ {α : Type u_2} [inst : LinearOrder α] [Locally
FiniteOrderBot α] {s : Set α}, s.Infinite → ∀ (a : α), ∃ b ∈ s, a < b
· 使用定理 `pow_ne_one_of_lt_orderOf`：pow_ne_one_of_lt_orderOf (n0 : n != 0) (h : n 
< orderOf x) : x ^ n != 1
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Monoid.exponent_dvd`：exponent_dvd {n : Nat} : exponent G ∣ n ↔ forall g 
: G, orderOf g ∣ n
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
-/
theorem exponent_ne_zero_iff_range_orderOf_finite (h : ∀ g : G, 0 < orderOf g) :
    exponent G ≠ 0 ↔ (Set.range (orderOf : G → ℕ)).Finite := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · by_contra h
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := Set.Infinite.exists_gt h (exponent G)
    exact pow_ne_one_of_lt_orderOf he het (pow_exponent_eq_one t)
  · lift Set.range (orderOf (G := G)) to Finset ℕ using he with t ht
    have htpos : 0 < t.prod id := by
      refine Finset.prod_pos fun a ha => ?_
      rw [← Finset.mem_coe, ht] at ha
      obtain ⟨k, rfl⟩ := ha
      exact h k
    suffices exponent G ∣ t.prod id by
      intro h
      rw [h, zero_dvd_iff] at this
      exact htpos.ne' this
    rw [exponent_dvd]
    intro g
    apply Finset.dvd_prod_of_mem id (?_ : orderOf g ∈ _)
    rw [← Finset.mem_coe, ht]
    exact Set.mem_range_self g

@[to_additive]
/-
**Monoid.exponent_eq_zero_iff_range_orderOf_infinite** 是 Mathlib 中的一个定理，位于命名空间 `
Monoid`。
形式化陈述：exponent_eq_zero_iff_range_orderOf_infinite (h : forall g : G, 0 < orderOf
 g) : exponent G = 0 ↔ (Set.range (orderOf : G -> Nat)).Infinite
参数：h : forall g : G, 0 < orderOf g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.exponent_ne_zero_iff_range_orderOf_finite`：exponent_ne_zero_iff_r
ange_orderOf_finite (h : forall g : G, 0 < orderOf g) : exponent G != 0 ↔ (Set.r
ange (orderOf : G -> Nat)).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
-/
theorem exponent_eq_zero_iff_range_orderOf_infinite (h : ∀ g : G, 0 < orderOf g) :
    exponent G = 0 ↔ (Set.range (orderOf : G → ℕ)).Infinite := by
  have := exponent_ne_zero_iff_range_orderOf_finite h
  rwa [Ne, not_iff_comm, Iff.comm] at this

@[to_additive]
/-
**Monoid.lcm_orderOf_eq_exponent** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：lcm_orderOf_eq_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf
 = exponent G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Monoid.lcm_orderOf_dvd_exponent`：lcm_orderOf_dvd_exponent [Fintype G] : 
(Finset.univ : Finset G).lcm orderOf ∣ exponent G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.exponent_dvd`：exponent_dvd {n : Nat} : exponent G ∣ n ↔ forall g 
: G, orderOf g ∣ n
· 使用定理 `Finset.dvd_lcm`：dvd_lcm {b : β} (hb : b in s) : f b ∣ s.lcm f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem lcm_orderOf_eq_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf = exponent G :=
  Nat.dvd_antisymm
    (lcm_orderOf_dvd_exponent G)
    (exponent_dvd.mpr fun g => Finset.dvd_lcm (Finset.mem_univ g))

variable {H : Type*} [Monoid H]

/--
If there exists an injective, multiplication-preserving map from `G` to `H`,
then the exponent of `G` divides the exponent of `H`.
-/
@[to_additive /-- If there exists an injective, addition-preserving map from `G` to `H`,
then the exponent of `G` divides the exponent of `H`. -/]
/-
**Monoid.exponent_dvd_of_monoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_dvd_of_monoidHom (e : G ->* H) (e_inj : Function.Injective e) : M
onoid.exponent G ∣ Monoid.exponent H
参数：e : G ->* H；e_inj : Function.Injective e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.exponent_dvd_of_forall_pow_eq_one`：∀ {G : Type u} [inst : Monoid 
G] {n : ℕ}, (∀ (g : G), g ^ n = 1) → Monoid.exponent G ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem exponent_dvd_of_monoidHom (e : G →* H) (e_inj : Function.Injective e) :
    Monoid.exponent G ∣ Monoid.exponent H :=
  exponent_dvd_of_forall_pow_eq_one fun g => e_inj (by
    rw [map_pow, pow_exponent_eq_one, map_one])

/--
The exponent of a submonoid `H ≤ G` divides the exponent of `G`.
-/
@[to_additive /-- The exponent of an additive submonoid `H ≤ G` divides the exponent of `G`. -/]
/-
**Monoid.exponent_submonoid_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_submonoid_dvd (H : Submonoid G) : Monoid.exponent H ∣ Monoid.expo
nent G
参数：H : Submonoid G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.exponent_dvd_of_monoidHom`：exponent_dvd_of_monoidHom (e : G ->* H
) (e_inj : Function.Injective e) : Monoid.exponent G ∣ Monoid.exponent H
· 使用引理 `Submonoid.subtype_injective`：subtype_injective (s : Submonoid M) : Funct
ion.Injective s.subtype

--- 原说明 ---
The exponent of a submonoid `H ≤ G` divides the exponent of `G`.
-/
theorem exponent_submonoid_dvd (H : Submonoid G) :
    Monoid.exponent H ∣ Monoid.exponent G :=
  Monoid.exponent_dvd_of_monoidHom H.subtype H.subtype_injective

/--
If there exists a multiplication-preserving equivalence between `G` and `H`,
then the exponent of `G` is equal to the exponent of `H`.
-/
@[to_additive /-- If there exists an addition-preserving equivalence between `G` and `H`,
then the exponent of `G` is equal to the exponent of `H`. -/]
/-
**Monoid.exponent_eq_of_mulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：exponent_eq_of_mulEquiv (e : G ≃* H) : Monoid.exponent G = Monoid.exponent
 H
参数：e : G ≃* H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Monoid.exponent_dvd_of_monoidHom`：exponent_dvd_of_monoidHom (e : G ->* H
) (e_inj : Function.Injective e) : Monoid.exponent G ∣ Monoid.exponent H
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
-/
theorem exponent_eq_of_mulEquiv (e : G ≃* H) : Monoid.exponent G = Monoid.exponent H :=
  Nat.dvd_antisymm
    (exponent_dvd_of_monoidHom e e.injective)
    (exponent_dvd_of_monoidHom e.symm e.symm.injective)

end Monoid

section Submonoid

variable [Monoid G]

variable (G) in
@[to_additive (attr := simp)]
/-
**_root_.Submonoid.exponent_top** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：_root_.Submonoid.exponent_top : Monoid.exponent (⊤ : Submonoid G) = Monoid
.exponent G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submonoid.exponent_top :
    Monoid.exponent (⊤ : Submonoid G) = Monoid.exponent G :=
  exponent_eq_of_mulEquiv Submonoid.topEquiv

@[to_additive]
/-
**_root_.Submonoid.pow_exponent_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：_root_.Submonoid.pow_exponent_eq_one {S : Submonoid G} {g : G} (g_in_s : g
 in S) : g ^ (Monoid.exponent S) = 1
参数：g_in_s : g in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submonoid.pow_exponent_eq_one {S : Submonoid G} {g : G} (g_in_s : g ∈ S) :
    g ^ (Monoid.exponent S) = 1 := by
  have := Monoid.pow_exponent_eq_one (⟨g, g_in_s⟩ : S)
  rwa [SubmonoidClass.mk_pow, ← OneMemClass.coe_eq_one] at this

end Submonoid

section LeftCancelMonoid

variable [LeftCancelMonoid G] [Finite G]

@[to_additive]
/-
**ExponentExists.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Monoid`。
形式化陈述：ExponentExists.of_finite : ExponentExists G
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ExponentExists.of_finite : ExponentExists G := by
  let _inst := Fintype.ofFinite G
  simp only [Monoid.ExponentExists]
  refine ⟨(Finset.univ : Finset G).lcm orderOf, ?_, fun g => ?_⟩
  · simpa [pos_iff_ne_zero, Finset.lcm_eq_zero_iff] using fun x => (_root_.orderOf_pos x).ne'
  · rw [← orderOf_dvd_iff_pow_eq_one, lcm_orderOf_eq_exponent]
    exact order_dvd_exponent g

@[to_additive]
/-
**exponent_ne_zero_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exponent_ne_zero_of_finite : exponent G ≠ 0 :=
  ExponentExists.of_finite.exponent_ne_zero

@[to_additive AddMonoid.one_lt_exponent]
/-
**one_lt_exponent** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_lt_exponent [Nontrivial G] : 1 < Monoid.exponent G := by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨exponent_ne_zero_of_finite, mt exp_eq_one_iff.mp (not_subsingleton G)⟩

@[to_additive]
/-
**neZero_exponent_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance neZero_exponent_of_finite : NeZero <| Monoid.exponent G :=
  ⟨Monoid.exponent_ne_zero_of_finite⟩

end LeftCancelMonoid

section CommMonoid

variable [CommMonoid G]

@[to_additive]
/-
**exists_orderOf_eq_exponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_orderOf_eq_exponent (hG : ExponentExists G) : ∃ g : G, orderOf g = exponent G := by
  have he := hG.exponent_ne_zero
  have hne : (Set.range (orderOf : G → ℕ)).Nonempty := ⟨1, 1, orderOf_one⟩
  have hfin : (Set.range (orderOf : G → ℕ)).Finite := by
    rwa [← exponent_ne_zero_iff_range_orderOf_finite hG.orderOf_pos]
  obtain ⟨t, ht⟩ := hne.csSup_mem hfin
  use t
  apply Nat.dvd_antisymm (order_dvd_exponent _)
  refine Nat.dvd_of_primeFactorsList_subperm he ?_
  rw [List.subperm_ext_iff]
  by_contra! ⟨p, hp, hpe⟩
  replace hp := Nat.prime_of_mem_primeFactorsList hp
  simp only [Nat.primeFactorsList_count_eq] at hpe
  set k := (orderOf t).factorization p with hk
  obtain ⟨g, hg⟩ := hp.exists_orderOf_eq_pow_factorization_exponent G
  suffices orderOf t < orderOf (t ^ p ^ k * g) by
    rw [ht] at this
    exact this.not_ge (le_csSup hfin.bddAbove <| Set.mem_range_self _)
  have hpk : p ^ k ∣ orderOf t := Nat.ordProj_dvd _ _
  have hpk' : orderOf (t ^ p ^ k) = orderOf t / p ^ k := by
    rw [orderOf_pow' t (pow_ne_zero k hp.ne_zero), Nat.gcd_eq_right hpk]
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_lt hpe
  have hcoprime : (orderOf (t ^ p ^ k)).Coprime (orderOf g) := by
    rw [hg, Nat.coprime_pow_right_iff (pos_of_gt hpe), Nat.coprime_comm]
    apply Or.resolve_right (Nat.coprime_or_dvd_of_prime hp _)
    nth_rw 1 [← pow_one p]
    have : 1 = (Nat.factorization (orderOf (t ^ p ^ k))) p + 1 := by
      rw [hpk', Nat.factorization_div hpk]
      simp [k, hp]
    rw [this]
    -- Porting note: convert made to_additive complain
    exact Nat.pow_succ_factorization_not_dvd (hG.orderOf_pos <| t ^ p ^ k).ne' hp
  rw [(Commute.all _ g).orderOf_mul_eq_mul_orderOf_of_coprime hcoprime, hpk',
    hg, ha, hk, pow_add, pow_add, pow_one, ← mul_assoc, ← mul_assoc,
    Nat.div_mul_cancel, mul_assoc, lt_mul_iff_one_lt_right <| hG.orderOf_pos t, ← pow_succ]
  · exact one_lt_pow₀ hp.one_lt a.succ_ne_zero
  · exact hpk

@[to_additive]
/-
**exponent_eq_iSup_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exponent_eq_iSup_orderOf (h : ∀ g : G, 0 < orderOf g) :
    exponent G = ⨆ g : G, orderOf g := by
  rw [iSup]
  by_cases ExponentExists G
  case neg he =>
    rw [← exponent_eq_zero_iff] at he
    rw [he, Set.Infinite.Nat.sSup_eq_zero <| (exponent_eq_zero_iff_range_orderOf_infinite h).1 he]
  case pos he =>
    rw [csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.range_nonempty _)]
    · simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      exact orderOf_le_exponent he
    intro x hx
    obtain ⟨g, hg⟩ := exists_orderOf_eq_exponent he
    rw [← hg] at hx
    simp_rw [Set.mem_range, exists_exists_eq_and]
    exact ⟨g, hx⟩

open scoped Classical in
@[to_additive]
/-
**exponent_eq_iSup_orderOf'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exponent_eq_iSup_orderOf' :
    exponent G = if ∃ g : G, orderOf g = 0 then 0 else ⨆ g : G, orderOf g := by
  split_ifs with h
  · obtain ⟨g, hg⟩ := h
    exact exponent_eq_zero_of_order_zero hg
  · have := not_exists.mp h
    exact exponent_eq_iSup_orderOf fun g => Ne.bot_lt <| this g

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid G]

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**exponent_eq_max'_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exponent_eq_max'_orderOf [Fintype G] :
    exponent G = ((@Finset.univ G _).image orderOf).max' ⟨1, by simp⟩ := by
  rw [← Finset.Nonempty.csSup_eq_max', Finset.coe_image, Finset.coe_univ, Set.image_univ, ← iSup]
  exact exponent_eq_iSup_orderOf orderOf_pos

end CancelCommMonoid

end Monoid

section Group

variable [Group G] {n m : ℤ}

@[to_additive]
/-
**Group.exponent_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.exponent_dvd_card [Fintype G] : Monoid.exponent G ∣ Fintype.card G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.exponent_dvd`：exponent_dvd {n : Nat} : exponent G ∣ n ↔ forall g 
: G, orderOf g ∣ n
· 使用定理 `orderOf_dvd_card`：orderOf_dvd_card : orderOf x ∣ Fintype.card G
-/
theorem Group.exponent_dvd_card [Fintype G] : Monoid.exponent G ∣ Fintype.card G :=
  Monoid.exponent_dvd.mpr <| fun _ => orderOf_dvd_card

@[to_additive]
/-
**Group.exponent_dvd_nat_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.exponent_dvd_nat_card : Monoid.exponent G ∣ Nat.card G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.exponent_dvd`：exponent_dvd {n : Nat} : exponent G ∣ n ↔ forall g 
: G, orderOf g ∣ n
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
-/
theorem Group.exponent_dvd_nat_card : Monoid.exponent G ∣ Nat.card G :=
  Monoid.exponent_dvd.mpr orderOf_dvd_natCard

@[to_additive]
/-
**Subgroup.exponent_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.exponent_toSubmonoid (H : Subgroup G) : Monoid.exponent H.toSubmo
noid = Monoid.exponent H
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.exponent_eq_of_mulEquiv`：exponent_eq_of_mulEquiv (e : G ≃* H) : M
onoid.exponent G = Monoid.exponent H
-/
theorem Subgroup.exponent_toSubmonoid (H : Subgroup G) :
    Monoid.exponent H.toSubmonoid = Monoid.exponent H :=
  Monoid.exponent_eq_of_mulEquiv (MulEquiv.subgroupCongr rfl)

@[to_additive (attr := simp)]
/-
**Subgroup.exponent_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.exponent_top : Monoid.exponent (⊤ : Subgroup G) = Monoid.exponent
 G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.exponent_eq_of_mulEquiv`：exponent_eq_of_mulEquiv (e : G ≃* H) : M
onoid.exponent G = Monoid.exponent H
-/
theorem Subgroup.exponent_top : Monoid.exponent (⊤ : Subgroup G) = Monoid.exponent G :=
  Monoid.exponent_eq_of_mulEquiv topEquiv

@[to_additive]
/-
**Subgroup.pow_exponent_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.pow_exponent_eq_one {H : Subgroup G} {g : G} (g_in_H : g in H) : 
g ^ Monoid.exponent H = 1
参数：g_in_H : g in H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.pow_exponent_eq_one`：∀ {G : Type u} [inst : Monoid G] {S : Sub
monoid G} {g : G}, g ∈ S → g ^ Monoid.exponent ↥S = 1
· 使用定理 `Subgroup.exponent_toSubmonoid`：Subgroup.exponent_toSubmonoid (H : Subgro
up G) : Monoid.exponent H.toSubmonoid = Monoid.exponent H
-/
theorem Subgroup.pow_exponent_eq_one {H : Subgroup G} {g : G} (g_in_H : g ∈ H) :
    g ^ Monoid.exponent H = 1 := exponent_toSubmonoid H ▸ Submonoid.pow_exponent_eq_one g_in_H

@[to_additive]
/-
**Group.exponent_dvd_iff_forall_zpow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.exponent_dvd_iff_forall_zpow_eq_one : (Monoid.exponent G : Int) ∣ n 
↔ forall g : G, g ^ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Group.exponent_dvd_iff_forall_zpow_eq_one :
    (Monoid.exponent G : ℤ) ∣ n ↔ ∀ g : G, g ^ n = 1 := by
  simp_rw [Int.natCast_dvd, Monoid.exponent_dvd_iff_forall_pow_eq_one, pow_natAbs_eq_one]

@[to_additive]
/-
**Group.exponent_dvd_sub_iff_zpow_eq_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.exponent_dvd_sub_iff_zpow_eq_zpow : (Monoid.exponent G : Int) ∣ n - 
m ↔ forall g : G, g ^ n = g ^ m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Group.exponent_dvd_sub_iff_zpow_eq_zpow :
    (Monoid.exponent G : ℤ) ∣ n - m ↔ ∀ g : G, g ^ n = g ^ m := by
  simp_rw [Group.exponent_dvd_iff_forall_zpow_eq_one, zpow_sub, mul_inv_eq_one]

end Group

section PiProd

open Finset Monoid

@[to_additive]
/-
**Monoid.exponent_pi_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.exponent_pi_eq_zero {ι : Type*} {M : ι -> Type*} [forall i, Monoid 
(M i)] {j : ι} (hj : exponent (M j) = 0) : exponent ((i : ι) -> M i) = 0
参数：M i；hj : exponent (M j) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.exponent_eq_zero_iff`：exponent_eq_zero_iff : exponent G = 0 ↔ ¬Ex
ponentExists G
· 使用定理 `Monoid.ExponentExists.eq_1`：∀ (G : Type u) [inst : Monoid G], Monoid.Exp
onentExists G = ∃ n, 0 < n ∧ ∀ (g : G), g ^ n = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem Monoid.exponent_pi_eq_zero {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {j : ι}
    (hj : exponent (M j) = 0) : exponent ((i : ι) → M i) = 0 := by
  classical
  rw [@exponent_eq_zero_iff, ExponentExists] at hj ⊢
  push Not at hj ⊢
  peel hj with n hn _
  obtain ⟨m, hm⟩ := this
  refine ⟨Pi.mulSingle j m, fun h ↦ hm ?_⟩
  simpa using congr_fun h j

/-- If `f : M₁ →⋆ M₂` is surjective, then the exponent of `M₂` divides the exponent of `M₁`. -/
@[to_additive]
/-
**MonoidHom.exponent_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.exponent_dvd {F M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] [FunLike 
F M₁ M₂] [MonoidHomClass F M₁ M₂] {f : F} (hf : Function.Surjective f) : exponen
t M₂ ∣ exponent M₁
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.exponent_dvd_of_forall_pow_eq_one`：∀ {G : Type u} [inst : Monoid 
G] {n : ℕ}, (∀ (g : G), g ^ n = 1) → Monoid.exponent G ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…

--- 原说明 ---
If `f : M₁ →⋆ M₂` is surjective, then the exponent of `M₂` divides the exponent 
of `M₁`.
-/
theorem MonoidHom.exponent_dvd {F M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
    [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂]
    {f : F} (hf : Function.Surjective f) : exponent M₂ ∣ exponent M₁ := by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun m₂ ↦ ?_
  obtain ⟨m₁, rfl⟩ := hf m₂
  rw [← map_pow, pow_exponent_eq_one, map_one]

/-- The exponent of finite product of monoids is the `Finset.lcm` of the exponents of the
constituent monoids. -/
@[to_additive /-- The exponent of finite product of additive monoids is the `Finset.lcm` of the
exponents of the constituent additive monoids. -/]
/-
**Monoid.exponent_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.exponent_pi {ι : Type*} [Fintype ι] {M : ι -> Type*} [forall i, Mon
oid (M i)] : exponent ((i : ι) -> M i) = lcm univ (exponent <| M ·)
参数：M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Monoid.exponent_dvd_of_forall_pow_eq_one`：∀ {G : Type u} [inst : Monoid 
G] {n : ℕ}, (∀ (g : G), g ^ n = 1) → Monoid.exponent G ∣ n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.pow_apply`：pow_apply (f : forall i, M i) (a : α) (i : ι) : (f ^ a) i 
= f i ^ a
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G
· 使用定理 `Finset.dvd_lcm`：dvd_lcm {b : β} (hb : b in s) : f b ∣ s.lcm f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.lcm_dvd`：lcm_dvd {a : α} : (forall b in s, f b ∣ a) -> s.lcm f ∣ 
a
· 使用定理 `MonoidHom.exponent_dvd`：MonoidHom.exponent_dvd {F M₁ M₂ : Type*} [Monoid
 M₁] [Monoid M₂] [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂] {f : F} (hf : Functi
on.Surjectiv…
· 使用定理 `Function.surjective_eval`：surjective_eval {α : Sort u} {β : α -> Sort v}
 [h : forall a, Nonempty (β a)] (a : α) : Surjective (eval a : (forall a, β a) -
> β a)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
theorem Monoid.exponent_pi {ι : Type*} [Fintype ι] {M : ι → Type*} [∀ i, Monoid (M i)] :
    exponent ((i : ι) → M i) = lcm univ (exponent <| M ·) := by
  refine dvd_antisymm ?_ ?_
  · refine exponent_dvd_of_forall_pow_eq_one fun m ↦ ?_
    ext i
    rw [Pi.pow_apply, Pi.one_apply, ← orderOf_dvd_iff_pow_eq_one]
    apply dvd_trans (Monoid.order_dvd_exponent (m i))
    exact Finset.dvd_lcm (mem_univ i)
  · apply Finset.lcm_dvd fun i _ ↦ ?_
    exact MonoidHom.exponent_dvd (f := Pi.evalMonoidHom (M ·) i) (Function.surjective_eval i)

/-- The exponent of product of two monoids is the `lcm` of the exponents of the
individual monoids. -/
@[to_additive AddMonoid.exponent_prod /-- The exponent of product of two additive monoids is the
`lcm` of the exponents of the individual additive monoids. -/]
/-
**Monoid.exponent_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.exponent_prod {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] : exponent (M
₁ × M₂) = lcm (exponent M₁) (exponent M₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Monoid.exponent_dvd_of_forall_pow_eq_one`：∀ {G : Type u} [inst : Monoid 
G] {n : ℕ}, (∀ (g : G), g ^ n = 1) → Monoid.exponent G ∣ n
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Prod.pow_fst`：pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c
· 使用定理 `Prod.fst_one`：fst_one : (1 : M × N).1 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G
· 使用定理 `dvd_lcm_left`：dvd_lcm_left [GCDMonoid α] (a b : α) : a ∣ lcm a b
· 使用引理 `Prod.pow_snd`：pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c
· 使用定理 `Prod.snd_one`：snd_one : (1 : M × N).2 = 1
· 使用定理 `dvd_lcm_right`：dvd_lcm_right [GCDMonoid α] (a b : α) : b ∣ lcm a b
· 使用定理 `lcm_dvd`：lcm_dvd [GCDMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) :
 lcm a c ∣ b
· 使用定理 `MonoidHom.exponent_dvd`：MonoidHom.exponent_dvd {F M₁ M₂ : Type*} [Monoid
 M₁] [Monoid M₂] [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂] {f : F} (hf : Functi
on.Surjectiv…
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
-/
theorem Monoid.exponent_prod {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] :
    exponent (M₁ × M₂) = lcm (exponent M₁) (exponent M₂) := by
  refine dvd_antisymm ?_ (lcm_dvd ?_ ?_)
  · refine exponent_dvd_of_forall_pow_eq_one fun g ↦ ?_
    ext1
    · rw [Prod.pow_fst, Prod.fst_one, ← orderOf_dvd_iff_pow_eq_one]
      exact dvd_trans (Monoid.order_dvd_exponent (g.1)) <| dvd_lcm_left _ _
    · rw [Prod.pow_snd, Prod.snd_one, ← orderOf_dvd_iff_pow_eq_one]
      exact dvd_trans (Monoid.order_dvd_exponent (g.2)) <| dvd_lcm_right _ _
  · exact MonoidHom.exponent_dvd (f := MonoidHom.fst M₁ M₂) Prod.fst_surjective
  · exact MonoidHom.exponent_dvd (f := MonoidHom.snd M₁ M₂) Prod.snd_surjective

end PiProd

/-! ### Properties of monoids with exponent two -/

section ExponentTwo

section Monoid

variable [Monoid G]

@[to_additive]
/-
**orderOf_eq_two_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_eq_two_iff (hG : Monoid.exponent G = 2) {x : G} : orderOf x = 2 ↔ 
x != 1
参数：hG : Monoid.exponent G = 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_eq_prime`：orderOf_eq_prime (hg : x ^ p = 1) (hg1 : x != 1) : ord
erOf x = p
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
-/
lemma orderOf_eq_two_iff (hG : Monoid.exponent G = 2) {x : G} :
    orderOf x = 2 ↔ x ≠ 1 :=
  ⟨by rintro hx rfl; norm_num at hx, orderOf_eq_prime (hG ▸ Monoid.pow_exponent_eq_one x)⟩

@[to_additive]
/-
**Commute.of_orderOf_dvd_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.of_orderOf_dvd_two [IsCancelMul G] (h : forall g : G, orderOf g ∣ 
2) (a b : G) : Commute a b
参数：h : forall g : G, orderOf g ∣ 2；a b : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_inj`：mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `mul_left_inj`：mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Commute.of_orderOf_dvd_two [IsCancelMul G] (h : ∀ g : G, orderOf g ∣ 2) (a b : G) :
    Commute a b := by
  simp_rw [orderOf_dvd_iff_pow_eq_one] at h
  rw [commute_iff_eq, ← mul_right_inj a, ← mul_left_inj b]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  calc
    a * (a * b) * b = a ^ 2 * b ^ 2 := by simp [pow_two, mul_assoc]
    _ = 1 := by rw [h, h, mul_one]
    _ = (a * b) ^ 2 := by rw [h]
    _ = a * (b * a) * b := by simp [pow_two, mul_assoc]

/-- In a cancellative monoid of exponent two, all elements commute. -/
@[to_additive]
/-
**mul_comm_of_exponent_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_comm_of_exponent_two [IsCancelMul G] (hG : Monoid.exponent G = 2) (a b
 : G) : a * b = b * a
参数：hG : Monoid.exponent G = 2；a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.of_orderOf_dvd_two`：Commute.of_orderOf_dvd_two [IsCancelMul G] (
h : forall g : G, orderOf g ∣ 2) (a b : G) : Commute a b
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G

--- 原说明 ---
In a cancellative monoid of exponent two, all elements commute.
-/
lemma mul_comm_of_exponent_two [IsCancelMul G] (hG : Monoid.exponent G = 2) (a b : G) :
    a * b = b * a :=
  Commute.of_orderOf_dvd_two (fun g => hG ▸ Monoid.order_dvd_exponent g) a b

/-- Any cancellative monoid of exponent two is abelian. -/
@[to_additive /-- Any additive group of exponent two is abelian. -/]
/-
**commMonoidOfExponentTwo** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：commMonoidOfExponentTwo [IsCancelMul G] (hG : Monoid.exponent G = 2) : Com
mMonoid G where mul_comm
参数：hG : Monoid.exponent G = 2。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `mul_comm_of_exponent_two`：mul_comm_of_exponent_two [IsCancelMul G] (hG :
 Monoid.exponent G = 2) (a b : G) : a * b = b * a

--- 原说明 ---
Any cancellative monoid of exponent two is abelian.
-/
abbrev commMonoidOfExponentTwo [IsCancelMul G] (hG : Monoid.exponent G = 2) : CommMonoid G where
  mul_comm := mul_comm_of_exponent_two hG

end Monoid

section Group

variable [Group G]

/--
If `H` is a normal subgroup of `G`, then the exponent of `G ⧸ H` divides the exponent of `G`.
-/
@[to_additive
/-- If `H` is a normal additive subgroup of `G`, then the exponent of `G ⧸ H` divides the
exponent of `G`. -/]
/-
**Group.exponent_quotient_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.exponent_quotient_dvd (H : Subgroup G) [H.Normal] : Monoid.exponent 
(G ⧸ H) ∣ Monoid.exponent G
参数：H : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.exponent_dvd`：MonoidHom.exponent_dvd {F M₁ M₂ : Type*} [Monoid
 M₁] [Monoid M₂] [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂] {f : F} (hf : Functi
on.Surjectiv…
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
-/
theorem Group.exponent_quotient_dvd (H : Subgroup G) [H.Normal] :
    Monoid.exponent (G ⧸ H) ∣ Monoid.exponent G :=
  MonoidHom.exponent_dvd (QuotientGroup.mk'_surjective H)

/-- In a group of exponent two, every element is its own inverse. -/
@[to_additive]
/-
**inv_eq_self_of_exponent_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_eq_self_of_exponent_two (hG : Monoid.exponent G = 2) (x : G) : x⁻¹ = x
参数：hG : Monoid.exponent G = 2；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_left`：inv_eq_of_mul_eq_one_left (h : a * b = 1) : b
⁻¹ = a
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
In a group of exponent two, every element is its own inverse.
-/
lemma inv_eq_self_of_exponent_two (hG : Monoid.exponent G = 2) (x : G) :
    x⁻¹ = x :=
  inv_eq_of_mul_eq_one_left <| pow_two (a := x) ▸ hG ▸ Monoid.pow_exponent_eq_one x

/-- If an element in a group has order two, then it is its own inverse. -/
@[to_additive]
/-
**inv_eq_self_of_orderOf_eq_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_eq_self_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x⁻¹ = x
参数：hx : orderOf x = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_left`：inv_eq_of_mul_eq_one_left (h : a * b = 1) : b
⁻¹ = a
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
If an element in a group has order two, then it is its own inverse.
-/
lemma inv_eq_self_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) :
    x⁻¹ = x :=
  inv_eq_of_mul_eq_one_left <| pow_two (a := x) ▸ hx ▸ pow_orderOf_eq_one x

@[to_additive]
/-
**mul_notMem_of_orderOf_eq_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_notMem_of_orderOf_eq_two {x y : G} (hx : orderOf x = 2) (hy : orderOf 
y = 2) (hxy : x != y) : x * y ∉ ({x, y, 1} : Set G)
参数：hx : orderOf x = 2；hy : orderOf y = 2；hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用引理 `inv_eq_self_of_orderOf_eq_two`：inv_eq_self_of_orderOf_eq_two {x : G} (hx
 : orderOf x = 2) : x⁻¹ = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mul_notMem_of_orderOf_eq_two {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x ≠ y) : x * y ∉ ({x, y, 1} : Set G) := by
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, mul_eq_left, mul_eq_right,
    mul_eq_one_iff_eq_inv, inv_eq_self_of_orderOf_eq_two hy, not_or]
  aesop

@[to_additive]
/-
**mul_notMem_of_exponent_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_notMem_of_exponent_two (h : Monoid.exponent G = 2) {x y : G} (hx : x !
= 1) (hy : y != 1) (hxy : x != y) : x * y ∉ ({x, y, 1} : Set G)
参数：h : Monoid.exponent G = 2；hx : x != 1；hy : y != 1；hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_notMem_of_orderOf_eq_two`：mul_notMem_of_orderOf_eq_two {x y : G} (hx
 : orderOf x = 2) (hy : orderOf y = 2) (hxy : x != y) : x * y ∉ ({x, y, 1} : Set
 G)
· 使用定理 `orderOf_eq_prime`：orderOf_eq_prime (hg : x ^ p = 1) (hg1 : x != 1) : ord
erOf x = p
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
-/
lemma mul_notMem_of_exponent_two (h : Monoid.exponent G = 2) {x y : G}
    (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) : x * y ∉ ({x, y, 1} : Set G) :=
  mul_notMem_of_orderOf_eq_two (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one x) hx)
    (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one y) hy) hxy

end Group

end ExponentTwo

