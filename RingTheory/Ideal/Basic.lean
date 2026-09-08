/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Tactic.FinCases

/-!

# Ideals over a ring

This file contains an assortment of definitions and results for `Ideal R`,
the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

@[expose] public section


variable {ι α β F : Type*}

open Set Function

open scoped Pointwise

section Semiring

namespace Ideal

variable {R : ι → Type*} [Π i, Semiring (R i)] (I J : Π i, Ideal (R i))

section Pi

/-- `Πᵢ Iᵢ` as an ideal of `Πᵢ Rᵢ`. -/
/-
**Ideal.pi** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：pi : Ideal (Π i, R i) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Πᵢ Iᵢ` as an ideal of `Πᵢ Rᵢ`.
-/
def pi : Ideal (Π i, R i) where
  carrier := { r | ∀ i, r i ∈ I i }
  zero_mem' i := (I i).zero_mem
  add_mem' ha hb i := (I i).add_mem (ha i) (hb i)
  smul_mem' a _b hb i := (I i).mul_mem_left (a i) (hb i)
/-
**Ideal.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_pi (r : Π i, R i) : r in pi I ↔ forall i, r i in I i
参数：r : Π i, R i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pi (r : Π i, R i) : r ∈ pi I ↔ ∀ i, r i ∈ I i :=
  Iff.rfl
/-
**Ideal.pi_span** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {ι : Type u_1} {R : ι → Type u_5} [inst : (i : ι) → Semiring (R i)] {r :
 (i : ι) → R i},   (Ideal.pi fun x => Ideal.span {r x}) = Ideal.span {r}
参数：i : ι；R i；i : ι；Ideal.pi fun x => Ideal.span {r x}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem pi_span {r : Π i, R i} : pi (span {r ·}) = span {r} := by
  ext; simp_rw [mem_pi, mem_span_singleton', funext_iff, Classical.skolem, Pi.mul_def]
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [∀ i, (I i).IsTwoSided] : (pi I).IsTwoSided :=
  ⟨fun _b hb i ↦ mul_mem_right _ _ (hb i)⟩

variable {I J}
/-
**Ideal.single_mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：single_mem_pi [DecidableEq ι] {i : ι} {r : R i} (hr : r in I i) : Pi.singl
e i r in pi I
参数：hr : r in I i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem single_mem_pi [DecidableEq ι] {i : ι} {r : R i} (hr : r ∈ I i) : Pi.single i r ∈ pi I := by
  intro j
  obtain rfl | ne := eq_or_ne i j
  · simpa
  · simp [ne]
/-
**Ideal.pi_le_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {ι : Type u_1} {R : ι → Type u_5} [inst : (i : ι) → Semiring (R i)] {I J
 : (i : ι) → Ideal (R i)},   Ideal.pi I ≤ Ideal.pi J ↔ I ≤ J
参数：i : ι；R i；i : ι；R i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Ideal.single_mem_pi`：single_mem_pi [DecidableEq ι] {i : ι} {r : R i} (hr
 : r in I i) : Pi.single i r in pi I
-/
@[simp] theorem pi_le_pi_iff : pi I ≤ pi J ↔ I ≤ J where
  mp le i r hr := by classical simpa using le (single_mem_pi hr) i
  mpr le r hr i := le i (hr i)

end Pi

section Commute

variable {α : Type*} [Semiring α] (I : Ideal α) {a b : α}

/-
**Ideal.add_pow_mem_of_pow_mem_of_le_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
`。
形式化陈述：add_pow_mem_of_pow_mem_of_le_of_commute {m n k : Nat} (ha : a ^ m in I) (h
b : b ^ n in I) (hk : m + n <= k + 1) (hab : Commute a b) : (a + b) ^ k in I
参数：ha : a ^ m in I；hb : b ^ n in I；hk : m + n <= k + 1；hab : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.add_pow`：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m
 in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
· 使用定理 `Ideal.pow_mem_of_pow_mem`：pow_mem_of_pow_mem {m n : Nat} (ha : a ^ m in 
I) (h : m <= n) : a ^ n in I
-/
theorem add_pow_mem_of_pow_mem_of_le_of_commute {m n k : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) (hk : m + n ≤ k + 1)
    (hab : Commute a b) :
    (a + b) ^ k ∈ I := by
  simp_rw [hab.add_pow, ← Nat.cast_comm]
  apply I.sum_mem
  intro c _
  apply mul_mem_left
  by_cases h : m ≤ c
  · rw [hab.pow_pow]
    exact I.mul_mem_left _ (I.pow_mem_of_pow_mem ha h)
  · refine I.mul_mem_left _ (I.pow_mem_of_pow_mem hb ?_)
    lia
/-
**Ideal.add_pow_add_pred_mem_of_pow_mem_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal`。
形式化陈述：add_pow_add_pred_mem_of_pow_mem_of_commute {m n : Nat} (ha : a ^ m in I) (
hb : b ^ n in I) (hab : Commute a b) : (a + b) ^ (m + n - 1) in I
参数：ha : a ^ m in I；hb : b ^ n in I；hab : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.add_pow_mem_of_pow_mem_of_le_of_commute`：add_pow_mem_of_pow_mem_of
_le_of_commute {m n k : Nat} (ha : a ^ m in I) (hb : b ^ n in I) (hk : m + n <= 
k + 1) (hab : Commute a b) : (a + b…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_le_iff_le_add`：∀ {a b c : ℕ}, a - b ≤ c ↔ a ≤ c + b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem add_pow_add_pred_mem_of_pow_mem_of_commute {m n : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) (hab : Commute a b) :
    (a + b) ^ (m + n - 1) ∈ I :=
  I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb (by rw [← Nat.sub_le_iff_le_add]) hab

end Commute

end Ideal

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

/-
**Ideal.add_pow_mem_of_pow_mem_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：add_pow_mem_of_pow_mem_of_le {m n k : Nat} (ha : a ^ m in I) (hb : b ^ n i
n I) (hk : m + n <= k + 1) : (a + b) ^ k in I
参数：ha : a ^ m in I；hb : b ^ n in I；hk : m + n <= k + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.add_pow_mem_of_pow_mem_of_le_of_commute`：add_pow_mem_of_pow_mem_of
_le_of_commute {m n k : Nat} (ha : a ^ m in I) (hb : b ^ n in I) (hk : m + n <= 
k + 1) (hab : Commute a b) : (a + b…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem add_pow_mem_of_pow_mem_of_le {m n k : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) (hk : m + n ≤ k + 1) :
    (a + b) ^ k ∈ I :=
  I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb hk (Commute.all ..)
/-
**Ideal.add_pow_add_pred_mem_of_pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：add_pow_add_pred_mem_of_pow_mem {m n : Nat} (ha : a ^ m in I) (hb : b ^ n 
in I) : (a + b) ^ (m + n - 1) in I
参数：ha : a ^ m in I；hb : b ^ n in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.add_pow_add_pred_mem_of_pow_mem_of_commute`：add_pow_add_pred_mem_o
f_pow_mem_of_commute {m n : Nat} (ha : a ^ m in I) (hb : b ^ n in I) (hab : Comm
ute a b) : (a + b) ^ (m + n - 1) in I
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem add_pow_add_pred_mem_of_pow_mem {m n : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) :
    (a + b) ^ (m + n - 1) ∈ I :=
  I.add_pow_add_pred_mem_of_pow_mem_of_commute ha hb (Commute.all ..)
/-
**Ideal.pow_multiset_sum_mem_span_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pow_multiset_sum_mem_span_pow [DecidableEq α] (s : Multiset α) (n : Nat) :
 s.sum ^ (Multiset.card s * n + 1) in span ((s.map fun (x : α) => x ^ (n + 1)).t
oFinset : Set α)
参数：s : Multiset α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.toFinset_cons`：toFinset_cons (a : α) (s : Multiset α) : toFinse
t (a ::ₘ s) = insert a (toFinset s)
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Ideal.mem_span_insert`：mem_span_insert {s : Set α} {x y} : x in span (in
sert y s) ↔ exists a, exists z in span s, x = a * y + z
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 41 条，此处仅展示前 30 条）
-/
theorem pow_multiset_sum_mem_span_pow [DecidableEq α] (s : Multiset α) (n : ℕ) :
    s.sum ^ (Multiset.card s * n + 1) ∈
    span ((s.map fun (x : α) ↦ x ^ (n + 1)).toFinset : Set α) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s hs => ?_
  simp only [Finset.coe_insert, Multiset.map_cons, Multiset.toFinset_cons, Multiset.sum_cons,
    Multiset.card_cons, add_pow]
  refine Submodule.sum_mem _ ?_
  intro c _hc
  rw [mem_span_insert]
  by_cases! h : n + 1 ≤ c
  · refine ⟨a ^ (c - (n + 1)) * s.sum ^ ((Multiset.card s + 1) * n + 1 - c) *
      ((Multiset.card s + 1) * n + 1).choose c, 0, Submodule.zero_mem _, ?_⟩
    rw [mul_comm _ (a ^ (n + 1))]
    simp_rw [← mul_assoc]
    rw [← pow_add, add_zero, add_tsub_cancel_of_le h]
  · use 0
    simp_rw [zero_mul, zero_add]
    refine ⟨_, ?_, rfl⟩
    replace h : c ≤ n := Nat.lt_succ_iff.mp h
    have : (Multiset.card s + 1) * n + 1 - c = Multiset.card s * n + 1 + (n - c) := by
      rw [add_mul, one_mul, add_assoc, add_comm n 1, ← add_assoc, add_tsub_assoc_of_le h]
    rw [this, pow_add]
    simp_rw [mul_assoc, mul_comm (s.sum ^ (Multiset.card s * n + 1)), ← mul_assoc]
    exact mul_mem_left _ _ hs
/-
**Ideal.sum_pow_mem_span_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：sum_pow_mem_span_pow {ι} (s : Finset ι) (f : ι -> α) (n : Nat) : (∑ i in s
, f i) ^ (s.card * n + 1) in span ((fun i => f i ^ (n + 1)) '' s)
参数：s : Finset ι；f : ι -> α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.toFinset_map`：Multiset.toFinset_map [DecidableEq α] [DecidableE
q β] (f : α -> β) (m : Multiset α) : (m.map f).toFinset = m.toFinset.image f
· 使用定理 `Finset.val_toFinset`：val_toFinset [DecidableEq α] (s : Finset α) : s.val
.toFinset = s
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Ideal.pow_multiset_sum_mem_span_pow`：pow_multiset_sum_mem_span_pow [Deci
dableEq α] (s : Multiset α) (n : Nat) : s.sum ^ (Multiset.card s * n + 1) in spa
n ((s.map fun (x : α) => …
-/
theorem sum_pow_mem_span_pow {ι} (s : Finset ι) (f : ι → α) (n : ℕ) :
    (∑ i ∈ s, f i) ^ (s.card * n + 1) ∈ span ((fun i => f i ^ (n + 1)) '' s) := by
  classical
  simpa only [Multiset.card_map, Multiset.map_map, comp_apply, Multiset.toFinset_map,
    Finset.coe_image, Finset.val_toFinset] using! pow_multiset_sum_mem_span_pow (s.1.map f) n
/-
**Ideal.span_pow_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：span_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : Nat) : span ((fun (x : 
α) => x ^ n) '' s) = ⊤
参数：s : Set α；hs : span s = ⊤；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finsupp.mem_span_iff_linearCombination`：mem_span_iff_linearCombination (
s : Set M) (x : M) : x in span R s ↔ exists l : s ->₀ R, linearCombination R (↑)
 l = x
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `Ideal.sum_pow_mem_span_pow`：sum_pow_mem_span_pow {ι} (s : Finset ι) (f :
 ι -> α) (n : Nat) : (∑ i in s, f i) ^ (s.card * n + 1) in span ((fun i => f i ^
 (n + 1)) '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem span_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : ℕ) :
    span ((fun (x : α) => x ^ n) '' s) = ⊤ := by
  rw [eq_top_iff_one]
  rcases n with - | n
  · obtain rfl | ⟨x, hx⟩ := eq_empty_or_nonempty s
    · rw [Set.image_empty, hs]
      trivial
    · exact subset_span ⟨_, hx, pow_zero _⟩
  rw [eq_top_iff_one, span, Finsupp.mem_span_iff_linearCombination] at hs
  rcases hs with ⟨f, hf⟩
  simp only [Finsupp.linearCombination, Finsupp.coe_lsum, Finsupp.sum, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, smul_eq_mul] at hf
  have := sum_pow_mem_span_pow f.support (fun a => f a * a) n
  rw [hf, one_pow] at this
  refine span_le.mpr ?_ this
  rintro _ hx
  simp_rw [Set.mem_image] at hx
  rcases hx with ⟨x, _, rfl⟩
  have : span ({(x : α) ^ (n + 1)} : Set α) ≤ span ((fun x : α => x ^ (n + 1)) '' s) := by
    rw [span_le, Set.singleton_subset_iff]
    exact subset_span ⟨x, x.prop, rfl⟩
  refine this ?_
  rw [mul_pow, mem_span_singleton]
  exact ⟨f x ^ (n + 1), mul_comm _ _⟩
/-
**Ideal.span_range_pow_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：span_range_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : s -> Nat) : span 
(Set.range fun x => x.1 ^ n x) = ⊤
参数：s : Set α；hs : span s = ⊤；n : s -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_span_finite_of_mem_span`：mem_span_finite_of_mem_span {S : 
Set M} {x : M} (hx : x in span R S) : exists T : Finset M, ↑T subseteq S ∧ x in 
span R (T : Set M)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.span_pow_eq_top`：span_pow_eq_top (s : Set α) (hs : span s = ⊤) (n 
: Nat) : span ((fun (x : α) => x ^ n) '' s) = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
theorem span_range_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : s → ℕ) :
    span (Set.range fun x ↦ x.1 ^ n x) = ⊤ := by
  have ⟨t, hts, mem⟩ := Submodule.mem_span_finite_of_mem_span ((eq_top_iff_one _).mp hs)
  refine top_unique ((span_pow_eq_top _ ((eq_top_iff_one _).mpr mem) <|
    t.attach.sup fun x ↦ n ⟨x, hts x.2⟩).ge.trans <| span_le.mpr ?_)
  rintro _ ⟨x, hxt, rfl⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup <| t.mem_attach ⟨x, hxt⟩)]
  simp_rw [pow_add]
  exact mul_mem_left _ _ (subset_span ⟨_, rfl⟩)
/-
**Ideal.prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_mem {ι : Type*} {f : ι -> α} {s : Finset ι} (I : Ideal α) {i : ι} (hi
 : i in s) (hfi : f i in I) : ∏ i in s, f i in I
参数：I : Ideal α；hi : i in s；hfi : f i in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_prod_sdiff_singleton_mul`：prod_eq_prod_sdiff_singleton_mu
l [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M) : ∏ x in s, f
 x = (∏ x in s \ {i}, f x) * …
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
-/
theorem prod_mem {ι : Type*} {f : ι → α} {s : Finset ι}
    (I : Ideal α) {i : ι} (hi : i ∈ s) (hfi : f i ∈ I) :
    ∏ i ∈ s, f i ∈ I := by
  classical
  rw [Finset.prod_eq_prod_sdiff_singleton_mul hi]
  exact Ideal.mul_mem_left _ _ hfi
/-
**Ideal.span_single_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：span_single_eq_top {ι : Type*} [DecidableEq ι] [Finite ι] (R : ι -> Type*)
 [forall i, Semiring (R i)] : Ideal.span (Set.range fun i => (Pi.single i 1 : Π 
i, R i)) = ⊤
参数：R : ι -> Type*；R i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `Pi.single_induction`：Pi.single_induction [forall i, AddCommMonoid (M i)]
 (p : (Π i, M i) -> Prop) (f : Π i, M i) (zero : p 0) (add : forall f g, p f -> 
p g -> p …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
lemma span_single_eq_top {ι : Type*} [DecidableEq ι] [Finite ι] (R : ι → Type*)
    [∀ i, Semiring (R i)] : Ideal.span (Set.range fun i ↦ (Pi.single i 1 : Π i, R i)) = ⊤ := by
  rw [_root_.eq_top_iff]
  rintro x -
  induction x using Pi.single_induction with
  | zero => simp
  | add f g hf hg => exact Ideal.add_mem _ hf hg
  | single i r =>
      rw [show Pi.single i r = Pi.single i r * Pi.single i 1 by simp [← Pi.single_mul_left]]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Ideal

end CommSemiring

section DivisionSemiring

variable {K : Type*} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

variable (K) in
/-- A bijection between (left) ideals of a division ring and `{0, 1}`, sending `⊥` to `0`
and `⊤` to `1`. -/
/-
**Ideal.equivFinTwo** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：equivFinTwo : Ideal K ≃ Fin 2 where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bijection between (left) ideals of a division ring and `{0, 1}`, sending `⊥` t
o `0`
and `⊤` to `1`.
-/
noncomputable def equivFinTwo : Ideal K ≃ Fin 2 where
  toFun := fun I ↦ if I = ⊥ then 0 else 1
  invFun := ![⊥, ⊤]
  left_inv := fun I ↦ by rcases eq_bot_or_top I with rfl | rfl <;> simp
  right_inv := fun i ↦ by fin_cases i <;> simp
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Finite (Ideal K) := let _i := Classical.decEq (Ideal K); ⟨equivFinTwo K⟩

/-- Ideals of a `DivisionSemiring` are a simple order. Thanks to the way abbreviations work,
this automatically gives an `IsSimpleModule K` instance. -/
/-
**Ideal.isSimpleOrder** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：isSimpleOrder : IsSimpleOrder (Ideal K)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Ideal.eq_bot_or_top`：eq_bot_or_top : I = ⊥ ∨ I = ⊤

--- 原说明 ---
Ideals of a `DivisionSemiring` are a simple order. Thanks to the way abbreviatio
ns work,
this automatically gives an `IsSimpleModule K` instance.
-/
instance isSimpleOrder : IsSimpleOrder (Ideal K) :=
  ⟨eq_bot_or_top⟩

end Ideal

end DivisionSemiring

-- TODO: consider moving the lemmas below out of the `Ring` namespace since they are
-- about `CommSemiring`s.
namespace Ring

variable {R : Type*} [CommSemiring R]

/-
**Ring.exists_not_isUnit_of_not_isField** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：exists_not_isUnit_of_not_isField [Nontrivial R] (hf : ¬IsField R) : exists
 (x : R) (_hx : x != (0 : R)), ¬IsUnit x
参数：hf : ¬IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
-/
theorem exists_not_isUnit_of_not_isField [Nontrivial R] (hf : ¬IsField R) :
    ∃ (x : R) (_hx : x ≠ (0 : R)), ¬IsUnit x := by
  have : ¬_ := fun h => hf ⟨exists_pair_ne R, mul_comm, h⟩
  simp_rw [isUnit_iff_exists_inv]
  push Not at this ⊢
  obtain ⟨x, hx, not_unit⟩ := this
  exact ⟨x, hx, not_unit⟩

open Ideal in
/-
**Ring.isField_iff_maximal_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：isField_iff_maximal_bot [Nontrivial R] : IsField R ↔ (⊥ : Ideal R).IsMaxim
al
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.bot_isMaximal`：bot_isMaximal : IsMaximal (⊥ : Ideal K)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ring.exists_not_isUnit_of_not_isField`：exists_not_isUnit_of_not_isField 
[Nontrivial R] (hf : ¬IsField R) : exists (x : R) (_hx : x != (0 : R)), ¬IsUnit 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.span_singleton_ne_top`：span_singleton_ne_top {α : Type*} [CommSemi
ring α] {x : α} (hx : ¬IsUnit x) : Ideal.span ({x} : Set α) != ⊤
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem isField_iff_maximal_bot [Nontrivial R] : IsField R ↔ (⊥ : Ideal R).IsMaximal := by
  refine ⟨fun h ↦ let := h.toSemifield; bot_isMaximal, fun hmax ↦ ?_⟩
  by_contra hf
  obtain ⟨x, hx0, hxu⟩ := exists_not_isUnit_of_not_isField hf
  exact hx0 <| span_singleton_eq_bot.mp (hmax.eq_of_le (span_singleton_ne_top hxu) bot_le).symm
/-
**Ring.exists_maximal_of_not_isField** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：exists_maximal_of_not_isField [Nontrivial R] (h : ¬ IsField R) : exists p 
: Ideal R, p != ⊥ ∧ p.IsMaximal
参数：h : ¬ IsField R。
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ring.isField_iff_maximal_bot`：isField_iff_maximal_bot [Nontrivial R] : I
sField R ↔ (⊥ : Ideal R).IsMaximal
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `Ideal.maximal_of_no_maximal`：maximal_of_no_maximal {P : Ideal α} (hmax :
 forall m : Ideal α, P < m -> ¬IsMaximal m) (J : Ideal α) (hPJ : P < J) : J = ⊤
-/
theorem exists_maximal_of_not_isField [Nontrivial R] (h : ¬ IsField R) :
    ∃ p : Ideal R, p ≠ ⊥ ∧ p.IsMaximal := by
  contrapose! h
  simp only [← bot_lt_iff_ne_bot] at h
  refine isField_iff_maximal_bot.mpr ⟨⟨bot_ne_top, Ideal.maximal_of_no_maximal h⟩⟩
/-
**Ring.not_isField_of_ne_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：not_isField_of_ne_of_ne [Nontrivial R] {I : Ideal R} (h_bot : I != ⊥) (h_t
op : I != ⊤) : ¬ IsField R
参数：h_bot : I != ⊥；h_top : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ring.isField_iff_maximal_bot`：isField_iff_maximal_bot [Nontrivial R] : I
sField R ↔ (⊥ : Ideal R).IsMaximal
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem not_isField_of_ne_of_ne [Nontrivial R] {I : Ideal R} (h_bot : I ≠ ⊥) (h_top : I ≠ ⊤) :
    ¬ IsField R := by
  contrapose h_bot
  exact ((isField_iff_maximal_bot.mp h_bot).eq_of_le h_top bot_le).symm
/-
**Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top** 是 Mathlib 中的一个定理，位于命名空间 
`Ring`。
形式化陈述：not_isField_iff_exists_ideal_bot_lt_and_lt_top [Nontrivial R] : ¬IsField R
 ↔ exists I : Ideal R, ⊥ < I ∧ I < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.exists_maximal_of_not_isField`：exists_maximal_of_not_isField [Nontr
ivial R] (h : ¬ IsField R) : exists p : Ideal R, p != ⊥ ∧ p.IsMaximal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Ring.not_isField_of_ne_of_ne`：not_isField_of_ne_of_ne [Nontrivial R] {I 
: Ideal R} (h_bot : I != ⊥) (h_top : I != ⊤) : ¬ IsField R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem not_isField_iff_exists_ideal_bot_lt_and_lt_top [Nontrivial R] :
    ¬IsField R ↔ ∃ I : Ideal R, ⊥ < I ∧ I < ⊤ := by
  refine ⟨fun h ↦ ?_, fun ⟨I, h_bot, h_top⟩ ↦ not_isField_of_ne_of_ne h_bot.ne' h_top.ne⟩
  obtain ⟨I, hI, hIm⟩ := exists_maximal_of_not_isField h
  exact ⟨I, bot_lt_iff_ne_bot.mpr hI, lt_top_iff_ne_top.mpr hIm.ne_top⟩
/-
**Ring.not_isField_iff_exists_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：not_isField_iff_exists_prime [Nontrivial R] : ¬IsField R ↔ exists p : Idea
l R, p != ⊥ ∧ p.IsPrime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.exists_maximal_of_not_isField`：exists_maximal_of_not_isField [Nontr
ivial R] (h : ¬ IsField R) : exists p : Ideal R, p != ⊥ ∧ p.IsMaximal
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ring.not_isField_of_ne_of_ne`：not_isField_of_ne_of_ne [Nontrivial R] {I 
: Ideal R} (h_bot : I != ⊥) (h_top : I != ⊤) : ¬ IsField R
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
theorem not_isField_iff_exists_prime [Nontrivial R] :
    ¬IsField R ↔ ∃ p : Ideal R, p ≠ ⊥ ∧ p.IsPrime := by
  refine ⟨fun h ↦ ?_, fun ⟨I, h_bot, h_top⟩ ↦ not_isField_of_ne_of_ne h_bot h_top.ne_top⟩
  obtain ⟨I, hI, hIm⟩ := exists_maximal_of_not_isField h
  exact ⟨I, hI, hIm.isPrime⟩

/-- Also see `Ideal.isSimpleOrder` for the forward direction as an instance when `R` is a
division (semi)ring.

This result actually holds for all division semirings, but we lack the predicate to state it. -/
/-
**Ring.isField_iff_isSimpleOrder_ideal** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：isField_iff_isSimpleOrder_ideal : IsField R ↔ IsSimpleOrder (Ideal R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `not_isField_of_subsingleton`：not_isField_of_subsingleton (R : Type u) [S
emiring R] [Subsingleton R] : ¬IsField R
· 使用定理 `false_of_nontrivial_of_subsingleton`：false_of_nontrivial_of_subsingleton
 (α : Type*) [Nontrivial α] [Subsingleton α] : False
· 使用定理 `IsSimpleOrder.toNontrivial`：∀ {α : Type u_4} {inst : LE α} {inst_1 : Bou
ndedOrder α} [self : IsSimpleOrder α], Nontrivial α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top`：not_isField_iff_exi
sts_ideal_bot_lt_and_lt_top [Nontrivial R] : ¬IsField R ↔ exists I : Ideal R, ⊥ 
< I ∧ I < ⊤
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤

--- 原说明 ---
Also see `Ideal.isSimpleOrder` for the forward direction as an instance when `R`
 is a
division (semi)ring.

This result actually holds for all division semirings, but we lack the predicate
 to state it.
-/
theorem isField_iff_isSimpleOrder_ideal : IsField R ↔ IsSimpleOrder (Ideal R) := by
  cases subsingleton_or_nontrivial R
  · exact
      ⟨fun h => (not_isField_of_subsingleton _ h).elim, fun h =>
        (false_of_nontrivial_of_subsingleton <| Ideal R).elim⟩
  rw [← not_iff_not, Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
  contrapose! +distrib
  simp_rw [not_lt_top_iff, not_bot_lt_iff]
  exact ⟨fun h => ⟨h⟩, fun h => h.2⟩

/-- When a ring is not a field, the maximal ideals are nontrivial. -/
/-
**Ring.ne_bot_of_isMaximal_of_not_isField** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：ne_bot_of_isMaximal_of_not_isField [Nontrivial R] {M : Ideal R} (max : M.I
sMaximal) (not_field : ¬IsField R) : M != ⊥
参数：max : M.IsMaximal；not_field : ¬IsField R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top`：not_isField_iff_exi
sts_ideal_bot_lt_and_lt_top [Nontrivial R] : ¬IsField R ↔ exists I : Ideal R, ⊥ 
< I ∧ I < ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
When a ring is not a field, the maximal ideals are nontrivial.
-/
theorem ne_bot_of_isMaximal_of_not_isField [Nontrivial R] {M : Ideal R} (max : M.IsMaximal)
    (not_field : ¬IsField R) : M ≠ ⊥ := by
  rintro rfl
  obtain ⟨I, hIbot, hItop⟩ := not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp not_field
  exact hIbot.ne (max.eq_of_le hItop.ne bot_le)

end Ring

namespace Ideal

variable {R : Type*} [CommSemiring R] [Nontrivial R]

/-
**Ideal.bot_lt_of_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：bot_lt_of_maximal (M : Ideal R) [hm : M.IsMaximal] (non_field : ¬IsField R
) : ⊥ < M
参数：M : Ideal R；non_field : ¬IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Ring.ne_bot_of_isMaximal_of_not_isField`：ne_bot_of_isMaximal_of_not_isFi
eld [Nontrivial R] {M : Ideal R} (max : M.IsMaximal) (not_field : ¬IsField R) : 
M != ⊥
-/
theorem bot_lt_of_maximal (M : Ideal R) [hm : M.IsMaximal] (non_field : ¬IsField R) : ⊥ < M :=
  (Ring.ne_bot_of_isMaximal_of_not_isField hm non_field).bot_lt

end Ideal

