/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.Derangements.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Derangements on fintypes

This file contains lemmas that describe the cardinality of `derangements α` when `α` is a fintype.

## Main definitions

* `card_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.
* `numDerangements n`: The number of derangements on an n-element set, defined in a computation-
    friendly way.
* `card_derangements_eq_numDerangements`: Proof that `numDerangements` really does compute the
    number of derangements.
* `numDerangements_sum`: A lemma giving an expression for `numDerangements n` in terms of
    factorials.
-/

@[expose] public section


open derangements Equiv Fintype

variable {α : Type*} [DecidableEq α] [Fintype α]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidablePred (· ∈ derangements α) := fun _ => Fintype.decidableForallFintype
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fintype (derangements α) :=
  inferInstanceAs <| Fintype { f : Perm α | ∀ x : α, f x ≠ x }
/-
**card_derangements_invariant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_derangements_invariant {α β : Type*} [Fintype α] [DecidableEq α] [Fin
type β] [DecidableEq β] (h : card α = card β) : card (derangements α) = card (de
rangements β)
参数：h : card α = card β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem card_derangements_invariant {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (h : card α = card β) : card (derangements α) = card (derangements β) :=
  Fintype.card_congr (Equiv.derangementsCongr <| equivOfCardEq h)
/-
**card_derangements_fin_add_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_derangements_fin_add_two (n : Nat) : card (derangements (Fin (n + 2))
) = (n + 1) * card (derangements (Fin n)) + (n + 1) * card (derangements (Fin (n
 + 1)))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_compl_set`：Fintype.card_compl_set [Fintype α] (s : Set α) [
Fintype s] [Fintype (↥sᶜ : Sort _)] : Fintype.card (↥sᶜ : Sort _) = Fintype.card
 α - Fintype…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.card_option`：Fintype.card_option {α : Type*} [Fintype α] : Finty
pe.card (Option α) = Fintype.card α + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `card_derangements_invariant`：card_derangements_invariant {α β : Type*} [
Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (h : card α = card β) : c
ard (derangements…
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem card_derangements_fin_add_two (n : ℕ) :
    card (derangements (Fin (n + 2))) =
      (n + 1) * card (derangements (Fin n)) + (n + 1) * card (derangements (Fin (n + 1))) := by
  -- get some basic results about the size of Fin (n+1) plus or minus an element
  have h1 : ∀ a : Fin (n + 1), card ({a}ᶜ : Set (Fin (n + 1))) = card (Fin n) := by
    intro a
    rw [Fintype.card_compl_set]
    simp
  have h2 : card (Fin (n + 2)) = card (Option (Fin (n + 1))) := by simp only [card_fin, card_option]
  -- rewrite the LHS and substitute in our fintype-level equivalence
  simp only [card_derangements_invariant h2,
    card_congr
      (@derangementsRecursionEquiv (Fin (n + 1))
        _), -- push the cardinality through the Σ and ⊕ so that we can use `card_n`
    card_sigma,
    card_sum, card_derangements_invariant (h1 _), Finset.sum_const, nsmul_eq_mul, Finset.card_fin,
    mul_add, Nat.cast_id]

/-- The number of derangements of an `n`-element set. -/
/-
**numDerangements** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of derangements of an `n`-element set.
-/
def numDerangements : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (numDerangements n + numDerangements (n + 1))

@[simp]
/-
**numDerangements_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：numDerangements_zero : numDerangements 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem numDerangements_zero : numDerangements 0 = 1 :=
  rfl

@[simp]
/-
**numDerangements_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：numDerangements_one : numDerangements 1 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem numDerangements_one : numDerangements 1 = 0 :=
  rfl
/-
**numDerangements_add_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：numDerangements_add_two (n : Nat) : numDerangements (n + 2) = (n + 1) * (n
umDerangements n + numDerangements (n + 1))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem numDerangements_add_two (n : ℕ) :
    numDerangements (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1)) :=
  rfl
/-
**numDerangements_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：numDerangements_succ (n : Nat) : (numDerangements (n + 1) : Int) = (n + 1)
 * (numDerangements n : Int) - (-1) ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 46 条，此处仅展示前 30 条）
-/
theorem numDerangements_succ (n : ℕ) :
    (numDerangements (n + 1) : ℤ) = (n + 1) * (numDerangements n : ℤ) - (-1) ^ n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    simp only [numDerangements_add_two, hn, pow_succ, Int.natCast_mul, Int.natCast_add]
    ring
/-
**card_derangements_fin_eq_numDerangements** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_derangements_fin_eq_numDerangements {n : Nat} : card (derangements (F
in n)) = numDerangements n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `numDerangements_add_two`：numDerangements_add_two (n : Nat) : numDerangem
ents (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1))
· 使用定理 `card_derangements_fin_add_two`：card_derangements_fin_add_two (n : Nat) :
 card (derangements (Fin (n + 2))) = (n + 1) * card (derangements (Fin n)) + (n 
+ 1) * card (derang…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem card_derangements_fin_eq_numDerangements {n : ℕ} :
    card (derangements (Fin n)) = numDerangements n := by
  induction n using Nat.strongRecOn with | ind n hyp => _
  rcases n with _ | _ | n
  -- knock out cases 0 and 1
  · rfl
  · rfl
  -- now we have n ≥ 2. rewrite everything in terms of card_derangements, so that we can use
  -- `card_derangements_fin_add_two`
  rw [numDerangements_add_two, card_derangements_fin_add_two, mul_add, hyp, hyp] <;> lia
/-
**card_derangements_eq_numDerangements** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_derangements_eq_numDerangements (α : Type*) [Fintype α] [DecidableEq 
α] : card (derangements α) = numDerangements (card α)
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `card_derangements_invariant`：card_derangements_invariant {α β : Type*} [
Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (h : card α = card β) : c
ard (derangements…
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `card_derangements_fin_eq_numDerangements`：card_derangements_fin_eq_numDe
rangements {n : Nat} : card (derangements (Fin n)) = numDerangements n
-/
theorem card_derangements_eq_numDerangements (α : Type*) [Fintype α] [DecidableEq α] :
    card (derangements α) = numDerangements (card α) := by
  rw [← card_derangements_invariant (card_fin _)]
  exact card_derangements_fin_eq_numDerangements
/-
**numDerangements_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：numDerangements_sum (n : Nat) : (numDerangements n : Int) = ∑ k in Finset.
range (n + 1), (-1 : Int) ^ k * Nat.ascFactorial (k + 1) (n - k)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `numDerangements_succ`：numDerangements_succ (n : Nat) : (numDerangements 
(n + 1) : Int) = (n + 1) * (numDerangements n : Int) - (-1) ^ n
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Nat.ascFactorial_zero`：ascFactorial_zero (n : Nat) : n.ascFactorial 0 = 
1
· 使用定理 `Int.ofNat_one`：↑1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
· 使用定理 `Nat.succ_sub`：∀ {m n : ℕ}, n ≤ m → m.succ - n = (m - n).succ
· 使用定理 `Nat.ascFactorial_succ`：ascFactorial_succ {n k : Nat} : n.ascFactorial k.
succ = (n + k) * n.ascFactorial k
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem numDerangements_sum (n : ℕ) :
    (numDerangements n : ℤ) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * Nat.ascFactorial (k + 1) (n - k) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Finset.sum_range_succ, numDerangements_succ, hn, Finset.mul_sum, tsub_self,
      Nat.ascFactorial_zero, Int.ofNat_one, mul_one, pow_succ', neg_one_mul, sub_eq_add_neg,
      add_left_inj, Finset.sum_congr rfl]
    -- show that (n + 1) * (-1)^x * asc_fac x (n - x) = (-1)^x * asc_fac x (n.succ - x)
    intro x hx
    have h_le : x ≤ n := Finset.mem_range_succ_iff.mp hx
    rw [Nat.succ_sub h_le, Nat.ascFactorial_succ, add_right_comm, add_tsub_cancel_of_le h_le,
      Int.natCast_mul, Int.natCast_add, mul_left_comm, Nat.cast_one]
