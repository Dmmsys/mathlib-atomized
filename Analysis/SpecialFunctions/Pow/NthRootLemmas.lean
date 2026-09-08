/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Zify
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# Lemmas about `Nat.nthRoot`

In this file we prove that `Nat.nthRoot n a` is indeed the floor of `ⁿ√a`.
-/

public section

namespace Nat

variable {m n a b guess fuel : ℕ}

/-
**Nat.nthRoot_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a : ℕ), Nat.nthRoot 0 a = 1
参数：a : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem nthRoot_zero_left (a : ℕ) : nthRoot 0 a = 1 := rfl
/-
**Nat.nthRoot_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.nthRoot 1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem nthRoot_one_left : nthRoot 1 = id := rfl

@[simp]
/-
**Nat.nthRoot_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nthRoot_zero_right (h : n != 0) : nthRoot n 0 = 0
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nthRoot_zero_right (h : n ≠ 0) : nthRoot n 0 = 0 := by
  rcases n with _ | _ | _ <;> grind [nthRoot, nthRoot.go]

@[simp]
/-
**Nat.nthRoot_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nthRoot_one_right : nthRoot n 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem nthRoot_one_right : nthRoot n 1 = 1 := by
  rcases n with _ | _ | _ <;> simp [nthRoot, nthRoot.go, Nat.add_comm 1]
/-
**Nat.nthRoot.pow_go_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem nthRoot.pow_go_le (hle : guess ≤ fuel) (n a : ℕ) :
    go n a fuel guess ^ (n + 2) ≤ a := by
  induction fuel generalizing guess with
  | zero =>
    obtain rfl : guess = 0 := by grind
    simp [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      grind
    case neg =>
      have : guess ≤ a / guess ^ (n + 1) := by
        linarith only [Nat.mul_le_of_le_div _ _ _ (not_lt.1 h)]
      replace := Nat.mul_le_of_le_div _ _ _ this
      grind

/-- `nthRoot n a ^ n ≤ a` unless both `n` and `a` are zeros. -/
@[simp]
/-
**Nat.pow_nthRoot_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_nthRoot_le_iff : nthRoot n a ^ n <= a ↔ n != 0 ∨ a != 0
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
`nthRoot n a ^ n ≤ a` unless both `n` and `a` are zeros.
-/
theorem pow_nthRoot_le_iff : nthRoot n a ^ n ≤ a ↔ n ≠ 0 ∨ a ≠ 0 := by
  rcases n with _ | _ | _ <;> first | grind | simp [nthRoot, nthRoot.pow_go_le]

alias ⟨_, pow_nthRoot_le⟩ := pow_nthRoot_le_iff
/-
**Nat.nthRoot.lt_pow_go_succ_aux0** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem nthRoot.lt_pow_go_succ_aux0 (hb : b ≠ 0) :
    a ≤ ((a ^ (n + 1) / b ^ n) + n * b) / (n + 1) := by
  rw [Nat.le_div_iff_mul_le (by positivity), Nat.mul_comm,
    ← Nat.add_mul_div_right _ _ (by positivity),
    Nat.le_div_iff_mul_le (by positivity)]
  #adaptation_note /-- Prior to nightly-2026-04-06, this was
  ```
  have := (Commute.all (b : ℤ) (a - b)).pow_add_mul_le_add_pow_of_sq_nonneg
    (by positivity) (sq_nonneg _) (sq_nonneg _) (by grind) (n + 1)
  grind
  ```
  -/
  zify
  have h := pow_add_mul_le_add_pow_of_sq_nonneg (a := (b : ℤ)) (b := (a : ℤ) - b)
    (ha := by positivity) (Hsq := by positivity) (Hsq' := by positivity) (H := by omega)
    (n := n + 1)
  rw [← sub_nonneg] at h ⊢
  convert! h using 1
  rw [pow_succ]; push_cast; ring1
/-
**Nat.nthRoot.always_exists** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem nthRoot.always_exists (n a : ℕ) :
    ∃ c, c ^ (n + 1) ≤ a ∧ a < (c + 1) ^ (n + 1) := by
  have H : ∃ c, a < (c + 1) ^ (n + 1) := ⟨a, Nat.le_self_pow (by positivity) (a + 1)⟩
  let +nondep (eq := hc) c := Nat.find H
  refine ⟨c, ?_, hc ▸ Nat.find_spec H⟩
  cases c with
  | zero => simp
  | succ k => simpa using Nat.find_min H hc.le

/--
An auxiliary lemma saying that if `b ≠ 0`,
then `(a / b ^ n + n * b) / (n + 1) + 1` is a strict upper estimate on `√[n + 1] a`.
-/
/-
**Nat.nthRoot.lt_pow_go_succ_aux** 是 Mathlib 中的一个定理，位于命名空间 `Nat.nthRoot`。
形式化陈述：∀ {n a b : ℕ}, b ≠ 0 → a < ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1)
参数：(a / b ^ n + n * b) / (n + 1) + 1；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas.0.Nat.nthRo
ot.always_exists`：∀ (n a : ℕ), ∃ c, c ^ (n + 1) ≤ a ∧ a < (c + 1) ^ (n + 1)
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas.0.Nat.nthRo
ot.lt_pow_go_succ_aux0`：∀ {n a b : ℕ}, b ≠ 0 → a ≤ (a ^ (n + 1) / b ^ n + n * b)
 / (n + 1)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.div_le_div_right`：∀ {a b c : ℕ}, a ≤ b → a / c ≤ b / c

--- 原说明 ---
An auxiliary lemma saying that if `b ≠ 0`,
then `(a / b ^ n + n * b) / (n + 1) + 1` is a strict upper estimate on `√[n + 1]
 a`.
-/
theorem nthRoot.lt_pow_go_succ_aux (hb : b ≠ 0) :
     a < ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
  have ⟨c, hc1, hc2⟩ := nthRoot.always_exists n a
  calc a < (c + 1) ^ (n + 1) := hc2
    _ ≤ ((c ^ (n + 1) / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
      gcongr
      exact nthRoot.lt_pow_go_succ_aux0 hb
    _ ≤ ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
      gcongr
/-
**Nat.nthRoot.lt_pow_go_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem nthRoot.lt_pow_go_succ (hlt : a < (guess + 1) ^ (n + 2)) :
    a < (go n a fuel guess + 1) ^ (n + 2) := by
  induction fuel generalizing guess with
  | zero => simpa [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      rcases eq_or_ne guess 0 with rfl | hguess
      · grind
      · exact ih <| Nat.nthRoot.lt_pow_go_succ_aux hguess
    case neg =>
      assumption
/-
**Nat.lt_pow_nthRoot_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_pow_nthRoot_add_one (hn : n != 0) (a : Nat) : a < (nthRoot n a + 1) ^ n
参数：hn : n != 0；a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
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
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas.0.Nat.nthRo
ot.lt_pow_go_succ`：∀ {n a guess fuel : ℕ}, a < (guess + 1) ^ (n + 2) → a < (Nat.
nthRoot.go n a fuel guess + 1) ^ (n + 2)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.le_self_pow`：∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
-/
theorem lt_pow_nthRoot_add_one (hn : n ≠ 0) (a : ℕ) : a < (nthRoot n a + 1) ^ n := by
  match n, hn with
  | 1, _ => simp
  | n + 2, hn =>
    simp only [nthRoot]
    apply nthRoot.lt_pow_go_succ
    exact a.lt_succ_self.trans_le (Nat.le_self_pow hn _)

@[simp]
/-
**Nat.le_nthRoot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_nthRoot_iff (hn : n != 0) : a <= nthRoot n b ↔ a ^ n <= b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `Nat.pow_nthRoot_le`：∀ {n a : ℕ}, n ≠ 0 ∨ a ≠ 0 → n.nthRoot a ^ n ≤ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.lt_pow_nthRoot_add_one`：lt_pow_nthRoot_add_one (hn : n != 0) (a : Na
t) : a < (nthRoot n a + 1) ^ n
-/
theorem le_nthRoot_iff (hn : n ≠ 0) : a ≤ nthRoot n b ↔ a ^ n ≤ b := by
  cases le_or_gt a (nthRoot n b) with
  | inl hle =>
    simp only [hle, true_iff]
    refine le_trans ?_ (pow_nthRoot_le (.inl hn))
    gcongr
  | inr hlt =>
    simp only [hlt.not_ge, false_iff, not_le]
    refine (lt_pow_nthRoot_add_one hn b).trans_le ?_
    gcongr
    assumption

@[simp]
/-
**Nat.nthRoot_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nthRoot_lt_iff (hn : n != 0) : nthRoot n a < b ↔ a < b ^ n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_nthRoot_iff`：le_nthRoot_iff (hn : n != 0) : a <= nthRoot n b ↔ a 
^ n <= b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nthRoot_lt_iff (hn : n ≠ 0) : nthRoot n a < b ↔ a < b ^ n := by
  simp only [← not_le, le_nthRoot_iff hn]

@[simp]
/-
**Nat.nthRoot_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nthRoot_pow (hn : n != 0) (a : Nat) : nthRoot n (a ^ n) = a
参数：hn : n != 0；a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_nthRoot_iff`：le_nthRoot_iff (hn : n != 0) : a <= nthRoot n b ↔ a 
^ n <= b
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Nat.pow_left_strictMono`：∀ {n : ℕ}, n ≠ 0 → StrictMono fun x => x ^ n
-/
theorem nthRoot_pow (hn : n ≠ 0) (a : ℕ) : nthRoot n (a ^ n) = a := by
  refine eq_of_forall_le_iff fun b ↦ ?_
  rw [le_nthRoot_iff hn]
  exact (Nat.pow_left_strictMono hn).le_iff_le

/-- If `a ^ n ≤ b < (a + 1) ^ n`, then `n` root of `b` equals `a`. -/
/-
**Nat.nthRoot_eq_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nthRoot_eq_of_le_of_lt (h₁ : a ^ n <= b) (h₂ : b < (a + 1) ^ n) : nthRoot 
n b = a
参数：h₁ : a ^ n <= b；h₂ : b < (a + 1) ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_nthRoot_iff`：le_nthRoot_iff (hn : n != 0) : a <= nthRoot n b ↔ a 
^ n <= b
· 使用定理 `Nat.nthRoot_lt_iff`：nthRoot_lt_iff (hn : n != 0) : nthRoot n a < b ↔ a <
 b ^ n

--- 原说明 ---
If `a ^ n ≤ b < (a + 1) ^ n`, then `n` root of `b` equals `a`.
-/
theorem nthRoot_eq_of_le_of_lt (h₁ : a ^ n ≤ b) (h₂ : b < (a + 1) ^ n) :
    nthRoot n b = a := by
  rcases eq_or_ne n 0 with rfl | hn
  · grind
  simp only [← le_nthRoot_iff hn, ← nthRoot_lt_iff hn] at h₁ h₂
  grind
/-
**Nat.exists_pow_eq_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_pow_eq_iff' (hn : n != 0) : (exists x, x ^ n = a) ↔ (nthRoot n a) ^
 n = a
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nthRoot_pow`：nthRoot_pow (hn : n != 0) (a : Nat) : nthRoot n (a ^ n)
 = a
-/
theorem exists_pow_eq_iff' (hn : n ≠ 0) : (∃ x, x ^ n = a) ↔ (nthRoot n a) ^ n = a := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [nthRoot_pow hn]
  · grind
/-
**Nat.exists_pow_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_pow_eq_iff : (exists x, x ^ n = a) ↔ ((n = 0 ∧ a = 1) ∨ (n != 0 ∧ (
nthRoot n a) ^ n = a))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_pow_eq_iff :
    (∃ x, x ^ n = a) ↔ ((n = 0 ∧ a = 1) ∨ (n ≠ 0 ∧ (nthRoot n a) ^ n = a)) := by
  rcases eq_or_ne n 0 with rfl | _ <;> grind [exists_pow_eq_iff']
/-
**Nat.instDecidableExistsPowEq** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instDecidableExistsPowEq : Decidable (exists x, x ^ n = a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_pow_eq_iff`：exists_pow_eq_iff : (exists x, x ^ n = a) ↔ ((n =
 0 ∧ a = 1) ∨ (n != 0 ∧ (nthRoot n a) ^ n = a))
-/
instance instDecidableExistsPowEq : Decidable (∃ x, x ^ n = a) :=
  decidable_of_iff' _ exists_pow_eq_iff

end Nat

