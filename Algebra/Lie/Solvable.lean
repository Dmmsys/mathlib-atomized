/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.IdealOperations
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Solvable Lie algebras

Like groups, Lie algebras admit a natural concept of solvability. We define this here via the
derived series and prove some related results. We also define the radical of a Lie algebra and
prove that it is solvable when the Lie algebra is Noetherian.

## Main definitions

  * `LieAlgebra.derivedSeriesOfIdeal`
  * `LieAlgebra.derivedSeries`
  * `LieAlgebra.IsSolvable`
  * `LieAlgebra.isSolvableAdd`
  * `LieAlgebra.radical`
  * `LieAlgebra.radicalIsSolvable`
  * `LieAlgebra.derivedLengthOfIdeal`
  * `LieAlgebra.derivedLength`
  * `LieAlgebra.derivedAbelianOfIdeal`

## Tags

lie algebra, derived series, derived length, solvable, radical
-/

@[expose] public section


universe u v w w₁ w₂

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

namespace LieAlgebra

/-- A generalisation of the derived series of a Lie algebra, whose zeroth term is a specified ideal.

It can be more convenient to work with this generalisation when considering the derived series of
an ideal since it provides a type-theoretic expression of the fact that the terms of the ideal's
derived series are also ideals of the enclosing algebra.

See also `LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap` and
`LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map` below. -/
/-
**LieAlgebra.derivedSeriesOfIdeal** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：derivedSeriesOfIdeal (k : Nat) : LieIdeal R L -> LieIdeal R L
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generalisation of the derived series of a Lie algebra, whose zeroth term is a 
specified ideal.

It can be more convenient to work with this generalisation when considering the 
derived series of
an ideal since it provides a type-theoretic expression of the fact that the term
s of the ideal's
derived series are also ideals of the enclosing algebra.

See also `LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap` and
`LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map` below.
-/
def derivedSeriesOfIdeal (k : ℕ) : LieIdeal R L → LieIdeal R L :=
  (fun I => ⁅I, I⁆)^[k]

@[simp]
/-
**LieAlgebra.derivedSeriesOfIdeal_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：derivedSeriesOfIdeal_zero : derivedSeriesOfIdeal R L 0 I = I
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem derivedSeriesOfIdeal_zero : derivedSeriesOfIdeal R L 0 I = I :=
  rfl

@[simp]
/-
**LieAlgebra.derivedSeriesOfIdeal_succ** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：derivedSeriesOfIdeal_succ (k : Nat) : derivedSeriesOfIdeal R L (k + 1) I =
 ⁅derivedSeriesOfIdeal R L k I, derivedSeriesOfIdeal R L k I⁆
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
-/
theorem derivedSeriesOfIdeal_succ (k : ℕ) :
    derivedSeriesOfIdeal R L (k + 1) I =
      ⁅derivedSeriesOfIdeal R L k I, derivedSeriesOfIdeal R L k I⁆ :=
  Function.iterate_succ_apply' (fun I => ⁅I, I⁆) k I

/-- The derived series of Lie ideals of a Lie algebra. -/
/-
**LieAlgebra.derivedSeries** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieAlgebra`。
形式化陈述：derivedSeries (k : Nat) : LieIdeal R L
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derived series of Lie ideals of a Lie algebra.
-/
abbrev derivedSeries (k : ℕ) : LieIdeal R L :=
  derivedSeriesOfIdeal R L k ⊤
/-
**LieAlgebra.derivedSeries_def** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：derivedSeries_def (k : Nat) : derivedSeries R L k = derivedSeriesOfIdeal R
 L k ⊤
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem derivedSeries_def (k : ℕ) : derivedSeries R L k = derivedSeriesOfIdeal R L k ⊤ :=
  rfl
/-
**LieAlgebra.coe_derivedSeries_one_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：coe_derivedSeries_one_eq : derivedSeries R L 1 = Submodule.span R {⁅x, y⁆ 
| (x : L) (y : L)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_derivedSeries_one_eq :
    derivedSeries R L 1 = Submodule.span R {⁅x, y⁆ | (x : L) (y : L)} := by
  ext z
  simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span']
  aesop

variable {R L}

local notation "D" => derivedSeriesOfIdeal R L
/-
**LieAlgebra.derivedSeriesOfIdeal_add** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：derivedSeriesOfIdeal_add (k l : Nat) : D (k + l) I = D k (D l I)
参数：k l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_zero`：derivedSeriesOfIdeal_zero : derive
dSeriesOfIdeal R L 0 I = I
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
-/
theorem derivedSeriesOfIdeal_add (k l : ℕ) : D (k + l) I = D k (D l I) := by
  induction k with
  | zero => rw [Nat.zero_add, derivedSeriesOfIdeal_zero]
  | succ k ih => rw [Nat.succ_add k l, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, ih]

@[gcongr, mono]
/-
**LieAlgebra.derivedSeriesOfIdeal_le** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：derivedSeriesOfIdeal_le {I J : LieIdeal R L} {k l : Nat} (h₁ : I <= J) (h₂
 : l <= k) : D k I <= D l J
参数：h₁ : I <= J；h₂ : l <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_zero`：derivedSeriesOfIdeal_zero : derive
dSeriesOfIdeal R L 0 I = I
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用定理 `LieSubmodule.mono_lie`：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <=
 ⁅J, N'⁆
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LieSubmodule.lie_le_left`：lie_le_left : ⁅I, J⁆ <= I
-/
theorem derivedSeriesOfIdeal_le {I J : LieIdeal R L} {k l : ℕ} (h₁ : I ≤ J) (h₂ : l ≤ k) :
    D k I ≤ D l J := by
  induction k generalizing l with
  | zero => rw [le_zero_iff] at h₂; rw [h₂, derivedSeriesOfIdeal_zero]; exact h₁
  | succ k ih =>
    have h : l = k.succ ∨ l ≤ k := by rwa [le_iff_eq_or_lt, Nat.lt_succ_iff] at h₂
    rcases h with h | h
    · rw [h, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ]
      exact LieSubmodule.mono_lie (ih (le_refl k)) (ih (le_refl k))
    · rw [derivedSeriesOfIdeal_succ]; exact le_trans (LieSubmodule.lie_le_left _ _) (ih h)
/-
**LieAlgebra.derivedSeriesOfIdeal_succ_le** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`
。
形式化陈述：derivedSeriesOfIdeal_succ_le (k : Nat) : D (k + 1) I <= D k I
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_le`：derivedSeriesOfIdeal_le {I J : LieId
eal R L} {k l : Nat} (h₁ : I <= J) (h₂ : l <= k) : D k I <= D l J
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem derivedSeriesOfIdeal_succ_le (k : ℕ) : D (k + 1) I ≤ D k I :=
  derivedSeriesOfIdeal_le le_rfl k.le_succ
/-
**LieAlgebra.derivedSeriesOfIdeal_le_self** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`
。
形式化陈述：derivedSeriesOfIdeal_le_self (k : Nat) : D k I <= I
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_le`：derivedSeriesOfIdeal_le {I J : LieId
eal R L} {k l : Nat} (h₁ : I <= J) (h₂ : l <= k) : D k I <= D l J
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem derivedSeriesOfIdeal_le_self (k : ℕ) : D k I ≤ I :=
  derivedSeriesOfIdeal_le le_rfl zero_le
/-
**LieAlgebra.derivedSeriesOfIdeal_mono** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：derivedSeriesOfIdeal_mono {I J : LieIdeal R L} (h : I <= J) (k : Nat) : D 
k I <= D k J
参数：h : I <= J；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_le`：derivedSeriesOfIdeal_le {I J : LieId
eal R L} {k l : Nat} (h₁ : I <= J) (h₂ : l <= k) : D k I <= D l J
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem derivedSeriesOfIdeal_mono {I J : LieIdeal R L} (h : I ≤ J) (k : ℕ) : D k I ≤ D k J :=
  derivedSeriesOfIdeal_le h le_rfl
/-
**LieAlgebra.derivedSeriesOfIdeal_antitone** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra
`。
形式化陈述：derivedSeriesOfIdeal_antitone {k l : Nat} (h : l <= k) : D k I <= D l I
参数：h : l <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_le`：derivedSeriesOfIdeal_le {I J : LieId
eal R L} {k l : Nat} (h₁ : I <= J) (h₂ : l <= k) : D k I <= D l J
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem derivedSeriesOfIdeal_antitone {k l : ℕ} (h : l ≤ k) : D k I ≤ D l I :=
  derivedSeriesOfIdeal_le le_rfl h

set_option backward.isDefEq.respectTransparency.types false in
/-
**LieAlgebra.derivedSeriesOfIdeal_add_le_add** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgeb
ra`。
形式化陈述：derivedSeriesOfIdeal_add_le_add (J : LieIdeal R L) (k l : Nat) : D (k + l)
 (I + J) <= D k I + D l J
参数：J : LieIdeal R L；k l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.mono_lie`：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <=
 ⁅J, N'⁆
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lie_sup`：lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieSubmodule.sup_lie`：sup_lie : ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderHom.iterate_sup_le_sup_iff`：iterate_sup_le_sup_iff {α : Type*} [Sem
ilatticeSup α] (f : α ->o α) : (forall n₁ n₂ a₁ a₂, f^[n₁ + n₂] (a₁ ⊔ a₂) <= f^[
n₁] a₁ ⊔ f^[n₂] a₂) ↔…
-/
theorem derivedSeriesOfIdeal_add_le_add (J : LieIdeal R L) (k l : ℕ) :
    D (k + l) (I + J) ≤ D k I + D l J := by
  let D₁ : LieIdeal R L →o LieIdeal R L :=
    { toFun := fun I => ⁅I, I⁆
      monotone' := fun I J h => LieSubmodule.mono_lie h h }
  have h₁ : ∀ I J : LieIdeal R L, D₁ (I ⊔ J) ≤ D₁ I ⊔ J := by
    simp [D₁, LieSubmodule.lie_le_right, LieSubmodule.lie_le_left, le_sup_of_le_right]
  rw [← D₁.iterate_sup_le_sup_iff] at h₁
  exact h₁ k l I J
/-
**LieAlgebra.derivedSeries_of_bot_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：derivedSeries_of_bot_eq_bot (k : Nat) : derivedSeriesOfIdeal R L k ⊥ = ⊥
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_le_self`：derivedSeriesOfIdeal_le_self (k
 : Nat) : D k I <= I
-/
theorem derivedSeries_of_bot_eq_bot (k : ℕ) : derivedSeriesOfIdeal R L k ⊥ = ⊥ := by
  rw [eq_bot_iff]; exact derivedSeriesOfIdeal_le_self ⊥ k
/-
**LieAlgebra.abelian_iff_derived_one_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebr
a`。
形式化陈述：abelian_iff_derived_one_eq_bot : IsLieAbelian I ↔ derivedSeriesOfIdeal R L
 1 I = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_zero`：derivedSeriesOfIdeal_zero : derive
dSeriesOfIdeal R L 0 I = I
· 使用定理 `LieSubmodule.lie_abelian_iff_lie_self_eq_bot`：LieSubmodule.lie_abelian_i
ff_lie_self_eq_bot : IsLieAbelian I ↔ ⁅I, I⁆ = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem abelian_iff_derived_one_eq_bot : IsLieAbelian I ↔ derivedSeriesOfIdeal R L 1 I = ⊥ := by
  rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    LieSubmodule.lie_abelian_iff_lie_self_eq_bot]
/-
**LieAlgebra.abelian_iff_derived_succ_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgeb
ra`。
形式化陈述：abelian_iff_derived_succ_eq_bot (I : LieIdeal R L) (k : Nat) : IsLieAbelia
n (derivedSeriesOfIdeal R L k I) ↔ derivedSeriesOfIdeal R L (k + 1) I = ⊥
参数：I : LieIdeal R L；k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_add`：derivedSeriesOfIdeal_add (k l : Nat
) : D (k + l) I = D k (D l I)
· 使用定理 `LieAlgebra.abelian_iff_derived_one_eq_bot`：abelian_iff_derived_one_eq_bo
t : IsLieAbelian I ↔ derivedSeriesOfIdeal R L 1 I = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem abelian_iff_derived_succ_eq_bot (I : LieIdeal R L) (k : ℕ) :
    IsLieAbelian (derivedSeriesOfIdeal R L k I) ↔ derivedSeriesOfIdeal R L (k + 1) I = ⊥ := by
  rw [add_comm, derivedSeriesOfIdeal_add I 1 k, abelian_iff_derived_one_eq_bot]

open TensorProduct in
/-
**LieAlgebra.derivedSeriesOfIdeal_baseChange** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgeb
ra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] (I : LieIdeal R L)   {A : Type u_1} [inst_3 : CommRing A] [
inst_4 : Algebra R A] (k : ℕ),   LieAlgebra.derivedSeriesOfIdeal A (TensorProduc
t R A L) k (LieSubmodule.baseChange A I) =     LieSubmodule.baseChange A (LieAlg
ebra.derivedSeriesOfIdeal R L k I)
参数：I : LieIdeal R L；k : ℕ；TensorProduct R A L；LieSubmodule.baseChange A I；LieAlg
ebra.derivedSeriesOfIdeal R L k I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用引理 `LieSubmodule.lie_baseChange`：lie_baseChange {I : LieIdeal R L} {N : LieS
ubmodule R L M} : ⁅I, N⁆.baseChange A = ⁅I.baseChange A, N.baseChange A⁆
-/
@[simp] theorem derivedSeriesOfIdeal_baseChange {A : Type*} [CommRing A] [Algebra R A] (k : ℕ) :
    derivedSeriesOfIdeal A (A ⊗[R] L) k (I.baseChange A) =
      (derivedSeriesOfIdeal R L k I).baseChange A := by
  induction k with
  | zero => simp
  | succ k ih => simp only [derivedSeriesOfIdeal_succ, ih, LieSubmodule.lie_baseChange]

open TensorProduct in
/-
**LieAlgebra.derivedSeries_baseChange** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] {A : Type u_1}   [inst_3 : CommRing A] [inst_4 : Algebra R 
A] (k : ℕ),   LieAlgebra.derivedSeries A (TensorProduct R A L) k = LieSubmodule.
baseChange A (LieAlgebra.derivedSeries R L k)
参数：k : ℕ；TensorProduct R A L；LieAlgebra.derivedSeries R L k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.derivedSeries_def`：derivedSeries_def (k : Nat) : derivedSerie
s R L k = derivedSeriesOfIdeal R L k ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_baseChange`：∀ {R : Type u} {L : Type v} 
[inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (I : LieIdeal
 R L)   {A : Type u_1} [inst_3 :…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LieSubmodule.baseChange_top`：baseChange_top : (⊤ : LieSubmodule R L M).b
aseChange A = ⊤
-/
@[simp] theorem derivedSeries_baseChange {A : Type*} [CommRing A] [Algebra R A] (k : ℕ) :
    derivedSeries A (A ⊗[R] L) k = (derivedSeries R L k).baseChange A := by
  rw [derivedSeries_def, derivedSeries_def, ← derivedSeriesOfIdeal_baseChange,
    LieSubmodule.baseChange_top]

end LieAlgebra

namespace LieIdeal

open LieAlgebra

variable {R L}

/-
**LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap** 是 Mathlib 中的一个定理，位于命名空间
 `LieIdeal`。
形式化陈述：derivedSeries_eq_derivedSeriesOfIdeal_comap (k : Nat) : derivedSeries R I 
k = (derivedSeriesOfIdeal R L k I).comap I.incl
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.comap_incl_self`：comap_incl_self : comap I.incl I = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用定理 `LieIdeal.comap_bracket_incl_of_le`：comap_bracket_incl_of_le {I₁ I₂ : Lie
Ideal R L} (h₁ : I₁ <= I) (h₂ : I₂ <= I) : ⁅comap I.incl I₁, comap I.incl I₂⁆ = 
comap I.incl ⁅I₁, I₂⁆
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_le_self`：derivedSeriesOfIdeal_le_self (k
 : Nat) : D k I <= I
-/
theorem derivedSeries_eq_derivedSeriesOfIdeal_comap (k : ℕ) :
    derivedSeries R I k = (derivedSeriesOfIdeal R L k I).comap I.incl := by
  induction k with
  | zero => simp only [derivedSeries_def, comap_incl_self, derivedSeriesOfIdeal_zero]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢; rw [ih]
    exact comap_bracket_incl_of_le I (derivedSeriesOfIdeal_le_self I k)
      (derivedSeriesOfIdeal_le_self I k)
/-
**LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map** 是 Mathlib 中的一个定理，位于命名空间 `
LieIdeal`。
形式化陈述：derivedSeries_eq_derivedSeriesOfIdeal_map (k : Nat) : (derivedSeries R I k
).map I.incl = derivedSeriesOfIdeal R L k I
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap`：derivedSeries_eq_d
erivedSeriesOfIdeal_comap (k : Nat) : derivedSeries R I k = (derivedSeriesOfIdea
l R L k I).comap I.incl
· 使用定理 `LieIdeal.map_comap_incl`：map_comap_incl {I₁ I₂ : LieIdeal R L} : map I₁.
incl (comap I₁.incl I₂) = I₁ ⊓ I₂
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_le_self`：derivedSeriesOfIdeal_le_self (k
 : Nat) : D k I <= I
-/
theorem derivedSeries_eq_derivedSeriesOfIdeal_map (k : ℕ) :
    (derivedSeries R I k).map I.incl = derivedSeriesOfIdeal R L k I := by
  rw [derivedSeries_eq_derivedSeriesOfIdeal_comap, map_comap_incl, inf_eq_right]
  apply derivedSeriesOfIdeal_le_self
/-
**LieIdeal.derivedSeries_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：derivedSeries_eq_bot_iff (k : Nat) : derivedSeries R I k = ⊥ ↔ derivedSeri
esOfIdeal R L k I = ⊥
参数：k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map`：derivedSeries_eq_der
ivedSeriesOfIdeal_map (k : Nat) : (derivedSeries R I k).map I.incl = derivedSeri
esOfIdeal R L k I
· 使用定理 `LieIdeal.map_eq_bot_iff`：map_eq_bot_iff : I.map f = ⊥ ↔ I <= f.ker
· 使用定理 `LieIdeal.ker_incl`：ker_incl : I.incl.ker = ⊥
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem derivedSeries_eq_bot_iff (k : ℕ) :
    derivedSeries R I k = ⊥ ↔ derivedSeriesOfIdeal R L k I = ⊥ := by
  rw [← derivedSeries_eq_derivedSeriesOfIdeal_map, map_eq_bot_iff, ker_incl, eq_bot_iff]
/-
**LieIdeal.derivedSeries_add_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：derivedSeries_add_eq_bot {k l : Nat} {I J : LieIdeal R L} (hI : derivedSer
ies R I k = ⊥) (hJ : derivedSeries R J l = ⊥) : derivedSeries R (I + J) (k + l) 
= ⊥
参数：hI : derivedSeries R I k = ⊥；hJ : derivedSeries R J l = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.derivedSeries_eq_bot_iff`：derivedSeries_eq_bot_iff (k : Nat) : 
derivedSeries R I k = ⊥ ↔ derivedSeriesOfIdeal R L k I = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_add_le_add`：derivedSeriesOfIdeal_add_le_
add (J : LieIdeal R L) (k l : Nat) : D (k + l) (I + J) <= D k I + D l J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
theorem derivedSeries_add_eq_bot {k l : ℕ} {I J : LieIdeal R L} (hI : derivedSeries R I k = ⊥)
    (hJ : derivedSeries R J l = ⊥) : derivedSeries R (I + J) (k + l) = ⊥ := by
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hI hJ ⊢
  rw [← le_bot_iff]
  let D := derivedSeriesOfIdeal R L; change D k I = ⊥ at hI; change D l J = ⊥ at hJ
  calc
    D (k + l) (I + J) ≤ D k I + D l J := derivedSeriesOfIdeal_add_le_add I J k l
    _ ≤ ⊥ := by rw [hI, hJ]; simp
/-
**LieIdeal.derivedSeries_map_le** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：derivedSeries_map_le (k : Nat) : (derivedSeries R L' k).map f <= derivedSe
ries R L k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LieIdeal.map_bracket_le`：map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅
I₁, I₂⁆ <= ⁅map f I₁, map f I₂⁆
· 使用定理 `LieSubmodule.mono_lie`：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <=
 ⁅J, N'⁆
-/
theorem derivedSeries_map_le (k : ℕ) : (derivedSeries R L' k).map f ≤ derivedSeries R L k := by
  induction k with
  | zero => simp only [derivedSeries_def, derivedSeriesOfIdeal_zero, le_top]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢
    exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie ih ih)
/-
**LieIdeal.derivedSeries_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：derivedSeries_map_eq (k : Nat) (h : Function.Surjective f) : (derivedSerie
s R L' k).map f = derivedSeries R L k
参数：k : Nat；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.idealRange_eq_map`：idealRange_eq_map : f.idealRange = LieIdeal.ma
p f ⊤
· 使用定理 `LieHom.idealRange_eq_top_of_surjective`：idealRange_eq_top_of_surjective 
(h : Function.Surjective f) : f.idealRange = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用定理 `LieIdeal.map_bracket_eq`：map_bracket_eq {I₁ I₂ : LieIdeal R L} (h : Func
tion.Surjective f) : map f ⁅I₁, I₂⁆ = ⁅map f I₁, map f I₂⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivedSeries_map_eq (k : ℕ) (h : Function.Surjective f) :
    (derivedSeries R L' k).map f = derivedSeries R L k := by
  induction k with
  | zero =>
    change (⊤ : LieIdeal R L').map f = ⊤
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  | succ k ih => simp only [derivedSeries_def, map_bracket_eq f h, ih, derivedSeriesOfIdeal_succ]
/-
**LieIdeal.derivedSeries_succ_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：derivedSeries_succ_eq_top_iff (n : Nat) : derivedSeries R L (n + 1) = ⊤ ↔ 
derivedSeries R L 1 = ⊤
参数：n : Nat。
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
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `LieSubmodule.lie_le_right`：lie_le_right : ⁅I, N⁆ <= N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem derivedSeries_succ_eq_top_iff (n : ℕ) :
    derivedSeries R L (n + 1) = ⊤ ↔ derivedSeries R L 1 = ⊤ := by
  simp only [derivedSeries_def]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [derivedSeriesOfIdeal_succ]
    refine ⟨fun h ↦ ?_, fun h ↦ by rwa [ih.mpr h]⟩
    rw [← ih, eq_top_iff]
    conv_lhs => rw [← h]
    exact LieSubmodule.lie_le_right _ _
/-
**LieIdeal.derivedSeries_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：derivedSeries_eq_top (n : Nat) (h : derivedSeries R L 1 = ⊤) : derivedSeri
es R L n = ⊤
参数：n : Nat；h : derivedSeries R L 1 = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.derivedSeries_succ_eq_top_iff`：derivedSeries_succ_eq_top_iff (n
 : Nat) : derivedSeries R L (n + 1) = ⊤ ↔ derivedSeries R L 1 = ⊤
-/
theorem derivedSeries_eq_top (n : ℕ) (h : derivedSeries R L 1 = ⊤) :
    derivedSeries R L n = ⊤ := by
  cases n
  · rfl
  · rwa [derivedSeries_succ_eq_top_iff]
/-
**LieIdeal.coe_derivedSeries_eq_int_aux** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coe_derivedSeries_eq_int_aux (R₁ R₂ L : Type*) [CommRing R₁] [CommRing R₂]
    [LieRing L] [LieAlgebra R₁ L] [LieAlgebra R₂ L] (k : ℕ)
    (ih : ∀ (x : L), x ∈ derivedSeriesOfIdeal R₁ L k ⊤ ↔ x ∈ derivedSeriesOfIdeal R₂ L k ⊤) :
    let I := derivedSeriesOfIdeal R₂ L k ⊤; let S : Set L := {⁅a, b⁆ | (a ∈ I) (b ∈ I)}
    (Submodule.span R₁ S : Set L) ≤ (Submodule.span R₂ S : Set L) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | add y z hy₁ hz₁ hy₂ hz₂ => exact Submodule.add_mem _ hy₂ hz₂
  | smul_mem c y hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      rw [← smul_lie]
      refine Submodule.subset_span ⟨c • a, ?_, b, hb, rfl⟩
      rw [← ih] at ha ⊢
      exact Submodule.smul_mem _ _ ha
/-
**LieIdeal.coe_derivedSeries_eq_int** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：coe_derivedSeries_eq_int (k : Nat) : (derivedSeries R L k : Set L) = (deri
vedSeries Int L k : Set L)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.coe_toSubmodule`：coe_toSubmodule : ((N : Submodule R M) : S
et M) = N
· 使用定理 `LieAlgebra.derivedSeries_def`：derivedSeries_def (k : Nat) : derivedSerie
s R L k = derivedSeriesOfIdeal R L k ⊤
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `instLieModuleInt`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1
 : AddCommGroup M] [inst_2 : LieRingModule L M], LieModule ℤ L M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `_private.Mathlib.Algebra.Lie.Solvable.0.LieIdeal.coe_derivedSeries_eq_in
t_aux`：∀ (R₁ : Type u_1) (R₂ : Type u_2) (L : Type u_3) [inst : CommRing R₁] [in
st_1 : CommRing R₂] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R₁ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem coe_derivedSeries_eq_int (k : ℕ) :
    (derivedSeries R L k : Set L) = (derivedSeries ℤ L k : Set L) := by
  rw [← LieSubmodule.coe_toSubmodule, ← LieSubmodule.coe_toSubmodule, derivedSeries_def,
    derivedSeries_def]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.lieIdeal_oper_eq_linear_span']
    rw [Set.ext_iff] at ih
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule] at ih
    simp only [ih]
    apply le_antisymm
    · exact coe_derivedSeries_eq_int_aux _ _ L k ih
    · simp

end LieIdeal

namespace LieAlgebra

/-- A Lie algebra is solvable if its derived series reaches 0 (in a finite number of steps). -/
@[mk_iff isSolvable_iff_int]
/-
**LieAlgebra.IsSolvable** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：(L : Type v) → [LieRing L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie algebra is solvable if its derived series reaches 0 (in a finite number of
 steps).
-/
class IsSolvable : Prop where
  mk_int ::
  solvable_int : ∃ k, derivedSeries ℤ L k = ⊥
/-
**LieAlgebra.isSolvableBot** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
形式化陈述：isSolvableBot : IsSolvable (⊥ : LieIdeal R L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance isSolvableBot : IsSolvable (⊥ : LieIdeal R L) :=
  ⟨⟨0, Subsingleton.elim _ ⊥⟩⟩
/-
**LieAlgebra.isSolvable_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：isSolvable_iff : IsSolvable L ↔ exists k, derivedSeries R L k = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieIdeal.coe_derivedSeries_eq_int`：coe_derivedSeries_eq_int (k : Nat) : 
(derivedSeries R L k : Set L) = (derivedSeries Int L k : Set L)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSolvable_iff : IsSolvable L ↔ ∃ k, derivedSeries R L k = ⊥ := by
  simp [isSolvable_iff_int, SetLike.ext'_iff, LieIdeal.coe_derivedSeries_eq_int]
/-
**LieAlgebra.IsSolvable.solvable** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.IsSolvabl
e`。
形式化陈述：∀ (R : Type u) (L : Type v) [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L]   [LieAlgebra.IsSolvable L], ∃ k, LieAlgebra.derivedSeries 
R L k = ⊥
参数：R : Type u；L : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieAlgebra.isSolvable_iff`：isSolvable_iff : IsSolvable L ↔ exists k, der
ivedSeries R L k = ⊥
-/
lemma IsSolvable.solvable [IsSolvable L] : ∃ k, derivedSeries R L k = ⊥ :=
  (isSolvable_iff R L).mp ‹_›

variable {R L} in
/-
**LieAlgebra.IsSolvable.mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.IsSolvable`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] {k : ℕ},   LieAlgebra.derivedSeries R L k = ⊥ → LieAlgebra.
IsSolvable L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LieAlgebra.isSolvable_iff`：isSolvable_iff : IsSolvable L ↔ exists k, der
ivedSeries R L k = ⊥
-/
lemma IsSolvable.mk {k : ℕ} (h : derivedSeries R L k = ⊥) : IsSolvable L :=
  (isSolvable_iff R L).mpr ⟨k, h⟩
/-
**LieAlgebra.isSolvableAdd** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
形式化陈述：isSolvableAdd {I J : LieIdeal R L} [IsSolvable I] [IsSolvable J] : IsSolva
ble (I + J)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.IsSolvable.solvable`：∀ (R : Type u) (L : Type v) [inst : Comm
Ring R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAlgebra.IsSolvable 
L], ∃ k, LieAlgebra.…
· 使用定理 `LieAlgebra.IsSolvable.mk`：∀ {R : Type u} {L : Type v} [inst : CommRing R
] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {k : ℕ},   LieAlgebra.derivedSe
ries R L k = ⊥…
· 使用定理 `LieIdeal.derivedSeries_add_eq_bot`：derivedSeries_add_eq_bot {k l : Nat} 
{I J : LieIdeal R L} (hI : derivedSeries R I k = ⊥) (hJ : derivedSeries R J l = 
⊥) : derivedSeries R (I…
-/
instance isSolvableAdd {I J : LieIdeal R L} [IsSolvable I] [IsSolvable J] :
    IsSolvable (I + J) := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R I
  obtain ⟨l, hl⟩ := IsSolvable.solvable R J
  exact IsSolvable.mk (LieIdeal.derivedSeries_add_eq_bot hk hl)
/-
**LieAlgebra.derivedSeries_lt_top_of_solvable** 是 Mathlib 中的一个定理，位于命名空间 `LieAlge
bra`。
形式化陈述：derivedSeries_lt_top_of_solvable [IsSolvable L] [Nontrivial L] : derivedSe
ries R L 1 < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.IsSolvable.solvable`：∀ (R : Type u) (L : Type v) [inst : Comm
Ring R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAlgebra.IsSolvable 
L], ∃ k, LieAlgebra.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `LieSubmodule.instNontrivial`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _ro
ot_.Module R M] […
· 使用定理 `LieIdeal.derivedSeries_eq_top`：derivedSeries_eq_top (n : Nat) (h : deriv
edSeries R L 1 = ⊤) : derivedSeries R L n = ⊤
-/
theorem derivedSeries_lt_top_of_solvable [IsSolvable L] [Nontrivial L] :
    derivedSeries R L 1 < ⊤ := by
  obtain ⟨n, hn⟩ := IsSolvable.solvable (R := R) (L := L)
  rw [lt_top_iff_ne_top]
  intro contra
  rw [LieIdeal.derivedSeries_eq_top n contra] at hn
  exact top_ne_bot hn

open TensorProduct in
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [CommRing A] [Algebra R A] [IsSolvable L] : IsSolvable (A ⊗[R] L) := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R L
  rw [isSolvable_iff A]
  use k
  rw [derivedSeries_baseChange, hk, LieSubmodule.baseChange_bot]

open TensorProduct in
variable {A : Type*} [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] in
/-
**LieAlgebra.isSolvable_tensorProduct_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`
。
形式化陈述：isSolvable_tensorProduct_iff : IsSolvable (A otimes[R] L) ↔ IsSolvable L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.isSolvable_iff`：isSolvable_iff : IsSolvable L ↔ exists k, der
ivedSeries R L k = ⊥
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
· 使用定理 `Module.FaithfullyFlat.one_tmul_eq_zero_iff`：one_tmul_eq_zero_iff {A : Ty
pe*} [Ring A] [Algebra R A] [FaithfullyFlat R A] (m : M) : (1 : A) otimesₜ[R] m 
= 0 ↔ m = 0
· 使用定理 `LieAlgebra.derivedSeries_baseChange`：∀ {R : Type u} {L : Type v} [inst :
 CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {A : Type u_1}   [in
st_3 : CommRing A] [inst_…
· 使用引理 `Submodule.tmul_mem_baseChange_of_mem`：tmul_mem_baseChange_of_mem (a : A)
 {m : M} (hm : m in p) : a otimesₜ[R] m in p.baseChange A
· 使用定理 `LieAlgebra.instIsSolvableTensorProduct`：∀ (R : Type u) (L : Type v) [ins
t : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {A : Type u_1}   
[inst_3 : CommRing A] [inst_…
-/
theorem isSolvable_tensorProduct_iff : IsSolvable (A ⊗[R] L) ↔ IsSolvable L := by
  refine ⟨?_, fun _ ↦ inferInstance⟩
  rw [isSolvable_iff A, isSolvable_iff R]
  rintro ⟨k, h⟩
  use k
  rw [eq_bot_iff] at h ⊢
  intro x hx
  rw [derivedSeries_baseChange] at h
  specialize h <| Submodule.tmul_mem_baseChange_of_mem 1 hx
  rw [LieSubmodule.mem_bot] at h ⊢
  rwa [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h

end LieAlgebra

variable {R L}

namespace Function

open LieAlgebra

/-
**Function.Injective.lieAlgebra_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 `Function.I
njective`。
形式化陈述：∀ {R : Type u} {L : Type v} {L' : Type w₁} [inst : CommRing R] [inst_1 : L
ieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing L'] [inst_4 : LieAlgebra
 R L'] {f : L' →ₗ⁅R⁆ L} [hL : LieAlgebra.IsSolvable L],   Function.Injective ⇑f 
→ LieAlgebra.IsSolvable L'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.isSolvable_iff`：isSolvable_iff : IsSolvable L ↔ exists k, der
ivedSeries R L k = ⊥
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LieIdeal.bot_of_map_eq_bot`：bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : F
unction.Injective f) (h₂ : I.map f = ⊥) : I = ⊥
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.derivedSeries_map_le`：derivedSeries_map_le (k : Nat) : (derived
Series R L' k).map f <= derivedSeries R L k
-/
theorem Injective.lieAlgebra_isSolvable [hL : IsSolvable L] (h : Injective f) :
    IsSolvable L' := by
  rw [isSolvable_iff R] at hL ⊢
  apply hL.imp
  intro k hk
  apply LieIdeal.bot_of_map_eq_bot h; rw [eq_bot_iff, ← hk]
  apply LieIdeal.derivedSeries_map_le
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : LieIdeal R L) [IsSolvable L] : IsSolvable A :=
  A.incl_injective.lieAlgebra_isSolvable
/-
**Function.Surjective.lieAlgebra_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 `Function.
Surjective`。
形式化陈述：∀ {R : Type u} {L : Type v} {L' : Type w₁} [inst : CommRing R] [inst_1 : L
ieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing L'] [inst_4 : LieAlgebra
 R L'] {f : L' →ₗ⁅R⁆ L} [hL' : LieAlgebra.IsSolvable L'],   Function.Surjective 
⇑f → LieAlgebra.IsSolvable L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.isSolvable_iff`：isSolvable_iff : IsSolvable L ↔ exists k, der
ivedSeries R L k = ⊥
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.derivedSeries_map_eq`：derivedSeries_map_eq (k : Nat) (h : Funct
ion.Surjective f) : (derivedSeries R L' k).map f = derivedSeries R L k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Surjective.lieAlgebra_isSolvable [hL' : IsSolvable L'] (h : Surjective f) :
    IsSolvable L := by
  rw [isSolvable_iff R] at hL' ⊢
  apply hL'.imp
  intro k hk
  rw [← LieIdeal.derivedSeries_map_eq k h, hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]

end Function

/-
**LieHom.isSolvable_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieHom.isSolvable_range (f : L' ->ₗ⁅R⁆ L) [LieAlgebra.IsSolvable L'] : Lie
Algebra.IsSolvable f.range
参数：f : L' ->ₗ⁅R⁆ L。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.lieAlgebra_isSolvable`：∀ {R : Type u} {L : Type v} {
L' : Type w₁} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]
   [inst_3 : LieRing L'] [inst_…
· 使用定理 `LieHom.surjective_rangeRestrict`：surjective_rangeRestrict : Function.Sur
jective f.rangeRestrict
-/
instance LieHom.isSolvable_range (f : L' →ₗ⁅R⁆ L) [LieAlgebra.IsSolvable L'] :
    LieAlgebra.IsSolvable f.range :=
  f.surjective_rangeRestrict.lieAlgebra_isSolvable

namespace LieAlgebra

/-
**LieAlgebra.solvable_iff_equiv_solvable** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：solvable_iff_equiv_solvable (e : L' ≃ₗ⁅R⁆ L) : IsSolvable L' ↔ IsSolvable 
L
参数：e : L' ≃ₗ⁅R⁆ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.lieAlgebra_isSolvable`：∀ {R : Type u} {L : Type v} {L
' : Type w₁} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] 
  [inst_3 : LieRing L'] [inst_…
· 使用定理 `LieEquiv.injective`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [inst : C
ommRing R] [inst_1 : LieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : LieAlgebra R 
L₁] [ins…
-/
theorem solvable_iff_equiv_solvable (e : L' ≃ₗ⁅R⁆ L) : IsSolvable L' ↔ IsSolvable L := by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isSolvable
  · exact e.injective.lieAlgebra_isSolvable
/-
**LieAlgebra.le_solvable_ideal_solvable** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：le_solvable_ideal_solvable {I J : LieIdeal R L} (h₁ : I <= J) (_ : IsSolva
ble J) : IsSolvable I
参数：h₁ : I <= J；_ : IsSolvable J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.lieAlgebra_isSolvable`：∀ {R : Type u} {L : Type v} {L
' : Type w₁} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] 
  [inst_3 : LieRing L'] [inst_…
· 使用定理 `LieIdeal.inclusion_injective`：inclusion_injective {I₁ I₂ : LieIdeal R L}
 (h : I₁ <= I₂) : Function.Injective (inclusion h)
-/
theorem le_solvable_ideal_solvable {I J : LieIdeal R L} (h₁ : I ≤ J) (_ : IsSolvable J) :
    IsSolvable I :=
  (LieIdeal.inclusion_injective h₁).lieAlgebra_isSolvable

variable (R L)
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ofAbelianIsSolvable [IsLieAbelian L] : IsSolvable L := by
  use 1
  rw [← abelian_iff_derived_one_eq_bot, lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv]
  infer_instance

/-- The (solvable) radical of Lie algebra is the `sSup` of all solvable ideals. -/
/-
**LieAlgebra.radical** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：radical
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (solvable) radical of Lie algebra is the `sSup` of all solvable ideals.
-/
def radical :=
  sSup { I : LieIdeal R L | IsSolvable I }

/-- The radical of a Noetherian Lie algebra is solvable. -/
/-
**LieAlgebra.radicalIsSolvable** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
形式化陈述：radicalIsSolvable [IsNoetherian R L] : IsSolvable (radical R L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CompleteLattice.isSupClosedCompact_iff_wellFoundedGT`：isSupClosedCompact
_iff_wellFoundedGT : IsSupClosedCompact α ↔ WellFoundedGT α
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x

--- 原说明 ---
The radical of a Noetherian Lie algebra is solvable.
-/
instance radicalIsSolvable [IsNoetherian R L] : IsSolvable (radical R L) := by
  have hwf := LieSubmodule.wellFoundedGT_of_noetherian R L L
  rw [← CompleteLattice.isSupClosedCompact_iff_wellFoundedGT] at hwf
  refine hwf { I : LieIdeal R L | IsSolvable I } ⟨⊥, ?_⟩ fun I hI J hJ => ?_
  · exact LieAlgebra.isSolvableBot R L
  · rw [Set.mem_ofPred_eq] at hI hJ ⊢
    apply LieAlgebra.isSolvableAdd R L

/-- The `→` direction of this lemma is actually true without the `IsNoetherian` assumption. -/
/-
**LieAlgebra.LieIdeal.solvable_iff_le_radical** 是 Mathlib 中的一个定理，位于命名空间 `LieAlge
bra.LieIdeal`。
形式化陈述：∀ (R : Type u) (L : Type v) [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] [IsNoetherian R L]   (I : LieIdeal R L), LieAlgebra.IsSolva
ble ↥I ↔ I ≤ LieAlgebra.radical R L
参数：R : Type u；L : Type v；I : LieIdeal R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `LieAlgebra.le_solvable_ideal_solvable`：le_solvable_ideal_solvable {I J :
 LieIdeal R L} (h₁ : I <= J) (_ : IsSolvable J) : IsSolvable I

--- 原说明 ---
The `→` direction of this lemma is actually true without the `IsNoetherian` assu
mption.
-/
theorem LieIdeal.solvable_iff_le_radical [IsNoetherian R L] (I : LieIdeal R L) :
    IsSolvable I ↔ I ≤ radical R L :=
  ⟨fun h => le_sSup h, fun h => le_solvable_ideal_solvable h inferInstance⟩
/-
**LieAlgebra.center_le_radical** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：center_le_radical : center R L <= radical R L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.ofAbelianIsSolvable`：∀ (L : Type v) [inst : LieRing L] [IsLie
Abelian L], LieAlgebra.IsSolvable L
· 使用定理 `LieAlgebra.instIsLieAbelianSubtypeMemLieIdealCenter`：∀ (R : Type u) (L :
 Type v) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   I
sLieAbelian ↥(LieAlgebra.center R L)
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem center_le_radical : center R L ≤ radical R L :=
  have h : IsSolvable (center R L) := inferInstance
  le_sSup h
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSolvable L] : IsSolvable (⊤ : LieSubalgebra R L) := by
  rwa [solvable_iff_equiv_solvable LieSubalgebra.topEquiv]
/-
**LieAlgebra.radical_eq_top_of_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`
。
形式化陈述：∀ (R : Type u) (L : Type v) [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L]   [LieAlgebra.IsSolvable L], LieAlgebra.radical R L = ⊤
参数：R : Type u；L : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `LieAlgebra.instIsSolvableSubtypeMemLieSubalgebraTop`：∀ (R : Type u) (L :
 Type v) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [L
ieAlgebra.IsSolvable L], LieAlgebra.IsSol…
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
@[simp] lemma radical_eq_top_of_isSolvable [IsSolvable L] :
    radical R L = ⊤ := by
  rw [eq_top_iff]
  have h : IsSolvable (⊤ : LieSubalgebra R L) := inferInstance
  exact le_sSup h

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
natural number `k` (the number of inclusions).

For a non-solvable ideal, the value is 0. -/
/-
**LieAlgebra.derivedLengthOfIdeal** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：derivedLengthOfIdeal (I : LieIdeal R L) : Nat
参数：I : LieIdeal R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, t
his is the
natural number `k` (the number of inclusions).

For a non-solvable ideal, the value is 0.
-/
noncomputable def derivedLengthOfIdeal (I : LieIdeal R L) : ℕ :=
  sInf { k | derivedSeriesOfIdeal R L k I = ⊥ }

/-- The derived length of a Lie algebra is the derived length of its 'top' Lie ideal.

See also `LieAlgebra.derivedLength_eq_derivedLengthOfIdeal`. -/
/-
**LieAlgebra.derivedLength** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieAlgebra`。
形式化陈述：derivedLength : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derived length of a Lie algebra is the derived length of its 'top' Lie ideal
.

See also `LieAlgebra.derivedLength_eq_derivedLengthOfIdeal`.
-/
noncomputable abbrev derivedLength : ℕ :=
  derivedLengthOfIdeal R L ⊤
/-
**LieAlgebra.derivedSeries_of_derivedLength_succ** 是 Mathlib 中的一个定理，位于命名空间 `LieA
lgebra`。
形式化陈述：derivedSeries_of_derivedLength_succ (I : LieIdeal R L) (k : Nat) : derived
LengthOfIdeal R L I = k + 1 ↔ IsLieAbelian (derivedSeriesOfIdeal R L k I) ∧ deri
vedSeriesOfIdeal R L k I != ⊥
参数：I : LieIdeal R L；k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.abelian_iff_derived_succ_eq_bot`：abelian_iff_derived_succ_eq_
bot (I : LieIdeal R L) (k : Nat) : IsLieAbelian (derivedSeriesOfIdeal R L k I) ↔
 derivedSeriesOfIdeal R L (k + 1…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_antitone`：derivedSeriesOfIdeal_antitone 
{k l : Nat} (h : l <= k) : D k I <= D l I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Nat.sInf_upward_closed_eq_succ_iff`：sInf_upward_closed_eq_succ_iff {s : 
Set Nat} (hs : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s) (k : Nat) : s
Inf s = k + 1 ↔ k + 1 in…
-/
theorem derivedSeries_of_derivedLength_succ (I : LieIdeal R L) (k : ℕ) :
    derivedLengthOfIdeal R L I = k + 1 ↔
      IsLieAbelian (derivedSeriesOfIdeal R L k I) ∧ derivedSeriesOfIdeal R L k I ≠ ⊥ := by
  rw [abelian_iff_derived_succ_eq_bot]
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s
  have hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := by
    intro k₁ k₂ h₁₂ h₁
    suffices derivedSeriesOfIdeal R L k₂ I ≤ ⊥ by exact eq_bot_iff.mpr this
    change derivedSeriesOfIdeal R L k₁ I = ⊥ at h₁; rw [← h₁]
    exact derivedSeriesOfIdeal_antitone I h₁₂
  exact Nat.sInf_upward_closed_eq_succ_iff hs k
/-
**LieAlgebra.derivedLength_eq_derivedLengthOfIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Li
eAlgebra`。
形式化陈述：derivedLength_eq_derivedLengthOfIdeal (I : LieIdeal R L) : derivedLength R
 I = derivedLengthOfIdeal R L I
参数：I : LieIdeal R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `LieIdeal.derivedSeries_eq_bot_iff`：derivedSeries_eq_bot_iff (k : Nat) : 
derivedSeries R I k = ⊥ ↔ derivedSeriesOfIdeal R L k I = ⊥
-/
theorem derivedLength_eq_derivedLengthOfIdeal (I : LieIdeal R L) :
    derivedLength R I = derivedLengthOfIdeal R L I := by
  let s₁ := { k | derivedSeries R I k = ⊥ }
  let s₂ := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s₁ = sInf s₂
  congr; ext k; exact I.derivedSeries_eq_bot_iff k

variable {R L}

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
`k-1`th term in the derived series (and is therefore an Abelian ideal contained in `I`).

For a non-solvable ideal, this is the zero ideal, `⊥`. -/
/-
**LieAlgebra.derivedAbelianOfIdeal** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：derivedAbelianOfIdeal (I : LieIdeal R L) : LieIdeal R L
参数：I : LieIdeal R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, t
his is the
`k-1`th term in the derived series (and is therefore an Abelian ideal contained 
in `I`).

For a non-solvable ideal, this is the zero ideal, `⊥`.
-/
noncomputable def derivedAbelianOfIdeal (I : LieIdeal R L) : LieIdeal R L :=
  match derivedLengthOfIdeal R L I with
  | 0 => ⊥
  | k + 1 => derivedSeriesOfIdeal R L k I
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique {x // x ∈ (⊥ : LieIdeal R L)} :=
  inferInstanceAs <| Unique {x // x ∈ (⊥ : Submodule R L)}
/-
**LieAlgebra.abelian_derivedAbelianOfIdeal** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra
`。
形式化陈述：abelian_derivedAbelianOfIdeal (I : LieIdeal R L) : IsLieAbelian (derivedAb
elianOfIdeal I)
参数：I : LieIdeal R L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.derivedSeries_of_derivedLength_succ`：derivedSeries_of_derived
Length_succ (I : LieIdeal R L) (k : Nat) : derivedLengthOfIdeal R L I = k + 1 ↔ 
IsLieAbelian (derivedSeriesOfIdeal R…
-/
theorem abelian_derivedAbelianOfIdeal (I : LieIdeal R L) :
    IsLieAbelian (derivedAbelianOfIdeal I) := by
  dsimp +instances only [derivedAbelianOfIdeal]
  rcases h : derivedLengthOfIdeal R L I with - | k
  · dsimp; infer_instance
  · rw [derivedSeries_of_derivedLength_succ] at h; exact h.1
/-
**LieAlgebra.derivedLength_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：derivedLength_zero (I : LieIdeal R L) [IsSolvable I] : derivedLengthOfIdea
l R L I = 0 ↔ I = ⊥
参数：I : LieIdeal R L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.IsSolvable.solvable`：∀ (R : Type u) (L : Type v) [inst : Comm
Ring R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAlgebra.IsSolvable 
L], ∃ k, LieAlgebra.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.derivedSeries_eq_bot_iff`：derivedSeries_eq_bot_iff (k : Nat) : 
derivedSeries R I k = ⊥ ↔ derivedSeriesOfIdeal R L k I = ⊥
· 使用定理 `LieAlgebra.derivedSeries_def`：derivedSeries_def (k : Nat) : derivedSerie
s R L k = derivedSeriesOfIdeal R L k ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem derivedLength_zero (I : LieIdeal R L) [IsSolvable I] :
    derivedLengthOfIdeal R L I = 0 ↔ I = ⊥ := by
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = 0 ↔ _
  have hne : s.Nonempty :=
    have ⟨k, hk⟩ := IsSolvable.solvable R I
    ⟨k, by rwa [derivedSeries_def, LieIdeal.derivedSeries_eq_bot_iff] at hk⟩
  simp [s, hne.ne_empty]
/-
**LieAlgebra.abelian_of_solvable_ideal_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Algebra`。
形式化陈述：abelian_of_solvable_ideal_eq_bot_iff (I : LieIdeal R L) [h : IsSolvable I]
 : derivedAbelianOfIdeal I = ⊥ ↔ I = ⊥
参数：I : LieIdeal R L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieAlgebra.derivedSeries_of_derivedLength_succ`：derivedSeries_of_derived
Length_succ (I : LieIdeal R L) (k : Nat) : derivedLengthOfIdeal R L I = k + 1 ↔ 
IsLieAbelian (derivedSeriesOfIdeal R…
· 使用定理 `LieAlgebra.derivedSeries_of_bot_eq_bot`：derivedSeries_of_bot_eq_bot (k :
 Nat) : derivedSeriesOfIdeal R L k ⊥ = ⊥
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem abelian_of_solvable_ideal_eq_bot_iff (I : LieIdeal R L) [h : IsSolvable I] :
    derivedAbelianOfIdeal I = ⊥ ↔ I = ⊥ := by
  dsimp only [derivedAbelianOfIdeal]
  split
  · simp_all only [derivedLength_zero]
  · rename_i k h
    obtain ⟨_, h₂⟩ := (derivedSeries_of_derivedLength_succ R L I k).mp h
    have h₃ : I ≠ ⊥ := by rintro rfl; apply h₂; apply derivedSeries_of_bot_eq_bot
    simp only [h₂, h₃]

end LieAlgebra

