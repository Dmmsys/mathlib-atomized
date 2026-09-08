/-
Copyright (c) 2022 Eric Wieser, Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# `Finset.sup` and ring operations
-/

public section

open Finset

namespace Nat
variable {ι R : Type*}

section LinearOrderedSemiring
variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {s : Finset ι}

set_option linter.docPrime false in
@[simp, norm_cast]
/-
**Nat.cast_finsetSup'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_finsetSup' (f : ι -> Nat) (hs) : ((s.sup' hs f : Nat) : R) = s.sup' h
s fun i => (f i : R)
参数：f : ι -> Nat；hs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup'_eq_sup'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
· 使用定理 `Nat.cast_max`：cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrdered
Ring α] (m n : Nat) : (↑(max m n : Nat) : α) = max (m : α) n
-/
lemma cast_finsetSup' (f : ι → ℕ) (hs) : ((s.sup' hs f : ℕ) : R) = s.sup' hs fun i ↦ (f i : R) :=
  apply_sup'_eq_sup'_comp _ _ cast_max

set_option linter.docPrime false in
@[simp, norm_cast]
/-
**Nat.cast_finsetInf'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_finsetInf' (f : ι -> Nat) (hs) : (↑(s.inf' hs f) : R) = s.inf' hs fun
 i => (f i : R)
参数：f : ι -> Nat；hs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_inf'_eq_inf'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
· 使用定理 `Nat.cast_min`：cast_min {α} [Semiring α] [LinearOrder α] [IsStrictOrdered
Ring α] (m n : Nat) : (↑(min m n : Nat) : α) = min (m : α) n
-/
lemma cast_finsetInf' (f : ι → ℕ) (hs) : (↑(s.inf' hs f) : R) = s.inf' hs fun i ↦ (f i : R) :=
  apply_inf'_eq_inf'_comp _ _ cast_min

@[simp, norm_cast]
/-
**Nat.cast_finsetSup** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_finsetSup [OrderBot R] [CanonicallyOrderedAdd R] (s : Finset ι) (f : 
ι -> Nat) : (↑(s.sup f) : R) = s.sup fun i => (f i : R)
参数：s : Finset ι；f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
· 使用定理 `Nat.cast_max`：cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrdered
Ring α] (m n : Nat) : (↑(max m n : Nat) : α) = max (m : α) n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cast_finsetSup [OrderBot R] [CanonicallyOrderedAdd R] (s : Finset ι) (f : ι → ℕ) :
    (↑(s.sup f) : R) = s.sup fun i ↦ (f i : R) :=
  apply_sup_eq_sup_comp _ cast_max (by simp)

end LinearOrderedSemiring

end Nat

section

variable {R ι : Type*} [LinearOrder R] [NonUnitalNonAssocSemiring R]
  [CanonicallyOrderedAdd R] [OrderBot R]

/-
**Finset.mul_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Finset.mul_sup₀ (s : Finset ι) (f : ι → R) (a : R) :
    a * s.sup f = s.sup (a * f ·) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, mul_max, ← IH]

/-- Also see `Finset.sup'_mul₀` for a version for `GroupWithZero`s. -/
/-
**Finset.sup_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Also see `Finset.sup'_mul₀` for a version for `GroupWithZero`s.
-/
lemma Finset.sup_mul₀ (s : Finset ι) (f : ι → R) (a : R) :
    s.sup f * a = s.sup (f · * a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, max_mul, ← IH]

end

