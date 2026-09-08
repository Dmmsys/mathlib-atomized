/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!

# The extension adjoining all p-th roots to a field of characteristic p.

In this file, we introduce the field extension adjoining all `p`-th roots to a
field of (exponential) characteristic `p`.

# Main definitions and results

* `AdjoinPthRoots`: the field extension adjoining all `p`-th roots to a field of
  (exponential) characteristic `p`.
* `AdjoinPthRoots.root`: for `k` a field of (exponential) characteristic `p`, the `p`-th root map
  `k → AdjoinPthRoots k`, mapping an element to its unique `p`-th root in `AdjoinPthRoots`,
  as a `RingEquiv`.

-/

public section

variable (k : Type*) [Field k]

/-- Adjoining all `p`-th root to a field of (exponential) characteristic `p`. -/
-- Note: It is defined as a typeclass synonym of the field `k` itself
-- with a `k`-algebra structure given by the frobenius map.
/-
**AdjoinPthRoots** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AdjoinPthRoots
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def AdjoinPthRoots := k

@[no_expose]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Field (AdjoinPthRoots k) := inferInstanceAs (Field k)

@[no_expose]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Algebra k (AdjoinPthRoots k) := (frobenius k (ringExpChar k)).toAlgebra
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : ℕ) [ExpChar k p] : ExpChar (AdjoinPthRoots k) p := inferInstanceAs (ExpChar k p)

/-- For `k` a field of (exponential) characteristic `p`,
the `p`-th root map `k → AdjoinPthRoots k`, as a `RingEquiv`. -/
/-
**AdjoinPthRoots.root** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AdjoinPthRoots.root : k ≃+* AdjoinPthRoots k
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `k` a field of (exponential) characteristic `p`,
the `p`-th root map `k → AdjoinPthRoots k`, as a `RingEquiv`.
-/
noncomputable def AdjoinPthRoots.root : k ≃+* AdjoinPthRoots k := RingEquiv.refl k

variable {k} (p : ℕ) [ExpChar k p]

@[simp]
/-
**AdjoinPthRoots.root_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AdjoinPthRoots.root_pow (x : k) : (AdjoinPthRoots.root k x) ^ p = algebraM
ap k (AdjoinPthRoots k) x
参数：x : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q
-/
lemma AdjoinPthRoots.root_pow (x : k) :
    (AdjoinPthRoots.root k x) ^ p = algebraMap k (AdjoinPthRoots k) x := by
  rw [← ringExpChar.eq k p]
  rfl
/-
**AdjoinPthRoots.algebraMap_root_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AdjoinPthRoots.algebraMap_root_symm (x : AdjoinPthRoots k) : algebraMap k 
(AdjoinPthRoots k) ((AdjoinPthRoots.root k).symm x) = x ^ p
参数：x : AdjoinPthRoots k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q
-/
lemma AdjoinPthRoots.algebraMap_root_symm (x : AdjoinPthRoots k) :
    algebraMap k (AdjoinPthRoots k) ((AdjoinPthRoots.root k).symm x) = x ^ p := by
  rw [← ringExpChar.eq k p]
  rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPurelyInseparable k (AdjoinPthRoots k) := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro x
  use 1, (AdjoinPthRoots.root k).symm x
  simp [AdjoinPthRoots.algebraMap_root_symm p]
