/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Finset.Insert

/-!
# Order isomorphisms from Fin to finsets

We define order isomorphisms like `Fin.orderIsoTriple` from `Fin 3`
to the finset `{a, b, c}` when `a < b` and `b < c`.

## Future works

* Do the same for `Set` without too much duplication of code (TODO)
* Provide a definition which would take as an input an order
  isomorphism `e : Fin (n + 1) ≃o s` (with `s : Set α` (or `Finset α`)) and
  extend it to an order isomorphism `Fin (n + 2) ≃o Finset.insert i s` when `i < e 0` (TODO).

-/

@[expose] public section

namespace Fin

variable {α : Type*} [Preorder α]

/-- This is the order isomorphism from `Fin 1` to a finset `{a}`. -/
/-
**Fin.orderIsoSingleton** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：orderIsoSingleton (a : α) : Fin 1 ≃o ({a} : Finset α)
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the order isomorphism from `Fin 1` to a finset `{a}`.
-/
noncomputable def orderIsoSingleton (a : α) :
    Fin 1 ≃o ({a} : Finset α) :=
  OrderIso.ofUnique _ _

@[simp]
/-
**Fin.orderIsoSingleton_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderIsoSingleton_apply (a : α) (i : Fin 1) : orderIsoSingleton a i = a
参数：a : α；i : Fin 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderIsoSingleton_apply (a : α) (i : Fin 1) :
    orderIsoSingleton a i = a := rfl

variable [DecidableEq α]

section

variable (a b : α) (hab : a < b)

/-- This is the order isomorphism from `Fin 2` to a finset `{a, b}` when `a < b`. -/
/-
**Fin.orderIsoPair** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：orderIsoPair : Fin 2 ≃o ({a, b} : Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the order isomorphism from `Fin 2` to a finset `{a, b}` when `a < b`.
-/
noncomputable def orderIsoPair :
    Fin 2 ≃o ({a, b} : Finset α) :=
  StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩]
    (strictMono_vecEmpty.vecCons hab) (fun ⟨x, hx⟩ ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)
/-
**Fin.orderIsoPair_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableEq α] (a b : α) (h
ab : a < b),   ↑((Fin.orderIsoPair a b hab) 0) = a
参数：a b : α；hab : a < b；(Fin.orderIsoPair a b hab) 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma orderIsoPair_zero : orderIsoPair a b hab 0 = a := rfl
/-
**Fin.orderIsoPair_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableEq α] (a b : α) (h
ab : a < b),   ↑((Fin.orderIsoPair a b hab) 1) = b
参数：a b : α；hab : a < b；(Fin.orderIsoPair a b hab) 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma orderIsoPair_one : orderIsoPair a b hab 1 = b := rfl

end

section

variable (a b c : α) (hab : a < b) (hbc : b < c)

/-- This is the order isomorphism from `Fin 3`
to a finset `{a, b, c}` when `a < b` and `b < c`. -/
/-
**Fin.orderIsoTriple** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：orderIsoTriple : Fin 3 ≃o ({a, b, c} : Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the order isomorphism from `Fin 3`
to a finset `{a, b, c}` when `a < b` and `b < c`.
-/
noncomputable def orderIsoTriple :
    Fin 3 ≃o ({a, b, c} : Finset α) :=
  StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩, ⟨c, by simp⟩]
    (StrictMono.vecCons (strictMono_vecEmpty.vecCons hbc) hab) (fun ⟨x, hx⟩ ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)
/-
**Fin.orderIsoTriple_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableEq α] (a b c : α) 
(hab : a < b) (hbc : b < c),   ↑((Fin.orderIsoTriple a b c hab hbc) 0) = a
参数：a b c : α；hab : a < b；hbc : b < c；(Fin.orderIsoTriple a b c hab hbc) 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma orderIsoTriple_zero : orderIsoTriple a b c hab hbc 0 = a := rfl
/-
**Fin.orderIsoTriple_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableEq α] (a b c : α) 
(hab : a < b) (hbc : b < c),   ↑((Fin.orderIsoTriple a b c hab hbc) 1) = b
参数：a b c : α；hab : a < b；hbc : b < c；(Fin.orderIsoTriple a b c hab hbc) 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma orderIsoTriple_one : orderIsoTriple a b c hab hbc 1 = b := rfl
/-
**Fin.orderIsoTriple_two** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableEq α] (a b c : α) 
(hab : a < b) (hbc : b < c),   ↑((Fin.orderIsoTriple a b c hab hbc) 2) = c
参数：a b c : α；hab : a < b；hbc : b < c；(Fin.orderIsoTriple a b c hab hbc) 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma orderIsoTriple_two : orderIsoTriple a b c hab hbc 2 = c := rfl

end

end Fin

