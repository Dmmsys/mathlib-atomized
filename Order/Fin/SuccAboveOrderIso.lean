/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# The order isomorphism `Fin (n + 1) ≃o {i}ᶜ`

Given `i : Fin (n + 2)`, we show that `Fin.succAboveOrderEmb` induces
an order isomorphism `Fin (n + 1) ≃o ({i}ᶜ : Finset (Fin (n + 2)))`.

-/

@[expose] public section

open Finset

/-- Given `i : Fin (n + 2)`, this is the order isomorphism
between `Fin (n + 1)` and the finite set `{i}ᶜ`. -/
/-
**Fin.succAboveOrderIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fin.succAboveOrderIso {n : Nat} (i : Fin (n + 2)) : Fin (n + 1) ≃o ({i}ᶜ :
 Finset (Fin (n + 2))) where toEquiv
参数：i : Fin (n + 2)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `i : Fin (n + 2)`, this is the order isomorphism
between `Fin (n + 1)` and the finite set `{i}ᶜ`.
-/
noncomputable def Fin.succAboveOrderIso {n : ℕ} (i : Fin (n + 2)) :
    Fin (n + 1) ≃o ({i}ᶜ : Finset (Fin (n + 2))) where
  toEquiv :=
    Equiv.ofBijective (f := fun a ↦ ⟨Fin.succAboveOrderEmb i a, by simp⟩) (by
      constructor
      · intro a b h
        exact (Fin.succAboveOrderEmb i).injective (by simpa using h)
      · rintro ⟨j, hj⟩
        simp only [mem_compl, mem_singleton] at hj
        obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ i
        · exact ⟨j.pred hj, by simp⟩
        · exact ⟨i.predAbove j, by aesop⟩)
  map_rel_iff' {a b} := by
    simp only [Equiv.ofBijective_apply, Subtype.mk_le_mk, OrderEmbedding.le_iff_le]
