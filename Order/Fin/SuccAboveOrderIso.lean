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

/--
Definition of `Fin.succAboveOrderIso` / `Fin.succAboveOrderIso` 的定义

English:
definition Fin.succAboveOrderIso
  signature: {n : Nat} (i : Fin (n + 2))
  body: Equiv.ofBijective (f := fun a => ⟨Fin.succAboveOrderEmb i a, by simp⟩) (by
      constructor
      · intro a b h
        exact (Fin.succAboveOrderEmb i).injective (by simpa using h)
      · rintro ⟨j, hj⟩
        simp only [mem_compl, mem_singleton] at hj
        obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero

中文:
定义 Fin.succAboveOrderIso
  签名: {n : 自然数} (i : Fin (n + 2))
  定义体: Equiv.ofBijective (f := fun a => ⟨Fin.succAboveOrderEmb i a, by simp⟩) (by
      constructor
      · intro a b h
        exact (Fin.succAboveOrderEmb i).injective (by simpa using h)
      · rintro ⟨j, hj⟩
        simp only [mem_compl, mem_singleton] at hj
        obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero

Depends on / 依赖: Equiv.ofBijective, Equiv.ofBijective_apply, Fin.eq_zero_or_eq_succ, Fin.succAboveOrderEmb, OrderEmbedding, OrderEmbedding.le_iff_le, Subtype, Subtype.mk_le_mk, eq_zero_or_eq_succ, i.predAbove, injective, j.pred, le_iff_le, map_rel_iff, mem_compl, mem_singleton, mk_le_mk, ofBijective, ofBijective_apply, predAbove
-/
noncomputable def Fin.succAboveOrderIso {n : Nat} (i : Fin (n + 2)) :
    Fin (n + 1) ≃o ({i}ᶜ : Finset (Fin (n + 2))) where
  toEquiv :=
    Equiv.ofBijective (f := fun a => ⟨Fin.succAboveOrderEmb i a, by simp⟩) (by
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
