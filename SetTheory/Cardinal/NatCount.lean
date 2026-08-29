/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Goryachev
-/
module

public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Set.Card

/-!
# Counting on ℕ

This file provides lemmas about the relation of `Nat.count` with cardinality functions.
-/

public section


namespace Nat
open Nat Count

variable {p : Nat -> Prop} [DecidablePred p] (n : Nat)

/--
theorem `count_le_cardinal` / 定理 `count_le_cardinal`

English:
theorem count_le_cardinal
  statement: (count p n : Cardinal) <= Cardinal.mk { k | p k }
  proof: by
  rw [count_eq_card_fintype]; rw [← Cardinal.mk_fintype]
  exact Cardinal.mk_subtype_mono fun x hx => hx.2

中文:
定理 count_le_cardinal
  结论: (count p n : 基数) <= 基数.mk { k | p k }
  证明: by
  rw [count_eq_card_fintype]; rw [← Cardinal.mk_fintype]
  exact Cardinal.mk_subtype_mono fun x hx => hx.2

Depends on / 依赖: Cardinal, Cardinal.mk_fintype, Cardinal.mk_subtype_mono, count_eq_card_fintype, mk_fintype, mk_subtype_mono
-/
theorem count_le_cardinal : (count p n : Cardinal) <= Cardinal.mk { k | p k } := by
  rw [count_eq_card_fintype]; rw [← Cardinal.mk_fintype]
  exact Cardinal.mk_subtype_mono fun x hx => hx.2

/--
theorem `count_le_setENCard` / 定理 `count_le_setENCard`

English:
theorem count_le_setENCard
  statement: count p n <= Set.encard { k | p k }
  proof: by
  simp only [Set.encard, ENat.card, Set.coe_ofPred, Cardinal.natCast_le_toENat]
  exact Nat.count_le_cardinal n

中文:
定理 count_le_setENCard
  结论: count p n <= 集合.encard { k | p k }
  证明: by
  simp only [Set.encard, ENat.card, Set.coe_ofPred, Cardinal.natCast_le_toENat]
  exact Nat.count_le_cardinal n

Depends on / 依赖: Cardinal, Cardinal.natCast_le_toENat, ENat.card, Nat.count_le_cardinal, Set.coe_ofPred, Set.encard, coe_ofPred, count_le_cardinal, encard, natCast_le_toENat
-/
theorem count_le_setENCard : count p n <= Set.encard { k | p k } := by
  simp only [Set.encard, ENat.card, Set.coe_ofPred, Cardinal.natCast_le_toENat]
  exact Nat.count_le_cardinal n

/--
theorem `count_le_setNCard` / 定理 `count_le_setNCard`

English:
theorem count_le_setNCard
  given: (h : { k | p k }.Finite)
  statement: count p n <= Set.ncard { k | p k }
  proof: by
  rw [Set.ncard_def]; rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_toNat (by simpa)]
  exact count_le_setENCard n

中文:
定理 count_le_setNCard
  条件: (h : { k | p k }.有限)
  结论: count p n <= 集合.ncard { k | p k }
  证明: by
  rw [Set.ncard_def]; rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_toNat (by simpa)]
  exact count_le_setENCard n

Depends on / 依赖: ENat.natCast_le_natCast, ENat.natCast_toNat, Set.ncard_def, count_le_setENCard, natCast_le_natCast, natCast_toNat, ncard_def
-/
theorem count_le_setNCard (h : { k | p k }.Finite) : count p n <= Set.ncard { k | p k } := by
  rw [Set.ncard_def]; rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_toNat (by simpa)]
  exact count_le_setENCard n

end Nat
