/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.PNat.Defs

/-!
# Finite intervals of positive naturals

This file proves that `ℕ+` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

public section


open Finset Function PNat

namespace PNat

variable (a b : Nat+)

/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: : LocallyFiniteOrder Nat+
  body: inferInstanceAs LocallyFiniteOrder (Subtype _)

中文:
实例 instLocallyFiniteOrder
  签名: : LocallyFiniteOrder 自然数+
  定义体: inferInstanceAs LocallyFiniteOrder (Subtype _)

Depends on / 依赖: LocallyFiniteOrder, Subtype
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder Nat+ :=
inferInstanceAs LocallyFiniteOrder (Subtype _)

/--
theorem `Icc_eq_finset_subtype` / 定理 `Icc_eq_finset_subtype`

English:
theorem Icc_eq_finset_subtype
  statement: Icc a b = (Icc (a : Nat) b).subtype fun n : Nat => 0 < n
  proof: rfl

中文:
定理 Icc_eq_finset_subtype
  结论: Icc a b = (Icc (a : 自然数) b).subtype fun n : 自然数 => 0 < n
  证明: rfl
-/
theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : Nat) b).subtype fun n : Nat => 0 < n :=
  rfl

/--
theorem `Ico_eq_finset_subtype` / 定理 `Ico_eq_finset_subtype`

English:
theorem Ico_eq_finset_subtype
  statement: Ico a b = (Ico (a : Nat) b).subtype fun n : Nat => 0 < n
  proof: rfl

中文:
定理 Ico_eq_finset_subtype
  结论: Ico a b = (Ico (a : 自然数) b).subtype fun n : 自然数 => 0 < n
  证明: rfl
-/
theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : Nat) b).subtype fun n : Nat => 0 < n :=
  rfl

/--
theorem `Ioc_eq_finset_subtype` / 定理 `Ioc_eq_finset_subtype`

English:
theorem Ioc_eq_finset_subtype
  statement: Ioc a b = (Ioc (a : Nat) b).subtype fun n : Nat => 0 < n
  proof: rfl

中文:
定理 Ioc_eq_finset_subtype
  结论: Ioc a b = (Ioc (a : 自然数) b).subtype fun n : 自然数 => 0 < n
  证明: rfl
-/
theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : Nat) b).subtype fun n : Nat => 0 < n :=
  rfl

/--
theorem `Ioo_eq_finset_subtype` / 定理 `Ioo_eq_finset_subtype`

English:
theorem Ioo_eq_finset_subtype
  statement: Ioo a b = (Ioo (a : Nat) b).subtype fun n : Nat => 0 < n
  proof: rfl

中文:
定理 Ioo_eq_finset_subtype
  结论: Ioo a b = (Ioo (a : 自然数) b).subtype fun n : 自然数 => 0 < n
  证明: rfl
-/
theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : Nat) b).subtype fun n : Nat => 0 < n :=
  rfl

/--
theorem `uIcc_eq_finset_subtype` / 定理 `uIcc_eq_finset_subtype`

English:
theorem uIcc_eq_finset_subtype
  statement: uIcc a b = (uIcc (a : Nat) b).subtype fun n : Nat => 0 < n
  proof: rfl

中文:
定理 uIcc_eq_finset_subtype
  结论: uIcc a b = (uIcc (a : 自然数) b).subtype fun n : 自然数 => 0 < n
  证明: rfl
-/
theorem uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : Nat) b).subtype fun n : Nat => 0 < n := rfl

/--
theorem `map_subtype_embedding_Icc` / 定理 `map_subtype_embedding_Icc`

English:
theorem map_subtype_embedding_Icc
  statement: (Icc a b).map (Embedding.subtype _) = Icc ↑a ↑b
  proof: Finset.map_subtype_embedding_Icc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

中文:
定理 map_subtype_embedding_Icc
  结论: (Icc a b).map (Embedding.subtype _) = Icc ↑a ↑b
  证明: Finset.map_subtype_embedding_Icc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

Depends on / 依赖: Finset, Finset.map_subtype_embedding_Icc, hc.trans_le, map_subtype_embedding_Icc, trans_le
-/
theorem map_subtype_embedding_Icc : (Icc a b).map (Embedding.subtype _) = Icc ↑a ↑b :=
  Finset.map_subtype_embedding_Icc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

/--
theorem `map_subtype_embedding_Ico` / 定理 `map_subtype_embedding_Ico`

English:
theorem map_subtype_embedding_Ico
  statement: (Ico a b).map (Embedding.subtype _) = Ico ↑a ↑b
  proof: Finset.map_subtype_embedding_Ico _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

中文:
定理 map_subtype_embedding_Ico
  结论: (Ico a b).map (Embedding.subtype _) = Ico ↑a ↑b
  证明: Finset.map_subtype_embedding_Ico _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

Depends on / 依赖: Finset, Finset.map_subtype_embedding_Ico, hc.trans_le, map_subtype_embedding_Ico, trans_le
-/
theorem map_subtype_embedding_Ico : (Ico a b).map (Embedding.subtype _) = Ico ↑a ↑b :=
  Finset.map_subtype_embedding_Ico _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

/--
theorem `map_subtype_embedding_Ioc` / 定理 `map_subtype_embedding_Ioc`

English:
theorem map_subtype_embedding_Ioc
  statement: (Ioc a b).map (Embedding.subtype _) = Ioc ↑a ↑b
  proof: Finset.map_subtype_embedding_Ioc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

中文:
定理 map_subtype_embedding_Ioc
  结论: (Ioc a b).map (Embedding.subtype _) = Ioc ↑a ↑b
  证明: Finset.map_subtype_embedding_Ioc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

Depends on / 依赖: Finset, Finset.map_subtype_embedding_Ioc, hc.trans_le, map_subtype_embedding_Ioc, trans_le
-/
theorem map_subtype_embedding_Ioc : (Ioc a b).map (Embedding.subtype _) = Ioc ↑a ↑b :=
  Finset.map_subtype_embedding_Ioc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

/--
theorem `map_subtype_embedding_Ioo` / 定理 `map_subtype_embedding_Ioo`

English:
theorem map_subtype_embedding_Ioo
  statement: (Ioo a b).map (Embedding.subtype _) = Ioo ↑a ↑b
  proof: Finset.map_subtype_embedding_Ioo _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

中文:
定理 map_subtype_embedding_Ioo
  结论: (Ioo a b).map (Embedding.subtype _) = Ioo ↑a ↑b
  证明: Finset.map_subtype_embedding_Ioo _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

Depends on / 依赖: Finset, Finset.map_subtype_embedding_Ioo, hc.trans_le, map_subtype_embedding_Ioo, trans_le
-/
theorem map_subtype_embedding_Ioo : (Ioo a b).map (Embedding.subtype _) = Ioo ↑a ↑b :=
  Finset.map_subtype_embedding_Ioo _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

/--
theorem `map_subtype_embedding_uIcc` / 定理 `map_subtype_embedding_uIcc`

English:
theorem map_subtype_embedding_uIcc
  statement: (uIcc a b).map (Embedding.subtype _) = uIcc ↑a ↑b
  proof: map_subtype_embedding_Icc _ _

中文:
定理 map_subtype_embedding_uIcc
  结论: (uIcc a b).map (Embedding.subtype _) = uIcc ↑a ↑b
  证明: map_subtype_embedding_Icc _ _

Depends on / 依赖: map_subtype_embedding_Icc
-/
theorem map_subtype_embedding_uIcc : (uIcc a b).map (Embedding.subtype _) = uIcc ↑a ↑b :=
  map_subtype_embedding_Icc _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `card_Icc` / 定理 `card_Icc`

English:
theorem card_Icc
  statement: #(Icc a b) = b + 1 - a
  proof: by
  rw [← Nat.card_Icc]; rw [← map_subtype_embedding_Icc]; rw [card_map]

中文:
定理 card_Icc
  结论: #(Icc a b) = b + 1 - a
  证明: by
  rw [← Nat.card_Icc]; rw [← map_subtype_embedding_Icc]; rw [card_map]

Depends on / 依赖: Nat.card_Icc, card_Icc, card_map, map_subtype_embedding_Icc
-/
theorem card_Icc : #(Icc a b) = b + 1 - a := by
  rw [← Nat.card_Icc]; rw [← map_subtype_embedding_Icc]; rw [card_map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `card_Ico` / 定理 `card_Ico`

English:
theorem card_Ico
  statement: #(Ico a b) = b - a
  proof: by
  rw [← Nat.card_Ico]; rw [← map_subtype_embedding_Ico]; rw [card_map]

中文:
定理 card_Ico
  结论: #(Ico a b) = b - a
  证明: by
  rw [← Nat.card_Ico]; rw [← map_subtype_embedding_Ico]; rw [card_map]

Depends on / 依赖: Nat.card_Ico, card_Ico, card_map, map_subtype_embedding_Ico
-/
theorem card_Ico : #(Ico a b) = b - a := by
  rw [← Nat.card_Ico]; rw [← map_subtype_embedding_Ico]; rw [card_map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `card_Ioc` / 定理 `card_Ioc`

English:
theorem card_Ioc
  statement: #(Ioc a b) = b - a
  proof: by
  rw [← Nat.card_Ioc]; rw [← map_subtype_embedding_Ioc]; rw [card_map]

中文:
定理 card_Ioc
  结论: #(Ioc a b) = b - a
  证明: by
  rw [← Nat.card_Ioc]; rw [← map_subtype_embedding_Ioc]; rw [card_map]

Depends on / 依赖: Nat.card_Ioc, card_Ioc, card_map, map_subtype_embedding_Ioc
-/
theorem card_Ioc : #(Ioc a b) = b - a := by
  rw [← Nat.card_Ioc]; rw [← map_subtype_embedding_Ioc]; rw [card_map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `card_Ioo` / 定理 `card_Ioo`

English:
theorem card_Ioo
  statement: #(Ioo a b) = b - a - 1
  proof: by
  rw [← Nat.card_Ioo]; rw [← map_subtype_embedding_Ioo]; rw [card_map]

中文:
定理 card_Ioo
  结论: #(Ioo a b) = b - a - 1
  证明: by
  rw [← Nat.card_Ioo]; rw [← map_subtype_embedding_Ioo]; rw [card_map]

Depends on / 依赖: Nat.card_Ioo, card_Ioo, card_map, map_subtype_embedding_Ioo
-/
theorem card_Ioo : #(Ioo a b) = b - a - 1 := by
  rw [← Nat.card_Ioo]; rw [← map_subtype_embedding_Ioo]; rw [card_map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `card_uIcc` / 定理 `card_uIcc`

English:
theorem card_uIcc
  statement: #(uIcc a b) = (b - a : Int).natAbs + 1
  proof: by
  rw [← Nat.card_uIcc]; rw [← map_subtype_embedding_uIcc]; rw [card_map]

中文:
定理 card_uIcc
  结论: #(uIcc a b) = (b - a : 整数).natAbs + 1
  证明: by
  rw [← Nat.card_uIcc]; rw [← map_subtype_embedding_uIcc]; rw [card_map]

Depends on / 依赖: Nat.card_uIcc, card_map, card_uIcc, map_subtype_embedding_uIcc
-/
theorem card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1 := by
  rw [← Nat.card_uIcc]; rw [← map_subtype_embedding_uIcc]; rw [card_map]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `card_fintype_Icc` / 定理 `card_fintype_Icc`

English:
theorem card_fintype_Icc
  statement: Fintype.card (Set.Icc a b) = b + 1 - a
  proof: by
  rw [← card_Icc]; rw [Fintype.card_ofFinset]

中文:
定理 card_fintype_Icc
  结论: Fintype.card (Set.Icc a b) = b + 1 - a
  证明: by
  rw [← card_Icc]; rw [Fintype.card_ofFinset]

Depends on / 依赖: Fintype, Fintype.card_ofFinset, card_Icc, card_ofFinset
-/
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc]; rw [Fintype.card_ofFinset]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `card_fintype_Ico` / 定理 `card_fintype_Ico`

English:
theorem card_fintype_Ico
  statement: Fintype.card (Set.Ico a b) = b - a
  proof: by
  rw [← card_Ico]; rw [Fintype.card_ofFinset]

中文:
定理 card_fintype_Ico
  结论: Fintype.card (Set.Ico a b) = b - a
  证明: by
  rw [← card_Ico]; rw [Fintype.card_ofFinset]

Depends on / 依赖: Fintype, Fintype.card_ofFinset, card_Ico, card_ofFinset
-/
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico]; rw [Fintype.card_ofFinset]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `card_fintype_Ioc` / 定理 `card_fintype_Ioc`

English:
theorem card_fintype_Ioc
  statement: Fintype.card (Set.Ioc a b) = b - a
  proof: by
  rw [← card_Ioc]; rw [Fintype.card_ofFinset]

中文:
定理 card_fintype_Ioc
  结论: Fintype.card (Set.Ioc a b) = b - a
  证明: by
  rw [← card_Ioc]; rw [Fintype.card_ofFinset]

Depends on / 依赖: Fintype, Fintype.card_ofFinset, card_Ioc, card_ofFinset
-/
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc]; rw [Fintype.card_ofFinset]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `card_fintype_Ioo` / 定理 `card_fintype_Ioo`

English:
theorem card_fintype_Ioo
  statement: Fintype.card (Set.Ioo a b) = b - a - 1
  proof: by
  rw [← card_Ioo]; rw [Fintype.card_ofFinset]

中文:
定理 card_fintype_Ioo
  结论: Fintype.card (Set.Ioo a b) = b - a - 1
  证明: by
  rw [← card_Ioo]; rw [Fintype.card_ofFinset]

Depends on / 依赖: Fintype, Fintype.card_ofFinset, card_Ioo, card_ofFinset
-/
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo]; rw [Fintype.card_ofFinset]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `card_fintype_uIcc` / 定理 `card_fintype_uIcc`

English:
theorem card_fintype_uIcc
  statement: Fintype.card (Set.uIcc a b) = (b - a : Int).natAbs + 1
  proof: by
  rw [← card_uIcc]; rw [Fintype.card_ofFinset]

中文:
定理 card_fintype_uIcc
  结论: Fintype.card (Set.uIcc a b) = (b - a : 整数).natAbs + 1
  证明: by
  rw [← card_uIcc]; rw [Fintype.card_ofFinset]

Depends on / 依赖: Fintype, Fintype.card_ofFinset, card_ofFinset, card_uIcc
-/
theorem card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a : Int).natAbs + 1 := by
  rw [← card_uIcc]; rw [Fintype.card_ofFinset]

end PNat
