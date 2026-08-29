/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Control.EquivFunctor
public import Mathlib.Data.Fintype.OfMap

/-!
# `EquivFunctor` instances

We derive some `EquivFunctor` instances, to enable `equiv_rw` to rewrite under these functions.
-/

public section


open Equiv

/--
Instance `EquivFunctorUnique` / 实例 `EquivFunctorUnique`

English:
instance EquivFunctorUnique
  signature: : EquivFunctor Unique where
  body: Equiv.uniqueCongr e
  map_refl' α := by simp [eq_iff_true_of_subsingleton]
  map_trans' := by simp [eq_iff_true_of_subsingleton]

中文:
实例 EquivFunctorUnique
  签名: : 等价函子 唯一 where
  定义体: Equiv.uniqueCongr e
  map_refl' α := by simp [eq_iff_true_of_subsingleton]
  map_trans' := by simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: Equiv.uniqueCongr, uniqueCongr
-/
instance EquivFunctorUnique : EquivFunctor Unique where
  map e := Equiv.uniqueCongr e
  map_refl' α := by simp [eq_iff_true_of_subsingleton]
  map_trans' := by simp [eq_iff_true_of_subsingleton]

/--
Instance `EquivFunctorPerm` / 实例 `EquivFunctorPerm`

English:
instance EquivFunctorPerm
  signature: : EquivFunctor Perm where
  body: (e.symm.trans p).trans e
  map_refl' α := by ext; simp
  map_trans' _ _ := by ext; simp

中文:
实例 EquivFunctorPerm
  签名: : 等价函子 置换 where
  定义体: (e.symm.trans p).trans e
  map_refl' α := by ext; simp
  map_trans' _ _ := by ext; simp

Depends on / 依赖: e.symm.trans
-/
instance EquivFunctorPerm : EquivFunctor Perm where
  map e p := (e.symm.trans p).trans e
  map_refl' α := by ext; simp
  map_trans' _ _ := by ext; simp

-- There is a classical instance of `LawfulFunctor Finset` available,
-- but we provide this computable alternative separately.
/--
Instance `EquivFunctorFinset` / 实例 `EquivFunctorFinset`

English:
instance EquivFunctorFinset
  signature: : EquivFunctor Finset where
  body: s.map e.toEmbedding
  map_refl' α := by ext; simp
  map_trans' k h := by ext; simp [-trans_toEmbedding]

中文:
实例 EquivFunctorFinset
  签名: : 等价函子 有限集 where
  定义体: s.map e.toEmbedding
  map_refl' α := by ext; simp
  map_trans' k h := by ext; simp [-trans_toEmbedding]

Depends on / 依赖: e.toEmbedding, s.map, toEmbedding
-/
instance EquivFunctorFinset : EquivFunctor Finset where
  map e s := s.map e.toEmbedding
  map_refl' α := by ext; simp
  map_trans' k h := by ext; simp [-trans_toEmbedding]

/--
Instance `EquivFunctorFintype` / 实例 `EquivFunctorFintype`

English:
instance EquivFunctorFintype
  signature: : EquivFunctor Fintype where
  body: Fintype.ofBijective e e.bijective
  map_refl' α := by ext; simp [eq_iff_true_of_subsingleton]
  map_trans' := by simp [eq_iff_true_of_subsingleton]

中文:
实例 EquivFunctorFintype
  签名: : 等价函子 有限类型 where
  定义体: Fintype.ofBijective e e.bijective
  map_refl' α := by ext; simp [eq_iff_true_of_subsingleton]
  map_trans' := by simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: Fintype, Fintype.ofBijective, bijective, e.bijective, ofBijective
-/
instance EquivFunctorFintype : EquivFunctor Fintype where
  map e _ := Fintype.ofBijective e e.bijective
  map_refl' α := by ext; simp [eq_iff_true_of_subsingleton]
  map_trans' := by simp [eq_iff_true_of_subsingleton]
