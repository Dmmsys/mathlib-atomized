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

/-
**EquivFunctorUnique** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EquivFunctorUnique : EquivFunctor Unique where map e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance EquivFunctorUnique : EquivFunctor Unique where
  map e := Equiv.uniqueCongr e
  map_refl' α := by simp [eq_iff_true_of_subsingleton]
  map_trans' := by simp [eq_iff_true_of_subsingleton]
/-
**EquivFunctorPerm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EquivFunctorPerm : EquivFunctor Perm where map e p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance EquivFunctorPerm : EquivFunctor Perm where
  map e p := (e.symm.trans p).trans e
  map_refl' α := by ext; simp
  map_trans' _ _ := by ext; simp

-- There is a classical instance of `LawfulFunctor Finset` available,
-- but we provide this computable alternative separately.
/-
**EquivFunctorFinset** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EquivFunctorFinset : EquivFunctor Finset where map e s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance EquivFunctorFinset : EquivFunctor Finset where
  map e s := s.map e.toEmbedding
  map_refl' α := by ext; simp
  map_trans' k h := by ext; simp [-trans_toEmbedding]
/-
**EquivFunctorFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EquivFunctorFintype : EquivFunctor Fintype where map e _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
instance EquivFunctorFintype : EquivFunctor Fintype where
  map e _ := Fintype.ofBijective e e.bijective
  map_refl' α := by ext; simp [eq_iff_true_of_subsingleton]
  map_trans' := by simp [eq_iff_true_of_subsingleton]
