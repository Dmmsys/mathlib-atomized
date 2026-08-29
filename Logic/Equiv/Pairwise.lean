/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Logic.Pairwise

/-!
# Interaction of equivalences with `Pairwise`
-/

public section

open scoped Function -- required for scoped `on` notation

/--
lemma `EmbeddingLike.pairwise_comp` / 引理 `EmbeddingLike.pairwise_comp`

English:
lemma EmbeddingLike.pairwise_comp
  statement: {X : Type*} {Y : Type*} {F} [FunLike F Y X] [EmbeddingLike F Y X]
  proof: h.comp_of_injective EmbeddingLike.injective f

中文:
引理 EmbeddingLike.pairwise_comp
  结论: {X : 类型} {Y : 类型} {F} [函数状 F Y X] [EmbeddingLike F Y X]
  证明: h.comp_of_injective EmbeddingLike.injective f

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, comp_of_injective, h.comp_of_injective, injective
-/
lemma EmbeddingLike.pairwise_comp {X : Type*} {Y : Type*} {F} [FunLike F Y X] [EmbeddingLike F Y X]
    (f : F) {p : X -> X -> Prop} (h : Pairwise p) : Pairwise (p on f) :=
h.comp_of_injective EmbeddingLike.injective f

/--
lemma `EquivLike.pairwise_comp_iff` / 引理 `EquivLike.pairwise_comp_iff`

English:
lemma EquivLike.pairwise_comp_iff
  statement: {X : Type*} {Y : Type*} {F} [EquivLike F Y X]
  proof: (EquivLike.bijective f).pairwise_comp_iff

中文:
引理 等价状.pairwise_comp_iff
  结论: {X : 类型} {Y : 类型} {F} [等价状 F Y X]
  证明: (EquivLike.bijective f).pairwise_comp_iff

Depends on / 依赖: EquivLike, EquivLike.bijective, bijective, pairwise_comp_iff
-/
lemma EquivLike.pairwise_comp_iff {X : Type*} {Y : Type*} {F} [EquivLike F Y X]
    (f : F) (p : X -> X -> Prop) : Pairwise (p on f) ↔ Pairwise p :=
  (EquivLike.bijective f).pairwise_comp_iff
