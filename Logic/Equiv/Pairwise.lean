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

/-
**EmbeddingLike.pairwise_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EmbeddingLike.pairwise_comp {X : Type*} {Y : Type*} {F} [FunLike F Y X] [E
mbeddingLike F Y X] (f : F) {p : X -> X -> Prop} (h : Pairwise p) : Pairwise (p 
on f)
参数：f : F；h : Pairwise p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pairwise.comp_of_injective`：Pairwise.comp_of_injective (hr : Pairwise r)
 {f : β -> α} (hf : Injective f) : Pairwise (r on f)
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
-/
lemma EmbeddingLike.pairwise_comp {X : Type*} {Y : Type*} {F} [FunLike F Y X] [EmbeddingLike F Y X]
    (f : F) {p : X → X → Prop} (h : Pairwise p) : Pairwise (p on f) :=
  h.comp_of_injective <| EmbeddingLike.injective f
/-
**EquivLike.pairwise_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EquivLike.pairwise_comp_iff {X : Type*} {Y : Type*} {F} [EquivLike F Y X] 
(f : F) (p : X -> X -> Prop) : Pairwise (p on f) ↔ Pairwise p
参数：f : F；p : X -> X -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Bijective.pairwise_comp_iff`：Function.Bijective.pairwise_comp_i
ff {f : β -> α} (hf : Bijective f) : Pairwise (r on f) ↔ Pairwise r
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
lemma EquivLike.pairwise_comp_iff {X : Type*} {Y : Type*} {F} [EquivLike F Y X]
    (f : F) (p : X → X → Prop) : Pairwise (p on f) ↔ Pairwise p :=
  (EquivLike.bijective f).pairwise_comp_iff
