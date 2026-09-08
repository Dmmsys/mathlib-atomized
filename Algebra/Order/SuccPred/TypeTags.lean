/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags

/-!
# Successor and predecessor on type tags

This file declares successor and predecessor orders on type tags.

-/

public section

variable {X : Type*}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder X] [h : SuccOrder X] : SuccOrder (Multiplicative X) := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder X] [h : SuccOrder X] : SuccOrder (Additive X) := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder X] [h : PredOrder X] : PredOrder (Multiplicative X) := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder X] [h : PredOrder X] : PredOrder (Additive X) := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder X] [SuccOrder X] [h : IsSuccArchimedean X] :
    IsSuccArchimedean (Multiplicative X) := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder X] [SuccOrder X] [h : IsSuccArchimedean X] :
    IsSuccArchimedean (Additive X) := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder X] [PredOrder X] [h : IsPredArchimedean X] :
    IsPredArchimedean (Multiplicative X) := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder X] [PredOrder X] [h : IsPredArchimedean X] :
    IsPredArchimedean (Additive X) := h

namespace Order

open Additive Multiplicative

/-
**Order.succ_ofMul** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {X : Type u_1} [inst : Preorder X] [inst_1 : SuccOrder X] (x : X),   Ord
er.succ (Additive.ofMul x) = Additive.ofMul (Order.succ x)
参数：x : X；Additive.ofMul x；Order.succ x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma succ_ofMul [Preorder X] [SuccOrder X] (x : X) : succ (ofMul x) = ofMul (succ x) := rfl
/-
**Order.succ_toMul** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {X : Type u_1} [inst : Preorder X] [inst_1 : SuccOrder X] (x : Additive 
X),   Order.succ (Additive.toMul x) = Additive.toMul (Order.succ x)
参数：x : Additive X；Additive.toMul x；Order.succ x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma succ_toMul [Preorder X] [SuccOrder X] (x : Additive X) :
    succ x.toMul = (succ x).toMul := rfl
/-
**Order.succ_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {X : Type u_1} [inst : Preorder X] [inst_1 : SuccOrder X] (x : X),   Ord
er.succ (Multiplicative.ofAdd x) = Multiplicative.ofAdd (Order.succ x)
参数：x : X；Multiplicative.ofAdd x；Order.succ x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma succ_ofAdd [Preorder X] [SuccOrder X] (x : X) : succ (ofAdd x) = ofAdd (succ x) := rfl
/-
**Order.succ_toAdd** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {X : Type u_1} [inst : Preorder X] [inst_1 : SuccOrder X] (x : Multiplic
ative X),   Order.succ (Multiplicative.toAdd x) = Multiplicative.toAdd (Order.su
cc x)
参数：x : Multiplicative X；Multiplicative.toAdd x；Order.succ x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma succ_toAdd [Preorder X] [SuccOrder X] (x : Multiplicative X) :
    succ x.toAdd = (succ x).toAdd :=
  rfl
/-
**Order.pred_ofMul** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {X : Type u_1} [inst : Preorder X] [inst_1 : PredOrder X] (x : X),   Ord
er.pred (Additive.ofMul x) = Additive.ofMul (Order.pred x)
参数：x : X；Additive.ofMul x；Order.pred x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pred_ofMul [Preorder X] [PredOrder X] (x : X) : pred (ofMul x) = ofMul (pred x) := rfl
@[simp]
/-
**Order.pred_toMul** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：pred_toMul [Preorder X] [PredOrder X] (x : Additive X) : pred x.toMul = (p
red x).toMul
参数：x : Additive X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pred_toMul [Preorder X] [PredOrder X] (x : Additive X) : pred x.toMul = (pred x).toMul := rfl
/-
**Order.pred_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {X : Type u_1} [inst : Preorder X] [inst_1 : PredOrder X] (x : X),   Ord
er.pred (Multiplicative.ofAdd x) = Multiplicative.ofAdd (Order.pred x)
参数：x : X；Multiplicative.ofAdd x；Order.pred x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pred_ofAdd [Preorder X] [PredOrder X] (x : X) : pred (ofAdd x) = ofAdd (pred x) := rfl
/-
**Order.pred_toAdd** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {X : Type u_1} [inst : Preorder X] [inst_1 : PredOrder X] (x : Multiplic
ative X),   Order.pred (Multiplicative.toAdd x) = Multiplicative.toAdd (Order.pr
ed x)
参数：x : Multiplicative X；Multiplicative.toAdd x；Order.pred x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pred_toAdd [Preorder X] [PredOrder X] (x : Multiplicative X) :
    pred x.toAdd = (pred x).toAdd :=
  rfl

end Order

