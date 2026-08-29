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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: X] [h
  body: h

中文:
实例 [预序
  签名: X] [h
  定义体: h
-/
instance [Preorder X] [h : SuccOrder X] : SuccOrder (Multiplicative X) := h
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: X] [h
  body: h

中文:
实例 [预序
  签名: X] [h
  定义体: h
-/
instance [Preorder X] [h : SuccOrder X] : SuccOrder (Additive X) := h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: X] [h
  body: h

中文:
实例 [预序
  签名: X] [h
  定义体: h
-/
instance [Preorder X] [h : PredOrder X] : PredOrder (Multiplicative X) := h
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: X] [h
  body: h

中文:
实例 [预序
  签名: X] [h
  定义体: h
-/
instance [Preorder X] [h : PredOrder X] : PredOrder (Additive X) := h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: X] [SuccOrder X] [h
  body: h

中文:
实例 [预序
  签名: X] [Succ序 X] [h
  定义体: h
-/
instance [Preorder X] [SuccOrder X] [h : IsSuccArchimedean X] :
    IsSuccArchimedean (Multiplicative X) := h
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: X] [SuccOrder X] [h
  body: h

中文:
实例 [预序
  签名: X] [Succ序 X] [h
  定义体: h
-/
instance [Preorder X] [SuccOrder X] [h : IsSuccArchimedean X] :
    IsSuccArchimedean (Additive X) := h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: X] [PredOrder X] [h
  body: h

中文:
实例 [预序
  签名: X] [Pred序 X] [h
  定义体: h
-/
instance [Preorder X] [PredOrder X] [h : IsPredArchimedean X] :
    IsPredArchimedean (Multiplicative X) := h
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: X] [PredOrder X] [h
  body: h

中文:
实例 [预序
  签名: X] [Pred序 X] [h
  定义体: h
-/
instance [Preorder X] [PredOrder X] [h : IsPredArchimedean X] :
    IsPredArchimedean (Additive X) := h

namespace Order

open Additive Multiplicative

/--
lemma `succ_ofMul` / 引理 `succ_ofMul`

English:
lemma succ_ofMul
  given: [Preorder X] [SuccOrder X] (x : X)
  statement: succ (ofMul x) = ofMul (succ x)
  proof: rfl

中文:
引理 succ_ofMul
  条件: [预序 X] [Succ序 X] (x : X)
  结论: succ (ofMul x) = ofMul (succ x)
  证明: rfl
-/
@[simp] lemma succ_ofMul [Preorder X] [SuccOrder X] (x : X) : succ (ofMul x) = ofMul (succ x) := rfl
/--
lemma `succ_toMul` / 引理 `succ_toMul`

English:
lemma succ_toMul
  given: [Preorder X] [SuccOrder X] (x : Additive X)
  proof: rfl

中文:
引理 succ_toMul
  条件: [预序 X] [Succ序 X] (x : 加性 X)
  证明: rfl
-/
@[simp] lemma succ_toMul [Preorder X] [SuccOrder X] (x : Additive X) :
    succ x.toMul = (succ x).toMul := rfl

/--
lemma `succ_ofAdd` / 引理 `succ_ofAdd`

English:
lemma succ_ofAdd
  given: [Preorder X] [SuccOrder X] (x : X)
  statement: succ (ofAdd x) = ofAdd (succ x)
  proof: rfl

中文:
引理 succ_ofAdd
  条件: [预序 X] [Succ序 X] (x : X)
  结论: succ (ofAdd x) = ofAdd (succ x)
  证明: rfl
-/
@[simp] lemma succ_ofAdd [Preorder X] [SuccOrder X] (x : X) : succ (ofAdd x) = ofAdd (succ x) := rfl
/--
lemma `succ_toAdd` / 引理 `succ_toAdd`

English:
lemma succ_toAdd
  given: [Preorder X] [SuccOrder X] (x : Multiplicative X)
  proof: rfl

中文:
引理 succ_toAdd
  条件: [预序 X] [Succ序 X] (x : Multiplicative X)
  证明: rfl
-/
@[simp] lemma succ_toAdd [Preorder X] [SuccOrder X] (x : Multiplicative X) :
    succ x.toAdd = (succ x).toAdd :=
  rfl

/--
lemma `pred_ofMul` / 引理 `pred_ofMul`

English:
lemma pred_ofMul
  given: [Preorder X] [PredOrder X] (x : X)
  statement: pred (ofMul x) = ofMul (pred x)
  proof: rfl
@[simp]

中文:
引理 pred_ofMul
  条件: [预序 X] [Pred序 X] (x : X)
  结论: pred (ofMul x) = ofMul (pred x)
  证明: rfl
@[simp]
-/
@[simp] lemma pred_ofMul [Preorder X] [PredOrder X] (x : X) : pred (ofMul x) = ofMul (pred x) := rfl
@[simp]
/--
lemma `pred_toMul` / 引理 `pred_toMul`

English:
lemma pred_toMul
  given: [Preorder X] [PredOrder X] (x : Additive X)
  statement: pred x.toMul = (pred x).toMul
  proof: rfl

中文:
引理 pred_toMul
  条件: [预序 X] [Pred序 X] (x : 加性 X)
  结论: pred x.toMul = (pred x).toMul
  证明: rfl
-/
lemma pred_toMul [Preorder X] [PredOrder X] (x : Additive X) : pred x.toMul = (pred x).toMul := rfl

/--
lemma `pred_ofAdd` / 引理 `pred_ofAdd`

English:
lemma pred_ofAdd
  given: [Preorder X] [PredOrder X] (x : X)
  statement: pred (ofAdd x) = ofAdd (pred x)
  proof: rfl

中文:
引理 pred_ofAdd
  条件: [预序 X] [Pred序 X] (x : X)
  结论: pred (ofAdd x) = ofAdd (pred x)
  证明: rfl
-/
@[simp] lemma pred_ofAdd [Preorder X] [PredOrder X] (x : X) : pred (ofAdd x) = ofAdd (pred x) := rfl
/--
lemma `pred_toAdd` / 引理 `pred_toAdd`

English:
lemma pred_toAdd
  given: [Preorder X] [PredOrder X] (x : Multiplicative X)
  proof: rfl

中文:
引理 pred_toAdd
  条件: [预序 X] [Pred序 X] (x : Multiplicative X)
  证明: rfl
-/
@[simp] lemma pred_toAdd [Preorder X] [PredOrder X] (x : Multiplicative X) :
    pred x.toAdd = (pred x).toAdd :=
  rfl

end Order
