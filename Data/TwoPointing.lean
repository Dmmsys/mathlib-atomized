/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Logic.Nonempty
public import Mathlib.Tactic.Simps.Basic
public import Batteries.Logic

/-!
# Two-pointings

This file defines `TwoPointing α`, the type of two pointings of `α`. A two-pointing is the data of
two distinct terms.

This is morally a Type-valued `Nontrivial`. Another type which is quite close in essence is `Sym2`.
Categorically speaking, `prod` is a cospan in the category of types. This forms the category of
bipointed types. Two-pointed types form a full subcategory of those.

## References

* [nLab, *Coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/

@[expose] public section

open Function

variable {α β : Type*}

/-- Two-pointing of a type. This is a Type-valued termed `Nontrivial`. -/
@[ext]
/--
Definition of `TwoPointing` / `TwoPointing` 的定义

English:
structure TwoPointing
  parameters: (α : Type*)
  extends: α × α
  axioms and operations (1):
    - fst_ne_snd : fst != snd

中文:
结构 TwoPointing
  参数: (α : 类型)
  继承: α × α
  公理与运算 (1 个):
    - fst_ne_snd : fst != snd
-/
structure TwoPointing (α : Type*) extends α × α where
  /-- `fst` and `snd` are distinct terms -/
  fst_ne_snd : fst != snd
  deriving DecidableEq

initialize_simps_projections TwoPointing (+toProd, -fst, -snd)

namespace TwoPointing

variable (p : TwoPointing α) (q : TwoPointing β)

/--
theorem `snd_ne_fst` / 定理 `snd_ne_fst`

English:
theorem snd_ne_fst
  statement: p.snd != p.fst
  proof: p.fst_ne_snd.symm

中文:
定理 snd_ne_fst
  结论: p.snd != p.fst
  证明: p.fst_ne_snd.symm

Depends on / 依赖: fst_ne_snd, p.fst_ne_snd.symm
-/
theorem snd_ne_fst : p.snd != p.fst :=
  p.fst_ne_snd.symm

/-- Swaps the two pointed elements. -/
@[simps]
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: : TwoPointing α
  body: ⟨(p.snd, p.fst), p.snd_ne_fst⟩

中文:
定义 swap
  签名: : TwoPointing α
  定义体: ⟨(p.snd, p.fst), p.snd_ne_fst⟩

Depends on / 依赖: p.fst, p.snd, p.snd_ne_fst, snd_ne_fst
-/
def swap : TwoPointing α :=
  ⟨(p.snd, p.fst), p.snd_ne_fst⟩

/--
theorem `swap_fst` / 定理 `swap_fst`

English:
theorem swap_fst
  statement: p.swap.fst = p.snd
  proof: rfl

中文:
定理 swap_fst
  结论: p.swap.fst = p.snd
  证明: rfl
-/
theorem swap_fst : p.swap.fst = p.snd := rfl

/--
theorem `swap_snd` / 定理 `swap_snd`

English:
theorem swap_snd
  statement: p.swap.snd = p.fst
  proof: rfl

@[simp]

中文:
定理 swap_snd
  结论: p.swap.snd = p.fst
  证明: rfl

@[simp]
-/
theorem swap_snd : p.swap.snd = p.fst := rfl

@[simp]
/--
theorem `swap_swap` / 定理 `swap_swap`

English:
theorem swap_swap
  statement: p.swap.swap = p
  proof: rfl

include p in

中文:
定理 swap_swap
  结论: p.swap.swap = p
  证明: rfl

include p in
-/
theorem swap_swap : p.swap.swap = p := rfl

include p in
/--
theorem `to_nontrivial` / 定理 `to_nontrivial`

English:
theorem to_nontrivial
  statement: Nontrivial α
  proof: ⟨⟨p.fst, p.snd, p.fst_ne_snd⟩⟩

中文:
定理 to_nontrivial
  结论: 非平凡 α
  证明: ⟨⟨p.fst, p.snd, p.fst_ne_snd⟩⟩

Depends on / 依赖: fst_ne_snd, p.fst, p.fst_ne_snd, p.snd
-/
theorem to_nontrivial : Nontrivial α :=
  ⟨⟨p.fst, p.snd, p.fst_ne_snd⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: α] : Nonempty (TwoPointing α)
  body: let ⟨a, b, h⟩ := exists_pair_ne α
  ⟨⟨(a, b), h⟩⟩

@[simp]

中文:
实例 [非平凡
  签名: α] : 非空 (TwoPointing α)
  定义体: let ⟨a, b, h⟩ := exists_pair_ne α
  ⟨⟨(a, b), h⟩⟩

@[simp]

Depends on / 依赖: exists_pair_ne
-/
instance [Nontrivial α] : Nonempty (TwoPointing α) :=
  let ⟨a, b, h⟩ := exists_pair_ne α
  ⟨⟨(a, b), h⟩⟩

@[simp]
/--
theorem `nonempty_two_pointing_iff` / 定理 `nonempty_two_pointing_iff`

English:
theorem nonempty_two_pointing_iff
  statement: Nonempty (TwoPointing α) ↔ Nontrivial α
  proof: ⟨fun ⟨p⟩ => p.to_nontrivial, fun _ => inferInstance⟩

中文:
定理 nonempty_two_pointing_iff
  结论: 非空 (TwoPointing α) ↔ 非平凡 α
  证明: ⟨fun ⟨p⟩ => p.to_nontrivial, fun _ => inferInstance⟩

Depends on / 依赖: p.to_nontrivial, to_nontrivial
-/
theorem nonempty_two_pointing_iff : Nonempty (TwoPointing α) ↔ Nontrivial α :=
  ⟨fun ⟨p⟩ => p.to_nontrivial, fun _ => inferInstance⟩

section Pi

variable (α) [Nonempty α]

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: : TwoPointing (α -> β) where
  body: q.fst
  snd _ := q.snd
  fst_ne_snd h := q.fst_ne_snd (congr_fun h (Classical.arbitrary α))

@[simp]

中文:
定义 pi
  签名: : TwoPointing (α -> β) where
  定义体: q.fst
  snd _ := q.snd
  fst_ne_snd h := q.fst_ne_snd (congr_fun h (Classical.arbitrary α))

@[simp]

Depends on / 依赖: q.fst
-/
def pi : TwoPointing (α -> β) where
  fst _ := q.fst
  snd _ := q.snd
  fst_ne_snd h := q.fst_ne_snd (congr_fun h (Classical.arbitrary α))

@[simp]
/--
theorem `pi_fst` / 定理 `pi_fst`

English:
theorem pi_fst
  statement: (q.pi α).fst = const α q.fst
  proof: rfl

@[simp]

中文:
定理 pi_fst
  结论: (q.pi α).fst = const α q.fst
  证明: rfl

@[simp]
-/
theorem pi_fst : (q.pi α).fst = const α q.fst :=
  rfl

@[simp]
/--
theorem `pi_snd` / 定理 `pi_snd`

English:
theorem pi_snd
  statement: (q.pi α).snd = const α q.snd
  proof: rfl

中文:
定理 pi_snd
  结论: (q.pi α).snd = const α q.snd
  证明: rfl
-/
theorem pi_snd : (q.pi α).snd = const α q.snd :=
  rfl

end Pi

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : TwoPointing (α × β) where
  body: (p.fst, q.fst)
  snd := (p.snd, q.snd)
  fst_ne_snd h := p.fst_ne_snd (congr_arg Prod.fst h)

@[simp]

中文:
定义 乘积
  签名: : TwoPointing (α × β) where
  定义体: (p.fst, q.fst)
  snd := (p.snd, q.snd)
  fst_ne_snd h := p.fst_ne_snd (congr_arg Prod.fst h)

@[simp]

Depends on / 依赖: p.fst, q.fst
-/
def prod : TwoPointing (α × β) where
  fst := (p.fst, q.fst)
  snd := (p.snd, q.snd)
  fst_ne_snd h := p.fst_ne_snd (congr_arg Prod.fst h)

@[simp]
/--
theorem `prod_fst` / 定理 `prod_fst`

English:
theorem prod_fst
  statement: (p.prod q).fst = (p.fst, q.fst)
  proof: rfl

@[simp]

中文:
定理 prod_fst
  结论: (p.乘积 q).fst = (p.fst, q.fst)
  证明: rfl

@[simp]
-/
theorem prod_fst : (p.prod q).fst = (p.fst, q.fst) :=
  rfl

@[simp]
/--
theorem `prod_snd` / 定理 `prod_snd`

English:
theorem prod_snd
  statement: (p.prod q).snd = (p.snd, q.snd)
  proof: rfl

中文:
定理 prod_snd
  结论: (p.乘积 q).snd = (p.snd, q.snd)
  证明: rfl
-/
theorem prod_snd : (p.prod q).snd = (p.snd, q.snd) :=
  rfl

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: : TwoPointing (α oplus β)
  body: ⟨(Sum.inl p.fst, Sum.inr q.snd), Sum.inl_ne_inr⟩

@[simp]

中文:
定义 求和
  签名: : TwoPointing (α oplus β)
  定义体: ⟨(Sum.inl p.fst, Sum.inr q.snd), Sum.inl_ne_inr⟩

@[simp]
-/
protected def sum : TwoPointing (α oplus β) :=
  ⟨(Sum.inl p.fst, Sum.inr q.snd), Sum.inl_ne_inr⟩

@[simp]
/--
theorem `sum_fst` / 定理 `sum_fst`

English:
theorem sum_fst
  statement: (p.sum q).fst = Sum.inl p.fst
  proof: rfl

@[simp]

中文:
定理 sum_fst
  结论: (p.求和 q).fst = 和.inl p.fst
  证明: rfl

@[simp]
-/
theorem sum_fst : (p.sum q).fst = Sum.inl p.fst :=
  rfl

@[simp]
/--
theorem `sum_snd` / 定理 `sum_snd`

English:
theorem sum_snd
  statement: (p.sum q).snd = Sum.inr q.snd
  proof: rfl

中文:
定理 sum_snd
  结论: (p.求和 q).snd = 和.inr q.snd
  证明: rfl
-/
theorem sum_snd : (p.sum q).snd = Sum.inr q.snd :=
  rfl

/--
Definition of `bool` / `bool` 的定义

English:
definition bool
  signature: : TwoPointing Bool
  body: ⟨(false, true), Bool.false_ne_true⟩

@[simp]

中文:
定义 bool
  签名: : TwoPointing 布尔值
  定义体: ⟨(false, true), Bool.false_ne_true⟩

@[simp]
-/
protected def bool : TwoPointing Bool :=
  ⟨(false, true), Bool.false_ne_true⟩

@[simp]
/--
theorem `bool_fst` / 定理 `bool_fst`

English:
theorem bool_fst
  statement: TwoPointing.bool.fst = false
  proof: rfl

@[simp]

中文:
定理 bool_fst
  结论: TwoPointing.bool.fst = false
  证明: rfl

@[simp]
-/
theorem bool_fst : TwoPointing.bool.fst = false := rfl

@[simp]
/--
theorem `bool_snd` / 定理 `bool_snd`

English:
theorem bool_snd
  statement: TwoPointing.bool.snd = true
  proof: rfl

中文:
定理 bool_snd
  结论: TwoPointing.bool.snd = true
  证明: rfl
-/
theorem bool_snd : TwoPointing.bool.snd = true := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (TwoPointing Bool)
  body: ⟨TwoPointing.bool⟩

中文:
实例 :
  签名: 可居 (TwoPointing 布尔值)
  定义体: ⟨TwoPointing.bool⟩

Depends on / 依赖: TwoPointing, TwoPointing.bool
-/
instance : Inhabited (TwoPointing Bool) :=
  ⟨TwoPointing.bool⟩

/--
Definition of `prop` / `prop` 的定义

English:
definition prop
  signature: : TwoPointing Prop
  body: ⟨(False, True), false_ne_true⟩

@[simp]

中文:
定义 prop
  签名: : TwoPointing 命题
  定义体: ⟨(False, True), false_ne_true⟩

@[simp]
-/
protected def prop : TwoPointing Prop :=
  ⟨(False, True), false_ne_true⟩

@[simp]
/--
theorem `prop_fst` / 定理 `prop_fst`

English:
theorem prop_fst
  statement: TwoPointing.prop.fst = False
  proof: rfl

@[simp]

中文:
定理 prop_fst
  结论: TwoPointing.prop.fst = 假
  证明: rfl

@[simp]
-/
theorem prop_fst : TwoPointing.prop.fst = False :=
  rfl

@[simp]
/--
theorem `prop_snd` / 定理 `prop_snd`

English:
theorem prop_snd
  statement: TwoPointing.prop.snd = True
  proof: rfl

中文:
定理 prop_snd
  结论: TwoPointing.prop.snd = 真
  证明: rfl
-/
theorem prop_snd : TwoPointing.prop.snd = True :=
  rfl

end TwoPointing
