/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.InitialSeg

/-!
# Intervals as initial segments

We show that `Iic` and `Iio` are respectively initial and principal segments, and that any principal
segment `f` is order isomorphic to `Iio f.top`.
-/

@[expose] public section

namespace Set

variable {α : Type*} [Preorder α] {i j : α}

set_option backward.isDefEq.respectTransparency false in
/-- `Iic j` is an initial segment. -/
@[simps]
/--
Definition of `initialSegIic` / `initialSegIic` 的定义

English:
definition initialSegIic
  signature: (j : α)
  body: j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := by simpa using h.le.trans x.2

中文:
定义 initialSegIic
  签名: (j : α)
  定义体: j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := by simpa using h.le.trans x.2
-/
def initialSegIic (j : α) : Iic j <=i α where
  toFun j := j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := by simpa using h.le.trans x.2

/-- `Iio j` is a principal segment. -/
@[simps]
/--
Definition of `principalSegIio` / `principalSegIio` 的定义

English:
definition principalSegIio
  signature: (j : α)
  body: j
  toFun j := j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]

中文:
定义 principalSegIio
  签名: (j : α)
  定义体: j
  toFun j := j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]
-/
def principalSegIio (j : α) : Iio j <i α where
  top := j
  toFun j := j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]
/--
lemma `principalSegIio_apply` / 引理 `principalSegIio_apply`

English:
lemma principalSegIio_apply
  given: (k : Iio j)
  statement: principalSegIio j k = k.1
  proof: rfl

@[deprecated (since := "2026-04-12")]
alias principalSegIio_toRelEmbedding := principalSegIio_apply

中文:
引理 principalSegIio_apply
  条件: (k : 左无界右开区间 j)
  结论: principalSegIio j k = k.1
  证明: rfl

@[deprecated (since := "2026-04-12")]
alias principalSegIio_toRelEmbedding := principalSegIio_apply
-/
lemma principalSegIio_apply (k : Iio j) : principalSegIio j k = k.1 :=
  rfl

@[deprecated (since := "2026-04-12")]
alias principalSegIio_toRelEmbedding := principalSegIio_apply

set_option backward.isDefEq.respectTransparency false in
/-- If `i ≤ j`, then `Iic i` is an initial segment of `Iic j`. -/
@[simps]
/--
Definition of `initialSegIicIicOfLE` / `initialSegIicIicOfLE` 的定义

English:
definition initialSegIicIicOfLE
  signature: (h : i <= j)
  body: ⟨k, k.2.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := ⟨⟨k.1, (Subtype.coe_le_coe.2 h.le).trans x.2⟩, rfl⟩

中文:
定义 initialSegIicIicOfLE
  签名: (h : i <= j)
  定义体: ⟨k, k.2.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := ⟨⟨k.1, (Subtype.coe_le_coe.2 h.le).trans x.2⟩, rfl⟩
-/
def initialSegIicIicOfLE (h : i <= j) : Iic i <=i Iic j where
  toFun k := ⟨k, k.2.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := ⟨⟨k.1, (Subtype.coe_le_coe.2 h.le).trans x.2⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `i ≤ j`, then `Iio i` is a principal segment of `Iic j`. -/
@[simps top]
/--
Definition of `principalSegIioIicOfLE` / `principalSegIioIicOfLE` 的定义

English:
definition principalSegIioIicOfLE
  signature: (h : i <= j)
  body: ⟨i, h⟩
  toFun k := ⟨k, k.2.le.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]

中文:
定义 principalSegIioIicOfLE
  签名: (h : i <= j)
  定义体: ⟨i, h⟩
  toFun k := ⟨k, k.2.le.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]
-/
def principalSegIioIicOfLE (h : i <= j) : Iio i <i Iic j where
  top := ⟨i, h⟩
  toFun k := ⟨k, k.2.le.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]
/--
lemma `principalSegIioIicOfLE_apply` / 引理 `principalSegIioIicOfLE_apply`

English:
lemma principalSegIioIicOfLE_apply
  given: (h : i <= j) (k : Iio i)
  proof: rfl

@[deprecated (since := "2026-04-12")]
alias principalSegIioIicOfLE_toRelEmbedding := principalSegIioIicOfLE_apply

中文:
引理 principalSegIioIicOfLE_apply
  条件: (h : i <= j) (k : 左无界右开区间 i)
  证明: rfl

@[deprecated (since := "2026-04-12")]
alias principalSegIioIicOfLE_toRelEmbedding := principalSegIioIicOfLE_apply
-/
lemma principalSegIioIicOfLE_apply (h : i <= j) (k : Iio i) :
    principalSegIioIicOfLE h k = ⟨k, k.2.le.trans h⟩ := rfl

@[deprecated (since := "2026-04-12")]
alias principalSegIioIicOfLE_toRelEmbedding := principalSegIioIicOfLE_apply

end Set

set_option backward.isDefEq.respectTransparency false in
/-- If `f : α <i β` is a principal segment, this is the induced order
isomorphism `α ≃o Iio f.top`. -/
@[simps! apply_coe]
/--
Definition of `PrincipalSeg.orderIsoIio` / `PrincipalSeg.orderIsoIio` 的定义

English:
definition PrincipalSeg.orderIsoIio
  signature: {α β : Type*} [PartialOrder α] [PartialOrder β]
  body: .ofRelIsoLT f.subrelIso.symm

中文:
定义 主段.orderIsoIio
  签名: {α β : 类型} [偏序 α] [偏序 β]
  定义体: .ofRelIsoLT f.subrelIso.symm

Depends on / 依赖: f.subrelIso.symm, ofRelIsoLT, subrelIso
-/
noncomputable def PrincipalSeg.orderIsoIio {α β : Type*} [PartialOrder α] [PartialOrder β]
    (f : α <i β) : α ≃o Set.Iio f.top :=
  .ofRelIsoLT f.subrelIso.symm
