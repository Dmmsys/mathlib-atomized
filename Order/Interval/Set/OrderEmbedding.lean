/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.Hom.Basic

/-!
# Preimages of intervals under order embeddings

In this file we prove that the preimage of an interval in the codomain under an `OrderEmbedding`
is an interval in the domain.

Note that similar statements about images require the range to be order-connected.
-/

public section

open Set

namespace OrderEmbedding

variable {α β : Type*}

section Preorder

variable [Preorder α] [Preorder β] (e : α ↪o β) (x y : α)

/--
theorem `preimage_Ici` / 定理 `preimage_Ici`

English:
theorem preimage_Ici
  statement: e ⁻¹' Ici (e x) = Ici x
  proof: ext fun _ => e.le_iff_le

中文:
定理 preimage_Ici
  结论: e ⁻¹' Ici (e x) = Ici x
  证明: ext fun _ => e.le_iff_le
-/
@[to_dual (attr := simp)] theorem preimage_Ici : e ⁻¹' Ici (e x) = Ici x := ext fun _ => e.le_iff_le
/--
theorem `preimage_Ioi` / 定理 `preimage_Ioi`

English:
theorem preimage_Ioi
  statement: e ⁻¹' Ioi (e x) = Ioi x
  proof: ext fun _ => e.lt_iff_lt

中文:
定理 preimage_Ioi
  结论: e ⁻¹' Ioi (e x) = Ioi x
  证明: ext fun _ => e.lt_iff_lt
-/
@[to_dual (attr := simp)] theorem preimage_Ioi : e ⁻¹' Ioi (e x) = Ioi x := ext fun _ => e.lt_iff_lt

/--
theorem `preimage_Icc` / 定理 `preimage_Icc`

English:
theorem preimage_Icc
  statement: e ⁻¹' Icc (e x) (e y) = Icc x y
  proof: by ext; simp

中文:
定理 preimage_Icc
  结论: e ⁻¹' Icc (e x) (e y) = Icc x y
  证明: by ext; simp
-/
@[simp] theorem preimage_Icc : e ⁻¹' Icc (e x) (e y) = Icc x y := by ext; simp
/--
theorem `preimage_Ico` / 定理 `preimage_Ico`

English:
theorem preimage_Ico
  statement: e ⁻¹' Ico (e x) (e y) = Ico x y
  proof: by ext; simp

中文:
定理 preimage_Ico
  结论: e ⁻¹' Ico (e x) (e y) = Ico x y
  证明: by ext; simp
-/
@[simp] theorem preimage_Ico : e ⁻¹' Ico (e x) (e y) = Ico x y := by ext; simp
/--
theorem `preimage_Ioc` / 定理 `preimage_Ioc`

English:
theorem preimage_Ioc
  statement: e ⁻¹' Ioc (e x) (e y) = Ioc x y
  proof: by ext; simp

中文:
定理 preimage_Ioc
  结论: e ⁻¹' Ioc (e x) (e y) = Ioc x y
  证明: by ext; simp
-/
@[simp] theorem preimage_Ioc : e ⁻¹' Ioc (e x) (e y) = Ioc x y := by ext; simp
/--
theorem `preimage_Ioo` / 定理 `preimage_Ioo`

English:
theorem preimage_Ioo
  statement: e ⁻¹' Ioo (e x) (e y) = Ioo x y
  proof: by ext; simp

中文:
定理 preimage_Ioo
  结论: e ⁻¹' Ioo (e x) (e y) = Ioo x y
  证明: by ext; simp
-/
@[simp] theorem preimage_Ioo : e ⁻¹' Ioo (e x) (e y) = Ioo x y := by ext; simp

end Preorder

variable [LinearOrder α]

/--
theorem `preimage_uIcc` / 定理 `preimage_uIcc`

English:
theorem preimage_uIcc
  given: [Lattice β] (e : α ↪o β) (x y : α)
  proof: by
  cases le_total x y <;> simp [*]

中文:
定理 preimage_uIcc
  条件: [Lattice β] (e : α ↪o β) (x y : α)
  证明: by
  cases le_total x y <;> simp [*]
-/
@[simp] theorem preimage_uIcc [Lattice β] (e : α ↪o β) (x y : α) :
    e ⁻¹' (uIcc (e x) (e y)) = uIcc x y := by
  cases le_total x y <;> simp [*]

/--
theorem `preimage_uIoc` / 定理 `preimage_uIoc`

English:
theorem preimage_uIoc
  given: [LinearOrder β] (e : α ↪o β) (x y : α)
  proof: by
  cases le_total x y <;> simp [*]

中文:
定理 preimage_uIoc
  条件: [LinearOrder β] (e : α ↪o β) (x y : α)
  证明: by
  cases le_total x y <;> simp [*]

Depends on / 依赖: IsTwoSided, N.colon, Submodule
-/
@[simp] theorem preimage_uIoc [LinearOrder β] (e : α ↪o β) (x y : α) :
    e ⁻¹' (uIoc (e x) (e y)) = uIoc x y := by
  cases le_total x y <;> simp [*]

end OrderEmbedding
