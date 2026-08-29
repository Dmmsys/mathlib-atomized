/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Hom.Set

/-!
# Lemmas about images of intervals under order isomorphisms.
-/

@[expose] public section

open Set

namespace OrderIso

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β]

@[to_dual (attr := simp)]
/--
theorem `preimage_Iic` / 定理 `preimage_Iic`

English:
theorem preimage_Iic
  given: (e : α ≃o β) (b : β)
  statement: e ⁻¹' Iic b = Iic (e.symm b)
  proof: by
  ext x
  simp [← e.le_iff_le]

@[to_dual (attr := simp)]

中文:
定理 preimage_Iic
  条件: (e : α ≃o β) (b : β)
  结论: e ⁻¹' Iic b = Iic (e.symm b)
  证明: by
  ext x
  simp [← e.le_iff_le]

@[to_dual (attr := simp)]

Depends on / 依赖: e.le_iff_le, le_iff_le
-/
theorem preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' Iic b = Iic (e.symm b) := by
  ext x
  simp [← e.le_iff_le]

@[to_dual (attr := simp)]
/--
theorem `preimage_Iio` / 定理 `preimage_Iio`

English:
theorem preimage_Iio
  given: (e : α ≃o β) (b : β)
  statement: e ⁻¹' Iio b = Iio (e.symm b)
  proof: by
  ext x
  simp [← e.lt_iff_lt]

@[simp, to_dual self]

中文:
定理 preimage_Iio
  条件: (e : α ≃o β) (b : β)
  结论: e ⁻¹' Iio b = Iio (e.symm b)
  证明: by
  ext x
  simp [← e.lt_iff_lt]

@[simp, to_dual self]

Depends on / 依赖: e.lt_iff_lt, lt_iff_lt
-/
theorem preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' Iio b = Iio (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]

@[simp, to_dual self]
/--
theorem `preimage_Icc` / 定理 `preimage_Icc`

English:
theorem preimage_Icc
  given: (e : α ≃o β) (a b : β)
  statement: e ⁻¹' Icc a b = Icc (e.symm a) (e.symm b)
  proof: by
  simp [← Ici_inter_Iic]

@[to_dual (attr := simp) (reorder := a b)]

中文:
定理 preimage_Icc
  条件: (e : α ≃o β) (a b : β)
  结论: e ⁻¹' Icc a b = Icc (e.symm a) (e.symm b)
  证明: by
  simp [← Ici_inter_Iic]

@[to_dual (attr := simp) (reorder := a b)]

Depends on / 依赖: Ici_inter_Iic
-/
theorem preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' Icc a b = Icc (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iic]

@[to_dual (attr := simp) (reorder := a b)]
/--
theorem `preimage_Ico` / 定理 `preimage_Ico`

English:
theorem preimage_Ico
  given: (e : α ≃o β) (a b : β)
  statement: e ⁻¹' Ico a b = Ico (e.symm a) (e.symm b)
  proof: by
  simp [← Ici_inter_Iio]

@[simp, to_dual self]

中文:
定理 preimage_Ico
  条件: (e : α ≃o β) (a b : β)
  结论: e ⁻¹' Ico a b = Ico (e.symm a) (e.symm b)
  证明: by
  simp [← Ici_inter_Iio]

@[simp, to_dual self]

Depends on / 依赖: Ici_inter_Iio
-/
theorem preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' Ico a b = Ico (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iio]

@[simp, to_dual self]
/--
theorem `preimage_Ioo` / 定理 `preimage_Ioo`

English:
theorem preimage_Ioo
  given: (e : α ≃o β) (a b : β)
  statement: e ⁻¹' Ioo a b = Ioo (e.symm a) (e.symm b)
  proof: by
  simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]

中文:
定理 preimage_Ioo
  条件: (e : α ≃o β) (a b : β)
  结论: e ⁻¹' Ioo a b = Ioo (e.symm a) (e.symm b)
  证明: by
  simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_inter_Iio
-/
theorem preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' Ioo a b = Ioo (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]
/--
theorem `image_Iic` / 定理 `image_Iic`

English:
theorem image_Iic
  given: (e : α ≃o β) (a : α)
  statement: e '' Iic a = Iic (e a)
  proof: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Iic]; rw [e.symm_symm]

@[to_dual (attr := simp)]

中文:
定理 image_Iic
  条件: (e : α ≃o β) (a : α)
  结论: e '' Iic a = Iic (e a)
  证明: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Iic]; rw [e.symm_symm]

@[to_dual (attr := simp)]

Depends on / 依赖: e.image_eq_preimage_symm, e.symm.preimage_Iic, e.symm_symm, image_eq_preimage_symm, preimage_Iic, symm_symm
-/
theorem image_Iic (e : α ≃o β) (a : α) : e '' Iic a = Iic (e a) := by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Iic]; rw [e.symm_symm]

@[to_dual (attr := simp)]
/--
theorem `image_Iio` / 定理 `image_Iio`

English:
theorem image_Iio
  given: (e : α ≃o β) (a : α)
  statement: e '' Iio a = Iio (e a)
  proof: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Iio]; rw [e.symm_symm]

@[simp, to_dual self]

中文:
定理 image_Iio
  条件: (e : α ≃o β) (a : α)
  结论: e '' Iio a = Iio (e a)
  证明: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Iio]; rw [e.symm_symm]

@[simp, to_dual self]

Depends on / 依赖: e.image_eq_preimage_symm, e.symm.preimage_Iio, e.symm_symm, image_eq_preimage_symm, preimage_Iio, symm_symm
-/
theorem image_Iio (e : α ≃o β) (a : α) : e '' Iio a = Iio (e a) := by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Iio]; rw [e.symm_symm]

@[simp, to_dual self]
/--
theorem `image_Ioo` / 定理 `image_Ioo`

English:
theorem image_Ioo
  given: (e : α ≃o β) (a b : α)
  statement: e '' Ioo a b = Ioo (e a) (e b)
  proof: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Ioo]; rw [e.symm_symm]

@[to_dual (attr := simp) (reorder := a b)]

中文:
定理 image_Ioo
  条件: (e : α ≃o β) (a b : α)
  结论: e '' Ioo a b = Ioo (e a) (e b)
  证明: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Ioo]; rw [e.symm_symm]

@[to_dual (attr := simp) (reorder := a b)]

Depends on / 依赖: e.image_eq_preimage_symm, e.symm.preimage_Ioo, e.symm_symm, image_eq_preimage_symm, preimage_Ioo, symm_symm
-/
theorem image_Ioo (e : α ≃o β) (a b : α) : e '' Ioo a b = Ioo (e a) (e b) := by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Ioo]; rw [e.symm_symm]

@[to_dual (attr := simp) (reorder := a b)]
/--
theorem `image_Ioc` / 定理 `image_Ioc`

English:
theorem image_Ioc
  given: (e : α ≃o β) (a b : α)
  statement: e '' Ioc a b = Ioc (e a) (e b)
  proof: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Ioc]; rw [e.symm_symm]

@[simp, to_dual self]

中文:
定理 image_Ioc
  条件: (e : α ≃o β) (a b : α)
  结论: e '' Ioc a b = Ioc (e a) (e b)
  证明: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Ioc]; rw [e.symm_symm]

@[simp, to_dual self]

Depends on / 依赖: e.image_eq_preimage_symm, e.symm.preimage_Ioc, e.symm_symm, image_eq_preimage_symm, preimage_Ioc, symm_symm
-/
theorem image_Ioc (e : α ≃o β) (a b : α) : e '' Ioc a b = Ioc (e a) (e b) := by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Ioc]; rw [e.symm_symm]

@[simp, to_dual self]
/--
theorem `image_Icc` / 定理 `image_Icc`

English:
theorem image_Icc
  given: (e : α ≃o β) (a b : α)
  statement: e '' Icc a b = Icc (e a) (e b)
  proof: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Icc]; rw [e.symm_symm]

中文:
定理 image_Icc
  条件: (e : α ≃o β) (a b : α)
  结论: e '' Icc a b = Icc (e a) (e b)
  证明: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Icc]; rw [e.symm_symm]

Depends on / 依赖: e.image_eq_preimage_symm, e.symm.preimage_Icc, e.symm_symm, image_eq_preimage_symm, preimage_Icc, symm_symm
-/
theorem image_Icc (e : α ≃o β) (a b : α) : e '' Icc a b = Icc (e a) (e b) := by
  rw [e.image_eq_preimage_symm]; rw [e.symm.preimage_Icc]; rw [e.symm_symm]

end Preorder

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
@[to_dual
/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/]
/--
Definition of `IicTop` / `IicTop` 的定义

English:
definition IicTop
  signature: {α : Type*} [Preorder α] [OrderTop α]
  body: { @Equiv.subtypeUnivEquiv α (· in Iic (⊤ : α)) fun _ => le_top with
    map_rel_iff' := @fun x y => by rfl }

中文:
定义 IicTop
  签名: {α : 类型} [Preorder α] [OrderTop α]
  定义体: { @Equiv.subtypeUnivEquiv α (· in Iic (⊤ : α)) fun _ => le_top with
    map_rel_iff' := @fun x y => by rfl }

Depends on / 依赖: Equiv.subtypeUnivEquiv, le_top, map_rel_iff, subtypeUnivEquiv
-/
def IicTop {α : Type*} [Preorder α] [OrderTop α] : Iic (⊤ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (· in Iic (⊤ : α)) fun _ => le_top with
    map_rel_iff' := @fun x y => by rfl }

end OrderIso
