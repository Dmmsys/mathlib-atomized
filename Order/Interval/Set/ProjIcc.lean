/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Projection of a line onto a closed interval

Given a linearly ordered type `α`, in this file we define

* `Set.projIci (a : α)` to be the map `α → [a, ∞)` sending `(-∞, a]` to `a`, and each point
  `x ∈ [a, ∞)` to itself;
* `Set.projIic (b : α)` to be the map `α → (-∞, b[` sending `[b, ∞)` to `b`, and each point
  `x ∈ (-∞, b]` to itself;
* `Set.projIcc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `Set.IccExtend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIcc a b h`.
* `Set.IciExtend {a : α} (f : Ici a → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIci a`.
* `Set.IicExtend {b : α} (f : Iic b → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIic b`.

We also prove some trivial properties of these maps.
-/

@[expose] public section


variable {α β : Type*} [LinearOrder α]

open Function

namespace Set

/--
Definition of `projIci` / `projIci` 的定义

English:
definition projIci
  signature: (a x : α)
  body: ⟨max a x, le_max_left _ _⟩

中文:
定义 projIci
  签名: (a x : α)
  定义体: ⟨max a x, le_max_left _ _⟩

Depends on / 依赖: le_max_left
-/
def projIci (a x : α) : Ici a := ⟨max a x, le_max_left _ _⟩

/--
Definition of `projIic` / `projIic` 的定义

English:
definition projIic
  signature: (b x : α)
  body: ⟨min b x, min_le_left _ _⟩

中文:
定义 projIic
  签名: (b x : α)
  定义体: ⟨min b x, min_le_left _ _⟩

Depends on / 依赖: min_le_left
-/
def projIic (b x : α) : Iic b := ⟨min b x, min_le_left _ _⟩

/--
Definition of `projIcc` / `projIcc` 的定义

English:
definition projIcc
  signature: (a b : α) (h : a <= b) (x : α)
  body: ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩

中文:
定义 projIcc
  签名: (a b : α) (h : a <= b) (x : α)
  定义体: ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩

Depends on / 依赖: le_max_left, max_le, min_le_left
-/
def projIcc (a b : α) (h : a <= b) (x : α) : Icc a b :=
  ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩

variable {a b : α} (h : a <= b) {x : α}

@[norm_cast]
/--
theorem `coe_projIci` / 定理 `coe_projIci`

English:
theorem coe_projIci
  given: (a x : α)
  statement: (projIci a x : α) = max a x
  proof: rfl

@[norm_cast]

中文:
定理 coe_projIci
  条件: (a x : α)
  结论: (projIci a x : α) = 最大值 a x
  证明: rfl

@[norm_cast]
-/
theorem coe_projIci (a x : α) : (projIci a x : α) = max a x := rfl

@[norm_cast]
/--
theorem `coe_projIic` / 定理 `coe_projIic`

English:
theorem coe_projIic
  given: (b x : α)
  statement: (projIic b x : α) = min b x
  proof: rfl

@[norm_cast]

中文:
定理 coe_projIic
  条件: (b x : α)
  结论: (projIic b x : α) = 最小值 b x
  证明: rfl

@[norm_cast]
-/
theorem coe_projIic (b x : α) : (projIic b x : α) = min b x := rfl

@[norm_cast]
/--
theorem `coe_projIcc` / 定理 `coe_projIcc`

English:
theorem coe_projIcc
  given: (a b : α) (h : a <= b) (x : α)
  statement: (projIcc a b h x : α) = max a (min b x)
  proof: rfl

中文:
定理 coe_projIcc
  条件: (a b : α) (h : a <= b) (x : α)
  结论: (projIcc a b h x : α) = 最大值 a (最小值 b x)
  证明: rfl
-/
theorem coe_projIcc (a b : α) (h : a <= b) (x : α) : (projIcc a b h x : α) = max a (min b x) := rfl

/--
theorem `projIci_of_le` / 定理 `projIci_of_le`

English:
theorem projIci_of_le
  given: (hx : x <= a)
  statement: projIci a x = ⟨a, le_rfl⟩
  proof: Subtype.ext max_eq_left hx

中文:
定理 projIci_of_le
  条件: (hx : x <= a)
  结论: projIci a x = ⟨a, le_rfl⟩
  证明: Subtype.ext max_eq_left hx

Depends on / 依赖: Subtype, Subtype.ext, max_eq_left
-/
theorem projIci_of_le (hx : x <= a) : projIci a x = ⟨a, le_rfl⟩ := Subtype.ext max_eq_left hx

/--
theorem `projIic_of_le` / 定理 `projIic_of_le`

English:
theorem projIic_of_le
  given: (hx : b <= x)
  statement: projIic b x = ⟨b, le_rfl⟩
  proof: Subtype.ext min_eq_left hx

中文:
定理 projIic_of_le
  条件: (hx : b <= x)
  结论: projIic b x = ⟨b, le_rfl⟩
  证明: Subtype.ext min_eq_left hx

Depends on / 依赖: Subtype, Subtype.ext, min_eq_left
-/
theorem projIic_of_le (hx : b <= x) : projIic b x = ⟨b, le_rfl⟩ := Subtype.ext min_eq_left hx

/--
theorem `projIcc_of_le_left` / 定理 `projIcc_of_le_left`

English:
theorem projIcc_of_le_left
  given: (hx : x <= a)
  statement: projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩
  proof: by
  simp [projIcc, hx, hx.trans h]

中文:
定理 projIcc_of_le_left
  条件: (hx : x <= a)
  结论: projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩
  证明: by
  simp [projIcc, hx, hx.trans h]

Depends on / 依赖: hx.trans, projIcc
-/
theorem projIcc_of_le_left (hx : x <= a) : projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩ := by
  simp [projIcc, hx, hx.trans h]

/--
theorem `projIcc_of_right_le` / 定理 `projIcc_of_right_le`

English:
theorem projIcc_of_right_le
  given: (hx : b <= x)
  statement: projIcc a b h x = ⟨b, right_mem_Icc.2 h⟩
  proof: by
  simp [projIcc, hx, h]

@[simp]

中文:
定理 projIcc_of_right_le
  条件: (hx : b <= x)
  结论: projIcc a b h x = ⟨b, right_mem_Icc.2 h⟩
  证明: by
  simp [projIcc, hx, h]

@[simp]

Depends on / 依赖: projIcc
-/
theorem projIcc_of_right_le (hx : b <= x) : projIcc a b h x = ⟨b, right_mem_Icc.2 h⟩ := by
  simp [projIcc, hx, h]

@[simp]
/--
theorem `projIci_self` / 定理 `projIci_self`

English:
theorem projIci_self
  given: (a : α)
  statement: projIci a a = ⟨a, le_rfl⟩
  proof: projIci_of_le le_rfl

@[simp]

中文:
定理 projIci_self
  条件: (a : α)
  结论: projIci a a = ⟨a, le_rfl⟩
  证明: projIci_of_le le_rfl

@[simp]

Depends on / 依赖: le_rfl, projIci_of_le
-/
theorem projIci_self (a : α) : projIci a a = ⟨a, le_rfl⟩ := projIci_of_le le_rfl

@[simp]
/--
theorem `projIic_self` / 定理 `projIic_self`

English:
theorem projIic_self
  given: (b : α)
  statement: projIic b b = ⟨b, le_rfl⟩
  proof: projIic_of_le le_rfl

@[simp]

中文:
定理 projIic_self
  条件: (b : α)
  结论: projIic b b = ⟨b, le_rfl⟩
  证明: projIic_of_le le_rfl

@[simp]

Depends on / 依赖: le_rfl, projIic_of_le
-/
theorem projIic_self (b : α) : projIic b b = ⟨b, le_rfl⟩ := projIic_of_le le_rfl

@[simp]
/--
theorem `projIcc_left` / 定理 `projIcc_left`

English:
theorem projIcc_left
  statement: projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩
  proof: projIcc_of_le_left h le_rfl

@[simp]

中文:
定理 projIcc_left
  结论: projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩
  证明: projIcc_of_le_left h le_rfl

@[simp]

Depends on / 依赖: le_rfl, projIcc_of_le_left
-/
theorem projIcc_left : projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩ :=
  projIcc_of_le_left h le_rfl

@[simp]
/--
theorem `projIcc_right` / 定理 `projIcc_right`

English:
theorem projIcc_right
  statement: projIcc a b h b = ⟨b, right_mem_Icc.2 h⟩
  proof: projIcc_of_right_le h le_rfl

中文:
定理 projIcc_right
  结论: projIcc a b h b = ⟨b, right_mem_Icc.2 h⟩
  证明: projIcc_of_right_le h le_rfl

Depends on / 依赖: le_rfl, projIcc_of_right_le
-/
theorem projIcc_right : projIcc a b h b = ⟨b, right_mem_Icc.2 h⟩ :=
  projIcc_of_right_le h le_rfl

/--
theorem `projIci_eq_self` / 定理 `projIci_eq_self`

English:
theorem projIci_eq_self
  statement: projIci a x = ⟨a, le_rfl⟩ ↔ x <= a
  proof: by simp [projIci, Subtype.ext_iff]

中文:
定理 projIci_eq_self
  结论: projIci a x = ⟨a, le_rfl⟩ ↔ x <= a
  证明: by simp [projIci, Subtype.ext_iff]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, projIci
-/
theorem projIci_eq_self : projIci a x = ⟨a, le_rfl⟩ ↔ x <= a := by simp [projIci, Subtype.ext_iff]

/--
theorem `projIic_eq_self` / 定理 `projIic_eq_self`

English:
theorem projIic_eq_self
  statement: projIic b x = ⟨b, le_rfl⟩ ↔ b <= x
  proof: by simp [projIic, Subtype.ext_iff]

中文:
定理 projIic_eq_self
  结论: projIic b x = ⟨b, le_rfl⟩ ↔ b <= x
  证明: by simp [projIic, Subtype.ext_iff]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, projIic
-/
theorem projIic_eq_self : projIic b x = ⟨b, le_rfl⟩ ↔ b <= x := by simp [projIic, Subtype.ext_iff]

/--
theorem `projIcc_eq_left` / 定理 `projIcc_eq_left`

English:
theorem projIcc_eq_left
  given: (h : a < b)
  statement: projIcc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x <= a
  proof: by
  simp [projIcc, Subtype.ext_iff, h.not_ge]

中文:
定理 projIcc_eq_left
  条件: (h : a < b)
  结论: projIcc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x <= a
  证明: by
  simp [projIcc, Subtype.ext_iff, h.not_ge]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, h.not_ge, not_ge, projIcc
-/
theorem projIcc_eq_left (h : a < b) : projIcc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x <= a := by
  simp [projIcc, Subtype.ext_iff, h.not_ge]

/--
theorem `projIcc_eq_right` / 定理 `projIcc_eq_right`

English:
theorem projIcc_eq_right
  given: (h : a < b)
  statement: projIcc a b h.le x = ⟨b, right_mem_Icc.2 h.le⟩ ↔ b <= x
  proof: by
  simp [projIcc, Subtype.ext_iff, max_min_distrib_left, h.le, h.not_ge]

中文:
定理 projIcc_eq_right
  条件: (h : a < b)
  结论: projIcc a b h.le x = ⟨b, right_mem_Icc.2 h.le⟩ ↔ b <= x
  证明: by
  simp [projIcc, Subtype.ext_iff, max_min_distrib_left, h.le, h.not_ge]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, h.le, h.not_ge, max_min_distrib_left, not_ge, projIcc
-/
theorem projIcc_eq_right (h : a < b) : projIcc a b h.le x = ⟨b, right_mem_Icc.2 h.le⟩ ↔ b <= x := by
  simp [projIcc, Subtype.ext_iff, max_min_distrib_left, h.le, h.not_ge]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `projIci_of_mem` / 定理 `projIci_of_mem`

English:
theorem projIci_of_mem
  given: (hx : x in Ici a)
  statement: projIci a x = ⟨x, hx⟩
  proof: by simpa [projIci]

中文:
定理 projIci_of_mem
  条件: (hx : x in 左闭右无界区间 a)
  结论: projIci a x = ⟨x, hx⟩
  证明: by simpa [projIci]

Depends on / 依赖: projIci
-/
theorem projIci_of_mem (hx : x in Ici a) : projIci a x = ⟨x, hx⟩ := by simpa [projIci]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `projIic_of_mem` / 定理 `projIic_of_mem`

English:
theorem projIic_of_mem
  given: (hx : x in Iic b)
  statement: projIic b x = ⟨x, hx⟩
  proof: by simpa [projIic]

中文:
定理 projIic_of_mem
  条件: (hx : x in 左无界右闭区间 b)
  结论: projIic b x = ⟨x, hx⟩
  证明: by simpa [projIic]

Depends on / 依赖: projIic
-/
theorem projIic_of_mem (hx : x in Iic b) : projIic b x = ⟨x, hx⟩ := by simpa [projIic]

/--
theorem `projIcc_of_mem` / 定理 `projIcc_of_mem`

English:
theorem projIcc_of_mem
  given: (hx : x in Icc a b)
  statement: projIcc a b h x = ⟨x, hx⟩
  proof: by
  simp [projIcc, hx.1, hx.2]

@[simp]

中文:
定理 projIcc_of_mem
  条件: (hx : x in 闭区间 a b)
  结论: projIcc a b h x = ⟨x, hx⟩
  证明: by
  simp [projIcc, hx.1, hx.2]

@[simp]

Depends on / 依赖: projIcc
-/
theorem projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x = ⟨x, hx⟩ := by
  simp [projIcc, hx.1, hx.2]

@[simp]
/--
theorem `projIci_coe` / 定理 `projIci_coe`

English:
theorem projIci_coe
  given: (x : Ici a)
  statement: projIci a x = x
  proof: by cases x; apply projIci_of_mem

@[simp]

中文:
定理 projIci_coe
  条件: (x : 左闭右无界区间 a)
  结论: projIci a x = x
  证明: by cases x; apply projIci_of_mem

@[simp]

Depends on / 依赖: projIci_of_mem
-/
theorem projIci_coe (x : Ici a) : projIci a x = x := by cases x; apply projIci_of_mem

@[simp]
/--
theorem `projIic_coe` / 定理 `projIic_coe`

English:
theorem projIic_coe
  given: (x : Iic b)
  statement: projIic b x = x
  proof: by cases x; apply projIic_of_mem

@[simp]

中文:
定理 projIic_coe
  条件: (x : 左无界右闭区间 b)
  结论: projIic b x = x
  证明: by cases x; apply projIic_of_mem

@[simp]

Depends on / 依赖: projIic_of_mem
-/
theorem projIic_coe (x : Iic b) : projIic b x = x := by cases x; apply projIic_of_mem

@[simp]
/--
theorem `projIcc_val` / 定理 `projIcc_val`

English:
theorem projIcc_val
  given: (x : Icc a b)
  statement: projIcc a b h x = x
  proof: by
  cases x
  apply projIcc_of_mem

中文:
定理 projIcc_val
  条件: (x : 闭区间 a b)
  结论: projIcc a b h x = x
  证明: by
  cases x
  apply projIcc_of_mem

Depends on / 依赖: projIcc_of_mem
-/
theorem projIcc_val (x : Icc a b) : projIcc a b h x = x := by
  cases x
  apply projIcc_of_mem

/--
theorem `projIci_surjOn` / 定理 `projIci_surjOn`

English:
theorem projIci_surjOn
  statement: SurjOn (projIci a) (Ici a) univ
  proof: fun x _ => ⟨x, x.2, projIci_coe x⟩

中文:
定理 projIci_surjOn
  结论: 满射限制 (projIci a) (左闭右无界区间 a) univ
  证明: fun x _ => ⟨x, x.2, projIci_coe x⟩

Depends on / 依赖: projIci_coe
-/
theorem projIci_surjOn : SurjOn (projIci a) (Ici a) univ := fun x _ => ⟨x, x.2, projIci_coe x⟩

/--
theorem `projIic_surjOn` / 定理 `projIic_surjOn`

English:
theorem projIic_surjOn
  statement: SurjOn (projIic b) (Iic b) univ
  proof: fun x _ => ⟨x, x.2, projIic_coe x⟩

中文:
定理 projIic_surjOn
  结论: 满射限制 (projIic b) (左无界右闭区间 b) univ
  证明: fun x _ => ⟨x, x.2, projIic_coe x⟩

Depends on / 依赖: projIic_coe
-/
theorem projIic_surjOn : SurjOn (projIic b) (Iic b) univ := fun x _ => ⟨x, x.2, projIic_coe x⟩

/--
theorem `projIcc_surjOn` / 定理 `projIcc_surjOn`

English:
theorem projIcc_surjOn
  statement: SurjOn (projIcc a b h) (Icc a b) univ
  proof: fun x _ =>
  ⟨x, x.2, projIcc_val h x⟩

中文:
定理 projIcc_surjOn
  结论: 满射限制 (projIcc a b h) (闭区间 a b) univ
  证明: fun x _ =>
  ⟨x, x.2, projIcc_val h x⟩
-/
theorem projIcc_surjOn : SurjOn (projIcc a b h) (Icc a b) univ := fun x _ =>
  ⟨x, x.2, projIcc_val h x⟩

/--
theorem `projIci_surjective` / 定理 `projIci_surjective`

English:
theorem projIci_surjective
  statement: Surjective (projIci a)
  proof: fun x => ⟨x, projIci_coe x⟩

中文:
定理 projIci_surjective
  结论: 满射 (projIci a)
  证明: fun x => ⟨x, projIci_coe x⟩

Depends on / 依赖: projIci_coe
-/
theorem projIci_surjective : Surjective (projIci a) := fun x => ⟨x, projIci_coe x⟩

/--
theorem `projIic_surjective` / 定理 `projIic_surjective`

English:
theorem projIic_surjective
  statement: Surjective (projIic b)
  proof: fun x => ⟨x, projIic_coe x⟩

中文:
定理 projIic_surjective
  结论: 满射 (projIic b)
  证明: fun x => ⟨x, projIic_coe x⟩

Depends on / 依赖: projIic_coe
-/
theorem projIic_surjective : Surjective (projIic b) := fun x => ⟨x, projIic_coe x⟩

/--
theorem `projIcc_surjective` / 定理 `projIcc_surjective`

English:
theorem projIcc_surjective
  statement: Surjective (projIcc a b h)
  proof: fun x => ⟨x, projIcc_val h x⟩

@[simp]

中文:
定理 projIcc_surjective
  结论: 满射 (projIcc a b h)
  证明: fun x => ⟨x, projIcc_val h x⟩

@[simp]

Depends on / 依赖: projIcc_val
-/
theorem projIcc_surjective : Surjective (projIcc a b h) := fun x => ⟨x, projIcc_val h x⟩

@[simp]
/--
theorem `range_projIci` / 定理 `range_projIci`

English:
theorem range_projIci
  statement: range (projIci a) = univ
  proof: projIci_surjective.range_eq

@[simp]

中文:
定理 range_projIci
  结论: range (projIci a) = univ
  证明: projIci_surjective.range_eq

@[simp]

Depends on / 依赖: projIci_surjective, projIci_surjective.range_eq, range_eq
-/
theorem range_projIci : range (projIci a) = univ := projIci_surjective.range_eq

@[simp]
/--
theorem `range_projIic` / 定理 `range_projIic`

English:
theorem range_projIic
  statement: range (projIic a) = univ
  proof: projIic_surjective.range_eq

@[simp]

中文:
定理 range_projIic
  结论: range (projIic a) = univ
  证明: projIic_surjective.range_eq

@[simp]

Depends on / 依赖: projIic_surjective, projIic_surjective.range_eq, range_eq
-/
theorem range_projIic : range (projIic a) = univ := projIic_surjective.range_eq

@[simp]
/--
theorem `range_projIcc` / 定理 `range_projIcc`

English:
theorem range_projIcc
  statement: range (projIcc a b h) = univ
  proof: (projIcc_surjective h).range_eq

中文:
定理 range_projIcc
  结论: range (projIcc a b h) = univ
  证明: (projIcc_surjective h).range_eq

Depends on / 依赖: projIcc_surjective, range_eq
-/
theorem range_projIcc : range (projIcc a b h) = univ :=
  (projIcc_surjective h).range_eq

/--
theorem `monotone_projIci` / 定理 `monotone_projIci`

English:
theorem monotone_projIci
  statement: Monotone (projIci a)
  proof: fun _ _ => max_le_max le_rfl

中文:
定理 monotone_projIci
  结论: 递增 (projIci a)
  证明: fun _ _ => max_le_max le_rfl

Depends on / 依赖: le_rfl, max_le_max
-/
theorem monotone_projIci : Monotone (projIci a) := fun _ _ => max_le_max le_rfl

/--
theorem `monotone_projIic` / 定理 `monotone_projIic`

English:
theorem monotone_projIic
  statement: Monotone (projIic a)
  proof: fun _ _ => min_le_min le_rfl

中文:
定理 monotone_projIic
  结论: 递增 (projIic a)
  证明: fun _ _ => min_le_min le_rfl

Depends on / 依赖: le_rfl, min_le_min
-/
theorem monotone_projIic : Monotone (projIic a) := fun _ _ => min_le_min le_rfl

/--
theorem `monotone_projIcc` / 定理 `monotone_projIcc`

English:
theorem monotone_projIcc
  statement: Monotone (projIcc a b h)
  proof: fun _ _ hxy =>
max_le_max le_rfl min_le_min le_rfl hxy

中文:
定理 monotone_projIcc
  结论: 递增 (projIcc a b h)
  证明: fun _ _ hxy =>
max_le_max le_rfl min_le_min le_rfl hxy
-/
theorem monotone_projIcc : Monotone (projIcc a b h) := fun _ _ hxy =>
max_le_max le_rfl min_le_min le_rfl hxy

/--
theorem `strictMonoOn_projIci` / 定理 `strictMonoOn_projIci`

English:
theorem strictMonoOn_projIci
  statement: StrictMonoOn (projIci a) (Ici a)
  proof: fun x hx y hy hxy => by
  simpa only [projIci_of_mem, hx, hy]

中文:
定理 strictMonoOn_projIci
  结论: StrictMonoOn (projIci a) (左闭右无界区间 a)
  证明: fun x hx y hy hxy => by
  simpa only [projIci_of_mem, hx, hy]

Depends on / 依赖: projIci_of_mem
-/
theorem strictMonoOn_projIci : StrictMonoOn (projIci a) (Ici a) := fun x hx y hy hxy => by
  simpa only [projIci_of_mem, hx, hy]

/--
theorem `strictMonoOn_projIic` / 定理 `strictMonoOn_projIic`

English:
theorem strictMonoOn_projIic
  statement: StrictMonoOn (projIic b) (Iic b)
  proof: fun x hx y hy hxy => by
  simpa only [projIic_of_mem, hx, hy]

中文:
定理 strictMonoOn_projIic
  结论: StrictMonoOn (projIic b) (左无界右闭区间 b)
  证明: fun x hx y hy hxy => by
  simpa only [projIic_of_mem, hx, hy]

Depends on / 依赖: projIic_of_mem
-/
theorem strictMonoOn_projIic : StrictMonoOn (projIic b) (Iic b) := fun x hx y hy hxy => by
  simpa only [projIic_of_mem, hx, hy]

/--
theorem `strictMonoOn_projIcc` / 定理 `strictMonoOn_projIcc`

English:
theorem strictMonoOn_projIcc
  statement: StrictMonoOn (projIcc a b h) (Icc a b)
  proof: fun x hx y hy hxy => by
  simpa only [projIcc_of_mem, hx, hy]

中文:
定理 strictMonoOn_projIcc
  结论: StrictMonoOn (projIcc a b h) (闭区间 a b)
  证明: fun x hx y hy hxy => by
  simpa only [projIcc_of_mem, hx, hy]

Depends on / 依赖: projIcc_of_mem
-/
theorem strictMonoOn_projIcc : StrictMonoOn (projIcc a b h) (Icc a b) := fun x hx y hy hxy => by
  simpa only [projIcc_of_mem, hx, hy]

/--
Definition of `IciExtend` / `IciExtend` 的定义

English:
definition IciExtend
  signature: (f : Ici a -> β)
  body: f ∘ projIci a

中文:
定义 IciExtend
  签名: (f : 左闭右无界区间 a -> β)
  定义体: f ∘ projIci a

Depends on / 依赖: projIci
-/
def IciExtend (f : Ici a -> β) : α -> β :=
  f ∘ projIci a

/--
Definition of `IicExtend` / `IicExtend` 的定义

English:
definition IicExtend
  signature: (f : Iic b -> β)
  body: f ∘ projIic b

中文:
定义 IicExtend
  签名: (f : 左无界右闭区间 b -> β)
  定义体: f ∘ projIic b

Depends on / 依赖: projIic
-/
def IicExtend (f : Iic b -> β) : α -> β :=
  f ∘ projIic b

/--
Definition of `IccExtend` / `IccExtend` 的定义

English:
definition IccExtend
  signature: {a b : α} (h : a <= b) (f : Icc a b -> β)
  body: f ∘ projIcc a b h

中文:
定义 IccExtend
  签名: {a b : α} (h : a <= b) (f : 闭区间 a b -> β)
  定义体: f ∘ projIcc a b h

Depends on / 依赖: projIcc
-/
def IccExtend {a b : α} (h : a <= b) (f : Icc a b -> β) : α -> β :=
  f ∘ projIcc a b h

/--
theorem `IciExtend_apply` / 定理 `IciExtend_apply`

English:
theorem IciExtend_apply
  given: (f : Ici a -> β) (x : α)
  statement: IciExtend f x = f ⟨max a x, le_max_left _ _⟩
  proof: rfl

中文:
定理 IciExtend_apply
  条件: (f : 左闭右无界区间 a -> β) (x : α)
  结论: IciExtend f x = f ⟨最大值 a x, le_max_left _ _⟩
  证明: rfl
-/
theorem IciExtend_apply (f : Ici a -> β) (x : α) : IciExtend f x = f ⟨max a x, le_max_left _ _⟩ :=
  rfl

/--
theorem `IicExtend_apply` / 定理 `IicExtend_apply`

English:
theorem IicExtend_apply
  given: (f : Iic b -> β) (x : α)
  statement: IicExtend f x = f ⟨min b x, min_le_left _ _⟩
  proof: rfl

中文:
定理 IicExtend_apply
  条件: (f : 左无界右闭区间 b -> β) (x : α)
  结论: IicExtend f x = f ⟨最小值 b x, min_le_left _ _⟩
  证明: rfl
-/
theorem IicExtend_apply (f : Iic b -> β) (x : α) : IicExtend f x = f ⟨min b x, min_le_left _ _⟩ :=
  rfl

/--
theorem `IccExtend_apply` / 定理 `IccExtend_apply`

English:
theorem IccExtend_apply
  given: (h : a <= b) (f : Icc a b -> β) (x : α)
  proof: rfl

@[simp]

中文:
定理 IccExtend_apply
  条件: (h : a <= b) (f : 闭区间 a b -> β) (x : α)
  证明: rfl

@[simp]
-/
theorem IccExtend_apply (h : a <= b) (f : Icc a b -> β) (x : α) :
    IccExtend h f x = f ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩ := rfl

@[simp]
/--
theorem `range_IciExtend` / 定理 `range_IciExtend`

English:
theorem range_IciExtend
  given: (f : Ici a -> β)
  statement: range (IciExtend f) = range f
  proof: by
  simp only [IciExtend, range_comp f, range_projIci, image_univ]

@[simp]

中文:
定理 range_IciExtend
  条件: (f : 左闭右无界区间 a -> β)
  结论: range (IciExtend f) = range f
  证明: by
  simp only [IciExtend, range_comp f, range_projIci, image_univ]

@[simp]

Depends on / 依赖: IciExtend, image_univ, range_comp, range_projIci
-/
theorem range_IciExtend (f : Ici a -> β) : range (IciExtend f) = range f := by
  simp only [IciExtend, range_comp f, range_projIci, image_univ]

@[simp]
/--
theorem `range_IicExtend` / 定理 `range_IicExtend`

English:
theorem range_IicExtend
  given: (f : Iic b -> β)
  statement: range (IicExtend f) = range f
  proof: by
  simp only [IicExtend, range_comp f, range_projIic, image_univ]

@[simp]

中文:
定理 range_IicExtend
  条件: (f : 左无界右闭区间 b -> β)
  结论: range (IicExtend f) = range f
  证明: by
  simp only [IicExtend, range_comp f, range_projIic, image_univ]

@[simp]

Depends on / 依赖: IicExtend, image_univ, range_comp, range_projIic
-/
theorem range_IicExtend (f : Iic b -> β) : range (IicExtend f) = range f := by
  simp only [IicExtend, range_comp f, range_projIic, image_univ]

@[simp]
/--
theorem `IccExtend_range` / 定理 `IccExtend_range`

English:
theorem IccExtend_range
  given: (f : Icc a b -> β)
  statement: range (IccExtend h f) = range f
  proof: by
  simp only [IccExtend, range_comp f, range_projIcc, image_univ]

中文:
定理 IccExtend_range
  条件: (f : 闭区间 a b -> β)
  结论: range (IccExtend h f) = range f
  证明: by
  simp only [IccExtend, range_comp f, range_projIcc, image_univ]

Depends on / 依赖: IccExtend, image_univ, range_comp, range_projIcc
-/
theorem IccExtend_range (f : Icc a b -> β) : range (IccExtend h f) = range f := by
  simp only [IccExtend, range_comp f, range_projIcc, image_univ]

/--
theorem `IciExtend_of_le` / 定理 `IciExtend_of_le`

English:
theorem IciExtend_of_le
  given: (f : Ici a -> β) (hx : x <= a)
  statement: IciExtend f x = f ⟨a, le_rfl⟩
  proof: congr_arg f projIci_of_le hx

中文:
定理 IciExtend_of_le
  条件: (f : 左闭右无界区间 a -> β) (hx : x <= a)
  结论: IciExtend f x = f ⟨a, le_rfl⟩
  证明: congr_arg f projIci_of_le hx

Depends on / 依赖: congr_arg, projIci_of_le
-/
theorem IciExtend_of_le (f : Ici a -> β) (hx : x <= a) : IciExtend f x = f ⟨a, le_rfl⟩ :=
congr_arg f projIci_of_le hx

/--
theorem `IicExtend_of_le` / 定理 `IicExtend_of_le`

English:
theorem IicExtend_of_le
  given: (f : Iic b -> β) (hx : b <= x)
  statement: IicExtend f x = f ⟨b, le_rfl⟩
  proof: congr_arg f projIic_of_le hx

中文:
定理 IicExtend_of_le
  条件: (f : 左无界右闭区间 b -> β) (hx : b <= x)
  结论: IicExtend f x = f ⟨b, le_rfl⟩
  证明: congr_arg f projIic_of_le hx

Depends on / 依赖: congr_arg, projIic_of_le
-/
theorem IicExtend_of_le (f : Iic b -> β) (hx : b <= x) : IicExtend f x = f ⟨b, le_rfl⟩ :=
congr_arg f projIic_of_le hx

/--
theorem `IccExtend_of_le_left` / 定理 `IccExtend_of_le_left`

English:
theorem IccExtend_of_le_left
  given: (f : Icc a b -> β) (hx : x <= a)
  proof: congr_arg f projIcc_of_le_left h hx

中文:
定理 IccExtend_of_le_left
  条件: (f : 闭区间 a b -> β) (hx : x <= a)
  证明: congr_arg f projIcc_of_le_left h hx

Depends on / 依赖: congr_arg, projIcc_of_le_left
-/
theorem IccExtend_of_le_left (f : Icc a b -> β) (hx : x <= a) :
    IccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩ :=
congr_arg f projIcc_of_le_left h hx

/--
theorem `IccExtend_of_right_le` / 定理 `IccExtend_of_right_le`

English:
theorem IccExtend_of_right_le
  given: (f : Icc a b -> β) (hx : b <= x)
  proof: congr_arg f projIcc_of_right_le h hx

@[simp]

中文:
定理 IccExtend_of_right_le
  条件: (f : 闭区间 a b -> β) (hx : b <= x)
  证明: congr_arg f projIcc_of_right_le h hx

@[simp]

Depends on / 依赖: congr_arg, projIcc_of_right_le
-/
theorem IccExtend_of_right_le (f : Icc a b -> β) (hx : b <= x) :
    IccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩ :=
congr_arg f projIcc_of_right_le h hx

@[simp]
/--
theorem `IciExtend_self` / 定理 `IciExtend_self`

English:
theorem IciExtend_self
  given: (f : Ici a -> β)
  statement: IciExtend f a = f ⟨a, le_rfl⟩
  proof: IciExtend_of_le f le_rfl

@[simp]

中文:
定理 IciExtend_self
  条件: (f : 左闭右无界区间 a -> β)
  结论: IciExtend f a = f ⟨a, le_rfl⟩
  证明: IciExtend_of_le f le_rfl

@[simp]

Depends on / 依赖: IciExtend_of_le, le_rfl
-/
theorem IciExtend_self (f : Ici a -> β) : IciExtend f a = f ⟨a, le_rfl⟩ :=
  IciExtend_of_le f le_rfl

@[simp]
/--
theorem `IicExtend_self` / 定理 `IicExtend_self`

English:
theorem IicExtend_self
  given: (f : Iic b -> β)
  statement: IicExtend f b = f ⟨b, le_rfl⟩
  proof: IicExtend_of_le f le_rfl

@[simp]

中文:
定理 IicExtend_self
  条件: (f : 左无界右闭区间 b -> β)
  结论: IicExtend f b = f ⟨b, le_rfl⟩
  证明: IicExtend_of_le f le_rfl

@[simp]

Depends on / 依赖: IicExtend_of_le, le_rfl
-/
theorem IicExtend_self (f : Iic b -> β) : IicExtend f b = f ⟨b, le_rfl⟩ :=
  IicExtend_of_le f le_rfl

@[simp]
/--
theorem `IccExtend_left` / 定理 `IccExtend_left`

English:
theorem IccExtend_left
  given: (f : Icc a b -> β)
  statement: IccExtend h f a = f ⟨a, left_mem_Icc.2 h⟩
  proof: IccExtend_of_le_left h f le_rfl

@[simp]

中文:
定理 IccExtend_left
  条件: (f : 闭区间 a b -> β)
  结论: IccExtend h f a = f ⟨a, left_mem_Icc.2 h⟩
  证明: IccExtend_of_le_left h f le_rfl

@[simp]

Depends on / 依赖: IccExtend_of_le_left, le_rfl
-/
theorem IccExtend_left (f : Icc a b -> β) : IccExtend h f a = f ⟨a, left_mem_Icc.2 h⟩ :=
  IccExtend_of_le_left h f le_rfl

@[simp]
/--
theorem `IccExtend_right` / 定理 `IccExtend_right`

English:
theorem IccExtend_right
  given: (f : Icc a b -> β)
  statement: IccExtend h f b = f ⟨b, right_mem_Icc.2 h⟩
  proof: IccExtend_of_right_le h f le_rfl

中文:
定理 IccExtend_right
  条件: (f : 闭区间 a b -> β)
  结论: IccExtend h f b = f ⟨b, right_mem_Icc.2 h⟩
  证明: IccExtend_of_right_le h f le_rfl

Depends on / 依赖: IccExtend_of_right_le, le_rfl
-/
theorem IccExtend_right (f : Icc a b -> β) : IccExtend h f b = f ⟨b, right_mem_Icc.2 h⟩ :=
  IccExtend_of_right_le h f le_rfl

/--
theorem `IciExtend_of_mem` / 定理 `IciExtend_of_mem`

English:
theorem IciExtend_of_mem
  given: (f : Ici a -> β) (hx : x in Ici a)
  statement: IciExtend f x = f ⟨x, hx⟩
  proof: congr_arg f projIci_of_mem hx

中文:
定理 IciExtend_of_mem
  条件: (f : 左闭右无界区间 a -> β) (hx : x in 左闭右无界区间 a)
  结论: IciExtend f x = f ⟨x, hx⟩
  证明: congr_arg f projIci_of_mem hx

Depends on / 依赖: congr_arg, projIci_of_mem
-/
theorem IciExtend_of_mem (f : Ici a -> β) (hx : x in Ici a) : IciExtend f x = f ⟨x, hx⟩ :=
congr_arg f projIci_of_mem hx

/--
theorem `IicExtend_of_mem` / 定理 `IicExtend_of_mem`

English:
theorem IicExtend_of_mem
  given: (f : Iic b -> β) (hx : x in Iic b)
  statement: IicExtend f x = f ⟨x, hx⟩
  proof: congr_arg f projIic_of_mem hx

中文:
定理 IicExtend_of_mem
  条件: (f : 左无界右闭区间 b -> β) (hx : x in 左无界右闭区间 b)
  结论: IicExtend f x = f ⟨x, hx⟩
  证明: congr_arg f projIic_of_mem hx

Depends on / 依赖: congr_arg, projIic_of_mem
-/
theorem IicExtend_of_mem (f : Iic b -> β) (hx : x in Iic b) : IicExtend f x = f ⟨x, hx⟩ :=
congr_arg f projIic_of_mem hx

/--
theorem `IccExtend_of_mem` / 定理 `IccExtend_of_mem`

English:
theorem IccExtend_of_mem
  given: (f : Icc a b -> β) (hx : x in Icc a b)
  statement: IccExtend h f x = f ⟨x, hx⟩
  proof: congr_arg f projIcc_of_mem h hx

@[simp]

中文:
定理 IccExtend_of_mem
  条件: (f : 闭区间 a b -> β) (hx : x in 闭区间 a b)
  结论: IccExtend h f x = f ⟨x, hx⟩
  证明: congr_arg f projIcc_of_mem h hx

@[simp]

Depends on / 依赖: congr_arg, projIcc_of_mem
-/
theorem IccExtend_of_mem (f : Icc a b -> β) (hx : x in Icc a b) : IccExtend h f x = f ⟨x, hx⟩ :=
congr_arg f projIcc_of_mem h hx

@[simp]
/--
theorem `IciExtend_coe` / 定理 `IciExtend_coe`

English:
theorem IciExtend_coe
  given: (f : Ici a -> β) (x : Ici a)
  statement: IciExtend f x = f x
  proof: congr_arg f projIci_coe x

@[simp]

中文:
定理 IciExtend_coe
  条件: (f : 左闭右无界区间 a -> β) (x : 左闭右无界区间 a)
  结论: IciExtend f x = f x
  证明: congr_arg f projIci_coe x

@[simp]

Depends on / 依赖: congr_arg, projIci_coe
-/
theorem IciExtend_coe (f : Ici a -> β) (x : Ici a) : IciExtend f x = f x :=
congr_arg f projIci_coe x

@[simp]
/--
theorem `IicExtend_coe` / 定理 `IicExtend_coe`

English:
theorem IicExtend_coe
  given: (f : Iic b -> β) (x : Iic b)
  statement: IicExtend f x = f x
  proof: congr_arg f projIic_coe x

@[simp]

中文:
定理 IicExtend_coe
  条件: (f : 左无界右闭区间 b -> β) (x : 左无界右闭区间 b)
  结论: IicExtend f x = f x
  证明: congr_arg f projIic_coe x

@[simp]

Depends on / 依赖: congr_arg, projIic_coe
-/
theorem IicExtend_coe (f : Iic b -> β) (x : Iic b) : IicExtend f x = f x :=
congr_arg f projIic_coe x

@[simp]
/--
theorem `IccExtend_val` / 定理 `IccExtend_val`

English:
theorem IccExtend_val
  given: (f : Icc a b -> β) (x : Icc a b)
  statement: IccExtend h f x = f x
  proof: congr_arg f projIcc_val h x

中文:
定理 IccExtend_val
  条件: (f : 闭区间 a b -> β) (x : 闭区间 a b)
  结论: IccExtend h f x = f x
  证明: congr_arg f projIcc_val h x

Depends on / 依赖: congr_arg, projIcc_val
-/
theorem IccExtend_val (f : Icc a b -> β) (x : Icc a b) : IccExtend h f x = f x :=
congr_arg f projIcc_val h x

/--
theorem `IccExtend_eq_self` / 定理 `IccExtend_eq_self`

English:
theorem IccExtend_eq_self
  given: (f : α -> β) (ha : forall x < a, f x = f a) (hb : forall x, b < x -> f x = f b)
  proof: by
  ext x
  rcases lt_or_ge x a with hxa | hax
  · simp [IccExtend_of_le_left _ _ hxa.le, ha x hxa]
  · rcases le_or_gt x b with hxb | hbx
    · lift x to Icc a b using ⟨hax, hxb⟩
      rw [IccExtend_val]; rw [comp_apply]
    · simp [IccExtend_of_right_le _ _ hbx.le, hb x hbx]

中文:
定理 IccExtend_eq_self
  条件: (f : α -> β) (ha : 对任意 x < a, f x = f a) (hb : 对任意 x, b < x -> f x = f b)
  证明: by
  ext x
  rcases lt_or_ge x a with hxa | hax
  · simp [IccExtend_of_le_left _ _ hxa.le, ha x hxa]
  · rcases le_or_gt x b with hxb | hbx
    · lift x to Icc a b using ⟨hax, hxb⟩
      rw [IccExtend_val]; rw [comp_apply]
    · simp [IccExtend_of_right_le _ _ hbx.le, hb x hbx]

Depends on / 依赖: IccExtend_of_le_left, IccExtend_of_right_le, IccExtend_val, comp_apply, hbx.le, hxa.le, le_or_gt, lt_or_ge
-/
theorem IccExtend_eq_self (f : α -> β) (ha : forall x < a, f x = f a) (hb : forall x, b < x -> f x = f b) :
    IccExtend h (f ∘ (↑)) = f := by
  ext x
  rcases lt_or_ge x a with hxa | hax
  · simp [IccExtend_of_le_left _ _ hxa.le, ha x hxa]
  · rcases le_or_gt x b with hxb | hbx
    · lift x to Icc a b using ⟨hax, hxb⟩
      rw [IccExtend_val]; rw [comp_apply]
    · simp [IccExtend_of_right_le _ _ hbx.le, hb x hbx]

end Set

open Set

variable [Preorder β] {s t : Set α} {a b : α} (h : a <= b) {f : Icc a b -> β}

/--
theorem `Monotone.IciExtend` / 定理 `Monotone.IciExtend`

English:
theorem Monotone.IciExtend
  given: {f : Ici a -> β} (hf : Monotone f)
  statement: Monotone (IciExtend f)
  proof: hf.comp monotone_projIci

中文:
定理 递增.IciExtend
  条件: {f : 左闭右无界区间 a -> β} (hf : 递增 f)
  结论: 递增 (IciExtend f)
  证明: hf.comp monotone_projIci
-/
protected theorem Monotone.IciExtend {f : Ici a -> β} (hf : Monotone f) : Monotone (IciExtend f) :=
  hf.comp monotone_projIci

/--
theorem `Monotone.IicExtend` / 定理 `Monotone.IicExtend`

English:
theorem Monotone.IicExtend
  given: {f : Iic b -> β} (hf : Monotone f)
  statement: Monotone (IicExtend f)
  proof: hf.comp monotone_projIic

中文:
定理 递增.IicExtend
  条件: {f : 左无界右闭区间 b -> β} (hf : 递增 f)
  结论: 递增 (IicExtend f)
  证明: hf.comp monotone_projIic
-/
protected theorem Monotone.IicExtend {f : Iic b -> β} (hf : Monotone f) : Monotone (IicExtend f) :=
  hf.comp monotone_projIic

/--
theorem `Monotone.IccExtend` / 定理 `Monotone.IccExtend`

English:
theorem Monotone.IccExtend
  given: (hf : Monotone f)
  statement: Monotone (IccExtend h f)
  proof: hf.comp monotone_projIcc h

中文:
定理 递增.IccExtend
  条件: (hf : 递增 f)
  结论: 递增 (IccExtend h f)
  证明: hf.comp monotone_projIcc h
-/
protected theorem Monotone.IccExtend (hf : Monotone f) : Monotone (IccExtend h f) :=
hf.comp monotone_projIcc h

/--
theorem `StrictMono.strictMonoOn_IciExtend` / 定理 `StrictMono.strictMonoOn_IciExtend`

English:
theorem StrictMono.strictMonoOn_IciExtend
  given: {f : Ici a -> β} (hf : StrictMono f)
  proof: hf.comp_strictMonoOn strictMonoOn_projIci

中文:
定理 严格递增.strictMonoOn_IciExtend
  条件: {f : 左闭右无界区间 a -> β} (hf : 严格递增 f)
  证明: hf.comp_strictMonoOn strictMonoOn_projIci

Depends on / 依赖: comp_strictMonoOn, hf.comp_strictMonoOn, strictMonoOn_projIci
-/
theorem StrictMono.strictMonoOn_IciExtend {f : Ici a -> β} (hf : StrictMono f) :
    StrictMonoOn (IciExtend f) (Ici a) :=
  hf.comp_strictMonoOn strictMonoOn_projIci

/--
theorem `StrictMono.strictMonoOn_IicExtend` / 定理 `StrictMono.strictMonoOn_IicExtend`

English:
theorem StrictMono.strictMonoOn_IicExtend
  given: {f : Iic b -> β} (hf : StrictMono f)
  proof: hf.comp_strictMonoOn strictMonoOn_projIic

中文:
定理 严格递增.strictMonoOn_IicExtend
  条件: {f : 左无界右闭区间 b -> β} (hf : 严格递增 f)
  证明: hf.comp_strictMonoOn strictMonoOn_projIic

Depends on / 依赖: comp_strictMonoOn, hf.comp_strictMonoOn, strictMonoOn_projIic
-/
theorem StrictMono.strictMonoOn_IicExtend {f : Iic b -> β} (hf : StrictMono f) :
    StrictMonoOn (IicExtend f) (Iic b) :=
  hf.comp_strictMonoOn strictMonoOn_projIic

/--
theorem `StrictMono.strictMonoOn_IccExtend` / 定理 `StrictMono.strictMonoOn_IccExtend`

English:
theorem StrictMono.strictMonoOn_IccExtend
  given: (hf : StrictMono f)
  proof: hf.comp_strictMonoOn (strictMonoOn_projIcc h)

中文:
定理 严格递增.strictMonoOn_IccExtend
  条件: (hf : 严格递增 f)
  证明: hf.comp_strictMonoOn (strictMonoOn_projIcc h)

Depends on / 依赖: comp_strictMonoOn, hf.comp_strictMonoOn, strictMonoOn_projIcc
-/
theorem StrictMono.strictMonoOn_IccExtend (hf : StrictMono f) :
    StrictMonoOn (IccExtend h f) (Icc a b) :=
  hf.comp_strictMonoOn (strictMonoOn_projIcc h)

/--
theorem `Set.OrdConnected.IciExtend` / 定理 `Set.OrdConnected.IciExtend`

English:
theorem Set.OrdConnected.IciExtend
  given: {s : Set (Ici a)} (hs : s.OrdConnected)
  proof: ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨max_le_max le_rfl hz.1, max_le_max le_rfl hz.2⟩⟩

中文:
定理 集合.序连通.IciExtend
  条件: {s : 集合 (左闭右无界区间 a)} (hs : s.序连通)
  证明: ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨max_le_max le_rfl hz.1, max_le_max le_rfl hz.2⟩⟩
-/
protected theorem Set.OrdConnected.IciExtend {s : Set (Ici a)} (hs : s.OrdConnected) :
    {x | IciExtend (· in s) x}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨max_le_max le_rfl hz.1, max_le_max le_rfl hz.2⟩⟩

/--
theorem `Set.OrdConnected.IicExtend` / 定理 `Set.OrdConnected.IicExtend`

English:
theorem Set.OrdConnected.IicExtend
  given: {s : Set (Iic b)} (hs : s.OrdConnected)
  proof: ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨min_le_min le_rfl hz.1, min_le_min le_rfl hz.2⟩⟩

中文:
定理 集合.序连通.IicExtend
  条件: {s : 集合 (左无界右闭区间 b)} (hs : s.序连通)
  证明: ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨min_le_min le_rfl hz.1, min_le_min le_rfl hz.2⟩⟩
-/
protected theorem Set.OrdConnected.IicExtend {s : Set (Iic b)} (hs : s.OrdConnected) :
    {x | IicExtend (· in s) x}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨min_le_min le_rfl hz.1, min_le_min le_rfl hz.2⟩⟩

/--
theorem `Set.OrdConnected.domRestrict` / 定理 `Set.OrdConnected.domRestrict`

English:
theorem Set.OrdConnected.domRestrict
  given: (hs : s.OrdConnected)
  proof: ⟨fun _ hx _ hy _ hz => hs.out hx hy hz⟩

@[deprecated (since := "2026-07-19")]
alias Set.OrdConnected.restrict := Set.OrdConnected.domRestrict

中文:
定理 集合.序连通.domRestrict
  条件: (hs : s.序连通)
  证明: ⟨fun _ hx _ hy _ hz => hs.out hx hy hz⟩

@[deprecated (since := "2026-07-19")]
alias Set.OrdConnected.restrict := Set.OrdConnected.domRestrict
-/
protected theorem Set.OrdConnected.domRestrict (hs : s.OrdConnected) :
    {x | domRestrict t (· in s) x}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy hz⟩

@[deprecated (since := "2026-07-19")]
alias Set.OrdConnected.restrict := Set.OrdConnected.domRestrict
