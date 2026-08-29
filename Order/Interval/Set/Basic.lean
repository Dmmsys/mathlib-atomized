/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Interval.Set.Defs

/-!
# Intervals

In any preorder, we define intervals (which on each side can be either infinite, open or closed)
using the following naming conventions:

- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side.
For instance, `Ioc a b` denotes the interval `(a, b]`.
The definitions can be found in `Mathlib/Order/Interval/Set/Defs.lean`.

This file contains basic facts on inclusion of and set operations on intervals
(where the precise statements depend on the order's properties;
statements requiring `LinearOrder` are in `Mathlib/Order/Interval/Set/LinearOrder.lean`).

A conscious decision was made not to list all possible inclusion relations.
Monotonicity results and "self" results *are* included.
Most use cases can suffice with a transitive combination of those, for example:
```
theorem Ico_subset_Ici (h : a₂ ≤ a₁) : Ico a₁ b₁ ⊆ Ici a₂ :=
  (Ico_subset_Ico_left h).trans Ico_subset_Ici_self
```
Logical equivalences, such as `Icc_subset_Ici_iff`, are however stated.
-/

public section

assert_not_exists RelIso

open Function

open OrderDual (toDual ofDual)

variable {α : Type*}

namespace Set

section Preorder

variable [Preorder α] {a a₁ a₂ b b₁ b₂ c x : α}

@[to_dual]
/--
Instance `decidableMemIio` / 实例 `decidableMemIio`

English:
instance decidableMemIio
  signature: [Decidable (x < b)]
  body: by assumption

@[to_dual]

中文:
实例 decidableMemIio
  签名: [Decidable (x < b)]
  定义体: by assumption

@[to_dual]
-/
instance decidableMemIio [Decidable (x < b)] : Decidable (x in Iio b) := by assumption

@[to_dual]
/--
Instance `decidableMemIic` / 实例 `decidableMemIic`

English:
instance decidableMemIic
  signature: [Decidable (x <= b)]
  body: by assumption

@[to_dual self (reorder := a b, 6 7)]

中文:
实例 decidableMemIic
  签名: [Decidable (x <= b)]
  定义体: by assumption

@[to_dual self (reorder := a b, 6 7)]
-/
instance decidableMemIic [Decidable (x <= b)] : Decidable (x in Iic b) := by assumption

@[to_dual self (reorder := a b, 6 7)]
/--
Instance `decidableMemIoo` / 实例 `decidableMemIoo`

English:
instance decidableMemIoo
  signature: [Decidable (a < x)] [Decidable (x < b)]
  body: instDecidableAnd

中文:
实例 decidableMemIoo
  签名: [Decidable (a < x)] [Decidable (x < b)]
  定义体: instDecidableAnd

Depends on / 依赖: instDecidableAnd
-/
instance decidableMemIoo [Decidable (a < x)] [Decidable (x < b)] : Decidable (x in Ioo a b) :=
  instDecidableAnd

/--
Instance `decidableMemIco` / 实例 `decidableMemIco`

English:
instance decidableMemIco
  signature: [Decidable (a <= x)] [Decidable (x < b)]
  body: instDecidableAnd

@[to_dual self (reorder := a b, 6 7)]

中文:
实例 decidableMemIco
  签名: [Decidable (a <= x)] [Decidable (x < b)]
  定义体: instDecidableAnd

@[to_dual self (reorder := a b, 6 7)]

Depends on / 依赖: instDecidableAnd
-/
instance decidableMemIco [Decidable (a <= x)] [Decidable (x < b)] : Decidable (x in Ico a b) :=
  instDecidableAnd

@[to_dual self (reorder := a b, 6 7)]
/--
Instance `decidableMemIcc` / 实例 `decidableMemIcc`

English:
instance decidableMemIcc
  signature: [Decidable (a <= x)] [Decidable (x <= b)]
  body: instDecidableAnd

@[to_dual existing (reorder := a b, 6 7)]

中文:
实例 decidableMemIcc
  签名: [Decidable (a <= x)] [Decidable (x <= b)]
  定义体: instDecidableAnd

@[to_dual existing (reorder := a b, 6 7)]

Depends on / 依赖: instDecidableAnd
-/
instance decidableMemIcc [Decidable (a <= x)] [Decidable (x <= b)] : Decidable (x in Icc a b) :=
  instDecidableAnd

@[to_dual existing (reorder := a b, 6 7)]
/--
Instance `decidableMemIoc` / 实例 `decidableMemIoc`

English:
instance decidableMemIoc
  signature: [Decidable (a < x)] [Decidable (x <= b)]
  body: instDecidableAnd

中文:
实例 decidableMemIoc
  签名: [Decidable (a < x)] [Decidable (x <= b)]
  定义体: instDecidableAnd

Depends on / 依赖: instDecidableAnd
-/
instance decidableMemIoc [Decidable (a < x)] [Decidable (x <= b)] : Decidable (x in Ioc a b) :=
  instDecidableAnd

/--
theorem `self_notMem_Iio` / 定理 `self_notMem_Iio`

English:
theorem self_notMem_Iio
  statement: a ∉ Iio a
  proof: by simp

中文:
定理 self_notMem_Iio
  结论: a ∉ Iio a
  证明: by simp
-/
@[to_dual] theorem self_notMem_Iio : a ∉ Iio a := by simp
/--
theorem `self_mem_Iic` / 定理 `self_mem_Iic`

English:
theorem self_mem_Iic
  statement: a in Iic a
  proof: by simp

@[to_dual right_notMem_Ioo]

中文:
定理 self_mem_Iic
  结论: a in Iic a
  证明: by simp

@[to_dual right_notMem_Ioo]
-/
@[to_dual] theorem self_mem_Iic : a in Iic a := by simp

@[to_dual right_notMem_Ioo]
/--
theorem `left_notMem_Ioo` / 定理 `left_notMem_Ioo`

English:
theorem left_notMem_Ioo
  statement: a ∉ Ioo a b
  proof: by simp

@[to_dual right_notMem_Ico]

中文:
定理 left_notMem_Ioo
  结论: a ∉ Ioo a b
  证明: by simp

@[to_dual right_notMem_Ico]
-/
theorem left_notMem_Ioo : a ∉ Ioo a b := by simp

@[to_dual right_notMem_Ico]
/--
theorem `left_notMem_Ioc` / 定理 `left_notMem_Ioc`

English:
theorem left_notMem_Ioc
  statement: a ∉ Ioc a b
  proof: by simp

中文:
定理 left_notMem_Ioc
  结论: a ∉ Ioc a b
  证明: by simp
-/
theorem left_notMem_Ioc : a ∉ Ioc a b := by simp

/--
theorem `left_mem_Ico` / 定理 `left_mem_Ico`

English:
theorem left_mem_Ico
  statement: a in Ico a b ↔ a < b
  proof: by simp

中文:
定理 left_mem_Ico
  结论: a in Ico a b ↔ a < b
  证明: by simp
-/
@[to_dual right_mem_Ioc] theorem left_mem_Ico : a in Ico a b ↔ a < b := by simp
/--
theorem `left_mem_Icc` / 定理 `left_mem_Icc`

English:
theorem left_mem_Icc
  statement: a in Icc a b ↔ a <= b
  proof: by simp

@[to_dual (attr := simp)]

中文:
定理 left_mem_Icc
  结论: a in Icc a b ↔ a <= b
  证明: by simp

@[to_dual (attr := simp)]
-/
@[to_dual right_mem_Icc] theorem left_mem_Icc : a in Icc a b ↔ a <= b := by simp

@[to_dual (attr := simp)]
/--
theorem `Iio_toDual` / 定理 `Iio_toDual`

English:
theorem Iio_toDual
  statement: Iio (toDual a) = ofDual ⁻¹' Ioi a
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 Iio_toDual
  结论: Iio (toDual a) = ofDual ⁻¹' Ioi a
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem Iio_toDual : Iio (toDual a) = ofDual ⁻¹' Ioi a :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `Iic_toDual` / 定理 `Iic_toDual`

English:
theorem Iic_toDual
  statement: Iic (toDual a) = ofDual ⁻¹' Ici a
  proof: rfl

@[simp, to_dual self]

中文:
定理 Iic_toDual
  结论: Iic (toDual a) = ofDual ⁻¹' Ici a
  证明: rfl

@[simp, to_dual self]
-/
theorem Iic_toDual : Iic (toDual a) = ofDual ⁻¹' Ici a :=
  rfl

@[simp, to_dual self]
/--
theorem `Icc_toDual` / 定理 `Icc_toDual`

English:
theorem Icc_toDual
  statement: Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc b a
  proof: Set.ext fun _ => and_comm

@[to_dual (attr := simp)]

中文:
定理 Icc_toDual
  结论: Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc b a
  证明: Set.ext fun _ => and_comm

@[to_dual (attr := simp)]

Depends on / 依赖: Set.ext, and_comm
-/
theorem Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc b a :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
/--
theorem `Ico_toDual` / 定理 `Ico_toDual`

English:
theorem Ico_toDual
  statement: Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc b a
  proof: Set.ext fun _ => and_comm

@[simp, to_dual self]

中文:
定理 Ico_toDual
  结论: Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc b a
  证明: Set.ext fun _ => and_comm

@[simp, to_dual self]

Depends on / 依赖: Set.ext, and_comm
-/
theorem Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc b a :=
  Set.ext fun _ => and_comm

@[simp, to_dual self]
/--
theorem `Ioo_toDual` / 定理 `Ioo_toDual`

English:
theorem Ioo_toDual
  statement: Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo b a
  proof: Set.ext fun _ => and_comm

@[to_dual (attr := simp)]

中文:
定理 Ioo_toDual
  结论: Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo b a
  证明: Set.ext fun _ => and_comm

@[to_dual (attr := simp)]

Depends on / 依赖: Set.ext, and_comm
-/
theorem Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo b a :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
/--
theorem `Iio_ofDual` / 定理 `Iio_ofDual`

English:
theorem Iio_ofDual
  given: {x : αᵒᵈ}
  statement: Iio (ofDual x) = toDual ⁻¹' Ioi x
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 Iio_ofDual
  条件: {x : αᵒᵈ}
  结论: Iio (ofDual x) = toDual ⁻¹' Ioi x
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem Iio_ofDual {x : αᵒᵈ} : Iio (ofDual x) = toDual ⁻¹' Ioi x :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `Iic_ofDual` / 定理 `Iic_ofDual`

English:
theorem Iic_ofDual
  given: {x : αᵒᵈ}
  statement: Iic (ofDual x) = toDual ⁻¹' Ici x
  proof: rfl

@[simp, to_dual self]

中文:
定理 Iic_ofDual
  条件: {x : αᵒᵈ}
  结论: Iic (ofDual x) = toDual ⁻¹' Ici x
  证明: rfl

@[simp, to_dual self]
-/
theorem Iic_ofDual {x : αᵒᵈ} : Iic (ofDual x) = toDual ⁻¹' Ici x :=
  rfl

@[simp, to_dual self]
/--
theorem `Icc_ofDual` / 定理 `Icc_ofDual`

English:
theorem Icc_ofDual
  given: {x y : αᵒᵈ}
  statement: Icc (ofDual y) (ofDual x) = toDual ⁻¹' Icc x y
  proof: Set.ext fun _ => and_comm

@[to_dual (attr := simp)]

中文:
定理 Icc_ofDual
  条件: {x y : αᵒᵈ}
  结论: Icc (ofDual y) (ofDual x) = toDual ⁻¹' Icc x y
  证明: Set.ext fun _ => and_comm

@[to_dual (attr := simp)]

Depends on / 依赖: Set.ext, and_comm
-/
theorem Icc_ofDual {x y : αᵒᵈ} : Icc (ofDual y) (ofDual x) = toDual ⁻¹' Icc x y :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
/--
theorem `Ico_ofDual` / 定理 `Ico_ofDual`

English:
theorem Ico_ofDual
  given: {x y : αᵒᵈ}
  statement: Ico (ofDual y) (ofDual x) = toDual ⁻¹' Ioc x y
  proof: Set.ext fun _ => and_comm

@[simp, to_dual self]

中文:
定理 Ico_ofDual
  条件: {x y : αᵒᵈ}
  结论: Ico (ofDual y) (ofDual x) = toDual ⁻¹' Ioc x y
  证明: Set.ext fun _ => and_comm

@[simp, to_dual self]

Depends on / 依赖: Set.ext, and_comm
-/
theorem Ico_ofDual {x y : αᵒᵈ} : Ico (ofDual y) (ofDual x) = toDual ⁻¹' Ioc x y :=
  Set.ext fun _ => and_comm

@[simp, to_dual self]
/--
theorem `Ioo_ofDual` / 定理 `Ioo_ofDual`

English:
theorem Ioo_ofDual
  given: {x y : αᵒᵈ}
  statement: Ioo (ofDual y) (ofDual x) = toDual ⁻¹' Ioo x y
  proof: Set.ext fun _ => and_comm

@[to_dual (attr := simp)]

中文:
定理 Ioo_ofDual
  条件: {x y : αᵒᵈ}
  结论: Ioo (ofDual y) (ofDual x) = toDual ⁻¹' Ioo x y
  证明: Set.ext fun _ => and_comm

@[to_dual (attr := simp)]

Depends on / 依赖: Set.ext, and_comm
-/
theorem Ioo_ofDual {x y : αᵒᵈ} : Ioo (ofDual y) (ofDual x) = toDual ⁻¹' Ioo x y :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
/--
theorem `nonempty_Iio` / 定理 `nonempty_Iio`

English:
theorem nonempty_Iio
  given: [NoMinOrder α]
  statement: (Iio a).Nonempty
  proof: exists_lt a

@[to_dual (attr := simp)]

中文:
定理 nonempty_Iio
  条件: [NoMinOrder α]
  结论: (Iio a).Nonempty
  证明: exists_lt a

@[to_dual (attr := simp)]

Depends on / 依赖: exists_lt
-/
theorem nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty :=
  exists_lt a

@[to_dual (attr := simp)]
/--
theorem `nonempty_Iic` / 定理 `nonempty_Iic`

English:
theorem nonempty_Iic
  statement: (Iic a).Nonempty
  proof: ⟨a, self_mem_Iic⟩

@[simp, to_dual self]

中文:
定理 nonempty_Iic
  结论: (Iic a).Nonempty
  证明: ⟨a, self_mem_Iic⟩

@[simp, to_dual self]

Depends on / 依赖: self_mem_Iic
-/
theorem nonempty_Iic : (Iic a).Nonempty :=
  ⟨a, self_mem_Iic⟩

@[simp, to_dual self]
/--
theorem `nonempty_Icc` / 定理 `nonempty_Icc`

English:
theorem nonempty_Icc
  statement: (Icc a b).Nonempty ↔ a <= b
  proof: ⟨fun ⟨_, hx⟩ => hx.1.trans hx.2, fun h => ⟨a, left_mem_Icc.2 h⟩⟩

@[to_dual (attr := simp)]

中文:
定理 nonempty_Icc
  结论: (Icc a b).Nonempty ↔ a <= b
  证明: ⟨fun ⟨_, hx⟩ => hx.1.trans hx.2, fun h => ⟨a, left_mem_Icc.2 h⟩⟩

@[to_dual (attr := simp)]

Depends on / 依赖: left_mem_Icc
-/
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a <= b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans hx.2, fun h => ⟨a, left_mem_Icc.2 h⟩⟩

@[to_dual (attr := simp)]
/--
theorem `nonempty_Ico` / 定理 `nonempty_Ico`

English:
theorem nonempty_Ico
  statement: (Ico a b).Nonempty ↔ a < b
  proof: ⟨fun ⟨_, hx⟩ => hx.1.trans_lt hx.2, fun h => ⟨a, left_mem_Ico.2 h⟩⟩


@[simp, to_dual self]

中文:
定理 nonempty_Ico
  结论: (Ico a b).Nonempty ↔ a < b
  证明: ⟨fun ⟨_, hx⟩ => hx.1.trans_lt hx.2, fun h => ⟨a, left_mem_Ico.2 h⟩⟩


@[simp, to_dual self]

Depends on / 依赖: left_mem_Ico, trans_lt
-/
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans_lt hx.2, fun h => ⟨a, left_mem_Ico.2 h⟩⟩


@[simp, to_dual self]
/--
theorem `nonempty_Ioo` / 定理 `nonempty_Ioo`

English:
theorem nonempty_Ioo
  given: [DenselyOrdered α]
  statement: (Ioo a b).Nonempty ↔ a < b
  proof: ⟨fun ⟨_, ha, hb⟩ => ha.trans hb, exists_between⟩

中文:
定理 nonempty_Ioo
  条件: [DenselyOrdered α]
  结论: (Ioo a b).Nonempty ↔ a < b
  证明: ⟨fun ⟨_, ha, hb⟩ => ha.trans hb, exists_between⟩

Depends on / 依赖: exists_between, ha.trans
-/
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, ha, hb⟩ => ha.trans hb, exists_between⟩

/-- In an order without minimal elements, the intervals `Iio` are nonempty. -/
@[to_dual /-- In an order without maximal elements, the intervals `Ioi` are nonempty. -/]
/--
Instance `nonempty_Iio_subtype` / 实例 `nonempty_Iio_subtype`

English:
instance nonempty_Iio_subtype
  signature: [NoMinOrder α]
  body: Nonempty.to_subtype nonempty_Iio

中文:
实例 nonempty_Iio_subtype
  签名: [NoMinOrder α]
  定义体: Nonempty.to_subtype nonempty_Iio

Depends on / 依赖: Nonempty, Nonempty.to_subtype, nonempty_Iio, to_subtype
-/
instance nonempty_Iio_subtype [NoMinOrder α] : Nonempty (Iio a) :=
  Nonempty.to_subtype nonempty_Iio

/-- An interval `Iic a` is nonempty. -/
@[to_dual /-- An interval `Ici a` is nonempty. -/]
/--
Instance `nonempty_Iic_subtype` / 实例 `nonempty_Iic_subtype`

English:
instance nonempty_Iic_subtype
  signature: : Nonempty (Iic a)
  body: Nonempty.to_subtype nonempty_Iic

@[to_dual self]

中文:
实例 nonempty_Iic_subtype
  签名: : Nonempty (Iic a)
  定义体: Nonempty.to_subtype nonempty_Iic

@[to_dual self]

Depends on / 依赖: Nonempty, Nonempty.to_subtype, nonempty_Iic, to_subtype
-/
instance nonempty_Iic_subtype : Nonempty (Iic a) :=
  Nonempty.to_subtype nonempty_Iic

@[to_dual self]
/--
theorem `nonempty_Icc_subtype` / 定理 `nonempty_Icc_subtype`

English:
theorem nonempty_Icc_subtype
  given: (h : a <= b)
  statement: Nonempty (Icc a b)
  proof: Nonempty.to_subtype (nonempty_Icc.mpr h)

@[to_dual]

中文:
定理 nonempty_Icc_subtype
  条件: (h : a <= b)
  结论: Nonempty (Icc a b)
  证明: Nonempty.to_subtype (nonempty_Icc.mpr h)

@[to_dual]

Depends on / 依赖: Nonempty, Nonempty.to_subtype, nonempty_Icc, nonempty_Icc.mpr, to_subtype
-/
theorem nonempty_Icc_subtype (h : a <= b) : Nonempty (Icc a b) :=
  Nonempty.to_subtype (nonempty_Icc.mpr h)

@[to_dual]
/--
theorem `nonempty_Ioc_subtype` / 定理 `nonempty_Ioc_subtype`

English:
theorem nonempty_Ioc_subtype
  given: (h : a < b)
  statement: Nonempty (Ioc a b)
  proof: Nonempty.to_subtype (nonempty_Ioc.mpr h)

@[to_dual self]

中文:
定理 nonempty_Ioc_subtype
  条件: (h : a < b)
  结论: Nonempty (Ioc a b)
  证明: Nonempty.to_subtype (nonempty_Ioc.mpr h)

@[to_dual self]

Depends on / 依赖: Nonempty, Nonempty.to_subtype, nonempty_Ioc, nonempty_Ioc.mpr, to_subtype
-/
theorem nonempty_Ioc_subtype (h : a < b) : Nonempty (Ioc a b) :=
  Nonempty.to_subtype (nonempty_Ioc.mpr h)

@[to_dual self]
/--
theorem `nonempty_Ioo_subtype` / 定理 `nonempty_Ioo_subtype`

English:
theorem nonempty_Ioo_subtype
  given: [DenselyOrdered α] (h : a < b)
  statement: Nonempty (Ioo a b)
  proof: Nonempty.to_subtype (nonempty_Ioo.mpr h)

@[to_additive (attr := simp)]

中文:
定理 nonempty_Ioo_subtype
  条件: [DenselyOrdered α] (h : a < b)
  结论: Nonempty (Ioo a b)
  证明: Nonempty.to_subtype (nonempty_Ioo.mpr h)

@[to_additive (attr := simp)]

Depends on / 依赖: Nonempty, Nonempty.to_subtype, nonempty_Ioo, nonempty_Ioo.mpr, to_subtype
-/
theorem nonempty_Ioo_subtype [DenselyOrdered α] (h : a < b) : Nonempty (Ioo a b) :=
  Nonempty.to_subtype (nonempty_Ioo.mpr h)

@[to_additive (attr := simp)]
/--
theorem `Iio_one_eq_empty` / 定理 `Iio_one_eq_empty`

English:
theorem Iio_one_eq_empty
  given: [One α] [IsBotOneClass α]
  statement: Set.Iio (1 : α) = ∅
  proof: by
  ext; simp

@[to_additive]

中文:
定理 Iio_one_eq_empty
  条件: [One α] [IsBotOneClass α]
  结论: Set.Iio (1 : α) = ∅
  证明: by
  ext; simp

@[to_additive]
-/
theorem Iio_one_eq_empty [One α] [IsBotOneClass α] : Set.Iio (1 : α) = ∅ := by
  ext; simp

@[to_additive]
/--
Instance `isEmpty_Iio_one` / 实例 `isEmpty_Iio_one`

English:
instance isEmpty_Iio_one
  signature: [One α] [IsBotOneClass α]
  body: by
  simp

@[to_dual]

中文:
实例 isEmpty_Iio_one
  签名: [One α] [IsBotOneClass α]
  定义体: by
  simp

@[to_dual]
-/
instance isEmpty_Iio_one [One α] [IsBotOneClass α] : IsEmpty (Set.Iio (1 : α)) := by
  simp

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoMinOrder
  signature: α] : NoMinOrder (Iio a)
  body: ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, lt_trans hb a.2⟩, hb⟩⟩

@[to_dual]

中文:
实例 [NoMinOrder
  签名: α] : NoMinOrder (Iio a)
  定义体: ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, lt_trans hb a.2⟩, hb⟩⟩

@[to_dual]

Depends on / 依赖: exists_lt, lt_trans
-/
instance [NoMinOrder α] : NoMinOrder (Iio a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, lt_trans hb a.2⟩, hb⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoMinOrder
  signature: α] : NoMinOrder (Iic a)
  body: ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, hb.le.trans a.2⟩, hb⟩⟩

@[simp, to_dual self]

中文:
实例 [NoMinOrder
  签名: α] : NoMinOrder (Iic a)
  定义体: ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, hb.le.trans a.2⟩, hb⟩⟩

@[simp, to_dual self]

Depends on / 依赖: exists_lt, hb.le.trans
-/
instance [NoMinOrder α] : NoMinOrder (Iic a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, hb.le.trans a.2⟩, hb⟩⟩

@[simp, to_dual self]
/--
theorem `Icc_eq_empty` / 定理 `Icc_eq_empty`

English:
theorem Icc_eq_empty
  given: (h : ¬a <= b)
  statement: Icc a b = ∅
  proof: eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[to_dual (attr := simp)]

中文:
定理 Icc_eq_empty
  条件: (h : ¬a <= b)
  结论: Icc a b = ∅
  证明: eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[to_dual (attr := simp)]

Depends on / 依赖: eq_empty_iff_forall_notMem, ha.trans
-/
theorem Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[to_dual (attr := simp)]
/--
theorem `Ico_eq_empty` / 定理 `Ico_eq_empty`

English:
theorem Ico_eq_empty
  given: (h : ¬a < b)
  statement: Ico a b = ∅
  proof: eq_empty_iff_forall_notMem.2 fun _ hab => h (hab.1.trans_lt hab.2)

@[simp, to_dual self]

中文:
定理 Ico_eq_empty
  条件: (h : ¬a < b)
  结论: Ico a b = ∅
  证明: eq_empty_iff_forall_notMem.2 fun _ hab => h (hab.1.trans_lt hab.2)

@[simp, to_dual self]

Depends on / 依赖: eq_empty_iff_forall_notMem, trans_lt
-/
theorem Ico_eq_empty (h : ¬a < b) : Ico a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hab => h (hab.1.trans_lt hab.2)

@[simp, to_dual self]
/--
theorem `Ioo_eq_empty` / 定理 `Ioo_eq_empty`

English:
theorem Ioo_eq_empty
  given: (h : ¬a < b)
  statement: Ioo a b = ∅
  proof: eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[simp, to_dual self]

中文:
定理 Ioo_eq_empty
  条件: (h : ¬a < b)
  结论: Ioo a b = ∅
  证明: eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[simp, to_dual self]

Depends on / 依赖: eq_empty_iff_forall_notMem, ha.trans
-/
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[simp, to_dual self]
/--
theorem `Icc_eq_empty_of_lt` / 定理 `Icc_eq_empty_of_lt`

English:
theorem Icc_eq_empty_of_lt
  given: (h : b < a)
  statement: Icc a b = ∅
  proof: Icc_eq_empty h.not_ge

@[to_dual (attr := simp)]

中文:
定理 Icc_eq_empty_of_lt
  条件: (h : b < a)
  结论: Icc a b = ∅
  证明: Icc_eq_empty h.not_ge

@[to_dual (attr := simp)]

Depends on / 依赖: Icc_eq_empty, h.not_ge, not_ge
-/
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_ge

@[to_dual (attr := simp)]
/--
theorem `Ico_eq_empty_of_le` / 定理 `Ico_eq_empty_of_le`

English:
theorem Ico_eq_empty_of_le
  given: (h : b <= a)
  statement: Ico a b = ∅
  proof: Ico_eq_empty h.not_gt

@[simp, to_dual self]

中文:
定理 Ico_eq_empty_of_le
  条件: (h : b <= a)
  结论: Ico a b = ∅
  证明: Ico_eq_empty h.not_gt

@[simp, to_dual self]

Depends on / 依赖: Ico_eq_empty, h.not_gt, not_gt
-/
theorem Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_gt

@[simp, to_dual self]
/--
theorem `Ioo_eq_empty_of_le` / 定理 `Ioo_eq_empty_of_le`

English:
theorem Ioo_eq_empty_of_le
  given: (h : b <= a)
  statement: Ioo a b = ∅
  proof: Ioo_eq_empty h.not_gt

@[to_dual]

中文:
定理 Ioo_eq_empty_of_le
  条件: (h : b <= a)
  结论: Ioo a b = ∅
  证明: Ioo_eq_empty h.not_gt

@[to_dual]

Depends on / 依赖: Ioo_eq_empty, h.not_gt, not_gt
-/
theorem Ioo_eq_empty_of_le (h : b <= a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_gt

@[to_dual]
/--
theorem `Ico_self` / 定理 `Ico_self`

English:
theorem Ico_self
  given: (a : α)
  statement: Ico a a = ∅
  proof: Ico_eq_empty lt_irrefl _

中文:
定理 Ico_self
  条件: (a : α)
  结论: Ico a a = ∅
  证明: Ico_eq_empty lt_irrefl _

Depends on / 依赖: Ico_eq_empty, lt_irrefl
-/
theorem Ico_self (a : α) : Ico a a = ∅ :=
Ico_eq_empty lt_irrefl _

/--
theorem `Ioo_self` / 定理 `Ioo_self`

English:
theorem Ioo_self
  given: (a : α)
  statement: Ioo a a = ∅
  proof: Ioo_eq_empty lt_irrefl _

中文:
定理 Ioo_self
  条件: (a : α)
  结论: Ioo a a = ∅
  证明: Ioo_eq_empty lt_irrefl _

Depends on / 依赖: Ioo_eq_empty, lt_irrefl
-/
theorem Ioo_self (a : α) : Ioo a a = ∅ :=
Ioo_eq_empty lt_irrefl _

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_subset_Iio_iff`. -/
@[to_dual (attr := gcongr)
/-- If `a ≤ b`, then `(b, +∞) ⊆ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_subset_Ioi_iff`. -/]
/--
theorem `Iio_subset_Iio` / 定理 `Iio_subset_Iio`

English:
theorem Iio_subset_Iio
  given: (h : a <= b)
  statement: Iio a subseteq Iio b
  proof: fun _ hx => lt_of_lt_of_le hx h

中文:
定理 Iio_subset_Iio
  条件: (h : a <= b)
  结论: Iio a subseteq Iio b
  证明: fun _ hx => lt_of_lt_of_le hx h

Depends on / 依赖: lt_of_lt_of_le
-/
theorem Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b := fun _ hx => lt_of_lt_of_le hx h

/-- If `a < b`, then `(-∞, a) ⊂ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_ssubset_Iio_iff`. -/
@[to_dual (attr := gcongr)
/-- If `a < b`, then `(b, +∞) ⊂ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_ssubset_Ioi_iff`. -/]
/--
theorem `Iio_ssubset_Iio` / 定理 `Iio_ssubset_Iio`

English:
theorem Iio_ssubset_Iio
  given: (h : a < b)
  statement: Iio a ⊂ Iio b
  proof: (ssubset_iff_of_subset (Iio_subset_Iio h.le)).mpr ⟨a, h, lt_irrefl a⟩

@[to_dual (attr := simp, gcongr)]

中文:
定理 Iio_ssubset_Iio
  条件: (h : a < b)
  结论: Iio a ⊂ Iio b
  证明: (ssubset_iff_of_subset (Iio_subset_Iio h.le)).mpr ⟨a, h, lt_irrefl a⟩

@[to_dual (attr := simp, gcongr)]

Depends on / 依赖: Iio_subset_Iio, h.le, lt_irrefl, ssubset_iff_of_subset
-/
theorem Iio_ssubset_Iio (h : a < b) : Iio a ⊂ Iio b :=
  (ssubset_iff_of_subset (Iio_subset_Iio h.le)).mpr ⟨a, h, lt_irrefl a⟩

@[to_dual (attr := simp, gcongr)]
/--
theorem `Iic_subset_Iic` / 定理 `Iic_subset_Iic`

English:
theorem Iic_subset_Iic
  statement: Iic a subseteq Iic b ↔ a <= b
  proof: ⟨fun h => h self_mem_Ici, fun h _ hx => hx.trans h⟩

@[to_dual (attr := simp, gcongr)]

中文:
定理 Iic_subset_Iic
  结论: Iic a subseteq Iic b ↔ a <= b
  证明: ⟨fun h => h self_mem_Ici, fun h _ hx => hx.trans h⟩

@[to_dual (attr := simp, gcongr)]

Depends on / 依赖: hx.trans, self_mem_Ici
-/
theorem Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b :=
  ⟨fun h => h self_mem_Ici, fun h _ hx => hx.trans h⟩

@[to_dual (attr := simp, gcongr)]
/--
theorem `Iic_ssubset_Iic` / 定理 `Iic_ssubset_Iic`

English:
theorem Iic_ssubset_Iic
  statement: Iic a ⊂ Iic b ↔ a < b where
  proof: by
    obtain ⟨ab, c, cb, ac⟩ := ssubset_iff_exists.mp h
    exact lt_of_le_not_ge (Iic_subset_Iic.mp ab) (fun h' => ac (cb.trans h'))
  mpr h := (ssubset_iff_of_subset (Iic_subset_Iic.mpr h.le)).mpr
    ⟨b, self_mem_Iic, fun h' => h.not_ge h'⟩

@[to_dual (attr := simp, gcongr strict)]

中文:
定理 Iic_ssubset_Iic
  结论: Iic a ⊂ Iic b ↔ a < b where
  证明: by
    obtain ⟨ab, c, cb, ac⟩ := ssubset_iff_exists.mp h
    exact lt_of_le_not_ge (Iic_subset_Iic.mp ab) (fun h' => ac (cb.trans h'))
  mpr h := (ssubset_iff_of_subset (Iic_subset_Iic.mpr h.le)).mpr
    ⟨b, self_mem_Iic, fun h' => h.not_ge h'⟩

@[to_dual (attr := simp, gcongr strict)]

Depends on / 依赖: Iic_subset_Iic, Iic_subset_Iic.mp, Iic_subset_Iic.mpr, cb.trans, h.le, h.not_ge, lt_of_le_not_ge, not_ge, self_mem_Iic, ssubset_iff_exists, ssubset_iff_exists.mp, ssubset_iff_of_subset
-/
theorem Iic_ssubset_Iic : Iic a ⊂ Iic b ↔ a < b where
  mp h := by
    obtain ⟨ab, c, cb, ac⟩ := ssubset_iff_exists.mp h
    exact lt_of_le_not_ge (Iic_subset_Iic.mp ab) (fun h' => ac (cb.trans h'))
  mpr h := (ssubset_iff_of_subset (Iic_subset_Iic.mpr h.le)).mpr
    ⟨b, self_mem_Iic, fun h' => h.not_ge h'⟩

@[to_dual (attr := simp, gcongr strict)]
/--
theorem `Iic_subset_Iio` / 定理 `Iic_subset_Iio`

English:
theorem Iic_subset_Iio
  statement: Iic a subseteq Iio b ↔ a < b
  proof: ⟨fun h => h self_mem_Iic, fun h _ hx => lt_of_le_of_lt hx h⟩

@[to_dual]

中文:
定理 Iic_subset_Iio
  结论: Iic a subseteq Iio b ↔ a < b
  证明: ⟨fun h => h self_mem_Iic, fun h _ hx => lt_of_le_of_lt hx h⟩

@[to_dual]

Depends on / 依赖: lt_of_le_of_lt, self_mem_Iic
-/
theorem Iic_subset_Iio : Iic a subseteq Iio b ↔ a < b :=
  ⟨fun h => h self_mem_Iic, fun h _ hx => lt_of_le_of_lt hx h⟩

@[to_dual]
/--
theorem `Iio_subset_Iic_self` / 定理 `Iio_subset_Iic_self`

English:
theorem Iio_subset_Iic_self
  statement: Iio a subseteq Iic a
  proof: fun _ hx => le_of_lt hx

中文:
定理 Iio_subset_Iic_self
  结论: Iio a subseteq Iic a
  证明: fun _ hx => le_of_lt hx

Depends on / 依赖: le_of_lt
-/
theorem Iio_subset_Iic_self : Iio a subseteq Iic a := fun _ hx => le_of_lt hx

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b]`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Iio_subset_Iic_iff`. -/
@[to_dual
/-- If `a ≤ b`, then `(b, +∞) ⊆ [a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Ioi_subset_Ici_iff`. -/]
/--
theorem `Iio_subset_Iic` / 定理 `Iio_subset_Iic`

English:
theorem Iio_subset_Iic
  given: (h : a <= b)
  statement: Iio a subseteq Iic b
  proof: (Iio_subset_Iio h).trans Iio_subset_Iic_self

@[to_dual]

中文:
定理 Iio_subset_Iic
  条件: (h : a <= b)
  结论: Iio a subseteq Iic b
  证明: (Iio_subset_Iio h).trans Iio_subset_Iic_self

@[to_dual]

Depends on / 依赖: Iio_subset_Iic_self, Iio_subset_Iio
-/
theorem Iio_subset_Iic (h : a <= b) : Iio a subseteq Iic b :=
  (Iio_subset_Iio h).trans Iio_subset_Iic_self

@[to_dual]
/--
theorem `Iio_ssubset_Iic_self` / 定理 `Iio_ssubset_Iic_self`

English:
theorem Iio_ssubset_Iic_self
  statement: Iio a ⊂ Iic a
  proof: ⟨Iio_subset_Iic_self, fun h => (h le_rfl).false⟩

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]

中文:
定理 Iio_ssubset_Iic_self
  结论: Iio a ⊂ Iic a
  证明: ⟨Iio_subset_Iic_self, fun h => (h le_rfl).false⟩

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]

Depends on / 依赖: Iio_subset_Iic_self, le_rfl
-/
theorem Iio_ssubset_Iic_self : Iio a ⊂ Iic a :=
  ⟨Iio_subset_Iic_self, fun h => (h le_rfl).false⟩

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]
/--
theorem `Ioo_subset_Ioo` / 定理 `Ioo_subset_Ioo`

English:
theorem Ioo_subset_Ioo
  given: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  statement: Ioo a₁ b₁ subseteq Ioo a₂ b₂
  proof: fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans_lt hx₁, hx₂.trans_le hb⟩

to_dual_name_hint Left Right

@[to_dual]

中文:
定理 Ioo_subset_Ioo
  条件: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  结论: Ioo a₁ b₁ subseteq Ioo a₂ b₂
  证明: fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans_lt hx₁, hx₂.trans_le hb⟩

to_dual_name_hint Left Right

@[to_dual]
-/
theorem Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo a₁ b₁ subseteq Ioo a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans_lt hx₁, hx₂.trans_le hb⟩

to_dual_name_hint Left Right

@[to_dual]
/--
theorem `Ioo_subset_Ioo_left` / 定理 `Ioo_subset_Ioo_left`

English:
theorem Ioo_subset_Ioo_left
  given: (h : a₁ <= a₂)
  statement: Ioo a₂ b subseteq Ioo a₁ b
  proof: Ioo_subset_Ioo h le_rfl

@[to_dual (attr := gcongr) (reorder := ha hb)]

中文:
定理 Ioo_subset_Ioo_left
  条件: (h : a₁ <= a₂)
  结论: Ioo a₂ b subseteq Ioo a₁ b
  证明: Ioo_subset_Ioo h le_rfl

@[to_dual (attr := gcongr) (reorder := ha hb)]

Depends on / 依赖: Ioo_subset_Ioo, le_rfl
-/
theorem Ioo_subset_Ioo_left (h : a₁ <= a₂) : Ioo a₂ b subseteq Ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl

@[to_dual (attr := gcongr) (reorder := ha hb)]
/--
theorem `Ico_subset_Ico` / 定理 `Ico_subset_Ico`

English:
theorem Ico_subset_Ico
  given: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  statement: Ico a₁ b₁ subseteq Ico a₂ b₂
  proof: fun _ hx =>
  ⟨ha.trans hx.1, hx.2.trans_le hb⟩

@[to_dual]

中文:
定理 Ico_subset_Ico
  条件: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  结论: Ico a₁ b₁ subseteq Ico a₂ b₂
  证明: fun _ hx =>
  ⟨ha.trans hx.1, hx.2.trans_le hb⟩

@[to_dual]
-/
theorem Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ico a₁ b₁ subseteq Ico a₂ b₂ := fun _ hx =>
  ⟨ha.trans hx.1, hx.2.trans_le hb⟩

@[to_dual]
/--
theorem `Ico_subset_Ico_left` / 定理 `Ico_subset_Ico_left`

English:
theorem Ico_subset_Ico_left
  given: (h : a₁ <= a₂)
  statement: Ico a₂ b subseteq Ico a₁ b
  proof: Ico_subset_Ico h le_rfl

@[to_dual]

中文:
定理 Ico_subset_Ico_left
  条件: (h : a₁ <= a₂)
  结论: Ico a₂ b subseteq Ico a₁ b
  证明: Ico_subset_Ico h le_rfl

@[to_dual]

Depends on / 依赖: Ico_subset_Ico, le_rfl
-/
theorem Ico_subset_Ico_left (h : a₁ <= a₂) : Ico a₂ b subseteq Ico a₁ b :=
  Ico_subset_Ico h le_rfl

@[to_dual]
/--
theorem `Ioc_subset_Ioc_left` / 定理 `Ioc_subset_Ioc_left`

English:
theorem Ioc_subset_Ioc_left
  given: (h : a₁ <= a₂)
  statement: Ioc a₂ b subseteq Ioc a₁ b
  proof: Ioc_subset_Ioc h le_rfl

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]

中文:
定理 Ioc_subset_Ioc_left
  条件: (h : a₁ <= a₂)
  结论: Ioc a₂ b subseteq Ioc a₁ b
  证明: Ioc_subset_Ioc h le_rfl

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]

Depends on / 依赖: Ioc_subset_Ioc, le_rfl
-/
theorem Ioc_subset_Ioc_left (h : a₁ <= a₂) : Ioc a₂ b subseteq Ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]
/--
theorem `Icc_subset_Icc` / 定理 `Icc_subset_Icc`

English:
theorem Icc_subset_Icc
  given: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  statement: Icc a₁ b₁ subseteq Icc a₂ b₂
  proof: fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans hx₁, le_trans hx₂ hb⟩

@[to_dual]

中文:
定理 Icc_subset_Icc
  条件: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  结论: Icc a₁ b₁ subseteq Icc a₂ b₂
  证明: fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans hx₁, le_trans hx₂ hb⟩

@[to_dual]
-/
theorem Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc a₁ b₁ subseteq Icc a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans hx₁, le_trans hx₂ hb⟩

@[to_dual]
/--
theorem `Icc_subset_Icc_left` / 定理 `Icc_subset_Icc_left`

English:
theorem Icc_subset_Icc_left
  given: (h : a₁ <= a₂)
  statement: Icc a₂ b subseteq Icc a₁ b
  proof: Icc_subset_Icc h le_rfl

@[to_dual (reorder := ha hb)]

中文:
定理 Icc_subset_Icc_left
  条件: (h : a₁ <= a₂)
  结论: Icc a₂ b subseteq Icc a₁ b
  证明: Icc_subset_Icc h le_rfl

@[to_dual (reorder := ha hb)]

Depends on / 依赖: Icc_subset_Icc, le_rfl
-/
theorem Icc_subset_Icc_left (h : a₁ <= a₂) : Icc a₂ b subseteq Icc a₁ b :=
  Icc_subset_Icc h le_rfl

@[to_dual (reorder := ha hb)]
/--
theorem `Icc_ssubset_Icc_left` / 定理 `Icc_ssubset_Icc_left`

English:
theorem Icc_ssubset_Icc_left
  given: (h₂ : a₂ <= b₂) (ha : a₂ < a₁) (hb : b₁ <= b₂)
  statement: Icc a₁ b₁ ⊂ Icc a₂ b₂
  proof: (ssubset_iff_of_subset (Icc_subset_Icc (le_of_lt ha) hb)).mpr
    ⟨a₂, left_mem_Icc.mpr h₂, not_and.mpr fun f _ => lt_irrefl a₂ (ha.trans_le f)⟩

@[to_dual (reorder := ha hb)]

中文:
定理 Icc_ssubset_Icc_left
  条件: (h₂ : a₂ <= b₂) (ha : a₂ < a₁) (hb : b₁ <= b₂)
  结论: Icc a₁ b₁ ⊂ Icc a₂ b₂
  证明: (ssubset_iff_of_subset (Icc_subset_Icc (le_of_lt ha) hb)).mpr
    ⟨a₂, left_mem_Icc.mpr h₂, not_and.mpr fun f _ => lt_irrefl a₂ (ha.trans_le f)⟩

@[to_dual (reorder := ha hb)]

Depends on / 依赖: Icc_subset_Icc, ha.trans_le, le_of_lt, left_mem_Icc, left_mem_Icc.mpr, lt_irrefl, not_and, not_and.mpr, ssubset_iff_of_subset, trans_le
-/
theorem Icc_ssubset_Icc_left (h₂ : a₂ <= b₂) (ha : a₂ < a₁) (hb : b₁ <= b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
  (ssubset_iff_of_subset (Icc_subset_Icc (le_of_lt ha) hb)).mpr
    ⟨a₂, left_mem_Icc.mpr h₂, not_and.mpr fun f _ => lt_irrefl a₂ (ha.trans_le f)⟩

@[to_dual (reorder := ha hb)]
/--
theorem `Ico_subset_Ioo` / 定理 `Ico_subset_Ioo`

English:
theorem Ico_subset_Ioo
  given: (ha : a₂ < a₁) (hb : b₁ <= b₂)
  statement: Ico a₁ b₁ subseteq Ioo a₂ b₂
  proof: fun _ hx =>
  ⟨ha.trans_le hx.1, hx.2.trans_le hb⟩

@[to_dual (attr := gcongr strict)]

中文:
定理 Ico_subset_Ioo
  条件: (ha : a₂ < a₁) (hb : b₁ <= b₂)
  结论: Ico a₁ b₁ subseteq Ioo a₂ b₂
  证明: fun _ hx =>
  ⟨ha.trans_le hx.1, hx.2.trans_le hb⟩

@[to_dual (attr := gcongr strict)]
-/
theorem Ico_subset_Ioo (ha : a₂ < a₁) (hb : b₁ <= b₂) : Ico a₁ b₁ subseteq Ioo a₂ b₂ := fun _ hx =>
  ⟨ha.trans_le hx.1, hx.2.trans_le hb⟩

@[to_dual (attr := gcongr strict)]
/--
theorem `Ico_subset_Ioo_left` / 定理 `Ico_subset_Ioo_left`

English:
theorem Ico_subset_Ioo_left
  given: (h : a₁ < a₂)
  statement: Ico a₂ b subseteq Ioo a₁ b
  proof: Ico_subset_Ioo h le_rfl

@[to_dual (reorder := ha hb)]

中文:
定理 Ico_subset_Ioo_left
  条件: (h : a₁ < a₂)
  结论: Ico a₂ b subseteq Ioo a₁ b
  证明: Ico_subset_Ioo h le_rfl

@[to_dual (reorder := ha hb)]

Depends on / 依赖: Ico_subset_Ioo, le_rfl
-/
theorem Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b subseteq Ioo a₁ b :=
  Ico_subset_Ioo h le_rfl

@[to_dual (reorder := ha hb)]
/--
theorem `Icc_subset_Ioc` / 定理 `Icc_subset_Ioc`

English:
theorem Icc_subset_Ioc
  given: (ha : a₂ < a₁) (hb : b₁ <= b₂)
  statement: Icc a₁ b₁ subseteq Ioc a₂ b₂
  proof: fun _ hx =>
  ⟨ha.trans_le hx.1, hx.2.trans hb⟩

@[to_dual (attr := gcongr strict)]

中文:
定理 Icc_subset_Ioc
  条件: (ha : a₂ < a₁) (hb : b₁ <= b₂)
  结论: Icc a₁ b₁ subseteq Ioc a₂ b₂
  证明: fun _ hx =>
  ⟨ha.trans_le hx.1, hx.2.trans hb⟩

@[to_dual (attr := gcongr strict)]
-/
theorem Icc_subset_Ioc (ha : a₂ < a₁) (hb : b₁ <= b₂) : Icc a₁ b₁ subseteq Ioc a₂ b₂ := fun _ hx =>
  ⟨ha.trans_le hx.1, hx.2.trans hb⟩

@[to_dual (attr := gcongr strict)]
/--
theorem `Icc_subset_Ioc_left` / 定理 `Icc_subset_Ioc_left`

English:
theorem Icc_subset_Ioc_left
  given: (h : a₁ < a₂)
  statement: Icc a₂ b subseteq Ioc a₁ b
  proof: Icc_subset_Ioc h le_rfl

@[to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]

中文:
定理 Icc_subset_Ioc_left
  条件: (h : a₁ < a₂)
  结论: Icc a₂ b subseteq Ioc a₁ b
  证明: Icc_subset_Ioc h le_rfl

@[to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]

Depends on / 依赖: Icc_subset_Ioc, le_rfl
-/
theorem Icc_subset_Ioc_left (h : a₁ < a₂) : Icc a₂ b subseteq Ioc a₁ b :=
  Icc_subset_Ioc h le_rfl

@[to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]
/--
theorem `Icc_subset_Ioo` / 定理 `Icc_subset_Ioo`

English:
theorem Icc_subset_Ioo
  given: (ha : a₂ < a₁) (hb : b₁ < b₂)
  statement: Icc a₁ b₁ subseteq Ioo a₂ b₂
  proof: (Icc_subset_Ioc_left ha).trans (Ioc_subset_Ioo_right hb)

中文:
定理 Icc_subset_Ioo
  条件: (ha : a₂ < a₁) (hb : b₁ < b₂)
  结论: Icc a₁ b₁ subseteq Ioo a₂ b₂
  证明: (Icc_subset_Ioc_left ha).trans (Ioc_subset_Ioo_right hb)

Depends on / 依赖: Icc_subset_Ioc_left, Ioc_subset_Ioo_right
-/
theorem Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a₁ b₁ subseteq Ioo a₂ b₂ :=
  (Icc_subset_Ioc_left ha).trans (Ioc_subset_Ioo_right hb)

/--
theorem `Ico_subset_Iio_self` / 定理 `Ico_subset_Iio_self`

English:
theorem Ico_subset_Iio_self
  statement: Ico a b subseteq Iio b
  proof: fun _ => And.right

中文:
定理 Ico_subset_Iio_self
  结论: Ico a b subseteq Iio b
  证明: fun _ => And.right
-/
@[to_dual] theorem Ico_subset_Iio_self : Ico a b subseteq Iio b := fun _ => And.right
/--
theorem `Ioo_subset_Iio_self` / 定理 `Ioo_subset_Iio_self`

English:
theorem Ioo_subset_Iio_self
  statement: Ioo a b subseteq Iio b
  proof: fun _ => And.right

中文:
定理 Ioo_subset_Iio_self
  结论: Ioo a b subseteq Iio b
  证明: fun _ => And.right
-/
@[to_dual] theorem Ioo_subset_Iio_self : Ioo a b subseteq Iio b := fun _ => And.right
/--
theorem `Ioc_subset_Iic_self` / 定理 `Ioc_subset_Iic_self`

English:
theorem Ioc_subset_Iic_self
  statement: Ioc a b subseteq Iic b
  proof: fun _ => And.right

中文:
定理 Ioc_subset_Iic_self
  结论: Ioc a b subseteq Iic b
  证明: fun _ => And.right
-/
@[to_dual] theorem Ioc_subset_Iic_self : Ioc a b subseteq Iic b := fun _ => And.right
/--
theorem `Icc_subset_Iic_self` / 定理 `Icc_subset_Iic_self`

English:
theorem Icc_subset_Iic_self
  statement: Icc a b subseteq Iic b
  proof: fun _ => And.right

中文:
定理 Icc_subset_Iic_self
  结论: Icc a b subseteq Iic b
  证明: fun _ => And.right
-/
@[to_dual] theorem Icc_subset_Iic_self : Icc a b subseteq Iic b := fun _ => And.right

/--
theorem `Ioo_subset_Ico_self` / 定理 `Ioo_subset_Ico_self`

English:
theorem Ioo_subset_Ico_self
  statement: Ioo a b subseteq Ico a b
  proof: fun _ => And.imp_left le_of_lt

中文:
定理 Ioo_subset_Ico_self
  结论: Ioo a b subseteq Ico a b
  证明: fun _ => And.imp_left le_of_lt
-/
@[to_dual] theorem Ioo_subset_Ico_self : Ioo a b subseteq Ico a b := fun _ => And.imp_left le_of_lt
/--
theorem `Ioc_subset_Icc_self` / 定理 `Ioc_subset_Icc_self`

English:
theorem Ioc_subset_Icc_self
  statement: Ioc a b subseteq Icc a b
  proof: fun _ => And.imp_left le_of_lt

@[to_dual self]

中文:
定理 Ioc_subset_Icc_self
  结论: Ioc a b subseteq Icc a b
  证明: fun _ => And.imp_left le_of_lt

@[to_dual self]
-/
@[to_dual] theorem Ioc_subset_Icc_self : Ioc a b subseteq Icc a b := fun _ => And.imp_left le_of_lt

@[to_dual self]
/--
theorem `Ioo_subset_Icc_self` / 定理 `Ioo_subset_Icc_self`

English:
theorem Ioo_subset_Icc_self
  statement: Ioo a b subseteq Icc a b
  proof: Ioo_subset_Ico_self.trans Ico_subset_Icc_self

@[to_dual none]

中文:
定理 Ioo_subset_Icc_self
  结论: Ioo a b subseteq Icc a b
  证明: Ioo_subset_Ico_self.trans Ico_subset_Icc_self

@[to_dual none]

Depends on / 依赖: Ico_subset_Icc_self, Ioo_subset_Ico_self, Ioo_subset_Ico_self.trans
-/
theorem Ioo_subset_Icc_self : Ioo a b subseteq Icc a b :=
  Ioo_subset_Ico_self.trans Ico_subset_Icc_self

@[to_dual none]
/--
theorem `Icc_subset_Icc_iff` / 定理 `Icc_subset_Icc_iff`

English:
theorem Icc_subset_Icc_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
  proof: ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans h'⟩⟩

@[to_dual none]

中文:
定理 Icc_subset_Icc_iff
  条件: (h₁ : a₁ <= b₁)
  结论: Icc a₁ b₁ subseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
  证明: ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans h'⟩⟩

@[to_dual none]

Depends on / 依赖: h.trans, le_rfl
-/
theorem Icc_subset_Icc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans h'⟩⟩

@[to_dual none]
/--
theorem `Icc_subset_Ioo_iff` / 定理 `Icc_subset_Ioo_iff`

English:
theorem Icc_subset_Ioo_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂
  proof: ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]

中文:
定理 Icc_subset_Ioo_iff
  条件: (h₁ : a₁ <= b₁)
  结论: Icc a₁ b₁ subseteq Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂
  证明: ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]

Depends on / 依赖: h.trans_le, le_rfl, trans_le, trans_lt
-/
theorem Icc_subset_Ioo_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]
/--
theorem `Icc_subset_Ico_iff` / 定理 `Icc_subset_Ico_iff`

English:
theorem Icc_subset_Ico_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ < b₂
  proof: ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]

中文:
定理 Icc_subset_Ico_iff
  条件: (h₁ : a₁ <= b₁)
  结论: Icc a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ < b₂
  证明: ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]

Depends on / 依赖: h.trans, le_rfl, trans_lt
-/
theorem Icc_subset_Ico_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]
/--
theorem `Icc_subset_Ioc_iff` / 定理 `Icc_subset_Ioc_iff`

English:
theorem Icc_subset_Ioc_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ <= b₂
  proof: ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans h'⟩⟩

@[to_dual]

中文:
定理 Icc_subset_Ioc_iff
  条件: (h₁ : a₁ <= b₁)
  结论: Icc a₁ b₁ subseteq Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ <= b₂
  证明: ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans h'⟩⟩

@[to_dual]

Depends on / 依赖: h.trans_le, le_rfl, trans_le
-/
theorem Icc_subset_Ioc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ <= b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans h'⟩⟩

@[to_dual]
/--
theorem `Icc_subset_Ioi_iff` / 定理 `Icc_subset_Ioi_iff`

English:
theorem Icc_subset_Ioi_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Ioi a₂ ↔ a₂ < a₁
  proof: ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans_le hx.1⟩

@[to_dual]

中文:
定理 Icc_subset_Ioi_iff
  条件: (h₁ : a₁ <= b₁)
  结论: Icc a₁ b₁ subseteq Ioi a₂ ↔ a₂ < a₁
  证明: ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans_le hx.1⟩

@[to_dual]

Depends on / 依赖: h.trans_le, le_rfl, trans_le
-/
theorem Icc_subset_Ioi_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioi a₂ ↔ a₂ < a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans_le hx.1⟩

@[to_dual]
/--
theorem `Icc_subset_Ici_iff` / 定理 `Icc_subset_Ici_iff`

English:
theorem Icc_subset_Ici_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Ici a₂ ↔ a₂ <= a₁
  proof: ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans hx.1⟩

中文:
定理 Icc_subset_Ici_iff
  条件: (h₁ : a₁ <= b₁)
  结论: Icc a₁ b₁ subseteq Ici a₂ ↔ a₂ <= a₁
  证明: ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans hx.1⟩

Depends on / 依赖: h.trans, le_rfl
-/
theorem Icc_subset_Ici_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ici a₂ ↔ a₂ <= a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans hx.1⟩

/--
theorem `Ici_inter_Iic` / 定理 `Ici_inter_Iic`

English:
theorem Ici_inter_Iic
  statement: Ici a inter Iic b = Icc a b
  proof: rfl

中文:
定理 Ici_inter_Iic
  结论: Ici a inter Iic b = Icc a b
  证明: rfl
-/
@[to_dual] theorem Ici_inter_Iic : Ici a inter Iic b = Icc a b := rfl
/--
theorem `Ici_inter_Iio` / 定理 `Ici_inter_Iio`

English:
theorem Ici_inter_Iio
  statement: Ici a inter Iio b = Ico a b
  proof: rfl

中文:
定理 Ici_inter_Iio
  结论: Ici a inter Iio b = Ico a b
  证明: rfl
-/
@[to_dual] theorem Ici_inter_Iio : Ici a inter Iio b = Ico a b := rfl
/--
theorem `Ioi_inter_Iic` / 定理 `Ioi_inter_Iic`

English:
theorem Ioi_inter_Iic
  statement: Ioi a inter Iic b = Ioc a b
  proof: rfl

中文:
定理 Ioi_inter_Iic
  结论: Ioi a inter Iic b = Ioc a b
  证明: rfl
-/
@[to_dual] theorem Ioi_inter_Iic : Ioi a inter Iic b = Ioc a b := rfl
/--
theorem `Ioi_inter_Iio` / 定理 `Ioi_inter_Iio`

English:
theorem Ioi_inter_Iio
  statement: Ioi a inter Iio b = Ioo a b
  proof: rfl

中文:
定理 Ioi_inter_Iio
  结论: Ioi a inter Iio b = Ioo a b
  证明: rfl
-/
@[to_dual] theorem Ioi_inter_Iio : Ioi a inter Iio b = Ioo a b := rfl

/--
theorem `mem_Icc_of_Ioo` / 定理 `mem_Icc_of_Ioo`

English:
theorem mem_Icc_of_Ioo
  given: (h : x in Ioo a b)
  statement: x in Icc a b
  proof: Ioo_subset_Icc_self h

中文:
定理 mem_Icc_of_Ioo
  条件: (h : x in Ioo a b)
  结论: x in Icc a b
  证明: Ioo_subset_Icc_self h
-/
@[to_dual self] theorem mem_Icc_of_Ioo (h : x in Ioo a b) : x in Icc a b := Ioo_subset_Icc_self h
/--
theorem `mem_Ico_of_Ioo` / 定理 `mem_Ico_of_Ioo`

English:
theorem mem_Ico_of_Ioo
  given: (h : x in Ioo a b)
  statement: x in Ico a b
  proof: Ioo_subset_Ico_self h

中文:
定理 mem_Ico_of_Ioo
  条件: (h : x in Ioo a b)
  结论: x in Ico a b
  证明: Ioo_subset_Ico_self h
-/
@[to_dual] theorem mem_Ico_of_Ioo (h : x in Ioo a b) : x in Ico a b := Ioo_subset_Ico_self h
/--
theorem `mem_Icc_of_Ioc` / 定理 `mem_Icc_of_Ioc`

English:
theorem mem_Icc_of_Ioc
  given: (h : x in Ioc a b)
  statement: x in Icc a b
  proof: Ioc_subset_Icc_self h

中文:
定理 mem_Icc_of_Ioc
  条件: (h : x in Ioc a b)
  结论: x in Icc a b
  证明: Ioc_subset_Icc_self h
-/
@[to_dual] theorem mem_Icc_of_Ioc (h : x in Ioc a b) : x in Icc a b := Ioc_subset_Icc_self h
/--
theorem `mem_Iic_of_Iio` / 定理 `mem_Iic_of_Iio`

English:
theorem mem_Iic_of_Iio
  given: (h : x in Iio a)
  statement: x in Iic a
  proof: Iio_subset_Iic_self h

@[to_dual self]

中文:
定理 mem_Iic_of_Iio
  条件: (h : x in Iio a)
  结论: x in Iic a
  证明: Iio_subset_Iic_self h

@[to_dual self]
-/
@[to_dual] theorem mem_Iic_of_Iio (h : x in Iio a) : x in Iic a := Iio_subset_Iic_self h

@[to_dual self]
/--
theorem `Icc_eq_empty_iff` / 定理 `Icc_eq_empty_iff`

English:
theorem Icc_eq_empty_iff
  statement: Icc a b = ∅ ↔ ¬a <= b
  proof: by
  contrapose!; exact nonempty_Icc

@[to_dual]

中文:
定理 Icc_eq_empty_iff
  结论: Icc a b = ∅ ↔ ¬a <= b
  证明: by
  contrapose!; exact nonempty_Icc

@[to_dual]

Depends on / 依赖: contrapose, nonempty_Icc
-/
theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a <= b := by
  contrapose!; exact nonempty_Icc

@[to_dual]
/--
theorem `Ico_eq_empty_iff` / 定理 `Ico_eq_empty_iff`

English:
theorem Ico_eq_empty_iff
  statement: Ico a b = ∅ ↔ ¬a < b
  proof: by
  contrapose!; exact nonempty_Ico

@[to_dual self]

中文:
定理 Ico_eq_empty_iff
  结论: Ico a b = ∅ ↔ ¬a < b
  证明: by
  contrapose!; exact nonempty_Ico

@[to_dual self]

Depends on / 依赖: contrapose, nonempty_Ico
-/
theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  contrapose!; exact nonempty_Ico

@[to_dual self]
/--
theorem `Ioo_eq_empty_iff` / 定理 `Ioo_eq_empty_iff`

English:
theorem Ioo_eq_empty_iff
  given: [DenselyOrdered α]
  statement: Ioo a b = ∅ ↔ ¬a < b
  proof: by
  contrapose!; exact nonempty_Ioo

@[to_dual]

中文:
定理 Ioo_eq_empty_iff
  条件: [DenselyOrdered α]
  结论: Ioo a b = ∅ ↔ ¬a < b
  证明: by
  contrapose!; exact nonempty_Ioo

@[to_dual]

Depends on / 依赖: contrapose, nonempty_Ioo
-/
theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  contrapose!; exact nonempty_Ioo

@[to_dual]
/--
theorem `_root_.IsTop.Iic_eq` / 定理 `_root_.IsTop.Iic_eq`

English:
theorem _root_.IsTop.Iic_eq
  given: (h : IsTop a)
  statement: Iic a = univ
  proof: eq_univ_of_forall h

@[to_dual (attr := simp)]

中文:
定理 _root_.IsTop.Iic_eq
  条件: (h : IsTop a)
  结论: Iic a = univ
  证明: eq_univ_of_forall h

@[to_dual (attr := simp)]

Depends on / 依赖: eq_univ_of_forall
-/
theorem _root_.IsTop.Iic_eq (h : IsTop a) : Iic a = univ :=
  eq_univ_of_forall h

@[to_dual (attr := simp)]
/--
theorem `Iio_eq_empty_iff` / 定理 `Iio_eq_empty_iff`

English:
theorem Iio_eq_empty_iff
  statement: Iio a = ∅ ↔ IsMin a
  proof: by
  simp only [isMin_iff_forall_not_lt, eq_empty_iff_forall_notMem, mem_Iio]

@[to_dual (attr := simp)] alias ⟨_, _root_.IsMin.Iio_eq⟩ := Iio_eq_empty_iff

@[to_dual (attr := simp)]

中文:
定理 Iio_eq_empty_iff
  结论: Iio a = ∅ ↔ IsMin a
  证明: by
  simp only [isMin_iff_forall_not_lt, eq_empty_iff_forall_notMem, mem_Iio]

@[to_dual (attr := simp)] alias ⟨_, _root_.IsMin.Iio_eq⟩ := Iio_eq_empty_iff

@[to_dual (attr := simp)]

Depends on / 依赖: eq_empty_iff_forall_notMem, isMin_iff_forall_not_lt, mem_Iio
-/
theorem Iio_eq_empty_iff : Iio a = ∅ ↔ IsMin a := by
  simp only [isMin_iff_forall_not_lt, eq_empty_iff_forall_notMem, mem_Iio]

@[to_dual (attr := simp)] alias ⟨_, _root_.IsMin.Iio_eq⟩ := Iio_eq_empty_iff

@[to_dual (attr := simp)]
/--
lemma `Iio_nonempty` / 引理 `Iio_nonempty`

English:
lemma Iio_nonempty
  statement: (Iio a).Nonempty ↔ ¬ IsMin a
  proof: by simp [nonempty_iff_ne_empty]

@[to_dual]

中文:
引理 Iio_nonempty
  结论: (Iio a).Nonempty ↔ ¬ IsMin a
  证明: by simp [nonempty_iff_ne_empty]

@[to_dual]

Depends on / 依赖: nonempty_iff_ne_empty
-/
lemma Iio_nonempty : (Iio a).Nonempty ↔ ¬ IsMin a := by simp [nonempty_iff_ne_empty]

@[to_dual]
/--
theorem `Iic_inter_Ioc_of_le` / 定理 `Iic_inter_Ioc_of_le`

English:
theorem Iic_inter_Ioc_of_le
  given: (h : a <= c)
  statement: Iic a inter Ioc b c = Ioc b a
  proof: ext fun _ => ⟨fun H => ⟨H.2.1, H.1⟩, fun H => ⟨H.2, H.1, H.2.trans h⟩⟩

@[to_dual notMem_Icc_of_gt]

中文:
定理 Iic_inter_Ioc_of_le
  条件: (h : a <= c)
  结论: Iic a inter Ioc b c = Ioc b a
  证明: ext fun _ => ⟨fun H => ⟨H.2.1, H.1⟩, fun H => ⟨H.2, H.1, H.2.trans h⟩⟩

@[to_dual notMem_Icc_of_gt]
-/
theorem Iic_inter_Ioc_of_le (h : a <= c) : Iic a inter Ioc b c = Ioc b a :=
  ext fun _ => ⟨fun H => ⟨H.2.1, H.1⟩, fun H => ⟨H.2, H.1, H.2.trans h⟩⟩

@[to_dual notMem_Icc_of_gt]
/--
theorem `notMem_Icc_of_lt` / 定理 `notMem_Icc_of_lt`

English:
theorem notMem_Icc_of_lt
  given: (ha : c < a)
  statement: c ∉ Icc a b
  proof: fun h => ha.not_ge h.1

@[to_dual notMem_Ioc_of_gt]

中文:
定理 notMem_Icc_of_lt
  条件: (ha : c < a)
  结论: c ∉ Icc a b
  证明: fun h => ha.not_ge h.1

@[to_dual notMem_Ioc_of_gt]

Depends on / 依赖: ha.not_ge, not_ge
-/
theorem notMem_Icc_of_lt (ha : c < a) : c ∉ Icc a b := fun h => ha.not_ge h.1

@[to_dual notMem_Ioc_of_gt]
/--
theorem `notMem_Ico_of_lt` / 定理 `notMem_Ico_of_lt`

English:
theorem notMem_Ico_of_lt
  given: (ha : c < a)
  statement: c ∉ Ico a b
  proof: fun h => ha.not_ge h.1

@[deprecated (since := "2026-02-10")] alias notMem_Ioi_self := self_notMem_Ioi

@[deprecated (since := "2026-02-10")] alias notMem_Iio_self := self_notMem_Iio

@[to_dual notMem_Ico_of_ge]

中文:
定理 notMem_Ico_of_lt
  条件: (ha : c < a)
  结论: c ∉ Ico a b
  证明: fun h => ha.not_ge h.1

@[deprecated (since := "2026-02-10")] alias notMem_Ioi_self := self_notMem_Ioi

@[deprecated (since := "2026-02-10")] alias notMem_Iio_self := self_notMem_Iio

@[to_dual notMem_Ico_of_ge]

Depends on / 依赖: ha.not_ge, not_ge
-/
theorem notMem_Ico_of_lt (ha : c < a) : c ∉ Ico a b := fun h => ha.not_ge h.1

@[deprecated (since := "2026-02-10")] alias notMem_Ioi_self := self_notMem_Ioi

@[deprecated (since := "2026-02-10")] alias notMem_Iio_self := self_notMem_Iio

@[to_dual notMem_Ico_of_ge]
/--
theorem `notMem_Ioc_of_le` / 定理 `notMem_Ioc_of_le`

English:
theorem notMem_Ioc_of_le
  given: (ha : c <= a)
  statement: c ∉ Ioc a b
  proof: fun h => lt_irrefl _ h.1.trans_le ha

@[to_dual notMem_Ioo_of_ge]

中文:
定理 notMem_Ioc_of_le
  条件: (ha : c <= a)
  结论: c ∉ Ioc a b
  证明: fun h => lt_irrefl _ h.1.trans_le ha

@[to_dual notMem_Ioo_of_ge]

Depends on / 依赖: lt_irrefl, trans_le
-/
theorem notMem_Ioc_of_le (ha : c <= a) : c ∉ Ioc a b := fun h => lt_irrefl _ h.1.trans_le ha

@[to_dual notMem_Ioo_of_ge]
/--
theorem `notMem_Ioo_of_le` / 定理 `notMem_Ioo_of_le`

English:
theorem notMem_Ioo_of_le
  given: (ha : c <= a)
  statement: c ∉ Ioo a b
  proof: fun h => lt_irrefl _ h.1.trans_le ha

中文:
定理 notMem_Ioo_of_le
  条件: (ha : c <= a)
  结论: c ∉ Ioo a b
  证明: fun h => lt_irrefl _ h.1.trans_le ha

Depends on / 依赖: lt_irrefl, trans_le
-/
theorem notMem_Ioo_of_le (ha : c <= a) : c ∉ Ioo a b := fun h => lt_irrefl _ h.1.trans_le ha

section matched_intervals

/--
theorem `Icc_eq_Ioc_same_iff` / 定理 `Icc_eq_Ioc_same_iff`

English:
theorem Icc_eq_Ioc_same_iff
  statement: Icc a b = Ioc a b ↔ ¬a <= b where
  proof: by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Icc_eq_empty h, Ioc_eq_empty (mt le_of_lt h)]

中文:
定理 Icc_eq_Ioc_same_iff
  结论: Icc a b = Ioc a b ↔ ¬a <= b where
  证明: by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Icc_eq_empty h, Ioc_eq_empty (mt le_of_lt h)]
-/
@[to_dual (attr := simp)] theorem Icc_eq_Ioc_same_iff : Icc a b = Ioc a b ↔ ¬a <= b where
  mp h := by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Icc_eq_empty h, Ioc_eq_empty (mt le_of_lt h)]

/--
theorem `Ioc_eq_Icc_same_iff` / 定理 `Ioc_eq_Icc_same_iff`

English:
theorem Ioc_eq_Icc_same_iff
  statement: Ioc a b = Icc a b ↔ ¬a <= b
  proof: eq_comm.trans Icc_eq_Ioc_same_iff

中文:
定理 Ioc_eq_Icc_same_iff
  结论: Ioc a b = Icc a b ↔ ¬a <= b
  证明: eq_comm.trans Icc_eq_Ioc_same_iff
-/
@[to_dual (attr := simp)] theorem Ioc_eq_Icc_same_iff : Ioc a b = Icc a b ↔ ¬a <= b :=
  eq_comm.trans Icc_eq_Ioc_same_iff

/--
theorem `Icc_eq_Ioo_same_iff` / 定理 `Icc_eq_Ioo_same_iff`

English:
theorem Icc_eq_Ioo_same_iff
  statement: Icc a b = Ioo a b ↔ ¬a <= b where
  proof: by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Icc_eq_empty h, Ioo_eq_empty (mt le_of_lt h)]

中文:
定理 Icc_eq_Ioo_same_iff
  结论: Icc a b = Ioo a b ↔ ¬a <= b where
  证明: by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Icc_eq_empty h, Ioo_eq_empty (mt le_of_lt h)]
-/
@[simp, to_dual self] theorem Icc_eq_Ioo_same_iff : Icc a b = Ioo a b ↔ ¬a <= b where
  mp h := by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Icc_eq_empty h, Ioo_eq_empty (mt le_of_lt h)]

/--
theorem `Ioo_eq_Icc_same_iff` / 定理 `Ioo_eq_Icc_same_iff`

English:
theorem Ioo_eq_Icc_same_iff
  statement: Ioo a b = Icc a b ↔ ¬a <= b
  proof: eq_comm.trans Icc_eq_Ioo_same_iff

中文:
定理 Ioo_eq_Icc_same_iff
  结论: Ioo a b = Icc a b ↔ ¬a <= b
  证明: eq_comm.trans Icc_eq_Ioo_same_iff
-/
@[simp, to_dual self] theorem Ioo_eq_Icc_same_iff : Ioo a b = Icc a b ↔ ¬a <= b :=
  eq_comm.trans Icc_eq_Ioo_same_iff

/--
theorem `Ioc_eq_Ico_same_iff` / 定理 `Ioc_eq_Ico_same_iff`

English:
theorem Ioc_eq_Ico_same_iff
  statement: Ioc a b = Ico a b ↔ ¬a < b where
  proof: by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Ioc_eq_empty h, Ico_eq_empty h]

中文:
定理 Ioc_eq_Ico_same_iff
  结论: Ioc a b = Ico a b ↔ ¬a < b where
  证明: by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Ioc_eq_empty h, Ico_eq_empty h]
-/
@[to_dual (attr := simp)] theorem Ioc_eq_Ico_same_iff : Ioc a b = Ico a b ↔ ¬a < b where
  mp h := by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Ioc_eq_empty h, Ico_eq_empty h]

/--
theorem `Ioo_eq_Ioc_same_iff` / 定理 `Ioo_eq_Ioc_same_iff`

English:
theorem Ioo_eq_Ioc_same_iff
  statement: Ioo a b = Ioc a b ↔ ¬a < b where
  proof: by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Ioo_eq_empty h, Ioc_eq_empty h]

中文:
定理 Ioo_eq_Ioc_same_iff
  结论: Ioo a b = Ioc a b ↔ ¬a < b where
  证明: by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Ioo_eq_empty h, Ioc_eq_empty h]
-/
@[to_dual (attr := simp)] theorem Ioo_eq_Ioc_same_iff : Ioo a b = Ioc a b ↔ ¬a < b where
  mp h := by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Ioo_eq_empty h, Ioc_eq_empty h]

/--
theorem `Ioc_eq_Ioo_same_iff` / 定理 `Ioc_eq_Ioo_same_iff`

English:
theorem Ioc_eq_Ioo_same_iff
  statement: Ioc a b = Ioo a b ↔ ¬a < b
  proof: eq_comm.trans Ioo_eq_Ioc_same_iff

中文:
定理 Ioc_eq_Ioo_same_iff
  结论: Ioc a b = Ioo a b ↔ ¬a < b
  证明: eq_comm.trans Ioo_eq_Ioc_same_iff
-/
@[to_dual (attr := simp)] theorem Ioc_eq_Ioo_same_iff : Ioc a b = Ioo a b ↔ ¬a < b :=
  eq_comm.trans Ioo_eq_Ioc_same_iff

end matched_intervals

@[to_additive (attr := simp)]
/--
lemma `Ici_one_eq_univ` / 引理 `Ici_one_eq_univ`

English:
lemma Ici_one_eq_univ
  given: [One α] [IsBotOneClass α]
  statement: Ici (1 : α) = univ
  proof: by ext; simp

中文:
引理 Ici_one_eq_univ
  条件: [One α] [IsBotOneClass α]
  结论: Ici (1 : α) = univ
  证明: by ext; simp
-/
lemma Ici_one_eq_univ [One α] [IsBotOneClass α] : Ici (1 : α) = univ := by ext; simp

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[simp]
/--
theorem `Icc_self` / 定理 `Icc_self`

English:
theorem Icc_self
  given: (a : α)
  statement: Icc a a = {a}
  proof: Set.ext by simp [Icc, le_antisymm_iff, and_comm]

中文:
定理 Icc_self
  条件: (a : α)
  结论: Icc a a = {a}
  证明: Set.ext by simp [Icc, le_antisymm_iff, and_comm]

Depends on / 依赖: Set.ext, and_comm, le_antisymm_iff
-/
theorem Icc_self (a : α) : Icc a a = {a} :=
Set.ext by simp [Icc, le_antisymm_iff, and_comm]

/--
Instance `instIccUnique` / 实例 `instIccUnique`

English:
instance instIccUnique
  signature: : Unique (Icc a a) where
  body: ⟨a, by simp⟩
uniq y := Subtype.ext by simpa using y.2

@[simp, to_dual none]

中文:
实例 instIccUnique
  签名: : Unique (Icc a a) where
  定义体: ⟨a, by simp⟩
uniq y := Subtype.ext by simpa using y.2

@[simp, to_dual none]
-/
instance instIccUnique : Unique (Icc a a) where
  default := ⟨a, by simp⟩
uniq y := Subtype.ext by simpa using y.2

@[simp, to_dual none]
/--
theorem `Icc_eq_singleton_iff` / 定理 `Icc_eq_singleton_iff`

English:
theorem Icc_eq_singleton_iff
  statement: Icc a b = {c} ↔ a = c ∧ b = c
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · have hab : a <= b := nonempty_Icc.1 (h.symm.subst <| singleton_nonempty c)
    exact
⟨eq_of_mem_singleton h ▸ left_mem_Icc.2 hab,
eq_of_mem_singleton h ▸ right_mem_Icc.2 hab⟩
  · rintro ⟨rfl, rfl⟩
    exact Icc_self _

@[to_dual self]

中文:
定理 Icc_eq_singleton_iff
  结论: Icc a b = {c} ↔ a = c ∧ b = c
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · have hab : a <= b := nonempty_Icc.1 (h.symm.subst <| singleton_nonempty c)
    exact
⟨eq_of_mem_singleton h ▸ left_mem_Icc.2 hab,
eq_of_mem_singleton h ▸ right_mem_Icc.2 hab⟩
  · rintro ⟨rfl, rfl⟩
    exact Icc_self _

@[to_dual self]

Depends on / 依赖: Icc_self, eq_of_mem_singleton, h.symm.subst, left_mem_Icc, nonempty_Icc, right_mem_Icc, singleton_nonempty
-/
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  refine ⟨fun h => ?_, ?_⟩
  · have hab : a <= b := nonempty_Icc.1 (h.symm.subst <| singleton_nonempty c)
    exact
⟨eq_of_mem_singleton h ▸ left_mem_Icc.2 hab,
eq_of_mem_singleton h ▸ right_mem_Icc.2 hab⟩
  · rintro ⟨rfl, rfl⟩
    exact Icc_self _

@[to_dual self]
/--
lemma `subsingleton_Icc_of_ge` / 引理 `subsingleton_Icc_of_ge`

English:
lemma subsingleton_Icc_of_ge
  given: (hba : b <= a)
  statement: Set.Subsingleton (Icc a b)
  proof: fun _x ⟨hax, hxb⟩ _y ⟨hay, hyb⟩ => le_antisymm
    (le_imp_le_of_le_of_le hxb hay hba) (le_imp_le_of_le_of_le hyb hax hba)

@[simp, to_dual self]

中文:
引理 subsingleton_Icc_of_ge
  条件: (hba : b <= a)
  结论: Set.Subsingleton (Icc a b)
  证明: fun _x ⟨hax, hxb⟩ _y ⟨hay, hyb⟩ => le_antisymm
    (le_imp_le_of_le_of_le hxb hay hba) (le_imp_le_of_le_of_le hyb hax hba)

@[simp, to_dual self]

Depends on / 依赖: le_antisymm, le_imp_le_of_le_of_le
-/
lemma subsingleton_Icc_of_ge (hba : b <= a) : Set.Subsingleton (Icc a b) :=
  fun _x ⟨hax, hxb⟩ _y ⟨hay, hyb⟩ => le_antisymm
    (le_imp_le_of_le_of_le hxb hay hba) (le_imp_le_of_le_of_le hyb hax hba)

@[simp, to_dual self]
/--
lemma `subsingleton_Icc_iff` / 引理 `subsingleton_Icc_iff`

English:
lemma subsingleton_Icc_iff
  given: {α : Type*} [LinearOrder α] {a b : α}
  proof: by
  refine ⟨fun h => ?_, subsingleton_Icc_of_ge⟩
  contrapose! h
  exact ⟨a, ⟨le_refl _, h.le⟩, b, ⟨h.le, le_refl _⟩, h.ne⟩

@[to_dual (attr := simp)]

中文:
引理 subsingleton_Icc_iff
  条件: {α : 类型} [LinearOrder α] {a b : α}
  证明: by
  refine ⟨fun h => ?_, subsingleton_Icc_of_ge⟩
  contrapose! h
  exact ⟨a, ⟨le_refl _, h.le⟩, b, ⟨h.le, le_refl _⟩, h.ne⟩

@[to_dual (attr := simp)]

Depends on / 依赖: contrapose, h.le, h.ne, le_refl, subsingleton_Icc_of_ge
-/
lemma subsingleton_Icc_iff {α : Type*} [LinearOrder α] {a b : α} :
    Set.Subsingleton (Icc a b) ↔ b <= a := by
  refine ⟨fun h => ?_, subsingleton_Icc_of_ge⟩
  contrapose! h
  exact ⟨a, ⟨le_refl _, h.le⟩, b, ⟨h.le, le_refl _⟩, h.ne⟩

@[to_dual (attr := simp)]
/--
theorem `Icc_sdiff_left` / 定理 `Icc_sdiff_left`

English:
theorem Icc_sdiff_left
  statement: Icc a b \ {a} = Ioc a b
  proof: ext fun x => by simp [lt_iff_le_and_ne, eq_comm, and_right_comm]

@[deprecated (since := "2026-06-03")] alias Icc_diff_left := Icc_sdiff_left

@[to_dual (attr := simp)]

中文:
定理 Icc_sdiff_left
  结论: Icc a b \ {a} = Ioc a b
  证明: ext fun x => by simp [lt_iff_le_and_ne, eq_comm, and_right_comm]

@[deprecated (since := "2026-06-03")] alias Icc_diff_left := Icc_sdiff_left

@[to_dual (attr := simp)]

Depends on / 依赖: and_right_comm, eq_comm, lt_iff_le_and_ne
-/
theorem Icc_sdiff_left : Icc a b \ {a} = Ioc a b :=
  ext fun x => by simp [lt_iff_le_and_ne, eq_comm, and_right_comm]

@[deprecated (since := "2026-06-03")] alias Icc_diff_left := Icc_sdiff_left

@[to_dual (attr := simp)]
/--
theorem `Ico_sdiff_left` / 定理 `Ico_sdiff_left`

English:
theorem Ico_sdiff_left
  statement: Ico a b \ {a} = Ioo a b
  proof: ext fun x => by simp [and_right_comm, ← lt_iff_le_and_ne, eq_comm]

@[deprecated (since := "2026-06-03")] alias Ico_diff_left := Ico_sdiff_left

@[simp, to_dual none]

中文:
定理 Ico_sdiff_left
  结论: Ico a b \ {a} = Ioo a b
  证明: ext fun x => by simp [and_right_comm, ← lt_iff_le_and_ne, eq_comm]

@[deprecated (since := "2026-06-03")] alias Ico_diff_left := Ico_sdiff_left

@[simp, to_dual none]

Depends on / 依赖: and_right_comm, eq_comm, lt_iff_le_and_ne
-/
theorem Ico_sdiff_left : Ico a b \ {a} = Ioo a b :=
  ext fun x => by simp [and_right_comm, ← lt_iff_le_and_ne, eq_comm]

@[deprecated (since := "2026-06-03")] alias Ico_diff_left := Ico_sdiff_left

@[simp, to_dual none]
/--
theorem `Icc_sdiff_both` / 定理 `Icc_sdiff_both`

English:
theorem Icc_sdiff_both
  statement: Icc a b \ {a, b} = Ioo a b
  proof: by
  rw [insert_eq]; rw [← sdiff_sdiff]; rw [Icc_sdiff_left]; rw [Ioc_sdiff_right]

@[deprecated (since := "2026-06-03")] alias Icc_diff_both := Icc_sdiff_both

@[to_dual (attr := simp)]

中文:
定理 Icc_sdiff_both
  结论: Icc a b \ {a, b} = Ioo a b
  证明: by
  rw [insert_eq]; rw [← sdiff_sdiff]; rw [Icc_sdiff_left]; rw [Ioc_sdiff_right]

@[deprecated (since := "2026-06-03")] alias Icc_diff_both := Icc_sdiff_both

@[to_dual (attr := simp)]

Depends on / 依赖: Icc_sdiff_left, Ioc_sdiff_right, insert_eq, sdiff_sdiff
-/
theorem Icc_sdiff_both : Icc a b \ {a, b} = Ioo a b := by
  rw [insert_eq]; rw [← sdiff_sdiff]; rw [Icc_sdiff_left]; rw [Ioc_sdiff_right]

@[deprecated (since := "2026-06-03")] alias Icc_diff_both := Icc_sdiff_both

@[to_dual (attr := simp)]
/--
theorem `Iic_sdiff_right` / 定理 `Iic_sdiff_right`

English:
theorem Iic_sdiff_right
  statement: Iic a \ {a} = Iio a
  proof: ext fun x => by simp [lt_iff_le_and_ne]

@[deprecated (since := "2026-06-03")] alias Iic_diff_right := Iic_sdiff_right

@[to_dual (attr := simp)]

中文:
定理 Iic_sdiff_right
  结论: Iic a \ {a} = Iio a
  证明: ext fun x => by simp [lt_iff_le_and_ne]

@[deprecated (since := "2026-06-03")] alias Iic_diff_right := Iic_sdiff_right

@[to_dual (attr := simp)]

Depends on / 依赖: lt_iff_le_and_ne
-/
theorem Iic_sdiff_right : Iic a \ {a} = Iio a :=
  ext fun x => by simp [lt_iff_le_and_ne]

@[deprecated (since := "2026-06-03")] alias Iic_diff_right := Iic_sdiff_right

@[to_dual (attr := simp)]
/--
theorem `Ico_sdiff_Ioo_same` / 定理 `Ico_sdiff_Ioo_same`

English:
theorem Ico_sdiff_Ioo_same
  given: (h : a < b)
  statement: Ico a b \ Ioo a b = {a}
  proof: by
  rw [← Ico_sdiff_left]; rw [sdiff_sdiff_cancel_left (singleton_subset_iff.2 <| left_mem_Ico.2 h)]

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ioo_same := Ico_sdiff_Ioo_same

@[to_dual (attr := simp)]

中文:
定理 Ico_sdiff_Ioo_same
  条件: (h : a < b)
  结论: Ico a b \ Ioo a b = {a}
  证明: by
  rw [← Ico_sdiff_left]; rw [sdiff_sdiff_cancel_left (singleton_subset_iff.2 <| left_mem_Ico.2 h)]

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ioo_same := Ico_sdiff_Ioo_same

@[to_dual (attr := simp)]

Depends on / 依赖: Ico_sdiff_left, left_mem_Ico, sdiff_sdiff_cancel_left, singleton_subset_iff
-/
theorem Ico_sdiff_Ioo_same (h : a < b) : Ico a b \ Ioo a b = {a} := by
  rw [← Ico_sdiff_left]; rw [sdiff_sdiff_cancel_left (singleton_subset_iff.2 <| left_mem_Ico.2 h)]

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ioo_same := Ico_sdiff_Ioo_same

@[to_dual (attr := simp)]
/--
theorem `Icc_sdiff_Ico_same` / 定理 `Icc_sdiff_Ico_same`

English:
theorem Icc_sdiff_Ico_same
  given: (h : a <= b)
  statement: Icc a b \ Ico a b = {b}
  proof: by
  rw [← Icc_sdiff_right]; rw [sdiff_sdiff_cancel_left (singleton_subset_iff.2 <| right_mem_Icc.2 h)]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ico_same := Icc_sdiff_Ico_same

@[simp, to_dual none]

中文:
定理 Icc_sdiff_Ico_same
  条件: (h : a <= b)
  结论: Icc a b \ Ico a b = {b}
  证明: by
  rw [← Icc_sdiff_right]; rw [sdiff_sdiff_cancel_left (singleton_subset_iff.2 <| right_mem_Icc.2 h)]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ico_same := Icc_sdiff_Ico_same

@[simp, to_dual none]

Depends on / 依赖: Icc_sdiff_right, right_mem_Icc, sdiff_sdiff_cancel_left, singleton_subset_iff
-/
theorem Icc_sdiff_Ico_same (h : a <= b) : Icc a b \ Ico a b = {b} := by
  rw [← Icc_sdiff_right]; rw [sdiff_sdiff_cancel_left (singleton_subset_iff.2 <| right_mem_Icc.2 h)]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ico_same := Icc_sdiff_Ico_same

@[simp, to_dual none]
/--
theorem `Icc_sdiff_Ioo_same` / 定理 `Icc_sdiff_Ioo_same`

English:
theorem Icc_sdiff_Ioo_same
  given: (h : a <= b)
  statement: Icc a b \ Ioo a b = {a, b}
  proof: by
  rw [← Icc_sdiff_both]; rw [sdiff_sdiff_cancel_left]
  simp [insert_subset_iff, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioo_same := Icc_sdiff_Ioo_same

@[to_dual (attr := simp)]

中文:
定理 Icc_sdiff_Ioo_same
  条件: (h : a <= b)
  结论: Icc a b \ Ioo a b = {a, b}
  证明: by
  rw [← Icc_sdiff_both]; rw [sdiff_sdiff_cancel_left]
  simp [insert_subset_iff, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioo_same := Icc_sdiff_Ioo_same

@[to_dual (attr := simp)]

Depends on / 依赖: Icc_sdiff_both, insert_subset_iff, sdiff_sdiff_cancel_left
-/
theorem Icc_sdiff_Ioo_same (h : a <= b) : Icc a b \ Ioo a b = {a, b} := by
  rw [← Icc_sdiff_both]; rw [sdiff_sdiff_cancel_left]
  simp [insert_subset_iff, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioo_same := Icc_sdiff_Ioo_same

@[to_dual (attr := simp)]
/--
theorem `Iic_sdiff_Iio_same` / 定理 `Iic_sdiff_Iio_same`

English:
theorem Iic_sdiff_Iio_same
  statement: Iic a \ Iio a = {a}
  proof: by
  rw [← Iic_sdiff_right]; rw [sdiff_sdiff_cancel_left (singleton_subset_iff.2 self_mem_Iic)]

@[deprecated (since := "2026-06-03")] alias Iic_diff_Iio_same := Iic_sdiff_Iio_same

@[to_dual]

中文:
定理 Iic_sdiff_Iio_same
  结论: Iic a \ Iio a = {a}
  证明: by
  rw [← Iic_sdiff_right]; rw [sdiff_sdiff_cancel_left (singleton_subset_iff.2 self_mem_Iic)]

@[deprecated (since := "2026-06-03")] alias Iic_diff_Iio_same := Iic_sdiff_Iio_same

@[to_dual]

Depends on / 依赖: Iic_sdiff_right, sdiff_sdiff_cancel_left, self_mem_Iic, singleton_subset_iff
-/
theorem Iic_sdiff_Iio_same : Iic a \ Iio a = {a} := by
  rw [← Iic_sdiff_right]; rw [sdiff_sdiff_cancel_left (singleton_subset_iff.2 self_mem_Iic)]

@[deprecated (since := "2026-06-03")] alias Iic_diff_Iio_same := Iic_sdiff_Iio_same

@[to_dual]
/--
theorem `Iio_union_right` / 定理 `Iio_union_right`

English:
theorem Iio_union_right
  statement: Iio a union {a} = Iic a
  proof: ext fun _ => le_iff_lt_or_eq.symm

@[to_dual]

中文:
定理 Iio_union_right
  结论: Iio a union {a} = Iic a
  证明: ext fun _ => le_iff_lt_or_eq.symm

@[to_dual]

Depends on / 依赖: le_iff_lt_or_eq, le_iff_lt_or_eq.symm
-/
theorem Iio_union_right : Iio a union {a} = Iic a :=
  ext fun _ => le_iff_lt_or_eq.symm

@[to_dual]
/--
theorem `Ioo_union_left` / 定理 `Ioo_union_left`

English:
theorem Ioo_union_left
  given: (hab : a < b)
  statement: Ioo a b union {a} = Ico a b
  proof: by
  rw [← Ico_sdiff_left]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Ico.2 hab)]

@[to_dual none]

中文:
定理 Ioo_union_left
  条件: (hab : a < b)
  结论: Ioo a b union {a} = Ico a b
  证明: by
  rw [← Ico_sdiff_left]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Ico.2 hab)]

@[to_dual none]

Depends on / 依赖: Ico_sdiff_left, left_mem_Ico, sdiff_union_self, singleton_subset_iff, union_eq_self_of_subset_right
-/
theorem Ioo_union_left (hab : a < b) : Ioo a b union {a} = Ico a b := by
  rw [← Ico_sdiff_left]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Ico.2 hab)]

@[to_dual none]
/--
theorem `Ioo_union_both` / 定理 `Ioo_union_both`

English:
theorem Ioo_union_both
  given: (h : a <= b)
  statement: Ioo a b union {a, b} = Icc a b
  proof: by
  have : (Icc a b \ {a, b}) union {a, b} = Icc a b := sdiff_union_of_subset fun
    | x, .inl rfl => left_mem_Icc.mpr h
    | x, .inr rfl => right_mem_Icc.mpr h
  rw [← this]; rw [Icc_sdiff_both]

@[to_dual]

中文:
定理 Ioo_union_both
  条件: (h : a <= b)
  结论: Ioo a b union {a, b} = Icc a b
  证明: by
  have : (Icc a b \ {a, b}) union {a, b} = Icc a b := sdiff_union_of_subset fun
    | x, .inl rfl => left_mem_Icc.mpr h
    | x, .inr rfl => right_mem_Icc.mpr h
  rw [← this]; rw [Icc_sdiff_both]

@[to_dual]

Depends on / 依赖: Icc_sdiff_both, left_mem_Icc, left_mem_Icc.mpr, right_mem_Icc, right_mem_Icc.mpr, sdiff_union_of_subset
-/
theorem Ioo_union_both (h : a <= b) : Ioo a b union {a, b} = Icc a b := by
  have : (Icc a b \ {a, b}) union {a, b} = Icc a b := sdiff_union_of_subset fun
    | x, .inl rfl => left_mem_Icc.mpr h
    | x, .inr rfl => right_mem_Icc.mpr h
  rw [← this]; rw [Icc_sdiff_both]

@[to_dual]
/--
theorem `Ioc_union_left` / 定理 `Ioc_union_left`

English:
theorem Ioc_union_left
  given: (hab : a <= b)
  statement: Ioc a b union {a} = Icc a b
  proof: by
  rw [← Icc_sdiff_left]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Icc.2 hab)]

@[to_dual (attr := simp)]

中文:
定理 Ioc_union_left
  条件: (hab : a <= b)
  结论: Ioc a b union {a} = Icc a b
  证明: by
  rw [← Icc_sdiff_left]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Icc.2 hab)]

@[to_dual (attr := simp)]

Depends on / 依赖: Icc_sdiff_left, left_mem_Icc, sdiff_union_self, singleton_subset_iff, union_eq_self_of_subset_right
-/
theorem Ioc_union_left (hab : a <= b) : Ioc a b union {a} = Icc a b := by
  rw [← Icc_sdiff_left]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Icc.2 hab)]

@[to_dual (attr := simp)]
/--
theorem `Ico_insert_right` / 定理 `Ico_insert_right`

English:
theorem Ico_insert_right
  given: (h : a <= b)
  statement: insert b (Ico a b) = Icc a b
  proof: by
  rw [insert_eq]; rw [union_comm]; rw [Ico_union_right h]

@[to_dual (attr := simp)]

中文:
定理 Ico_insert_right
  条件: (h : a <= b)
  结论: insert b (Ico a b) = Icc a b
  证明: by
  rw [insert_eq]; rw [union_comm]; rw [Ico_union_right h]

@[to_dual (attr := simp)]

Depends on / 依赖: Ico_union_right, insert_eq, union_comm
-/
theorem Ico_insert_right (h : a <= b) : insert b (Ico a b) = Icc a b := by
  rw [insert_eq]; rw [union_comm]; rw [Ico_union_right h]

@[to_dual (attr := simp)]
/--
theorem `Ioo_insert_left` / 定理 `Ioo_insert_left`

English:
theorem Ioo_insert_left
  given: (h : a < b)
  statement: insert a (Ioo a b) = Ico a b
  proof: by
  rw [insert_eq]; rw [union_comm]; rw [Ioo_union_left h]

@[to_dual (attr := simp)]

中文:
定理 Ioo_insert_left
  条件: (h : a < b)
  结论: insert a (Ioo a b) = Ico a b
  证明: by
  rw [insert_eq]; rw [union_comm]; rw [Ioo_union_left h]

@[to_dual (attr := simp)]

Depends on / 依赖: Ioo_union_left, insert_eq, union_comm
-/
theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [insert_eq]; rw [union_comm]; rw [Ioo_union_left h]

@[to_dual (attr := simp)]
/--
theorem `Iio_insert` / 定理 `Iio_insert`

English:
theorem Iio_insert
  statement: insert a (Iio a) = Iic a
  proof: ext fun _ => le_iff_eq_or_lt.symm

@[to_dual]

中文:
定理 Iio_insert
  结论: insert a (Iio a) = Iic a
  证明: ext fun _ => le_iff_eq_or_lt.symm

@[to_dual]

Depends on / 依赖: le_iff_eq_or_lt, le_iff_eq_or_lt.symm
-/
theorem Iio_insert : insert a (Iio a) = Iic a :=
  ext fun _ => le_iff_eq_or_lt.symm

@[to_dual]
/--
theorem `mem_Iic_Iio_of_subset_of_subset` / 定理 `mem_Iic_Iio_of_subset_of_subset`

English:
theorem mem_Iic_Iio_of_subset_of_subset
  given: {s : Set α} (ho : Iio a subseteq s) (hc : s subseteq Iic a)
  proof: by_cases
    (fun h : a in s =>
Or.inl Subset.antisymm hc by rw [← Iio_union_right, union_subset_iff]; simp [*])
    fun h =>
Or.inr Subset.antisymm (fun _ hx => lt_of_le_of_ne (hc hx) fun heq => h <| heq.symm ▸ hx) ho

中文:
定理 mem_Iic_Iio_of_subset_of_subset
  条件: {s : Set α} (ho : Iio a subseteq s) (hc : s subseteq Iic a)
  证明: by_cases
    (fun h : a in s =>
Or.inl Subset.antisymm hc by rw [← Iio_union_right, union_subset_iff]; simp [*])
    fun h =>
Or.inr Subset.antisymm (fun _ hx => lt_of_le_of_ne (hc hx) fun heq => h <| heq.symm ▸ hx) ho

Depends on / 依赖: Iio_union_right, Or.inl, Or.inr, Subset, Subset.antisymm, antisymm, heq.symm, lt_of_le_of_ne, union_subset_iff
-/
theorem mem_Iic_Iio_of_subset_of_subset {s : Set α} (ho : Iio a subseteq s) (hc : s subseteq Iic a) :
    s in ({Iic a, Iio a} : Set (Set α)) :=
  by_cases
    (fun h : a in s =>
Or.inl Subset.antisymm hc by rw [← Iio_union_right, union_subset_iff]; simp [*])
    fun h =>
Or.inr Subset.antisymm (fun _ hx => lt_of_le_of_ne (hc hx) fun heq => h <| heq.symm ▸ hx) ho

/--
theorem `mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset` / 定理 `mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset`

English:
theorem mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
  given: {s : Set α} (ho : Ioo a b subseteq s) (hc : s subseteq Icc a b)
  proof: by
  by_cases ha : a in s <;> by_cases hb : b in s
  · refine Or.inl (Subset.antisymm hc ?_)
    rwa [← Ico_sdiff_left, sdiff_singleton_subset_iff, insert_eq_of_mem ha, ← Icc_sdiff_right,
      sdiff_singleton_subset_iff, insert_eq_of_mem hb] at ho
· refine Or.inr Or.inl Subset.antisymm ?_ ?_
    · 

中文:
定理 mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
  条件: {s : Set α} (ho : Ioo a b subseteq s) (hc : s subseteq Icc a b)
  证明: by
  by_cases ha : a in s <;> by_cases hb : b in s
  · refine Or.inl (Subset.antisymm hc ?_)
    rwa [← Ico_sdiff_left, sdiff_singleton_subset_iff, insert_eq_of_mem ha, ← Icc_sdiff_right,
      sdiff_singleton_subset_iff, insert_eq_of_mem hb] at ho
· refine Or.inr Or.inl Subset.antisymm ?_ ?_
    · 

Depends on / 依赖: Icc_sdiff_left, Icc_sdiff_right, Ico_sdiff_left, Or.inl, Or.inr, Subset, Subset.antisymm, antisymm, insert_eq_of_mem, sdiff_singleton_subset_iff, subset_sdiff_singleton
-/
theorem mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset {s : Set α} (ho : Ioo a b subseteq s) (hc : s subseteq Icc a b) :
    s in ({Icc a b, Ico a b, Ioc a b, Ioo a b} : Set (Set α)) := by
  by_cases ha : a in s <;> by_cases hb : b in s
  · refine Or.inl (Subset.antisymm hc ?_)
    rwa [← Ico_sdiff_left, sdiff_singleton_subset_iff, insert_eq_of_mem ha, ← Icc_sdiff_right,
      sdiff_singleton_subset_iff, insert_eq_of_mem hb] at ho
· refine Or.inr Or.inl Subset.antisymm ?_ ?_
    · rw [← Icc_sdiff_right]
      exact subset_sdiff_singleton hc hb
    · rwa [← Ico_sdiff_left, sdiff_singleton_subset_iff, insert_eq_of_mem ha] at ho
· refine Or.inr Or.inr Or.inl Subset.antisymm ?_ ?_
    · rw [← Icc_sdiff_left]
      exact subset_sdiff_singleton hc ha
    · rwa [← Ioc_sdiff_right, sdiff_singleton_subset_iff, insert_eq_of_mem hb] at ho
· refine Or.inr Or.inr Or.inr Subset.antisymm ?_ ho
    rw [← Ico_sdiff_left]; rw [← Icc_sdiff_right]
    apply_rules [subset_sdiff_singleton]

@[to_dual]
/--
theorem `eq_left_or_mem_Ioo_of_mem_Ico` / 定理 `eq_left_or_mem_Ioo_of_mem_Ico`

English:
theorem eq_left_or_mem_Ioo_of_mem_Ico
  given: {x : α} (hmem : x in Ico a b)
  statement: x = a ∨ x in Ioo a b
  proof: hmem.1.eq_or_lt'.imp_right fun h => ⟨h, hmem.2⟩

@[to_dual none]

中文:
定理 eq_left_or_mem_Ioo_of_mem_Ico
  条件: {x : α} (hmem : x in Ico a b)
  结论: x = a ∨ x in Ioo a b
  证明: hmem.1.eq_or_lt'.imp_right fun h => ⟨h, hmem.2⟩

@[to_dual none]

Depends on / 依赖: eq_or_lt, imp_right
-/
theorem eq_left_or_mem_Ioo_of_mem_Ico {x : α} (hmem : x in Ico a b) : x = a ∨ x in Ioo a b :=
  hmem.1.eq_or_lt'.imp_right fun h => ⟨h, hmem.2⟩

@[to_dual none]
/--
theorem `eq_endpoints_or_mem_Ioo_of_mem_Icc` / 定理 `eq_endpoints_or_mem_Ioo_of_mem_Icc`

English:
theorem eq_endpoints_or_mem_Ioo_of_mem_Icc
  given: {x : α} (hmem : x in Icc a b)
  proof: hmem.1.eq_or_lt'.imp_right fun h => eq_right_or_mem_Ioo_of_mem_Ioc ⟨h, hmem.2⟩

@[to_dual]

中文:
定理 eq_endpoints_or_mem_Ioo_of_mem_Icc
  条件: {x : α} (hmem : x in Icc a b)
  证明: hmem.1.eq_or_lt'.imp_right fun h => eq_right_or_mem_Ioo_of_mem_Ioc ⟨h, hmem.2⟩

@[to_dual]

Depends on / 依赖: eq_or_lt, eq_right_or_mem_Ioo_of_mem_Ioc, imp_right
-/
theorem eq_endpoints_or_mem_Ioo_of_mem_Icc {x : α} (hmem : x in Icc a b) :
    x = a ∨ x = b ∨ x in Ioo a b :=
  hmem.1.eq_or_lt'.imp_right fun h => eq_right_or_mem_Ioo_of_mem_Ioc ⟨h, hmem.2⟩

@[to_dual]
/--
theorem `_root_.IsMin.Iic_eq` / 定理 `_root_.IsMin.Iic_eq`

English:
theorem _root_.IsMin.Iic_eq
  given: (h : IsMin a)
  statement: Iic a = {a}
  proof: eq_singleton_iff_unique_mem.2 ⟨self_mem_Ici, fun _ => h.eq_of_le⟩

@[to_dual]

中文:
定理 _root_.IsMin.Iic_eq
  条件: (h : IsMin a)
  结论: Iic a = {a}
  证明: eq_singleton_iff_unique_mem.2 ⟨self_mem_Ici, fun _ => h.eq_of_le⟩

@[to_dual]

Depends on / 依赖: eq_of_le, eq_singleton_iff_unique_mem, h.eq_of_le, self_mem_Ici
-/
theorem _root_.IsMin.Iic_eq (h : IsMin a) : Iic a = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨self_mem_Ici, fun _ => h.eq_of_le⟩

@[to_dual]
/--
theorem `Iic_injective` / 定理 `Iic_injective`

English:
theorem Iic_injective
  statement: Injective (Iic : α -> Set α)
  proof: fun _ _ =>
  eq_of_forall_le_iff ∘ Set.ext_iff.1

@[to_dual]

中文:
定理 Iic_injective
  结论: Injective (Iic : α -> Set α)
  证明: fun _ _ =>
  eq_of_forall_le_iff ∘ Set.ext_iff.1

@[to_dual]
-/
theorem Iic_injective : Injective (Iic : α -> Set α) := fun _ _ =>
  eq_of_forall_le_iff ∘ Set.ext_iff.1

@[to_dual]
/--
theorem `Iic_inj` / 定理 `Iic_inj`

English:
theorem Iic_inj
  statement: Iic a = Iic b ↔ a = b
  proof: Iic_injective.eq_iff

@[simp, to_dual none]

中文:
定理 Iic_inj
  结论: Iic a = Iic b ↔ a = b
  证明: Iic_injective.eq_iff

@[simp, to_dual none]

Depends on / 依赖: Iic_injective, Iic_injective.eq_iff, eq_iff
-/
theorem Iic_inj : Iic a = Iic b ↔ a = b :=
  Iic_injective.eq_iff

@[simp, to_dual none]
/--
theorem `Icc_inter_Icc_eq_singleton` / 定理 `Icc_inter_Icc_eq_singleton`

English:
theorem Icc_inter_Icc_eq_singleton
  given: (hab : a <= b) (hbc : b <= c)
  statement: Icc a b inter Icc b c = {b}
  proof: by
  rw [← Ici_inter_Iic]; rw [← Iic_inter_Ici]; rw [inter_inter_inter_comm]; rw [Iic_inter_Ici]
  simp [hab, hbc]

@[to_dual none]

中文:
定理 Icc_inter_Icc_eq_singleton
  条件: (hab : a <= b) (hbc : b <= c)
  结论: Icc a b inter Icc b c = {b}
  证明: by
  rw [← Ici_inter_Iic]; rw [← Iic_inter_Ici]; rw [inter_inter_inter_comm]; rw [Iic_inter_Ici]
  simp [hab, hbc]

@[to_dual none]

Depends on / 依赖: Ici_inter_Iic, Iic_inter_Ici, inter_inter_inter_comm
-/
theorem Icc_inter_Icc_eq_singleton (hab : a <= b) (hbc : b <= c) : Icc a b inter Icc b c = {b} := by
  rw [← Ici_inter_Iic]; rw [← Iic_inter_Ici]; rw [inter_inter_inter_comm]; rw [Iic_inter_Ici]
  simp [hab, hbc]

@[to_dual none]
/--
lemma `Icc_eq_Icc_iff` / 引理 `Icc_eq_Icc_iff`

English:
lemma Icc_eq_Icc_iff
  given: {d : α} (h : a <= b)
  proof: by
  refine ⟨fun heq => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have h' : c <= d := by
    by_contra contra; rw [Icc_eq_empty_iff.mpr contra, Icc_eq_empty_iff] at heq; contradiction
  simp only [Set.ext_iff, mem_Icc] at heq
  obtain ⟨-, h₁⟩ := (heq b).mp ⟨h, le_refl _⟩
  obtain ⟨h₂, -⟩ := (heq a).mp ⟨le_re

中文:
引理 Icc_eq_Icc_iff
  条件: {d : α} (h : a <= b)
  证明: by
  refine ⟨fun heq => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have h' : c <= d := by
    by_contra contra; rw [Icc_eq_empty_iff.mpr contra, Icc_eq_empty_iff] at heq; contradiction
  simp only [Set.ext_iff, mem_Icc] at heq
  obtain ⟨-, h₁⟩ := (heq b).mp ⟨h, le_refl _⟩
  obtain ⟨h₂, -⟩ := (heq a).mp ⟨le_re

Depends on / 依赖: Icc_eq_empty_iff, Icc_eq_empty_iff.mpr, Set.ext_iff, contra, ext_iff, le_antisymm, le_refl, mem_Icc
-/
lemma Icc_eq_Icc_iff {d : α} (h : a <= b) :
    Icc a b = Icc c d ↔ a = c ∧ b = d := by
  refine ⟨fun heq => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have h' : c <= d := by
    by_contra contra; rw [Icc_eq_empty_iff.mpr contra, Icc_eq_empty_iff] at heq; contradiction
  simp only [Set.ext_iff, mem_Icc] at heq
  obtain ⟨-, h₁⟩ := (heq b).mp ⟨h, le_refl _⟩
  obtain ⟨h₂, -⟩ := (heq a).mp ⟨le_refl _, h⟩
  obtain ⟨h₃, -⟩ := (heq c).mpr ⟨le_refl _, h'⟩
  obtain ⟨-, h₄⟩ := (heq d).mpr ⟨h', le_refl _⟩
  exact ⟨le_antisymm h₃ h₂, le_antisymm h₁ h₄⟩

end PartialOrder

section OrderTop

@[to_dual (attr := simp)]
/--
theorem `Ici_top` / 定理 `Ici_top`

English:
theorem Ici_top
  given: [PartialOrder α] [OrderTop α]
  statement: Ici (⊤ : α) = {⊤}
  proof: isMax_top.Ici_eq

@[to_dual]

中文:
定理 Ici_top
  条件: [PartialOrder α] [OrderTop α]
  结论: Ici (⊤ : α) = {⊤}
  证明: isMax_top.Ici_eq

@[to_dual]

Depends on / 依赖: Ici_eq, isMax_top, isMax_top.Ici_eq
-/
theorem Ici_top [PartialOrder α] [OrderTop α] : Ici (⊤ : α) = {⊤} :=
  isMax_top.Ici_eq

@[to_dual]
/--
theorem `Iio_top` / 定理 `Iio_top`

English:
theorem Iio_top
  given: [PartialOrder α] [OrderTop α]
  statement: Iio (⊤ : α) = {⊤}ᶜ
  proof: ext fun _ => lt_top_iff_ne_top

中文:
定理 Iio_top
  条件: [PartialOrder α] [OrderTop α]
  结论: Iio (⊤ : α) = {⊤}ᶜ
  证明: ext fun _ => lt_top_iff_ne_top

Depends on / 依赖: lt_top_iff_ne_top
-/
theorem Iio_top [PartialOrder α] [OrderTop α] : Iio (⊤ : α) = {⊤}ᶜ :=
  ext fun _ => lt_top_iff_ne_top

variable [Preorder α] [OrderTop α] {a : α}

@[to_dual]
/--
theorem `Ioi_top` / 定理 `Ioi_top`

English:
theorem Ioi_top
  statement: Ioi (⊤ : α) = ∅
  proof: isMax_top.Ioi_eq

@[to_dual (attr := simp)]

中文:
定理 Ioi_top
  结论: Ioi (⊤ : α) = ∅
  证明: isMax_top.Ioi_eq

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_eq, isMax_top, isMax_top.Ioi_eq
-/
theorem Ioi_top : Ioi (⊤ : α) = ∅ :=
  isMax_top.Ioi_eq

@[to_dual (attr := simp)]
/--
theorem `Iic_top` / 定理 `Iic_top`

English:
theorem Iic_top
  statement: Iic (⊤ : α) = univ
  proof: isTop_top.Iic_eq

@[to_dual (attr := simp)]

中文:
定理 Iic_top
  结论: Iic (⊤ : α) = univ
  证明: isTop_top.Iic_eq

@[to_dual (attr := simp)]

Depends on / 依赖: Iic_eq, isTop_top, isTop_top.Iic_eq
-/
theorem Iic_top : Iic (⊤ : α) = univ :=
  isTop_top.Iic_eq

@[to_dual (attr := simp)]
/--
theorem `Icc_top` / 定理 `Icc_top`

English:
theorem Icc_top
  statement: Icc a ⊤ = Ici a
  proof: by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]

中文:
定理 Icc_top
  结论: Icc a ⊤ = Ici a
  证明: by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_inter_Iic
-/
theorem Icc_top : Icc a ⊤ = Ici a := by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]
/--
theorem `Ioc_top` / 定理 `Ioc_top`

English:
theorem Ioc_top
  statement: Ioc a ⊤ = Ioi a
  proof: by simp [← Ioi_inter_Iic]

中文:
定理 Ioc_top
  结论: Ioc a ⊤ = Ioi a
  证明: by simp [← Ioi_inter_Iic]

Depends on / 依赖: Ioi_inter_Iic
-/
theorem Ioc_top : Ioc a ⊤ = Ioi a := by simp [← Ioi_inter_Iic]

end OrderTop

/--
theorem `Icc_bot_top` / 定理 `Icc_bot_top`

English:
theorem Icc_bot_top
  given: [Preorder α] [BoundedOrder α]
  statement: Icc (⊥ : α) ⊤ = univ
  proof: by simp

中文:
定理 Icc_bot_top
  条件: [Preorder α] [BoundedOrder α]
  结论: Icc (⊥ : α) ⊤ = univ
  证明: by simp
-/
theorem Icc_bot_top [Preorder α] [BoundedOrder α] : Icc (⊥ : α) ⊤ = univ := by simp

section Lattice

section Inf

variable [SemilatticeInf α]

@[to_dual (attr := simp)]
/--
theorem `Iic_inter_Iic` / 定理 `Iic_inter_Iic`

English:
theorem Iic_inter_Iic
  given: {a b : α}
  statement: Iic a inter Iic b = Iic (a ⊓ b)
  proof: by
  ext x
  simp [Iic]

@[to_dual (reorder := a b) (attr := simp)]

中文:
定理 Iic_inter_Iic
  条件: {a b : α}
  结论: Iic a inter Iic b = Iic (a ⊓ b)
  证明: by
  ext x
  simp [Iic]

@[to_dual (reorder := a b) (attr := simp)]
-/
theorem Iic_inter_Iic {a b : α} : Iic a inter Iic b = Iic (a ⊓ b) := by
  ext x
  simp [Iic]

@[to_dual (reorder := a b) (attr := simp)]
/--
theorem `Ioc_inter_Iic` / 定理 `Ioc_inter_Iic`

English:
theorem Ioc_inter_Iic
  given: (a b c : α)
  statement: Ioc a b inter Iic c = Ioc a (b ⊓ c)
  proof: by
  rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]; rw [inter_assoc]; rw [Iic_inter_Iic]

中文:
定理 Ioc_inter_Iic
  条件: (a b c : α)
  结论: Ioc a b inter Iic c = Ioc a (b ⊓ c)
  证明: by
  rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]; rw [inter_assoc]; rw [Iic_inter_Iic]

Depends on / 依赖: Iic_inter_Iic, Ioi_inter_Iic, inter_assoc
-/
theorem Ioc_inter_Iic (a b c : α) : Ioc a b inter Iic c = Ioc a (b ⊓ c) := by
  rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]; rw [inter_assoc]; rw [Iic_inter_Iic]

end Inf

variable [Lattice α] {a b c a₁ a₂ b₁ b₂ : α}

@[to_dual self]
/--
theorem `Icc_inter_Icc` / 定理 `Icc_inter_Icc`

English:
theorem Icc_inter_Icc
  statement: Icc a₁ b₁ inter Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂)
  proof: by
  simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm]; ac_rfl

中文:
定理 Icc_inter_Icc
  结论: Icc a₁ b₁ inter Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂)
  证明: by
  simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm]; ac_rfl

Depends on / 依赖: Ici_inter_Ici, Ici_inter_Ici.symm, Ici_inter_Iic, Ici_inter_Iic.symm, Iic_inter_Iic, Iic_inter_Iic.symm
-/
theorem Icc_inter_Icc : Icc a₁ b₁ inter Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm]; ac_rfl

end Lattice

/-! ### Closed intervals in `α × β` -/

section Prod

variable {β : Type*} [Preorder α] [Preorder β]

@[to_dual (attr := simp)]
/--
theorem `Iic_prod_Iic` / 定理 `Iic_prod_Iic`

English:
theorem Iic_prod_Iic
  given: (a : α) (b : β)
  statement: Iic a ×ˢ Iic b = Iic (a, b)
  proof: rfl

@[to_dual]

中文:
定理 Iic_prod_Iic
  条件: (a : α) (b : β)
  结论: Iic a ×ˢ Iic b = Iic (a, b)
  证明: rfl

@[to_dual]
-/
theorem Iic_prod_Iic (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) :=
  rfl

@[to_dual]
/--
theorem `Iic_prod_eq` / 定理 `Iic_prod_eq`

English:
theorem Iic_prod_eq
  given: (a : α × β)
  statement: Iic a = Iic a.1 ×ˢ Iic a.2
  proof: rfl

@[simp, to_dual self]

中文:
定理 Iic_prod_eq
  条件: (a : α × β)
  结论: Iic a = Iic a.1 ×ˢ Iic a.2
  证明: rfl

@[simp, to_dual self]
-/
theorem Iic_prod_eq (a : α × β) : Iic a = Iic a.1 ×ˢ Iic a.2 :=
  rfl

@[simp, to_dual self]
/--
theorem `Icc_prod_Icc` / 定理 `Icc_prod_Icc`

English:
theorem Icc_prod_Icc
  given: (a₁ a₂ : α) (b₁ b₂ : β)
  statement: Icc a₁ a₂ ×ˢ Icc b₁ b₂ = Icc (a₁, b₁) (a₂, b₂)
  proof: by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

@[to_dual self]

中文:
定理 Icc_prod_Icc
  条件: (a₁ a₂ : α) (b₁ b₂ : β)
  结论: Icc a₁ a₂ ×ˢ Icc b₁ b₂ = Icc (a₁, b₁) (a₂, b₂)
  证明: by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

@[to_dual self]

Depends on / 依赖: and_assoc, and_left_comm
-/
theorem Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : Icc a₁ a₂ ×ˢ Icc b₁ b₂ = Icc (a₁, b₁) (a₂, b₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

@[to_dual self]
/--
theorem `Icc_prod_eq` / 定理 `Icc_prod_eq`

English:
theorem Icc_prod_eq
  given: (a b : α × β)
  statement: Icc a b = Icc a.1 b.1 ×ˢ Icc a.2 b.2
  proof: by simp

中文:
定理 Icc_prod_eq
  条件: (a b : α × β)
  结论: Icc a b = Icc a.1 b.1 ×ˢ Icc a.2 b.2
  证明: by simp
-/
theorem Icc_prod_eq (a b : α × β) : Icc a b = Icc a.1 b.1 ×ˢ Icc a.2 b.2 := by simp

end Prod

/-! ### Lemmas about intervals in dense orders -/

section Dense

variable (α) [Preorder α] [DenselyOrdered α] {x y : α}

@[to_dual] -- TODO: `to_dual` only works with the `mem_Ioo.mpr` in the proof.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoMinOrder (Ioo x y)
  body: ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioo.mpr ⟨hb₁, hb₂.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual] -- TODO: `to_dual` only works with the `mem_Ioc.mpr` in the proof.

中文:
实例 :
  签名: NoMinOrder (Ioo x y)
  定义体: ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioo.mpr ⟨hb₁, hb₂.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual] -- TODO: `to_dual` only works with the `mem_Ioc.mpr` in the proof.

Depends on / 依赖: exists_between, mem_Ioo, mem_Ioo.mpr
-/
instance : NoMinOrder (Ioo x y) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioo.mpr ⟨hb₁, hb₂.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual] -- TODO: `to_dual` only works with the `mem_Ioc.mpr` in the proof.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoMinOrder (Ioc x y)
  body: ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioc.mpr ⟨hb₁, hb₂.le.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual]

中文:
实例 :
  签名: NoMinOrder (Ioc x y)
  定义体: ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioc.mpr ⟨hb₁, hb₂.le.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual]

Depends on / 依赖: exists_between, le.trans, mem_Ioc, mem_Ioc.mpr
-/
instance : NoMinOrder (Ioc x y) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioc.mpr ⟨hb₁, hb₂.le.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoMinOrder (Ioi x)
  body: ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁⟩, hb₂⟩⟩

中文:
实例 :
  签名: NoMinOrder (Ioi x)
  定义体: ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁⟩, hb₂⟩⟩

Depends on / 依赖: exists_between
-/
instance : NoMinOrder (Ioi x) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁⟩, hb₂⟩⟩

end Dense


/--
lemma `Iic_False` / 引理 `Iic_False`

English:
lemma Iic_False
  statement: Iic False = {False}
  proof: by aesop

中文:
引理 Iic_False
  结论: Iic False = {False}
  证明: by aesop
-/
@[simp] lemma Iic_False : Iic False = {False} := by aesop
/--
lemma `Iic_True` / 引理 `Iic_True`

English:
lemma Iic_True
  statement: Iic True = univ
  proof: by aesop

中文:
引理 Iic_True
  结论: Iic True = univ
  证明: by aesop
-/
@[simp] lemma Iic_True : Iic True = univ := by aesop
/--
lemma `Ici_False` / 引理 `Ici_False`

English:
lemma Ici_False
  statement: Ici False = univ
  proof: by aesop

中文:
引理 Ici_False
  结论: Ici False = univ
  证明: by aesop
-/
@[simp] lemma Ici_False : Ici False = univ := by aesop
/--
lemma `Ici_True` / 引理 `Ici_True`

English:
lemma Ici_True
  statement: Ici True = {True}
  proof: by aesop

中文:
引理 Ici_True
  结论: Ici True = {True}
  证明: by aesop
-/
@[simp] lemma Ici_True : Ici True = {True} := by aesop
/--
lemma `Iio_False` / 引理 `Iio_False`

English:
lemma Iio_False
  statement: Iio False = ∅
  proof: by aesop

中文:
引理 Iio_False
  结论: Iio False = ∅
  证明: by aesop

Depends on / 依赖: I_le_J, Ideal.span_mono, Iio_True, Ioi_False, Set.image_mono, image_mono, lt_iff_le_not_ge, span_mono
-/
lemma Iio_False : Iio False = ∅ := by aesop
/--
lemma `Iio_True` / 引理 `Iio_True`

English:
lemma Iio_True
  statement: Iio True = {False}
  proof: by aesop (add simp [Ioi, lt_iff_le_not_ge])

中文:
引理 Iio_True
  结论: Iio True = {False}
  证明: by aesop (add simp [Ioi, lt_iff_le_not_ge])

Depends on / 依赖: Ideal.span_le, image_preimage_subset, span_le
-/
@[simp] lemma Iio_True : Iio True = {False} := by aesop (add simp [Ioi, lt_iff_le_not_ge])
/--
lemma `Ioi_False` / 引理 `Ioi_False`

English:
lemma Ioi_False
  statement: Ioi False = {True}
  proof: by aesop (add simp [Ioi, lt_iff_le_not_ge])

中文:
引理 Ioi_False
  结论: Ioi False = {True}
  证明: by aesop (add simp [Ioi, lt_iff_le_not_ge])
-/
@[simp] lemma Ioi_False : Ioi False = {True} := by aesop (add simp [Ioi, lt_iff_le_not_ge])
/--
lemma `Ioi_True` / 引理 `Ioi_True`

English:
lemma Ioi_True
  statement: Ioi True = ∅
  proof: by aesop

中文:
引理 Ioi_True
  结论: Ioi True = ∅
  证明: by aesop
-/
lemma Ioi_True : Ioi True = ∅ := by aesop

end Set
