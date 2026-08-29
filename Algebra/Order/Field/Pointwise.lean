/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Interval.Set.OrderIso

/-!
# Pointwise operations on ordered algebraic objects

This file contains lemmas about the effect of pointwise operations on sets with an order structure.
-/

public section

open Function Set
open scoped Pointwise

namespace LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b r : K} (hr : 0 < r)
include hr

/--
theorem `smul_Ioo` / 定理 `smul_Ioo`

English:
theorem smul_Ioo
  statement: r • Ioo a b = Ioo (r * a) (r * b)
  proof: (OrderIso.mulLeft₀ r hr).image_Ioo a b

中文:
定理 smul_Ioo
  结论: r • 开区间 a b = 开区间 (r * a) (r * b)
  证明: (OrderIso.mulLeft₀ r hr).image_Ioo a b

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ioo
-/
theorem smul_Ioo : r • Ioo a b = Ioo (r * a) (r * b) := (OrderIso.mulLeft₀ r hr).image_Ioo a b
/--
theorem `smul_Icc` / 定理 `smul_Icc`

English:
theorem smul_Icc
  statement: r • Icc a b = Icc (r * a) (r * b)
  proof: (OrderIso.mulLeft₀ r hr).image_Icc a b

中文:
定理 smul_Icc
  结论: r • 闭区间 a b = 闭区间 (r * a) (r * b)
  证明: (OrderIso.mulLeft₀ r hr).image_Icc a b

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Icc
-/
theorem smul_Icc : r • Icc a b = Icc (r * a) (r * b) := (OrderIso.mulLeft₀ r hr).image_Icc a b
/--
theorem `smul_Ico` / 定理 `smul_Ico`

English:
theorem smul_Ico
  statement: r • Ico a b = Ico (r * a) (r * b)
  proof: (OrderIso.mulLeft₀ r hr).image_Ico a b

中文:
定理 smul_Ico
  结论: r • 左闭右开区间 a b = 左闭右开区间 (r * a) (r * b)
  证明: (OrderIso.mulLeft₀ r hr).image_Ico a b

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ico
-/
theorem smul_Ico : r • Ico a b = Ico (r * a) (r * b) := (OrderIso.mulLeft₀ r hr).image_Ico a b
/--
theorem `smul_Ioc` / 定理 `smul_Ioc`

English:
theorem smul_Ioc
  statement: r • Ioc a b = Ioc (r * a) (r * b)
  proof: (OrderIso.mulLeft₀ r hr).image_Ioc a b

中文:
定理 smul_Ioc
  结论: r • 左开右闭区间 a b = 左开右闭区间 (r * a) (r * b)
  证明: (OrderIso.mulLeft₀ r hr).image_Ioc a b

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ioc
-/
theorem smul_Ioc : r • Ioc a b = Ioc (r * a) (r * b) := (OrderIso.mulLeft₀ r hr).image_Ioc a b
/--
theorem `smul_Ioi` / 定理 `smul_Ioi`

English:
theorem smul_Ioi
  statement: r • Ioi a = Ioi (r * a)
  proof: (OrderIso.mulLeft₀ r hr).image_Ioi a

中文:
定理 smul_Ioi
  结论: r • 左开右无界区间 a = 左开右无界区间 (r * a)
  证明: (OrderIso.mulLeft₀ r hr).image_Ioi a

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ioi
-/
theorem smul_Ioi : r • Ioi a = Ioi (r * a) := (OrderIso.mulLeft₀ r hr).image_Ioi a
/--
theorem `smul_Iio` / 定理 `smul_Iio`

English:
theorem smul_Iio
  statement: r • Iio a = Iio (r * a)
  proof: (OrderIso.mulLeft₀ r hr).image_Iio a

中文:
定理 smul_Iio
  结论: r • 左无界右开区间 a = 左无界右开区间 (r * a)
  证明: (OrderIso.mulLeft₀ r hr).image_Iio a

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Iio
-/
theorem smul_Iio : r • Iio a = Iio (r * a) := (OrderIso.mulLeft₀ r hr).image_Iio a
/--
theorem `smul_Ici` / 定理 `smul_Ici`

English:
theorem smul_Ici
  statement: r • Ici a = Ici (r * a)
  proof: (OrderIso.mulLeft₀ r hr).image_Ici a

中文:
定理 smul_Ici
  结论: r • 左闭右无界区间 a = 左闭右无界区间 (r * a)
  证明: (OrderIso.mulLeft₀ r hr).image_Ici a

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ici
-/
theorem smul_Ici : r • Ici a = Ici (r * a) := (OrderIso.mulLeft₀ r hr).image_Ici a
/--
theorem `smul_Iic` / 定理 `smul_Iic`

English:
theorem smul_Iic
  statement: r • Iic a = Iic (r * a)
  proof: (OrderIso.mulLeft₀ r hr).image_Iic a

中文:
定理 smul_Iic
  结论: r • 左无界右闭区间 a = 左无界右闭区间 (r * a)
  证明: (OrderIso.mulLeft₀ r hr).image_Iic a

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Iic
-/
theorem smul_Iic : r • Iic a = Iic (r * a) := (OrderIso.mulLeft₀ r hr).image_Iic a

end LinearOrderedField
