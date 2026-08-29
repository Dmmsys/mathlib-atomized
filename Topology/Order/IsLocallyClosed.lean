/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.LocallyClosed

/-!
# Intervals are locally closed

We prove that the intervals on a topological ordered space are locally closed.
-/

public section

variable {X : Type*} [TopologicalSpace X] {a b : X}

/--
theorem `isLocallyClosed_Icc` / 定理 `isLocallyClosed_Icc`

English:
theorem isLocallyClosed_Icc
  given: [Preorder X] [OrderClosedTopology X]
  proof: isClosed_Icc.isLocallyClosed

中文:
定理 isLocallyClosed_Icc
  条件: [预序 X] [OrderClosed拓扑 X]
  证明: isClosed_Icc.isLocallyClosed

Depends on / 依赖: isClosed_Icc, isClosed_Icc.isLocallyClosed, isLocallyClosed
-/
theorem isLocallyClosed_Icc [Preorder X] [OrderClosedTopology X] :
    IsLocallyClosed (Set.Icc a b) :=
  isClosed_Icc.isLocallyClosed

/--
theorem `isLocallyClosed_Ioo` / 定理 `isLocallyClosed_Ioo`

English:
theorem isLocallyClosed_Ioo
  given: [LinearOrder X] [OrderClosedTopology X]
  proof: isOpen_Ioo.isLocallyClosed

中文:
定理 isLocallyClosed_Ioo
  条件: [线性序 X] [OrderClosed拓扑 X]
  证明: isOpen_Ioo.isLocallyClosed

Depends on / 依赖: isLocallyClosed, isOpen_Ioo, isOpen_Ioo.isLocallyClosed
-/
theorem isLocallyClosed_Ioo [LinearOrder X] [OrderClosedTopology X] :
    IsLocallyClosed (Set.Ioo a b) :=
  isOpen_Ioo.isLocallyClosed

/--
theorem `isLocallyClosed_Ici` / 定理 `isLocallyClosed_Ici`

English:
theorem isLocallyClosed_Ici
  given: [Preorder X] [ClosedIciTopology X]
  proof: isClosed_Ici.isLocallyClosed

中文:
定理 isLocallyClosed_Ici
  条件: [预序 X] [ClosedIci拓扑 X]
  证明: isClosed_Ici.isLocallyClosed

Depends on / 依赖: isClosed_Ici, isClosed_Ici.isLocallyClosed, isLocallyClosed
-/
theorem isLocallyClosed_Ici [Preorder X] [ClosedIciTopology X] :
    IsLocallyClosed (Set.Ici a) :=
  isClosed_Ici.isLocallyClosed

/--
theorem `isLocallyClosed_Iic` / 定理 `isLocallyClosed_Iic`

English:
theorem isLocallyClosed_Iic
  given: [Preorder X] [ClosedIicTopology X]
  proof: isClosed_Iic.isLocallyClosed

中文:
定理 isLocallyClosed_Iic
  条件: [预序 X] [ClosedIic拓扑 X]
  证明: isClosed_Iic.isLocallyClosed

Depends on / 依赖: isClosed_Iic, isClosed_Iic.isLocallyClosed, isLocallyClosed
-/
theorem isLocallyClosed_Iic [Preorder X] [ClosedIicTopology X] :
    IsLocallyClosed (Set.Iic a) :=
  isClosed_Iic.isLocallyClosed

/--
theorem `isLocallyClosed_Ioi` / 定理 `isLocallyClosed_Ioi`

English:
theorem isLocallyClosed_Ioi
  given: [LinearOrder X] [ClosedIicTopology X]
  proof: isOpen_Ioi.isLocallyClosed

中文:
定理 isLocallyClosed_Ioi
  条件: [线性序 X] [ClosedIic拓扑 X]
  证明: isOpen_Ioi.isLocallyClosed

Depends on / 依赖: isLocallyClosed, isOpen_Ioi, isOpen_Ioi.isLocallyClosed
-/
theorem isLocallyClosed_Ioi [LinearOrder X] [ClosedIicTopology X] :
    IsLocallyClosed (Set.Ioi a) :=
  isOpen_Ioi.isLocallyClosed

/--
theorem `isLocallyClosed_Iio` / 定理 `isLocallyClosed_Iio`

English:
theorem isLocallyClosed_Iio
  given: [LinearOrder X] [ClosedIciTopology X]
  proof: isOpen_Iio.isLocallyClosed

中文:
定理 isLocallyClosed_Iio
  条件: [线性序 X] [ClosedIci拓扑 X]
  证明: isOpen_Iio.isLocallyClosed

Depends on / 依赖: isLocallyClosed, isOpen_Iio, isOpen_Iio.isLocallyClosed
-/
theorem isLocallyClosed_Iio [LinearOrder X] [ClosedIciTopology X] :
    IsLocallyClosed (Set.Iio a) :=
  isOpen_Iio.isLocallyClosed

/--
theorem `isLocallyClosed_Ioc` / 定理 `isLocallyClosed_Ioc`

English:
theorem isLocallyClosed_Ioc
  given: [LinearOrder X] [ClosedIicTopology X]
  proof: by
  rw [← Set.Iic_inter_Ioi]
  exact isLocallyClosed_Iic.inter isLocallyClosed_Ioi

中文:
定理 isLocallyClosed_Ioc
  条件: [线性序 X] [ClosedIic拓扑 X]
  证明: by
  rw [← Set.Iic_inter_Ioi]
  exact isLocallyClosed_Iic.inter isLocallyClosed_Ioi

Depends on / 依赖: Iic_inter_Ioi, Set.Iic_inter_Ioi, isLocallyClosed_Iic, isLocallyClosed_Iic.inter, isLocallyClosed_Ioi
-/
theorem isLocallyClosed_Ioc [LinearOrder X] [ClosedIicTopology X] :
    IsLocallyClosed (Set.Ioc a b) := by
  rw [← Set.Iic_inter_Ioi]
  exact isLocallyClosed_Iic.inter isLocallyClosed_Ioi

/--
theorem `isLocallyClosed_Ico` / 定理 `isLocallyClosed_Ico`

English:
theorem isLocallyClosed_Ico
  given: [LinearOrder X] [ClosedIciTopology X]
  proof: by
  rw [← Set.Iio_inter_Ici]
  exact isLocallyClosed_Iio.inter isLocallyClosed_Ici

中文:
定理 isLocallyClosed_Ico
  条件: [线性序 X] [ClosedIci拓扑 X]
  证明: by
  rw [← Set.Iio_inter_Ici]
  exact isLocallyClosed_Iio.inter isLocallyClosed_Ici

Depends on / 依赖: Iio_inter_Ici, Set.Iio_inter_Ici, isLocallyClosed_Ici, isLocallyClosed_Iio, isLocallyClosed_Iio.inter
-/
theorem isLocallyClosed_Ico [LinearOrder X] [ClosedIciTopology X] :
    IsLocallyClosed (Set.Ico a b) := by
  rw [← Set.Iio_inter_Ici]
  exact isLocallyClosed_Iio.inter isLocallyClosed_Ici
