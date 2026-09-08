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

/-
**isLocallyClosed_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyClosed_Icc [Preorder X] [OrderClosedTopology X] : IsLocallyClosed
 (Set.Icc a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
-/
theorem isLocallyClosed_Icc [Preorder X] [OrderClosedTopology X] :
    IsLocallyClosed (Set.Icc a b) :=
  isClosed_Icc.isLocallyClosed
/-
**isLocallyClosed_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyClosed_Ioo [LinearOrder X] [OrderClosedTopology X] : IsLocallyClo
sed (Set.Ioo a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
-/
theorem isLocallyClosed_Ioo [LinearOrder X] [OrderClosedTopology X] :
    IsLocallyClosed (Set.Ioo a b) :=
  isOpen_Ioo.isLocallyClosed
/-
**isLocallyClosed_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyClosed_Ici [Preorder X] [ClosedIciTopology X] : IsLocallyClosed (
Set.Ici a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
-/
theorem isLocallyClosed_Ici [Preorder X] [ClosedIciTopology X] :
    IsLocallyClosed (Set.Ici a) :=
  isClosed_Ici.isLocallyClosed
/-
**isLocallyClosed_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyClosed_Iic [Preorder X] [ClosedIicTopology X] : IsLocallyClosed (
Set.Iic a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
-/
theorem isLocallyClosed_Iic [Preorder X] [ClosedIicTopology X] :
    IsLocallyClosed (Set.Iic a) :=
  isClosed_Iic.isLocallyClosed
/-
**isLocallyClosed_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyClosed_Ioi [LinearOrder X] [ClosedIicTopology X] : IsLocallyClose
d (Set.Ioi a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
-/
theorem isLocallyClosed_Ioi [LinearOrder X] [ClosedIicTopology X] :
    IsLocallyClosed (Set.Ioi a) :=
  isOpen_Ioi.isLocallyClosed
/-
**isLocallyClosed_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyClosed_Iio [LinearOrder X] [ClosedIciTopology X] : IsLocallyClose
d (Set.Iio a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
-/
theorem isLocallyClosed_Iio [LinearOrder X] [ClosedIciTopology X] :
    IsLocallyClosed (Set.Iio a) :=
  isOpen_Iio.isLocallyClosed
/-
**isLocallyClosed_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyClosed_Ioc [LinearOrder X] [ClosedIicTopology X] : IsLocallyClose
d (Set.Ioc a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iic_inter_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ic a ∩ Set.Ioi b = Set.Ioc b a
· 使用引理 `IsLocallyClosed.inter`：IsLocallyClosed.inter (hs : IsLocallyClosed s) (h
t : IsLocallyClosed t) : IsLocallyClosed (s inter t)
· 使用定理 `isLocallyClosed_Iic`：isLocallyClosed_Iic [Preorder X] [ClosedIicTopology
 X] : IsLocallyClosed (Set.Iic a)
· 使用定理 `isLocallyClosed_Ioi`：isLocallyClosed_Ioi [LinearOrder X] [ClosedIicTopol
ogy X] : IsLocallyClosed (Set.Ioi a)
-/
theorem isLocallyClosed_Ioc [LinearOrder X] [ClosedIicTopology X] :
    IsLocallyClosed (Set.Ioc a b) := by
  rw [← Set.Iic_inter_Ioi]
  exact isLocallyClosed_Iic.inter isLocallyClosed_Ioi
/-
**isLocallyClosed_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyClosed_Ico [LinearOrder X] [ClosedIciTopology X] : IsLocallyClose
d (Set.Ico a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_inter_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
io a ∩ Set.Ici b = Set.Ico b a
· 使用引理 `IsLocallyClosed.inter`：IsLocallyClosed.inter (hs : IsLocallyClosed s) (h
t : IsLocallyClosed t) : IsLocallyClosed (s inter t)
· 使用定理 `isLocallyClosed_Iio`：isLocallyClosed_Iio [LinearOrder X] [ClosedIciTopol
ogy X] : IsLocallyClosed (Set.Iio a)
· 使用定理 `isLocallyClosed_Ici`：isLocallyClosed_Ici [Preorder X] [ClosedIciTopology
 X] : IsLocallyClosed (Set.Ici a)
-/
theorem isLocallyClosed_Ico [LinearOrder X] [ClosedIciTopology X] :
    IsLocallyClosed (Set.Ico a b) := by
  rw [← Set.Iio_inter_Ici]
  exact isLocallyClosed_Iio.inter isLocallyClosed_Ici
