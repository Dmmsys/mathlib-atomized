/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Ideal
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
The matrix ring over a simple ring is simple
-/

public section

namespace IsSimpleRing

variable (ι A : Type*) [Ring A] [Fintype ι] [Nonempty ι]

/-
**IsSimpleRing.matrix** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleRing`。
形式化陈述：matrix [IsSimpleRing A] : IsSimpleRing (Matrix ι ι A) where .symm.isSimple
Order simple
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isSimpleOrder`：isSimpleOrder [BoundedOrder α] [BoundedOrder β] 
[h : IsSimpleOrder β] (f : α ≃o β) : IsSimpleOrder α
· 使用定理 `IsSimpleRing.simple`：∀ {R : Type u_1} {inst : NonUnitalNonAssocRing R} [
self : IsSimpleRing R], IsSimpleOrder (TwoSidedIdeal R)
-/
instance matrix [IsSimpleRing A] : IsSimpleRing (Matrix ι ι A) where
  simple := letI := Classical.decEq ι; TwoSidedIdeal.orderIsoMatrix |>.symm.isSimpleOrder

end IsSimpleRing

