/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Divisible
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.GroupTheory.QuotientGroup.ModEq

/-!
# The additive circle

We define the additive circle `AddCircle p` as the quotient `𝕜 ⧸ ℤ ∙ p` for some period `p : 𝕜`.

See also `Circle` and `Real.Angle`.  For the normed group structure on `AddCircle`, see
`AddCircle.NormedAddCommGroup` in a later file.

## Main definitions and results:

* `AddCircle`: the additive circle `𝕜 ⧸ ℤ ∙ p` for some period `p : 𝕜`
* `UnitAddCircle`: the special case `ℝ ⧸ ℤ`
* `AddCircle.equivAddCircle`: the rescaling equivalence `AddCircle p ≃+ AddCircle q`
* `AddCircle.equivIco` and `AddCircle.equivIoc`: the natural equivalences
  `AddCircle p ≃ Ico a (a + p)` and `AddCircle p ≃ Ioc a (a + p)`
* `AddCircle.addOrderOf_div_of_gcd_eq_one`: rational points have finite order
* `AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder`: finite-order points are rational
* `AddCircle.homeoIccQuot`: the natural topological equivalence between `AddCircle p` and
  `Icc a (a + p)` with its endpoints identified.
* `AddCircle.liftIco_continuous` and `AddCircle.liftIoc_continuous`: if `f : ℝ → B` is continuous,
  and `f a = f (a + p)` for some `a`, then there is a continuous function `AddCircle p → B`
  which agrees with `f` on `Icc a (a + p)`.

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `AddCircle (1 : ℚ)`, and so we set things up more generally.

## TODO

* Link with periodicity
* Lie group structure
* Exponential equivalence to `Circle`

-/

@[expose] public section


noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace

open Topology

variable {𝕜 B : Type*}

section Continuity

variable [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [Archimedean 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {p : 𝕜} (hp : 0 < p) (a x : 𝕜)

/-- `toIcoDiv` is eventually constant on the right at every point. -/
/-
**eventuallyEq_toIcoDiv_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_toIcoDiv_nhdsGE : toIcoDiv hp a =ᶠ[𝓝[>=] x] fun _ => toIcoDiv
 hp a x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ico_mem_nhdsGE_of_mem`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : LinearOrder α] [ClosedIciTopology α] {a b c : α},   b ∈ Set.Ico c a → Set.Ic
o c a ∈ nhd…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sub_mem_Ico_iff_left`：sub_mem_Ico_iff_left : a - b in Set.Ico c d ↔ 
a in Set.Ico (c + b) (d + b)
· 使用定理 `toIcoDiv_eq_iff`：toIcoDiv_eq_iff : toIcoDiv hp a b = n ↔ b - n • p in Se
t.Ico a (a + p)

--- 原说明 ---
`toIcoDiv` is eventually constant on the right at every point.
-/
theorem eventuallyEq_toIcoDiv_nhdsGE : toIcoDiv hp a =ᶠ[𝓝[≥] x] fun _ ↦ toIcoDiv hp a x := by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsGE_of_mem
  rw [← sub_mem_Ico_iff_left, ← toIcoDiv_eq_iff]

/-- `toIcoDiv` is continuous on the right at every point.

In fact, a stronger statement is true:
it's eventually constant on the right, see `eventuallyEq_toIcoDiv_nhdsGE`. -/
/-
**continuousWithinAt_toIcoDiv_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_toIcoDiv_Ici : ContinuousWithinAt (toIcoDiv hp a) (Ici 
x) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `eventuallyEq_toIcoDiv_nhdsGE`：eventuallyEq_toIcoDiv_nhdsGE : toIcoDiv hp
 a =ᶠ[𝓝[>=] x] fun _ => toIcoDiv hp a x
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)

--- 原说明 ---
`toIcoDiv` is continuous on the right at every point.

In fact, a stronger statement is true:
it's eventually constant on the right, see `eventuallyEq_toIcoDiv_nhdsGE`.
-/
theorem continuousWithinAt_toIcoDiv_Ici : ContinuousWithinAt (toIcoDiv hp a) (Ici x) x :=
  Filter.tendsto_pure.mpr (eventuallyEq_toIcoDiv_nhdsGE hp a x) |>.mono_right <| pure_le_nhds _

/-- `toIocDiv` is eventually constant on the left at every point. -/
/-
**eventuallyEq_toIocDiv_nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_toIocDiv_nhdsLE : toIocDiv hp a =ᶠ[𝓝[<=] x] fun _ => toIocDiv
 hp a x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ioc_mem_nhdsLE_of_mem`：Ioc_mem_nhdsLE_of_mem (H : b in Ioc a c) : Ioc a 
c in 𝓝[<=] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sub_mem_Ioc_iff_left`：sub_mem_Ioc_iff_left : a - b in Set.Ioc c d ↔ 
a in Set.Ioc (c + b) (d + b)
· 使用定理 `toIocDiv_eq_iff`：toIocDiv_eq_iff : toIocDiv hp a b = n ↔ b - n • p in Se
t.Ioc a (a + p)

--- 原说明 ---
`toIocDiv` is eventually constant on the left at every point.
-/
theorem eventuallyEq_toIocDiv_nhdsLE : toIocDiv hp a =ᶠ[𝓝[≤] x] fun _ ↦ toIocDiv hp a x := by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsLE_of_mem
  rw [← sub_mem_Ioc_iff_left, ← toIocDiv_eq_iff]

/-- `toIocDiv` is continuous on the left at every point.

In fact, a stronger statement is true:
it's eventually constant on the left, see `eventuallyEq_toIocDiv_nhdsLE`. -/
/-
**continuousWithinAt_toIocDiv_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_toIocDiv_Iic : ContinuousWithinAt (toIocDiv hp a) (Iic 
x) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `eventuallyEq_toIocDiv_nhdsLE`：eventuallyEq_toIocDiv_nhdsLE : toIocDiv hp
 a =ᶠ[𝓝[<=] x] fun _ => toIocDiv hp a x
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)

--- 原说明 ---
`toIocDiv` is continuous on the left at every point.

In fact, a stronger statement is true:
it's eventually constant on the left, see `eventuallyEq_toIocDiv_nhdsLE`.
-/
theorem continuousWithinAt_toIocDiv_Iic : ContinuousWithinAt (toIocDiv hp a) (Iic x) x :=
  Filter.tendsto_pure.mpr (eventuallyEq_toIocDiv_nhdsLE hp a x) |>.mono_right <| pure_le_nhds _

/-- `toIcoMod` is continuous on the right at every point. -/
/-
**continuousWithinAt_toIcoMod_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_toIcoMod_Ici : ContinuousWithinAt (toIcoMod hp a) (Ici 
x) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {
f g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `continuousWithinAt_id`：continuousWithinAt_id {s : Set α} {x : α} : Conti
nuousWithinAt id s x
· 使用定理 `ContinuousWithinAt.smul`：ContinuousWithinAt.smul (hf : ContinuousWithinA
t f s b) (hg : ContinuousWithinAt g s b) : ContinuousWithinAt (f • g) s b
· 使用定理 `continuousWithinAt_toIcoDiv_Ici`：continuousWithinAt_toIcoDiv_Ici : Conti
nuousWithinAt (toIcoDiv hp a) (Ici x) x
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x

--- 原说明 ---
`toIcoMod` is continuous on the right at every point.
-/
theorem continuousWithinAt_toIcoMod_Ici : ContinuousWithinAt (toIcoMod hp a) (Ici x) x :=
  continuousWithinAt_id.sub <|
    (continuousWithinAt_toIcoDiv_Ici hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_right_toIcoMod := continuousWithinAt_toIcoMod_Ici

/-- `toIocMod` is continuous on the right at every point. -/
/-
**continuousWithinAt_toIocMod_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_toIocMod_Iic : ContinuousWithinAt (toIocMod hp a) (Iic 
x) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {
f g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `continuousWithinAt_id`：continuousWithinAt_id {s : Set α} {x : α} : Conti
nuousWithinAt id s x
· 使用定理 `ContinuousWithinAt.smul`：ContinuousWithinAt.smul (hf : ContinuousWithinA
t f s b) (hg : ContinuousWithinAt g s b) : ContinuousWithinAt (f • g) s b
· 使用定理 `continuousWithinAt_toIocDiv_Iic`：continuousWithinAt_toIocDiv_Iic : Conti
nuousWithinAt (toIocDiv hp a) (Iic x) x
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x

--- 原说明 ---
`toIocMod` is continuous on the right at every point.
-/
theorem continuousWithinAt_toIocMod_Iic : ContinuousWithinAt (toIocMod hp a) (Iic x) x :=
  continuousWithinAt_id.sub <|
    (continuousWithinAt_toIocDiv_Iic hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_left_toIocMod := continuousWithinAt_toIocMod_Iic

/-- At every point `x`, for all `y < x` sufficiently close to `x`,
we have `toIcoDiv hp a y = toIocDiv hp a x`.

Note that we use different functions on the LHS and on the RHS.
-/
/-
**eventuallyEq_toIcoDiv_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_toIcoDiv_nhdsLT : toIcoDiv hp a =ᶠ[𝓝[<] x] fun _ => toIocDiv 
hp a x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ico_mem_nhdsLT_of_mem`：Ico_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ico a 
c in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sub_mem_Ioc_iff_left`：sub_mem_Ioc_iff_left : a - b in Set.Ioc c d ↔ 
a in Set.Ioc (c + b) (d + b)
· 使用定理 `toIocDiv_eq_iff`：toIocDiv_eq_iff : toIocDiv hp a b = n ↔ b - n • p in Se
t.Ioc a (a + p)

--- 原说明 ---
At every point `x`, for all `y < x` sufficiently close to `x`,
we have `toIcoDiv hp a y = toIocDiv hp a x`.

Note that we use different functions on the LHS and on the RHS.
-/
theorem eventuallyEq_toIcoDiv_nhdsLT : toIcoDiv hp a =ᶠ[𝓝[<] x] fun _ ↦ toIocDiv hp a x := by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsLT_of_mem
  rw [← sub_mem_Ioc_iff_left, ← toIocDiv_eq_iff]

/-- At every point `x`, for all `y > x` sufficiently close to `x`,
we have `toIocDiv hp a y = toIcoDiv hp a x`.

Note that we use different functions on the LHS and on the RHS.
-/
/-
**eventuallyEq_toIocDiv_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_toIocDiv_nhdsGT : toIocDiv hp a =ᶠ[𝓝[>] x] fun _ => toIcoDiv 
hp a x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ioc_mem_nhdsGT_of_mem`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : LinearOrder α] [ClosedIciTopology α] {a b c : α},   b ∈ Set.Ico c a → Set.Io
c c a ∈ nhd…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sub_mem_Ico_iff_left`：sub_mem_Ico_iff_left : a - b in Set.Ico c d ↔ 
a in Set.Ico (c + b) (d + b)
· 使用定理 `toIcoDiv_eq_iff`：toIcoDiv_eq_iff : toIcoDiv hp a b = n ↔ b - n • p in Se
t.Ico a (a + p)

--- 原说明 ---
At every point `x`, for all `y > x` sufficiently close to `x`,
we have `toIocDiv hp a y = toIcoDiv hp a x`.

Note that we use different functions on the LHS and on the RHS.
-/
theorem eventuallyEq_toIocDiv_nhdsGT : toIocDiv hp a =ᶠ[𝓝[>] x] fun _ ↦ toIcoDiv hp a x := by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsGT_of_mem
  rw [← sub_mem_Ico_iff_left, ← toIcoDiv_eq_iff]

variable {x}

/-- If `x` is not congruent to `a` modulo `p`, then `toIcoDiv` is locally constant near `x`. -/
/-
**eventuallyEq_toIcoDiv_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_toIcoDiv_nhds (hx : ¬x ≡ a [PMOD p]) : toIcoDiv hp a =ᶠ[𝓝 x] 
fun _ => toIcoDiv hp a x
参数：hx : ¬x ≡ a [PMOD p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsLT_sup_nhdsGE`：nhdsLT_sup_nhdsGE (a : α) : 𝓝[<] a ⊔ 𝓝[>=] a = 𝓝 a
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.eventually_sup`：eventually_sup {p : α -> Prop} {f g : Filter α} :
 (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddCommGroup.not_modEq_iff_toIcoDiv_eq_toIocDiv`：not_modEq_iff_toIcoDiv_
eq_toIocDiv : ¬a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `Filter.EventuallyEq.eventually`：∀ {α : Type u} {β : Type v} {l : Filter 
α} {f g : α → β}, f =ᶠ[l] g → ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `eventuallyEq_toIcoDiv_nhdsLT`：eventuallyEq_toIcoDiv_nhdsLT : toIcoDiv hp
 a =ᶠ[𝓝[<] x] fun _ => toIocDiv hp a x
· 使用定理 `eventuallyEq_toIcoDiv_nhdsGE`：eventuallyEq_toIcoDiv_nhdsGE : toIcoDiv hp
 a =ᶠ[𝓝[>=] x] fun _ => toIcoDiv hp a x

--- 原说明 ---
If `x` is not congruent to `a` modulo `p`, then `toIcoDiv` is locally constant n
ear `x`.
-/
theorem eventuallyEq_toIcoDiv_nhds (hx : ¬x ≡ a [PMOD p]) :
    toIcoDiv hp a =ᶠ[𝓝 x] fun _ ↦ toIcoDiv hp a x := by
  rw [← nhdsLT_sup_nhdsGE, Filter.EventuallyEq, Filter.eventually_sup]
  refine ⟨?_, eventuallyEq_toIcoDiv_nhdsGE hp a x⟩
  convert! (eventuallyEq_toIcoDiv_nhdsLT hp a x).eventually using 3
  rwa [← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

/-- If `x` is not congruent to `a` modulo `p`, then `toIcoDiv` is continuous at `x`.

In fact, it is locally near `x`, see `eventuallyEq_toIcoDiv_nhds`. -/
/-
**continuousAt_toIcoDiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_toIcoDiv (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIcoDiv hp a
) x
参数：hx : ¬x ≡ a [PMOD p]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `eventuallyEq_toIcoDiv_nhds`：eventuallyEq_toIcoDiv_nhds (hx : ¬x ≡ a [PMO
D p]) : toIcoDiv hp a =ᶠ[𝓝 x] fun _ => toIcoDiv hp a x

--- 原说明 ---
If `x` is not congruent to `a` modulo `p`, then `toIcoDiv` is continuous at `x`.

In fact, it is locally near `x`, see `eventuallyEq_toIcoDiv_nhds`.
-/
theorem continuousAt_toIcoDiv (hx : ¬x ≡ a [PMOD p]) :
    ContinuousAt (toIcoDiv hp a) x :=
  tendsto_nhds_of_eventually_eq <| eventuallyEq_toIcoDiv_nhds hp a hx

/-- `toIcoDiv` is continuous on the set of points that are not congruent to `a` modulo `p`. -/
/-
**continuousOn_toIcoDiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_toIcoDiv : ContinuousOn (toIcoDiv hp a) {x | ¬x ≡ a [PMOD p]}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `continuousAt_toIcoDiv`：continuousAt_toIcoDiv (hx : ¬x ≡ a [PMOD p]) : Co
ntinuousAt (toIcoDiv hp a) x

--- 原说明 ---
`toIcoDiv` is continuous on the set of points that are not congruent to `a` modu
lo `p`.
-/
theorem continuousOn_toIcoDiv : ContinuousOn (toIcoDiv hp a) {x | ¬x ≡ a [PMOD p]} := fun _x hx ↦
  (continuousAt_toIcoDiv hp a hx).continuousWithinAt

/-- If `x` is not congruent to `a` modulo `p`, then `toIocDiv` is locally constant near `x`. -/
/-
**eventuallyEq_toIocDiv_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_toIocDiv_nhds (hx : ¬x ≡ a [PMOD p]) : toIocDiv hp a =ᶠ[𝓝 x] 
fun _ => toIocDiv hp a x
参数：hx : ¬x ≡ a [PMOD p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsLE_sup_nhdsGT`：nhdsLE_sup_nhdsGT (a : α) : 𝓝[<=] a ⊔ 𝓝[>] a = 𝓝 a
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.eventually_sup`：eventually_sup {p : α -> Prop} {f g : Filter α} :
 (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
· 使用定理 `eventuallyEq_toIocDiv_nhdsLE`：eventuallyEq_toIocDiv_nhdsLE : toIocDiv hp
 a =ᶠ[𝓝[<=] x] fun _ => toIocDiv hp a x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AddCommGroup.not_modEq_iff_toIcoDiv_eq_toIocDiv`：not_modEq_iff_toIcoDiv_
eq_toIocDiv : ¬a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `Filter.EventuallyEq.eventually`：∀ {α : Type u} {β : Type v} {l : Filter 
α} {f g : α → β}, f =ᶠ[l] g → ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `eventuallyEq_toIocDiv_nhdsGT`：eventuallyEq_toIocDiv_nhdsGT : toIocDiv hp
 a =ᶠ[𝓝[>] x] fun _ => toIcoDiv hp a x

--- 原说明 ---
If `x` is not congruent to `a` modulo `p`, then `toIocDiv` is locally constant n
ear `x`.
-/
theorem eventuallyEq_toIocDiv_nhds (hx : ¬x ≡ a [PMOD p]) :
    toIocDiv hp a =ᶠ[𝓝 x] fun _ ↦ toIocDiv hp a x := by
  rw [← nhdsLE_sup_nhdsGT, Filter.EventuallyEq, Filter.eventually_sup]
  refine ⟨eventuallyEq_toIocDiv_nhdsLE hp a x, ?_⟩
  convert! (eventuallyEq_toIocDiv_nhdsGT hp a x).eventually using 3
  rwa [eq_comm, ← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

/-- If `x` is not congruent to `a` modulo `p`, then `toIocDiv` is continuous at `x`.

In fact, it is locally near `x`, see `eventuallyEq_toIocDiv_nhds`. -/
/-
**continuousAt_toIocDiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_toIocDiv (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIocDiv hp a
) x
参数：hx : ¬x ≡ a [PMOD p]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `eventuallyEq_toIocDiv_nhds`：eventuallyEq_toIocDiv_nhds (hx : ¬x ≡ a [PMO
D p]) : toIocDiv hp a =ᶠ[𝓝 x] fun _ => toIocDiv hp a x

--- 原说明 ---
If `x` is not congruent to `a` modulo `p`, then `toIocDiv` is continuous at `x`.

In fact, it is locally near `x`, see `eventuallyEq_toIocDiv_nhds`.
-/
theorem continuousAt_toIocDiv (hx : ¬x ≡ a [PMOD p]) :
    ContinuousAt (toIocDiv hp a) x :=
  tendsto_nhds_of_eventually_eq <| eventuallyEq_toIocDiv_nhds hp a hx

/-- `toIocDiv` is continuous on the set of points
that aren't congruent to the endpoint modulo the period. -/
/-
**continuousOn_toIocDiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_toIocDiv : ContinuousOn (toIocDiv hp a) {x | ¬x ≡ a [PMOD p]}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `continuousAt_toIocDiv`：continuousAt_toIocDiv (hx : ¬x ≡ a [PMOD p]) : Co
ntinuousAt (toIocDiv hp a) x

--- 原说明 ---
`toIocDiv` is continuous on the set of points
that aren't congruent to the endpoint modulo the period.
-/
theorem continuousOn_toIocDiv :
    ContinuousOn (toIocDiv hp a) {x | ¬x ≡ a [PMOD p]} := fun _x hx ↦
  (continuousAt_toIocDiv hp a hx).continuousWithinAt
/-
**toIcoMod_eventuallyEq_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIcoMod_eventuallyEq_toIocMod (hx : ¬x ≡ a [PMOD p]) : toIcoMod hp a =ᶠ[𝓝
 x] toIocMod hp a
参数：hx : ¬x ≡ a [PMOD p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ico_eq_locus_Ioc_eq_iUnion_Ioo`：Ico_eq_locus_Ioc_eq_iUnion_Ioo : { b | t
oIcoMod hp a b = toIocMod hp a b } = ⋃ z : Int, Set.Ioo (a + z • p) (a + p + z •
 p)
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod`：not_modEq_iff_toIcoMod_
eq_toIocMod : ¬a ≡ b [PMOD p] ↔ toIcoMod hp a b = toIocMod hp a b
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
-/
theorem toIcoMod_eventuallyEq_toIocMod (hx : ¬x ≡ a [PMOD p]) :
    toIcoMod hp a =ᶠ[𝓝 x] toIocMod hp a := by
  refine IsOpen.mem_nhds ?_ ?_
  · rw [Ico_eq_locus_Ioc_eq_iUnion_Ioo]
    exact isOpen_iUnion fun i => isOpen_Ioo
  · rwa [mem_ofPred_eq, ← not_modEq_iff_toIcoMod_eq_toIocMod hp, AddCommGroup.modEq_comm]
/-
**continuousAt_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_toIcoMod (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIcoMod hp a
) x
参数：hx : ¬x ≡ a [PMOD p]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `eventuallyEq_toIcoDiv_nhds`：eventuallyEq_toIcoDiv_nhds (hx : ¬x ≡ a [PMO
D p]) : toIcoDiv hp a =ᶠ[𝓝 x] fun _ => toIcoDiv hp a x
-/
theorem continuousAt_toIcoMod (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIcoMod hp a) x :=
  continuousAt_id.sub <| tendsto_nhds_of_eventually_eq <|
    (eventuallyEq_toIcoDiv_nhds hp a hx).fun_comp (· • p)
/-
**continuousAt_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_toIocMod (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIocMod hp a
) x
参数：hx : ¬x ≡ a [PMOD p]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `eventuallyEq_toIocDiv_nhds`：eventuallyEq_toIocDiv_nhds (hx : ¬x ≡ a [PMO
D p]) : toIocDiv hp a =ᶠ[𝓝 x] fun _ => toIocDiv hp a x
-/
theorem continuousAt_toIocMod (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIocMod hp a) x :=
  continuousAt_id.sub <| tendsto_nhds_of_eventually_eq <|
    (eventuallyEq_toIocDiv_nhds hp a hx).fun_comp (· • p)

end Continuity

/-- The "additive circle": `𝕜 ⧸ ℤ ∙ p`. See also `Circle` and `Real.Angle`. -/
/-
**AddCircle** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddCircle [AddCommGroup 𝕜] (p : 𝕜)
参数：p : 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "additive circle": `𝕜 ⧸ ℤ ∙ p`. See also `Circle` and `Real.Angle`.
-/
abbrev AddCircle [AddCommGroup 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p

namespace AddCircle

section LinearOrderedAddCommGroup

variable [AddCommGroup 𝕜] (p : 𝕜)

/-
**AddCircle.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_nsmul {n : Nat} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircl
e p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nsmul {n : ℕ} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl
/-
**AddCircle.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_zsmul {n : Int} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircl
e p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zsmul {n : ℤ} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl
/-
**AddCircle.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_add (x y : 𝕜) : (↑(x + y) : AddCircle p) = (x : AddCircle p) + (y : Ad
dCircle p)
参数：x y : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (x y : 𝕜) : (↑(x + y) : AddCircle p) = (x : AddCircle p) + (y : AddCircle p) :=
  rfl
/-
**AddCircle.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_sub (x y : 𝕜) : (↑(x - y) : AddCircle p) = (x : AddCircle p) - (y : Ad
dCircle p)
参数：x y : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (x y : 𝕜) : (↑(x - y) : AddCircle p) = (x : AddCircle p) - (y : AddCircle p) :=
  rfl
/-
**AddCircle.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_neg {x : 𝕜} : (↑(-x) : AddCircle p) = -(x : AddCircle p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg {x : 𝕜} : (↑(-x) : AddCircle p) = -(x : AddCircle p) :=
  rfl

@[norm_cast]
/-
**AddCircle.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_zero : ↑(0 : 𝕜) = (0 : AddCircle p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ↑(0 : 𝕜) = (0 : AddCircle p) :=
  rfl
/-
**AddCircle.coe_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) = 0 ↔ exists n : Int, n • p = 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) = 0 ↔ ∃ n : ℤ, n • p = x := by
  simp [AddSubgroup.mem_zmultiples_iff]
/-
**AddCircle.coe_period** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_period : (p : AddCircle p) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientAddGroup.eq_zero_iff`：∀ {G : Type u_1} [inst : AddGroup G] {N : 
AddSubgroup G} [inst_1 : N.Normal] (x : G), ↑x = 0 ↔ x ∈ N
· 使用定理 `AddSubgroup.mem_zmultiples`：∀ {G : Type u_1} [inst : AddGroup G] (g : G)
, g ∈ AddSubgroup.zmultiples g
-/
theorem coe_period : (p : AddCircle p) = 0 :=
  (QuotientAddGroup.eq_zero_iff p).2 <| mem_zmultiples p
/-
**AddCircle.coe_add_period** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_add_period (x : 𝕜) : ((x + p : 𝕜) : AddCircle p) = x
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.coe_add`：coe_add (x y : 𝕜) : (↑(x + y) : AddCircle p) = (x : A
ddCircle p) + (y : AddCircle p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `AddCircle.coe_period`：coe_period : (p : AddCircle p) = 0
-/
theorem coe_add_period (x : 𝕜) : ((x + p : 𝕜) : AddCircle p) = x := by
  rw [coe_add, ← eq_sub_iff_add_eq', sub_self, coe_period]

@[continuity, nolint unusedArguments]
/-
**AddCircle.continuous_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : AddCommGroup 𝕜] (p : 𝕜) [inst_1 : TopologicalSpac
e 𝕜],   Continuous ⇑(QuotientAddGroup.mk' (AddSubgroup.zmultiples p))
参数：p : 𝕜；QuotientAddGroup.mk' (AddSubgroup.zmultiples p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
-/
protected theorem continuous_mk' [TopologicalSpace 𝕜] :
    Continuous (QuotientAddGroup.mk' (zmultiples p) : 𝕜 → AddCircle p) :=
  continuous_coinduced_rng

section Torsion

-- TODO: move this (and the definition `AddCircle`) to GroupTheory.QuotientGroup.Basic
open QuotientAddGroup Cardinal in
/-
**AddCircle.card_torsion_le_of_isSMulRegular** 是 Mathlib 中的一个定理，位于命名空间 `AddCircl
e`。
形式化陈述：card_torsion_le_of_isSMulRegular (n : Nat) (h0 : n != 0) (hn : IsSMulRegul
ar 𝕜 n) : {x : AddCircle p | n • x = 0}.encard <= n
参数：n : Nat；h0 : n != 0；hn : IsSMulRegular 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `QuotientAddGroup.mk_surjective`：∀ {α : Type u_1} [inst : AddGroup α] {s 
: AddSubgroup α}, Function.Surjective QuotientAddGroup.mk
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientAddGroup.eq_zero_iff`：∀ {G : Type u_1} [inst : AddGroup G] {N : 
AddSubgroup G} [inst_1 : N.Normal] (x : G), ↑x = 0 ↔ x ∈ N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientAddGroup.mk_nsmul`：∀ {G : Type u_1} [inst : AddGroup G] (N : Add
Subgroup G) [nN : N.Normal] (a : G) (n : ℕ), ↑(n • a) = n • ↑a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddCircle.coe_period`：coe_period : (p : AddCircle p) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Int.divModEquiv_symm_apply`：∀ (n : ℕ) [inst : NeZero n] (p : ℤ × Fin n),
 (Int.divModEquiv n).symm p = p.1 * ↑n + ↑↑p.2
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ENat.card_le_card_of_injective`：card_le_card_of_injective {α β : Type*} 
{f : α -> β} (hf : Injective f) : card α <= card β
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
（共 33 条，此处仅展示前 30 条）
-/
theorem card_torsion_le_of_isSMulRegular (n : ℕ) (h0 : n ≠ 0) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.encard ≤ n := by
  have (x : {x : AddCircle p | n • x = 0}) : ∃ (k : Fin n) (y : 𝕜), y = x.1 ∧ n • y = k.1 • p := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := mk_surjective x
    rw [Set.mem_ofPred, ← mk_nsmul, eq_zero_iff] at hx
    have ⟨m', hm⟩ := hx
    have : NeZero n := ⟨h0⟩
    rw [← (Int.divModEquiv n).symm_apply_apply m', Int.divModEquiv_symm_apply] at hm
    set m := m'.divModEquiv n
    use m.2, y - m.1 • p
    simp_rw [mk_sub, mk_zsmul, sub_eq_self, coe_period, smul_zero]
    rw [smul_sub, sub_eq_iff_eq_add, ← hm, add_comm]
    simp [add_smul, mul_comm, mul_smul]
  choose f hf using this
  refine (ENat.card_le_card_of_injective (f := f) fun x x' eq ↦ Subtype.ext ?_).trans (by simp)
  have ⟨y, hyx, hy⟩ := hf x
  have ⟨y', hyx', hy'⟩ := hf x'
  rw [eq, ← hy', hn.eq_iff] at hy
  rw [← hyx, hy, hyx']
/-
**AddCircle.finite_torsion_of_isSMulRegular** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle
`。
形式化陈述：finite_torsion_of_isSMulRegular (n : Nat) (hn : IsSMulRegular 𝕜 n) : {x : 
AddCircle p | n • x = 0}.Finite
参数：n : Nat；hn : IsSMulRegular 𝕜 n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `AddSubgroup.finite_quotient_of_finiteIndex`：∀ {G : Type u_1} [inst : Add
Group G] {H : AddSubgroup G} [H.FiniteIndex], Finite (G ⧸ H)
· 使用定理 `AddSubgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : AddGroup G] 
{H : AddSubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `IsSMulRegular.not_zero`：not_zero [nM : Nontrivial M] : ¬IsSMulRegular M 
(0 : R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENat.card_lt_top`：∀ {α : Type u_1}, ENat.card α < ⊤ ↔ Finite α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `AddCircle.card_torsion_le_of_isSMulRegular`：card_torsion_le_of_isSMulReg
ular (n : Nat) (h0 : n != 0) (hn : IsSMulRegular 𝕜 n) : {x : AddCircle p | n • x
 = 0}.encard <= n
· 使用引理 `ENat.natCast_lt_top`：natCast_lt_top (n : Nat) : (n : Nat∞) < ⊤
-/
theorem finite_torsion_of_isSMulRegular (n : ℕ) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.Finite := by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
    (card_torsion_le_of_isSMulRegular p n h0 hn).trans_lt <| ENat.natCast_lt_top n]
/-
**AddCircle.card_torsion_le_of_isSMulRegular_int** 是 Mathlib 中的一个定理，位于命名空间 `AddC
ircle`。
形式化陈述：card_torsion_le_of_isSMulRegular_int (n : Int) (h0 : n != 0) (hn : IsSMulR
egular 𝕜 n) : {x : AddCircle p | n • x = 0}.encard <= n.natAbs
参数：n : Int；h0 : n != 0；hn : IsSMulRegular 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddCircle.card_torsion_le_of_isSMulRegular`：card_torsion_le_of_isSMulReg
ular (n : Nat) (h0 : n != 0) (hn : IsSMulRegular 𝕜 n) : {x : AddCircle p | n • x
 = 0}.encard <= n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natAbs_ne_zero`：∀ {a : ℤ}, a.natAbs ≠ 0 ↔ a ≠ 0
· 使用定理 `IsSMulRegular.natAbs_iff`：∀ {M : Type u_3} [inst : SubtractionMonoid M] 
{n : ℤ}, IsSMulRegular M n.natAbs ↔ IsSMulRegular M n
-/
theorem card_torsion_le_of_isSMulRegular_int (n : ℤ) (h0 : n ≠ 0) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.encard ≤ n.natAbs := by
  convert!
    card_torsion_le_of_isSMulRegular p _ (Int.natAbs_ne_zero.mpr h0)
      (IsSMulRegular.natAbs_iff.mpr hn) using 1
  simp
/-
**AddCircle.finite_torsion_of_isSMulRegular_int** 是 Mathlib 中的一个定理，位于命名空间 `AddCi
rcle`。
形式化陈述：finite_torsion_of_isSMulRegular_int (n : Int) (hn : IsSMulRegular 𝕜 n) : {
x : AddCircle p | n • x = 0}.Finite
参数：n : Int；hn : IsSMulRegular 𝕜 n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `AddSubgroup.finite_quotient_of_finiteIndex`：∀ {G : Type u_1} [inst : Add
Group G] {H : AddSubgroup G} [H.FiniteIndex], Finite (G ⧸ H)
· 使用定理 `AddSubgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : AddGroup G] 
{H : AddSubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `IsSMulRegular.not_zero`：not_zero [nM : Nontrivial M] : ¬IsSMulRegular M 
(0 : R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENat.card_lt_top`：∀ {α : Type u_1}, ENat.card α < ⊤ ↔ Finite α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `AddCircle.card_torsion_le_of_isSMulRegular_int`：card_torsion_le_of_isSMu
lRegular_int (n : Int) (h0 : n != 0) (hn : IsSMulRegular 𝕜 n) : {x : AddCircle p
 | n • x = 0}.encard <= n.natAbs
· 使用引理 `ENat.natCast_lt_top`：natCast_lt_top (n : Nat) : (n : Nat∞) < ⊤
-/
theorem finite_torsion_of_isSMulRegular_int (n : ℤ) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.Finite := by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
    (card_torsion_le_of_isSMulRegular_int p n h0 hn).trans_lt <| ENat.natCast_lt_top _]

end Torsion

variable [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]

/-
**AddCircle.finite_torsion** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：finite_torsion {n : Nat} (hn : 0 < n) : { u : AddCircle p | n • u = 0 }.Fi
nite
参数：hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.finite_torsion_of_isSMulRegular`：finite_torsion_of_isSMulRegul
ar (n : Nat) (hn : IsSMulRegular 𝕜 n) : {x : AddCircle p | n • x = 0}.Finite
· 使用定理 `IsSMulRegular.of_right_eq_zero_of_smul`：∀ {R : Type u_1} {M : Type u_3} 
[inst : AddGroup M] [inst_1 : DistribSMul R M] {r : R},   (∀ (m : M), r • m = 0 
→ m = 0) → IsSMulRegular M r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem finite_torsion {n : ℕ} (hn : 0 < n) : { u : AddCircle p | n • u = 0 }.Finite :=
  finite_torsion_of_isSMulRegular _ _ <| .of_right_eq_zero_of_smul fun _ ↦ by simp [hn.ne']
/-
**AddCircle.finite_setOfPred_addOrderOf_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`
。
形式化陈述：finite_setOfPred_addOrderOf_eq {n : Nat} (hn : 0 < n) : {u : AddCircle p |
 addOrderOf u = n}.Finite
参数：hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddCircle.finite_torsion`：finite_torsion {n : Nat} (hn : 0 < n) : { u : 
AddCircle p | n • u = 0 }.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `addOrderOf_eq_iff`：∀ {G : Type u_1} [inst : AddMonoid G] {x : G} {n : ℕ}
,   0 < n → (addOrderOf x = n ↔ n • x = 0 ∧ ∀ m < n, 0 < m → m • x ≠ 0)
-/
theorem finite_setOfPred_addOrderOf_eq {n : ℕ} (hn : 0 < n) :
    {u : AddCircle p | addOrderOf u = n}.Finite :=
  (finite_torsion p hn).subset fun _ h ↦ ((addOrderOf_eq_iff hn).mp h).1

@[deprecated (since := "2026-07-09")]
alias finite_setOf_addOrderOf_eq := finite_setOfPred_addOrderOf_eq
/-
**AddCircle.coe_eq_zero_of_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_eq_zero_of_pos_iff (hp : 0 < p) {x : 𝕜} (hx : 0 < x) : (x : AddCircle 
p) = 0 ↔ exists n : Nat, n • p = x
参数：hp : 0 < p；hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.coe_eq_zero_iff`：coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) =
 0 ↔ exists n : Int, n • p = x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zsmul_neg'`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ
), n • -a = -n • a
· 使用定理 `zsmul_nonneg`：∀ {G : Type u_2} [inst : SubNegMonoid G] [inst_1 : Preorde
r G] [AddLeftMono G] {x : G},   0 ≤ x → ∀ {n : ℤ}, 0 ≤ n → 0 ≤ n • x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_eq_zero_of_pos_iff (hp : 0 < p) {x : 𝕜} (hx : 0 < x) :
    (x : AddCircle p) = 0 ↔ ∃ n : ℕ, n • p = x := by
  rw [coe_eq_zero_iff]
  constructor <;> rintro ⟨n, rfl⟩
  · replace hx : 0 < n := by
      contrapose! hx
      simpa only [← neg_nonneg, ← zsmul_neg, zsmul_neg'] using zsmul_nonneg hp.le (neg_nonneg.2 hx)
    exact ⟨n.toNat, by rw [← natCast_zsmul, Int.toNat_of_nonneg hx.le]⟩
  · exact ⟨(n : ℤ), by simp⟩

variable [hp : Fact (0 < p)] (a : 𝕜) [Archimedean 𝕜]

/-- The equivalence between `AddCircle p` and the half-open interval `[a, a + p)`, whose inverse
is the natural quotient map. -/
/-
**AddCircle.equivIco** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：equivIco : AddCircle p ≃ Ico a (a + p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `AddCircle p` and the half-open interval `[a, a + p)`, w
hose inverse
is the natural quotient map.
-/
def equivIco : AddCircle p ≃ Ico a (a + p) :=
  QuotientAddGroup.equivIcoMod hp.out a

/-- The equivalence between `AddCircle p` and the half-open interval `(a, a + p]`, whose inverse
is the natural quotient map. -/
/-
**AddCircle.equivIoc** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：equivIoc : AddCircle p ≃ Ioc a (a + p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `AddCircle p` and the half-open interval `(a, a + p]`, w
hose inverse
is the natural quotient map.
-/
def equivIoc : AddCircle p ≃ Ioc a (a + p) :=
  QuotientAddGroup.equivIocMod hp.out a

/-- Given a function on `𝕜`, return the unique function on `AddCircle p` agreeing with `f` on
`[a, a + p)`. -/
/-
**AddCircle.liftIco** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：liftIco (f : 𝕜 -> B) : AddCircle p -> B
参数：f : 𝕜 -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function on `𝕜`, return the unique function on `AddCircle p` agreeing wi
th `f` on
`[a, a + p)`.
-/
def liftIco (f : 𝕜 → B) : AddCircle p → B :=
  domRestrict _ f ∘ AddCircle.equivIco p a

/-- Given a function on `𝕜`, return the unique function on `AddCircle p` agreeing with `f` on
`(a, a + p]`. -/
/-
**AddCircle.liftIoc** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：liftIoc (f : 𝕜 -> B) : AddCircle p -> B
参数：f : 𝕜 -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function on `𝕜`, return the unique function on `AddCircle p` agreeing wi
th `f` on
`(a, a + p]`.
-/
def liftIoc (f : 𝕜 → B) : AddCircle p → B :=
  domRestrict _ f ∘ AddCircle.equivIoc p a

variable {p a}
/-
**AddCircle.equivIco_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：equivIco_coe_eq {x : 𝕜} (hx : x in Ico a (a + p)) : (equivIco p a) x = ⟨x,
 hx⟩
参数：hx : x in Ico a (a + p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `AddCircle.equivIco.eq_1`：∀ {𝕜 : Type u_1} [inst : AddCommGroup 𝕜] (p : 𝕜
) [inst_1 : LinearOrder 𝕜] [inst_2 : IsOrderedAddMonoid 𝕜]   [hp : Fact (0 < p)]
 (a : 𝕜) [ins…
· 使用定理 `QuotientAddGroup.equivIcoMod_symm_apply`：∀ {α : Type u_1} [inst : AddCom
mGroup α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archime
dean α]   {p : α} (hp : 0 < p…
-/
theorem equivIco_coe_eq {x : 𝕜} (hx : x ∈ Ico a (a + p)) : (equivIco p a) x = ⟨x, hx⟩ := by
  rw [← Equiv.eq_symm_apply, equivIco, QuotientAddGroup.equivIcoMod_symm_apply]
/-
**AddCircle.equivIoc_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：equivIoc_coe_eq {x : 𝕜} (hx : x in Ioc a (a + p)) : (equivIoc p a) x = ⟨x,
 hx⟩
参数：hx : x in Ioc a (a + p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `AddCircle.equivIoc.eq_1`：∀ {𝕜 : Type u_1} [inst : AddCommGroup 𝕜] (p : 𝕜
) [inst_1 : LinearOrder 𝕜] [inst_2 : IsOrderedAddMonoid 𝕜]   [hp : Fact (0 < p)]
 (a : 𝕜) [ins…
· 使用定理 `QuotientAddGroup.equivIocMod_symm_apply`：∀ {α : Type u_1} [inst : AddCom
mGroup α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archime
dean α]   {p : α} (hp : 0 < p…
-/
theorem equivIoc_coe_eq {x : 𝕜} (hx : x ∈ Ioc a (a + p)) : (equivIoc p a) x = ⟨x, hx⟩ := by
  rw [← Equiv.eq_symm_apply, equivIoc, QuotientAddGroup.equivIocMod_symm_apply]

@[simp]
/-
**AddCircle.coe_equivIco** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：coe_equivIco {y : AddCircle p} : (equivIco p a y : AddCircle p) = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
lemma coe_equivIco {y : AddCircle p} :
    (equivIco p a y : AddCircle p) = y :=
  (equivIco p a).left_inv y

@[simp]
/-
**AddCircle.coe_equivIoc** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：coe_equivIoc {y : AddCircle p} : (equivIoc p a y : AddCircle p) = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
lemma coe_equivIoc {y : AddCircle p} :
    (equivIoc p a y : AddCircle p) = y :=
  (equivIoc p a).left_inv y
/-
**AddCircle.equivIco_coe_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：equivIco_coe_of_mem {y : 𝕜} (hy : y in Ico a (a + p)) : equivIco p a y = y
参数：hy : y in Ico a (a + p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivIco_coe_of_mem {y : 𝕜} (hy : y ∈ Ico a (a + p)) :
    equivIco p a y = y := by
  have : equivIco p a y = ⟨y, hy⟩ := (equivIco p a).right_inv ⟨y, hy⟩
  simp [this]
/-
**AddCircle.equivIoc_coe_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：equivIoc_coe_of_mem {y : 𝕜} (hy : y in Ioc a (a + p)) : equivIoc p a y = y
参数：hy : y in Ioc a (a + p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivIoc_coe_of_mem {y : 𝕜} (hy : y ∈ Ioc a (a + p)) :
    equivIoc p a y = y := by
  have : equivIoc p a y = ⟨y, hy⟩ := (equivIoc p a).right_inv ⟨y, hy⟩
  simp [this]
/-
**AddCircle.coe_eq_coe_iff_of_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_eq_coe_iff_of_mem_Ico {x y : 𝕜} (hx : x in Ico a (a + p)) (hy : y in I
co a (a + p)) : (x : AddCircle p) = y ↔ x = y
参数：hx : x in Ico a (a + p)；hy : y in Ico a (a + p)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
-/
theorem coe_eq_coe_iff_of_mem_Ico {x y : 𝕜} (hx : x ∈ Ico a (a + p)) (hy : y ∈ Ico a (a + p)) :
    (x : AddCircle p) = y ↔ x = y := by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ico a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIco p a at h
  rw [← (equivIco p a).right_inv ⟨x, hx⟩, ← (equivIco p a).right_inv ⟨y, hy⟩]
  exact h

/-- Ioc version of `coe_eq_coe_iff_of_mem_Ico`. -/
/-
**AddCircle.coe_eq_coe_iff_of_mem_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：coe_eq_coe_iff_of_mem_Ioc {x y : 𝕜} (hx : x in Ioc a (a + p)) (hy : y in I
oc a (a + p)) : (x : AddCircle p) = y ↔ x = y
参数：hx : x in Ioc a (a + p)；hy : y in Ioc a (a + p)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…

--- 原说明 ---
Ioc version of `coe_eq_coe_iff_of_mem_Ico`.
-/
lemma coe_eq_coe_iff_of_mem_Ioc {x y : 𝕜} (hx : x ∈ Ioc a (a + p)) (hy : y ∈ Ioc a (a + p)) :
    (x : AddCircle p) = y ↔ x = y := by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ioc a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIoc p a at h
  rw [← (equivIoc p a).right_inv ⟨x, hx⟩, ← (equivIoc p a).right_inv ⟨y, hy⟩]
  exact h
/-
**AddCircle.liftIco_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIco_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ico a (a + p)) : liftIco
 p a f ↑x = f x
参数：hx : x in Ico a (a + p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.equivIco_coe_eq`：equivIco_coe_eq {x : 𝕜} (hx : x in Ico a (a +
 p)) : (equivIco p a) x = ⟨x, hx⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftIco_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico a (a + p)) :
    liftIco p a f ↑x = f x := by
  simp [liftIco, equivIco_coe_eq hx]
/-
**AddCircle.liftIoc_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIoc_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ioc a (a + p)) : liftIoc
 p a f ↑x = f x
参数：hx : x in Ioc a (a + p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.equivIoc_coe_eq`：equivIoc_coe_eq {x : 𝕜} (hx : x in Ioc a (a +
 p)) : (equivIoc p a) x = ⟨x, hx⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftIoc_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ioc a (a + p)) :
    liftIoc p a f ↑x = f x := by
  simp [liftIoc, equivIoc_coe_eq hx]
/-
**AddCircle.liftIoc_eq_liftIco_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIoc_eq_liftIco_of_ne {f : 𝕜 -> B} {x : AddCircle p} (x_ne_a : x != a) 
: liftIoc p a f x = liftIco p a f x
参数：x_ne_a : x != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AddCircle.coe_equivIco`：coe_equivIco {y : AddCircle p} : (equivIco p a y
 : AddCircle p) = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.liftIco_coe_apply`：liftIco_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx 
: x in Ico a (a + p)) : liftIco p a f ↑x = f x
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `AddCircle.liftIoc_coe_apply`：liftIoc_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx 
: x in Ioc a (a + p)) : liftIoc p a f ↑x = f x
-/
theorem liftIoc_eq_liftIco_of_ne {f : 𝕜 → B} {x : AddCircle p}
    (x_ne_a : x ≠ a) : liftIoc p a f x = liftIco p a f x := by
  have x_eq_b : x = ↑(equivIco p a x) := coe_equivIco.symm
  rw [x_eq_b, liftIco_coe_apply (equivIco p a x).coe_prop]
  exact liftIoc_coe_apply (by grind)
/-
**AddCircle.liftIco_comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：liftIco_comp_apply {α β : Type*} {f : 𝕜 -> α} {g : α -> β} {a : 𝕜} {x : Ad
dCircle p} : liftIco p a (g ∘ f) x = g (liftIco p a f x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftIco_comp_apply {α β : Type*} {f : 𝕜 → α} {g : α → β} {a : 𝕜} {x : AddCircle p} :
    liftIco p a (g ∘ f) x = g (liftIco p a f x) := rfl
/-
**AddCircle.liftIoc_comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：liftIoc_comp_apply {α β : Type*} {f : 𝕜 -> α} {g : α -> β} {a : 𝕜} {x : Ad
dCircle p} : liftIoc p a (g ∘ f) x = g (liftIoc p a f x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftIoc_comp_apply {α β : Type*} {f : 𝕜 → α} {g : α → β} {a : 𝕜} {x : AddCircle p} :
    liftIoc p a (g ∘ f) x = g (liftIoc p a f x) := rfl
/-
**AddCircle.eq_coe_Ico** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：eq_coe_Ico (a : AddCircle p) : exists b in Ico 0 p, ↑b = a
参数：a : AddCircle p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma eq_coe_Ico (a : AddCircle p) : ∃ b ∈ Ico 0 p, ↑b = a := by
  let b := QuotientAddGroup.equivIcoMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIcoMod hp.out 0).symm_apply_apply a⟩

/-- `Ioc` version of `eq_coe_Ico`. -/
/-
**AddCircle.eq_coe_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：eq_coe_Ioc (a : AddCircle p) : exists b in Ioc 0 p, ↑b = a
参数：a : AddCircle p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x

--- 原说明 ---
`Ioc` version of `eq_coe_Ico`.
-/
lemma eq_coe_Ioc (a : AddCircle p) : ∃ b ∈ Ioc 0 p, ↑b = a := by
  let b := QuotientAddGroup.equivIocMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIocMod hp.out 0).symm_apply_apply a⟩
/-
**AddCircle.coe_eq_zero_iff_of_mem_Ico** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：coe_eq_zero_iff_of_mem_Ico (ha : a in Ico 0 p) : (a : AddCircle p) = 0 ↔ a
 = 0
参数：ha : a in Ico 0 p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCircle.coe_eq_coe_iff_of_mem_Ico`：coe_eq_coe_iff_of_mem_Ico {x y : 𝕜}
 (hx : x in Ico a (a + p)) (hy : y in Ico a (a + p)) : (x : AddCircle p) = y ↔ x
 = y
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `QuotientAddGroup.mk_zero`：∀ {G : Type u_1} [inst : AddGroup G] (N : AddS
ubgroup G) [nN : N.Normal], ↑0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma coe_eq_zero_iff_of_mem_Ico (ha : a ∈ Ico 0 p) :
    (a : AddCircle p) = 0 ↔ a = 0 := by
  have h0 : 0 ∈ Ico 0 (0 + p) := by simpa [zero_add, left_mem_Ico] using hp.out
  have ha' : a ∈ Ico 0 (0 + p) := by rwa [zero_add]
  rw [← AddCircle.coe_eq_coe_iff_of_mem_Ico ha' h0, QuotientAddGroup.mk_zero]

variable (p a)

section Continuity

variable [TopologicalSpace 𝕜]

@[continuity]
/-
**AddCircle.continuous_equivIco_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：continuous_equivIco_symm : Continuous (equivIco p a).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuous_equivIco_symm : Continuous (equivIco p a).symm :=
  continuous_quotient_mk'.comp continuous_subtype_val

@[continuity]
/-
**AddCircle.continuous_equivIoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：continuous_equivIoc_symm : Continuous (equivIoc p a).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuous_equivIoc_symm : Continuous (equivIoc p a).symm :=
  continuous_quotient_mk'.comp continuous_subtype_val

variable [OrderTopology 𝕜] {x : AddCircle p}
/-
**AddCircle.continuousAt_equivIco** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：continuousAt_equivIco (hx : x != a) : ContinuousAt (equivIco p a) x
参数：hx : x != a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `QuotientAddGroup.nhds_eq`：∀ {G : Type u_1} [inst : TopologicalSpace G] [
inst_1 : AddGroup G] [SeparatelyContinuousAdd G] (N : AddSubgroup G)   (x : G), 
nhds ↑x = Filt…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `ContinuousAt.codRestrict`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {t : Set Y}   (h1 : ∀ (x : X
), f x ∈ t) {x…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `continuousAt_toIcoMod`：continuousAt_toIcoMod (hx : ¬x ≡ a [PMOD p]) : Co
ntinuousAt (toIcoMod hp a) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGroup.not_modEq_iff_ne_mod_zmultiples`：not_modEq_iff_ne_mod_zmult
iples : ¬a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) != b
-/
theorem continuousAt_equivIco (hx : x ≠ a) : ContinuousAt (equivIco p a) x := by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt, Filter.Tendsto, QuotientAddGroup.nhds_eq, Filter.map_map]
  exact (continuousAt_toIcoMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _
/-
**AddCircle.continuousAt_equivIoc** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：continuousAt_equivIoc (hx : x != a) : ContinuousAt (equivIoc p a) x
参数：hx : x != a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `QuotientAddGroup.nhds_eq`：∀ {G : Type u_1} [inst : TopologicalSpace G] [
inst_1 : AddGroup G] [SeparatelyContinuousAdd G] (N : AddSubgroup G)   (x : G), 
nhds ↑x = Filt…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `ContinuousAt.codRestrict`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {t : Set Y}   (h1 : ∀ (x : X
), f x ∈ t) {x…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `continuousAt_toIocMod`：continuousAt_toIocMod (hx : ¬x ≡ a [PMOD p]) : Co
ntinuousAt (toIocMod hp a) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGroup.not_modEq_iff_ne_mod_zmultiples`：not_modEq_iff_ne_mod_zmult
iples : ¬a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) != b
-/
theorem continuousAt_equivIoc (hx : x ≠ a) : ContinuousAt (equivIoc p a) x := by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt, Filter.Tendsto, QuotientAddGroup.nhds_eq, Filter.map_map]
  exact (continuousAt_toIocMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _

/-- The quotient map `𝕜 → AddCircle p` as an open partial homeomorphism. -/
/-
**AddCircle.openPartialHomeomorphCoe** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：{𝕜 : Type u_1} →   [inst : AddCommGroup 𝕜] →     (p : 𝕜) →       [inst_1 :
 LinearOrder 𝕜] →         [IsOrderedAddMonoid 𝕜] →           [hp : Fact (0 < p)]
 →             𝕜 →               [Archimedean 𝕜] →                 [inst_4 : Top
ologicalSpace 𝕜] →                   [OrderTopology 𝕜] →                     [Di
screteTopology ↥(AddSubgroup.zmultiples p)] → OpenPartialHomeomorph 𝕜 (AddCircle
 p)
参数：p : 𝕜；0 < p；AddSubgroup.zmultiples p；AddCircle p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient map `𝕜 → AddCircle p` as an open partial homeomorphism.
-/
@[simps] def openPartialHomeomorphCoe [DiscreteTopology (zmultiples p)] :
    OpenPartialHomeomorph 𝕜 (AddCircle p) where
  toFun := (↑)
  invFun := fun x ↦ equivIco p a x
  source := Ioo a (a + p)
  target := {↑a}ᶜ
  map_source' := by
    intro x hx hx'
    exact hx.1.ne' ((coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hx)
      (left_mem_Ico.mpr (lt_add_of_pos_right a hp.out))).mp hx')
  map_target' := by
    intro x hx
    exact (eq_left_or_mem_Ioo_of_mem_Ico (equivIco p a x).2).resolve_left
      (hx ∘ ((equivIco p a).symm_apply_apply x).symm.trans ∘ congrArg _)
  left_inv' :=
    fun x hx ↦ congrArg _ ((equivIco p a).apply_symm_apply ⟨x, Ioo_subset_Ico_self hx⟩)
  right_inv' := fun x _ ↦ (equivIco p a).symm_apply_apply x
  open_source := isOpen_Ioo
  open_target := isOpen_compl_singleton
  continuousOn_toFun := (AddCircle.continuous_mk' p).continuousOn
  continuousOn_invFun := by
    exact continuousOn_of_forall_continuousAt
      (fun _ ↦ continuousAt_subtype_val.comp ∘ continuousAt_equivIco p a)

end Continuity

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → AddCircle p` is
the entire space. -/
@[simp]
/-
**AddCircle.coe_image_Ico_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_image_Ico_eq : ((↑) : 𝕜 -> AddCircle p) '' Ico a (a + p) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Equiv.range_eq_univ`：range_eq_univ (e : α ≃ β) : range e = univ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → A
ddCircle p` is
the entire space.
-/
theorem coe_image_Ico_eq : ((↑) : 𝕜 → AddCircle p) '' Ico a (a + p) = univ := by
  rw [image_eq_range]
  exact (equivIco p a).symm.range_eq_univ

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → AddCircle p` is
the entire space. -/
@[simp]
/-
**AddCircle.coe_image_Ioc_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_image_Ioc_eq : ((↑) : 𝕜 -> AddCircle p) '' Ioc a (a + p) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Equiv.range_eq_univ`：range_eq_univ (e : α ≃ β) : range e = univ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → A
ddCircle p` is
the entire space.
-/
theorem coe_image_Ioc_eq : ((↑) : 𝕜 → AddCircle p) '' Ioc a (a + p) = univ := by
  rw [image_eq_range]
  exact (equivIoc p a).symm.range_eq_univ

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → AddCircle p` is the
entire space. -/
@[simp]
/-
**AddCircle.coe_image_Icc_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_image_Icc_eq : ((↑) : 𝕜 -> AddCircle p) '' Icc a (a + p) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_mono`：eq_top_mono (h : a <= b) (h₂ : a = ⊤) : b = ⊤
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `AddCircle.coe_image_Ico_eq`：coe_image_Ico_eq : ((↑) : 𝕜 -> AddCircle p) 
'' Ico a (a + p) = univ

--- 原说明 ---
The image of the closed interval `[0, p]` under the quotient map `𝕜 → AddCircle 
p` is the
entire space.
-/
theorem coe_image_Icc_eq : ((↑) : 𝕜 → AddCircle p) '' Icc a (a + p) = univ :=
  eq_top_mono (image_mono Ico_subset_Icc_self) <| coe_image_Ico_eq _ _

/-- If functions on AddCircle agree on the image of the interval `[a, a + p)` then they are equal -/
/-
**AddCircle.Ico_ext** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：Ico_ext {α : Type*} {f g : AddCircle p -> α} (a : 𝕜) (h : forall x in Ico 
a (a + p), f x = g x) : f = g
参数：a : 𝕜；h : forall x in Ico a (a + p), f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eqOn_univ`：eqOn_univ (f₁ f₂ : α -> β) : EqOn f₁ f₂ univ ↔ f₁ = f₂
· 使用定理 `AddCircle.coe_image_Ico_eq`：coe_image_Ico_eq : ((↑) : 𝕜 -> AddCircle p) 
'' Ico a (a + p) = univ

--- 原说明 ---
If functions on AddCircle agree on the image of the interval `[a, a + p)` then t
hey are equal
-/
lemma Ico_ext {α : Type*} {f g : AddCircle p → α} (a : 𝕜)
    (h : ∀ x ∈ Ico a (a + p), f x = g x) : f = g := by
  rw [← Set.eqOn_univ, ← coe_image_Ico_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

/-- If functions on AddCircle agree on the image of the interval `(a, a + p]` then they are equal -/
/-
**AddCircle.Ioc_ext** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：Ioc_ext {α : Type*} {f g : AddCircle p -> α} (a : 𝕜) (h : forall x in Ioc 
a (a + p), f x = g x) : f = g
参数：a : 𝕜；h : forall x in Ioc a (a + p), f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eqOn_univ`：eqOn_univ (f₁ f₂ : α -> β) : EqOn f₁ f₂ univ ↔ f₁ = f₂
· 使用定理 `AddCircle.coe_image_Ioc_eq`：coe_image_Ioc_eq : ((↑) : 𝕜 -> AddCircle p) 
'' Ioc a (a + p) = univ

--- 原说明 ---
If functions on AddCircle agree on the image of the interval `(a, a + p]` then t
hey are equal
-/
lemma Ioc_ext {α : Type*} {f g : AddCircle p → α} (a : 𝕜)
    (h : ∀ x ∈ Ioc a (a + p), f x = g x) : f = g := by
  rw [← Set.eqOn_univ, ← coe_image_Ioc_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

end LinearOrderedAddCommGroup

section LinearOrderedField

variable [Field 𝕜] (p q : 𝕜)

/-- The rescaling equivalence between additive circles with different periods. -/
/-
**AddCircle.equivAddCircle** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：equivAddCircle (hp : p != 0) (hq : q != 0) : AddCircle p ≃+ AddCircle q
参数：hp : p != 0；hq : q != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rescaling equivalence between additive circles with different periods.
-/
def equivAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃+ AddCircle q :=
  QuotientAddGroup.congr _ _ (AddAut.mulRight <| (Units.mk0 p hp)⁻¹ * Units.mk0 q hq) <| by
    rw [AddMonoidHom.map_zmultiples, AddMonoidHom.coe_coe, AddAut.mulRight_apply, Units.val_mul,
      Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel_left₀ hp]

@[simp]
/-
**AddCircle.equivAddCircle_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：equivAddCircle_apply_mk (hp : p != 0) (hq : q != 0) (x : 𝕜) : equivAddCirc
le p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜)
参数：hp : p != 0；hq : q != 0；x : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivAddCircle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    equivAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
/-
**AddCircle.equivAddCircle_symm_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：equivAddCircle_symm_apply_mk (hp : p != 0) (hq : q != 0) (x : 𝕜) : (equivA
ddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜)
参数：hp : p != 0；hq : q != 0；x : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivAddCircle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (equivAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl

section
variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/-- The rescaling homeomorphism between additive circles with different periods. -/
/-
**AddCircle.homeomorphAddCircle** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：homeomorphAddCircle (hp : p != 0) (hq : q != 0) : AddCircle p ≃ₜ AddCircle
 q
参数：hp : p != 0；hq : q != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rescaling homeomorphism between additive circles with different periods.
-/
def homeomorphAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃ₜ AddCircle q :=
  ⟨equivAddCircle p q hp hq,
    (continuous_quotient_mk'.comp (continuous_mul_const (p⁻¹ * q))).quotient_lift _,
    (continuous_quotient_mk'.comp (continuous_mul_const (q⁻¹ * p))).quotient_lift _⟩

@[simp]
/-
**AddCircle.homeomorphAddCircle_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：homeomorphAddCircle_apply_mk (hp : p != 0) (hq : q != 0) (x : 𝕜) : homeomo
rphAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜)
参数：hp : p != 0；hq : q != 0；x : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homeomorphAddCircle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    homeomorphAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
/-
**AddCircle.homeomorphAddCircle_symm_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddCirc
le`。
形式化陈述：homeomorphAddCircle_symm_apply_mk (hp : p != 0) (hq : q != 0) (x : 𝕜) : (h
omeomorphAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜)
参数：hp : p != 0；hq : q != 0；x : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homeomorphAddCircle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (homeomorphAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl
end

/-
**AddCircle.natCast_div_mul_eq_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：natCast_div_mul_eq_nsmul (r : 𝕜) (m : Nat) : (↑(↑m / q * r) : AddCircle p)
 = m • (r / q : AddCircle p)
参数：r : 𝕜；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `AddCircle.coe_nsmul`：coe_nsmul {n : Nat} {x : 𝕜} : (↑(n • x) : AddCircle
 p) = n • (x : AddCircle p)
-/
lemma natCast_div_mul_eq_nsmul (r : 𝕜) (m : ℕ) :
    (↑(↑m / q * r) : AddCircle p) = m • (r / q : AddCircle p) := by
  rw [mul_comm_div, ← nsmul_eq_mul, coe_nsmul]
/-
**AddCircle.intCast_div_mul_eq_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：intCast_div_mul_eq_zsmul (r : 𝕜) (m : Int) : (↑(↑m / q * r) : AddCircle p)
 = m • (r / q : AddCircle p)
参数：r : 𝕜；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `AddCircle.coe_zsmul`：coe_zsmul {n : Int} {x : 𝕜} : (↑(n • x) : AddCircle
 p) = n • (x : AddCircle p)
-/
lemma intCast_div_mul_eq_zsmul (r : 𝕜) (m : ℤ) :
    (↑(↑m / q * r) : AddCircle p) = m • (r / q : AddCircle p) := by
  rw [mul_comm_div, ← zsmul_eq_mul, coe_zsmul]

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [hp : Fact (0 < p)]

section FloorRing

variable [FloorRing 𝕜]

@[simp]
/-
**AddCircle.coe_equivIco_mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：coe_equivIco_mk_apply (x : 𝕜) : (equivIco p 0 <| QuotientAddGroup.mk x : 𝕜
) = Int.fract (x / p) * p
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toIcoMod_eq_fract_mul`：toIcoMod_eq_fract_mul (b : α) : toIcoMod hp 0 b =
 Int.fract (b / p) * p
-/
theorem coe_equivIco_mk_apply (x : 𝕜) :
    (equivIco p 0 <| QuotientAddGroup.mk x : 𝕜) = Int.fract (x / p) * p :=
  toIcoMod_eq_fract_mul _ x
/-
**AddCircle.** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DivisibleBy (AddCircle p) ℤ where
  div x n := (↑((n : 𝕜)⁻¹ * (equivIco p 0 x : 𝕜)) : AddCircle p)
  div_zero x := by simp
  div_cancel {n} x hn := by
    replace hn : (n : 𝕜) ≠ 0 := by norm_cast
    change n • QuotientAddGroup.mk' _ ((n : 𝕜)⁻¹ * ↑(equivIco p 0 x)) = x
    rw [← map_zsmul, ← smul_mul_assoc, zsmul_eq_mul, mul_inv_cancel₀ hn, one_mul]
    exact (equivIco p 0).symm_apply_apply x

omit [IsStrictOrderedRing 𝕜] in
/-
**AddCircle.coe_fract** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : Floor
Ring 𝕜] (x : 𝕜), ↑(Int.fract x) = ↑x
参数：x : 𝕜；Int.fract x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
@[simp] lemma coe_fract (x : 𝕜) : (↑(Int.fract x) : AddCircle (1 : 𝕜)) = x := by
  simp [← Int.self_sub_floor, mem_zmultiples_iff]

end FloorRing

section FiniteOrderPoints

variable {p}

/-
**AddCircle.addOrderOf_period_div** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：addOrderOf_period_div {n : Nat} (h : 0 < n) : addOrderOf ((p / n : 𝕜) : Ad
dCircle p) = n
参数：h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `addOrderOf_eq_iff`：∀ {G : Type u_1} [inst : AddMonoid G] {x : G} {n : ℕ}
,   0 < n → (addOrderOf x = n ↔ n • x = 0 ∧ ∀ m < n, 0 < m → m • x ≠ 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `AddCircle.coe_period`：coe_period : (p : AddCircle p) = 0
· 使用定理 `AddCircle.coe_eq_zero_of_pos_iff`：coe_eq_zero_of_pos_iff (hp : 0 < p) {x
 : 𝕜} (hx : 0 < x) : (x : AddCircle p) = 0 ↔ exists n : Nat, n • p = x
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
（共 36 条，此处仅展示前 30 条）
-/
theorem addOrderOf_period_div {n : ℕ} (h : 0 < n) : addOrderOf ((p / n : 𝕜) : AddCircle p) = n := by
  rw [addOrderOf_eq_iff h]
  replace h : 0 < (n : 𝕜) := Nat.cast_pos.2 h
  refine ⟨?_, fun m hn h0 => ?_⟩ <;> simp only [Ne, ← coe_nsmul, nsmul_eq_mul]
  · rw [mul_div_cancel₀ _ h.ne', coe_period]
  rw [coe_eq_zero_of_pos_iff p hp.out (mul_pos (Nat.cast_pos.2 h0) <| div_pos hp.out h)]
  rintro ⟨k, hk⟩
  rw [mul_div, eq_div_iff h.ne', nsmul_eq_mul, mul_right_comm, ← Nat.cast_mul,
    (mul_left_injective₀ hp.out.ne').eq_iff, Nat.cast_inj, mul_comm] at hk
  exact (Nat.le_of_dvd h0 ⟨_, hk.symm⟩).not_gt hn

variable (p) in
/-
**AddCircle.gcd_mul_addOrderOf_div_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：gcd_mul_addOrderOf_div_eq {n : Nat} (m : Nat) (hn : 0 < n) : m.gcd n * add
OrderOf (↑(↑m / ↑n * p) : AddCircle p) = n
参数：m : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddCircle.natCast_div_mul_eq_nsmul`：natCast_div_mul_eq_nsmul (r : 𝕜) (m 
: Nat) : (↑(↑m / q * r) : AddCircle p) = m • (r / q : AddCircle p)
· 使用定理 `IsOfFinAddOrder.addOrderOf_nsmul`：∀ {G : Type u_1} [inst : AddMonoid G] 
(x : G) (n : ℕ),   IsOfFinAddOrder x → addOrderOf (n • x) = addOrderOf x / (addO
rderOf x).gcd n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `addOrderOf_pos_iff`：∀ {G : Type u_1} [inst : AddMonoid G] {x : G}, 0 < a
ddOrderOf x ↔ IsOfFinAddOrder x
· 使用定理 `AddCircle.addOrderOf_period_div`：addOrderOf_period_div {n : Nat} (h : 0 
< n) : addOrderOf ((p / n : 𝕜) : AddCircle p) = n
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
-/
theorem gcd_mul_addOrderOf_div_eq {n : ℕ} (m : ℕ) (hn : 0 < n) :
    m.gcd n * addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  rw [natCast_div_mul_eq_nsmul, IsOfFinAddOrder.addOrderOf_nsmul]
  · rw [addOrderOf_period_div hn, Nat.gcd_comm, Nat.mul_div_cancel']
    exact n.gcd_dvd_left m
  · rwa [← addOrderOf_pos_iff, addOrderOf_period_div hn]
/-
**AddCircle.addOrderOf_div_of_gcd_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：addOrderOf_div_of_gcd_eq_one {m n : Nat} (hn : 0 < n) (h : m.gcd n = 1) : 
addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n
参数：hn : 0 < n；h : m.gcd n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddCircle.gcd_mul_addOrderOf_div_eq`：gcd_mul_addOrderOf_div_eq {n : Nat}
 (m : Nat) (hn : 0 < n) : m.gcd n * addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = 
n
-/
theorem addOrderOf_div_of_gcd_eq_one {m n : ℕ} (hn : 0 < n) (h : m.gcd n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  convert! gcd_mul_addOrderOf_div_eq p m hn
  rw [h, one_mul]
/-
**AddCircle.addOrderOf_div_of_gcd_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：addOrderOf_div_of_gcd_eq_one' {m : Int} {n : Nat} (hn : 0 < n) (h : m.natA
bs.gcd n = 1) : addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n
参数：hn : 0 < n；h : m.natAbs.gcd n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `AddCircle.addOrderOf_div_of_gcd_eq_one`：addOrderOf_div_of_gcd_eq_one {m 
n : Nat} (hn : 0 < n) (h : m.gcd n = 1) : addOrderOf (↑(↑m / ↑n * p) : AddCircle
 p) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `addOrderOf_neg`：∀ {G : Type u_1} [inst : AddGroup G] (x : G), addOrderOf
 (-x) = addOrderOf x
-/
theorem addOrderOf_div_of_gcd_eq_one' {m : ℤ} {n : ℕ} (hn : 0 < n) (h : m.natAbs.gcd n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  cases m
  · simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.natAbs_natCast] at h ⊢
    exact addOrderOf_div_of_gcd_eq_one hn h
  · simp only [Int.cast_negSucc, neg_div, neg_mul, coe_neg, addOrderOf_neg]
    exact addOrderOf_div_of_gcd_eq_one hn h
/-
**AddCircle.addOrderOf_coe_rat** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：addOrderOf_coe_rat {q : Rat} : addOrderOf (↑(↑q * p) : AddCircle p) = q.de
n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
· 使用引理 `Rat.cast_divInt_of_ne_zero`：cast_divInt_of_ne_zero (a : Int) {b : Int} (
b0 : (b : α) != 0) : (a /. b : α) = a / b
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `AddCircle.addOrderOf_div_of_gcd_eq_one'`：addOrderOf_div_of_gcd_eq_one' {
m : Int} {n : Nat} (hn : 0 < n) (h : m.natAbs.gcd n = 1) : addOrderOf (↑(↑m / ↑n
 * p) : AddCircle p) = n
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
-/
theorem addOrderOf_coe_rat {q : ℚ} : addOrderOf (↑(↑q * p) : AddCircle p) = q.den := by
  have : (↑(q.den : ℤ) : 𝕜) ≠ 0 := by
    norm_cast
    exact q.pos.ne.symm
  rw [← q.num_divInt_den, Rat.cast_divInt_of_ne_zero _ this, Int.cast_natCast, Rat.num_divInt_den,
    addOrderOf_div_of_gcd_eq_one' q.pos q.reduced]
/-
**AddCircle.nsmul_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Field 𝕜] {p : 𝕜} [inst_1 : LinearOrder 𝕜] [IsStri
ctOrderedRing 𝕜] [hp : Fact (0 < p)]   {u : AddCircle p} {n : ℕ}, 0 < n → (n • u
 = 0 ↔ ∃ m < n, ↑(↑m / ↑n * p) = u)
参数：0 < p；n • u = 0 ↔ ∃ m < n, ↑(↑m / ↑n * p) = u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.coe_eq_zero_iff`：coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) =
 0 ↔ exists n : Int, n • p = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCircle.coe_nsmul`：coe_nsmul {n : Nat} {x : 𝕜} : (↑(n • x) : AddCircle
 p) = n • (x : AddCircle p)
· 使用引理 `Int.natMod_lt`：natMod_lt {n : Nat} (hn : n != 0) : m.natMod n < n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Int.ediv_mul_add_emod`：∀ (a b : ℤ), a / b * b + a % b = a
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `AddCircle.coe_add`：coe_add (x y : 𝕜) : (↑(x + y) : AddCircle p) = (x : A
ddCircle p) + (y : AddCircle p)
· 使用定理 `Int.natMod.eq_1`：∀ (m n : ℤ), m.natMod n = (m % n).toNat
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 40 条，此处仅展示前 30 条）
-/
protected theorem nsmul_eq_zero_iff {u : AddCircle p} {n : ℕ} (h : 0 < n) :
    n • u = 0 ↔ ∃ m < n, ↑(↑m / ↑n * p) = u := by
  refine ⟨QuotientAddGroup.induction_on u fun k hk ↦ ?_, ?_⟩
  · rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    rintro ⟨m, -, rfl⟩
    constructor; rw [mul_comm, eq_comm]
    exact gcd_mul_addOrderOf_div_eq p m h
  rw [← coe_nsmul, coe_eq_zero_iff] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨a.natMod n, Int.natMod_lt h.ne', ?_⟩
  have h0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 h.ne'
  rw [nsmul_eq_mul, mul_comm, ← div_eq_iff h0, ← a.ediv_mul_add_emod n, add_smul, add_div,
    zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, ← mul_div, mul_comm _ p,
    mul_div_cancel_right₀ p h0] at ha
  rw [← ha, coe_add, ← Int.cast_natCast, Int.natMod, Int.toNat_of_nonneg, zsmul_eq_mul,
    mul_div_right_comm, eq_comm, add_eq_right, ← zsmul_eq_mul, coe_zsmul, coe_period, smul_zero]
  exact Int.emod_nonneg _ (by exact_mod_cast h.ne')
/-
**AddCircle.addOrderOf_eq_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：addOrderOf_eq_pos_iff {u : AddCircle p} {n : Nat} (h : 0 < n) : addOrderOf
 u = n ↔ exists m < n, m.gcd n = 1 ∧ ↑(↑m / ↑n * p) = u
参数：h : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddCircle.nsmul_eq_zero_iff`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] {p : 𝕜} [
inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [hp : Fact (0 < p)]   {u : AddCi
rcle p} {n : ℕ}, …
· 使用定理 `addOrderOf_nsmul_eq_zero`：∀ {G : Type u_1} [inst : AddMonoid G] (x : G),
 addOrderOf x • x = 0
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddCircle.gcd_mul_addOrderOf_div_eq`：gcd_mul_addOrderOf_div_eq {n : Nat}
 (m : Nat) (hn : 0 < n) : m.gcd n * addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = 
n
· 使用定理 `AddCircle.addOrderOf_div_of_gcd_eq_one`：addOrderOf_div_of_gcd_eq_one {m 
n : Nat} (hn : 0 < n) (h : m.gcd n = 1) : addOrderOf (↑(↑m / ↑n * p) : AddCircle
 p) = n
-/
theorem addOrderOf_eq_pos_iff {u : AddCircle p} {n : ℕ} (h : 0 < n) :
    addOrderOf u = n ↔ ∃ m < n, m.gcd n = 1 ∧ ↑(↑m / ↑n * p) = u := by
  refine ⟨QuotientAddGroup.induction_on u ?_, ?_⟩
  · rintro ⟨m, -, h₁, rfl⟩
    exact addOrderOf_div_of_gcd_eq_one h h₁
  rintro k rfl
  obtain ⟨m, hm, hk⟩ := (AddCircle.nsmul_eq_zero_iff h).mp
    (addOrderOf_nsmul_eq_zero (k : AddCircle p))
  refine ⟨m, hm, mul_right_cancel₀ h.ne' ?_, hk⟩
  convert! gcd_mul_addOrderOf_div_eq p m h using 1
  · rw [hk]
  · apply one_mul
/-
**AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder** 是 Mathlib 中的一个定理，位于命名空间 `AddC
ircle`。
形式化陈述：exists_gcd_eq_one_of_isOfFinAddOrder {u : AddCircle p} (h : IsOfFinAddOrde
r u) : exists m : Nat, m.gcd (addOrderOf u) = 1 ∧ m < addOrderOf u ∧ ↑((m : 𝕜) /
 addOrderOf u * p) = u
参数：h : IsOfFinAddOrder u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddCircle.addOrderOf_eq_pos_iff`：addOrderOf_eq_pos_iff {u : AddCircle p}
 {n : Nat} (h : 0 < n) : addOrderOf u = n ↔ exists m < n, m.gcd n = 1 ∧ ↑(↑m / ↑
n * p) = u
· 使用定理 `IsOfFinAddOrder.addOrderOf_pos`：∀ {G : Type u_1} [inst : AddMonoid G] {x
 : G}, IsOfFinAddOrder x → 0 < addOrderOf x
-/
theorem exists_gcd_eq_one_of_isOfFinAddOrder {u : AddCircle p} (h : IsOfFinAddOrder u) :
    ∃ m : ℕ, m.gcd (addOrderOf u) = 1 ∧ m < addOrderOf u ∧ ↑((m : 𝕜) / addOrderOf u * p) = u :=
  let ⟨m, hl, hg, he⟩ := (addOrderOf_eq_pos_iff h.addOrderOf_pos).1 rfl
  ⟨m, hg, hl, he⟩
/-
**AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div** 是 Mathlib 中的一个引理，位于命名空间 
`AddCircle`。
形式化陈述：not_isOfFinAddOrder_iff_forall_rat_ne_div {a : 𝕜} : ¬ IsOfFinAddOrder (a :
 AddCircle p) ↔ forall q : Rat, (q : 𝕜) != a / p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_isOfFinAddOrder_iff_forall_rat_ne_div {a : 𝕜} :
    ¬ IsOfFinAddOrder (a : AddCircle p) ↔ ∀ q : ℚ, (q : 𝕜) ≠ a / p := by
  simp +contextual [← QuotientAddGroup.mk_zsmul, mul_comm (Int.cast _), mem_zmultiples_iff,
    eq_div_iff (Fact.out : 0 < p).ne', isOfFinAddOrder_iff_zsmul_eq_zero, Rat.forall, div_eq_iff,
    div_mul_eq_mul_div]
  grind
/-
**AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div** 是 Mathlib 中的一个引理，位于命名空间 `Add
Circle`。
形式化陈述：isOfFinAddOrder_iff_exists_rat_eq_div {a : 𝕜} : IsOfFinAddOrder (a : AddCi
rcle p) ↔ exists q : Rat, (q : 𝕜) = a / p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用引理 `AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div`：not_isOfFinAddOrder
_iff_forall_rat_ne_div {a : 𝕜} : ¬ IsOfFinAddOrder (a : AddCircle p) ↔ forall q 
: Rat, (q : 𝕜) != a / p
-/
lemma isOfFinAddOrder_iff_exists_rat_eq_div {a : 𝕜} :
    IsOfFinAddOrder (a : AddCircle p) ↔ ∃ q : ℚ, (q : 𝕜) = a / p := by
  simpa using not_isOfFinAddOrder_iff_forall_rat_ne_div.not_right

variable (p)

set_option backward.isDefEq.respectTransparency false in
/-- The natural bijection between points of order `n` and natural numbers less than and coprime to
`n`. The inverse of the map sends `m ↦ (m/n * p : AddCircle p)` where `m` is coprime to `n` and
satisfies `0 ≤ m < n`. -/
/-
**AddCircle.setAddOrderOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：setAddOrderOfEquiv {n : Nat} (hn : 0 < n) : { u : AddCircle p | addOrderOf
 u = n } ≃ { m | m < n ∧ m.gcd n = 1 }
参数：hn : 0 < n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural bijection between points of order `n` and natural numbers less than 
and coprime to
`n`. The inverse of the map sends `m ↦ (m/n * p : AddCircle p)` where `m` is cop
rime to `n` and
satisfies `0 ≤ m < n`.
-/
def setAddOrderOfEquiv {n : ℕ} (hn : 0 < n) :
    { u : AddCircle p | addOrderOf u = n } ≃ { m | m < n ∧ m.gcd n = 1 } :=
  Equiv.symm <|
    Equiv.ofBijective (fun m => ⟨↑((m : 𝕜) / n * p), addOrderOf_div_of_gcd_eq_one hn m.prop.2⟩)
      (by
        refine ⟨fun m₁ m₂ h => Subtype.ext ?_, fun u => ?_⟩
        · simp_rw [Subtype.mk_eq_mk, natCast_div_mul_eq_nsmul] at h
          refine nsmul_injOn_Iio_addOrderOf ?_ ?_ h <;> rw [addOrderOf_period_div hn]
          exacts [m₁.2.1, m₂.2.1]
        · obtain ⟨m, hmn, hg, he⟩ := (addOrderOf_eq_pos_iff hn).mp u.2
          exact ⟨⟨m, hmn, hg⟩, Subtype.ext he⟩)

@[simp]
/-
**AddCircle.card_addOrderOf_eq_totient** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：card_addOrderOf_eq_totient {n : Nat} : Nat.card { u : AddCircle p // addOr
derOf u = n } = n.totient
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.coe_ofPred`：Set.coe_ofPred (p : α -> Prop) : ↥{ x | p x } = { x // p
 x }
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `infinite_not_isOfFinAddOrder`：∀ {G : Type u_1} [inst : AddLeftCancelMono
id G] {x : G}, ¬IsOfFinAddOrder x → {y | ¬IsOfFinAddOrder y}.Infinite
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.card_of_isEmpty`：∀ {α : Type u_1} [IsEmpty α], Nat.card α = 0
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.totient_eq_card_lt_and_coprime`：totient_eq_card_lt_and_coprime (n : 
Nat) : φ n = Nat.card { m | m < n ∧ n.Coprime m }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_addOrderOf_eq_totient {n : ℕ} :
    Nat.card { u : AddCircle p // addOrderOf u = n } = n.totient := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp only [Nat.totient_zero, addOrderOf_eq_zero_iff]
    rcases em (∃ u : AddCircle p, ¬IsOfFinAddOrder u) with (⟨u, hu⟩ | h)
    · have : Infinite { u : AddCircle p // ¬IsOfFinAddOrder u } := by
        rw [← coe_ofPred, infinite_coe_iff]
        exact infinite_not_isOfFinAddOrder hu
      exact Nat.card_eq_zero_of_infinite
    · have : IsEmpty { u : AddCircle p // ¬IsOfFinAddOrder u } := by simpa [isEmpty_subtype] using h
      exact Nat.card_of_isEmpty
  · rw [← coe_ofPred, Nat.card_congr (setAddOrderOfEquiv p hn),
      n.totient_eq_card_lt_and_coprime]
    simp only [Nat.gcd_comm]

end FiniteOrderPoints

end LinearOrderedField

end AddCircle

section IdentifyIccEnds

/-! This section proves that for any `a`, the natural map from `[a, a + p] ⊂ 𝕜` to `AddCircle p`
gives an identification of `AddCircle p`, as a topological space, with the quotient of `[a, a + p]`
by the equivalence relation identifying the endpoints. -/

namespace AddCircle

variable [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] (p a : 𝕜)
  [hp : Fact (0 < p)]

local notation "𝕋" => AddCircle p

/-- The relation identifying the endpoints of `Icc a (a + p)`. -/
/-
**AddCircle.EndpointIdent** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddCircle`。
形式化陈述：{𝕜 : Type u_1} →   [inst : AddCommGroup 𝕜] →     [inst_1 : LinearOrder 𝕜] 
→       [IsOrderedAddMonoid 𝕜] → (p a : 𝕜) → [hp : Fact (0 < p)] → ↑(Set.Icc a (
a + p)) → ↑(Set.Icc a (a + p)) → Prop
参数：p a : 𝕜；0 < p；Set.Icc a (a + p)；Set.Icc a (a + p)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation identifying the endpoints of `Icc a (a + p)`.
-/
inductive EndpointIdent : Icc a (a + p) → Icc a (a + p) → Prop
  | mk :
    EndpointIdent ⟨a, left_mem_Icc.mpr <| le_add_of_nonneg_right hp.out.le⟩
      ⟨a + p, right_mem_Icc.mpr <| le_add_of_nonneg_right hp.out.le⟩

variable [Archimedean 𝕜]

/-- The equivalence between `AddCircle p` and the quotient of `[a, a + p]` by the relation
identifying the endpoints. -/
/-
**AddCircle.equivIccQuot** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：equivIccQuot : 𝕋 ≃ Quot (EndpointIdent p a) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `AddCircle p` and the quotient of `[a, a + p]` by the re
lation
identifying the endpoints.
-/
def equivIccQuot : 𝕋 ≃ Quot (EndpointIdent p a) where
  toFun x := Quot.mk _ <| inclusion Ico_subset_Icc_self (equivIco _ _ x)
  invFun x :=
    Quot.liftOn x (↑) <| by
      rintro _ _ ⟨_⟩
      exact (coe_add_period p a).symm
  left_inv := (equivIco p a).symm_apply_apply
  right_inv :=
    Quot.ind <| by
      rintro ⟨x, hx⟩
      rcases ne_or_eq x (a + p) with (h | rfl)
      · revert x
        dsimp only
        intro x hx h
        congr
        ext1
        apply congr_arg Subtype.val ((equivIco p a).right_inv ⟨x, hx.1, hx.2.lt_of_ne h⟩)
      · rw [← Quot.sound EndpointIdent.mk]
        dsimp only
        congr
        ext1
        apply congr_arg Subtype.val
          ((equivIco p a).right_inv ⟨a, le_refl a, lt_add_of_pos_right a hp.out⟩)
/-
**AddCircle.equivIccQuot_comp_mk_eq_toIcoMod** 是 Mathlib 中的一个定理，位于命名空间 `AddCircl
e`。
形式化陈述：equivIccQuot_comp_mk_eq_toIcoMod : equivIccQuot p a ∘ Quotient.mk'' = fun 
x => Quot.mk _ ⟨toIcoMod hp.out a x, Ico_subset_Icc_self toIcoMod_mem_Ico _ _ x⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem equivIccQuot_comp_mk_eq_toIcoMod :
    equivIccQuot p a ∘ Quotient.mk'' = fun x =>
      Quot.mk _ ⟨toIcoMod hp.out a x, Ico_subset_Icc_self <| toIcoMod_mem_Ico _ _ x⟩ :=
  rfl
/-
**AddCircle.equivIccQuot_comp_mk_eq_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 `AddCircl
e`。
形式化陈述：equivIccQuot_comp_mk_eq_toIocMod : equivIccQuot p a ∘ Quotient.mk'' = fun 
x => Quot.mk _ ⟨toIocMod hp.out a x, Ioc_subset_Icc_self toIocMod_mem_Ioc _ _ x⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `toIocMod_mem_Ioc`：toIocMod_mem_Ioc (a b : α) : toIocMod hp a b in Set.Io
c a (a + p)
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `toIcoMod_mem_Ico`：toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b in Set.Ic
o a (a + p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.equivIccQuot_comp_mk_eq_toIcoMod`：equivIccQuot_comp_mk_eq_toIc
oMod : equivIccQuot p a ∘ Quotient.mk'' = fun x => Quot.mk _ ⟨toIcoMod hp.out a 
x, Ico_subset_Icc_self toIcoMod_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddCommGroup.modEq_iff_toIcoMod_eq_left`：modEq_iff_toIcoMod_eq_left : a 
≡ b [PMOD p] ↔ toIcoMod hp a b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `AddCommGroup.modEq_iff_toIocMod_eq_right`：modEq_iff_toIocMod_eq_right : 
a ≡ b [PMOD p] ↔ toIocMod hp a b = a + p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod`：not_modEq_iff_toIcoMod_
eq_toIocMod : ¬a ≡ b [PMOD p] ↔ toIcoMod hp a b = toIocMod hp a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivIccQuot_comp_mk_eq_toIocMod :
    equivIccQuot p a ∘ Quotient.mk'' = fun x =>
      Quot.mk _ ⟨toIocMod hp.out a x, Ioc_subset_Icc_self <| toIocMod_mem_Ioc _ _ x⟩ := by
  rw [equivIccQuot_comp_mk_eq_toIcoMod]
  funext x
  by_cases h : a ≡ x [PMOD p]
  · simp_rw [(modEq_iff_toIcoMod_eq_left hp.out).1 h, (modEq_iff_toIocMod_eq_right hp.out).1 h]
    exact Quot.sound EndpointIdent.mk
  · simp_rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp.out).1 h]

/-- The natural map from `[a, a + p] ⊂ 𝕜` with endpoints identified to `𝕜 / ℤ • p`, as a
homeomorphism of topological spaces. -/
/-
**AddCircle.homeoIccQuot** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：homeoIccQuot [TopologicalSpace 𝕜] [OrderTopology 𝕜] : 𝕋 ≃ₜ Quot (EndpointI
dent p a) where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from `[a, a + p] ⊂ 𝕜` with endpoints identified to `𝕜 / ℤ • p`, 
as a
homeomorphism of topological spaces.
-/
def homeoIccQuot [TopologicalSpace 𝕜] [OrderTopology 𝕜] : 𝕋 ≃ₜ Quot (EndpointIdent p a) where
  toEquiv := equivIccQuot p a
  continuous_toFun := by
    simp_rw [isQuotientMap_quotient_mk'.continuous_iff, continuous_iff_continuousAt,
      continuousAt_iff_continuous_left_right]
    intro x; constructor
    on_goal 1 => erw [equivIccQuot_comp_mk_eq_toIocMod]
    on_goal 2 => erw [equivIccQuot_comp_mk_eq_toIcoMod]
    all_goals
      apply continuous_quot_mk.continuousAt.comp_continuousWithinAt
      rw [IsInducing.subtypeVal.continuousWithinAt_iff]
    · apply continuousWithinAt_toIocMod_Iic
    · apply continuousWithinAt_toIcoMod_Ici
  continuous_invFun :=
    continuous_quot_lift _ ((AddCircle.continuous_mk' p).comp continuous_subtype_val)

/-! We now show that a continuous function on `[a, a + p]` satisfying `f a = f (a + p)` is the
pullback of a continuous function on `AddCircle p`, by first showing that
various lifts are equivalent. -/


variable {p a}

/-
**AddCircle.liftIoc_eq_liftIco** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIoc_eq_liftIco {f : 𝕜 -> B} (hf : f a = f (a + p)) : liftIoc p a f = l
iftIco p a f
参数：hf : f a = f (a + p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCircle.coe_image_Ico_eq`：coe_image_Ico_eq : ((↑) : 𝕜 -> AddCircle p) 
'' Ico a (a + p) = univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.liftIco_coe_apply`：liftIco_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx 
: x in Ico a (a + p)) : liftIco p a f ↑x = f x
· 使用定理 `or_and_right`：∀ {a b c : Prop}, (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `Set.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
co a b ↔ a ≤ x ∧ x < b
· 使用定理 `AddCircle.coe_add_period`：coe_add_period (x : 𝕜) : ((x + p : 𝕜) : AddCir
cle p) = x
· 使用定理 `AddCircle.liftIoc_coe_apply`：liftIoc_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx 
: x in Ioc a (a + p)) : liftIoc p a f ↑x = f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem liftIoc_eq_liftIco {f : 𝕜 → B} (hf : f a = f (a + p)) :
    liftIoc p a f = liftIco p a f := by
  ext q
  obtain ⟨x, hx, rfl⟩ := by simpa only [mem_image] using coe_image_Ico_eq p a ▸ mem_univ q
  rw [liftIco_coe_apply hx]
  obtain (⟨rfl, -⟩ | h) := by rwa [mem_Ico, le_iff_eq_or_lt, or_and_right] at hx
  · rw [← coe_add_period, liftIoc_coe_apply (by simp [hp.out]), hf]
  · exact liftIoc_coe_apply ⟨h.1, h.2.le⟩
/-
**AddCircle.liftIco_eq_lift_Icc** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIco_eq_lift_Icc {f : 𝕜 -> B} (h : f a = f (a + p)) : liftIco p a f = Q
uot.lift (domRestrict (Icc a <| a + p) f) (by rintro _ _ ⟨_⟩ exact h) ∘ equivIcc
Quot p a
参数：h : f a = f (a + p)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftIco_eq_lift_Icc {f : 𝕜 → B} (h : f a = f (a + p)) :
    liftIco p a f =
      Quot.lift (domRestrict (Icc a <| a + p) f)
          (by
            rintro _ _ ⟨_⟩
            exact h) ∘
        equivIccQuot p a :=
  rfl
/-
**AddCircle.liftIoc_eq_lift_Icc** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIoc_eq_lift_Icc {f : 𝕜 -> B} (h : f a = f (a + p)) : liftIoc p a f = Q
uot.lift (domRestrict (Icc a <| a + p) f) (by rintro _ _ ⟨_⟩ exact h) ∘ equivIcc
Quot p a
参数：h : f a = f (a + p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCircle.liftIco_eq_lift_Icc`：liftIco_eq_lift_Icc {f : 𝕜 -> B} (h : f a
 = f (a + p)) : liftIco p a f = Quot.lift (domRestrict (Icc a <| a + p) f) (by r
intro _ _ ⟨_⟩ exact…
· 使用定理 `AddCircle.liftIoc_eq_liftIco`：liftIoc_eq_liftIco {f : 𝕜 -> B} (hf : f a 
= f (a + p)) : liftIoc p a f = liftIco p a f
-/
theorem liftIoc_eq_lift_Icc {f : 𝕜 → B} (h : f a = f (a + p)) :
    liftIoc p a f =
      Quot.lift (domRestrict (Icc a <| a + p) f)
          (by
            rintro _ _ ⟨_⟩
            exact h) ∘
        equivIccQuot p a := by
  rw [← liftIco_eq_lift_Icc h]
  exact liftIoc_eq_liftIco h
/-
**AddCircle.liftIco_zero_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIco_zero_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ico 0 p) : liftIco 
p 0 f ↑x = f x
参数：hx : x in Ico 0 p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.liftIco_coe_apply`：liftIco_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx 
: x in Ico a (a + p)) : liftIco p a f ↑x = f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem liftIco_zero_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico 0 p) : liftIco p 0 f ↑x = f x :=
  liftIco_coe_apply (by rwa [zero_add])
/-
**AddCircle.liftIoc_zero_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIoc_zero_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ioc 0 p) : liftIoc 
p 0 f ↑x = f x
参数：hx : x in Ioc 0 p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.liftIoc_coe_apply`：liftIoc_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx 
: x in Ioc a (a + p)) : liftIoc p a f ↑x = f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem liftIoc_zero_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ioc 0 p) : liftIoc p 0 f ↑x = f x :=
  liftIoc_coe_apply (by rwa [zero_add])

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
/-
**AddCircle.liftIco_continuous** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIco_continuous [TopologicalSpace B] {f : 𝕜 -> B} (hf : f a = f (a + p)
) (hc : ContinuousOn f <| Icc a (a + p)) : Continuous (liftIco p a f)
参数：hf : f a = f (a + p)；hc : ContinuousOn f <| Icc a (a + p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.liftIco_eq_lift_Icc`：liftIco_eq_lift_Icc {f : 𝕜 -> B} (h : f a
 = f (a + p)) : liftIco p a f = Quot.lift (domRestrict (Icc a <| a + p) f) (by r
intro _ _ ⟨_⟩ exact…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Homeomorph.continuous_toFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous sel
f.toFun
-/
theorem liftIco_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f a = f (a + p))
    (hc : ContinuousOn f <| Icc a (a + p)) : Continuous (liftIco p a f) := by
  rw [liftIco_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_domRestrict.mp hc)
/-
**AddCircle.liftIco_zero_continuous** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIco_zero_continuous [TopologicalSpace B] {f : 𝕜 -> B} (hf : f 0 = f p)
 (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIco p 0 f)
参数：hf : f 0 = f p；hc : ContinuousOn f <| Icc 0 p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.liftIco_continuous`：liftIco_continuous [TopologicalSpace B] {f
 : 𝕜 -> B} (hf : f a = f (a + p)) (hc : ContinuousOn f <| Icc a (a + p)) : Conti
nuous (liftIco p a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem liftIco_zero_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f 0 = f p)
    (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIco p 0 f) :=
  liftIco_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])
/-
**AddCircle.liftIoc_continuous** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIoc_continuous [TopologicalSpace B] {f : 𝕜 -> B} (hf : f a = f (a + p)
) (hc : ContinuousOn f <| Icc a (a + p)) : Continuous (liftIoc p a f)
参数：hf : f a = f (a + p)；hc : ContinuousOn f <| Icc a (a + p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.liftIoc_eq_lift_Icc`：liftIoc_eq_lift_Icc {f : 𝕜 -> B} (h : f a
 = f (a + p)) : liftIoc p a f = Quot.lift (domRestrict (Icc a <| a + p) f) (by r
intro _ _ ⟨_⟩ exact…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Homeomorph.continuous_toFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous sel
f.toFun
-/
theorem liftIoc_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f a = f (a + p))
    (hc : ContinuousOn f <| Icc a (a + p)) : Continuous (liftIoc p a f) := by
  rw [liftIoc_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_domRestrict.mp hc)
/-
**AddCircle.liftIoc_zero_continuous** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：liftIoc_zero_continuous [TopologicalSpace B] {f : 𝕜 -> B} (hf : f 0 = f p)
 (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIoc p 0 f)
参数：hf : f 0 = f p；hc : ContinuousOn f <| Icc 0 p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.liftIoc_continuous`：liftIoc_continuous [TopologicalSpace B] {f
 : 𝕜 -> B} (hf : f a = f (a + p)) (hc : ContinuousOn f <| Icc a (a + p)) : Conti
nuous (liftIoc p a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem liftIoc_zero_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f 0 = f p)
    (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIoc p 0 f) :=
  liftIoc_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

end AddCircle

end IdentifyIccEnds

