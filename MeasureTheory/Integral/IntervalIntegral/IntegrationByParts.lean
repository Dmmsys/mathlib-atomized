/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integration by parts and by substitution

We derive additional integration techniques from FTC-2:
* `intervalIntegral.integral_mul_deriv_eq_deriv_mul` - integration by parts
* `intervalIntegral.integral_comp_mul_deriv''` - integration by substitution

Versions of the change of variables formula for monotone and antitone functions, but with much
weaker assumptions on the integrands and not restricted to intervals,
can be found in `Mathlib/MeasureTheory/Function/JacobianOneDim.lean`

## Tags

integration by parts, change of variables in integrals
-/

public section

open MeasureTheory Set

open scoped Topology Interval

namespace intervalIntegral

variable {a b : ℝ}

section Parts

section Mul

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {u v u' v' : ℝ → A}

/-- The integral of the derivative of a product of two maps.
For improper integrals, see `MeasureTheory.integral_deriv_mul_eq_sub`,
`MeasureTheory.integral_Ioi_deriv_mul_eq_sub`, and `MeasureTheory.integral_Iic_deriv_mul_eq_sub`. -/
/-
**intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right** 是 Mathlib 中的一个定
理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_deriv_mul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]])
 (hv : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a b) (max a b), Has
DerivWithinAt u (u' x) (Ioi x) x) (hvv' : forall x in Ioo (min a b) (max a b), H
asDerivWithinAt v (v' x) (Ioi x) x) (hu' : IntervalIntegrable u' volume a b) (hv
' : IntervalIntegrable v' volume a b) : ∫ x in a..b, u' x * v x + u x * v' x = u
 b * v b - u a * v a
参数：hu : ContinuousOn u [[a, b]]；hv : ContinuousOn v [[a, b]]；huu' : forall x in 
Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x；hvv' : forall x in 
Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x；hu' : IntervalInteg
rable u' volume a b；hv' : IntervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDeriv_right`：integral_eq_sub_of_h
asDeriv_right (hcont : ContinuousOn f (uIcc a b)) (hderiv : forall x in Ioo (min
 a b) (max a b), HasDerivWithinAt f (f' …
· 使用定理 `ContinuousOn.mul`：ContinuousOn.mul (hf : ContinuousOn f s) (hg : Continu
ousOn g s) : ContinuousOn (f * g) s
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasDerivWithinAt.mul`：HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s
 x) (hd : HasDerivWithinAt d d' s x) : HasDerivWithinAt (c * d) (c' * d x + c x 
* d') s x
· 使用定理 `IntervalIntegrable.add`：add [ContinuousAdd ε] (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x + g
 x) μ a b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IntervalIntegrable.mul_continuousOn`：mul_continuousOn {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => f x * g x…
· 使用定理 `IntervalIntegrable.continuousOn_mul`：continuousOn_mul {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => g x * f x…

--- 原说明 ---
The integral of the derivative of a product of two maps.
For improper integrals, see `MeasureTheory.integral_deriv_mul_eq_sub`,
`MeasureTheory.integral_Ioi_deriv_mul_eq_sub`, and `MeasureTheory.integral_Iic_d
eriv_mul_eq_sub`.
-/
theorem integral_deriv_mul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a := by
  apply integral_eq_sub_of_hasDeriv_right (hu.mul hv) fun x hx ↦ (huu' x hx).mul (hvv' x hx)
  exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)

/-- The integral of the derivative of a product of two maps.
Special case of `integral_deriv_mul_eq_sub_of_hasDeriv_right` where the functions have a
two-sided derivative in the interior of the interval. -/
/-
**intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：integral_deriv_mul_eq_sub_of_hasDerivAt (hu : ContinuousOn u [[a, b]]) (hv
 : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a b) (max a b), HasDeri
vAt u (u' x) x) (hvv' : forall x in Ioo (min a b) (max a b), HasDerivAt v (v' x)
 x) (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume
 a b) : ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a
参数：hu : ContinuousOn u [[a, b]]；hv : ContinuousOn v [[a, b]]；huu' : forall x in 
Ioo (min a b) (max a b), HasDerivAt u (u' x) x；hvv' : forall x in Ioo (min a b) 
(max a b), HasDerivAt v (v' x) x；hu' : IntervalIntegrable u' volume a b；hv' : In
tervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right`：integral_d
eriv_mul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]]) (hv : Continuou
sOn v [[a, b]]) (huu' : forall x in Ioo (min a b) …
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
The integral of the derivative of a product of two maps.
Special case of `integral_deriv_mul_eq_sub_of_hasDeriv_right` where the function
s have a
two-sided derivative in the interior of the interval.
-/
theorem integral_deriv_mul_eq_sub_of_hasDerivAt (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]]) (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv
    (fun x hx ↦ huu' x hx |>.hasDerivWithinAt) (fun x hx ↦ hvv' x hx |>.hasDerivWithinAt) hu' hv'

/-- The integral of the derivative of a product of two maps.
Special case of `integral_deriv_mul_eq_sub_of_hasDeriv_right` where the functions have a
  one-sided derivative at the endpoints. -/
/-
**intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt** 是 Mathlib 中的一
个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_deriv_mul_eq_sub_of_hasDerivWithinAt (hu : forall x in [[a, b]], 
HasDerivWithinAt u (u' x) [[a, b]] x) (hv : forall x in [[a, b]], HasDerivWithin
At v (v' x) [[a, b]] x) (hu' : IntervalIntegrable u' volume a b) (hv' : Interval
Integrable v' volume a b) : ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u
 a * v a
参数：hu : forall x in [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x；hv : forall x
 in [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x；hu' : IntervalIntegrable u' v
olume a b；hv' : IntervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt`：integral_deriv
_mul_eq_sub_of_hasDerivAt (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[
a, b]]) (huu' : forall x in Ioo (min a b) (max…
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `Set.mem_Icc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo a b → x ∈ Set.Icc a b
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The integral of the derivative of a product of two maps.
Special case of `integral_deriv_mul_eq_sub_of_hasDeriv_right` where the function
s have a
  one-sided derivative at the endpoints.
-/
theorem integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDerivAt
    (fun x hx ↦ (hu x hx).continuousWithinAt)
    (fun x hx ↦ (hv x hx).continuousWithinAt)
    (fun x hx ↦ hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx ↦ hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/-- Special case of `integral_deriv_mul_eq_sub_of_hasDeriv_right` where the functions have a
  derivative at the endpoints. -/
/-
**intervalIntegral.integral_deriv_mul_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `interval
Integral`。
形式化陈述：integral_deriv_mul_eq_sub (hu : forall x in [[a, b]], HasDerivAt u (u' x) 
x) (hv : forall x in [[a, b]], HasDerivAt v (v' x) x) (hu' : IntervalIntegrable 
u' volume a b) (hv' : IntervalIntegrable v' volume a b) : ∫ x in a..b, u' x * v 
x + u x * v' x = u b * v b - u a * v a
参数：hu : forall x in [[a, b]], HasDerivAt u (u' x) x；hv : forall x in [[a, b]], H
asDerivAt v (v' x) x；hu' : IntervalIntegrable u' volume a b；hv' : IntervalIntegr
able v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt`：integral
_deriv_mul_eq_sub_of_hasDerivWithinAt (hu : forall x in [[a, b]], HasDerivWithin
At u (u' x) [[a, b]] x) (hv : forall x in [[a, b]], …
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
Special case of `integral_deriv_mul_eq_sub_of_hasDeriv_right` where the function
s have a
  derivative at the endpoints.
-/
theorem integral_deriv_mul_eq_sub
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (fun x hx ↦ hu x hx |>.hasDerivWithinAt) (fun x hx ↦ hv x hx |>.hasDerivWithinAt) hu' hv'

/-- **Integration by parts**. For improper integrals, see
`MeasureTheory.integral_mul_deriv_eq_deriv_mul`,
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`,
and `MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul`. -/
/-
**intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right** 是 Mathlib
 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right (hu : ContinuousOn u [[a
, b]]) (hv : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a b) (max a b
), HasDerivWithinAt u (u' x) (Ioi x) x) (hvv' : forall x in Ioo (min a b) (max a
 b), HasDerivWithinAt v (v' x) (Ioi x) x) (hu' : IntervalIntegrable u' volume a 
b) (hv' : IntervalIntegrable v' volume a b) : ∫ x in a..b, u x * v' x = u b * v 
b - u a * v a - ∫ x in a..b, u' x * v x
参数：hu : ContinuousOn u [[a, b]]；hv : ContinuousOn v [[a, b]]；huu' : forall x in 
Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x；hvv' : forall x in 
Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x；hu' : IntervalInteg
rable u' volume a b；hv' : IntervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right`：integral_d
eriv_mul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]]) (hv : Continuou
sOn v [[a, b]]) (huu' : forall x in Ioo (min a b) …
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用定理 `IntervalIntegrable.add`：add [ContinuousAdd ε] (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x + g
 x) μ a b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IntervalIntegrable.mul_continuousOn`：mul_continuousOn {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => f x * g x…
· 使用定理 `IntervalIntegrable.continuousOn_mul`：continuousOn_mul {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => g x * f x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Integration by parts**. For improper integrals, see
`MeasureTheory.integral_mul_deriv_eq_deriv_mul`,
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`,
and `MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul`.
-/
theorem integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  rw [← integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv', ← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)
  · exact hu'.mul_continuousOn hv

/-- **Integration by parts**. Special case of `integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
where the functions have a two-sided derivative in the interior of the interval. -/
/-
**intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt** 是 Mathlib 中的一
个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (hu : ContinuousOn u [[a, b]
]) (hv : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a b) (max a b), H
asDerivAt u (u' x) x) (hvv' : forall x in Ioo (min a b) (max a b), HasDerivAt v 
(v' x) x) (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' 
volume a b) : ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' 
x * v x
参数：hu : ContinuousOn u [[a, b]]；hv : ContinuousOn v [[a, b]]；huu' : forall x in 
Ioo (min a b) (max a b), HasDerivAt u (u' x) x；hvv' : forall x in Ioo (min a b) 
(max a b), HasDerivAt v (v' x) x；hu' : IntervalIntegrable u' volume a b；hv' : In
tervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`：inte
gral_mul_deriv_eq_deriv_mul_of_hasDeriv_right (hu : ContinuousOn u [[a, b]]) (hv
 : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (min…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
**Integration by parts**. Special case of `integral_mul_deriv_eq_deriv_mul_of_ha
sDeriv_right`
where the functions have a two-sided derivative in the interior of the interval.
-/
theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hu hv
        (fun x hx ↦ (huu' x hx).hasDerivWithinAt) (fun x hx ↦ (hvv' x hx).hasDerivWithinAt) hu' hv'

/-- **Integration by parts**. Special case of
`intervalIntegrable.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
where the functions have a one-sided derivative at the endpoints. -/
/-
**intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt** 是 Mathl
ib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt (hu : forall x in [[a,
 b]], HasDerivWithinAt u (u' x) [[a, b]] x) (hv : forall x in [[a, b]], HasDeriv
WithinAt v (v' x) [[a, b]] x) (hu' : IntervalIntegrable u' volume a b) (hv' : In
tervalIntegrable v' volume a b) : ∫ x in a..b, u x * v' x = u b * v b - u a * v 
a - ∫ x in a..b, u' x * v x
参数：hu : forall x in [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x；hv : forall x
 in [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x；hu' : IntervalIntegrable u' v
olume a b；hv' : IntervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`：integral
_mul_deriv_eq_deriv_mul_of_hasDerivAt (hu : ContinuousOn u [[a, b]]) (hv : Conti
nuousOn v [[a, b]]) (huu' : forall x in Ioo (min a b…
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `Set.mem_Icc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo a b → x ∈ Set.Icc a b
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Integration by parts**. Special case of
`intervalIntegrable.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
where the functions have a one-sided derivative at the endpoints.
-/
theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (fun x hx ↦ (hu x hx).continuousWithinAt)
    (fun x hx ↦ (hv x hx).continuousWithinAt)
    (fun x hx ↦ hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx ↦ hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/-- **Integration by parts**. Special case of
`intervalIntegrable.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
where the functions have a derivative also at the endpoints.
For improper integrals, see
`MeasureTheory.integral_mul_deriv_eq_deriv_mul`,
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`,
and `MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul`. -/
/-
**intervalIntegral.integral_mul_deriv_eq_deriv_mul** 是 Mathlib 中的一个定理，位于命名空间 `in
tervalIntegral`。
形式化陈述：integral_mul_deriv_eq_deriv_mul (hu : forall x in [[a, b]], HasDerivAt u (
u' x) x) (hv : forall x in [[a, b]], HasDerivAt v (v' x) x) (hu' : IntervalInteg
rable u' volume a b) (hv' : IntervalIntegrable v' volume a b) : ∫ x in a..b, u x
 * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x
参数：hu : forall x in [[a, b]], HasDerivAt u (u' x) x；hv : forall x in [[a, b]], H
asDerivAt v (v' x) x；hu' : IntervalIntegrable u' volume a b；hv' : IntervalIntegr
able v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt`：in
tegral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt (hu : forall x in [[a, b]], Ha
sDerivWithinAt u (u' x) [[a, b]] x) (hv : forall x in [[a,…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
**Integration by parts**. Special case of
`intervalIntegrable.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
where the functions have a derivative also at the endpoints.
For improper integrals, see
`MeasureTheory.integral_mul_deriv_eq_deriv_mul`,
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`,
and `MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul`.
-/
theorem integral_mul_deriv_eq_deriv_mul
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (fun x hx ↦ (hu x hx).hasDerivWithinAt) (fun x hx ↦ (hv x hx).hasDerivWithinAt) hu' hv'

end Mul

section SMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
variable [IsScalarTower ℝ 𝕜 E]

variable {u u' : ℝ → 𝕜}
variable {v v' : ℝ → E}

/-- The integral of the derivative of a scalar multiplication. -/
/-
**intervalIntegral.integral_deriv_smul_eq_sub_of_hasDeriv_right** 是 Mathlib 中的一个
定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_deriv_smul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]]
) (hv : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a b) (max a b), Ha
sDerivWithinAt u (u' x) (Ioi x) x) (hvv' : forall x in Ioo (min a b) (max a b), 
HasDerivWithinAt v (v' x) (Ioi x) x) (hu' : IntervalIntegrable u' volume a b) (h
v' : IntervalIntegrable v' volume a b) : ∫ x in a..b, u' x • v x + u x • v' x = 
u b • v b - u a • v a
参数：hu : ContinuousOn u [[a, b]]；hv : ContinuousOn v [[a, b]]；huu' : forall x in 
Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x；hvv' : forall x in 
Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x；hu' : IntervalInteg
rable u' volume a b；hv' : IntervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDeriv_right`：integral_eq_sub_of_h
asDeriv_right (hcont : ContinuousOn f (uIcc a b)) (hderiv : forall x in Ioo (min
 a b) (max a b), HasDerivWithinAt f (f' …
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `HasDerivWithinAt.smul`：HasDerivWithinAt.smul (hc : HasDerivWithinAt c c'
 s x) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (c • f) (c x • f' + c'
 • f x) s x
· 使用定理 `IntervalIntegrable.add`：add [ContinuousAdd ε] (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x + g
 x) μ a b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IntervalIntegrable.continuousOn_smul`：continuousOn_smul (hg : IntervalIn
tegrable g μ a b) (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 
f x • g x) μ a b
· 使用定理 `IntervalIntegrable.smul_continuousOn`：smul_continuousOn (hf : IntervalIn
tegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => 
f x • g x) μ a b

--- 原说明 ---
The integral of the derivative of a scalar multiplication.
-/
theorem integral_deriv_smul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x • v x + u x • v' x = u b • v b - u a • v a := by
  simp_rw [add_comm]
  apply integral_eq_sub_of_hasDeriv_right (hu.smul hv) fun x hx ↦ (huu' x hx).smul (hvv' x hx)
  exact (hv'.continuousOn_smul hu).add (hu'.smul_continuousOn hv)

/-- **Integration by parts** (vector-valued). -/
/-
**intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right** 是 Mathl
ib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right (hu : ContinuousOn u [
[a, b]]) (hv : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a b) (max a
 b), HasDerivWithinAt u (u' x) (Ioi x) x) (hvv' : forall x in Ioo (min a b) (max
 a b), HasDerivWithinAt v (v' x) (Ioi x) x) (hu' : IntervalIntegrable u' volume 
a b) (hv' : IntervalIntegrable v' volume a b) : ∫ x in a..b, u x • v' x = u b • 
v b - u a • v a - ∫ x in a..b, u' x • v x
参数：hu : ContinuousOn u [[a, b]]；hv : ContinuousOn v [[a, b]]；huu' : forall x in 
Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x；hvv' : forall x in 
Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x；hu' : IntervalInteg
rable u' volume a b；hv' : IntervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_deriv_smul_eq_sub_of_hasDeriv_right`：integral_
deriv_smul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]]) (hv : Continu
ousOn v [[a, b]]) (huu' : forall x in Ioo (min a b)…
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用定理 `IntervalIntegrable.add`：add [ContinuousAdd ε] (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x + g
 x) μ a b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IntervalIntegrable.smul_continuousOn`：smul_continuousOn (hf : IntervalIn
tegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => 
f x • g x) μ a b
· 使用定理 `IntervalIntegrable.continuousOn_smul`：continuousOn_smul (hg : IntervalIn
tegrable g μ a b) (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 
f x • g x) μ a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Integration by parts** (vector-valued).
-/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x := by
  rw [← integral_deriv_smul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv', ← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.smul_continuousOn hv).add (hv'.continuousOn_smul hu)
  · exact hu'.smul_continuousOn hv

/-- **Integration by parts** (vector-valued).
Special case of `integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a two-sided derivative in the interior of the interval. -/
/-
**intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt** 是 Mathlib 中
的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_smul_deriv_eq_deriv_smul_of_hasDerivAt (hu : ContinuousOn u [[a, 
b]]) (hv : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a b) (max a b),
 HasDerivAt u (u' x) x) (hvv' : forall x in Ioo (min a b) (max a b), HasDerivAt 
v (v' x) x) (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v
' volume a b) : ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u
' x • v x
参数：hu : ContinuousOn u [[a, b]]；hv : ContinuousOn v [[a, b]]；huu' : forall x in 
Ioo (min a b) (max a b), HasDerivAt u (u' x) x；hvv' : forall x in Ioo (min a b) 
(max a b), HasDerivAt v (v' x) x；hu' : IntervalIntegrable u' volume a b；hv' : In
tervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`：in
tegral_smul_deriv_eq_deriv_smul_of_hasDeriv_right (hu : ContinuousOn u [[a, b]])
 (hv : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (m…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
**Integration by parts** (vector-valued).
Special case of `integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a two-sided derivative in the interior of the interval.
-/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right hu hv
        (fun x hx ↦ (huu' x hx).hasDerivWithinAt) (fun x hx ↦ (hvv' x hx).hasDerivWithinAt) hu' hv'

/-- **Integration by parts** (vector-valued). Special case of
`intervalIntegrable.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a one-sided derivative at the endpoints. -/
/-
**intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt** 是 Mat
hlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt (hu : forall x in [[
a, b]], HasDerivWithinAt u (u' x) [[a, b]] x) (hv : forall x in [[a, b]], HasDer
ivWithinAt v (v' x) [[a, b]] x) (hu' : IntervalIntegrable u' volume a b) (hv' : 
IntervalIntegrable v' volume a b) : ∫ x in a..b, u x • v' x = u b • v b - u a • 
v a - ∫ x in a..b, u' x • v x
参数：hu : forall x in [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x；hv : forall x
 in [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x；hu' : IntervalIntegrable u' v
olume a b；hv' : IntervalIntegrable v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt`：integr
al_smul_deriv_eq_deriv_smul_of_hasDerivAt (hu : ContinuousOn u [[a, b]]) (hv : C
ontinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a…
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `Set.mem_Icc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo a b → x ∈ Set.Icc a b
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Integration by parts** (vector-valued). Special case of
`intervalIntegrable.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a one-sided derivative at the endpoints.
-/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (fun x hx ↦ (hu x hx).continuousWithinAt)
    (fun x hx ↦ (hv x hx).continuousWithinAt)
    (fun x hx ↦ hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx ↦ hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/-- **Integration by parts** (vector-valued). Special case of
`intervalIntegrable.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a derivative also at the endpoints. -/
/-
**intervalIntegral.integral_smul_deriv_eq_deriv_smul** 是 Mathlib 中的一个定理，位于命名空间 `
intervalIntegral`。
形式化陈述：integral_smul_deriv_eq_deriv_smul (hu : forall x in [[a, b]], HasDerivAt u
 (u' x) x) (hv : forall x in [[a, b]], HasDerivAt v (v' x) x) (hu' : IntervalInt
egrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) : ∫ x in a..b, u
 x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x
参数：hu : forall x in [[a, b]], HasDerivAt u (u' x) x；hv : forall x in [[a, b]], H
asDerivAt v (v' x) x；hu' : IntervalIntegrable u' volume a b；hv' : IntervalIntegr
able v' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt`：
integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt (hu : forall x in [[a, b]]
, HasDerivWithinAt u (u' x) [[a, b]] x) (hv : forall x in [[…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
**Integration by parts** (vector-valued). Special case of
`intervalIntegrable.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a derivative also at the endpoints.
-/
theorem integral_smul_deriv_eq_deriv_smul
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (fun x hx ↦ (hu x hx).hasDerivWithinAt) (fun x hx ↦ (hv x hx).hasDerivWithinAt) hu' hv'

end SMul

end Parts

/-!
### Integration by substitution / Change of variables
-/

section SMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → ℝ} {g g' : ℝ → E}

/-- Change of variables, general form. If `f` is continuous on `[a, b]` and has
right-derivative `f'` in `(a, b)`, `g` is continuous on `f '' (a, b)` and integrable on
`f '' [a, b]`, and `f' x • (g ∘ f) x` is integrable on `[a, b]`,
then we can substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.

If the function `f` is monotone or antitone, see also `integral_deriv_smul_comp_of_deriv_nonneg`
and `integral_deriv_smul_comp_of_deriv_nonpos` dropping all assumptions on `g`. -/
/-
**intervalIntegral.integral_deriv_smul_comp'''** 是 Mathlib 中的一个定理，位于命名空间 `interv
alIntegral`。
形式化陈述：integral_deriv_smul_comp''' (hf : ContinuousOn f [[a, b]]) (hff' : forall 
x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x) (hg_cont : Co
ntinuousOn g (f '' Ioo (min a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]
])) (hg2 : IntegrableOn (fun x => f' x • (g ∘ f) x) [[a, b]]) : (∫ x in a..b, f'
 x • (g ∘ f) x) = ∫ u in f a..f b, g u
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivWithinAt f (f' x) (Ioi x) x；hg_cont : ContinuousOn g (f '' Ioo (min a b) (ma
x a b))；hg1 : IntegrableOn g (f '' [[a, b]])；hg2 : IntegrableOn (fun x => f' x •
 (g ∘ f) x) [[a, b]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `intervalIntegral.continuousOn_primitive_interval'`：continuousOn_primitiv
e_interval' (h_int : IntervalIntegrable f μ b₁ b₂) (ha : a in [[b₁, b₂]]) : Cont
inuousOn (fun b => ∫ x in a..b, f x ∂μ)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegrable_iff'`：intervalIntegrable_iff' [NullSingletonClass μ] 
(h : ‖f (min a b)‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `ContinuousOn.image_uIcc`：image_uIcc (h : ContinuousOn f <| [[a, b]]) : f
 '' [[a, b]] = [[sInf (f '' [[a, b]]), sSup (f '' [[a, b]])]]
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Set.Icc_subset_Ioo`：Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a
₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
Change of variables, general form. If `f` is continuous on `[a, b]` and has
right-derivative `f'` in `(a, b)`, `g` is continuous on `f '' (a, b)` and integr
able on
`f '' [a, b]`, and `f' x • (g ∘ f) x` is integrable on `[a, b]`,
then we can substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in 
f a..f b, g u`.

If the function `f` is monotone or antitone, see also `integral_deriv_smul_comp_
of_deriv_nonneg`
and `integral_deriv_smul_comp_of_deriv_nonpos` dropping all assumptions on `g`.
-/
theorem integral_deriv_smul_comp''' (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g (f '' Ioo (min a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]]))
    (hg2 : IntegrableOn (fun x ↦ f' x • (g ∘ f) x) [[a, b]]) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE]
  rw [hf.image_uIcc, ← intervalIntegrable_iff'] at hg1
  have h_cont : ContinuousOn (fun u ↦ ∫ t in f a..f u, g t) [[a, b]] := by
    refine (continuousOn_primitive_interval' hg1 ?_).comp hf ?_
    · rw [← hf.image_uIcc]; exact mem_image_of_mem f left_mem_uIcc
    · rw [← hf.image_uIcc]; exact mapsTo_image _ _
  have h_der :
    ∀ x ∈ Ioo (min a b) (max a b),
      HasDerivWithinAt (fun u ↦ ∫ t in f a..f u, g t) (f' x • (g ∘ f) x) (Ioi x) x := by
    intro x hx
    obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hx.1
    obtain ⟨d, hd⟩ := nonempty_Ioo.mpr hx.2
    have cdsub : [[c, d]] ⊆ Ioo (min a b) (max a b) := by
      rw [uIcc_of_le (hc.2.trans hd.1).le]
      exact Icc_subset_Ioo hc.1 hd.2
    replace hg_cont := hg_cont.mono (image_mono cdsub)
    let J := [[sInf (f '' [[c, d]]), sSup (f '' [[c, d]])]]
    have hJ : f '' [[c, d]] = J := (hf.mono (cdsub.trans Ioo_subset_Icc_self)).image_uIcc
    rw [hJ] at hg_cont
    have h2x : f x ∈ J := by rw [← hJ]; exact mem_image_of_mem _ (mem_uIcc_of_le hc.2.le hd.1.le)
    have h2g : IntervalIntegrable g volume (f a) (f x) := by
      refine hg1.mono_set ?_
      rw [← hf.image_uIcc]
      exact hf.surjOn_uIcc left_mem_uIcc (Ioo_subset_Icc_self hx)
    have h3g : StronglyMeasurableAtFilter g (𝓝[J] f x) :=
      hg_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc (f x)
    have : Fact (f x ∈ J) := ⟨h2x⟩
    have : HasDerivWithinAt (fun u ↦ ∫ x in f a..u, g x) (g (f x)) J (f x) :=
      intervalIntegral.integral_hasDerivWithinAt_right h2g h3g (hg_cont (f x) h2x)
    refine (this.scomp x ((hff' x hx).Ioo_of_Ioi hd.1) ?_).Ioi_of_Ioo hd.1
    rw [← hJ]
    refine (mapsTo_image _ _).mono ?_ Subset.rfl
    exact Ioo_subset_Icc_self.trans ((Icc_subset_Icc_left hc.2.le).trans Icc_subset_uIcc)
  rw [← intervalIntegrable_iff'] at hg2
  simp_rw [integral_eq_sub_of_hasDeriv_right h_cont h_der hg2, integral_same, sub_zero]

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv''' := integral_deriv_smul_comp'''

/-- Change of variables for continuous integrands. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.

If the function `f` is monotone or antitone, see also `integral_deriv_smul_comp_of_deriv_nonneg`
and `integral_deriv_smul_comp_of_deriv_nonpos` dropping all assumptions on `g`. -/
/-
**intervalIntegral.integral_deriv_smul_comp''** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：integral_deriv_smul_comp'' (hf : ContinuousOn f [[a, b]]) (hff' : forall x
 in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x) (hf' : Continu
ousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) : (∫ x in a..b, f' x • 
(g ∘ f) x) = ∫ u in f a..f b, g u
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivWithinAt f (f' x) (Ioi x) x；hf' : ContinuousOn f' [[a, b]]；hg : ContinuousOn
 g (f '' [[a, b]])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `intervalIntegral.integral_deriv_smul_comp'''`：integral_deriv_smul_comp''
' (hf : ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), Ha
sDerivWithinAt f (f' x) (Ioi x) x)…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.image_uIcc`：image_uIcc (h : ContinuousOn f <| [[a, b]]) : f
 '' [[a, b]] = [[sInf (f '' [[a, b]]), sSup (f '' [[a, b]])]]
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ContinuousOn.integrableOn_Icc`：ContinuousOn.integrableOn_Icc [Preorder X
] [CompactIccSpace X] [T2Space X] (hf : ContinuousOn f (Icc a b)) : IntegrableOn
 f (Icc a b) μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
Change of variables for continuous integrands. If `f` is continuous on `[a, b]` 
and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a,
 b]` then we can
substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g 
u`.

If the function `f` is monotone or antitone, see also `integral_deriv_smul_comp_
of_deriv_nonneg`
and `integral_deriv_smul_comp_of_deriv_nonpos` dropping all assumptions on `g`.
-/
theorem integral_deriv_smul_comp'' (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  refine integral_deriv_smul_comp''' hf hff' (hg.mono <| image_mono Ioo_subset_Icc_self) ?_
    (hf'.smul (hg.comp hf <| subset_preimage_image f _)).integrableOn_Icc
  rw [hf.image_uIcc] at hg ⊢
  exact hg.integrableOn_Icc

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv'' := integral_deriv_smul_comp''

/-- Change of variables. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.
Compared to `intervalIntegral.integral_deriv_smul_comp` we only require that `g` is continuous on
`f '' [a, b]`.

If the function `f` is monotone or antitone, see also `integral_deriv_smul_comp_of_deriv_nonneg`
and `integral_deriv_smul_comp_of_deriv_nonpos` dropping all assumptions on `g`. -/
/-
**intervalIntegral.integral_deriv_smul_comp'** 是 Mathlib 中的一个定理，位于命名空间 `interval
Integral`。
形式化陈述：integral_deriv_smul_comp' (h : forall x in uIcc a b, HasDerivAt f (f' x) x
) (h' : ContinuousOn f' (uIcc a b)) (hg : ContinuousOn g (f '' [[a, b]])) : (∫ x
 in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x
参数：h : forall x in uIcc a b, HasDerivAt f (f' x) x；h' : ContinuousOn f' (uIcc a 
b)；hg : ContinuousOn g (f '' [[a, b]])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `intervalIntegral.integral_deriv_smul_comp''`：integral_deriv_smul_comp'' 
(hf : ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), HasD
erivWithinAt f (f' x) (Ioi x) x) …
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b

--- 原说明 ---
Change of variables. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.
Compared to `intervalIntegral.integral_deriv_smul_comp` we only require that `g`
 is continuous on
`f '' [a, b]`.

If the function `f` is monotone or antitone, see also `integral_deriv_smul_comp_
of_deriv_nonneg`
and `integral_deriv_smul_comp_of_deriv_nonpos` dropping all assumptions on `g`.
-/
theorem integral_deriv_smul_comp' (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_deriv_smul_comp'' (fun x hx ↦ (h x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (h x <| Ioo_subset_Icc_self hx).hasDerivWithinAt) h' hg

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv' := integral_deriv_smul_comp'

/-- Change of variables, most common version. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.

If the function `f` is monotone or antitone, see also `integral_deriv_smul_comp_of_deriv_nonneg`
and `integral_deriv_smul_comp_of_deriv_nonpos` dropping all assumptions on `g`. -/
/-
**intervalIntegral.integral_deriv_smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `intervalI
ntegral`。
形式化陈述：integral_deriv_smul_comp (h : forall x in uIcc a b, HasDerivAt f (f' x) x)
 (h' : ContinuousOn f' (uIcc a b)) (hg : Continuous g) : (∫ x in a..b, f' x • (g
 ∘ f) x) = ∫ x in f a..f b, g x
参数：h : forall x in uIcc a b, HasDerivAt f (f' x) x；h' : ContinuousOn f' (uIcc a 
b)；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `intervalIntegral.integral_deriv_smul_comp'`：integral_deriv_smul_comp' (h
 : forall x in uIcc a b, HasDerivAt f (f' x) x) (h' : ContinuousOn f' (uIcc a b)
) (hg : ContinuousOn g (f '' [[a…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
Change of variables, most common version. If `f` has continuous derivative `f'` 
on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.

If the function `f` is monotone or antitone, see also `integral_deriv_smul_comp_
of_deriv_nonneg`
and `integral_deriv_smul_comp_of_deriv_nonpos` dropping all assumptions on `g`.
-/
theorem integral_deriv_smul_comp (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : Continuous g) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_deriv_smul_comp' h h' hg.continuousOn

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv := integral_deriv_smul_comp

/-- Change of variables for monotone functions.
If `f` is continuous on `[a, b]` and has a nonnegative derivative `f'` in `(a, b)`,
then we can substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`. -/
/-
**intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg** 是 Mathlib 中的一个定理，位
于命名空间 `intervalIntegral`。
形式化陈述：integral_deriv_smul_comp_of_deriv_nonneg (hf : ContinuousOn f [[a, b]]) (h
ff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x) (hf' : forall 
x in Ioo (min a b) (max a b), 0 <= f' x) : (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u
 in f a..f b, g u
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivAt f (f' x) x；hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_uIcc`：convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIcc.eq_1`：∀ {α : Type u_1} [inst : Lattice α] (a b : α), Set.uIcc a
 b = Set.Icc (a ⊓ b) (a ⊔ b)
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_Icc_eq_integral_Ioc`：integral_Icc_eq_integral_Ioc
 : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ
· 使用定理 `MeasureTheory.integral_Icc_deriv_smul_of_deriv_nonneg`：integral_Icc_deri
v_smul_of_deriv_nonneg {a b : Real} {g : Real -> F} (hf : ContinuousOn f (Icc a 
b)) (hff' : forall x in Ioo a b, HasDerivAt…
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
· 使用定理 `Set.right_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, b ∈ S
et.uIcc a b
· 使用定理 `intervalIntegral.integral_of_ge`：integral_of_ge (h : b <= a) : ∫ x in a.
.b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Change of variables for monotone functions.
If `f` is continuous on `[a, b]` and has a nonnegative derivative `f'` in `(a, b
)`,
then we can substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in 
f a..f b, g u`.
-/
theorem integral_deriv_smul_comp_of_deriv_nonneg (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ f' x) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  have M : MonotoneOn f (uIcc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz ↦ (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  simp only [Function.comp_apply]
  rcases le_or_gt a b with hab | hab
  · rw [integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_deriv_smul_of_deriv_nonneg, integral_of_le, ← integral_Icc_eq_integral_Ioc]
    · apply M left_mem_uIcc right_mem_uIcc hab
    · rwa [uIcc_of_le hab] at hf
    · grind
    · grind
    · exact hab
  · rw [integral_of_ge hab.le, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_deriv_smul_of_deriv_nonneg, integral_of_ge, ← integral_Icc_eq_integral_Ioc]
    · apply M right_mem_uIcc left_mem_uIcc hab.le
    · rwa [uIcc_of_ge hab.le] at hf
    · grind
    · grind
    · exact hab.le
/-
**intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg** 是 Mathlib 中的
一个引理，位于命名空间 `intervalIntegral`。
形式化陈述：integrable_deriv_smul_comp_iff_of_deriv_nonneg (hf : ContinuousOn f [[a, b
]]) (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x) (hf' : f
orall x in Ioo (min a b) (max a b), 0 <= f' x) : IntervalIntegrable (fun x => f'
 x • (g ∘ f) x) volume a b ↔ IntervalIntegrable g volume (f a) (f b)
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivAt f (f' x) x；hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_uIcc`：convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIcc.eq_1`：∀ {α : Type u_1} [inst : Lattice α] (a b : α), Set.uIcc a
 b = Set.Icc (a ⊓ b) (a ⊔ b)
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`：intervalIntegrable_iff_in
tegrableOn_Icc_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg`：integrabl
eOn_Icc_deriv_smul_iff_of_deriv_nonneg {a b : Real} {g : Real -> F} (hf : Contin
uousOn f (Icc a b)) (hff' : forall x in Ioo a b, Ha…
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
· 使用定理 `Set.right_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, b ∈ S
et.uIcc a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
（共 33 条，此处仅展示前 30 条）
-/
lemma integrable_deriv_smul_comp_iff_of_deriv_nonneg (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ f' x) :
    IntervalIntegrable (fun x ↦ f' x • (g ∘ f) x) volume a b ↔
      IntervalIntegrable g volume (f a) (f b) := by
  have M : MonotoneOn f (uIcc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz ↦ (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  simp only [Function.comp_apply]
  rcases le_or_gt a b with hab | hab
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab,
      integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg,
      intervalIntegrable_iff_integrableOn_Icc_of_le]
    · apply M left_mem_uIcc right_mem_uIcc hab
    · rwa [uIcc_of_le hab] at hf
    · grind
    · grind
    · exact hab
  · rw [IntervalIntegrable.symm_iff, intervalIntegrable_iff_integrableOn_Icc_of_le hab.le,
      integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg,
      IntervalIntegrable.symm_iff, intervalIntegrable_iff_integrableOn_Icc_of_le]
    · apply M right_mem_uIcc left_mem_uIcc hab.le
    · rwa [uIcc_of_ge hab.le] at hf
    · grind
    · grind
    · exact hab.le

/-- Change of variables for antitone functions.
If `f` is continuous on `[a, b]` and has a nonpositive derivative `f'` in `(a, b)`,
then we can substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`. -/
/-
**intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos** 是 Mathlib 中的一个定理，位
于命名空间 `intervalIntegral`。
形式化陈述：integral_deriv_smul_comp_of_deriv_nonpos (hf : ContinuousOn f [[a, b]]) (h
ff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x) (hf' : forall 
x in Ioo (min a b) (max a b), f' x <= 0) : (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u
 in f a..f b, g u
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivAt f (f' x) x；hf' : forall x in Ioo (min a b) (max a b), f' x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_uIcc`：convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIcc.eq_1`：∀ {α : Type u_1} [inst : Lattice α] (a b : α), Set.uIcc a
 b = Set.Icc (a ⊓ b) (a ⊔ b)
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_Icc_eq_integral_Ioc`：integral_Icc_eq_integral_Ioc
 : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ
· 使用定理 `MeasureTheory.integral_Icc_deriv_smul_of_deriv_nonpos`：integral_Icc_deri
v_smul_of_deriv_nonpos {a b : Real} {g : Real -> F} (hf : ContinuousOn f (Icc a 
b)) (hff' : forall x in Ioo a b, HasDerivAt…
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `intervalIntegral.integral_of_ge`：integral_of_ge (h : b <= a) : ∫ x in a.
.b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Change of variables for antitone functions.
If `f` is continuous on `[a, b]` and has a nonpositive derivative `f'` in `(a, b
)`,
then we can substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in 
f a..f b, g u`.
-/
theorem integral_deriv_smul_comp_of_deriv_nonpos (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo (min a b) (max a b), f' x ≤ 0) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  have M : AntitoneOn f (uIcc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz ↦ (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  simp only [Function.comp_apply]
  rcases le_or_gt a b with hab | hab
  · rw [integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_deriv_smul_of_deriv_nonpos, integral_of_ge, ← integral_Icc_eq_integral_Ioc]
    · apply M left_mem_uIcc right_mem_uIcc hab
    · rwa [uIcc_of_le hab] at hf
    · grind
    · grind
    · exact hab
  · rw [integral_of_ge hab.le, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_deriv_smul_of_deriv_nonpos, integral_of_le, ← integral_Icc_eq_integral_Ioc,
      neg_neg]
    · apply M right_mem_uIcc left_mem_uIcc hab.le
    · rwa [uIcc_of_ge hab.le] at hf
    · grind
    · grind
    · exact hab.le
/-
**intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonpos** 是 Mathlib 中的
一个引理，位于命名空间 `intervalIntegral`。
形式化陈述：integrable_deriv_smul_comp_iff_of_deriv_nonpos (hf : ContinuousOn f [[a, b
]]) (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x) (hf' : f
orall x in Ioo (min a b) (max a b), f' x <= 0) : IntervalIntegrable (fun x => f'
 x • (g ∘ f) x) volume a b ↔ IntervalIntegrable g volume (f a) (f b)
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivAt f (f' x) x；hf' : forall x in Ioo (min a b) (max a b), f' x <= 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_uIcc`：convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIcc.eq_1`：∀ {α : Type u_1} [inst : Lattice α] (a b : α), Set.uIcc a
 b = Set.Icc (a ⊓ b) (a ⊔ b)
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`：intervalIntegrable_iff_in
tegrableOn_Icc_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos`：integrabl
eOn_Icc_deriv_smul_iff_of_deriv_nonpos {a b : Real} {g : Real -> F} (hf : Contin
uousOn f (Icc a b)) (hff' : forall x in Ioo a b, Ha…
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `IntervalIntegrable.symm_iff`：symm_iff : IntervalIntegrable f μ a b ↔ Int
ervalIntegrable f μ b a
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
（共 34 条，此处仅展示前 30 条）
-/
lemma integrable_deriv_smul_comp_iff_of_deriv_nonpos (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo (min a b) (max a b), f' x ≤ 0) :
    IntervalIntegrable (fun x ↦ f' x • (g ∘ f) x) volume a b ↔
      IntervalIntegrable g volume (f a) (f b) := by
  have M : AntitoneOn f (uIcc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz ↦ (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  simp only [Function.comp_apply]
  rcases le_or_gt a b with hab | hab
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab,
      integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos,
      IntervalIntegrable.symm_iff, intervalIntegrable_iff_integrableOn_Icc_of_le]
    · apply M left_mem_uIcc right_mem_uIcc hab
    · rwa [uIcc_of_le hab] at hf
    · grind
    · grind
    · exact hab
  · rw [IntervalIntegrable.symm_iff, intervalIntegrable_iff_integrableOn_Icc_of_le hab.le,
      integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos,
      intervalIntegrable_iff_integrableOn_Icc_of_le]
    · apply M right_mem_uIcc left_mem_uIcc hab.le
    · rwa [uIcc_of_ge hab.le] at hf
    · grind
    · grind
    · exact hab.le

section CompleteSpace

variable [CompleteSpace E]

/-
**intervalIntegral.integral_deriv_smul_deriv_comp'** 是 Mathlib 中的一个定理，位于命名空间 `in
tervalIntegral`。
形式化陈述：integral_deriv_smul_deriv_comp' (hf : ContinuousOn f [[a, b]]) (hff' : for
all x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x) (hf' : Co
ntinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f b]]) (hgg' : forall x in I
oo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithinAt g (g' x) (Ioi x) x) (hg
' : ContinuousOn g' (f '' [[a, b]])) : (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f
) b - (g ∘ f) a
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivWithinAt f (f' x) (Ioi x) x；hf' : ContinuousOn f' [[a, b]]；hg : ContinuousOn
 g [[f a, f b]]；hgg' : forall x in Ioo (min (f a) (f b)) (max (f a) (f b)), HasD
erivWithinAt g (g' x) (Ioi x) x；hg' : ContinuousOn g' (f '' [[a, b]])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_deriv_smul_comp''`：integral_deriv_smul_comp'' 
(hf : ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), HasD
erivWithinAt f (f' x) (Ioi x) x) …
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDeriv_right`：integral_eq_sub_of_h
asDeriv_right (hcont : ContinuousOn f (uIcc a b)) (hderiv : forall x in Ioo (min
 a b) (max a b), HasDerivWithinAt f (f' …
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `intermediate_value_uIcc`：intermediate_value_uIcc {a b : α} {f : α -> δ} 
(hf : ContinuousOn f [[a, b]]) : [[f a, f b]] subseteq f '' uIcc a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem integral_deriv_smul_deriv_comp' (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f b]])
    (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a := by
  rw [integral_deriv_smul_comp'' hf hff' hf' hg',
    integral_eq_sub_of_hasDeriv_right hg hgg' (hg'.mono _).intervalIntegrable]
  exacts [rfl, intermediate_value_uIcc hf]

@[deprecated (since := "2026-03-19")]
alias integral_deriv_comp_smul_deriv' := integral_deriv_smul_deriv_comp'
/-
**intervalIntegral.integral_deriv_smul_deriv_comp** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：integral_deriv_smul_deriv_comp (hf : forall x in uIcc a b, HasDerivAt f (f
' x) x) (hg : forall x in uIcc a b, HasDerivAt g (g' (f x)) (f x)) (hf' : Contin
uousOn f' (uIcc a b)) (hg' : Continuous g') : (∫ x in a..b, f' x • (g' ∘ f) x) =
 (g ∘ f) b - (g ∘ f) a
参数：hf : forall x in uIcc a b, HasDerivAt f (f' x) x；hg : forall x in uIcc a b, H
asDerivAt g (g' (f x)) (f x)；hf' : ContinuousOn f' (uIcc a b)；hg' : Continuous g
'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt`：integral_eq_sub_of_hasDe
rivAt (hderiv : forall x in uIcc a b, HasDerivAt f (f' x) x) (hint : IntervalInt
egrable f' volume a b) : ∫ y in a..b…
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `HasDerivAt.continuousOn`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 
𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {s 
: Set 𝕜} {f f…
-/
theorem integral_deriv_smul_deriv_comp (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (uIcc a b))
    (hg' : Continuous g') : (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a :=
  integral_eq_sub_of_hasDerivAt (fun x hx ↦ (hg x hx).scomp x <| hf x hx)
    (hf'.smul (hg'.comp_continuousOn <| HasDerivAt.continuousOn hf)).intervalIntegrable

@[deprecated (since := "2026-03-19")]
alias integral_deriv_comp_smul_deriv := integral_deriv_smul_deriv_comp

end CompleteSpace

end SMul

section Mul

/-- Change of variables, general form for scalar functions. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, `g` is continuous on `f '' (a, b)` and integrable on
`f '' [a, b]`, and `(g ∘ f) x * f' x` is integrable on `[a, b]`, then we can substitute `u = f x`
to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
/-
**intervalIntegral.integral_comp_mul_deriv'''** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：integral_comp_mul_deriv''' {a b : Real} {f f' : Real -> Real} {g : Real ->
 Real} (hf : ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b
), HasDerivWithinAt f (f' x) (Ioi x) x) (hg_cont : ContinuousOn g (f '' Ioo (min
 a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]])) (hg2 : IntegrableOn (fu
n x => (g ∘ f) x * f' x) [[a, b]]) : (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f 
a..f b, g u
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivWithinAt f (f' x) (Ioi x) x；hg_cont : ContinuousOn g (f '' Ioo (min a b) (ma
x a b))；hg1 : IntegrableOn g (f '' [[a, b]])；hg2 : IntegrableOn (fun x => (g ∘ f
) x * f' x) [[a, b]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `intervalIntegral.integral_deriv_smul_comp'''`：integral_deriv_smul_comp''
' (hf : ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), Ha
sDerivWithinAt f (f' x) (Ioi x) x)…

--- 原说明 ---
Change of variables, general form for scalar functions. If `f` is continuous on 
`[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, `g` is continuous on `f '' (a, b)`
 and integrable on
`f '' [a, b]`, and `(g ∘ f) x * f' x` is integrable on `[a, b]`, then we can sub
stitute `u = f x`
to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_mul_deriv''' {a b : ℝ} {f f' : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g (f '' Ioo (min a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]]))
    (hg2 : IntegrableOn (fun x ↦ (g ∘ f) x * f' x) [[a, b]]) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  have hg2' : IntegrableOn (fun x ↦ f' x • (g ∘ f) x) [[a, b]] := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_deriv_smul_comp''' hf hff' hg_cont hg1 hg2'

/-- Change of variables for continuous integrands. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
/-
**intervalIntegral.integral_comp_mul_deriv''** 是 Mathlib 中的一个定理，位于命名空间 `interval
Integral`。
形式化陈述：integral_comp_mul_deriv'' {f f' g : Real -> Real} (hf : ContinuousOn f [[a
, b]]) (hff' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (I
oi x) x) (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) 
: (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivWithinAt f (f' x) (Ioi x) x；hf' : ContinuousOn f' [[a, b]]；hg : ContinuousOn
 g (f '' [[a, b]])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `intervalIntegral.integral_deriv_smul_comp''`：integral_deriv_smul_comp'' 
(hf : ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), HasD
erivWithinAt f (f' x) (Ioi x) x) …

--- 原说明 ---
Change of variables for continuous integrands. If `f` is continuous on `[a, b]` 
and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a,
 b]` then we can
substitute `u = f x` to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g 
u`.
-/
theorem integral_comp_mul_deriv'' {f f' g : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  simpa [mul_comm] using integral_deriv_smul_comp'' hf hff' hf' hg

/-- Change of variables. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
Compared to `intervalIntegral.integral_comp_mul_deriv` we only require that `g` is continuous on
`f '' [a, b]`.
-/
/-
**intervalIntegral.integral_comp_mul_deriv'** 是 Mathlib 中的一个定理，位于命名空间 `intervalI
ntegral`。
形式化陈述：integral_comp_mul_deriv' {f f' g : Real -> Real} (h : forall x in uIcc a b
, HasDerivAt f (f' x) x) (h' : ContinuousOn f' (uIcc a b)) (hg : ContinuousOn g 
(f '' [[a, b]])) : (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x
参数：h : forall x in uIcc a b, HasDerivAt f (f' x) x；h' : ContinuousOn f' (uIcc a 
b)；hg : ContinuousOn g (f '' [[a, b]])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `intervalIntegral.integral_deriv_smul_comp'`：integral_deriv_smul_comp' (h
 : forall x in uIcc a b, HasDerivAt f (f' x) x) (h' : ContinuousOn f' (uIcc a b)
) (hg : ContinuousOn g (f '' [[a…

--- 原说明 ---
Change of variables. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
Compared to `intervalIntegral.integral_comp_mul_deriv` we only require that `g` 
is continuous on
`f '' [a, b]`.
-/
theorem integral_comp_mul_deriv' {f f' g : ℝ → ℝ} (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x := by
  simpa [mul_comm] using integral_deriv_smul_comp' h h' hg

/-- Change of variables, most common version. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
@[wikidata Q1071270]
/-
**intervalIntegral.integral_comp_mul_deriv** 是 Mathlib 中的一个定理，位于命名空间 `intervalIn
tegral`。
形式化陈述：integral_comp_mul_deriv {f f' g : Real -> Real} (h : forall x in uIcc a b,
 HasDerivAt f (f' x) x) (h' : ContinuousOn f' (uIcc a b)) (hg : Continuous g) : 
(∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x
参数：h : forall x in uIcc a b, HasDerivAt f (f' x) x；h' : ContinuousOn f' (uIcc a 
b)；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `intervalIntegral.integral_comp_mul_deriv'`：integral_comp_mul_deriv' {f f
' g : Real -> Real} (h : forall x in uIcc a b, HasDerivAt f (f' x) x) (h' : Cont
inuousOn f' (uIcc a b)) (hg : C…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
Change of variables, most common version. If `f` has continuous derivative `f'` 
on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_mul_deriv {f f' g : ℝ → ℝ} (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : Continuous g) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x :=
  integral_comp_mul_deriv' h h' hg.continuousOn

/-- Change of variables for monotone functions.
If `f` is continuous on `[a, b]` and has a nonnegative derivative `f'` in `(a, b)`,
then we can substitute `u = f x` to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`. -/
/-
**intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：integral_comp_mul_deriv_of_deriv_nonneg {f f' g : Real -> Real} (hf : Cont
inuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (
f' x) x) (hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x) : (∫ x in a..b, 
(g ∘ f) x * f' x) = ∫ u in f a..f b, g u
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivAt f (f' x) x；hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg`：integral_deri
v_smul_comp_of_deriv_nonneg (hf : ContinuousOn f [[a, b]]) (hff' : forall x in I
oo (min a b) (max a b), HasDerivAt f (f' x) x) …

--- 原说明 ---
Change of variables for monotone functions.
If `f` is continuous on `[a, b]` and has a nonnegative derivative `f'` in `(a, b
)`,
then we can substitute `u = f x` to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in 
f a..f b, g u`.
-/
theorem integral_comp_mul_deriv_of_deriv_nonneg {f f' g : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ f' x) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  simpa [mul_comm] using! integral_deriv_smul_comp_of_deriv_nonneg hf hff' hf'

/-- Change of variables for monotone functions.
If `f` is continuous on `[a, b]` and has a nonnegative derivative `f'` in `(a, b)`,
then we can substitute `u = f x` to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`. -/
/-
**intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：integral_comp_mul_deriv_of_deriv_nonpos {f f' g : Real -> Real} (hf : Cont
inuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (
f' x) x) (hf' : forall x in Ioo (min a b) (max a b), f' x <= 0) : (∫ x in a..b, 
(g ∘ f) x * f' x) = ∫ u in f a..f b, g u
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivAt f (f' x) x；hf' : forall x in Ioo (min a b) (max a b), f' x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos`：integral_deri
v_smul_comp_of_deriv_nonpos (hf : ContinuousOn f [[a, b]]) (hff' : forall x in I
oo (min a b) (max a b), HasDerivAt f (f' x) x) …

--- 原说明 ---
Change of variables for monotone functions.
If `f` is continuous on `[a, b]` and has a nonnegative derivative `f'` in `(a, b
)`,
then we can substitute `u = f x` to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in 
f a..f b, g u`.
-/
theorem integral_comp_mul_deriv_of_deriv_nonpos {f f' g : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo (min a b) (max a b), f' x ≤ 0) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  simpa [mul_comm] using! integral_deriv_smul_comp_of_deriv_nonpos hf hff' hf'
/-
**intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg** 是 Mathlib 中的一
个引理，位于命名空间 `intervalIntegral`。
形式化陈述：integrable_comp_mul_deriv_iff_of_deriv_nonneg {f f' g : Real -> Real} (hf 
: ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), HasDeriv
At f (f' x) x) (hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x) : Interval
Integrable (fun x => (g ∘ f) x * f' x) volume a b ↔ IntervalIntegrable g volume 
(f a) (f b)
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivAt f (f' x) x；hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg`：integra
ble_deriv_smul_comp_iff_of_deriv_nonneg (hf : ContinuousOn f [[a, b]]) (hff' : f
orall x in Ioo (min a b) (max a b), HasDerivAt f (f' …
-/
lemma integrable_comp_mul_deriv_iff_of_deriv_nonneg {f f' g : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ f' x) :
    IntervalIntegrable (fun x ↦ (g ∘ f) x * f' x) volume a b ↔
      IntervalIntegrable g volume (f a) (f b) := by
  simpa [mul_comm] using! integrable_deriv_smul_comp_iff_of_deriv_nonneg hf hff' hf'
/-
**intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos** 是 Mathlib 中的一
个引理，位于命名空间 `intervalIntegral`。
形式化陈述：integrable_comp_mul_deriv_iff_of_deriv_nonpos {f f' g : Real -> Real} (hf 
: ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), HasDeriv
At f (f' x) x) (hf' : forall x in Ioo (min a b) (max a b), f' x <= 0) : Interval
Integrable (fun x => (g ∘ f) x * f' x) volume a b ↔ IntervalIntegrable g volume 
(f a) (f b)
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivAt f (f' x) x；hf' : forall x in Ioo (min a b) (max a b), f' x <= 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonpos`：integra
ble_deriv_smul_comp_iff_of_deriv_nonpos (hf : ContinuousOn f [[a, b]]) (hff' : f
orall x in Ioo (min a b) (max a b), HasDerivAt f (f' …
-/
lemma integrable_comp_mul_deriv_iff_of_deriv_nonpos {f f' g : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo (min a b) (max a b), f' x ≤ 0) :
    IntervalIntegrable (fun x ↦ (g ∘ f) x * f' x) volume a b ↔
      IntervalIntegrable g volume (f a) (f b) := by
  simpa [mul_comm] using! integrable_deriv_smul_comp_iff_of_deriv_nonpos hf hff' hf'
/-
**intervalIntegral.integral_deriv_comp_mul_deriv'** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：integral_deriv_comp_mul_deriv' {f f' g g' : Real -> Real} (hf : Continuous
On f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt f (
f' x) (Ioi x) x) (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f 
b]]) (hgg' : forall x in Ioo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithin
At g (g' x) (Ioi x) x) (hg' : ContinuousOn g' (f '' [[a, b]])) : (∫ x in a..b, (
g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a
参数：hf : ContinuousOn f [[a, b]]；hff' : forall x in Ioo (min a b) (max a b), HasD
erivWithinAt f (f' x) (Ioi x) x；hf' : ContinuousOn f' [[a, b]]；hg : ContinuousOn
 g [[f a, f b]]；hgg' : forall x in Ioo (min (f a) (f b)) (max (f a) (f b)), HasD
erivWithinAt g (g' x) (Ioi x) x；hg' : ContinuousOn g' (f '' [[a, b]])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `intervalIntegral.integral_deriv_smul_deriv_comp'`：integral_deriv_smul_de
riv_comp' (hf : ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max 
a b), HasDerivWithinAt f (f' x) (Ioi x…
-/
theorem integral_deriv_comp_mul_deriv' {f f' g g' : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f b]])
    (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' [[a, b]])) :
    (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [mul_comm] using integral_deriv_smul_deriv_comp' hf hff' hf' hg hgg' hg'
/-
**intervalIntegral.integral_deriv_comp_mul_deriv** 是 Mathlib 中的一个定理，位于命名空间 `inte
rvalIntegral`。
形式化陈述：integral_deriv_comp_mul_deriv {f f' g g' : Real -> Real} (hf : forall x in
 uIcc a b, HasDerivAt f (f' x) x) (hg : forall x in uIcc a b, HasDerivAt g (g' (
f x)) (f x)) (hf' : ContinuousOn f' (uIcc a b)) (hg' : Continuous g') : (∫ x in 
a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a
参数：hf : forall x in uIcc a b, HasDerivAt f (f' x) x；hg : forall x in uIcc a b, H
asDerivAt g (g' (f x)) (f x)；hf' : ContinuousOn f' (uIcc a b)；hg' : Continuous g
'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `intervalIntegral.integral_deriv_smul_deriv_comp`：integral_deriv_smul_der
iv_comp (hf : forall x in uIcc a b, HasDerivAt f (f' x) x) (hg : forall x in uIc
c a b, HasDerivAt g (g' (f x)) (f x))…
-/
theorem integral_deriv_comp_mul_deriv {f f' g g' : ℝ → ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (uIcc a b))
    (hg' : Continuous g') : (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [mul_comm] using integral_deriv_smul_deriv_comp hf hg hf' hg'

end Mul

end intervalIntegral

