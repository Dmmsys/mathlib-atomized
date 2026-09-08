/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Side
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Oriented angles.

This file defines oriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.oangle`, with notation `∡`, is the oriented angle determined by three
  points.

-/

@[expose] public section


noncomputable section

open Module Complex

open scoped Affine EuclideanGeometry Real RealInnerProductSpace ComplexConjugate

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- A fixed choice of positive orientation of Euclidean space `ℝ²` -/
/-
**EuclideanGeometry.o** 是 Mathlib 中的一个缩写定义，位于命名空间 `EuclideanGeometry`。
形式化陈述：o
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fixed choice of positive orientation of Euclidean space `ℝ²`
-/
abbrev o := @Module.Oriented.positiveOrientation

/-- The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If
either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the
corresponding unoriented angle definition. -/
/-
**EuclideanGeometry.oangle** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle (p₁ p₂ p₃ : P) : Real.Angle
参数：p₁ p₂ p₃ : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2
 * π`. If
either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for
 the
corresponding unoriented angle definition.
-/
def oangle (p₁ p₂ p₃ : P) : Real.Angle :=
  o.oangle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)

@[inherit_doc] scoped notation "∡" => EuclideanGeometry.oangle

/-- Oriented angles are continuous when neither endpoint equals the middle point. -/
/-
**EuclideanGeometry.continuousAt_oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeom
etry`。
形式化陈述：continuousAt_oangle {x : P × P × P} (hx12 : x.1 != x.2.1) (hx32 : x.2.2 !=
 x.2.1) : ContinuousAt (fun y : P × P × P => ∡ y.1 y.2.1 y.2.2) x
参数：hx12 : x.1 != x.2.1；hx32 : x.2.2 != x.2.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `Orientation.continuousAt_oangle`：continuousAt_oangle {x : V × V} (hx1 : 
x.1 != 0) (hx2 : x.2 != 0) : ContinuousAt (fun y : V × V => o.oangle y.1 y.2) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `ContinuousAt.vsub`：∀ {V : Type u_1} {P : Type u_2} {α : Type u_3} [inst 
: AddGroup V] [inst_1 : TopologicalSpace V]   [inst_2 : AddTorsor V P] [inst_3 :
 Topolo…
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `ContinuousAt.fst`：ContinuousAt.fst {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).1) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `ContinuousAt.snd`：ContinuousAt.snd {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).2) x

--- 原说明 ---
Oriented angles are continuous when neither endpoint equals the middle point.
-/
theorem continuousAt_oangle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
    ContinuousAt (fun y : P × P × P => ∡ y.1 y.2.1 y.2.2) x := by
  unfold oangle
  fun_prop (disch := simp [*])

/-- The angle ∡AAB at a point. -/
@[simp]
/-
**EuclideanGeometry.oangle_self_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：oangle_self_left (p₁ p₂ : P) : ∡ p₁ p₁ p₂ = 0
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The angle ∡AAB at a point.
-/
theorem oangle_self_left (p₁ p₂ : P) : ∡ p₁ p₁ p₂ = 0 := by simp [oangle]

/-- The angle ∡ABB at a point. -/
@[simp]
/-
**EuclideanGeometry.oangle_self_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
形式化陈述：oangle_self_right (p₁ p₂ : P) : ∡ p₁ p₂ p₂ = 0
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The angle ∡ABB at a point.
-/
theorem oangle_self_right (p₁ p₂ : P) : ∡ p₁ p₂ p₂ = 0 := by simp [oangle]

/-- The angle ∡ABA at a point. -/
@[simp]
/-
**EuclideanGeometry.oangle_self_left_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry`。
形式化陈述：oangle_self_left_right (p₁ p₂ : P) : ∡ p₁ p₂ p₁ = 0
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0

--- 原说明 ---
The angle ∡ABA at a point.
-/
theorem oangle_self_left_right (p₁ p₂ : P) : ∡ p₁ p₂ p₁ = 0 :=
  o.oangle_self _

/-- If the angle between three points is nonzero, the first two points are not equal. -/
/-
**EuclideanGeometry.left_ne_of_oangle_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anGeometry`。
形式化陈述：left_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₂
参数：h : ∡ p₁ p₂ p₃ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `Orientation.left_ne_zero_of_oangle_ne_zero`：left_ne_zero_of_oangle_ne_ze
ro {x y : V} (h : o.oangle x y != 0) : x != 0

--- 原说明 ---
If the angle between three points is nonzero, the first two points are not equal
.
-/
theorem left_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ ≠ 0) : p₁ ≠ p₂ := by
  rw [← @vsub_ne_zero V]; exact o.left_ne_zero_of_oangle_ne_zero h

/-- If the angle between three points is nonzero, the last two points are not equal. -/
/-
**EuclideanGeometry.right_ne_of_oangle_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：right_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₃ != p₂
参数：h : ∡ p₁ p₂ p₃ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `Orientation.right_ne_zero_of_oangle_ne_zero`：right_ne_zero_of_oangle_ne_
zero {x y : V} (h : o.oangle x y != 0) : y != 0

--- 原说明 ---
If the angle between three points is nonzero, the last two points are not equal.
-/
theorem right_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ ≠ 0) : p₃ ≠ p₂ := by
  rw [← @vsub_ne_zero V]; exact o.right_ne_zero_of_oangle_ne_zero h

/-- If the angle between three points is nonzero, the first and third points are not equal. -/
/-
**EuclideanGeometry.left_ne_right_of_oangle_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：left_ne_right_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ 
!= p₃
参数：h : ∡ p₁ p₂ p₃ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `vsub_left_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p : P), Function.Injective fun x => x -ᵥ p
· 使用定理 `Orientation.ne_of_oangle_ne_zero`：ne_of_oangle_ne_zero {x y : V} (h : o.
oangle x y != 0) : x != y

--- 原说明 ---
If the angle between three points is nonzero, the first and third points are not
 equal.
-/
theorem left_ne_right_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ ≠ 0) : p₁ ≠ p₃ := by
  rw [← (vsub_left_injective p₂).ne_iff]; exact o.ne_of_oangle_ne_zero h

/-- If the angle between three points is `π`, the first two points are not equal. -/
/-
**EuclideanGeometry.left_ne_of_oangle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry`。
形式化陈述：left_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ != p₂
参数：h : ∡ p₁ p₂ p₃ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_ne_zero`：left_ne_of_oangle_ne_zero {
p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₂
· 使用定理 `Real.Angle.pi_ne_zero`：pi_ne_zero : (π : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between three points is `π`, the first two points are not equal.
-/
theorem left_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π`, the last two points are not equal. -/
/-
**EuclideanGeometry.right_ne_of_oangle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Euclidea
nGeometry`。
形式化陈述：right_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₃ != p₂
参数：h : ∡ p₁ p₂ p₃ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_ne_zero`：right_ne_of_oangle_ne_zero
 {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₃ != p₂
· 使用定理 `Real.Angle.pi_ne_zero`：pi_ne_zero : (π : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between three points is `π`, the last two points are not equal.
-/
theorem right_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π`, the first and third points are not equal. -/
/-
**EuclideanGeometry.left_ne_right_of_oangle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Euc
lideanGeometry`。
形式化陈述：left_ne_right_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ != 
p₃
参数：h : ∡ p₁ p₂ p₃ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.left_ne_right_of_oangle_ne_zero`：left_ne_right_of_oang
le_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₃
· 使用定理 `Real.Angle.pi_ne_zero`：pi_ne_zero : (π : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between three points is `π`, the first and third points are not equ
al.
-/
theorem left_ne_right_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π / 2`, the first two points are not equal. -/
/-
**EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：left_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : 
Real)) : p₁ != p₂
参数：h : ∡ p₁ p₂ p₃ = (π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_ne_zero`：left_ne_of_oangle_ne_zero {
p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₂
· 使用定理 `Real.Angle.pi_div_two_ne_zero`：pi_div_two_ne_zero : ((π / 2 : Real) : An
gle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between three points is `π / 2`, the first two points are not equal
.
-/
theorem left_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) : p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π / 2`, the last two points are not equal. -/
/-
**EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：right_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 :
 Real)) : p₃ != p₂
参数：h : ∡ p₁ p₂ p₃ = (π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_ne_zero`：right_ne_of_oangle_ne_zero
 {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₃ != p₂
· 使用定理 `Real.Angle.pi_div_two_ne_zero`：pi_div_two_ne_zero : ((π / 2 : Real) : An
gle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between three points is `π / 2`, the last two points are not equal.
-/
theorem right_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) : p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π / 2`, the first and third points are not equal. -/
/-
**EuclideanGeometry.left_ne_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：left_ne_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π 
/ 2 : Real)) : p₁ != p₃
参数：h : ∡ p₁ p₂ p₃ = (π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.left_ne_right_of_oangle_ne_zero`：left_ne_right_of_oang
le_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₃
· 使用定理 `Real.Angle.pi_div_two_ne_zero`：pi_div_two_ne_zero : ((π / 2 : Real) : An
gle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between three points is `π / 2`, the first and third points are not
 equal.
-/
theorem left_ne_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) :
    p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `-π / 2`, the first two points are not equal. -/
/-
**EuclideanGeometry.left_ne_of_oangle_eq_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry`。
形式化陈述：left_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π /
 2 : Real)) : p₁ != p₂
参数：h : ∡ p₁ p₂ p₃ = (-π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_ne_zero`：left_ne_of_oangle_ne_zero {
p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₂
· 使用定理 `Real.Angle.neg_pi_div_two_ne_zero`：neg_pi_div_two_ne_zero : ((-π / 2 : R
eal) : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between three points is `-π / 2`, the first two points are not equa
l.
-/
theorem left_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
    p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `-π / 2`, the last two points are not equal. -/
/-
**EuclideanGeometry.right_ne_of_oangle_eq_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名
空间 `EuclideanGeometry`。
形式化陈述：right_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π 
/ 2 : Real)) : p₃ != p₂
参数：h : ∡ p₁ p₂ p₃ = (-π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_ne_zero`：right_ne_of_oangle_ne_zero
 {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₃ != p₂
· 使用定理 `Real.Angle.neg_pi_div_two_ne_zero`：neg_pi_div_two_ne_zero : ((-π / 2 : R
eal) : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between three points is `-π / 2`, the last two points are not equal
.
-/
theorem right_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
    p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `-π / 2`, the first and third points are not equal. -/
/-
**EuclideanGeometry.left_ne_right_of_oangle_eq_neg_pi_div_two** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：left_ne_right_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ =
 (-π / 2 : Real)) : p₁ != p₃
参数：h : ∡ p₁ p₂ p₃ = (-π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.left_ne_right_of_oangle_ne_zero`：left_ne_right_of_oang
le_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₃
· 使用定理 `Real.Angle.neg_pi_div_two_ne_zero`：neg_pi_div_two_ne_zero : ((-π / 2 : R
eal) : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between three points is `-π / 2`, the first and third points are no
t equal.
-/
theorem left_ne_right_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
    p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the sign of the angle between three points is nonzero, the first two points are not
equal. -/
/-
**EuclideanGeometry.left_ne_of_oangle_sign_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：left_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0)
 : p₁ != p₂
参数：h : (∡ p₁ p₂ p₃).sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_ne_zero`：left_ne_of_oangle_ne_zero {
p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.sign_ne_zero_iff`：sign_ne_zero_iff {θ : Angle} : θ.sign != 0 
↔ θ != 0 ∧ θ != π

--- 原说明 ---
If the sign of the angle between three points is nonzero, the first two points a
re not
equal.
-/
theorem left_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between three points is nonzero, the last two points are not
equal. -/
/-
**EuclideanGeometry.right_ne_of_oangle_sign_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：right_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0
) : p₃ != p₂
参数：h : (∡ p₁ p₂ p₃).sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_ne_zero`：right_ne_of_oangle_ne_zero
 {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₃ != p₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.sign_ne_zero_iff`：sign_ne_zero_iff {θ : Angle} : θ.sign != 0 
↔ θ != 0 ∧ θ != π

--- 原说明 ---
If the sign of the angle between three points is nonzero, the last two points ar
e not
equal.
-/
theorem right_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between three points is nonzero, the first and third points are not
equal. -/
/-
**EuclideanGeometry.left_ne_right_of_oangle_sign_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 `EuclideanGeometry`。
形式化陈述：left_ne_right_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign
 != 0) : p₁ != p₃
参数：h : (∡ p₁ p₂ p₃).sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.left_ne_right_of_oangle_ne_zero`：left_ne_right_of_oang
le_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₃
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.sign_ne_zero_iff`：sign_ne_zero_iff {θ : Angle} : θ.sign != 0 
↔ θ != 0 ∧ θ != π

--- 原说明 ---
If the sign of the angle between three points is nonzero, the first and third po
ints are not
equal.
-/
theorem left_ne_right_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between three points is positive, the first two points are not
equal. -/
/-
**EuclideanGeometry.left_ne_of_oangle_sign_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Euc
lideanGeometry`。
形式化陈述：left_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) :
 p₁ != p₂
参数：h : (∡ p₁ p₂ p₃).sign = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_sign_ne_zero`：left_ne_of_oangle_sign
_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0) : p₁ != p₂
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between three points is positive, the first two points 
are not
equal.
-/
theorem left_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ ≠ p₂ :=
  left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is positive, the last two points are not
equal. -/
/-
**EuclideanGeometry.right_ne_of_oangle_sign_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：right_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) 
: p₃ != p₂
参数：h : (∡ p₁ p₂ p₃).sign = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_sign_ne_zero`：right_ne_of_oangle_si
gn_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0) : p₃ != p₂
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between three points is positive, the last two points a
re not
equal.
-/
theorem right_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₃ ≠ p₂ :=
  right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is positive, the first and third points are not
equal. -/
/-
**EuclideanGeometry.left_ne_right_of_oangle_sign_eq_one** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry`。
形式化陈述：left_ne_right_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign 
= 1) : p₁ != p₃
参数：h : (∡ p₁ p₂ p₃).sign = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.left_ne_right_of_oangle_sign_ne_zero`：left_ne_right_of
_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0) : p₁ != p₃
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between three points is positive, the first and third p
oints are not
equal.
-/
theorem left_ne_right_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ ≠ p₃ :=
  left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is negative, the first two points are not
equal. -/
/-
**EuclideanGeometry.left_ne_of_oangle_sign_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：left_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 
-1) : p₁ != p₂
参数：h : (∡ p₁ p₂ p₃).sign = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_sign_ne_zero`：left_ne_of_oangle_sign
_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0) : p₁ != p₂
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between three points is negative, the first two points 
are not
equal.
-/
theorem left_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₁ ≠ p₂ :=
  left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is negative, the last two points are not equal.
-/
/-
**EuclideanGeometry.right_ne_of_oangle_sign_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry`。
形式化陈述：right_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign =
 -1) : p₃ != p₂
参数：h : (∡ p₁ p₂ p₃).sign = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_sign_ne_zero`：right_ne_of_oangle_si
gn_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0) : p₃ != p₂
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between three points is negative, the last two points a
re not equal.
-/
theorem right_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₃ ≠ p₂ :=
  right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is negative, the first and third points are not
equal. -/
/-
**EuclideanGeometry.left_ne_right_of_oangle_sign_eq_neg_one** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry`。
形式化陈述：left_ne_right_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).s
ign = -1) : p₁ != p₃
参数：h : (∡ p₁ p₂ p₃).sign = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.left_ne_right_of_oangle_sign_ne_zero`：left_ne_right_of
_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0) : p₁ != p₃
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between three points is negative, the first and third p
oints are not
equal.
-/
theorem left_ne_right_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) :
    p₁ ≠ p₃ :=
  left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- Reversing the order of the points passed to `oangle` negates the angle. -/
/-
**EuclideanGeometry.oangle_rev** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -∡ p₁ p₂ p₃
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y

--- 原说明 ---
Reversing the order of the points passed to `oangle` negates the angle.
-/
theorem oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -∡ p₁ p₂ p₃ :=
  o.oangle_rev _ _

/-- Adding an angle to that with the order of the points reversed results in 0. -/
@[simp]
/-
**EuclideanGeometry.oangle_add_oangle_rev** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：oangle_add_oangle_rev (p₁ p₂ p₃ : P) : ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_add_oangle_rev`：oangle_add_oangle_rev (x y : V) : o.o
angle x y + o.oangle y x = 0

--- 原说明 ---
Adding an angle to that with the order of the points reversed results in 0.
-/
theorem oangle_add_oangle_rev (p₁ p₂ p₃ : P) : ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0 :=
  o.oangle_add_oangle_rev _ _

/-- An oriented angle is zero if and only if the angle with the order of the points reversed is
zero. -/
/-
**EuclideanGeometry.oangle_eq_zero_iff_oangle_rev_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：oangle_eq_zero_iff_oangle_rev_eq_zero {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ↔ ∡ 
p₃ p₂ p₁ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_zero_iff_oangle_rev_eq_zero`：oangle_eq_zero_iff_oa
ngle_rev_eq_zero {x y : V} : o.oangle x y = 0 ↔ o.oangle y x = 0

--- 原说明 ---
An oriented angle is zero if and only if the angle with the order of the points 
reversed is
zero.
-/
theorem oangle_eq_zero_iff_oangle_rev_eq_zero {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ↔ ∡ p₃ p₂ p₁ = 0 :=
  o.oangle_eq_zero_iff_oangle_rev_eq_zero

/-- An oriented angle is `π` if and only if the angle with the order of the points reversed is
`π`. -/
/-
**EuclideanGeometry.oangle_eq_pi_iff_oangle_rev_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：oangle_eq_pi_iff_oangle_rev_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∡ p₃ p
₂ p₁ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_pi_iff_oangle_rev_eq_pi`：oangle_eq_pi_iff_oangle_r
ev_eq_pi {x y : V} : o.oangle x y = π ↔ o.oangle y x = π

--- 原说明 ---
An oriented angle is `π` if and only if the angle with the order of the points r
eversed is
`π`.
-/
theorem oangle_eq_pi_iff_oangle_rev_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∡ p₃ p₂ p₁ = π :=
  o.oangle_eq_pi_iff_oangle_rev_eq_pi

/-- A homothety with a nonzero scale factor preserves angles. -/
/-
**EuclideanGeometry.oangle_homothety** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] [
hd2 : Fact (Module.finrank ℝ V = 2)] [inst_4 : Module.Oriented ℝ V (Fin 2)]   (p
 p₁ p₂ p₃ : P) {r : ℝ},   r ≠ 0 →     EuclideanGeometry.oangle ((AffineMap.homot
hety p r) p₁) ((AffineMap.homothety p r) p₂)         ((AffineMap.homothety p r) 
p₃) =       EuclideanGeometry.oangle p₁ p₂ p₃
参数：Module.finrank ℝ V = 2；Fin 2；p p₁ p₂ p₃ : P；(AffineMap.homothety p r) p₁；(Aff
ineMap.homothety p r) p₂；(AffineMap.homothety p r) p₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `AffineMap.homothety_linear`：homothety_linear (c : P1) (r : k) : (homothe
ty c r).linear = r • LinearMap.id
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Orientation.oangle_smul_right_of_neg`：oangle_smul_right_of_neg (x y : V)
 {r : Real} (hr : r < 0) : o.oangle x (r • y) = o.oangle x (-y)
· 使用定理 `Orientation.oangle_smul_left_of_neg`：oangle_smul_left_of_neg (x y : V) {
r : Real} (hr : r < 0) : o.oangle (r • x) y = o.oangle (-x) y
· 使用定理 `Orientation.oangle_neg_neg`：oangle_neg_neg (x y : V) : o.oangle (-x) (-y
) = o.oangle x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_smul_right_of_pos`：oangle_smul_right_of_pos (x y : V)
 {r : Real} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y
· 使用定理 `Orientation.oangle_smul_left_of_pos`：oangle_smul_left_of_pos (x y : V) {
r : Real} (hr : 0 < r) : o.oangle (r • x) y = o.oangle x y

--- 原说明 ---
A homothety with a nonzero scale factor preserves angles.
-/
@[simp] lemma oangle_homothety (p p₁ p₂ p₃ : P) {r : ℝ} (h : r ≠ 0) :
    ∡ (AffineMap.homothety p r p₁) (AffineMap.homothety p r p₂) (AffineMap.homothety p r p₃) =
      ∡ p₁ p₂ p₃ := by
  simp_rw [oangle, ← AffineMap.linearMap_vsub, AffineMap.homothety_linear, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rcases h.lt_or_gt with hlt | hlt <;> simp [hlt, -neg_vsub_eq_vsub_rev]

/-- An oriented angle is not zero or `π` if and only if the three points are affinely
independent. -/
/-
**EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affineIndependent** 是 Mathlib 中
的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_ne_zero_and_ne_pi_iff_affineIndependent {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃
 != 0 ∧ ∡ p₁ p₂ p₃ != π ↔ AffineIndependent Real ![p₁, p₂, p₃]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `Orientation.oangle_ne_zero_and_ne_pi_iff_linearIndependent`：oangle_ne_ze
ro_and_ne_pi_iff_linearIndependent {x y : V} : o.oangle x y != 0 ∧ o.oangle x y 
!= π ↔ LinearIndependent Real ![x, y]
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An oriented angle is not zero or `π` if and only if the three points are affinel
y
independent.
-/
theorem oangle_ne_zero_and_ne_pi_iff_affineIndependent {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ ≠ 0 ∧ ∡ p₁ p₂ p₃ ≠ π ↔ AffineIndependent ℝ ![p₁, p₂, p₃] := by
  rw [oangle, o.oangle_ne_zero_and_ne_pi_iff_linearIndependent,
    affineIndependent_iff_linearIndependent_vsub ℝ _ (1 : Fin 3), ←
    linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))]
  convert! Iff.rfl
  ext i
  fin_cases i <;> rfl

/-- An oriented angle is zero or `π` if and only if the three points are collinear. -/
/-
**EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：oangle_eq_zero_or_eq_pi_iff_collinear {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ∨ ∡ 
p₁ p₂ p₃ = π ↔ Collinear Real ({p₁, p₂, p₃} : Set P)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affineIndependent`：oangle
_ne_zero_and_ne_pi_iff_affineIndependent {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ != 0 ∧ ∡ p₁
 p₂ p₃ != π ↔ AffineIndependent Real ![p₁, p₂, p₃]
· 使用定理 `affineIndependent_iff_not_collinear_set`：affineIndependent_iff_not_colli
near_set {p₁ p₂ p₃ : P} : AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁,
 p₂, p₃} : Set P)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An oriented angle is zero or `π` if and only if the three points are collinear.
-/
theorem oangle_eq_zero_or_eq_pi_iff_collinear {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ = 0 ∨ ∡ p₁ p₂ p₃ = π ↔ Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
  rw [← not_iff_not, not_or, oangle_ne_zero_and_ne_pi_iff_affineIndependent,
    affineIndependent_iff_not_collinear_set]

/-- An oriented angle has a sign zero if and only if the three points are collinear. -/
/-
**EuclideanGeometry.oangle_sign_eq_zero_iff_collinear** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：oangle_sign_eq_zero_iff_collinear {p₁ p₂ p₃ : P} : (∡ p₁ p₂ p₃).sign = 0 ↔
 Collinear Real ({p₁, p₂, p₃} : Set P)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.sign_eq_zero_iff`：sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔
 θ = 0 ∨ θ = π
· 使用定理 `EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear`：oangle_eq_zero_
or_eq_pi_iff_collinear {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ∨ ∡ p₁ p₂ p₃ = π ↔ Collin
ear Real ({p₁, p₂, p₃} : Set P)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An oriented angle has a sign zero if and only if the three points are collinear.
-/
theorem oangle_sign_eq_zero_iff_collinear {p₁ p₂ p₃ : P} :
    (∡ p₁ p₂ p₃).sign = 0 ↔ Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
  rw [Real.Angle.sign_eq_zero_iff, oangle_eq_zero_or_eq_pi_iff_collinear]

/-- An oriented angle is not zero and `π` if and only if the three points are not collinear. -/
/-
**EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_not_collinear** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_ne_zero_and_ne_pi_iff_not_collinear {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ != 
0 ∧ ∡ p₁ p₂ p₃ != π ↔ ¬ Collinear Real {p₁, p₂, p₃}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affineIndependent`：oangle
_ne_zero_and_ne_pi_iff_affineIndependent {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ != 0 ∧ ∡ p₁
 p₂ p₃ != π ↔ AffineIndependent Real ![p₁, p₂, p₃]
· 使用定理 `affineIndependent_iff_not_collinear_set`：affineIndependent_iff_not_colli
near_set {p₁ p₂ p₃ : P} : AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁,
 p₂, p₃} : Set P)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An oriented angle is not zero and `π` if and only if the three points are not co
llinear.
-/
theorem oangle_ne_zero_and_ne_pi_iff_not_collinear {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ ≠ 0 ∧ ∡ p₁ p₂ p₃ ≠ π ↔ ¬ Collinear ℝ {p₁, p₂, p₃} := by
  rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent, affineIndependent_iff_not_collinear_set]

/-- If twice the oriented angles between two triples of points are equal, one triple is affinely
independent if and only if the other is. -/
/-
**EuclideanGeometry.affineIndependent_iff_of_two_zsmul_oangle_eq** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：affineIndependent_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : 
(2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆) : AffineIndependent Real ![p₁, 
p₂, p₃] ↔ AffineIndependent Real ![p₄, p₅, p₆]
参数：h : (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If twice the oriented angles between two triples of points are equal, one triple
 is affinely
independent if and only if the other is.
-/
theorem affineIndependent_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆) :
    AffineIndependent ℝ ![p₁, p₂, p₃] ↔ AffineIndependent ℝ ![p₄, p₅, p₆] := by
  simp_rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.two_zsmul_ne_zero_iff, h]

/-- If twice the oriented angles between two triples of points are equal, one triple is collinear
if and only if the other is. -/
/-
**EuclideanGeometry.collinear_iff_of_two_zsmul_oangle_eq** 是 Mathlib 中的一个定理，位于命名
空间 `EuclideanGeometry`。
形式化陈述：collinear_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : (2 : Int
) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆) : Collinear Real ({p₁, p₂, p₃} : Set P)
 ↔ Collinear Real ({p₄, p₅, p₆} : Set P)
参数：h : (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If twice the oriented angles between two triples of points are equal, one triple
 is collinear
if and only if the other is.
-/
theorem collinear_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ Collinear ℝ ({p₄, p₅, p₆} : Set P) := by
  simp_rw [← oangle_eq_zero_or_eq_pi_iff_collinear, ← Real.Angle.two_zsmul_eq_zero_iff, h]

/-- If corresponding pairs of points in two angles have the same vector span, twice those angles
are equal. -/
/-
**EuclideanGeometry.two_zsmul_oangle_of_vectorSpan_eq** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：two_zsmul_oangle_of_vectorSpan_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₁₂₄₅ : vectorS
pan Real ({p₁, p₂} : Set P) = vectorSpan Real ({p₄, p₅} : Set P)) (h₃₂₆₅ : vecto
rSpan Real ({p₃, p₂} : Set P) = vectorSpan Real ({p₆, p₅} : Set P)) : (2 : Int) 
• ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆
参数：h₁₂₄₅ : vectorSpan Real ({p₁, p₂} : Set P) = vectorSpan Real ({p₄, p₅} : Set 
P)；h₃₂₆₅ : vectorSpan Real ({p₃, p₂} : Set P) = vectorSpan Real ({p₆, p₅} : Set 
P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.two_zsmul_oangle_of_span_eq_of_span_eq`：two_zsmul_oangle_of_
span_eq_of_span_eq {w x y z : V} (hwx : Real ∙ w = Real ∙ x) (hyz : Real ∙ y = R
eal ∙ z) : (2 : Int) • o.oangle w y = (2…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_pair`：vectorSpan_pair (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : 
Set P) = k ∙ (p₁ -ᵥ p₂)

--- 原说明 ---
If corresponding pairs of points in two angles have the same vector span, twice 
those angles
are equal.
-/
theorem two_zsmul_oangle_of_vectorSpan_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h₁₂₄₅ : vectorSpan ℝ ({p₁, p₂} : Set P) = vectorSpan ℝ ({p₄, p₅} : Set P))
    (h₃₂₆₅ : vectorSpan ℝ ({p₃, p₂} : Set P) = vectorSpan ℝ ({p₆, p₅} : Set P)) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆ := by
  simp_rw [vectorSpan_pair] at h₁₂₄₅ h₃₂₆₅
  exact o.two_zsmul_oangle_of_span_eq_of_span_eq h₁₂₄₅ h₃₂₆₅

/-- If the lines determined by corresponding pairs of points in two angles are parallel, twice
those angles are equal. -/
/-
**EuclideanGeometry.two_zsmul_oangle_of_parallel** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：two_zsmul_oangle_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₁₂₄₅ : line[Real, p
₁, p₂] ∥ line[Real, p₄, p₅]) (h₃₂₆₅ : line[Real, p₃, p₂] ∥ line[Real, p₆, p₅]) :
 (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆
参数：h₁₂₄₅ : line[Real, p₁, p₂] ∥ line[Real, p₄, p₅]；h₃₂₆₅ : line[Real, p₃, p₂] ∥ 
line[Real, p₆, p₅]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.two_zsmul_oangle_of_vectorSpan_eq`：two_zsmul_oangle_of
_vectorSpan_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₁₂₄₅ : vectorSpan Real ({p₁, p₂} : Set 
P) = vectorSpan Real ({p₄, p₅} : Set P)) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq`：affineSpan_pa
ir_parallel_iff_vectorSpan_eq {p₁ p₂ p₃ p₄ : P} : line[k, p₁, p₂] ∥ line[k, p₃, 
p₄] ↔ vectorSpan k ({p₁, p₂} : Set P) = vectorS…

--- 原说明 ---
If the lines determined by corresponding pairs of points in two angles are paral
lel, twice
those angles are equal.
-/
theorem two_zsmul_oangle_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h₁₂₄₅ : line[ℝ, p₁, p₂] ∥ line[ℝ, p₄, p₅]) (h₃₂₆₅ : line[ℝ, p₃, p₂] ∥ line[ℝ, p₆, p₅]) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆ := by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq] at h₁₂₄₅ h₃₂₆₅
  exact two_zsmul_oangle_of_vectorSpan_eq h₁₂₄₅ h₃₂₆₅

/-- Consider two angles `∡ p₁ p₂ p₃` and `∡ p₄ p₅ p₆` defined by triples of points. Each is the
angle between two lines; if the pair `p₁ p₂` and `p₄ p₅` of corresponding lines is parallel, and
also the pair `p₃ p₂` and `p₆ p₅` of corresponding lines is parallel, and also (roughly) the third
pair of lines `p₁ p₃` and `p₄ p₆` are the same line, then the two angles are equal.  This is a
stronger version of `two_zsmul_oangle_of_parallel`, which shows that the two angles are equal mod
`π` in the absence of the condition on the third pair of lines. -/
/-
**EuclideanGeometry.oangle_eq_of_parallel** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：oangle_eq_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[Real, p₁, p₃
]) (h₄ : p₄ in line[Real, p₁, p₃]) (h₆ : p₆ in line[Real, p₁, p₃]) (h₁₂₄₅ : line
[Real, p₁, p₂] ∥ line[Real, p₄, p₅]) (h₃₂₆₅ : line[Real, p₃, p₂] ∥ line[Real, p₆
, p₅]) : ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆
参数：h₂ : p₂ ∉ line[Real, p₁, p₃]；h₄ : p₄ in line[Real, p₁, p₃]；h₆ : p₆ in line[Re
al, p₁, p₃]；h₁₂₄₅ : line[Real, p₁, p₂] ∥ line[Real, p₄, p₅]；h₃₂₆₅ : line[Real, p
₃, p₂] ∥ line[Real, p₆, p₅]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `affineSpan_pair_le_of_mem_of_mem`：affineSpan_pair_le_of_mem_of_mem {p₁ p
₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : line[k, p₁, p₂
] <= s
· 使用定理 `exists_eq_smul_of_parallel`：exists_eq_smul_of_parallel {p₁ p₂ p₃ p₄ p₅ p
₆ : P} (h₂ : p₂ ∉ line[k, p₁, p₃]) (h₁₂₄₅ : line[k, p₁, p₂] ∥ line[k, p₄, p₅]) (
h₂₃₅₆ : line[k, …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.Parallel.direction_eq`：∀ {k : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k
 V]   [inst_3 : AddTorsor …
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Orientation.oangle_smul_right_of_neg`：oangle_smul_right_of_neg (x y : V)
 {r : Real} (hr : r < 0) : o.oangle x (r • y) = o.oangle x (-y)
· 使用定理 `Orientation.oangle_smul_left_of_neg`：oangle_smul_left_of_neg (x y : V) {
r : Real} (hr : r < 0) : o.oangle (r • x) y = o.oangle (-x) y
· 使用定理 `Orientation.oangle_neg_neg`：oangle_neg_neg (x y : V) : o.oangle (-x) (-y
) = o.oangle x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_smul_right_of_pos`：oangle_smul_right_of_pos (x y : V)
 {r : Real} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y
· 使用定理 `Orientation.oangle_smul_left_of_pos`：oangle_smul_left_of_pos (x y : V) {
r : Real} (hr : 0 < r) : o.oangle (r • x) y = o.oangle x y

--- 原说明 ---
Consider two angles `∡ p₁ p₂ p₃` and `∡ p₄ p₅ p₆` defined by triples of points. 
Each is the
angle between two lines; if the pair `p₁ p₂` and `p₄ p₅` of corresponding lines 
is parallel, and
also the pair `p₃ p₂` and `p₆ p₅` of corresponding lines is parallel, and also (
roughly) the third
pair of lines `p₁ p₃` and `p₄ p₆` are the same line, then the two angles are equ
al.  This is a
stronger version of `two_zsmul_oangle_of_parallel`, which shows that the two ang
les are equal mod
`π` in the absence of the condition on the third pair of lines.
-/
theorem oangle_eq_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[ℝ, p₁, p₃])
    (h₄ : p₄ ∈ line[ℝ, p₁, p₃]) (h₆ : p₆ ∈ line[ℝ, p₁, p₃])
    (h₁₂₄₅ : line[ℝ, p₁, p₂] ∥ line[ℝ, p₄, p₅]) (h₃₂₆₅ : line[ℝ, p₃, p₂] ∥ line[ℝ, p₆, p₅]) :
    ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ := by
  rw [oangle, oangle]
  have hd : line[ℝ, p₆, p₄].direction ≤ line[ℝ, p₃, p₁].direction := by
    rw [Set.pair_comm p₃]
    exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem h₆ h₄)
  obtain ⟨r, hr, h₅₄, h₆₅, -⟩ := exists_eq_smul_of_parallel h₂ h₁₂₄₅
    (Set.pair_comm p₃ p₂ ▸ Set.pair_comm p₆ p₅ ▸ h₃₂₆₅).direction_eq.symm.le hd
  rw [← neg_inj, neg_vsub_eq_vsub_rev, ← smul_neg, neg_vsub_eq_vsub_rev] at h₅₄
  rw [h₅₄, h₆₅]
  rcases hr.lt_or_gt with hlt | hlt
  · simp [-neg_vsub_eq_vsub_rev, hlt]
  · simp [hlt]

/-- Given three points not equal to `p`, the angle between the first and the second at `p` plus
the angle between the second and the third equals the angle between the first and the third. -/
@[simp]
/-
**EuclideanGeometry.oangle_add** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_add {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p
) : ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃
参数：hp₁ : p₁ != p；hp₂ : p₂ != p；hp₃ : p₃ != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_add`：oangle_add {x y z : V} (hx : x != 0) (hy : y != 
0) (hz : z != 0) : o.oangle x y + o.oangle y z = o.oangle x z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
Given three points not equal to `p`, the angle between the first and the second 
at `p` plus
the angle between the second and the third equals the angle between the first an
d the third.
-/
theorem oangle_add {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃ :=
  o.oangle_add (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the second and the third at `p` plus
the angle between the first and the second equals the angle between the first and the third. -/
@[simp]
/-
**EuclideanGeometry.oangle_add_swap** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：oangle_add_swap {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃
 != p) : ∡ p₂ p p₃ + ∡ p₁ p p₂ = ∡ p₁ p p₃
参数：hp₁ : p₁ != p；hp₂ : p₂ != p；hp₃ : p₃ != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_add_swap`：oangle_add_swap {x y z : V} (hx : x != 0) (
hy : y != 0) (hz : z != 0) : o.oangle y z + o.oangle x y = o.oangle x z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
Given three points not equal to `p`, the angle between the second and the third 
at `p` plus
the angle between the first and the second equals the angle between the first an
d the third.
-/
theorem oangle_add_swap {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₂ p p₃ + ∡ p₁ p p₂ = ∡ p₁ p p₃ :=
  o.oangle_add_swap (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the first and the second equals the angle between the second and the third. -/
@[simp]
/-
**EuclideanGeometry.oangle_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：oangle_sub_left {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃
 != p) : ∡ p₁ p p₃ - ∡ p₁ p p₂ = ∡ p₂ p p₃
参数：hp₁ : p₁ != p；hp₂ : p₂ != p；hp₃ : p₃ != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_sub_left`：oangle_sub_left {x y z : V} (hx : x != 0) (
hy : y != 0) (hz : z != 0) : o.oangle x z - o.oangle x y = o.oangle y z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
Given three points not equal to `p`, the angle between the first and the third a
t `p` minus
the angle between the first and the second equals the angle between the second a
nd the third.
-/
theorem oangle_sub_left {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₁ p p₃ - ∡ p₁ p p₂ = ∡ p₂ p p₃ :=
  o.oangle_sub_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the second and the third equals the angle between the first and the second. -/
@[simp]
/-
**EuclideanGeometry.oangle_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：oangle_sub_right {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p
₃ != p) : ∡ p₁ p p₃ - ∡ p₂ p p₃ = ∡ p₁ p p₂
参数：hp₁ : p₁ != p；hp₂ : p₂ != p；hp₃ : p₃ != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_sub_right`：oangle_sub_right {x y z : V} (hx : x != 0)
 (hy : y != 0) (hz : z != 0) : o.oangle x z - o.oangle y z = o.oangle x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
Given three points not equal to `p`, the angle between the first and the third a
t `p` minus
the angle between the second and the third equals the angle between the first an
d the second.
-/
theorem oangle_sub_right {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₁ p p₃ - ∡ p₂ p p₃ = ∡ p₁ p p₂ :=
  o.oangle_sub_right (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, adding the angles between them at `p` in cyclic order
results in 0. -/
/-
**EuclideanGeometry.oangle_add_cyc3** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：oangle_add_cyc3 {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃
 != p) : ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0
参数：hp₁ : p₁ != p；hp₂ : p₂ != p；hp₃ : p₃ != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_add`：oangle_add {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p
) (hp₂ : p₂ != p) (hp₃ : p₃ != p) : ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EuclideanGeometry.oangle_add_oangle_rev`：oangle_add_oangle_rev (p₁ p₂ p₃
 : P) : ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given three points not equal to `p`, adding the angles between them at `p` in cy
clic order
results in 0.
-/
theorem oangle_add_cyc3 {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0 := by
  simp [*]

/-- Pons asinorum, oriented angle-at-point form. -/
/-
**EuclideanGeometry.oangle_eq_oangle_of_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
形式化陈述：oangle_eq_oangle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
 ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁
参数：h : dist p₁ p₂ = dist p₁ p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `Orientation.oangle_sub_eq_oangle_sub_rev_of_norm_eq`：oangle_sub_eq_oangl
e_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : o.oangle x (x - y) = o.oangle (
y - x) y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖

--- 原说明 ---
Pons asinorum, oriented angle-at-point form.
-/
theorem oangle_eq_oangle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
    ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁ := by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle, oangle, ← vsub_sub_vsub_cancel_left p₃ p₂ p₁, ← vsub_sub_vsub_cancel_left p₂ p₃ p₁,
    o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form. -/
/-
**EuclideanGeometry.oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq {p₁ p₂ p₃ : P} (hn : p₂ != p₃
) (h : dist p₁ p₂ = dist p₁ p₃) : ∡ p₃ p₁ p₂ = π - (2 : Int) • ∡ p₁ p₂ p₃
参数：hn : p₂ != p₃；h : dist p₁ p₂ = dist p₁ p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Orientation.oangle_neg_neg`：oangle_neg_neg (x y : V) : o.oangle (-x) (-y
) = o.oangle x y
· 使用定理 `Orientation.oangle_sub_eq_oangle_sub_rev_of_norm_eq`：oangle_sub_eq_oangl
e_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : o.oangle x (x - y) = o.oangle (
y - x) y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq`：oangle_eq_
pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x != y) (h : ‖x‖ = ‖y‖) :
 o.oangle y x = π - (2 : Int) • o.oangle (y - x) y

--- 原说明 ---
The angle at the apex of an isosceles triangle is `π` minus twice a base angle, 
oriented
angle-at-point form.
-/
theorem oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq {p₁ p₂ p₃ : P} (hn : p₂ ≠ p₃)
    (h : dist p₁ p₂ = dist p₁ p₃) : ∡ p₃ p₁ p₂ = π - (2 : ℤ) • ∡ p₁ p₂ p₃ := by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle, oangle]
  convert! o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq _ h using 1
  · rw [← neg_vsub_eq_vsub_rev p₁ p₃, ← neg_vsub_eq_vsub_rev p₁ p₂, o.oangle_neg_neg]
  · rw [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]; simp
  · simpa using hn

/-- A base angle of an isosceles triangle is acute, oriented angle-at-point form. -/
/-
**EuclideanGeometry.abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist 
p₁ p₂ = dist p₁ p₃) : |(∡ p₁ p₂ p₃).toReal| < π / 2
参数：h : dist p₁ p₂ = dist p₁ p₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `Orientation.abs_oangle_sub_right_toReal_lt_pi_div_two`：abs_oangle_sub_ri
ght_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) : |(o.oangle x (x - y)).toRea
l| < π / 2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖

--- 原说明 ---
A base angle of an isosceles triangle is acute, oriented angle-at-point form.
-/
theorem abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P}
    (h : dist p₁ p₂ = dist p₁ p₃) : |(∡ p₁ p₂ p₃).toReal| < π / 2 := by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle, ← vsub_sub_vsub_cancel_left p₃ p₂ p₁]
  exact o.abs_oangle_sub_right_toReal_lt_pi_div_two h

/-- A base angle of an isosceles triangle is acute, oriented angle-at-point form. -/
/-
**EuclideanGeometry.abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq** 是 Mathlib 
中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p
₁ p₂ = dist p₁ p₃) : |(∡ p₂ p₃ p₁).toReal| < π / 2
参数：h : dist p₁ p₂ = dist p₁ p₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq`：abs_
oangle_right_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = di
st p₁ p₃) : |(∡ p₁ p₂ p₃).toReal| < π / 2
· 使用定理 `EuclideanGeometry.oangle_eq_oangle_of_dist_eq`：oangle_eq_oangle_of_dist_
eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) : ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁

--- 原说明 ---
A base angle of an isosceles triangle is acute, oriented angle-at-point form.
-/
theorem abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P}
    (h : dist p₁ p₂ = dist p₁ p₃) : |(∡ p₂ p₃ p₁).toReal| < π / 2 :=
  oangle_eq_oangle_of_dist_eq h ▸ abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq h

/-- The cosine of the oriented angle at `p` between two points not equal to `p` equals that of the
unoriented angle. -/
/-
**EuclideanGeometry.cos_oangle_eq_cos_angle** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry`。
形式化陈述：cos_oangle_eq_cos_angle {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) : Re
al.Angle.cos (∡ p₁ p p₂) = Real.cos (∠ p₁ p p₂)
参数：hp₁ : p₁ != p；hp₂ : p₂ != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.cos_oangle_eq_cos_angle`：cos_oangle_eq_cos_angle {x y : V} (
hx : x != 0) (hy : y != 0) : Real.Angle.cos (o.oangle x y) = Real.cos (InnerProd
uctGeometry.angle x y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
The cosine of the oriented angle at `p` between two points not equal to `p` equa
ls that of the
unoriented angle.
-/
theorem cos_oangle_eq_cos_angle {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
    Real.Angle.cos (∡ p₁ p p₂) = Real.cos (∠ p₁ p p₂) :=
  o.cos_oangle_eq_cos_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- The oriented angle at `p` between two points not equal to `p` is plus or minus the unoriented
angle. -/
/-
**EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：oangle_eq_angle_or_eq_neg_angle {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ !=
 p) : ∡ p₁ p p₂ = ∠ p₁ p p₂ ∨ ∡ p₁ p p₂ = -∠ p₁ p p₂
参数：hp₁ : p₁ != p；hp₂ : p₂ != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_angle_or_eq_neg_angle`：oangle_eq_angle_or_eq_neg_a
ngle {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle x y = InnerProductGeometry
.angle x y ∨ o.oangle x y = -Inne…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
The oriented angle at `p` between two points not equal to `p` is plus or minus t
he unoriented
angle.
-/
theorem oangle_eq_angle_or_eq_neg_angle {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
    ∡ p₁ p p₂ = ∠ p₁ p p₂ ∨ ∡ p₁ p p₂ = -∠ p₁ p p₂ :=
  o.oangle_eq_angle_or_eq_neg_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- The unoriented angle at `p` between two points not equal to `p` is the absolute value of the
oriented angle. -/
/-
**EuclideanGeometry.angle_eq_abs_oangle_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：angle_eq_abs_oangle_toReal {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) :
 ∠ p₁ p p₂ = |(∡ p₁ p p₂).toReal|
参数：hp₁ : p₁ != p；hp₂ : p₂ != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.angle_eq_abs_oangle_toReal`：angle_eq_abs_oangle_toReal {x y 
: V} (hx : x != 0) (hy : y != 0) : InnerProductGeometry.angle x y = |(o.oangle x
 y).toReal|
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
The unoriented angle at `p` between two points not equal to `p` is the absolute 
value of the
oriented angle.
-/
theorem angle_eq_abs_oangle_toReal {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
    ∠ p₁ p p₂ = |(∡ p₁ p p₂).toReal| :=
  o.angle_eq_abs_oangle_toReal (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- If the sign of the oriented angle at `p` between two points is zero, either one of the points
equals `p` or the unoriented angle is 0 or π. -/
/-
**EuclideanGeometry.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero** 是 Ma
thlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {p p₁ p₂ : P} (h : (
∡ p₁ p p₂).sign = 0) : p₁ = p ∨ p₂ = p ∨ ∠ p₁ p p₂ = 0 ∨ ∠ p₁ p p₂ = π
参数：h : (∡ p₁ p p₂).sign = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Orientation.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero`：eq_ze
ro_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {x y : V} (h : (o.oangle x y).s
ign = 0) : x = 0 ∨ y = 0 ∨ InnerProductGeometry.angle x…

--- 原说明 ---
If the sign of the oriented angle at `p` between two points is zero, either one 
of the points
equals `p` or the unoriented angle is 0 or π.
-/
theorem eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {p p₁ p₂ : P}
    (h : (∡ p₁ p p₂).sign = 0) : p₁ = p ∨ p₂ = p ∨ ∠ p₁ p p₂ = 0 ∨ ∠ p₁ p p₂ = π := by
  convert! o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h <;> simp

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
equal, then the oriented angles are equal (even in degenerate cases). -/
/-
**EuclideanGeometry.oangle_eq_of_angle_eq_of_sign_eq** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：oangle_eq_of_angle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ =
 ∠ p₄ p₅ p₆) (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) : ∡ p₁ p₂ p₃ = ∡ p₄ p₅
 p₆
参数：h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆；hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_of_angle_eq_of_sign_eq`：oangle_eq_of_angle_eq_of_s
ign_eq {w x y z : V} (h : InnerProductGeometry.angle w x = InnerProductGeometry.
angle y z) (hs : (o.oangle w x).si…

--- 原说明 ---
If two unoriented angles are equal, and the signs of the corresponding oriented 
angles are
equal, then the oriented angles are equal (even in degenerate cases).
-/
theorem oangle_eq_of_angle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
    (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) : ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
  o.oangle_eq_of_angle_eq_of_sign_eq h hs

/-- If the signs of two nondegenerate oriented angles between points are equal, the oriented
angles are equal if and only if the unoriented angles are equal. -/
/-
**EuclideanGeometry.angle_eq_iff_oangle_eq_of_sign_eq** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：angle_eq_iff_oangle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ != p₂)
 (hp₃ : p₃ != p₂) (hp₄ : p₄ != p₅) (hp₆ : p₆ != p₅) (hs : (∡ p₁ p₂ p₃).sign = (∡
 p₄ p₅ p₆).sign) : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆
参数：hp₁ : p₁ != p₂；hp₃ : p₃ != p₂；hp₄ : p₄ != p₅；hp₆ : p₆ != p₅；hs : (∡ p₁ p₂ p₃)
.sign = (∡ p₄ p₅ p₆).sign。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.angle_eq_iff_oangle_eq_of_sign_eq`：angle_eq_iff_oangle_eq_of
_sign_eq {w x y z : V} (hw : w != 0) (hx : x != 0) (hy : y != 0) (hz : z != 0) (
hs : (o.oangle w x).sign = (o.oangl…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
If the signs of two nondegenerate oriented angles between points are equal, the 
oriented
angles are equal if and only if the unoriented angles are equal.
-/
theorem angle_eq_iff_oangle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ ≠ p₂) (hp₃ : p₃ ≠ p₂)
    (hp₄ : p₄ ≠ p₅) (hp₆ : p₆ ≠ p₅) (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) :
    ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
  o.angle_eq_iff_oangle_eq_of_sign_eq (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃) (vsub_ne_zero.2 hp₄)
    (vsub_ne_zero.2 hp₆) hs

/-- The oriented angle are equal or opposite if the unoriented angles are equal. -/
/-
**EuclideanGeometry.oangle_eq_or_eq_neg_of_angle_eq** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：oangle_eq_or_eq_neg_of_angle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = 
∠ p₄ p₅ p₆) (h1 : p₂ != p₁) (h2 : p₂ != p₃) (h3 : p₅ != p₄) (h4 : p₅ != p₆) : ∡ 
p₁ p₂ p₃ = ∡ p₄ p₅ p₆ ∨ ∡ p₁ p₂ p₃ = - ∡ p₄ p₅ p₆
参数：h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆；h1 : p₂ != p₁；h2 : p₂ != p₃；h3 : p₅ != p₄；h4 : p₅
 != p₆。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle`：oangle_eq_angle_or_eq
_neg_angle {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) : ∡ p₁ p p₂ = ∠ p₁ p p₂
 ∨ ∡ p₁ p p₂ = -∠ p₁ p p₂
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
The oriented angle are equal or opposite if the unoriented angles are equal.
-/
theorem oangle_eq_or_eq_neg_of_angle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
    (h1 : p₂ ≠ p₁) (h2 : p₂ ≠ p₃) (h3 : p₅ ≠ p₄) (h4 : p₅ ≠ p₆) :
    ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ ∨ ∡ p₁ p₂ p₃ = - ∡ p₄ p₅ p₆ := by
  have h_1 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h1.symm h2.symm
  have h_2 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h3.symm h4.symm
  rcases h_1 with h₁ | h₁ <;> rcases h_2 with h₂ | h₂
  · left
    rw [h₁, h₂, h]
  · right
    rw [h₁, h₂, h, neg_neg]
  · right
    rw [h₁, h₂, h]
  · left
    rw [h₁, h₂, h]

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
negations of each other, then the oriented angles are negations of each other (even in degenerate
cases). -/
/-
**EuclideanGeometry.oangle_eq_neg_of_angle_eq_of_sign_eq_neg** 是 Mathlib 中的一个引理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_eq_neg_of_angle_eq_of_sign_eq_neg {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁
 p₂ p₃ = ∠ p₄ p₅ p₆) (hs : (∡ p₁ p₂ p₃).sign = -(∡ p₄ p₅ p₆).sign) : ∡ p₁ p₂ p₃ 
= -∡ p₄ p₅ p₆
参数：h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆；hs : (∡ p₁ p₂ p₃).sign = -(∡ p₄ p₅ p₆).sign。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Orientation.oangle_eq_neg_of_angle_eq_of_sign_eq_neg`：oangle_eq_neg_of_a
ngle_eq_of_sign_eq_neg {w x y z : V} (h : InnerProductGeometry.angle w x = Inner
ProductGeometry.angle y z) (hs : (o.oangle…

--- 原说明 ---
If two unoriented angles are equal, and the signs of the corresponding oriented 
angles are
negations of each other, then the oriented angles are negations of each other (e
ven in degenerate
cases).
-/
lemma oangle_eq_neg_of_angle_eq_of_sign_eq_neg {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆) (hs : (∡ p₁ p₂ p₃).sign = -(∡ p₄ p₅ p₆).sign) :
    ∡ p₁ p₂ p₃ = -∡ p₄ p₅ p₆ :=
  o.oangle_eq_neg_of_angle_eq_of_sign_eq_neg h hs

/-- If the signs of two nondegenerate oriented angles between points are negations of each other,
the oriented angles are negations of each other if and only if the unoriented angles are equal. -/
/-
**EuclideanGeometry.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg** 是 Mathlib 中的一个引理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_iff_oangle_eq_neg_of_sign_eq_neg {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p
₁ != p₂) (hp₃ : p₃ != p₂) (hp₄ : p₄ != p₅) (hp₆ : p₆ != p₅) (hs : (∡ p₁ p₂ p₃).s
ign = -(∡ p₄ p₅ p₆).sign) : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = -∡ p₄ p₅ p₆
参数：hp₁ : p₁ != p₂；hp₃ : p₃ != p₂；hp₄ : p₄ != p₅；hp₆ : p₆ != p₅；hs : (∡ p₁ p₂ p₃)
.sign = -(∡ p₄ p₅ p₆).sign。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Orientation.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg`：angle_eq_iff_oang
le_eq_neg_of_sign_eq_neg {w x y z : V} (hw : w != 0) (hx : x != 0) (hy : y != 0)
 (hz : z != 0) (hs : (o.oangle w x).sign = …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
If the signs of two nondegenerate oriented angles between points are negations o
f each other,
the oriented angles are negations of each other if and only if the unoriented an
gles are equal.
-/
lemma angle_eq_iff_oangle_eq_neg_of_sign_eq_neg {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ ≠ p₂)
    (hp₃ : p₃ ≠ p₂) (hp₄ : p₄ ≠ p₅) (hp₆ : p₆ ≠ p₅) (hs : (∡ p₁ p₂ p₃).sign = -(∡ p₄ p₅ p₆).sign) :
    ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = -∡ p₄ p₅ p₆ :=
  o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃)
    (vsub_ne_zero.2 hp₄) (vsub_ne_zero.2 hp₆) hs

/-- The oriented angle between three points equals the unoriented angle if the sign is
positive. -/
/-
**EuclideanGeometry.oangle_eq_angle_of_sign_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：oangle_eq_angle_of_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) 
: ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
参数：h : (∡ p₁ p₂ p₃).sign = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y

--- 原说明 ---
The oriented angle between three points equals the unoriented angle if the sign 
is
positive.
-/
theorem oangle_eq_angle_of_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) :
    ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃ :=
  o.oangle_eq_angle_of_sign_eq_one h

/-- The oriented angle between three points equals minus the unoriented angle if the sign is
negative. -/
/-
**EuclideanGeometry.oangle_eq_neg_angle_of_sign_eq_neg_one** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry`。
形式化陈述：oangle_eq_neg_angle_of_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).si
gn = -1) : ∡ p₁ p₂ p₃ = -∠ p₁ p₂ p₃
参数：h : (∡ p₁ p₂ p₃).sign = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_neg_angle_of_sign_eq_neg_one`：oangle_eq_neg_angle_
of_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : o.oangle x y = -In
nerProductGeometry.angle x y

--- 原说明 ---
The oriented angle between three points equals minus the unoriented angle if the
 sign is
negative.
-/
theorem oangle_eq_neg_angle_of_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) :
    ∡ p₁ p₂ p₃ = -∠ p₁ p₂ p₃ :=
  o.oangle_eq_neg_angle_of_sign_eq_neg_one h

/-- The unoriented angle at `p` between two points not equal to `p` is zero if and only if the
unoriented angle is zero. -/
/-
**EuclideanGeometry.oangle_eq_zero_iff_angle_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：oangle_eq_zero_iff_angle_eq_zero {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ !
= p) : ∡ p₁ p p₂ = 0 ↔ ∠ p₁ p p₂ = 0
参数：hp₁ : p₁ != p；hp₂ : p₂ != p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_zero_iff_angle_eq_zero`：oangle_eq_zero_iff_angle_e
q_zero {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle x y = 0 ↔ InnerProductGe
ometry.angle x y = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
The unoriented angle at `p` between two points not equal to `p` is zero if and o
nly if the
unoriented angle is zero.
-/
theorem oangle_eq_zero_iff_angle_eq_zero {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
    ∡ p₁ p p₂ = 0 ↔ ∠ p₁ p p₂ = 0 :=
  o.oangle_eq_zero_iff_angle_eq_zero (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- The oriented angle between three points is `π` if and only if the unoriented angle is `π`. -/
/-
**EuclideanGeometry.oangle_eq_pi_iff_angle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：oangle_eq_pi_iff_angle_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ 
= π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_pi_iff_angle_eq_pi`：oangle_eq_pi_iff_angle_eq_pi {
x y : V} : o.oangle x y = π ↔ InnerProductGeometry.angle x y = π

--- 原说明 ---
The oriented angle between three points is `π` if and only if the unoriented ang
le is `π`.
-/
theorem oangle_eq_pi_iff_angle_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ = π :=
  o.oangle_eq_pi_iff_angle_eq_pi

/-- If the oriented angle between three points is `π / 2`, so is the unoriented angle. -/
/-
**EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个
定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃
 = ↑(π / 2)) : ∠ p₁ p₂ p₃ = π / 2
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0

--- 原说明 ---
If the oriented angle between three points is `π / 2`, so is the unoriented angl
e.
-/
theorem angle_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∠ p₁ p₂ p₃ = π / 2 := by
  rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact o.inner_eq_zero_of_oangle_eq_pi_div_two h

/-- If the oriented angle between three points is `π / 2`, so is the unoriented angle
(reversed). -/
/-
**EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p
₂ p₃ = ↑(π / 2)) : ∠ p₃ p₂ p₁ = π / 2
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2

--- 原说明 ---
If the oriented angle between three points is `π / 2`, so is the unoriented angl
e
(reversed).
-/
theorem angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∠ p₃ p₂ p₁ = π / 2 := by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_pi_div_two h

/-- If the oriented angle between three points is `-π / 2`, the unoriented angle is `π / 2`. -/
/-
**EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p
₂ p₃ = ↑(-π / 2)) : ∠ p₁ p₂ p₃ = π / 2
参数：h : ∡ p₁ p₂ p₃ = ↑(-π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_neg_pi_div_two`：inner_eq_zero_of_
oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : Real)) : ⟪x, y⟫
 = 0

--- 原说明 ---
If the oriented angle between three points is `-π / 2`, the unoriented angle is 
`π / 2`.
-/
theorem angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₁ p₂ p₃ = π / 2 := by
  rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h

/-- If the oriented angle between three points is `-π / 2`, the unoriented angle (reversed) is
`π / 2`. -/
/-
**EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two** 是 Math
lib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ 
p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₃ p₂ p₁ = π / 2
参数：h : ∡ p₁ p₂ p₃ = ↑(-π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two`：angle
_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(-π
 / 2)) : ∠ p₁ p₂ p₃ = π / 2

--- 原说明 ---
If the oriented angle between three points is `-π / 2`, the unoriented angle (re
versed) is
`π / 2`.
-/
theorem angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₃ p₂ p₁ = π / 2 := by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two h

/-- Swapping the first and second points in an oriented angle negates the sign of that angle. -/
/-
**EuclideanGeometry.oangle_swap** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Swapping the first and second points in an oriented angle negates the sign of th
at angle.
-/
theorem oangle_swap₁₂_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₂ p₁ p₃).sign := by
  rw [eq_comm, oangle, oangle, ← o.oangle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, ←
    vsub_sub_vsub_cancel_left p₁ p₃ p₂, ← neg_vsub_eq_vsub_rev p₃ p₂, sub_eq_add_neg,
    neg_vsub_eq_vsub_rev p₂ p₁, add_comm, ← @neg_one_smul ℝ]
  nth_rw 2 [← one_smul ℝ (p₁ -ᵥ p₂)]
  rw [o.oangle_sign_smul_add_smul_right]
  simp

/-- Swapping the first and third points in an oriented angle negates the sign of that angle. -/
/-
**EuclideanGeometry.oangle_swap** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Swapping the first and third points in an oriented angle negates the sign of tha
t angle.
-/
theorem oangle_swap₁₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₃ p₂ p₁).sign := by
  rw [oangle_rev, Real.Angle.sign_neg, neg_neg]

/-- Swapping the second and third points in an oriented angle negates the sign of that angle. -/
/-
**EuclideanGeometry.oangle_swap** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Swapping the second and third points in an oriented angle negates the sign of th
at angle.
-/
theorem oangle_swap₂₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign := by
  rw [oangle_swap₁₃_sign, ← oangle_swap₁₂_sign, oangle_swap₁₃_sign]

/-- Rotating the points in an oriented angle does not change the sign of that angle. -/
/-
**EuclideanGeometry.oangle_rotate_sign** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
形式化陈述：oangle_rotate_sign (p₁ p₂ p₃ : P) : (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_swap₁₂_sign`：oangle_swap₁₂_sign (p₁ p₂ p₃ : P) 
: -(∡ p₁ p₂ p₃).sign = (∡ p₂ p₁ p₃).sign
· 使用定理 `EuclideanGeometry.oangle_swap₁₃_sign`：oangle_swap₁₃_sign (p₁ p₂ p₃ : P) 
: -(∡ p₁ p₂ p₃).sign = (∡ p₃ p₂ p₁).sign

--- 原说明 ---
Rotating the points in an oriented angle does not change the sign of that angle.
-/
theorem oangle_rotate_sign (p₁ p₂ p₃ : P) : (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign := by
  rw [← oangle_swap₁₂_sign, oangle_swap₁₃_sign]

/-- The oriented angle between three points is π if and only if the second point is strictly
between the other two. -/
/-
**EuclideanGeometry.oangle_eq_pi_iff_sbtw** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：oangle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_eq_pi_iff_angle_eq_pi`：oangle_eq_pi_iff_angle_e
q_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ = π
· 使用定理 `EuclideanGeometry.angle_eq_pi_iff_sbtw`：angle_eq_pi_iff_sbtw {p₁ p₂ p₃ :
 P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The oriented angle between three points is π if and only if the second point is 
strictly
between the other two.
-/
theorem oangle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃ := by
  rw [oangle_eq_pi_iff_angle_eq_pi, angle_eq_pi_iff_sbtw]

/-- If the second of three points is strictly between the other two, the oriented angle at that
point is π. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the oriented an
gle at that
point is π.
-/
theorem _root_.Sbtw.oangle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₂ p₃ = π :=
  oangle_eq_pi_iff_sbtw.2 h

/-- If the second of three points is strictly between the other two, the oriented angle at that
point (reversed) is π. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the oriented an
gle at that
point (reversed) is π.
-/
theorem _root_.Sbtw.oangle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₂ p₁ = π := by
  rw [oangle_eq_pi_iff_oangle_rev_eq_pi, ← h.oangle₁₂₃_eq_pi]

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point is zero. -/
/-
**EuclideanGeometry._root_.Wbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is weakly between the other two, the oriented angl
e at the
first point is zero.
-/
theorem _root_.Wbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 := by
  by_cases hp₂p₁ : p₂ = p₁; · simp [hp₂p₁]
  by_cases hp₃p₁ : p₃ = p₁; · simp [hp₃p₁]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₂p₁ hp₃p₁]
  exact h.angle₂₁₃_eq_zero_of_ne hp₂p₁

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point is zero. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the oriented an
gle at the
first point is zero.
-/
theorem _root_.Sbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 :=
  h.wbtw.oangle₂₁₃_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point (reversed) is zero. -/
/-
**EuclideanGeometry._root_.Wbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is weakly between the other two, the oriented angl
e at the
first point (reversed) is zero.
-/
theorem _root_.Wbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 := by
  rw [oangle_eq_zero_iff_oangle_rev_eq_zero, h.oangle₂₁₃_eq_zero]

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point (reversed) is zero. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the oriented an
gle at the
first point (reversed) is zero.
-/
theorem _root_.Sbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 :=
  h.wbtw.oangle₃₁₂_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point is zero. -/
/-
**EuclideanGeometry._root_.Wbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is weakly between the other two, the oriented angl
e at the
third point is zero.
-/
theorem _root_.Wbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
  h.symm.oangle₂₁₃_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point is zero. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the oriented an
gle at the
third point is zero.
-/
theorem _root_.Sbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
  h.wbtw.oangle₂₃₁_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point (reversed) is zero. -/
/-
**EuclideanGeometry._root_.Wbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is weakly between the other two, the oriented angl
e at the
third point (reversed) is zero.
-/
theorem _root_.Wbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
  h.symm.oangle₃₁₂_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point (reversed) is zero. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the oriented an
gle at the
third point (reversed) is zero.
-/
theorem _root_.Sbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
  h.wbtw.oangle₁₃₂_eq_zero

/-- The oriented angle between three points is zero if and only if one of the first and third
points is weakly between the other two. -/
/-
**EuclideanGeometry.oangle_eq_zero_iff_wbtw** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry`。
形式化陈述：oangle_eq_zero_iff_wbtw {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ↔ Wbtw Real p₂ p₁ 
p₃ ∨ Wbtw Real p₂ p₃ p₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.oangle.congr_simp`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.oangle_self_left`：oangle_self_left (p₁ p₂ : P) : ∡ p₁ 
p₁ p₂ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `EuclideanGeometry.oangle_self_right`：oangle_self_right (p₁ p₂ : P) : ∡ p
₁ p₂ p₂ = 0
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `EuclideanGeometry.oangle_eq_zero_iff_angle_eq_zero`：oangle_eq_zero_iff_a
ngle_eq_zero {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) : ∡ p₁ p p₂ = 0 ↔ ∠ p
₁ p p₂ = 0
· 使用定理 `EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw`：angle_eq_zero_iff_ne_an
d_wbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = 0 ↔ p₁ != p₂ ∧ Wbtw Real p₂ p₁ p₃ ∨ p₃ != p
₂ ∧ Wbtw Real p₂ p₃ p₁
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
The oriented angle between three points is zero if and only if one of the first 
and third
points is weakly between the other two.
-/
theorem oangle_eq_zero_iff_wbtw {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ = 0 ↔ Wbtw ℝ p₂ p₁ p₃ ∨ Wbtw ℝ p₂ p₃ p₁ := by
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₁p₂ hp₃p₂, angle_eq_zero_iff_ne_and_wbtw]
  simp [hp₁p₂, hp₃p₂]

/-- An oriented angle is unchanged by replacing the first point by one weakly further away on the
same ray. -/
/-
**EuclideanGeometry._root_.Wbtw.oangle_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An oriented angle is unchanged by replacing the first point by one weakly furthe
r away on the
same ray.
-/
theorem _root_.Wbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : Wbtw ℝ p₂ p₁ p₁') (hp₁p₂ : p₁ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ := by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  by_cases hp₁'p₂ : p₁' = p₂; · rw [hp₁'p₂, wbtw_self_iff] at h; exact False.elim (hp₁p₂ h)
  rw [← oangle_add hp₁'p₂ hp₁p₂ hp₃p₂, h.oangle₃₁₂_eq_zero, zero_add]

/-- An oriented angle is unchanged by replacing the first point by one strictly further away on
the same ray. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An oriented angle is unchanged by replacing the first point by one strictly furt
her away on
the same ray.
-/
theorem _root_.Sbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : Sbtw ℝ p₂ p₁ p₁') :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ :=
  h.wbtw.oangle_eq_left h.ne_left

/-- An oriented angle is unchanged by replacing the third point by one weakly further away on the
same ray. -/
/-
**EuclideanGeometry._root_.Wbtw.oangle_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An oriented angle is unchanged by replacing the third point by one weakly furthe
r away on the
same ray.
-/
theorem _root_.Wbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : Wbtw ℝ p₂ p₃ p₃') (hp₃p₂ : p₃ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' := by rw [oangle_rev, h.oangle_eq_left hp₃p₂, ← oangle_rev]

/-- An oriented angle is unchanged by replacing the third point by one strictly further away on
the same ray. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An oriented angle is unchanged by replacing the third point by one strictly furt
her away on
the same ray.
-/
theorem _root_.Sbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : Sbtw ℝ p₂ p₃ p₃') :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' :=
  h.wbtw.oangle_eq_right h.ne_left

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between it and the second point. -/
@[simp]
/-
**EuclideanGeometry.oangle_midpoint_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeo
metry`。
形式化陈述：oangle_midpoint_left (p₁ p₂ p₃ : P) : ∡ (midpoint Real p₁ p₂) p₂ p₃ = ∡ p₁
 p₂ p₃
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle.congr_simp`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `midpoint_self`：midpoint_self (x : P) : midpoint R x x = x
· 使用定理 `EuclideanGeometry.oangle_self_left`：oangle_self_left (p₁ p₂ : P) : ∡ p₁ 
p₁ p₂ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Sbtw.oangle_eq_left`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCo
mmGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 :
 NormedAd…
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Sbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `sbtw_midpoint_of_ne`：sbtw_midpoint_of_ne {x y : P} (h : x != y) : Sbtw R
 x (midpoint R x y) y

--- 原说明 ---
An oriented angle is unchanged by replacing the first point with the midpoint of
 the segment
between it and the second point.
-/
theorem oangle_midpoint_left (p₁ p₂ p₃ : P) : ∡ (midpoint ℝ p₁ p₂) p₂ p₃ = ∡ p₁ p₂ p₃ := by
  by_cases h : p₁ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne ℝ h).symm.oangle_eq_left

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between the second point and that point. -/
@[simp]
/-
**EuclideanGeometry.oangle_midpoint_rev_left** 是 Mathlib 中的一个定理，位于命名空间 `Euclidea
nGeometry`。
形式化陈述：oangle_midpoint_rev_left (p₁ p₂ p₃ : P) : ∡ (midpoint Real p₂ p₁) p₂ p₃ = 
∡ p₁ p₂ p₃
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `EuclideanGeometry.oangle_midpoint_left`：oangle_midpoint_left (p₁ p₂ p₃ :
 P) : ∡ (midpoint Real p₁ p₂) p₂ p₃ = ∡ p₁ p₂ p₃

--- 原说明 ---
An oriented angle is unchanged by replacing the first point with the midpoint of
 the segment
between the second point and that point.
-/
theorem oangle_midpoint_rev_left (p₁ p₂ p₃ : P) : ∡ (midpoint ℝ p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃ := by
  rw [midpoint_comm, oangle_midpoint_left]

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between it and the second point. -/
@[simp]
/-
**EuclideanGeometry.oangle_midpoint_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：oangle_midpoint_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint Real p₃ p₂) = ∡ p
₁ p₂ p₃
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle.congr_simp`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `midpoint_self`：midpoint_self (x : P) : midpoint R x x = x
· 使用定理 `EuclideanGeometry.oangle_self_right`：oangle_self_right (p₁ p₂ : P) : ∡ p
₁ p₂ p₂ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Sbtw.oangle_eq_right`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddC
ommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 
: NormedAd…
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Sbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `sbtw_midpoint_of_ne`：sbtw_midpoint_of_ne {x y : P} (h : x != y) : Sbtw R
 x (midpoint R x y) y

--- 原说明 ---
An oriented angle is unchanged by replacing the third point with the midpoint of
 the segment
between it and the second point.
-/
theorem oangle_midpoint_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint ℝ p₃ p₂) = ∡ p₁ p₂ p₃ := by
  by_cases h : p₃ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne ℝ h).symm.oangle_eq_right

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between the second point and that point. -/
@[simp]
/-
**EuclideanGeometry.oangle_midpoint_rev_right** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anGeometry`。
形式化陈述：oangle_midpoint_rev_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint Real p₂ p₃) =
 ∡ p₁ p₂ p₃
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `EuclideanGeometry.oangle_midpoint_right`：oangle_midpoint_right (p₁ p₂ p₃
 : P) : ∡ p₁ p₂ (midpoint Real p₃ p₂) = ∡ p₁ p₂ p₃

--- 原说明 ---
An oriented angle is unchanged by replacing the third point with the midpoint of
 the segment
between the second point and that point.
-/
theorem oangle_midpoint_rev_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint ℝ p₂ p₃) = ∡ p₁ p₂ p₃ := by
  rw [midpoint_comm, oangle_midpoint_right]

/-- Replacing the first point by one on the same line but the opposite ray adds π to the oriented
angle. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_eq_add_pi_left** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replacing the first point by one on the same line but the opposite ray adds π to
 the oriented
angle.
-/
theorem _root_.Sbtw.oangle_eq_add_pi_left
    {p₁ p₁' p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₁') (hp₃p₂ : p₃ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ + π := by
  rw [← h.oangle₁₂₃_eq_pi, oangle_add_swap h.left_ne h.right_ne hp₃p₂]

/-- Replacing the third point by one on the same line but the opposite ray adds π to the oriented
angle. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_eq_add_pi_right** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replacing the third point by one on the same line but the opposite ray adds π to
 the oriented
angle.
-/
theorem _root_.Sbtw.oangle_eq_add_pi_right
    {p₁ p₂ p₃ p₃' : P} (h : Sbtw ℝ p₃ p₂ p₃') (hp₁p₂ : p₁ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' + π := by
  rw [← h.oangle₃₂₁_eq_pi, oangle_add hp₁p₂ h.right_ne h.left_ne]

/-- Replacing both the first and third points by ones on the same lines but the opposite rays
does not change the oriented angle (vertically opposite angles). -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_eq_left_right** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replacing both the first and third points by ones on the same lines but the oppo
site rays
does not change the oriented angle (vertically opposite angles).
-/
theorem _root_.Sbtw.oangle_eq_left_right {p₁ p₁' p₂ p₃ p₃' : P} (h₁ : Sbtw ℝ p₁ p₂ p₁')
    (h₃ : Sbtw ℝ p₃ p₂ p₃') : ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃' := by
  rw [h₁.oangle_eq_add_pi_left h₃.left_ne, h₃.oangle_eq_add_pi_right h₁.right_ne, add_assoc,
    Real.Angle.coe_pi_add_coe_pi, add_zero]
/-
**EuclideanGeometry.oangle_pointReflection_right** 是 Mathlib 中的一个引理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：oangle_pointReflection_right {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != 
p₂) : ∡ p₁ p₂ (AffineEquiv.pointReflection Real p₂ p₃) = ∡ p₁ p₂ p₃ + π
参数：h₁₂ : p₁ != p₂；h₃₂ : p₃ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineEquiv.pointReflection_self`：pointReflection_self (x : P₁) : pointR
eflection k x x = x
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `AffineEquiv.injective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} 
{V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [in
st_2 : AddC…
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `EuclideanGeometry.oangle_sub_left`：oangle_sub_left {p p₁ p₂ p₃ : P} (hp₁
 : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p) : ∡ p₁ p p₃ - ∡ p₁ p p₂ = ∡ p₂ p p₃
· 使用定理 `Sbtw.oangle₁₂₃_eq_pi`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddC
ommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 
: NormedAd…
· 使用定理 `sbtw_pointReflection_of_ne`：sbtw_pointReflection_of_ne {x y : P} (h : x 
!= y) : Sbtw R y x (pointReflection R x y)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma oangle_pointReflection_right {p₁ p₂ p₃ : P} (h₁₂ : p₁ ≠ p₂) (h₃₂ : p₃ ≠ p₂) :
    ∡ p₁ p₂ (AffineEquiv.pointReflection ℝ p₂ p₃) = ∡ p₁ p₂ p₃ + π := by
  have h₂₃' : (AffineEquiv.pointReflection ℝ p₂) p₃ ≠ p₂ := by
    conv_rhs => rw [← AffineEquiv.pointReflection_self ℝ p₂]
    rw [(AffineEquiv.pointReflection ℝ p₂).injective.ne_iff]
    exact h₃₂
  rw [← sub_eq_iff_eq_add', oangle_sub_left h₁₂ h₃₂ h₂₃']
  exact Sbtw.oangle₁₂₃_eq_pi <| sbtw_pointReflection_of_ne ℝ h₃₂.symm
/-
**EuclideanGeometry.oangle_pointReflection_left** 是 Mathlib 中的一个引理，位于命名空间 `Eucli
deanGeometry`。
形式化陈述：oangle_pointReflection_left {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p
₂) : ∡ (AffineEquiv.pointReflection Real p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃ + π
参数：h₁₂ : p₁ != p₂；h₃₂ : p₃ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rev`：oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -
∡ p₁ p₂ p₃
· 使用引理 `EuclideanGeometry.oangle_pointReflection_right`：oangle_pointReflection_r
ight {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂) : ∡ p₁ p₂ (AffineEquiv.poi
ntReflection Real p₂ p₃) = ∡ p₁ p₂ p…
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma oangle_pointReflection_left {p₁ p₂ p₃ : P} (h₁₂ : p₁ ≠ p₂) (h₃₂ : p₃ ≠ p₂) :
    ∡ (AffineEquiv.pointReflection ℝ p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃ + π := by
  rw [oangle_rev, oangle_pointReflection_right h₃₂ h₁₂, neg_add, ← oangle_rev]
  simp

/-- Replacing the first point by one on the same line does not change twice the oriented angle. -/
/-
**EuclideanGeometry._root_.Collinear.two_zsmul_oangle_eq_left** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replacing the first point by one on the same line does not change twice the orie
nted angle.
-/
theorem _root_.Collinear.two_zsmul_oangle_eq_left {p₁ p₁' p₂ p₃ : P}
    (h : Collinear ℝ ({p₁, p₂, p₁'} : Set P)) (hp₁p₂ : p₁ ≠ p₂) (hp₁'p₂ : p₁' ≠ p₂) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁' p₂ p₃ := by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · have hw' : Sbtw ℝ p₁ p₂ p₁' := ⟨hw, hp₁p₂.symm, hp₁'p₂.symm⟩
    rw [hw'.oangle_eq_add_pi_left hp₃p₂, smul_add, Real.Angle.two_zsmul_coe_pi, add_zero]
  · rw [hw.oangle_eq_left hp₁'p₂]
  · rw [hw.symm.oangle_eq_left hp₁p₂]

/-- Replacing the third point by one on the same line does not change twice the oriented angle. -/
/-
**EuclideanGeometry._root_.Collinear.two_zsmul_oangle_eq_right** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replacing the third point by one on the same line does not change twice the orie
nted angle.
-/
theorem _root_.Collinear.two_zsmul_oangle_eq_right {p₁ p₂ p₃ p₃' : P}
    (h : Collinear ℝ ({p₃, p₂, p₃'} : Set P)) (hp₃p₂ : p₃ ≠ p₂) (hp₃'p₂ : p₃' ≠ p₂) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃' := by
  rw [oangle_rev, smul_neg, h.two_zsmul_oangle_eq_left hp₃p₂ hp₃'p₂, ← smul_neg, ← oangle_rev]

/-- Two different points are equidistant from a third point if and only if that third point
equals some multiple of a `π / 2` rotation of the vector between those points, plus the midpoint
of those points. -/
/-
**EuclideanGeometry.dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint** 是 Ma
thlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint {p₁ p₂ p : P} (h : p
₁ != p₂) : dist p₁ p = dist p₂ p ↔ exists r : Real, r • o.rotation (π / 2 : Real
) (p₂ -ᵥ p₁) +ᵥ midpoint Real p₁ p₂ = p
参数：h : p₁ != p₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_midpoint`：vsub_midpoint (p₁ p₂ p : P) : p -ᵥ midpoint R p₁ p₂ = (⅟2
 : R) • (p -ᵥ p₁) + (⅟2 : R) • (p -ᵥ p₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
· 使用定理 `mul_self_inj`：mul_self_inj [PosMulStrictMono R] [MulPosMono R] {a b : R}
 (h1 : 0 <= a) (h2 : 0 <= b) : a * a = b * b ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `_private.Mathlib.Geometry.Euclidean.Angle.Oriented.Affine.0.EuclideanGeo
metry.dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint._abel_1_1`：∀ {V : Ty
pe u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace
 ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two`：in
ner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two {x y : V} : ⟪x, y⟫ = 0 ↔ 
x = 0 ∨ exists r : Real, r • o.rotation (π / 2 : Real) x =…
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `left_vsub_midpoint`：left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁
 p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Two different points are equidistant from a third point if and only if that thir
d point
equals some multiple of a `π / 2` rotation of the vector between those points, p
lus the midpoint
of those points.
-/
theorem dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint {p₁ p₂ p : P} (h : p₁ ≠ p₂) :
    dist p₁ p = dist p₂ p ↔
      ∃ r : ℝ, r • o.rotation (π / 2 : ℝ) (p₂ -ᵥ p₁) +ᵥ midpoint ℝ p₁ p₂ = p := by
  refine ⟨fun hd => ?_, fun hr => ?_⟩
  · have hi : ⟪p₂ -ᵥ p₁, p -ᵥ midpoint ℝ p₁ p₂⟫ = 0 := by
      rw [@dist_eq_norm_vsub' V, @dist_eq_norm_vsub' V, ←
        mul_self_inj (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_mul_norm, ←
        real_inner_self_eq_norm_mul_norm] at hd
      simp_rw [vsub_midpoint, ← vsub_sub_vsub_cancel_left p₂ p₁ p, inner_sub_left, inner_add_right,
        inner_smul_right, hd, real_inner_comm (p -ᵥ p₁)]
      abel
    rw [@Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two V _ _ _ o,
      or_iff_right (vsub_ne_zero.2 h.symm)] at hi
    rcases hi with ⟨r, hr⟩
    rw [eq_comm, ← eq_vadd_iff_vsub_eq] at hr
    exact ⟨r, hr.symm⟩
  · rcases hr with ⟨r, rfl⟩
    simp_rw [@dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, left_vsub_midpoint, right_vsub_midpoint,
      invOf_eq_inv, ← neg_vsub_eq_vsub_rev p₂ p₁, ← mul_self_inj (norm_nonneg _) (norm_nonneg _), ←
      real_inner_self_eq_norm_mul_norm, inner_sub_sub_self]
    simp [-neg_vsub_eq_vsub_rev]

open AffineSubspace

/-- Given two pairs of distinct points on the same line, such that the vectors between those
pairs of points are on the same ray (oriented in the same direction on that line), and a fifth
point, the angles at the fifth point between each of those two pairs of points have the same
sign. -/
/-
**EuclideanGeometry._root_.Collinear.oangle_sign_of_sameRay_vsub** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two pairs of distinct points on the same line, such that the vectors betwe
en those
pairs of points are on the same ray (oriented in the same direction on that line
), and a fifth
point, the angles at the fifth point between each of those two pairs of points h
ave the same
sign.
-/
theorem _root_.Collinear.oangle_sign_of_sameRay_vsub {p₁ p₂ p₃ p₄ : P} (p₅ : P) (hp₁p₂ : p₁ ≠ p₂)
    (hp₃p₄ : p₃ ≠ p₄) (hc : Collinear ℝ ({p₁, p₂, p₃, p₄} : Set P))
    (hr : SameRay ℝ (p₂ -ᵥ p₁) (p₄ -ᵥ p₃)) : (∡ p₁ p₅ p₂).sign = (∡ p₃ p₅ p₄).sign := by
  by_cases hc₅₁₂ : Collinear ℝ ({p₅, p₁, p₂} : Set P)
  · have hc₅₁₂₃₄ : Collinear ℝ ({p₅, p₁, p₂, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hp₁p₂).2 hc₅₁₂
    have hc₅₃₄ : Collinear ℝ ({p₅, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_singleton _)))) hp₃p₄).1 hc₅₁₂₃₄
    rw [Set.insert_comm] at hc₅₁₂ hc₅₃₄
    have hs₁₅₂ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₁₂
    have hs₃₅₄ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₃₄
    rw [← Real.Angle.sign_eq_zero_iff] at hs₁₅₂ hs₃₅₄
    rw [hs₁₅₂, hs₃₅₄]
  · let s : Set (P × P × P) :=
      (fun x : line[ℝ, p₁, p₂] × V => (x.1, p₅, x.2 +ᵥ (x.1 : P))) ''
        Set.univ ×ˢ {v | SameRay ℝ (p₂ -ᵥ p₁) v ∧ v ≠ 0}
    have hco : IsConnected s :=
      haveI : ConnectedSpace line[ℝ, p₁, p₂] := AddTorsor.connectedSpace _ _
      (isConnected_univ.prod (isConnected_setOfPred_sameRay_and_ne_zero
        (vsub_ne_zero.2 hp₁p₂.symm))).image _ (by fun_prop)
    have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) s := by
      refine continuousOn_of_forall_continuousAt fun p hp => continuousAt_oangle ?_ ?_
      all_goals
        simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and, Prod.ext_iff] at hp
        obtain ⟨q₁, q₅, q₂⟩ := p
        dsimp only at hp ⊢
        obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
        dsimp only [Subtype.coe_mk, Set.mem_ofPred] at hv ⊢
        obtain ⟨hvr, -⟩ := hv
        rintro rfl
        refine hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan ?_).2 (collinear_pair _ _ _))
      · exact hq
      · refine vadd_mem_of_mem_direction ?_ hq
        rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
        obtain ⟨r, -, rfl⟩ := hvr
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hsp : ∀ p : P × P × P, p ∈ s → ∡ p.1 p.2.1 p.2.2 ≠ 0 ∧ ∡ p.1 p.2.1 p.2.2 ≠ π := by
      intro p hp
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff] at hp
      obtain ⟨q₁, q₅, q₂⟩ := p
      dsimp only at hp ⊢
      obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
      dsimp only [Subtype.coe_mk, Set.mem_ofPred] at hv ⊢
      obtain ⟨hvr, hv0⟩ := hv
      rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
      obtain ⟨r, -, rfl⟩ := hvr
      change q ∈ line[ℝ, p₁, p₂] at hq
      rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
      refine affineIndependent_of_ne_of_mem_of_notMem_of_mem ?_ hq
          (fun h => hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan h).2 (collinear_pair _ _ _))) ?_
      · rwa [← @vsub_ne_zero V, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_ne_zero]
      · refine vadd_mem_of_mem_direction ?_ hq
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hp₁p₂s : (p₁, p₅, p₂) ∈ s := by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff]
      refine ⟨⟨⟨p₁, left_mem_affineSpan_pair ℝ _ _⟩, p₂ -ᵥ p₁⟩,
        ⟨SameRay.rfl, vsub_ne_zero.2 hp₁p₂.symm⟩, ?_⟩
      simp
    have hp₃p₄s : (p₃, p₅, p₄) ∈ s := by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff]
      refine ⟨⟨⟨p₃, hc.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hp₁p₂⟩, p₄ -ᵥ p₃⟩,
        ⟨hr, vsub_ne_zero.2 hp₃p₄.symm⟩, ?_⟩
      simp
    convert! Real.Angle.sign_eq_of_continuousOn hco hf hsp hp₃p₄s hp₁p₂s

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or second and third points have the same sign. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_sign_eq** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given three points in strict order on the same line, and a fourth point, the ang
les at the
fourth point between the first and second or second and third points have the sa
me sign.
-/
theorem _root_.Sbtw.oangle_sign_eq {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw ℝ p₁ p₂ p₃) :
    (∡ p₁ p₄ p₂).sign = (∡ p₂ p₄ p₃).sign :=
  haveI hc : Collinear ℝ ({p₁, p₂, p₂, p₃} : Set P) := by simpa using h.wbtw.collinear
  hc.oangle_sign_of_sameRay_vsub _ h.left_ne h.ne_right h.wbtw.sameRay_vsub

/-- Given three points in weak order on the same line, with the first not equal to the second,
and a fourth point, the angles at the fourth point between the first and second or first and
third points have the same sign. -/
/-
**EuclideanGeometry._root_.Wbtw.oangle_sign_eq_of_ne_left** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given three points in weak order on the same line, with the first not equal to t
he second,
and a fourth point, the angles at the fourth point between the first and second 
or first and
third points have the same sign.
-/
theorem _root_.Wbtw.oangle_sign_eq_of_ne_left {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw ℝ p₁ p₂ p₃)
    (hne : p₁ ≠ p₂) : (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
  haveI hc : Collinear ℝ ({p₁, p₂, p₁, p₃} : Set P) := by
    simpa [Set.insert_comm p₂] using h.collinear
  hc.oangle_sign_of_sameRay_vsub _ hne (h.left_ne_right_of_ne_left hne.symm) h.sameRay_vsub_left

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or first and third points have the same sign. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_sign_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given three points in strict order on the same line, and a fourth point, the ang
les at the
fourth point between the first and second or first and third points have the sam
e sign.
-/
theorem _root_.Sbtw.oangle_sign_eq_left {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw ℝ p₁ p₂ p₃) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
  h.wbtw.oangle_sign_eq_of_ne_left _ h.left_ne

/-- Given three points in weak order on the same line, with the second not equal to the third,
and a fourth point, the angles at the fourth point between the second and third or first and
third points have the same sign. -/
/-
**EuclideanGeometry._root_.Wbtw.oangle_sign_eq_of_ne_right** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given three points in weak order on the same line, with the second not equal to 
the third,
and a fourth point, the angles at the fourth point between the second and third 
or first and
third points have the same sign.
-/
theorem _root_.Wbtw.oangle_sign_eq_of_ne_right {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw ℝ p₁ p₂ p₃)
    (hne : p₂ ≠ p₃) : (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign := by
  simp_rw [oangle_rev p₃, Real.Angle.sign_neg, h.symm.oangle_sign_eq_of_ne_left _ hne.symm]

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the second and third or first and third points have the same sign. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_sign_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given three points in strict order on the same line, and a fourth point, the ang
les at the
fourth point between the second and third or first and third points have the sam
e sign.
-/
theorem _root_.Sbtw.oangle_sign_eq_right {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw ℝ p₁ p₂ p₃) :
    (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign :=
  h.wbtw.oangle_sign_eq_of_ne_right _ h.ne_right

/-- Given two lines intersecting at a common point lying strictly between the defining points on
each line. Fixing one point from each line as the endpoints, choosing either remaining point as the
vertex yields oriented angles with the same sign. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_sign_eq_of_sbtw** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two lines intersecting at a common point lying strictly between the defini
ng points on
each line. Fixing one point from each line as the endpoints, choosing either rem
aining point as the
vertex yields oriented angles with the same sign.
-/
theorem _root_.Sbtw.oangle_sign_eq_of_sbtw {p p₁ p₂ p₃ p₄ : P} (hp₁₃ : Sbtw ℝ p₁ p p₃)
    (hp₂₄ : Sbtw ℝ p₂ p p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign := by
  rw [← Sbtw.oangle_eq_right hp₂₄.symm, Sbtw.oangle_sign_eq _ hp₁₃, ← oangle_rotate_sign,
    Sbtw.oangle_sign_eq _ hp₂₄.symm, Sbtw.oangle_eq_left hp₁₃.symm]

/-- Given two lines sharing a common point lying strictly outside the segments determined by the
defining points. Fixing one point from each line as the endpoints, choosing either remaining point
as the vertex yields oriented angles with the same sign. -/
/-
**EuclideanGeometry._root_.Sbtw.oangle_sign_eq_of_sbtw_left** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two lines sharing a common point lying strictly outside the segments deter
mined by the
defining points. Fixing one point from each line as the endpoints, choosing eith
er remaining point
as the vertex yields oriented angles with the same sign.
-/
theorem _root_.Sbtw.oangle_sign_eq_of_sbtw_left {p p₁ p₂ p₃ p₄ : P} (hp₁₃ : Sbtw ℝ p p₁ p₃)
    (hp₂₄ : Sbtw ℝ p p₂ p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign := by
  rw [Sbtw.oangle_eq_right hp₂₄.symm, Sbtw.oangle_sign_eq_right _ hp₁₃.symm, oangle_rotate_sign,
    ← Sbtw.oangle_sign_eq_left p₃ hp₂₄, Sbtw.oangle_eq_left hp₁₃.symm]

/-- Given two points in an affine subspace, the angles between those two points at two other
points on the same side of that subspace have the same sign. -/
/-
**EuclideanGeometry._root_.AffineSubspace.SSameSide.oangle_sign_eq** 是 Mathlib 中
的一个定理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two points in an affine subspace, the angles between those two points at t
wo other
points on the same side of that subspace have the same sign.
-/
theorem _root_.AffineSubspace.SSameSide.oangle_sign_eq {s : AffineSubspace ℝ P} {p₁ p₂ p₃ p₄ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.SSameSide p₃ p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign := by
  by_cases h : p₁ = p₂; · simp [h]
  let sp : Set (P × P × P) := (fun p : P => (p₁, p, p₂)) '' {p | s.SSameSide p₃ p}
  have hc : IsConnected sp :=
    (isConnected_setOfPred_sSameSide hp₃p₄.2.1 hp₃p₄.nonempty).image _ (by fun_prop)
  have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) sp := by
    refine continuousOn_of_forall_continuousAt fun p hp => continuousAt_oangle ?_ ?_
    all_goals
      simp_rw [sp, Set.mem_image, Set.mem_ofPred] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      dsimp only
      rintro rfl
    · exact hp'.2.2 hp₁
    · exact hp'.2.2 hp₂
  have hsp : ∀ p : P × P × P, p ∈ sp → ∡ p.1 p.2.1 p.2.2 ≠ 0 ∧ ∡ p.1 p.2.1 p.2.2 ≠ π := by
    intro p hp
    simp_rw [sp, Set.mem_image, Set.mem_ofPred] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    dsimp only
    rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
    exact affineIndependent_of_ne_of_mem_of_notMem_of_mem h hp₁ hp'.2.2 hp₂
  have hp₃ : (p₁, p₃, p₂) ∈ sp :=
    Set.mem_image_of_mem _ (sSameSide_self_iff.2 ⟨hp₃p₄.nonempty, hp₃p₄.2.1⟩)
  have hp₄ : (p₁, p₄, p₂) ∈ sp := Set.mem_image_of_mem _ hp₃p₄
  convert! Real.Angle.sign_eq_of_continuousOn hc hf hsp hp₃ hp₄

/-- Given two points in an affine subspace, the angles between those two points at two other
points on opposite sides of that subspace have opposite signs. -/
/-
**EuclideanGeometry._root_.AffineSubspace.SOppSide.oangle_sign_eq_neg** 是 Mathli
b 中的一个定理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two points in an affine subspace, the angles between those two points at t
wo other
points on opposite sides of that subspace have opposite signs.
-/
theorem _root_.AffineSubspace.SOppSide.oangle_sign_eq_neg {s : AffineSubspace ℝ P} {p₁ p₂ p₃ p₄ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.SOppSide p₃ p₄) :
    (∡ p₁ p₄ p₂).sign = -(∡ p₁ p₃ p₂).sign := by
  have hp₁p₃ : p₁ ≠ p₃ := by rintro rfl; exact hp₃p₄.left_notMem hp₁
  rw [← (hp₃p₄.symm.trans (sOppSide_pointReflection hp₁ hp₃p₄.left_notMem)).oangle_sign_eq hp₁ hp₂,
    ← oangle_rotate_sign p₁, ← oangle_rotate_sign p₁, oangle_swap₁₃_sign,
    (sbtw_pointReflection_of_ne ℝ hp₁p₃).symm.oangle_sign_eq _]

/-- The unoriented angles at `p₂` between `p₁` and `p₃`, and between `p₃` and `p₄`, are equal if
and only if the oriented angles are equal (`p₃` lies on the angle bisector) or one of `p₁` and `p₄`
is weakly between `p₂` and the other. -/
/-
**EuclideanGeometry.angle_eq_iff_oangle_eq_or_wbtw** 是 Mathlib 中的一个引理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：angle_eq_iff_oangle_eq_or_wbtw {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ != p₂) (hp₄ : p
₄ != p₂) : ∠ p₁ p₂ p₃ = ∠ p₃ p₂ p₄ ↔ ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ ∨ Wbtw Real p₂ p₁ p
₄ ∨ Wbtw Real p₂ p₄ p₁
参数：hp₁ : p₁ != p₂；hp₄ : p₄ != p₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Orientation.angle_eq_iff_oangle_eq_or_sameRay`：angle_eq_iff_oangle_eq_or
_sameRay {x y z : V} (hx : x != 0) (hz : z != 0) : InnerProductGeometry.angle x 
y = InnerProductGeometry.angle y z …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `or_congr_right`：∀ {b c a : Prop}, (b ↔ c) → (a ∨ b ↔ a ∨ c)
· 使用定理 `SameRay.exists_pos_left`：exists_pos_left (h : SameRay R x y) (hx : x != 
0) (hy : y != 0) : exists r : R, 0 < r ∧ r • x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `wbtw_or_wbtw_smul_vadd_of_nonneg`：wbtw_or_wbtw_smul_vadd_of_nonneg (x : 
P) (v : V) {r₁ r₂ : R} (hr₁ : 0 <= r₁) (hr₂ : 0 <= r₂) : Wbtw R x (r₁ • v +ᵥ x) 
(r₂ • v +ᵥ x) ∨ Wbtw R…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Wbtw.sameRay_vsub_left`：Wbtw.sameRay_vsub_left {x y z : P} (h : Wbtw R x
 y z) : SameRay R (y -ᵥ x) (z -ᵥ x)
· 使用定理 `SameRay.symm`：symm (h : SameRay R x y) : SameRay R y x

--- 原说明 ---
The unoriented angles at `p₂` between `p₁` and `p₃`, and between `p₃` and `p₄`, 
are equal if
and only if the oriented angles are equal (`p₃` lies on the angle bisector) or o
ne of `p₁` and `p₄`
is weakly between `p₂` and the other.
-/
lemma angle_eq_iff_oangle_eq_or_wbtw {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ≠ p₂) (hp₄ : p₄ ≠ p₂) :
    ∠ p₁ p₂ p₃ = ∠ p₃ p₂ p₄ ↔ ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ ∨ Wbtw ℝ p₂ p₁ p₄ ∨ Wbtw ℝ p₂ p₄ p₁ := by
  simp_rw [angle, oangle,
    o.angle_eq_iff_oangle_eq_or_sameRay (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₄)]
  apply or_congr_right
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨r, hr, he⟩ := h.exists_pos_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₄)
    rw [← vsub_vadd p₁ p₂, ← vsub_vadd p₄ p₂, ← he]
    nth_rw 1 4 [← one_smul ℝ (p₁ -ᵥ p₂)]
    exact wbtw_or_wbtw_smul_vadd_of_nonneg _ _ zero_le_one hr.le
  · rcases h with h | h
    · exact h.sameRay_vsub_left
    · exact h.sameRay_vsub_left.symm

/-- If `p₃` bisects the angle `∡ p₁ p₂ p₄`, and `p₃` and `p₄` lie on the same side of the line
`p₁ p₂`, then the unoriented angle `∠ p₁ p₂ p₃` is half `∠ p₁ p₂ p₄`. -/
/-
**EuclideanGeometry.angle_eq_angle_div_two_of_oangle_eq_of_sSameSide** 是 Mathlib
 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_angle_div_two_of_oangle_eq_of_sSameSide {p₁ p₂ p₃ p₄ : P} (h₁₂ : 
p₁ != p₂) (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄) (hs : line[Real, p₁, p₂].SSameSide p₃ p
₄) : ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄ / 2
参数：h₁₂ : p₁ != p₂；ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄；hs : line[Real, p₁, p₂].SSameSide
 p₃ p₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SSameSide.left_notMem`：∀ {R : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictO
rderedRing R] [inst_3 : Ad…
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]
· 使用定理 `AffineSubspace.SSameSide.right_notMem`：∀ {R : Type u_1} {V : Type u_2} {
P : Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Ad…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.oangle_add`：oangle_add {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p
) (hp₂ : p₂ != p) (hp₃ : p₃ != p) : ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_left_inj'`：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Collinear.mem_affineSpan_of_mem_of_ne`：Collinear.mem_affineSpan_of_mem_o
f_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in
 s) (hp₃ : p₃ in s) (hp₁p₂ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear`：oangle_eq_zero_
or_eq_pi_iff_collinear {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ∨ ∡ p₁ p₂ p₃ = π ↔ Collin
ear Real ({p₁, p₂, p₃} : Set P)
· 使用引理 `Real.Angle.toReal_add_eq_toReal_add_toReal`：toReal_add_eq_toReal_add_toR
eal {θ ψ : Angle} (hθ : θ != π) (hψ : ψ != π) (hs : θ.sign != ψ.sign ∨ θ.sign = 
(θ + ψ).sign) : (θ + ψ).toReal =…
· 使用定理 `EuclideanGeometry.oangle_swap₂₃_sign`：oangle_swap₂₃_sign (p₁ p₂ p₃ : P) 
: -(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AffineSubspace.SSameSide.oangle_sign_eq`：∀ {V : Type u_1} {P : Type u_2}
 [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAd…
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `EuclideanGeometry.angle_eq_abs_oangle_toReal`：angle_eq_abs_oangle_toReal
 {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) : ∠ p₁ p p₂ = |(∡ p₁ p p₂).toReal
|
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.abs_ofNat`：abs_ofNat (n : Nat) [n.AtLeastTwo] : |(ofNat(n) : R)| = o
fNat(n)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `p₃` bisects the angle `∡ p₁ p₂ p₄`, and `p₃` and `p₄` lie on the same side o
f the line
`p₁ p₂`, then the unoriented angle `∠ p₁ p₂ p₃` is half `∠ p₁ p₂ p₄`.
-/
lemma angle_eq_angle_div_two_of_oangle_eq_of_sSameSide {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ ≠ p₂)
    (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄) (hs : line[ℝ, p₁, p₂].SSameSide p₃ p₄) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄ / 2 := by
  have h₃₂ : p₃ ≠ p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ ≠ p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  suffices ((∡ p₁ p₂ p₃).toReal + (∡ p₃ p₂ p₄).toReal) / 2 = (∡ p₁ p₂ p₄).toReal / 2 by
    rw [← ha, add_self_div_two] at this
    rw [angle_eq_abs_oangle_toReal h₁₂ h₃₂, angle_eq_abs_oangle_toReal h₁₂ h₄₂, this, abs_div]
    simp
  have hadd := oangle_add h₁₂ h₃₂ h₄₂
  rw [div_left_inj' (by norm_num), ← hadd]
  have h : ∡ p₁ p₂ p₃ ≠ π := fun h ↦ hs.left_notMem ((oangle_eq_zero_or_eq_pi_iff_collinear.1
    (.inr h)).mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) h₁₂)
  refine (Real.Angle.toReal_add_eq_toReal_add_toReal h (ha ▸ h) (.inr ?_)).symm
  rw [hadd, ← oangle_swap₂₃_sign p₁ p₃ p₂, ← oangle_swap₂₃_sign p₁ p₄ p₂, neg_inj, eq_comm]
  exact hs.oangle_sign_eq (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

/-- If `p₃` bisects the angle `∡ p₁ p₂ p₄`, and `p₃` and `p₄` lie on opposite sides of the line
`p₁ p₂`, then the unoriented angle `∠ p₁ p₂ p₃` is `π` minus half `∠ p₁ p₂ p₄`. -/
/-
**EuclideanGeometry.angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide** 是 M
athlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide {p₁ p₂ p₃ p₄ : P} (
h₁₂ : p₁ != p₂) (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄) (hs : line[Real, p₁, p₂].SOppSide
 p₃ p₄) : ∠ p₁ p₂ p₃ = π - ∠ p₁ p₂ p₄ / 2
参数：h₁₂ : p₁ != p₂；ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄；hs : line[Real, p₁, p₂].SOppSide 
p₃ p₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SOppSide.left_notMem`：∀ {R : Type u_1} {V : Type u_2} {P 
: Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : Ad…
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]
· 使用定理 `AffineSubspace.SOppSide.right_notMem`：∀ {R : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictO
rderedRing R] [inst_3 : Ad…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.oangle_pointReflection_left`：oangle_pointReflection_le
ft {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂) : ∡ (AffineEquiv.pointReflec
tion Real p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃…
· 使用引理 `EuclideanGeometry.oangle_pointReflection_right`：oangle_pointReflection_r
ight {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂) : ∡ p₁ p₂ (AffineEquiv.poi
ntReflection Real p₂ p₃) = ∡ p₁ p₂ p…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AffineSubspace.sOppSide_pointReflection`：sOppSide_pointReflection {s : A
ffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) : s.SOppSide y (pointRef
lection R x y)
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EuclideanGeometry.angle_pointReflection_right`：angle_pointReflection_rig
ht {p₁ p₂ p₃ : P} : ∠ p₁ p₂ (AffineEquiv.pointReflection Real p₂ p₃) = π - ∠ p₁ 
p₂ p₃
· 使用引理 `EuclideanGeometry.angle_eq_angle_div_two_of_oangle_eq_of_sSameSide`：angl
e_eq_angle_div_two_of_oangle_eq_of_sSameSide {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ != p₂) 
(ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄) (hs : line[Real, p₁, p₂].…
· 使用定理 `AffineSubspace.SOppSide.trans`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrderedRing 
R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.SOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
If `p₃` bisects the angle `∡ p₁ p₂ p₄`, and `p₃` and `p₄` lie on opposite sides 
of the line
`p₁ p₂`, then the unoriented angle `∠ p₁ p₂ p₃` is `π` minus half `∠ p₁ p₂ p₄`.
-/
lemma angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ ≠ p₂)
    (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄) (hs : line[ℝ, p₁, p₂].SOppSide p₃ p₄) :
    ∠ p₁ p₂ p₃ = π - ∠ p₁ p₂ p₄ / 2 := by
  have h₃₂ : p₃ ≠ p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ ≠ p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ (AffineEquiv.pointReflection ℝ p₂ p₃) =
      ∡ (AffineEquiv.pointReflection ℝ p₂ p₃) p₂ p₄ := by
    rw [oangle_pointReflection_left h₃₂ h₄₂, oangle_pointReflection_right h₁₂ h₃₂]
    simpa using ha
  have hs' : line[ℝ, p₁, p₂].SOppSide p₃ (AffineEquiv.pointReflection ℝ p₂ p₃) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.left_notMem)
  obtain h := angle_eq_angle_div_two_of_oangle_eq_of_sSameSide h₁₂ ha' (hs'.symm.trans hs)
  rw [angle_pointReflection_right] at h
  linear_combination -h

/-- If `p₃` bisects the angle `∡ p₁ p₂ p₄` externally, and `p₃` and `p₄` lie on the same side of
the line `p₁ p₂`, then the unoriented angle `∠ p₁ p₂ p₃` is half `∠ p₁ p₂ p₄` plus `π / 2`. -/
/-
**EuclideanGeometry.angle_eq_angle_add_pi_div_two_of_oangle_eq_add_pi_of_sSameSi
de** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_angle_add_pi_div_two_of_oangle_eq_add_pi_of_sSameSide {p₁ p₂ p₃ p
₄ : P} (h₁₂ : p₁ != p₂) (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ + π) (hs : line[Real, p₁, 
p₂].SSameSide p₃ p₄) : ∠ p₁ p₂ p₃ = (∠ p₁ p₂ p₄ + π) / 2
参数：h₁₂ : p₁ != p₂；ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ + π；hs : line[Real, p₁, p₂].SSame
Side p₃ p₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SSameSide.left_notMem`：∀ {R : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictO
rderedRing R] [inst_3 : Ad…
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]
· 使用定理 `AffineSubspace.SSameSide.right_notMem`：∀ {R : Type u_1} {V : Type u_2} {
P : Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Ad…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.oangle_pointReflection_right`：oangle_pointReflection_r
ight {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂) : ∡ p₁ p₂ (AffineEquiv.poi
ntReflection Real p₂ p₃) = ∡ p₁ p₂ p…
· 使用定理 `AffineSubspace.sOppSide_pointReflection`：sOppSide_pointReflection {s : A
ffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) : s.SOppSide y (pointRef
lection R x y)
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `EuclideanGeometry.angle_pointReflection_right`：angle_pointReflection_rig
ht {p₁ p₂ p₃ : P} : ∠ p₁ p₂ (AffineEquiv.pointReflection Real p₂ p₃) = π - ∠ p₁ 
p₂ p₃
· 使用引理 `EuclideanGeometry.angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide
`：angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide {p₁ p₂ p₃ p₄ : P} (h₁₂ 
: p₁ != p₂) (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄) (hs : line[Real, p₁…
· 使用定理 `AffineSubspace.SSameSide.trans_sOppSide`：∀ {R : Type u_1} {V : Type u_2}
 {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : AddCom…
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
If `p₃` bisects the angle `∡ p₁ p₂ p₄` externally, and `p₃` and `p₄` lie on the 
same side of
the line `p₁ p₂`, then the unoriented angle `∠ p₁ p₂ p₃` is half `∠ p₁ p₂ p₄` pl
us `π / 2`.
-/
lemma angle_eq_angle_add_pi_div_two_of_oangle_eq_add_pi_of_sSameSide {p₁ p₂ p₃ p₄ : P}
    (h₁₂ : p₁ ≠ p₂) (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ + π) (hs : line[ℝ, p₁, p₂].SSameSide p₃ p₄) :
    ∠ p₁ p₂ p₃ = (∠ p₁ p₂ p₄ + π) / 2 := by
  have h₃₂ : p₃ ≠ p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ ≠ p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ (AffineEquiv.pointReflection ℝ p₂ p₄) := by
    rw [oangle_pointReflection_right h₃₂ h₄₂]
    exact ha
  have hs' : line[ℝ, p₁, p₂].SOppSide p₄ (AffineEquiv.pointReflection ℝ p₂ p₄) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.right_notMem)
  obtain h := angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide h₁₂ ha' (hs.trans_sOppSide hs')
  rw [angle_pointReflection_right] at h
  linear_combination h

/-- If `p₃` bisects the angle `∡ p₁ p₂ p₄` externally, and `p₃` and `p₄` lie on opposite sides of
the line `p₁ p₂`, then the unoriented angle `∠ p₁ p₂ p₃` is `π / 2` minus half `∠ p₁ p₂ p₄`. -/
/-
**EuclideanGeometry.angle_eq_pi_sub_angle_div_two_of_oangle_eq_add_pi_of_sOppSid
e** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_pi_sub_angle_div_two_of_oangle_eq_add_pi_of_sOppSide {p₁ p₂ p₃ p₄
 : P} (h₁₂ : p₁ != p₂) (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ + π) (hs : line[Real, p₁, p
₂].SOppSide p₃ p₄) : ∠ p₁ p₂ p₃ = (π - ∠ p₁ p₂ p₄) / 2
参数：h₁₂ : p₁ != p₂；ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ + π；hs : line[Real, p₁, p₂].SOppS
ide p₃ p₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SOppSide.left_notMem`：∀ {R : Type u_1} {V : Type u_2} {P 
: Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : Ad…
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]
· 使用定理 `AffineSubspace.SOppSide.right_notMem`：∀ {R : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictO
rderedRing R] [inst_3 : Ad…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.oangle_pointReflection_right`：oangle_pointReflection_r
ight {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂) : ∡ p₁ p₂ (AffineEquiv.poi
ntReflection Real p₂ p₃) = ∡ p₁ p₂ p…
· 使用定理 `AffineSubspace.sOppSide_pointReflection`：sOppSide_pointReflection {s : A
ffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) : s.SOppSide y (pointRef
lection R x y)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EuclideanGeometry.angle_pointReflection_right`：angle_pointReflection_rig
ht {p₁ p₂ p₃ : P} : ∠ p₁ p₂ (AffineEquiv.pointReflection Real p₂ p₃) = π - ∠ p₁ 
p₂ p₃
· 使用引理 `EuclideanGeometry.angle_eq_angle_div_two_of_oangle_eq_of_sSameSide`：angl
e_eq_angle_div_two_of_oangle_eq_of_sSameSide {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ != p₂) 
(ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄) (hs : line[Real, p₁, p₂].…
· 使用定理 `AffineSubspace.SOppSide.trans`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrderedRing 
R] [inst_3 : AddCom…

--- 原说明 ---
If `p₃` bisects the angle `∡ p₁ p₂ p₄` externally, and `p₃` and `p₄` lie on oppo
site sides of
the line `p₁ p₂`, then the unoriented angle `∠ p₁ p₂ p₃` is `π / 2` minus half `
∠ p₁ p₂ p₄`.
-/
lemma angle_eq_pi_sub_angle_div_two_of_oangle_eq_add_pi_of_sOppSide {p₁ p₂ p₃ p₄ : P}
    (h₁₂ : p₁ ≠ p₂) (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ + π) (hs : line[ℝ, p₁, p₂].SOppSide p₃ p₄) :
    ∠ p₁ p₂ p₃ = (π - ∠ p₁ p₂ p₄) / 2 := by
  have h₃₂ : p₃ ≠ p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ ≠ p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ (AffineEquiv.pointReflection ℝ p₂ p₄) := by
    rw [oangle_pointReflection_right h₃₂ h₄₂]
    exact ha
  have hs' : line[ℝ, p₁, p₂].SOppSide p₄ (AffineEquiv.pointReflection ℝ p₂ p₄) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.right_notMem)
  obtain h := angle_eq_angle_div_two_of_oangle_eq_of_sSameSide h₁₂ ha' (hs.trans hs')
  rw [angle_pointReflection_right] at h
  exact h

end EuclideanGeometry

