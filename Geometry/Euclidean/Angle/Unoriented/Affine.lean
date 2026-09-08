/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Angles between points

This file defines unoriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.angle`, with notation `∠`, is the undirected angle determined by three
  points.
-/

@[expose] public section


noncomputable section

open Real RealInnerProductSpace

namespace EuclideanGeometry

open InnerProductGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {p p₀ : P}

/-- The undirected angle at `p₂` between the line segments to `p₁` and
`p₃`. If either of those points equals `p₂`, this is π/2. Use
`open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃`
notation. -/
nonrec def angle (p₁ p₂ p₃ : P) : ℝ :=
  angle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂)

@[inherit_doc] scoped notation "∠" => EuclideanGeometry.angle

/-
**EuclideanGeometry.continuousAt_angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeome
try`。
形式化陈述：continuousAt_angle {x : P × P × P} (hx12 : x.1 != x.2.1) (hx32 : x.2.2 != 
x.2.1) : ContinuousAt (fun y : P × P × P => ∠ y.1 y.2.1 y.2.2) x
参数：hx12 : x.1 != x.2.1；hx32 : x.2.2 != x.2.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `InnerProductGeometry.continuousAt_angle`：continuousAt_angle {x : V × V} 
(hx1 : x.1 != 0) (hx2 : x.2 != 0) : ContinuousAt (fun y : V × V => angle y.1 y.2
) x
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
-/
theorem continuousAt_angle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
    ContinuousAt (fun y : P × P × P => ∠ y.1 y.2.1 y.2.2) x := by
  let f : P × P × P → V × V := fun y => (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1)
  have hf1 : (f x).1 ≠ 0 := by simp [f, hx12]
  have hf2 : (f x).2 ≠ 0 := by simp [f, hx32]
  exact (InnerProductGeometry.continuousAt_angle hf1 hf2).comp (by fun_prop)

@[simp]
/-
**EuclideanGeometry._root_.AffineIsometry.angle_map** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AffineIsometry.angle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂]
    [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    (f : P →ᵃⁱ[ℝ] P₂) (p₁ p₂ p₃ : P) : ∠ (f p₁) (f p₂) (f p₃) = ∠ p₁ p₂ p₃ := by
  simp_rw [angle, ← AffineIsometry.map_vsub, LinearIsometry.angle_map]

@[simp, norm_cast]
/-
**EuclideanGeometry._root_.AffineSubspace.angle_coe** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AffineSubspace.angle_coe {s : AffineSubspace ℝ P} (p₁ p₂ p₃ : s) :
    haveI : Nonempty s := ⟨p₁⟩
    ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
  haveI : Nonempty s := ⟨p₁⟩
  s.subtypeₐᵢ.angle_map p₁ p₂ p₃

/-- A homothety with a nonzero scale factor preserves angles. -/
/-
**EuclideanGeometry.angle_homothety** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
p p₁ p₂ p₃ : P) {r : ℝ},   r ≠ 0 →     EuclideanGeometry.angle ((AffineMap.homot
hety p r) p₁) ((AffineMap.homothety p r) p₂)         ((AffineMap.homothety p r) 
p₃) =       EuclideanGeometry.angle p₁ p₂ p₃
参数：p p₁ p₂ p₃ : P；(AffineMap.homothety p r) p₁；(AffineMap.homothety p r) p₂；(Aff
ineMap.homothety p r) p₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineMap.homothety_linear`：homothety_linear (c : P1) (r : k) : (homothe
ty c r).linear = r • LinearMap.id
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `InnerProductGeometry.angle_smul_right_of_neg`：angle_smul_right_of_neg (x
 y : V) {r : Real} (hr : r < 0) : angle x (r • y) = angle x (-y)
· 使用定理 `InnerProductGeometry.angle_smul_left_of_neg`：angle_smul_left_of_neg (x y
 : V) {r : Real} (hr : r < 0) : angle (r • x) y = angle (-x) y
· 使用定理 `InnerProductGeometry.angle_neg_neg`：angle_neg_neg (x y : V) : angle (-x)
 (-y) = angle x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `InnerProductGeometry.angle_smul_right_of_pos`：angle_smul_right_of_pos (x
 y : V) {r : Real} (hr : 0 < r) : angle x (r • y) = angle x y
· 使用定理 `InnerProductGeometry.angle_smul_left_of_pos`：angle_smul_left_of_pos (x y
 : V) {r : Real} (hr : 0 < r) : angle (r • x) y = angle x y

--- 原说明 ---
A homothety with a nonzero scale factor preserves angles.
-/
@[simp] lemma angle_homothety (p p₁ p₂ p₃ : P) {r : ℝ} (h : r ≠ 0) :
    ∠ (AffineMap.homothety p r p₁) (AffineMap.homothety p r p₂) (AffineMap.homothety p r p₃) =
      ∠ p₁ p₂ p₃ := by
  simp_rw [angle, ← AffineMap.linearMap_vsub, AffineMap.homothety_linear, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rcases h.lt_or_gt with hlt | hlt <;> simp [hlt, -neg_vsub_eq_vsub_rev]

/-- Angles are translation invariant. -/
@[simp]
/-
**EuclideanGeometry.angle_const_vadd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：angle_const_vadd (v : V) (p₁ p₂ p₃ : P) : ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) 
= ∠ p₁ p₂ p₃
参数：v : V；p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.angle_map`：∀ {V : Type u_1} {P : Type u_2} [inst : Normed
AddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [ins
t_3 : NormedAd…

--- 原说明 ---
Angles are translation invariant.
-/
theorem angle_const_vadd (v : V) (p₁ p₂ p₃ : P) : ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVAdd ℝ P v).toAffineIsometry.angle_map _ _ _

/-- Angles are translation invariant. -/
@[simp]
/-
**EuclideanGeometry.angle_vadd_const** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：angle_vadd_const (v₁ v₂ v₃ : V) (p : P) : ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) 
= ∠ v₁ v₂ v₃
参数：v₁ v₂ v₃ : V；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.angle_map`：∀ {V : Type u_1} {P : Type u_2} [inst : Normed
AddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [ins
t_3 : NormedAd…

--- 原说明 ---
Angles are translation invariant.
-/
theorem angle_vadd_const (v₁ v₂ v₃ : V) (p : P) : ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.angle_map _ _ _

/-- Angles are translation invariant. -/
@[simp]
/-
**EuclideanGeometry.angle_const_vsub** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：angle_const_vsub (p p₁ p₂ p₃ : P) : ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁
 p₂ p₃
参数：p p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.angle_map`：∀ {V : Type u_1} {P : Type u_2} [inst : Normed
AddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [ins
t_3 : NormedAd…

--- 原说明 ---
Angles are translation invariant.
-/
theorem angle_const_vsub (p p₁ p₂ p₃ : P) : ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVSub ℝ p).toAffineIsometry.angle_map _ _ _

/-- Angles are translation invariant. -/
@[simp]
/-
**EuclideanGeometry.angle_vsub_const** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：angle_vsub_const (p₁ p₂ p₃ p : P) : ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁
 p₂ p₃
参数：p₁ p₂ p₃ p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.angle_map`：∀ {V : Type u_1} {P : Type u_2} [inst : Normed
AddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [ins
t_3 : NormedAd…

--- 原说明 ---
Angles are translation invariant.
-/
theorem angle_vsub_const (p₁ p₂ p₃ p : P) : ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).symm.toAffineIsometry.angle_map _ _ _

/-- Angles in a vector space are translation invariant. -/
@[simp]
/-
**EuclideanGeometry.angle_add_const** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：angle_add_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ 
v₁ v₂ v₃
参数：v₁ v₂ v₃ : V；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.angle_vadd_const`：angle_vadd_const (v₁ v₂ v₃ : V) (p :
 P) : ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃

--- 原说明 ---
Angles in a vector space are translation invariant.
-/
theorem angle_add_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ v₁ v₂ v₃ :=
  angle_vadd_const _ _ _ _

/-- Angles in a vector space are translation invariant. -/
@[simp]
/-
**EuclideanGeometry.angle_const_add** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：angle_const_add (v : V) (v₁ v₂ v₃ : V) : ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ 
v₁ v₂ v₃
参数：v : V；v₁ v₂ v₃ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.angle_const_vadd`：angle_const_vadd (v : V) (p₁ p₂ p₃ :
 P) : ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃

--- 原说明 ---
Angles in a vector space are translation invariant.
-/
theorem angle_const_add (v : V) (v₁ v₂ v₃ : V) : ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ v₁ v₂ v₃ :=
  angle_const_vadd _ _ _ _

/-- Angles in a vector space are translation invariant. -/
@[simp]
/-
**EuclideanGeometry.angle_sub_const** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：angle_sub_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ 
v₁ v₂ v₃
参数：v₁ v₂ v₃ : V；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.angle_vsub_const`：angle_vsub_const (p₁ p₂ p₃ p : P) : 
∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃

--- 原说明 ---
Angles in a vector space are translation invariant.
-/
theorem angle_sub_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_vsub_const v₁ v₂ v₃ v

/-- Angles in a vector space are invariant under inversion. -/
@[simp]
/-
**EuclideanGeometry.angle_const_sub** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：angle_const_sub (v : V) (v₁ v₂ v₃ : V) : ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ 
v₁ v₂ v₃
参数：v : V；v₁ v₂ v₃ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.angle_const_vsub`：angle_const_vsub (p p₁ p₂ p₃ : P) : 
∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃

--- 原说明 ---
Angles in a vector space are invariant under inversion.
-/
theorem angle_const_sub (v : V) (v₁ v₂ v₃ : V) : ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_const_vsub v v₁ v₂ v₃

/-- Angles in a vector space are invariant under inversion. -/
@[simp]
/-
**EuclideanGeometry.angle_neg** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_neg (v₁ v₂ v₃ : V) : ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃
参数：v₁ v₂ v₃ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `EuclideanGeometry.angle_const_sub`：angle_const_sub (v : V) (v₁ v₂ v₃ : V
) : ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃

--- 原说明 ---
Angles in a vector space are invariant under inversion.
-/
theorem angle_neg (v₁ v₂ v₃ : V) : ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [zero_sub] using angle_const_sub 0 v₁ v₂ v₃
/-
**EuclideanGeometry.angle_smul_right_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry`。
形式化陈述：angle_smul_right_of_pos (p₁ : P) {p₂ p₃ p₄ : P} {r : Real} (hr : 0 < r) (h
rv : r • (p₄ -ᵥ p₂) = p₃ -ᵥ p₂) : ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄
参数：p₁ : P；hr : 0 < r；hrv : r • (p₄ -ᵥ p₂) = p₃ -ᵥ p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductGeometry.angle_smul_right_of_pos`：angle_smul_right_of_pos (x
 y : V) {r : Real} (hr : 0 < r) : angle x (r • y) = angle x y
-/
theorem angle_smul_right_of_pos (p₁ : P) {p₂ p₃ p₄ : P} {r : ℝ} (hr : 0 < r)
    (hrv : r • (p₄ -ᵥ p₂) = p₃ -ᵥ p₂) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄ := by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_right_of_pos (p₁ -ᵥ p₂) (p₄ -ᵥ p₂) hr
/-
**EuclideanGeometry.angle_smul_left_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry`。
形式化陈述：angle_smul_left_of_pos {p₁ p₂ p₄ : P} (p₃ : P) {r : Real} (hr : 0 < r) (hr
v : r • (p₄ -ᵥ p₂) = p₁ -ᵥ p₂) : ∠ p₁ p₂ p₃ = ∠ p₄ p₂ p₃
参数：p₃ : P；hr : 0 < r；hrv : r • (p₄ -ᵥ p₂) = p₁ -ᵥ p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductGeometry.angle_smul_left_of_pos`：angle_smul_left_of_pos (x y
 : V) {r : Real} (hr : 0 < r) : angle (r • x) y = angle x y
-/
theorem angle_smul_left_of_pos {p₁ p₂ p₄ : P} (p₃ : P) {r : ℝ} (hr : 0 < r)
    (hrv : r • (p₄ -ᵥ p₂) = p₁ -ᵥ p₂) :
    ∠ p₁ p₂ p₃ = ∠ p₄ p₂ p₃ := by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_left_of_pos (p₄ -ᵥ p₂) (p₃ -ᵥ p₂) hr

/-- The angle at a point does not depend on the order of the other two
points. -/
nonrec theorem angle_comm (p₁ p₂ p₃ : P) : ∠ p₁ p₂ p₃ = ∠ p₃ p₂ p₁ :=
  angle_comm _ _

/-- The angle at a point is nonnegative. -/
nonrec theorem angle_nonneg (p₁ p₂ p₃ : P) : 0 ≤ ∠ p₁ p₂ p₃ :=
  angle_nonneg _ _

/-- The angle at a point is at most π. -/
nonrec theorem angle_le_pi (p₁ p₂ p₃ : P) : ∠ p₁ p₂ p₃ ≤ π :=
  angle_le_pi _ _

/-- The angle ∠AAB at a point is always `π / 2`. -/
/-
**EuclideanGeometry.angle_self_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
p₀ p : P), EuclideanGeometry.angle p₀ p₀ p = Real.pi / 2
参数：p₀ p : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2

--- 原说明 ---
The angle ∠AAB at a point is always `π / 2`.
-/
@[simp] lemma angle_self_left (p₀ p : P) : ∠ p₀ p₀ p = π / 2 := by
  unfold angle
  rw [vsub_self]
  exact angle_zero_left _

/-- The angle ∠ABB at a point is always `π / 2`. -/
/-
**EuclideanGeometry.angle_self_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
p₀ p : P), EuclideanGeometry.angle p p₀ p₀ = Real.pi / 2
参数：p₀ p : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_self_left`：∀ {V : Type u_1} {P : Type u_2} [inst
 : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAd…

--- 原说明 ---
The angle ∠ABB at a point is always `π / 2`.
-/
@[simp] lemma angle_self_right (p₀ p : P) : ∠ p p₀ p₀ = π / 2 := by rw [angle_comm, angle_self_left]

/-- The angle ∠ABA at a point is `0`, unless `A = B`. -/
/-
**EuclideanGeometry.angle_self_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：angle_self_of_ne (h : p != p₀) : ∠ p p₀ p = 0
参数：h : p != p₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductGeometry.angle_self`：angle_self {x : V} (hx : x != 0) : angl
e x x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
The angle ∠ABA at a point is `0`, unless `A = B`.
-/
theorem angle_self_of_ne (h : p ≠ p₀) : ∠ p p₀ p = 0 := angle_self <| vsub_ne_zero.2 h


/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
/-
**EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_left** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：angle_eq_zero_of_angle_eq_pi_left {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : ∠ 
p₂ p₁ p₃ = 0
参数：h : ∠ p₁ p₂ p₃ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle_eq_pi_iff`：angle_eq_pi_iff {x y : V} : angle 
x y = π ↔ x != 0 ∧ exists r : Real, r < 0 ∧ y = r • x
· 使用定理 `InnerProductGeometry.angle_eq_zero_iff`：angle_eq_zero_iff {x y : V} : an
gle x y = 0 ↔ x != 0 ∧ exists r : Real, 0 < r ∧ y = r • x
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_pos_of_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a : α}, a < 0 → 0 < -a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the angle ∠ABC at a point is π, the angle ∠BAC is 0.
-/
theorem angle_eq_zero_of_angle_eq_pi_left {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : ∠ p₂ p₁ p₃ = 0 := by
  unfold angle at h
  rw [angle_eq_pi_iff] at h
  rcases h with ⟨hp₁p₂, ⟨r, ⟨hr, hpr⟩⟩⟩
  unfold angle
  rw [angle_eq_zero_iff]
  rw [← neg_vsub_eq_vsub_rev, neg_ne_zero] at hp₁p₂
  use hp₁p₂, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one
  rw [add_smul, ← neg_vsub_eq_vsub_rev p₁ p₂, smul_neg]
  simp [← hpr]

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
/-
**EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_right** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry`。
形式化陈述：angle_eq_zero_of_angle_eq_pi_right {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : ∠
 p₂ p₃ p₁ = 0
参数：h : ∠ p₁ p₂ p₃ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_left`：angle_eq_zero_of_an
gle_eq_pi_left {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : ∠ p₂ p₁ p₃ = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…

--- 原说明 ---
If the angle ∠ABC at a point is π, the angle ∠BCA is 0.
-/
theorem angle_eq_zero_of_angle_eq_pi_right {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
    ∠ p₂ p₃ p₁ = 0 := by
  rw [angle_comm] at h
  exact angle_eq_zero_of_angle_eq_pi_left h

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
/-
**EuclideanGeometry.angle_eq_angle_of_angle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Euc
lideanGeometry`。
形式化陈述：angle_eq_angle_of_angle_eq_pi (p₁ : P) {p₂ p₃ p₄ : P} (h : ∠ p₂ p₃ p₄ = π)
 : ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄
参数：p₁ : P；h : ∠ p₂ p₃ p₄ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `InnerProductGeometry.angle_eq_pi_iff`：angle_eq_pi_iff {x y : V} : angle 
x y = π ↔ x != 0 ∧ exists r : Real, r < 0 ∧ y = r • x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
If ∠BCD = π, then ∠ABC = ∠ABD.
-/
theorem angle_eq_angle_of_angle_eq_pi (p₁ : P) {p₂ p₃ p₄ : P} (h : ∠ p₂ p₃ p₄ = π) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄ := by
  unfold angle at *
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, hpr⟩⟩⟩
  rw [eq_comm]
  replace hpr : (-r + 1) • (p₃ -ᵥ p₂) = p₄ -ᵥ p₂ := by
    rw [add_smul, ← neg_vsub_eq_vsub_rev p₂ p₃, smul_neg, neg_smul, ← hpr]
    simp
  replace hr : 0 < -r + 1 := by linarith
  exact angle_smul_right_of_pos p₁ hr hpr

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
nonrec theorem angle_add_angle_eq_pi_of_angle_eq_pi (p₁ : P) {p₂ p₃ p₄ : P} (h : ∠ p₂ p₃ p₄ = π) :
    ∠ p₁ p₃ p₂ + ∠ p₁ p₃ p₄ = π := by
  unfold angle at h
  rw [angle_comm p₁ p₃ p₂, angle_comm p₁ p₃ p₄]
  unfold angle
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h

/-- **Vertical Angles Theorem**: angles opposite each other, formed by two intersecting straight
lines, are equal. -/
/-
**EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p₁ p₂ p₃ p₄ p₅ : P} (hapc : 
∠ p₁ p₅ p₃ = π) (hbpd : ∠ p₂ p₅ p₄ = π) : ∠ p₁ p₅ p₂ = ∠ p₃ p₅ p₄
参数：hapc : ∠ p₁ p₅ p₃ = π；hbpd : ∠ p₂ p₅ p₄ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
**Vertical Angles Theorem**: angles opposite each other, formed by two intersect
ing straight
lines, are equal.
-/
theorem angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p₁ p₂ p₃ p₄ p₅ : P} (hapc : ∠ p₁ p₅ p₃ = π)
    (hbpd : ∠ p₂ p₅ p₄ = π) : ∠ p₁ p₅ p₂ = ∠ p₃ p₅ p₄ := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₁ hbpd, angle_comm p₄ p₅ p₁,
    angle_add_angle_eq_pi_of_angle_eq_pi p₄ hapc, angle_comm p₄ p₅ p₃]

/-- If ∠ABC = π then dist A B ≠ 0. -/
/-
**EuclideanGeometry.left_dist_ne_zero_of_angle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：left_dist_ne_zero_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : dis
t p₁ p₂ != 0
参数：h : ∠ p₁ p₂ p₃ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
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
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
If ∠ABC = π then dist A B ≠ 0.
-/
theorem left_dist_ne_zero_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : dist p₁ p₂ ≠ 0 := by
  by_contra heq
  rw [dist_eq_zero] at heq
  rw [heq, angle_self_left] at h
  exact Real.pi_ne_zero (by linarith)

/-- If ∠ABC = π then dist C B ≠ 0. -/
/-
**EuclideanGeometry.right_dist_ne_zero_of_angle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：right_dist_ne_zero_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : di
st p₃ p₂ != 0
参数：h : ∠ p₁ p₂ p₃ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.left_dist_ne_zero_of_angle_eq_pi`：left_dist_ne_zero_of
_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : dist p₁ p₂ != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…

--- 原说明 ---
If ∠ABC = π then dist C B ≠ 0.
-/
theorem right_dist_ne_zero_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : dist p₃ p₂ ≠ 0 :=
  left_dist_ne_zero_of_angle_eq_pi <| (angle_comm _ _ _).trans h

/-- If ∠ABC = π, then (dist A C) = (dist A B) + (dist B C). -/
/-
**EuclideanGeometry.dist_eq_add_dist_of_angle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：dist_eq_add_dist_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : dist
 p₁ p₃ = dist p₁ p₂ + dist p₃ p₂
参数：h : ∠ p₁ p₂ p₃ = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `InnerProductGeometry.norm_sub_eq_add_norm_of_angle_eq_pi`：norm_sub_eq_ad
d_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) : ‖x - y‖ = ‖x‖ + ‖y‖

--- 原说明 ---
If ∠ABC = π, then (dist A C) = (dist A B) + (dist B C).
-/
theorem dist_eq_add_dist_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
    dist p₁ p₃ = dist p₁ p₂ + dist p₃ p₂ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_add_norm_of_angle_eq_pi h

/-- If A ≠ B and C ≠ B then ∠ABC = π if and only if (dist A C) = (dist A B) + (dist B C). -/
/-
**EuclideanGeometry.dist_eq_add_dist_iff_angle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：dist_eq_add_dist_iff_angle_eq_pi {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (hp₃p₂ 
: p₃ != p₂) : dist p₁ p₃ = dist p₁ p₂ + dist p₃ p₂ ↔ ∠ p₁ p₂ p₃ = π
参数：hp₁p₂ : p₁ != p₂；hp₃p₂ : p₃ != p₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `InnerProductGeometry.norm_sub_eq_add_norm_iff_angle_eq_pi`：norm_sub_eq_a
dd_norm_iff_angle_eq_pi {x y : V} (hx : x != 0) (hy : y != 0) : ‖x - y‖ = ‖x‖ + 
‖y‖ ↔ angle x y = π
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂

--- 原说明 ---
If A ≠ B and C ≠ B then ∠ABC = π if and only if (dist A C) = (dist A B) + (dist 
B C).
-/
theorem dist_eq_add_dist_iff_angle_eq_pi {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ ≠ p₂) (hp₃p₂ : p₃ ≠ p₂) :
    dist p₁ p₃ = dist p₁ p₂ + dist p₃ p₂ ↔ ∠ p₁ p₂ p₃ = π := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_add_norm_iff_angle_eq_pi (fun he => hp₁p₂ (vsub_eq_zero_iff_eq.1 he)) fun he =>
      hp₃p₂ (vsub_eq_zero_iff_eq.1 he)

/-- If ∠ABC = 0, then (dist A C) = abs ((dist A B) - (dist B C)). -/
/-
**EuclideanGeometry.dist_eq_abs_sub_dist_of_angle_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：dist_eq_abs_sub_dist_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) 
: dist p₁ p₃ = |dist p₁ p₂ - dist p₃ p₂|
参数：h : ∠ p₁ p₂ p₃ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `InnerProductGeometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zero`：norm_sub
_eq_abs_sub_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ‖x - y‖ = |‖x‖
 - ‖y‖|

--- 原说明 ---
If ∠ABC = 0, then (dist A C) = abs ((dist A B) - (dist B C)).
-/
theorem dist_eq_abs_sub_dist_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) :
    dist p₁ p₃ = |dist p₁ p₂ - dist p₃ p₂| := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h

/-- If A ≠ B and C ≠ B then ∠ABC = 0 if and only if (dist A C) = abs ((dist A B) - (dist B C)). -/
/-
**EuclideanGeometry.dist_eq_abs_sub_dist_iff_angle_eq_zero** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry`。
形式化陈述：dist_eq_abs_sub_dist_iff_angle_eq_zero {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (
hp₃p₂ : p₃ != p₂) : dist p₁ p₃ = |dist p₁ p₂ - dist p₃ p₂| ↔ ∠ p₁ p₂ p₃ = 0
参数：hp₁p₂ : p₁ != p₂；hp₃p₂ : p₃ != p₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `InnerProductGeometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zero`：norm_su
b_eq_abs_sub_norm_iff_angle_eq_zero {x y : V} (hx : x != 0) (hy : y != 0) : ‖x -
 y‖ = |‖x‖ - ‖y‖| ↔ angle x y = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂

--- 原说明 ---
If A ≠ B and C ≠ B then ∠ABC = 0 if and only if (dist A C) = abs ((dist A B) - (
dist B C)).
-/
theorem dist_eq_abs_sub_dist_iff_angle_eq_zero {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ ≠ p₂) (hp₃p₂ : p₃ ≠ p₂) :
    dist p₁ p₃ = |dist p₁ p₂ - dist p₃ p₂| ↔ ∠ p₁ p₂ p₃ = 0 := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_abs_sub_norm_iff_angle_eq_zero (fun he => hp₁p₂ (vsub_eq_zero_iff_eq.1 he))
      fun he => hp₃p₂ (vsub_eq_zero_iff_eq.1 he)

/-- If M is the midpoint of the segment AB, then ∠AMB = π. -/
/-
**EuclideanGeometry.angle_midpoint_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeo
metry`。
形式化陈述：angle_midpoint_eq_pi (p₁ p₂ : P) (hp₁p₂ : p₁ != p₂) : ∠ p₁ (midpoint Real 
p₁ p₂) p₂ = π
参数：p₁ p₂ : P；hp₁p₂ : p₁ != p₂。
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
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `left_vsub_midpoint`：left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁
 p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `midpoint_vsub_right`：midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ 
-ᵥ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.dist_eq_add_dist_iff_angle_eq_pi`：dist_eq_add_dist_iff
_angle_eq_pi {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (hp₃p₂ : p₃ != p₂) : dist p₁ p₃ =
 dist p₁ p₂ + dist p₃ p₂ ↔ ∠ p₁ p₂ p₃ = …
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
If M is the midpoint of the segment AB, then ∠AMB = π.
-/
theorem angle_midpoint_eq_pi (p₁ p₂ : P) (hp₁p₂ : p₁ ≠ p₂) : ∠ p₁ (midpoint ℝ p₁ p₂) p₂ = π := by
  suffices dist p₁ p₂ = dist p₁ (midpoint ℝ p₁ p₂) + dist (midpoint ℝ p₁ p₂) p₂ by
    rwa [← dist_eq_add_dist_iff_angle_eq_pi (by simpa) (by simpa), dist_comm p₂]
  simp [dist_eq_norm_vsub V, left_vsub_midpoint, midpoint_vsub_right, norm_smul, ← two_mul]

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMA = π / 2. -/
/-
**EuclideanGeometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_left_midpoint_eq_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₃ p
₁ = dist p₃ p₂) : ∠ p₃ (midpoint Real p₁ p₂) p₁ = π / 2
参数：h : dist p₃ p₁ = dist p₃ p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `left_vsub_midpoint`：left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁
 p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
· 使用定理 `midpoint_vsub_right`：midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ 
-ᵥ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `InnerProductGeometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two`：norm_
add_eq_norm_sub_iff_angle_eq_pi_div_two (x y : V) : ‖x + y‖ = ‖x - y‖ ↔ angle x 
y = π / 2
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖

--- 原说明 ---
If M is the midpoint of the segment AB and C is the same distance from A as it i
s from B
then ∠CMA = π / 2.
-/
theorem angle_left_midpoint_eq_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₃ p₁ = dist p₃ p₂) :
    ∠ p₃ (midpoint ℝ p₁ p₂) p₁ = π / 2 := by
  let m : P := midpoint ℝ p₁ p₂
  have h1 : p₃ -ᵥ p₁ = p₃ -ᵥ m - (p₁ -ᵥ m) := (vsub_sub_vsub_cancel_right p₃ p₁ m).symm
  have h2 : p₃ -ᵥ p₂ = p₃ -ᵥ m + (p₁ -ᵥ m) := by
    rw [left_vsub_midpoint, ← midpoint_vsub_right, vsub_add_vsub_cancel]
  rw [dist_eq_norm_vsub V p₃ p₁, dist_eq_norm_vsub V p₃ p₂, h1, h2] at h
  exact (norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (p₃ -ᵥ m) (p₁ -ᵥ m)).mp h.symm

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMB = π / 2. -/
/-
**EuclideanGeometry.angle_right_midpoint_eq_pi_div_two_of_dist_eq** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_right_midpoint_eq_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₃ 
p₁ = dist p₃ p₂) : ∠ p₃ (midpoint Real p₁ p₂) p₂ = π / 2
参数：h : dist p₃ p₁ = dist p₃ p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `EuclideanGeometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq`：angle_le
ft_midpoint_eq_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₃ p₁ = dist p₃ p₂
) : ∠ p₃ (midpoint Real p₁ p₂) p₁ = π / 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If M is the midpoint of the segment AB and C is the same distance from A as it i
s from B
then ∠CMB = π / 2.
-/
theorem angle_right_midpoint_eq_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₃ p₁ = dist p₃ p₂) :
    ∠ p₃ (midpoint ℝ p₁ p₂) p₂ = π / 2 := by
  rw [midpoint_comm p₁ p₂, angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]

/-- If the second of three points is strictly between the other two, the angle at that point
is π. -/
/-
**EuclideanGeometry._root_.Sbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the angle at th
at point
is π.
-/
theorem _root_.Sbtw.angle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₂ p₃ = π := by
  rw [angle, angle_eq_pi_iff]
  rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩
  refine ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r, ?_⟩
  have hr0' : r ≠ 0 := by
    rintro rfl
    rw [← hp₂] at hp₂p₁
    simp at hp₂p₁
  have hr1' : r ≠ 1 := by
    rintro rfl
    rw [← hp₂] at hp₂p₃
    simp at hp₂p₃
  replace hr0 := hr0.lt_of_ne hr0'.symm
  replace hr1 := hr1.lt_of_ne hr1'
  refine ⟨div_neg_of_neg_of_pos (Left.neg_neg_iff.2 (sub_pos.2 hr1)) hr0, ?_⟩
  rw [← hp₂, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, vsub_self,
    zero_sub, smul_neg, smul_smul, div_mul_cancel₀ _ hr0', neg_smul, neg_neg, sub_eq_iff_eq_add, ←
    add_smul, sub_add_cancel, one_smul]

/-- If the second of three points is strictly between the other two, the angle at that point
(reversed) is π. -/
/-
**EuclideanGeometry._root_.Sbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the angle at th
at point
(reversed) is π.
-/
theorem _root_.Sbtw.angle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₂ p₁ = π := by
  rw [← h.angle₁₂₃_eq_pi, angle_comm]

/-- The angle between three points is π if and only if the second point is strictly between the
other two. -/
/-
**EuclideanGeometry.angle_eq_pi_iff_sbtw** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeo
metry`。
形式化陈述：angle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `InnerProductGeometry.angle_eq_pi_iff`：angle_eq_pi_iff {x y : V} : angle 
x y = π ↔ x != 0 ∧ exists r : Real, r < 0 ∧ y = r • x
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_sub_self_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] (a : α) {b : α}, a ≤ a - b ↔ b ≤ 0
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
（共 102 条，此处仅展示前 30 条）

--- 原说明 ---
The angle between three points is π if and only if the second point is strictly 
between the
other two.
-/
theorem angle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃ := by
  refine ⟨?_, fun h => h.angle₁₂₃_eq_pi⟩
  rw [angle, angle_eq_pi_iff]
  rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩
  refine ⟨⟨1 / (1 - r), ⟨div_nonneg zero_le_one (sub_nonneg.2 (hr.le.trans zero_le_one)),
    (div_le_one (sub_pos.2 (hr.trans zero_lt_one))).2 ((le_sub_self_iff 1).2 hr.le)⟩, ?_⟩,
    (vsub_ne_zero.1 hp₁p₂).symm, ?_⟩
  · rw [← eq_vadd_iff_vsub_eq] at hp₃p₂
    rw [AffineMap.lineMap_apply, hp₃p₂, vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev p₂ p₁, smul_neg, ←
      neg_smul, smul_add, smul_smul, ← add_smul, eq_comm, eq_vadd_iff_vsub_eq]
    convert! (one_smul ℝ (p₂ -ᵥ p₁)).symm
    field [(sub_pos.2 (hr.trans zero_lt_one)).ne.symm]
  · rw [ne_comm, ← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
    exact ⟨hr.ne, hp₁p₂⟩

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point is zero. -/
/-
**EuclideanGeometry._root_.Wbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is weakly between the other two, and not equal to 
the first,
the angle at the first point is zero.
-/
theorem _root_.Wbtw.angle₂₁₃_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    ∠ p₂ p₁ p₃ = 0 := by
  rw [angle, angle_eq_zero_iff]
  rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
  have hr0' : r ≠ 0 := by
    rintro rfl
    simp at hp₂p₁
  replace hr0 := hr0.lt_of_ne hr0'.symm
  refine ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, ?_⟩
  rw [AffineMap.lineMap_apply, vadd_vsub_assoc, vsub_self, add_zero, smul_smul,
    inv_mul_cancel₀ hr0', one_smul]

/-- If the second of three points is strictly between the other two, the angle at the first point
is zero. -/
/-
**EuclideanGeometry._root_.Sbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the angle at th
e first point
is zero.
-/
theorem _root_.Sbtw.angle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₁ p₃ = 0 :=
  h.wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point (reversed) is zero. -/
/-
**EuclideanGeometry._root_.Wbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is weakly between the other two, and not equal to 
the first,
the angle at the first point (reversed) is zero.
-/
theorem _root_.Wbtw.angle₃₁₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    ∠ p₃ p₁ p₂ = 0 := by rw [← h.angle₂₁₃_eq_zero_of_ne hp₂p₁, angle_comm]

/-- If the second of three points is strictly between the other two, the angle at the first point
(reversed) is zero. -/
/-
**EuclideanGeometry._root_.Sbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the angle at th
e first point
(reversed) is zero.
-/
theorem _root_.Sbtw.angle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₁ p₂ = 0 :=
  h.wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point is zero. -/
/-
**EuclideanGeometry._root_.Wbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is weakly between the other two, and not equal to 
the third,
the angle at the third point is zero.
-/
theorem _root_.Wbtw.angle₂₃₁_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    ∠ p₂ p₃ p₁ = 0 :=
  h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃

/-- If the second of three points is strictly between the other two, the angle at the third point
is zero. -/
/-
**EuclideanGeometry._root_.Sbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the angle at th
e third point
is zero.
-/
theorem _root_.Sbtw.angle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₃ p₁ = 0 :=
  h.wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point (reversed) is zero. -/
/-
**EuclideanGeometry._root_.Wbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is weakly between the other two, and not equal to 
the third,
the angle at the third point (reversed) is zero.
-/
theorem _root_.Wbtw.angle₁₃₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    ∠ p₁ p₃ p₂ = 0 :=
  h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃

/-- If the second of three points is strictly between the other two, the angle at the third point
(reversed) is zero. -/
/-
**EuclideanGeometry._root_.Sbtw.angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the second of three points is strictly between the other two, the angle at th
e third point
(reversed) is zero.
-/
theorem _root_.Sbtw.angle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₃ p₂ = 0 :=
  h.wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right

/-- The angle between three points is zero if and only if one of the first and third points is
weakly between the other two, and not equal to the second. -/
/-
**EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw** 是 Mathlib 中的一个定理，位于命名空间 `Euc
lideanGeometry`。
形式化陈述：angle_eq_zero_iff_ne_and_wbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = 0 ↔ p₁ != p₂ ∧
 Wbtw Real p₂ p₁ p₃ ∨ p₃ != p₂ ∧ Wbtw Real p₂ p₃ p₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `InnerProductGeometry.angle_eq_zero_iff`：angle_eq_zero_iff {x y : V} : an
gle x y = 0 ↔ x != 0 ∧ exists r : Real, 0 < r ∧ y = r • x
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `inv_le_one_of_one_le₀`：inv_le_one_of_one_le₀ (ha : 1 <= a) : a⁻¹ <= 1
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_ne_zero_iff`：smul_ne_zero_iff : r • m != 0 ↔ r != 0 ∧ m != 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Wbtw.angle₂₁₃_eq_zero_of_ne`：∀ {V : Type u_1} {P : Type u_2} [inst : Nor
medAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [
inst_3 : NormedAd…
· 使用定理 `Wbtw.angle₃₁₂_eq_zero_of_ne`：∀ {V : Type u_1} {P : Type u_2} [inst : Nor
medAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [
inst_3 : NormedAd…

--- 原说明 ---
The angle between three points is zero if and only if one of the first and third
 points is
weakly between the other two, and not equal to the second.
-/
theorem angle_eq_zero_iff_ne_and_wbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ := by
  constructor
  · rw [angle, angle_eq_zero_iff]
    rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩
    rcases le_or_gt 1 r with (hr1 | hr1)
    · refine Or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one_of_one_le₀ hr1⟩, ?_⟩
      rw [AffineMap.lineMap_apply, hp₃p₂, smul_smul, inv_mul_cancel₀ hr0.ne.symm, one_smul,
        vsub_vadd]
    · refine Or.inr ⟨?_, r, ⟨hr0.le, hr1.le⟩, ?_⟩
      · rw [← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
        exact ⟨hr0.ne.symm, hp₁p₂⟩
      · rw [AffineMap.lineMap_apply, ← hp₃p₂, vsub_vadd]
  · rintro (⟨hp₁p₂, h⟩ | ⟨hp₃p₂, h⟩)
    · exact h.angle₂₁₃_eq_zero_of_ne hp₁p₂
    · exact h.angle₃₁₂_eq_zero_of_ne hp₃p₂

/-- The angle between three points is zero if and only if one of the first and third points is
strictly between the other two, or those two points are equal but not equal to the second. -/
/-
**EuclideanGeometry.angle_eq_zero_iff_eq_and_ne_or_sbtw** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry`。
形式化陈述：angle_eq_zero_iff_eq_and_ne_or_sbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = 0 ↔ p₁ =
 p₃ ∧ p₁ != p₂ ∨ Sbtw Real p₂ p₁ p₃ ∨ Sbtw Real p₂ p₃ p₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw`：angle_eq_zero_iff_ne_an
d_wbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = 0 ↔ p₁ != p₂ ∧ Wbtw Real p₂ p₁ p₃ ∨ p₃ != p
₂ ∧ Wbtw Real p₂ p₃ p₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p

--- 原说明 ---
The angle between three points is zero if and only if one of the first and third
 points is
strictly between the other two, or those two points are equal but not equal to t
he second.
-/
theorem angle_eq_zero_iff_eq_and_ne_or_sbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ = p₃ ∧ p₁ ≠ p₂ ∨ Sbtw ℝ p₂ p₁ p₃ ∨ Sbtw ℝ p₂ p₃ p₁ := by
  rw [angle_eq_zero_iff_ne_and_wbtw]
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₁p₃ : p₁ = p₃; · simp [hp₁p₃]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  simp [hp₁p₂, hp₁p₃, Ne.symm hp₁p₃, Sbtw, hp₃p₂]

/-- An Unoriented angle is unchanged by replacing the third point by one strictly further away on
the same ray. -/
/-
**EuclideanGeometry._root_.Sbtw.angle_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Unoriented angle is unchanged by replacing the third point by one strictly fu
rther away on
the same ray.
-/
theorem _root_.Sbtw.angle_eq_right {p₂ p₃ p : P} (p₁ : P) (h : Sbtw ℝ p₂ p₃ p) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p :=
  angle_eq_angle_of_angle_eq_pi _ h.angle₁₂₃_eq_pi

/-- An Unoriented angle is unchanged by replacing the first point by one strictly further away on
the same ray. -/
/-
**EuclideanGeometry._root_.Sbtw.angle_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Unoriented angle is unchanged by replacing the first point by one strictly fu
rther away on
the same ray.
-/
theorem _root_.Sbtw.angle_eq_left {p₁ p p₂ : P} (p₃ : P) (h : Sbtw ℝ p₂ p₁ p) :
    ∠ p₁ p₂ p₃ = ∠ p p₂ p₃ := by
  simpa only [angle_comm] using h.angle_eq_right p₃

/-- An Unoriented angle is unchanged by replacing the third point by one weakly further away on the
same ray. -/
/-
**EuclideanGeometry._root_.Wbtw.angle_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Unoriented angle is unchanged by replacing the third point by one weakly furt
her away on the
same ray.
-/
theorem _root_.Wbtw.angle_eq_right {p₂ p₃ p : P} (p₁ : P) (h : Wbtw ℝ p₂ p₃ p) (hp₃p₂ : p₃ ≠ p₂) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p := by
  by_cases hp₃p : p₃ = p; · simp [hp₃p]
  exact Sbtw.angle_eq_right _ ⟨h, hp₃p₂, hp₃p⟩

/-- An Unoriented angle is unchanged by replacing the first point by one weakly further away on the
same ray. -/
/-
**EuclideanGeometry._root_.Wbtw.angle_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Unoriented angle is unchanged by replacing the first point by one weakly furt
her away on the
same ray.
-/
theorem _root_.Wbtw.angle_eq_left {p₁ p p₂ : P} (p₃ : P) (h : Wbtw ℝ p₂ p₁ p) (hp₁p₂ : p₁ ≠ p₂) :
    ∠ p₁ p₂ p₃ = ∠ p p₂ p₃ := by
  simpa only [angle_comm] using h.angle_eq_right p₃ hp₁p₂
/-
**EuclideanGeometry.angle_pointReflection_right** 是 Mathlib 中的一个引理，位于命名空间 `Eucli
deanGeometry`。
形式化陈述：angle_pointReflection_right {p₁ p₂ p₃ : P} : ∠ p₁ p₂ (AffineEquiv.pointRef
lection Real p₂ p₃) = π - ∠ p₁ p₂ p₃
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.pointReflection_self`：pointReflection_self (x : P) : pointReflecti
on x x = x
· 使用定理 `EuclideanGeometry.angle_self_right`：∀ {V : Type u_1} {P : Type u_2} [ins
t : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAd…
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
（共 61 条，此处仅展示前 30 条）
-/
lemma angle_pointReflection_right {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ (AffineEquiv.pointReflection ℝ p₂ p₃) = π - ∠ p₁ p₂ p₃ := by
  by_cases! h₃₂ : p₃ = p₂
  · simp [h₃₂]
    field
  rw [eq_sub_iff_add_eq]
  apply EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi
  exact Sbtw.angle₁₂₃_eq_pi <| (sbtw_pointReflection_of_ne ℝ h₃₂.symm).symm

/-- Three points are collinear if and only if the first or third point equals the second or the
angle between them is 0 or π. -/
/-
**EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi** 是 M
athlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} : Co
llinear Real ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ 
p₂ p₃ = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.wbtw_or_wbtw_or_wbtw`：Collinear.wbtw_or_wbtw_or_wbtw {x y z : 
P} (h : Collinear R ({x, y, z} : Set P)) : Wbtw R x y z ∨ Wbtw R y z x ∨ Wbtw R 
z x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.angle_eq_pi_iff_sbtw`：angle_eq_pi_iff_sbtw {p₁ p₂ p₃ :
 P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Wbtw.angle₃₁₂_eq_zero_of_ne`：∀ {V : Type u_1} {P : Type u_2} [inst : Nor
medAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [
inst_3 : NormedAd…
· 使用定理 `Wbtw.angle₂₃₁_eq_zero_of_ne`：∀ {V : Type u_1} {P : Type u_2} [inst : Nor
medAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [
inst_3 : NormedAd…
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `collinear_pair`：collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set
 P)
· 使用定理 `EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw`：angle_eq_zero_iff_ne_an
d_wbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = 0 ↔ p₁ != p₂ ∧ Wbtw Real p₂ p₁ p₃ ∨ p₃ != p
₂ ∧ Wbtw Real p₂ p₃ p₁
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `Wbtw.collinear`：Wbtw.collinear {x y z : P} (h : Wbtw R x y z) : Collinea
r R ({x, y, z} : Set P)
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z

--- 原说明 ---
Three points are collinear if and only if the first or third point equals the se
cond or the
angle between them is 0 or π.
-/
theorem collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · replace h := h.wbtw_or_wbtw_or_wbtw
    by_cases h₁₂ : p₁ = p₂
    · exact Or.inl h₁₂
    by_cases h₃₂ : p₃ = p₂
    · exact Or.inr (Or.inl h₃₂)
    rw [or_iff_right h₁₂, or_iff_right h₃₂]
    rcases h with (h | h | h)
    · exact Or.inr (angle_eq_pi_iff_sbtw.2 ⟨h, Ne.symm h₁₂, Ne.symm h₃₂⟩)
    · exact Or.inl (h.angle₃₁₂_eq_zero_of_ne h₃₂)
    · exact Or.inl (h.angle₂₃₁_eq_zero_of_ne h₁₂)
  · rcases h with (rfl | rfl | h | h)
    · simpa using collinear_pair ℝ p₁ p₃
    · simpa using collinear_pair ℝ p₁ p₃
    · rw [angle_eq_zero_iff_ne_and_wbtw] at h
      rcases h with (⟨-, h⟩ | ⟨-, h⟩)
      · rw [Set.insert_comm]
        exact h.collinear
      · rw [Set.insert_comm, Set.pair_comm]
        exact h.collinear
    · rw [angle_eq_pi_iff_sbtw] at h
      exact h.wbtw.collinear

/-- If the angle between three points is 0, they are collinear. -/
/-
**EuclideanGeometry.collinear_of_angle_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：collinear_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) : Collinear
 Real ({p₁, p₂, p₃} : Set P)
参数：h : ∠ p₁ p₂ p₃ = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi
`：collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} : Collin
ear Real ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ …

--- 原说明 ---
If the angle between three points is 0, they are collinear.
-/
theorem collinear_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 <| Or.inr <| Or.inr <| Or.inl h

/-- If the angle between three points is π, they are collinear. -/
/-
**EuclideanGeometry.collinear_of_angle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Euclidea
nGeometry`。
形式化陈述：collinear_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : Collinear R
eal ({p₁, p₂, p₃} : Set P)
参数：h : ∠ p₁ p₂ p₃ = π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi
`：collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} : Collin
ear Real ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ …

--- 原说明 ---
If the angle between three points is π, they are collinear.
-/
theorem collinear_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 <| Or.inr <| Or.inr <| Or.inr h

/-- If three points are not collinear, the angle between them is nonzero. -/
/-
**EuclideanGeometry.angle_ne_zero_of_not_collinear** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：angle_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p
₂, p₃} : Set P)) : ∠ p₁ p₂ p₃ != 0
参数：h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `EuclideanGeometry.collinear_of_angle_eq_zero`：collinear_of_angle_eq_zero
 {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) : Collinear Real ({p₁, p₂, p₃} : Set P)

--- 原说明 ---
If three points are not collinear, the angle between them is nonzero.
-/
theorem angle_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ ≠ 0 :=
  mt collinear_of_angle_eq_zero h

/-- If three points are not collinear, the angle between them is not π. -/
/-
**EuclideanGeometry.angle_ne_pi_of_not_collinear** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：angle_ne_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂,
 p₃} : Set P)) : ∠ p₁ p₂ p₃ != π
参数：h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `EuclideanGeometry.collinear_of_angle_eq_pi`：collinear_of_angle_eq_pi {p₁
 p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : Collinear Real ({p₁, p₂, p₃} : Set P)

--- 原说明 ---
If three points are not collinear, the angle between them is not π.
-/
theorem angle_ne_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ ≠ π :=
  mt collinear_of_angle_eq_pi h

/-- If three points are not collinear, the angle between them is positive. -/
/-
**EuclideanGeometry.angle_pos_of_not_collinear** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：angle_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p
₃} : Set P)) : 0 < ∠ p₁ p₂ p₃
参数：h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `EuclideanGeometry.angle_nonneg`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `EuclideanGeometry.angle_ne_zero_of_not_collinear`：angle_ne_zero_of_not_c
ollinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) : ∠ p₁ p₂ p
₃ != 0

--- 原说明 ---
If three points are not collinear, the angle between them is positive.
-/
theorem angle_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < ∠ p₁ p₂ p₃ :=
  (angle_nonneg _ _ _).lt_of_ne (angle_ne_zero_of_not_collinear h).symm

/-- If three points are not collinear, the angle between them is less than π. -/
/-
**EuclideanGeometry.angle_lt_pi_of_not_collinear** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：angle_lt_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂,
 p₃} : Set P)) : ∠ p₁ p₂ p₃ < π
参数：h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `EuclideanGeometry.angle_le_pi`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_ne_pi_of_not_collinear`：angle_ne_pi_of_not_colli
near {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) : ∠ p₁ p₂ p₃ !=
 π

--- 原说明 ---
If three points are not collinear, the angle between them is less than π.
-/
theorem angle_lt_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ < π :=
  (angle_le_pi _ _ _).lt_of_ne <| angle_ne_pi_of_not_collinear h

/-- The cosine of the angle between three points is 1 if and only if the angle is 0. -/
nonrec theorem cos_eq_one_iff_angle_eq_zero {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = 0 :=
  cos_eq_one_iff_angle_eq_zero

/-- The cosine of the angle between three points is 0 if and only if the angle is π / 2. -/
nonrec theorem cos_eq_zero_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  cos_eq_zero_iff_angle_eq_pi_div_two

/-- The cosine of the angle between three points is -1 if and only if the angle is π. -/
nonrec theorem cos_eq_neg_one_iff_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = -1 ↔ ∠ p₁ p₂ p₃ = π :=
  cos_eq_neg_one_iff_angle_eq_pi

/-- The sine of the angle between three points is 0 if and only if the angle is 0 or π. -/
nonrec theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π :=
  sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi

/-- The sine of the angle between three points is 1 if and only if the angle is π / 2. -/
nonrec theorem sin_eq_one_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  sin_eq_one_iff_angle_eq_pi_div_two

/-- Three points are collinear if and only if the first or third point equals the second or
the sine of the angle between three points is zero. -/
/-
**EuclideanGeometry.collinear_iff_eq_or_eq_or_sin_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：collinear_iff_eq_or_eq_or_sin_eq_zero {p₁ p₂ p₃ : P} : Collinear Real ({p₁
, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ Real.sin (∠ p₁ p₂ p₃) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi`：∀ {V : T
ype u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpac
e ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi
`：collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} : Collin
ear Real ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Three points are collinear if and only if the first or third point equals the se
cond or
the sine of the angle between three points is zero.
-/
theorem collinear_iff_eq_or_eq_or_sin_eq_zero {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ Real.sin (∠ p₁ p₂ p₃) = 0 := by
  rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi,
    collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]

/-- If three points are not collinear, the sine of the angle between them is positive. -/
/-
**EuclideanGeometry.sin_pos_of_not_collinear** 是 Mathlib 中的一个定理，位于命名空间 `Euclidea
nGeometry`。
形式化陈述：sin_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃}
 : Set P)) : 0 < Real.sin (∠ p₁ p₂ p₃)
参数：h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sin_pos_of_pos_of_lt_pi`：sin_pos_of_pos_of_lt_pi {x : Real} (h0x : 
0 < x) (hxp : x < π) : 0 < sin x
· 使用定理 `EuclideanGeometry.angle_pos_of_not_collinear`：angle_pos_of_not_collinear
 {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) : 0 < ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_lt_pi_of_not_collinear`：angle_lt_pi_of_not_colli
near {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) : ∠ p₁ p₂ p₃ < 
π

--- 原说明 ---
If three points are not collinear, the sine of the angle between them is positiv
e.
-/
theorem sin_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < Real.sin (∠ p₁ p₂ p₃) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear h) (angle_lt_pi_of_not_collinear h)

/-- If three points are not collinear, the sine of the angle between them is nonzero. -/
/-
**EuclideanGeometry.sin_ne_zero_of_not_collinear** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：sin_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂,
 p₃} : Set P)) : Real.sin (∠ p₁ p₂ p₃) != 0
参数：h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `EuclideanGeometry.sin_pos_of_not_collinear`：sin_pos_of_not_collinear {p₁
 p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) : 0 < Real.sin (∠ p₁ p₂
 p₃)

--- 原说明 ---
If three points are not collinear, the sine of the angle between them is nonzero
.
-/
theorem sin_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    Real.sin (∠ p₁ p₂ p₃) ≠ 0 :=
  ne_of_gt (sin_pos_of_not_collinear h)

/-- If the sine of the angle between three points is 0, they are collinear. -/
/-
**EuclideanGeometry.collinear_of_sin_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Euclidea
nGeometry`。
形式化陈述：collinear_of_sin_eq_zero {p₁ p₂ p₃ : P} (h : Real.sin (∠ p₁ p₂ p₃) = 0) : 
Collinear Real ({p₁, p₂, p₃} : Set P)
参数：h : Real.sin (∠ p₁ p₂ p₃) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `EuclideanGeometry.sin_ne_zero_of_not_collinear`：sin_ne_zero_of_not_colli
near {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) : Real.sin (∠ p
₁ p₂ p₃) != 0

--- 原说明 ---
If the sine of the angle between three points is 0, they are collinear.
-/
theorem collinear_of_sin_eq_zero {p₁ p₂ p₃ : P} (h : Real.sin (∠ p₁ p₂ p₃) = 0) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
  revert h
  contrapose
  exact sin_ne_zero_of_not_collinear

end EuclideanGeometry

