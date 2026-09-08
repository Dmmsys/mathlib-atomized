/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Oliver Nash
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Module

/-!
# (Local) homeomorphism between a normed space and a ball

In this file we show that a real (semi)normed vector space is homeomorphic to the unit ball.

We formalize it in two ways:

- as a `Homeomorph`, see `Homeomorph.unitBall`;
- as an `OpenPartialHomeomorph` with `source = Set.univ` and `target = Metric.ball (0 : E) 1`.

While the former approach is more natural, the latter approach provides us
with a globally defined inverse function which makes it easier to say
that this homeomorphism is in fact a diffeomorphism.

We also show that the unit ball `Metric.ball (0 : E) 1` is homeomorphic
to a ball of positive radius in an affine space over `E`, see `OpenPartialHomeomorph.unitBallBall`.

## Tags

homeomorphism, ball
-/

@[expose] public section

open Set Metric Pointwise
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

/-- Local homeomorphism between a real (semi)normed space and the unit ball.
See also `Homeomorph.unitBall`. -/
@[simps -isSimp]
/-
**OpenPartialHomeomorph.univUnitBall** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E where toFun
 x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Local homeomorphism between a real (semi)normed space and the unit ball.
See also `Homeomorph.unitBall`.
-/
def OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E where
  toFun x := (√(1 + ‖x‖ ^ 2))⁻¹ • x
  invFun y := (√(1 - ‖(y : E)‖ ^ 2))⁻¹ • (y : E)
  source := univ
  target := ball 0 1
  map_source' x _ := by
    have : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, ← _root_.div_eq_inv_mul,
      div_lt_one (abs_pos.mpr <| Real.sqrt_ne_zero'.mpr this), ← abs_norm x, ← sq_lt_sq,
      abs_norm, Real.sq_sqrt this.le]
    exact lt_one_add _
  map_target' _ _ := trivial
  left_inv' x _ := by
    match_scalars
    simp [norm_smul]
    field_simp
    simp [sq_abs, Real.sq_sqrt (zero_lt_one_add_norm_sq x).le]
  right_inv' y hy := by
    have : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y, mem_ball_zero_iff.1 hy]
    match_scalars
    simp [norm_smul]
    field_simp
    simp [field, sq_abs, Real.sq_sqrt this.le]
  open_source := isOpen_univ
  open_target := isOpen_ball
  continuousOn_toFun := by
    suffices Continuous fun (x : E) => (√(1 + ‖x‖ ^ 2))⁻¹ by fun_prop
    exact Continuous.inv₀ (by fun_prop) fun x => Real.sqrt_ne_zero'.mpr (by positivity)
  continuousOn_invFun := by
    have : ∀ y ∈ ball (0 : E) 1, √(1 - ‖(y : E)‖ ^ 2) ≠ 0 := fun y hy ↦ by
      rw [Real.sqrt_ne_zero']
      nlinarith [norm_nonneg y, mem_ball_zero_iff.1 hy]
    exact ContinuousOn.smul (ContinuousOn.inv₀
      (continuousOn_const.sub (continuous_norm.continuousOn.pow _)).sqrt this) continuousOn_id

@[simp]
/-
**OpenPartialHomeomorph.univUnitBall_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.univUnitBall_apply_zero : univUnitBall (0 : E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.univUnitBall_apply`：∀ {E : Type u_1} [inst : Semin
ormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (x : E),   ↑OpenPartialHomeomorp
h.univUnitBall x = (√(1 + ‖x‖ …
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.sqrt_one`：sqrt_one : √1 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem OpenPartialHomeomorph.univUnitBall_apply_zero : univUnitBall (0 : E) = 0 := by
  simp [OpenPartialHomeomorph.univUnitBall_apply]

@[simp]
/-
**OpenPartialHomeomorph.univUnitBall_symm_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：OpenPartialHomeomorph.univUnitBall_symm_apply_zero : univUnitBall.symm (0 
: E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.univUnitBall_symm_apply`：∀ {E : Type u_1} [inst : 
SeminormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (y : E),   ↑OpenPartialHome
omorph.univUnitBall.symm y = (√(1 -…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Real.sqrt_one`：sqrt_one : √1 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem OpenPartialHomeomorph.univUnitBall_symm_apply_zero : univUnitBall.symm (0 : E) = 0 := by
  simp [OpenPartialHomeomorph.univUnitBall_symm_apply]

/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ‖x‖²)^(- ½) • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`Homeomorph.unitBall_apply_coe` and `Homeomorph.unitBall_symm_apply` as `@[simp]`.

See also `Homeomorph.contDiff_unitBall` and `OpenPartialHomeomorph.contDiffOn_unitBall_symm`
for smoothness properties that hold when `E` is an inner-product space. -/
@[simps! -isSimp]
/-
**Homeomorph.unitBall** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.unitBall : E ≃ₜ ball (0 : E) 1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (semi) normed real vector space is homeomorphic to the unit ball in the same s
pace.
This homeomorphism sends `x : E` to `(1 + ‖x‖²)^(- ½) • x`.

In many cases the actual implementation is not important, so we don't mark the p
rojection lemmas
`Homeomorph.unitBall_apply_coe` and `Homeomorph.unitBall_symm_apply` as `@[simp]
`.

See also `Homeomorph.contDiff_unitBall` and `OpenPartialHomeomorph.contDiffOn_un
itBall_symm`
for smoothness properties that hold when `E` is an inner-product space.
-/
def Homeomorph.unitBall : E ≃ₜ ball (0 : E) 1 :=
  (Homeomorph.Set.univ _).symm.trans OpenPartialHomeomorph.univUnitBall.toHomeomorphSourceTarget

@[simp]
/-
**Homeomorph.coe_unitBall_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.coe_unitBall_apply_zero : (Homeomorph.unitBall (0 : E) : E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.univUnitBall_apply_zero`：OpenPartialHomeomorph.uni
vUnitBall_apply_zero : univUnitBall (0 : E) = 0
-/
theorem Homeomorph.coe_unitBall_apply_zero :
    (Homeomorph.unitBall (0 : E) : E) = 0 :=
  OpenPartialHomeomorph.univUnitBall_apply_zero

variable {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]

namespace OpenPartialHomeomorph

/-- Affine homeomorphism `(r • · +ᵥ c)` between a normed space and an add torsor over this space,
interpreted as an `OpenPartialHomeomorph` between `Metric.ball 0 1` and `Metric.ball c r`. -/
@[simps!]
/-
**OpenPartialHomeomorph.unitBallBall** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：unitBallBall (c : P) (r : Real) (hr : 0 < r) : OpenPartialHomeomorph E P
参数：c : P；r : Real；hr : 0 < r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Affine homeomorphism `(r • · +ᵥ c)` between a normed space and an add torsor ove
r this space,
interpreted as an `OpenPartialHomeomorph` between `Metric.ball 0 1` and `Metric.
ball c r`.
-/
def unitBallBall (c : P) (r : ℝ) (hr : 0 < r) : OpenPartialHomeomorph E P :=
  ((Homeomorph.smulOfNeZero r hr.ne').trans
      (IsometryEquiv.vaddConst c).toHomeomorph).toOpenPartialHomeomorphOfImageEq
      (ball 0 1) isOpen_ball (ball c r) <| by
    change (IsometryEquiv.vaddConst c) ∘ (r • ·) '' ball (0 : E) 1 = ball c r
    rw [image_comp, image_smul, smul_unitBall hr.ne', IsometryEquiv.image_ball]
    simp [abs_of_pos hr]

/-- If `r > 0`, then `OpenPartialHomeomorph.univBall c r` is a smooth open partial homeomorphism
with `source = Set.univ` and `target = Metric.ball c r`.
Otherwise, it is the translation by `c`.
Thus in all cases, it sends `0` to `c`, see `OpenPartialHomeomorph.univBall_apply_zero`. -/
/-
**OpenPartialHomeomorph.univBall** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorp
h`。
形式化陈述：univBall (c : P) (r : Real) : OpenPartialHomeomorph E P
参数：c : P；r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `r > 0`, then `OpenPartialHomeomorph.univBall c r` is a smooth open partial h
omeomorphism
with `source = Set.univ` and `target = Metric.ball c r`.
Otherwise, it is the translation by `c`.
Thus in all cases, it sends `0` to `c`, see `OpenPartialHomeomorph.univBall_appl
y_zero`.
-/
def univBall (c : P) (r : ℝ) : OpenPartialHomeomorph E P :=
  if h : 0 < r then univUnitBall.trans' (unitBallBall c r h) rfl
  else (IsometryEquiv.vaddConst c).toHomeomorph.toOpenPartialHomeomorph

@[simp]
/-
**OpenPartialHomeomorph.univBall_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：univBall_source (c : P) (r : Real) : (univBall c r).source = univ
参数：c : P；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem univBall_source (c : P) (r : ℝ) : (univBall c r).source = univ := by
  unfold univBall; split_ifs <;> rfl
/-
**OpenPartialHomeomorph.univBall_target** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：univBall_target (c : P) {r : Real} (hr : 0 < r) : (univBall c r).target = 
ball c r
参数：c : P；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.univBall.eq_1`：∀ {E : Type u_1} [inst : Seminormed
AddCommGroup E] [inst_1 : NormedSpace ℝ E] {P : Type u_2}   [inst_2 : PseudoMetr
icSpace P] [inst_3 : Norm…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem univBall_target (c : P) {r : ℝ} (hr : 0 < r) : (univBall c r).target = ball c r := by
  rw [univBall, dif_pos hr]; rfl
/-
**OpenPartialHomeomorph.ball_subset_univBall_target** 是 Mathlib 中的一个定理，位于命名空间 `O
penPartialHomeomorph`。
形式化陈述：ball_subset_univBall_target (c : P) (r : Real) : ball c r subseteq (univBa
ll c r).target
参数：c : P；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.univBall_target`：univBall_target (c : P) {r : Real
} (hr : 0 < r) : (univBall c r).target = ball c r
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `OpenPartialHomeomorph.univBall.eq_1`：∀ {E : Type u_1} [inst : Seminormed
AddCommGroup E] [inst_1 : NormedSpace ℝ E] {P : Type u_2}   [inst_2 : PseudoMetr
icSpace P] [inst_3 : Norm…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ball_subset_univBall_target (c : P) (r : ℝ) : ball c r ⊆ (univBall c r).target := by
  by_cases hr : 0 < r
  · rw [univBall_target c hr]
  · rw [univBall, dif_neg hr]
    exact subset_univ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**OpenPartialHomeomorph.univBall_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `OpenParti
alHomeomorph`。
形式化陈述：univBall_apply_zero (c : P) (r : Real) : univBall c r 0 = c
参数：c : P；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OpenPartialHomeomorph.trans'_apply`：∀ {X : Type u_1} {Y : Type u_3} {Z :
 Type u_5} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 :
 TopologicalSpace Z] (e …
· 使用定理 `OpenPartialHomeomorph.univUnitBall_apply_zero`：OpenPartialHomeomorph.uni
vUnitBall_apply_zero : univUnitBall (0 : E) = 0
· 使用定理 `OpenPartialHomeomorph.unitBallBall_apply`：∀ {E : Type u_1} [inst : Semin
ormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {P : Type u_2}   [inst_2 : Pseud
oMetricSpace P] [inst_3 : Norm…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_apply`：∀ {X : Type u_1} {Y : Type u_3
} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   ↑e.t
oOpenPartialHomeomorph = ⇑e
· 使用定理 `IsometryEquiv.vaddConst_apply`：∀ {V : Type u_2} {P : Type u_3} [inst : S
eminormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTor
sor V P] (x : P) (v…
-/
theorem univBall_apply_zero (c : P) (r : ℝ) : univBall c r 0 = c := by
  unfold univBall; split_ifs <;> simp

@[simp]
/-
**OpenPartialHomeomorph.univBall_symm_apply_center** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：univBall_symm_apply_center (c : P) (r : Real) : (univBall c r).symm c = 0
参数：c : P；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.univBall_source`：univBall_source (c : P) (r : Real
) : (univBall c r).source = univ
· 使用定理 `OpenPartialHomeomorph.univBall_apply_zero`：univBall_apply_zero (c : P) (
r : Real) : univBall c r 0 = c
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
-/
theorem univBall_symm_apply_center (c : P) (r : ℝ) : (univBall c r).symm c = 0 := by
  have : 0 ∈ (univBall c r).source := by simp
  simpa only [univBall_apply_zero] using (univBall c r).left_inv this

@[continuity]
/-
**OpenPartialHomeomorph.continuous_univBall** 是 Mathlib 中的一个定理，位于命名空间 `OpenParti
alHomeomorph`。
形式化陈述：continuous_univBall (c : P) (r : Real) : Continuous (univBall c r)
参数：c : P；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.univBall_source`：univBall_source (c : P) (r : Real
) : (univBall c r).source = univ
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
-/
theorem continuous_univBall (c : P) (r : ℝ) : Continuous (univBall c r) := by
  simpa [continuousOn_univ] using (univBall c r).continuousOn
/-
**OpenPartialHomeomorph.continuousOn_univBall_symm** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：continuousOn_univBall_symm (c : P) (r : Real) : ContinuousOn (univBall c r
).symm (ball c r)
参数：c : P；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
· 使用定理 `OpenPartialHomeomorph.ball_subset_univBall_target`：ball_subset_univBall_
target (c : P) (r : Real) : ball c r subseteq (univBall c r).target
-/
theorem continuousOn_univBall_symm (c : P) (r : ℝ) : ContinuousOn (univBall c r).symm (ball c r) :=
  (univBall c r).symm.continuousOn.mono <| ball_subset_univBall_target c r

end OpenPartialHomeomorph

