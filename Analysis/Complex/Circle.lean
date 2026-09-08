/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The circle

This file defines `Circle` to be the metric sphere (`Metric.sphere`) in `ℂ` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `ℂ`
* a group
* a topological group

We furthermore define `Circle.exp` to be the natural map `fun t ↦ exp (t * I)` from `ℝ` to
`Circle`, and show that this map is a group homomorphism.

We define two additive characters onto the circle:
* `Real.fourierChar`: The character `fun x ↦ exp ((2 * π * x) * I)` (for which we introduce the
  notation `𝐞` in the scope `FourierTransform`). This uses the analyst convention that there is a
  `2 * π` in the exponent.
* `Real.probChar`: The character `fun x ↦ exp (x * I)`, which uses the probabilist convention that
  there is no `2 * π` in the exponent.

## Implementation notes

Because later (in `Geometry.Manifold.Instances.Sphere`) one wants to equip the circle with a smooth
manifold structure borrowed from `Metric.sphere`, the underlying set is
`{z : ℂ | abs (z - 0) = 1}`.  This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `Complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | normSq z = 1}`, which
is the kernel of the homomorphism `Complex.normSq` from `ℂ` to `ℝ`.

-/

@[expose] public section


noncomputable section

open Complex Function Metric ComplexConjugate

/-- The unit circle in `ℂ`. -/
@[wikidata Q203425]
/-
**Circle** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Circle : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit circle in `ℂ`.
-/
def Circle : Type := Submonoid.unitSphere ℂ
deriving TopologicalSpace

namespace Circle
variable {x y : Circle}

/-
**Circle.instCoeOut** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instCoeOut : CoeOut Circle Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeOut : CoeOut Circle ℂ := subtypeCoe
/-
**Circle.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instCommGroup : CommGroup Circle
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroup : CommGroup Circle := inferInstanceAs <| CommGroup (sphere _ _)
/-
**Circle.** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasDistribNeg Circle := inferInstanceAs <| HasDistribNeg (sphere _ _)
/-
**Circle.** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousNeg Circle := inferInstanceAs <| ContinuousNeg (sphere _ _)
/-
**Circle.instMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instMetricSpace : MetricSpace Circle
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMetricSpace : MetricSpace Circle := inferInstanceAs <| MetricSpace (sphere _ _)
/-
**Circle.ext** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ {x y : Circle}, ↑x = ↑y → x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
@[ext] lemma ext : (x : ℂ) = y → x = y := Subtype.ext
/-
**Circle.coe_injective** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：coe_injective : Injective ((↑) : Circle -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.ext`：∀ {x y : Circle}, ↑x = ↑y → x = y
-/
lemma coe_injective : Injective ((↑) : Circle → ℂ) := fun _ _ ↦ ext

-- Not simp because `SetLike.coe_eq_coe` already proves it
/-
**Circle.coe_inj** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：coe_inj : (x : Complex) = y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Circle.coe_injective`：coe_injective : Injective ((↑) : Circle -> Complex
)
-/
lemma coe_inj : (x : ℂ) = y ↔ x = y := coe_injective.eq_iff
/-
**Circle.norm_coe** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：norm_coe (z : Circle) : ‖(z : Complex)‖ = 1
参数：z : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_sphere_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E]
 {a : E} {r : ℝ}, a ∈ Metric.sphere 0 r ↔ ‖a‖ = r
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma norm_coe (z : Circle) : ‖(z : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.1 z.2

set_option backward.isDefEq.respectTransparency false in
/-
**Circle.normSq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (z : Circle), Complex.normSq ↑z = 1
参数：z : Circle。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `norm_eq_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ} (x : ↑(Metric.sphere 0 r)), ‖↑x‖ = r
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma normSq_coe (z : Circle) : normSq z = 1 := by simp [normSq_eq_norm_sq]
/-
**Circle.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (z : Circle), ↑z ≠ 0
参数：z : Circle。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_zero_of_mem_unit_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup 
E] (x : ↑(Metric.sphere 0 1)), ↑x ≠ 0
-/
@[simp] lemma coe_ne_zero (z : Circle) : (z : ℂ) ≠ 0 := ne_zero_of_mem_unit_sphere z
/-
**Circle.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_one : ↑(1 : Circle) = (1 : ℂ) := rfl
-- Not simp because `OneMemClass.coe_eq_one` already proves it
/-
**Circle.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ {x : Circle}, ↑x = 1 ↔ x = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Circle.coe_inj`：coe_inj : (x : Complex) = y ↔ x = y
· 使用定理 `Circle.coe_one`：↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[norm_cast] lemma coe_eq_one : (x : ℂ) = 1 ↔ x = 1 := by rw [← coe_inj, coe_one]
/-
**Circle.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (z w : Circle), ↑(z * w) = ↑z * ↑w
参数：z w : Circle；z * w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul (z w : Circle) : ↑(z * w) = (z : ℂ) * w := rfl
/-
**Circle.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (z : Circle), ↑z⁻¹ = (↑z)⁻¹
参数：z : Circle；↑z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inv (z : Circle) : ↑z⁻¹ = (z : ℂ)⁻¹ := rfl
/-
**Circle.coe_inv_eq_conj** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：coe_inv_eq_conj (z : Circle) : ↑z⁻¹ = conj (z : Complex)
参数：z : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Circle.coe_inv`：∀ (z : Circle), ↑z⁻¹ = (↑z)⁻¹
· 使用定理 `Complex.inv_def`：inv_def (z : Complex) : z⁻¹ = conj z * ((normSq z)⁻¹ : 
Real)
· 使用定理 `Circle.normSq_coe`：∀ (z : Circle), Complex.normSq ↑z = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma coe_inv_eq_conj (z : Circle) : ↑z⁻¹ = conj (z : ℂ) := by
  rw [coe_inv, inv_def, normSq_coe, inv_one, ofReal_one, mul_one]
/-
**Circle.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (z w : Circle), ↑(z / w) = ↑z / ↑w
参数：z w : Circle；z / w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_div (z w : Circle) : ↑(z / w) = (z : ℂ) / w := rfl
/-
**Circle.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (z : Circle) (n : ℕ), ↑(z ^ n) = ↑z ^ n
参数：z : Circle；n : ℕ；z ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pow (z : Circle) (n : ℕ) : ↑(z ^ n) = (z : ℂ) ^ n := rfl
/-
**Circle.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (z : Circle) (n : ℤ), ↑(z ^ n) = ↑z ^ n
参数：z : Circle；n : ℤ；z ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zpow (z : Circle) (n : ℤ) : ↑(z ^ n) = (z : ℂ) ^ n := rfl
/-
**Circle.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (x : Circle), ↑(-x) = -↑x
参数：x : Circle；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_neg (x : Circle) : ↑(-x) = -(x : ℂ) := rfl
/-
**Circle.neg_ne_self** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：neg_ne_self (x : Circle) : -x != x
参数：x : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.coe_ne_zero`：∀ (z : Circle), ↑z ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_eq_self`：∀ {G : Type u_2} [inst : AddGroup G] [IsAddTorsionFree G] {
a : G}, -a = a ↔ a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Circle.coe_neg`：∀ (x : Circle), ↑(-x) = -↑x
-/
lemma neg_ne_self (x : Circle) : -x ≠ x :=
  fun h ↦ coe_ne_zero x <| neg_eq_self.mp <| coe_neg x ▸ congrArg Subtype.val h

/-- The coercion `Circle → ℂ` as a monoid homomorphism. -/
@[simps]
/-
**Circle.coeHom** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：coeHom : Circle ->* Complex where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.coe_one`：↑1 = 1
· 使用定理 `Circle.coe_mul`：∀ (z w : Circle), ↑(z * w) = ↑z * ↑w

--- 原说明 ---
The coercion `Circle → ℂ` as a monoid homomorphism.
-/
def coeHom : Circle →* ℂ where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul

/-- The elements of the circle embed into the units. -/
/-
**Circle.toUnits** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：toUnits : Circle ->* Units Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The elements of the circle embed into the units.
-/
def toUnits : Circle →* Units ℂ := unitSphereToUnits ℂ

-- written manually because `@[simps]` generated the wrong lemma
/-
**Circle.toUnits_apply** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (z : Circle), Circle.toUnits z = Units.mk0 ↑z ⋯
参数：z : Circle。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toUnits_apply (z : Circle) : toUnits z = Units.mk0 ↑z z.coe_ne_zero := rfl
/-
**Circle.** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompactSpace Circle := inferInstanceAs <| CompactSpace (sphere _ _)
/-
**Circle.** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalGroup Circle := inferInstanceAs <| IsTopologicalGroup (sphere _ _)
/-
**Circle.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instUniformSpace : UniformSpace Circle
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace : UniformSpace Circle := inferInstanceAs <| UniformSpace (sphere _ _)

/-- If `z` is a nonzero complex number, then `conj z / z` belongs to the unit circle. -/
@[simps]
/-
**Circle.ofConjDivSelf** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：ofConjDivSelf (z : Complex) (hz : z != 0) : Circle where val
参数：z : Complex；hz : z != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `z` is a nonzero complex number, then `conj z / z` belongs to the unit circle
.
-/
def ofConjDivSelf (z : ℂ) (hz : z ≠ 0) : Circle where
  val := conj z / z
  property := mem_sphere_zero_iff_norm.2 <| by
    rw [norm_div, RCLike.norm_conj, div_self]; exact norm_ne_zero_iff.mpr hz

/-- The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`. -/
/-
**Circle.exp** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：exp : C(Real, Circle) where toFun t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`.
-/
def exp : C(ℝ, Circle) where
  toFun t := ⟨(t * I).exp, by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I]⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop)
    (by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I])

@[simp, norm_cast]
/-
**Circle.coe_exp** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
参数：t : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_exp (t : ℝ) : exp t = Complex.exp (t * Complex.I) := rfl

@[simp]
/-
**Circle.exp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：exp_zero : exp 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Circle.coe_exp`：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
· 使用定理 `Complex.ofReal_zero`：ofReal_zero : ((0 : Real) : Complex) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `Circle.coe_one`：↑1 = 1
-/
theorem exp_zero : exp 0 = 1 :=
  Subtype.ext <| by rw [coe_exp, ofReal_zero, zero_mul, Complex.exp_zero, coe_one]

@[simp]
/-
**Circle.exp_add** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：exp_add (x y : Real) : exp (x + y) = exp x * exp y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exp_add (x y : ℝ) : exp (x + y) = exp x * exp y :=
  Subtype.ext <| by
    simp only [coe_exp, ofReal_add, add_mul, Complex.exp_add, coe_mul]

/-- The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`,
considered as a homomorphism of groups. -/
@[simps]
/-
**Circle.expHom** 是 Mathlib 中的一个定义，位于命名空间 `Circle`。
形式化陈述：expHom : Real ->+ Additive Circle where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `Circle.exp_add`：exp_add (x y : Real) : exp (x + y) = exp x * exp y

--- 原说明 ---
The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`,
considered as a homomorphism of groups.
-/
def expHom : ℝ →+ Additive Circle where
  toFun := Additive.ofMul ∘ exp
  map_zero' := exp_zero
  map_add' := exp_add
/-
**Circle.exp_sub** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (x y : ℝ), Circle.exp (x - y) = Circle.exp x / Circle.exp y
参数：x y : ℝ；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
-/
@[simp] lemma exp_sub (x y : ℝ) : exp (x - y) = exp x / exp y := expHom.map_sub x y
/-
**Circle.exp_neg** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (x : ℝ), Circle.exp (-x) = (Circle.exp x)⁻¹
参数：x : ℝ；-x；Circle.exp x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (a : α), f (-a) = -f a
-/
@[simp] lemma exp_neg (x : ℝ) : exp (-x) = (exp x)⁻¹ := expHom.map_neg x
/-
**Circle.exp_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_nsmul (x : Real) (n : Nat) : exp (n • x) = exp x ^ n
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
lemma exp_nsmul (x : ℝ) (n : ℕ) : exp (n • x) = exp x ^ n := expHom.map_nsmul n x
/-
**Circle.exp_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_zsmul (x : Real) (z : Int) : exp (z • x) = exp x ^ z
参数：x : Real；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zsmul`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup
 α] [inst_1 : SubtractionMonoid β] (f : α →+ β) (n : ℤ) (g : α),   f (n • g) = n
 • f g
-/
lemma exp_zsmul (x : ℝ) (z : ℤ) : exp (z • x) = exp x ^ z := expHom.map_zsmul z x
/-
**Circle.exp_natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (x : ℝ) (n : ℕ), Circle.exp (↑n * x) = Circle.exp x ^ n
参数：x : ℝ；n : ℕ；↑n * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `Circle.exp_nsmul`：exp_nsmul (x : Real) (n : Nat) : exp (n • x) = exp x ^
 n
-/
@[simp] lemma exp_natCast_mul (x : ℝ) (n : ℕ) : exp (n * x) = exp x ^ n := by
  rw [← nsmul_eq_mul, exp_nsmul]
/-
**Circle.exp_intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ (x : ℝ) (z : ℤ), Circle.exp (↑z * x) = Circle.exp x ^ z
参数：x : ℝ；z : ℤ；↑z * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用引理 `Circle.exp_zsmul`：exp_zsmul (x : Real) (z : Int) : exp (z • x) = exp x ^
 z
-/
@[simp] lemma exp_intCast_mul (x : ℝ) (z : ℤ) : exp (z * x) = exp x ^ z := by
  rw [← zsmul_eq_mul, exp_zsmul]
/-
**Circle.exp_pi_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：exp_pi_ne_one : Circle.exp Real.pi != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isInt_eq_false`：∀ {α : Type u_1} [inst : Ring α] [C
harZero α] {a b : α} {a' b' : ℤ},   Mathlib.Meta.NormNum.IsInt a a' → Mathlib.Me
ta.NormNum.IsInt b b' → d…
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.exp_pi_mul_I`：exp_pi_mul_I : exp (π * I) = -1
· 使用定理 `Circle.coe_exp`：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
-/
lemma exp_pi_ne_one : Circle.exp Real.pi ≠ 1 := by
  intro h
  have heq : (Circle.exp Real.pi : ℂ) = 1 := by simp [h]
  rw [Circle.coe_exp, exp_pi_mul_I] at heq
  norm_num at heq

variable {e : AddChar ℝ Circle}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Circle.star_addChar** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：star_addChar (x : Real) : star ((e x) : Complex) = e (-x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Circle.coe_inv_eq_conj`：coe_inv_eq_conj (z : Circle) : ↑z⁻¹ = conj (z : 
Complex)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用引理 `AddChar.map_neg_eq_inv`：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a
) = (ψ a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma star_addChar (x : ℝ) : star ((e x) : ℂ) = e (-x) := by
  have h := Circle.coe_inv_eq_conj ⟨e x, ?_⟩
  · simp [← h, e.map_neg_eq_inv]
  · simp only [Submonoid.unitSphere, SetLike.coe_mem]

@[simp]
/-
**Circle.starRingEnd_addChar** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：starRingEnd_addChar (x : Real) : starRingEnd Complex (e x) = e (-x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Circle.star_addChar`：star_addChar (x : Real) : star ((e x) : Complex) = 
e (-x)
-/
lemma starRingEnd_addChar (x : ℝ) : starRingEnd ℂ (e x) = e (-x) := star_addChar x

variable {α β M : Type*}
/-
**Circle.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instSMul [SMul Complex α] : SMul Circle α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul [SMul ℂ α] : SMul Circle α := inferInstanceAs <| SMul (Submonoid.unitSphere _) α
/-
**Circle.instSMulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instSMulCommClass_left [SMul Complex β] [SMul α β] [SMulCommClass Complex 
α β] : SMulCommClass Circle α β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulCommClass_left [SMul ℂ β] [SMul α β] [SMulCommClass ℂ α β] :
    SMulCommClass Circle α β :=
  inferInstanceAs <| SMulCommClass (Submonoid.unitSphere _) α β
/-
**Circle.instSMulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instSMulCommClass_right [SMul Complex β] [SMul α β] [SMulCommClass α Compl
ex β] : SMulCommClass α Circle β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulCommClass_right [SMul ℂ β] [SMul α β] [SMulCommClass α ℂ β] :
    SMulCommClass α Circle β :=
  inferInstanceAs <| SMulCommClass α (Submonoid.unitSphere _) β
/-
**Circle.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instIsScalarTower [SMul Complex α] [SMul Complex β] [SMul α β] [IsScalarTo
wer Complex α β] : IsScalarTower Circle α β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower [SMul ℂ α] [SMul ℂ β] [SMul α β] [IsScalarTower ℂ α β] :
    IsScalarTower Circle α β :=
  inferInstanceAs <| IsScalarTower (Submonoid.unitSphere _) α β
/-
**Circle.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instMulAction [MulAction Complex α] : MulAction Circle α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction [MulAction ℂ α] : MulAction Circle α :=
  inferInstanceAs <| MulAction (Submonoid.unitSphere _) α
/-
**Circle.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instDistribMulAction [AddMonoid M] [DistribMulAction Complex M] : DistribM
ulAction Circle M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [AddMonoid M] [DistribMulAction ℂ M] :
    DistribMulAction Circle M :=
  inferInstanceAs <| DistribMulAction (Submonoid.unitSphere _) M
/-
**Circle.smul_def** 是 Mathlib 中的一个引理，位于命名空间 `Circle`。
形式化陈述：smul_def [SMul Complex α] (z : Circle) (a : α) : z • a = (z : Complex) • a
参数：z : Circle；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_def [SMul ℂ α] (z : Circle) (a : α) : z • a = (z : ℂ) • a := rfl
/-
**Circle.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `Circle`。
形式化陈述：instContinuousSMul [TopologicalSpace α] [MulAction Complex α] [ContinuousS
Mul Complex α] : ContinuousSMul Circle α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instContinuousSMul [TopologicalSpace α] [MulAction ℂ α] [ContinuousSMul ℂ α] :
    ContinuousSMul Circle α :=
  inferInstanceAs <| ContinuousSMul (Submonoid.unitSphere _) α

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Circle.norm_smul** 是 Mathlib 中的一个定理，位于命名空间 `Circle`。
形式化陈述：∀ {E : Type u_4} [inst : SeminormedAddCommGroup E] [inst_1 : NormedSpace ℂ
 E] (u : Circle) (v : E), ‖u • v‖ = ‖v‖
参数：u : Circle；v : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Circle.smul_def`：smul_def [SMul Complex α] (z : Circle) (a : α) : z • a 
= (z : Complex) • a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_eq_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ} (x : ↑(Metric.sphere 0 r)), ‖↑x‖ = r
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected lemma norm_smul {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (u : Circle) (v : E) :
    ‖u • v‖ = ‖v‖ := by
  rw [smul_def, norm_smul, norm_eq_of_mem_sphere, one_mul]

end Circle

namespace Real

/-- The additive character from `ℝ` onto the circle, given by `fun x ↦ exp (2 * π * x * I)`.
Denoted as `𝐞` within the `Real.FourierTransform` namespace. This uses the analyst convention that
there is a `2 * π` in the exponent. -/
/-
**Real.fourierChar** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：fourierChar : AddChar Real Circle where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive character from `ℝ` onto the circle, given by `fun x ↦ exp (2 * π * 
x * I)`.
Denoted as `𝐞` within the `Real.FourierTransform` namespace. This uses the analy
st convention that
there is a `2 * π` in the exponent.
-/
def fourierChar : AddChar ℝ Circle where
  toFun z := .exp (2 * π * z)
  map_zero_eq_one' := by rw [mul_zero, Circle.exp_zero]
  map_add_eq_mul' x y := by rw [mul_add, Circle.exp_add]

@[inherit_doc] scoped[FourierTransform] notation "𝐞" => Real.fourierChar

open FourierTransform
/-
**Real.fourierChar_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourierChar_apply' (x : Real) : 𝐞 x = Circle.exp (2 * π * x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fourierChar_apply' (x : ℝ) : 𝐞 x = Circle.exp (2 * π * x) := rfl
/-
**Real.fourierChar_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourierChar_apply (x : Real) : 𝐞 x = Complex.exp (↑(2 * π * x) * Complex.I
)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fourierChar_apply (x : ℝ) : 𝐞 x = Complex.exp (↑(2 * π * x) * Complex.I) := rfl

@[continuity, fun_prop]
/-
**Real.continuous_fourierChar** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_fourierChar : Continuous 𝐞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
theorem continuous_fourierChar : Continuous 𝐞 := Circle.exp.continuous.comp (continuous_const_mul _)
/-
**Real.fourierChar_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourierChar_ne_one : fourierChar != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Circle.exp_pi_ne_one`：exp_pi_ne_one : Circle.exp Real.pi != 1
-/
theorem fourierChar_ne_one : fourierChar ≠ 1 := by
  rw [DFunLike.ne_iff]
  use 2⁻¹
  simp only [fourierChar_apply', AddChar.one_apply]
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  exact Circle.exp_pi_ne_one

/-- The additive character from `ℝ` onto the circle, given by `fun x ↦ exp (x * I)`. This uses the
probabilist convention that there is no `2 * π` in the exponent. -/
/-
**Real.probChar** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：probChar : AddChar Real Circle where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `Circle.exp_add`：exp_add (x y : Real) : exp (x + y) = exp x * exp y

--- 原说明 ---
The additive character from `ℝ` onto the circle, given by `fun x ↦ exp (x * I)`.
 This uses the
probabilist convention that there is no `2 * π` in the exponent.
-/
def probChar : AddChar ℝ Circle where
  toFun := Circle.exp
  map_zero_eq_one' := Circle.exp_zero
  map_add_eq_mul' := Circle.exp_add
/-
**Real.probChar_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：probChar_apply' (x : Real) : probChar x = Circle.exp x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem probChar_apply' (x : ℝ) : probChar x = Circle.exp x := rfl
/-
**Real.probChar_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：probChar_apply (x : Real) : probChar x = Complex.exp (x * Complex.I)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem probChar_apply (x : ℝ) : probChar x = Complex.exp (x * Complex.I) := rfl

@[continuity, fun_prop]
/-
**Real.continuous_probChar** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_probChar : Continuous probChar
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
theorem continuous_probChar : Continuous probChar := map_continuous Circle.exp
/-
**Real.probChar_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：probChar_ne_one : probChar != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用引理 `Circle.exp_pi_ne_one`：exp_pi_ne_one : Circle.exp Real.pi != 1
-/
theorem probChar_ne_one : probChar ≠ 1 := by
  rw [DFunLike.ne_iff]
  use Real.pi
  simpa only [probChar_apply'] using! Circle.exp_pi_ne_one

end Real

