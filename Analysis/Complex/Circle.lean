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
radius `1`. We equip it with the following structure:

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
`{z : ℂ | abs (z - 0) = 1}`. This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `Complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | normSq z = 1}`, which
is the kernel of the homomorphism `Complex.normSq` from `ℂ` to `ℝ`.

-/

@[expose] public section


noncomputable section

open Complex Function Metric ComplexConjugate

/-- The unit circle in `ℂ`. -/
@[wikidata Q203425]
/--
Definition of `Circle` / `Circle` 的定义

English:
definition Circle
  signature: : Type
  body: Submonoid.unitSphere Complex
deriving TopologicalSpace

中文:
定义 Circle
  签名: : 类型
  定义体: Submonoid.unitSphere Complex
deriving TopologicalSpace

Depends on / 依赖: Submonoid, Submonoid.unitSphere, unitSphere
-/
def Circle : Type := Submonoid.unitSphere Complex
deriving TopologicalSpace

namespace Circle
variable {x y : Circle}

/--
Instance `instCoeOut` / 实例 `instCoeOut`

English:
instance instCoeOut
  signature: : CoeOut Circle Complex
  body: subtypeCoe

中文:
实例 instCoeOut
  签名: : CoeOut Circle 复形
  定义体: subtypeCoe

Depends on / 依赖: subtypeCoe
-/
instance instCoeOut : CoeOut Circle Complex := subtypeCoe

/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: : CommGroup Circle
  body: inferInstanceAs CommGroup (sphere _ _)

中文:
实例 instCommGroup
  签名: : 交换群 Circle
  定义体: inferInstanceAs CommGroup (sphere _ _)

Depends on / 依赖: CommGroup, RCLike, RCLike.instContinuousMapUniqueHom, TopologicalSpace, instContinuousMapUniqueHom, sphere
-/
instance instCommGroup : CommGroup Circle := inferInstanceAs CommGroup (sphere _ _)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDistribNeg Circle
  body: inferInstanceAs HasDistribNeg (sphere _ _)

中文:
实例 :
  签名: 有DistribNeg Circle
  定义体: inferInstanceAs HasDistribNeg (sphere _ _)

Depends on / 依赖: HasDistribNeg, sphere
-/
instance : HasDistribNeg Circle := inferInstanceAs HasDistribNeg (sphere _ _)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousNeg Circle
  body: inferInstanceAs ContinuousNeg (sphere _ _)

中文:
实例 :
  签名: 连续取负 Circle
  定义体: inferInstanceAs ContinuousNeg (sphere _ _)

Depends on / 依赖: ContinuousNeg, sphere
-/
instance : ContinuousNeg Circle := inferInstanceAs ContinuousNeg (sphere _ _)
/--
Instance `instMetricSpace` / 实例 `instMetricSpace`

English:
instance instMetricSpace
  signature: : MetricSpace Circle
  body: inferInstanceAs MetricSpace (sphere _ _)

中文:
实例 instMetricSpace
  签名: : 度量空间 Circle
  定义体: inferInstanceAs MetricSpace (sphere _ _)

Depends on / 依赖: MetricSpace, sphere
-/
instance instMetricSpace : MetricSpace Circle := inferInstanceAs MetricSpace (sphere _ _)

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (x : Complex) = y -> x = y
  proof: Subtype.ext

中文:
引理 ext
  结论: (x : 复形) = y -> x = y
  证明: Subtype.ext
-/
@[ext] lemma ext : (x : Complex) = y -> x = y := Subtype.ext

/--
lemma `coe_injective` / 引理 `coe_injective`

English:
lemma coe_injective
  statement: Injective ((↑) : Circle -> Complex)
  proof: fun _ _ => ext

中文:
引理 coe_injective
  结论: 单射 ((↑) : Circle -> 复形)
  证明: fun _ _ => ext
-/
lemma coe_injective : Injective ((↑) : Circle -> Complex) := fun _ _ => ext

-- Not simp because `SetLike.coe_eq_coe` already proves it
/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  statement: (x : Complex) = y ↔ x = y
  proof: coe_injective.eq_iff

中文:
引理 coe_inj
  结论: (x : 复形) = y ↔ x = y
  证明: coe_injective.eq_iff

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
lemma coe_inj : (x : Complex) = y ↔ x = y := coe_injective.eq_iff

/--
lemma `norm_coe` / 引理 `norm_coe`

English:
lemma norm_coe
  given: (z : Circle)
  statement: ‖(z : Complex)‖ = 1
  proof: mem_sphere_zero_iff_norm.1 z.2

中文:
引理 norm_coe
  条件: (z : Circle)
  结论: ‖(z : 复形)‖ = 1
  证明: mem_sphere_zero_iff_norm.1 z.2

Depends on / 依赖: mem_sphere_zero_iff_norm
-/
lemma norm_coe (z : Circle) : ‖(z : Complex)‖ = 1 := mem_sphere_zero_iff_norm.1 z.2

set_option backward.isDefEq.respectTransparency false in
/--
lemma `normSq_coe` / 引理 `normSq_coe`

English:
lemma normSq_coe
  given: (z : Circle)
  statement: normSq z = 1
  proof: by simp [normSq_eq_norm_sq]

中文:
引理 normSq_coe
  条件: (z : Circle)
  结论: normSq z = 1
  证明: by simp [normSq_eq_norm_sq]
-/
@[simp] lemma normSq_coe (z : Circle) : normSq z = 1 := by simp [normSq_eq_norm_sq]
/--
lemma `coe_ne_zero` / 引理 `coe_ne_zero`

English:
lemma coe_ne_zero
  given: (z : Circle)
  statement: (z : Complex) != 0
  proof: ne_zero_of_mem_unit_sphere z

中文:
引理 coe_ne_zero
  条件: (z : Circle)
  结论: (z : 复形) != 0
  证明: ne_zero_of_mem_unit_sphere z
-/
@[simp] lemma coe_ne_zero (z : Circle) : (z : Complex) != 0 := ne_zero_of_mem_unit_sphere z
/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ↑(1 : Circle) = (1 : Complex)
  proof: rfl

中文:
引理 coe_one
  结论: ↑(1 : Circle) = (1 : 复形)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_one : ↑(1 : Circle) = (1 : Complex) := rfl
-- Not simp because `OneMemClass.coe_eq_one` already proves it
/--
lemma `coe_eq_one` / 引理 `coe_eq_one`

English:
lemma coe_eq_one
  statement: (x : Complex) = 1 ↔ x = 1
  proof: by rw [← coe_inj, coe_one]

中文:
引理 coe_eq_one
  结论: (x : 复形) = 1 ↔ x = 1
  证明: by rw [← coe_inj, coe_one]
-/
@[norm_cast] lemma coe_eq_one : (x : Complex) = 1 ↔ x = 1 := by rw [← coe_inj, coe_one]
/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (z w : Circle)
  statement: ↑(z * w) = (z : Complex) * w
  proof: rfl

中文:
引理 coe_mul
  条件: (z w : Circle)
  结论: ↑(z * w) = (z : 复形) * w
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mul (z w : Circle) : ↑(z * w) = (z : Complex) * w := rfl
/--
lemma `coe_inv` / 引理 `coe_inv`

English:
lemma coe_inv
  given: (z : Circle)
  statement: ↑z⁻¹ = (z : Complex)⁻¹
  proof: rfl

中文:
引理 coe_inv
  条件: (z : Circle)
  结论: ↑z⁻¹ = (z : 复形)⁻¹
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inv (z : Circle) : ↑z⁻¹ = (z : Complex)⁻¹ := rfl
/--
lemma `coe_inv_eq_conj` / 引理 `coe_inv_eq_conj`

English:
lemma coe_inv_eq_conj
  given: (z : Circle)
  statement: ↑z⁻¹ = conj (z : Complex)
  proof: by
  rw [coe_inv]; rw [inv_def]; rw [normSq_coe]; rw [inv_one]; rw [ofReal_one]; rw [mul_one]

中文:
引理 coe_inv_eq_conj
  条件: (z : Circle)
  结论: ↑z⁻¹ = conj (z : 复形)
  证明: by
  rw [coe_inv]; rw [inv_def]; rw [normSq_coe]; rw [inv_one]; rw [ofReal_one]; rw [mul_one]

Depends on / 依赖: coe_inv, inv_def, inv_one, mul_one, normSq_coe, ofReal_one
-/
lemma coe_inv_eq_conj (z : Circle) : ↑z⁻¹ = conj (z : Complex) := by
  rw [coe_inv]; rw [inv_def]; rw [normSq_coe]; rw [inv_one]; rw [ofReal_one]; rw [mul_one]

/--
lemma `coe_div` / 引理 `coe_div`

English:
lemma coe_div
  given: (z w : Circle)
  statement: ↑(z / w) = (z : Complex) / w
  proof: rfl

中文:
引理 coe_div
  条件: (z w : Circle)
  结论: ↑(z / w) = (z : 复形) / w
  证明: rfl
-/
@[simp, norm_cast] lemma coe_div (z w : Circle) : ↑(z / w) = (z : Complex) / w := rfl
/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (z : Circle) (n : Nat)
  statement: ↑(z ^ n) = (z : Complex) ^ n
  proof: rfl

中文:
引理 coe_pow
  条件: (z : Circle) (n : 自然数)
  结论: ↑(z ^ n) = (z : 复形) ^ n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_pow (z : Circle) (n : Nat) : ↑(z ^ n) = (z : Complex) ^ n := rfl
/--
lemma `coe_zpow` / 引理 `coe_zpow`

English:
lemma coe_zpow
  given: (z : Circle) (n : Int)
  statement: ↑(z ^ n) = (z : Complex) ^ n
  proof: rfl

中文:
引理 coe_zpow
  条件: (z : Circle) (n : 整数)
  结论: ↑(z ^ n) = (z : 复形) ^ n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zpow (z : Circle) (n : Int) : ↑(z ^ n) = (z : Complex) ^ n := rfl
/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: (x : Circle)
  statement: ↑(-x) = -(x : Complex)
  proof: rfl

中文:
引理 coe_neg
  条件: (x : Circle)
  结论: ↑(-x) = -(x : 复形)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_neg (x : Circle) : ↑(-x) = -(x : Complex) := rfl

/--
lemma `neg_ne_self` / 引理 `neg_ne_self`

English:
lemma neg_ne_self
  given: (x : Circle)
  statement: -x != x
  proof: fun h => coe_ne_zero x neg_eq_self.mp coe_neg x ▸ congrArg Subtype.val h

中文:
引理 neg_ne_self
  条件: (x : Circle)
  结论: -x != x
  证明: fun h => coe_ne_zero x neg_eq_self.mp coe_neg x ▸ congrArg Subtype.val h

Depends on / 依赖: Subtype, Subtype.val, coe_ne_zero, coe_neg, neg_eq_self, neg_eq_self.mp
-/
lemma neg_ne_self (x : Circle) : -x != x :=
fun h => coe_ne_zero x neg_eq_self.mp coe_neg x ▸ congrArg Subtype.val h

/-- The coercion `Circle → ℂ` as a monoid homomorphism. -/
@[simps]
/--
Definition of `coeHom` / `coeHom` 的定义

English:
definition coeHom
  signature: : Circle ->* Complex where
  body: (↑)
  map_one' := coe_one
  map_mul' := coe_mul

中文:
定义 coeHom
  签名: : Circle ->* 复形 where
  定义体: (↑)
  map_one' := coe_one
  map_mul' := coe_mul
-/
def coeHom : Circle ->* Complex where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul

/--
Definition of `toUnits` / `toUnits` 的定义

English:
definition toUnits
  signature: : Circle ->* Units Complex
  body: unitSphereToUnits Complex

中文:
定义 toUnits
  签名: : Circle ->* 单位群 复形
  定义体: unitSphereToUnits Complex

Depends on / 依赖: unitSphereToUnits
-/
def toUnits : Circle ->* Units Complex := unitSphereToUnits Complex

-- written manually because `@[simps]` generated the wrong lemma
/--
lemma `toUnits_apply` / 引理 `toUnits_apply`

English:
lemma toUnits_apply
  given: (z : Circle)
  statement: toUnits z = Units.mk0 ↑z z.coe_ne_zero
  proof: rfl

中文:
引理 toUnits_apply
  条件: (z : Circle)
  结论: toUnits z = 单位群.mk0 ↑z z.coe_ne_zero
  证明: rfl
-/
@[simp] lemma toUnits_apply (z : Circle) : toUnits z = Units.mk0 ↑z z.coe_ne_zero := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompactSpace Circle
  body: inferInstanceAs CompactSpace (sphere _ _)

中文:
实例 :
  签名: 紧空间 Circle
  定义体: inferInstanceAs CompactSpace (sphere _ _)

Depends on / 依赖: CompactSpace, sphere
-/
instance : CompactSpace Circle := inferInstanceAs CompactSpace (sphere _ _)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalGroup Circle
  body: inferInstanceAs IsTopologicalGroup (sphere _ _)

中文:
实例 :
  签名: 是拓扑群 Circle
  定义体: inferInstanceAs IsTopologicalGroup (sphere _ _)

Depends on / 依赖: IsTopologicalGroup, sphere
-/
instance : IsTopologicalGroup Circle := inferInstanceAs IsTopologicalGroup (sphere _ _)
/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace Circle
  body: inferInstanceAs UniformSpace (sphere _ _)

中文:
实例 instUniformSpace
  签名: : 一致空间 Circle
  定义体: inferInstanceAs UniformSpace (sphere _ _)

Depends on / 依赖: UniformSpace, sphere
-/
instance instUniformSpace : UniformSpace Circle := inferInstanceAs UniformSpace (sphere _ _)

/-- If `z` is a nonzero complex number, then `conj z / z` belongs to the unit circle. -/
@[simps]
/--
Definition of `ofConjDivSelf` / `ofConjDivSelf` 的定义

English:
definition ofConjDivSelf
  signature: (z : Complex) (hz : z != 0)
  body: conj z / z
property := mem_sphere_zero_iff_norm.2 by
    rw [norm_div]; rw [RCLike.norm_conj]; rw [div_self]; exact norm_ne_zero_iff.mpr hz

中文:
定义 ofConjDivSelf
  签名: (z : 复形) (hz : z != 0)
  定义体: conj z / z
property := mem_sphere_zero_iff_norm.2 by
    rw [norm_div]; rw [RCLike.norm_conj]; rw [div_self]; exact norm_ne_zero_iff.mpr hz
-/
def ofConjDivSelf (z : Complex) (hz : z != 0) : Circle where
  val := conj z / z
property := mem_sphere_zero_iff_norm.2 by
    rw [norm_div]; rw [RCLike.norm_conj]; rw [div_self]; exact norm_ne_zero_iff.mpr hz

/--
Definition of `exp` / `exp` 的定义

English:
definition exp
  signature: : C(Real, Circle) where
  body: ⟨(t * I).exp, by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I]⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop)
    (by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I])

@[simp, norm_cast]

中文:
定义 exp
  签名: : C(实数, Circle) where
  定义体: ⟨(t * I).exp, by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I]⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop)
    (by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I])

@[simp, norm_cast]

Depends on / 依赖: Submonoid, Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I, unitSphere
-/
def exp : C(Real, Circle) where
  toFun t := ⟨(t * I).exp, by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I]⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop)
    (by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I])

@[simp, norm_cast]
/--
theorem `coe_exp` / 定理 `coe_exp`

English:
theorem coe_exp
  given: (t : Real)
  statement: exp t = Complex.exp (t * Complex.I)
  proof: rfl

@[simp]

中文:
定理 coe_exp
  条件: (t : 实数)
  结论: exp t = 复形.exp (t * 复形.I)
  证明: rfl

@[simp]
-/
theorem coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I) := rfl

@[simp]
/--
theorem `exp_zero` / 定理 `exp_zero`

English:
theorem exp_zero
  statement: exp 0 = 1
  proof: Subtype.ext by rw [coe_exp, ofReal_zero, zero_mul, Complex.exp_zero, coe_one]

@[simp]

中文:
定理 exp_zero
  结论: exp 0 = 1
  证明: Subtype.ext by rw [coe_exp, ofReal_zero, zero_mul, Complex.exp_zero, coe_one]

@[simp]

Depends on / 依赖: Complex.exp_zero, Subtype, Subtype.ext, coe_exp, coe_one, exp_zero, ofReal_zero, zero_mul
-/
theorem exp_zero : exp 0 = 1 :=
Subtype.ext by rw [coe_exp, ofReal_zero, zero_mul, Complex.exp_zero, coe_one]

@[simp]
/--
theorem `exp_add` / 定理 `exp_add`

English:
theorem exp_add
  given: (x y : Real)
  statement: exp (x + y) = exp x * exp y
  proof: Subtype.ext by
    simp only [coe_exp, ofReal_add, add_mul, Complex.exp_add, coe_mul]

中文:
定理 exp_add
  条件: (x y : 实数)
  结论: exp (x + y) = exp x * exp y
  证明: Subtype.ext by
    simp only [coe_exp, ofReal_add, add_mul, Complex.exp_add, coe_mul]

Depends on / 依赖: Complex.exp_add, Subtype, Subtype.ext, add_mul, coe_exp, coe_mul, exp_add, ofReal_add
-/
theorem exp_add (x y : Real) : exp (x + y) = exp x * exp y :=
Subtype.ext by
    simp only [coe_exp, ofReal_add, add_mul, Complex.exp_add, coe_mul]

/-- The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`,
considered as a homomorphism of groups. -/
@[simps]
/--
Definition of `expHom` / `expHom` 的定义

English:
definition expHom
  signature: : Real ->+ Additive Circle where
  body: Additive.ofMul ∘ exp
  map_zero' := exp_zero
  map_add' := exp_add

中文:
定义 expHom
  签名: : 实数 ->+ 加性 Circle where
  定义体: Additive.ofMul ∘ exp
  map_zero' := exp_zero
  map_add' := exp_add

Depends on / 依赖: Additive, Additive.ofMul
-/
def expHom : Real ->+ Additive Circle where
  toFun := Additive.ofMul ∘ exp
  map_zero' := exp_zero
  map_add' := exp_add

/--
lemma `exp_sub` / 引理 `exp_sub`

English:
lemma exp_sub
  given: (x y : Real)
  statement: exp (x - y) = exp x / exp y
  proof: expHom.map_sub x y

中文:
引理 exp_sub
  条件: (x y : 实数)
  结论: exp (x - y) = exp x / exp y
  证明: expHom.map_sub x y
-/
@[simp] lemma exp_sub (x y : Real) : exp (x - y) = exp x / exp y := expHom.map_sub x y
/--
lemma `exp_neg` / 引理 `exp_neg`

English:
lemma exp_neg
  given: (x : Real)
  statement: exp (-x) = (exp x)⁻¹
  proof: expHom.map_neg x

中文:
引理 exp_neg
  条件: (x : 实数)
  结论: exp (-x) = (exp x)⁻¹
  证明: expHom.map_neg x

Depends on / 依赖: continuous, functional, instead, simply
-/
@[simp] lemma exp_neg (x : Real) : exp (-x) = (exp x)⁻¹ := expHom.map_neg x
/--
lemma `exp_nsmul` / 引理 `exp_nsmul`

English:
lemma exp_nsmul
  given: (x : Real) (n : Nat)
  statement: exp (n • x) = exp x ^ n
  proof: expHom.map_nsmul n x

中文:
引理 exp_nsmul
  条件: (x : 实数) (n : 自然数)
  结论: exp (n • x) = exp x ^ n
  证明: expHom.map_nsmul n x

Depends on / 依赖: expHom, expHom.map_nsmul, map_nsmul
-/
lemma exp_nsmul (x : Real) (n : Nat) : exp (n • x) = exp x ^ n := expHom.map_nsmul n x
/--
lemma `exp_zsmul` / 引理 `exp_zsmul`

English:
lemma exp_zsmul
  given: (x : Real) (z : Int)
  statement: exp (z • x) = exp x ^ z
  proof: expHom.map_zsmul z x

中文:
引理 exp_zsmul
  条件: (x : 实数) (z : 整数)
  结论: exp (z • x) = exp x ^ z
  证明: expHom.map_zsmul z x

Depends on / 依赖: expHom, expHom.map_zsmul, map_zsmul
-/
lemma exp_zsmul (x : Real) (z : Int) : exp (z • x) = exp x ^ z := expHom.map_zsmul z x
/--
lemma `exp_natCast_mul` / 引理 `exp_natCast_mul`

English:
lemma exp_natCast_mul
  given: (x : Real) (n : Nat)
  statement: exp (n * x) = exp x ^ n
  proof: by
  rw [← nsmul_eq_mul]; rw [exp_nsmul]

中文:
引理 exp_natCast_mul
  条件: (x : 实数) (n : 自然数)
  结论: exp (n * x) = exp x ^ n
  证明: by
  rw [← nsmul_eq_mul]; rw [exp_nsmul]
-/
@[simp] lemma exp_natCast_mul (x : Real) (n : Nat) : exp (n * x) = exp x ^ n := by
  rw [← nsmul_eq_mul]; rw [exp_nsmul]
/--
lemma `exp_intCast_mul` / 引理 `exp_intCast_mul`

English:
lemma exp_intCast_mul
  given: (x : Real) (z : Int)
  statement: exp (z * x) = exp x ^ z
  proof: by
  rw [← zsmul_eq_mul]; rw [exp_zsmul]

中文:
引理 exp_intCast_mul
  条件: (x : 实数) (z : 整数)
  结论: exp (z * x) = exp x ^ z
  证明: by
  rw [← zsmul_eq_mul]; rw [exp_zsmul]
-/
@[simp] lemma exp_intCast_mul (x : Real) (z : Int) : exp (z * x) = exp x ^ z := by
  rw [← zsmul_eq_mul]; rw [exp_zsmul]

/--
lemma `exp_pi_ne_one` / 引理 `exp_pi_ne_one`

English:
lemma exp_pi_ne_one
  statement: Circle.exp Real.pi != 1
  proof: by
  intro h
  have heq : (Circle.exp Real.pi : Complex) = 1 := by simp [h]
  rw [Circle.coe_exp]; rw [exp_pi_mul_I] at heq
  norm_num at heq

中文:
引理 exp_pi_ne_one
  结论: Circle.exp 实数.pi != 1
  证明: by
  intro h
  have heq : (Circle.exp Real.pi : Complex) = 1 := by simp [h]
  rw [Circle.coe_exp]; rw [exp_pi_mul_I] at heq
  norm_num at heq

Depends on / 依赖: Circle, Circle.coe_exp, Circle.exp, Real.pi, coe_exp, exp_pi_mul_I
-/
lemma exp_pi_ne_one : Circle.exp Real.pi != 1 := by
  intro h
  have heq : (Circle.exp Real.pi : Complex) = 1 := by simp [h]
  rw [Circle.coe_exp]; rw [exp_pi_mul_I] at heq
  norm_num at heq

variable {e : AddChar Real Circle}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `star_addChar` / 引理 `star_addChar`

English:
lemma star_addChar
  given: (x : Real)
  statement: star ((e x) : Complex) = e (-x)
  proof: by
  have h := Circle.coe_inv_eq_conj ⟨e x, ?_⟩
  · simp [← h, e.map_neg_eq_inv]
  · simp only [Submonoid.unitSphere, SetLike.coe_mem]

@[simp]

中文:
引理 star_addChar
  条件: (x : 实数)
  结论: star ((e x) : 复形) = e (-x)
  证明: by
  have h := Circle.coe_inv_eq_conj ⟨e x, ?_⟩
  · simp [← h, e.map_neg_eq_inv]
  · simp only [Submonoid.unitSphere, SetLike.coe_mem]

@[simp]

Depends on / 依赖: Circle, Circle.coe_inv_eq_conj, SetLike, SetLike.coe_mem, Submonoid, Submonoid.unitSphere, coe_inv_eq_conj, coe_mem, e.map_neg_eq_inv, map_neg_eq_inv, unitSphere
-/
lemma star_addChar (x : Real) : star ((e x) : Complex) = e (-x) := by
  have h := Circle.coe_inv_eq_conj ⟨e x, ?_⟩
  · simp [← h, e.map_neg_eq_inv]
  · simp only [Submonoid.unitSphere, SetLike.coe_mem]

@[simp]
/--
lemma `starRingEnd_addChar` / 引理 `starRingEnd_addChar`

English:
lemma starRingEnd_addChar
  given: (x : Real)
  statement: starRingEnd Complex (e x) = e (-x)
  proof: star_addChar x

中文:
引理 starRingEnd_addChar
  条件: (x : 实数)
  结论: starRingEnd 复形 (e x) = e (-x)
  证明: star_addChar x

Depends on / 依赖: star_addChar
-/
lemma starRingEnd_addChar (x : Real) : starRingEnd Complex (e x) = e (-x) := star_addChar x

variable {α β M : Type*}

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [SMul Complex α]
  body: inferInstanceAs SMul (Submonoid.unitSphere _) α

中文:
实例 instSMul
  签名: [标量乘法 复形 α]
  定义体: inferInstanceAs SMul (Submonoid.unitSphere _) α

Depends on / 依赖: Submonoid, Submonoid.unitSphere, unitSphere
-/
instance instSMul [SMul Complex α] : SMul Circle α := inferInstanceAs SMul (Submonoid.unitSphere _) α

/--
Instance `instSMulCommClass_left` / 实例 `instSMulCommClass_left`

English:
instance instSMulCommClass_left
  signature: [SMul Complex β] [SMul α β] [SMulCommClass Complex α β]
  body: inferInstanceAs SMulCommClass (Submonoid.unitSphere _) α β

中文:
实例 instSMulCommClass_left
  签名: [标量乘法 复形 β] [标量乘法 α β] [标量交换类 复形 α β]
  定义体: inferInstanceAs SMulCommClass (Submonoid.unitSphere _) α β

Depends on / 依赖: SMulCommClass, Submonoid, Submonoid.unitSphere, unitSphere
-/
instance instSMulCommClass_left [SMul Complex β] [SMul α β] [SMulCommClass Complex α β] :
    SMulCommClass Circle α β :=
inferInstanceAs SMulCommClass (Submonoid.unitSphere _) α β

/--
Instance `instSMulCommClass_right` / 实例 `instSMulCommClass_right`

English:
instance instSMulCommClass_right
  signature: [SMul Complex β] [SMul α β] [SMulCommClass α Complex β]
  body: inferInstanceAs SMulCommClass α (Submonoid.unitSphere _) β

中文:
实例 instSMulCommClass_right
  签名: [标量乘法 复形 β] [标量乘法 α β] [标量交换类 α 复形 β]
  定义体: inferInstanceAs SMulCommClass α (Submonoid.unitSphere _) β

Depends on / 依赖: SMulCommClass, Submonoid, Submonoid.unitSphere, unitSphere
-/
instance instSMulCommClass_right [SMul Complex β] [SMul α β] [SMulCommClass α Complex β] :
    SMulCommClass α Circle β :=
inferInstanceAs SMulCommClass α (Submonoid.unitSphere _) β

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul Complex α] [SMul Complex β] [SMul α β] [IsScalarTower Complex α β]
  body: inferInstanceAs IsScalarTower (Submonoid.unitSphere _) α β

中文:
实例 instIsScalarTower
  签名: [标量乘法 复形 α] [标量乘法 复形 β] [标量乘法 α β] [标量塔 复形 α β]
  定义体: inferInstanceAs IsScalarTower (Submonoid.unitSphere _) α β

Depends on / 依赖: IsScalarTower, Submonoid, Submonoid.unitSphere, unitSphere
-/
instance instIsScalarTower [SMul Complex α] [SMul Complex β] [SMul α β] [IsScalarTower Complex α β] :
    IsScalarTower Circle α β :=
inferInstanceAs IsScalarTower (Submonoid.unitSphere _) α β

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [MulAction Complex α]
  body: inferInstanceAs MulAction (Submonoid.unitSphere _) α

中文:
实例 instMulAction
  签名: [乘法作用 复形 α]
  定义体: inferInstanceAs MulAction (Submonoid.unitSphere _) α

Depends on / 依赖: MulAction, Submonoid, Submonoid.unitSphere, unitSphere
-/
instance instMulAction [MulAction Complex α] : MulAction Circle α :=
inferInstanceAs MulAction (Submonoid.unitSphere _) α

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [AddMonoid M] [DistribMulAction Complex M]
  body: inferInstanceAs DistribMulAction (Submonoid.unitSphere _) M

中文:
实例 instDistribMulAction
  签名: [加法幺半群 M] [分配乘法作用 复形 M]
  定义体: inferInstanceAs DistribMulAction (Submonoid.unitSphere _) M

Depends on / 依赖: DistribMulAction, Submonoid, Submonoid.unitSphere, unitSphere
-/
instance instDistribMulAction [AddMonoid M] [DistribMulAction Complex M] :
    DistribMulAction Circle M :=
inferInstanceAs DistribMulAction (Submonoid.unitSphere _) M

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: [SMul Complex α] (z : Circle) (a : α)
  statement: z • a = (z : Complex) • a
  proof: rfl

中文:
引理 smul_def
  条件: [标量乘法 复形 α] (z : Circle) (a : α)
  结论: z • a = (z : 复形) • a
  证明: rfl
-/
lemma smul_def [SMul Complex α] (z : Circle) (a : α) : z • a = (z : Complex) • a := rfl

/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: [TopologicalSpace α] [MulAction Complex α] [ContinuousSMul Complex α]
  body: inferInstanceAs ContinuousSMul (Submonoid.unitSphere _) α

中文:
实例 instContinuousSMul
  签名: [拓扑空间 α] [乘法作用 复形 α] [连续标量乘法 复形 α]
  定义体: inferInstanceAs ContinuousSMul (Submonoid.unitSphere _) α

Depends on / 依赖: ContinuousSMul, Submonoid, Submonoid.unitSphere, unitSphere
-/
instance instContinuousSMul [TopologicalSpace α] [MulAction Complex α] [ContinuousSMul Complex α] :
    ContinuousSMul Circle α :=
inferInstanceAs ContinuousSMul (Submonoid.unitSphere _) α

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `norm_smul` / 引理 `norm_smul`

English:
lemma norm_smul
  statement: {E : Type*} [SeminormedAddCommGroup E] [NormedSpace Complex E]
  proof: by
  rw [smul_def]; rw [norm_smul]; rw [norm_eq_of_mem_sphere]; rw [one_mul]

中文:
引理 norm_smul
  结论: {E : 类型} [SeminormedAddComm群 E] [赋范空间 复形 E]
  证明: by
  rw [smul_def]; rw [norm_smul]; rw [norm_eq_of_mem_sphere]; rw [one_mul]
-/
protected lemma norm_smul {E : Type*} [SeminormedAddCommGroup E] [NormedSpace Complex E]
    (u : Circle) (v : E) :
    ‖u • v‖ = ‖v‖ := by
  rw [smul_def]; rw [norm_smul]; rw [norm_eq_of_mem_sphere]; rw [one_mul]

end Circle

namespace Real

/--
Definition of `fourierChar` / `fourierChar` 的定义

English:
definition fourierChar
  signature: : AddChar Real Circle where
  body: .exp (2 * π * z)
  map_zero_eq_one' := by rw [mul_zero, Circle.exp_zero]
  map_add_eq_mul' x y := by rw [mul_add, Circle.exp_add]

@[inherit_doc] scoped[FourierTransform] notation "𝐞" => Real.fourierChar

中文:
定义 fourierChar
  签名: : 加法特征 实数 Circle where
  定义体: .exp (2 * π * z)
  map_zero_eq_one' := by rw [mul_zero, Circle.exp_zero]
  map_add_eq_mul' x y := by rw [mul_add, Circle.exp_add]

@[inherit_doc] scoped[FourierTransform] notation "𝐞" => Real.fourierChar
-/
def fourierChar : AddChar Real Circle where
  toFun z := .exp (2 * π * z)
  map_zero_eq_one' := by rw [mul_zero, Circle.exp_zero]
  map_add_eq_mul' x y := by rw [mul_add, Circle.exp_add]

@[inherit_doc] scoped[FourierTransform] notation "𝐞" => Real.fourierChar

open FourierTransform

/--
theorem `fourierChar_apply'` / 定理 `fourierChar_apply'`

English:
theorem fourierChar_apply'
  given: (x : Real)
  statement: 𝐞 x = Circle.exp (2 * π * x)
  proof: rfl

中文:
定理 fourierChar_apply'
  条件: (x : 实数)
  结论: 𝐞 x = Circle.exp (2 * π * x)
  证明: rfl
-/
theorem fourierChar_apply' (x : Real) : 𝐞 x = Circle.exp (2 * π * x) := rfl

/--
theorem `fourierChar_apply` / 定理 `fourierChar_apply`

English:
theorem fourierChar_apply
  given: (x : Real)
  statement: 𝐞 x = Complex.exp (↑(2 * π * x) * Complex.I)
  proof: rfl

@[continuity, fun_prop]

中文:
定理 fourierChar_apply
  条件: (x : 实数)
  结论: 𝐞 x = 复形.exp (↑(2 * π * x) * 复形.I)
  证明: rfl

@[continuity, fun_prop]
-/
theorem fourierChar_apply (x : Real) : 𝐞 x = Complex.exp (↑(2 * π * x) * Complex.I) := rfl

@[continuity, fun_prop]
/--
theorem `continuous_fourierChar` / 定理 `continuous_fourierChar`

English:
theorem continuous_fourierChar
  statement: Continuous 𝐞
  proof: Circle.exp.continuous.comp (continuous_const_mul _)

中文:
定理 continuous_fourierChar
  结论: 连续 𝐞
  证明: Circle.exp.continuous.comp (continuous_const_mul _)

Depends on / 依赖: Circle, Circle.exp.continuous.comp, continuous, continuous_const_mul
-/
theorem continuous_fourierChar : Continuous 𝐞 := Circle.exp.continuous.comp (continuous_const_mul _)

/--
theorem `fourierChar_ne_one` / 定理 `fourierChar_ne_one`

English:
theorem fourierChar_ne_one
  statement: fourierChar != 1
  proof: by
  rw [DFunLike.ne_iff]
  use 2⁻¹
  simp only [fourierChar_apply', AddChar.one_apply]
  rw [mul_comm]; rw [← mul_assoc]; rw [inv_mul_cancel₀ (by positivity)]; rw [one_mul]
  exact Circle.exp_pi_ne_one

中文:
定理 fourierChar_ne_one
  结论: fourierChar != 1
  证明: by
  rw [DFunLike.ne_iff]
  use 2⁻¹
  simp only [fourierChar_apply', AddChar.one_apply]
  rw [mul_comm]; rw [← mul_assoc]; rw [inv_mul_cancel₀ (by positivity)]; rw [one_mul]
  exact Circle.exp_pi_ne_one

Depends on / 依赖: AddChar, AddChar.one_apply, Circle, Circle.exp_pi_ne_one, DFunLike, DFunLike.ne_iff, exp_pi_ne_one, fourierChar_apply, mul_assoc, mul_comm, ne_iff, one_apply, one_mul
-/
theorem fourierChar_ne_one : fourierChar != 1 := by
  rw [DFunLike.ne_iff]
  use 2⁻¹
  simp only [fourierChar_apply', AddChar.one_apply]
  rw [mul_comm]; rw [← mul_assoc]; rw [inv_mul_cancel₀ (by positivity)]; rw [one_mul]
  exact Circle.exp_pi_ne_one

/--
Definition of `probChar` / `probChar` 的定义

English:
definition probChar
  signature: : AddChar Real Circle where
  body: Circle.exp
  map_zero_eq_one' := Circle.exp_zero
  map_add_eq_mul' := Circle.exp_add

中文:
定义 probChar
  签名: : 加法特征 实数 Circle where
  定义体: Circle.exp
  map_zero_eq_one' := Circle.exp_zero
  map_add_eq_mul' := Circle.exp_add

Depends on / 依赖: Circle, Circle.exp
-/
def probChar : AddChar Real Circle where
  toFun := Circle.exp
  map_zero_eq_one' := Circle.exp_zero
  map_add_eq_mul' := Circle.exp_add

/--
theorem `probChar_apply'` / 定理 `probChar_apply'`

English:
theorem probChar_apply'
  given: (x : Real)
  statement: probChar x = Circle.exp x
  proof: rfl

中文:
定理 probChar_apply'
  条件: (x : 实数)
  结论: probChar x = Circle.exp x
  证明: rfl
-/
theorem probChar_apply' (x : Real) : probChar x = Circle.exp x := rfl

/--
theorem `probChar_apply` / 定理 `probChar_apply`

English:
theorem probChar_apply
  given: (x : Real)
  statement: probChar x = Complex.exp (x * Complex.I)
  proof: rfl

@[continuity, fun_prop]

中文:
定理 probChar_apply
  条件: (x : 实数)
  结论: probChar x = 复形.exp (x * 复形.I)
  证明: rfl

@[continuity, fun_prop]
-/
theorem probChar_apply (x : Real) : probChar x = Complex.exp (x * Complex.I) := rfl

@[continuity, fun_prop]
/--
theorem `continuous_probChar` / 定理 `continuous_probChar`

English:
theorem continuous_probChar
  statement: Continuous probChar
  proof: map_continuous Circle.exp

中文:
定理 continuous_probChar
  结论: 连续 probChar
  证明: map_continuous Circle.exp

Depends on / 依赖: Circle, Circle.exp, map_continuous
-/
theorem continuous_probChar : Continuous probChar := map_continuous Circle.exp

/--
theorem `probChar_ne_one` / 定理 `probChar_ne_one`

English:
theorem probChar_ne_one
  statement: probChar != 1
  proof: by
  rw [DFunLike.ne_iff]
  use Real.pi
  simpa only [probChar_apply'] using! Circle.exp_pi_ne_one

中文:
定理 probChar_ne_one
  结论: probChar != 1
  证明: by
  rw [DFunLike.ne_iff]
  use Real.pi
  simpa only [probChar_apply'] using! Circle.exp_pi_ne_one

Depends on / 依赖: Circle, Circle.exp_pi_ne_one, DFunLike, DFunLike.ne_iff, Real.pi, exp_pi_ne_one, ne_iff, probChar_apply
-/
theorem probChar_ne_one : probChar != 1 := by
  rw [DFunLike.ne_iff]
  use Real.pi
  simpa only [probChar_apply'] using! Circle.exp_pi_ne_one

end Real
