/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Algebra.CharZero.Quotient
public import Mathlib.Topology.Instances.Sign
import Mathlib.Algebra.Order.Ring.Interval

/-!
# The type of angles

In this file we define `Real.Angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/

@[expose] public section


open Real

noncomputable section

namespace Real

/--
Definition of `Angle` / `Angle` 的定义

English:
definition Angle
  signature: : Type
  body: AddCircle (2 * π)
deriving NormedAddCommGroup, Inhabited

中文:
定义 Angle
  签名: : 类型
  定义体: AddCircle (2 * π)
deriving NormedAddCommGroup, Inhabited

Depends on / 依赖: AddCircle
-/
def Angle : Type :=
  AddCircle (2 * π)
deriving NormedAddCommGroup, Inhabited

namespace Angle

/-- The canonical map from `ℝ` to the quotient `Angle`. -/
@[coe]
/--
Definition of `coe` / `coe` 的定义

English:
definition coe
  signature: (r : Real)
  body: QuotientAddGroup.mk r

中文:
定义 coe
  签名: (r : 实数)
  定义体: QuotientAddGroup.mk r
-/
protected def coe (r : Real) : Angle := QuotientAddGroup.mk r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Real Angle
  body: ⟨Angle.coe⟩

中文:
实例 :
  签名: Coe 实数 Angle
  定义体: ⟨Angle.coe⟩

Depends on / 依赖: Angle.coe
-/
instance : Coe Real Angle := ⟨Angle.coe⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CircularOrder Real.Angle
  body: fast_instance% QuotientAddGroup.circularOrder (hp' := ⟨by simp [pi_pos]⟩)

@[continuity, fun_prop]

中文:
实例 :
  签名: Circular序 实数.Angle
  定义体: fast_instance% QuotientAddGroup.circularOrder (hp' := ⟨by simp [pi_pos]⟩)

@[continuity, fun_prop]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.circularOrder, circularOrder, fast_instance, pi_pos
-/
instance : CircularOrder Real.Angle :=
  fast_instance% QuotientAddGroup.circularOrder (hp' := ⟨by simp [pi_pos]⟩)

@[continuity, fun_prop]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : Real -> Angle)
  proof: continuous_quotient_mk'

中文:
定理 continuous_coe
  结论: 连续 ((↑) : 实数 -> Angle)
  证明: continuous_quotient_mk'

Depends on / 依赖: continuous_quotient_mk
-/
theorem continuous_coe : Continuous ((↑) : Real -> Angle) :=
  continuous_quotient_mk'

/--
Definition of `coeHom` / `coeHom` 的定义

English:
definition coeHom
  signature: : Real ->+ Angle
  body: QuotientAddGroup.mk' _

@[simp]

中文:
定义 coeHom
  签名: : 实数 ->+ Angle
  定义体: QuotientAddGroup.mk' _

@[simp]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.mk
-/
def coeHom : Real ->+ Angle :=
  QuotientAddGroup.mk' _

@[simp]
/--
theorem `coe_coeHom` / 定理 `coe_coeHom`

English:
theorem coe_coeHom
  statement: (coeHom : Real -> Angle) = ((↑) : Real -> Angle)
  proof: rfl

中文:
定理 coe_coeHom
  结论: (coeHom : 实数 -> Angle) = ((↑) : 实数 -> Angle)
  证明: rfl
-/
theorem coe_coeHom : (coeHom : Real -> Angle) = ((↑) : Real -> Angle) :=
  rfl

/-- An induction principle to deduce results for `Angle` from those for `ℝ`, used with
`induction θ using Real.Angle.induction_on`. -/
@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: {p : Angle -> Prop} (θ : Angle) (h : forall x : Real, p x)
  statement: p θ
  proof: Quotient.inductionOn' θ h

@[simp]

中文:
定理 induction_on
  条件: {p : Angle -> 命题} (θ : Angle) (h : 对任意 x : 实数, p x)
  结论: p θ
  证明: Quotient.inductionOn' θ h

@[simp]
-/
protected theorem induction_on {p : Angle -> Prop} (θ : Angle) (h : forall x : Real, p x) : p θ :=
  Quotient.inductionOn' θ h

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ↑(0 : Real) = (0 : Angle)
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ↑(0 : 实数) = (0 : Angle)
  证明: rfl

@[simp]
-/
theorem coe_zero : ↑(0 : Real) = (0 : Angle) :=
  rfl

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : Real)
  statement: ↑(x + y : Real) = (↑x + ↑y : Angle)
  proof: rfl

@[simp]

中文:
定理 coe_add
  条件: (x y : 实数)
  结论: ↑(x + y : 实数) = (↑x + ↑y : Angle)
  证明: rfl

@[simp]
-/
theorem coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : Angle) :=
  rfl

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (x : Real)
  statement: ↑(-x : Real) = -(↑x : Angle)
  proof: rfl

@[simp]

中文:
定理 coe_neg
  条件: (x : 实数)
  结论: ↑(-x : 实数) = -(↑x : Angle)
  证明: rfl

@[simp]
-/
theorem coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle) :=
  rfl

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (x y : Real)
  statement: ↑(x - y : Real) = (↑x - ↑y : Angle)
  proof: rfl

中文:
定理 coe_sub
  条件: (x y : 实数)
  结论: ↑(x - y : 实数) = (↑x - ↑y : Angle)
  证明: rfl
-/
theorem coe_sub (x y : Real) : ↑(x - y : Real) = (↑x - ↑y : Angle) :=
  rfl

/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  given: (n : Nat) (x : Real)
  statement: ↑(n • x : Real) = n • (↑x : Angle)
  proof: rfl

中文:
定理 coe_nsmul
  条件: (n : 自然数) (x : 实数)
  结论: ↑(n • x : 实数) = n • (↑x : Angle)
  证明: rfl
-/
theorem coe_nsmul (n : Nat) (x : Real) : ↑(n • x : Real) = n • (↑x : Angle) :=
  rfl

/--
theorem `coe_zsmul` / 定理 `coe_zsmul`

English:
theorem coe_zsmul
  given: (z : Int) (x : Real)
  statement: ↑(z • x : Real) = z • (↑x : Angle)
  proof: rfl

中文:
定理 coe_zsmul
  条件: (z : 整数) (x : 实数)
  结论: ↑(z • x : 实数) = z • (↑x : Angle)
  证明: rfl
-/
theorem coe_zsmul (z : Int) (x : Real) : ↑(z • x : Real) = z • (↑x : Angle) :=
  rfl

/--
theorem `coe_eq_zero_iff` / 定理 `coe_eq_zero_iff`

English:
theorem coe_eq_zero_iff
  given: {x : Real}
  statement: (x : Angle) = 0 ↔ exists n : Int, n • (2 * π) = x
  proof: AddCircle.coe_eq_zero_iff (2 * π)

@[simp, norm_cast]

中文:
定理 coe_eq_zero_iff
  条件: {x : 实数}
  结论: (x : Angle) = 0 ↔ 存在 n : 整数, n • (2 * π) = x
  证明: AddCircle.coe_eq_zero_iff (2 * π)

@[simp, norm_cast]

Depends on / 依赖: AddCircle, AddCircle.coe_eq_zero_iff, coe_eq_zero_iff
-/
theorem coe_eq_zero_iff {x : Real} : (x : Angle) = 0 ↔ exists n : Int, n • (2 * π) = x :=
  AddCircle.coe_eq_zero_iff (2 * π)

@[simp, norm_cast]
/--
theorem `natCast_mul_eq_nsmul` / 定理 `natCast_mul_eq_nsmul`

English:
theorem natCast_mul_eq_nsmul
  given: (x : Real) (n : Nat)
  statement: ↑((n : Real) * x) = n • (↑x : Angle)
  proof: by
  simpa only [nsmul_eq_mul] using! coeHom.map_nsmul n x

@[simp, norm_cast]

中文:
定理 natCast_mul_eq_nsmul
  条件: (x : 实数) (n : 自然数)
  结论: ↑((n : 实数) * x) = n • (↑x : Angle)
  证明: by
  simpa only [nsmul_eq_mul] using! coeHom.map_nsmul n x

@[simp, norm_cast]

Depends on / 依赖: coeHom, coeHom.map_nsmul, map_nsmul, nsmul_eq_mul
-/
theorem natCast_mul_eq_nsmul (x : Real) (n : Nat) : ↑((n : Real) * x) = n • (↑x : Angle) := by
  simpa only [nsmul_eq_mul] using! coeHom.map_nsmul n x

@[simp, norm_cast]
/--
theorem `intCast_mul_eq_zsmul` / 定理 `intCast_mul_eq_zsmul`

English:
theorem intCast_mul_eq_zsmul
  given: (x : Real) (n : Int)
  statement: ↑((n : Real) * x : Real) = n • (↑x : Angle)
  proof: by
  simpa only [zsmul_eq_mul] using! coeHom.map_zsmul n x

中文:
定理 intCast_mul_eq_zsmul
  条件: (x : 实数) (n : 整数)
  结论: ↑((n : 实数) * x : 实数) = n • (↑x : Angle)
  证明: by
  simpa only [zsmul_eq_mul] using! coeHom.map_zsmul n x

Depends on / 依赖: coeHom, coeHom.map_zsmul, map_zsmul, zsmul_eq_mul
-/
theorem intCast_mul_eq_zsmul (x : Real) (n : Int) : ↑((n : Real) * x : Real) = n • (↑x : Angle) := by
  simpa only [zsmul_eq_mul] using! coeHom.map_zsmul n x

set_option backward.isDefEq.respectTransparency false in
/--
theorem `angle_eq_iff_two_pi_dvd_sub` / 定理 `angle_eq_iff_two_pi_dvd_sub`

English:
theorem angle_eq_iff_two_pi_dvd_sub
  given: {ψ θ : Real}
  statement: (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k
  proof: by
  simp only [eq_comm]
  rw [Angle.coe]; rw [Angle.coe]; rw [QuotientAddGroup.eq]
  simp only [AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

@[simp]

中文:
定理 angle_eq_iff_two_pi_dvd_sub
  条件: {ψ θ : 实数}
  结论: (θ : Angle) = ψ ↔ 存在 k : 整数, θ - ψ = 2 * π * k
  证明: by
  simp only [eq_comm]
  rw [Angle.coe]; rw [Angle.coe]; rw [QuotientAddGroup.eq]
  simp only [AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

@[simp]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_closure_singleton, AddSubgroup.zmultiples_eq_closure, Angle.coe, QuotientAddGroup, QuotientAddGroup.eq, eq_comm, mem_closure_singleton, sub_eq_neg_add, zmultiples_eq_closure, zsmul_eq_mul
-/
theorem angle_eq_iff_two_pi_dvd_sub {ψ θ : Real} : (θ : Angle) = ψ ↔ exists k : Int, θ - ψ = 2 * π * k := by
  simp only [eq_comm]
  rw [Angle.coe]; rw [Angle.coe]; rw [QuotientAddGroup.eq]
  simp only [AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

@[simp]
/--
theorem `coe_two_pi` / 定理 `coe_two_pi`

English:
theorem coe_two_pi
  statement: ↑(2 * π : Real) = (0 : Angle)
  proof: angle_eq_iff_two_pi_dvd_sub.2 ⟨1, by rw [sub_zero, Int.cast_one, mul_one]⟩

@[simp]

中文:
定理 coe_two_pi
  结论: ↑(2 * π : 实数) = (0 : Angle)
  证明: angle_eq_iff_two_pi_dvd_sub.2 ⟨1, by rw [sub_zero, Int.cast_one, mul_one]⟩

@[simp]

Depends on / 依赖: Int.cast_one, angle_eq_iff_two_pi_dvd_sub, cast_one, mul_one, sub_zero
-/
theorem coe_two_pi : ↑(2 * π : Real) = (0 : Angle) :=
  angle_eq_iff_two_pi_dvd_sub.2 ⟨1, by rw [sub_zero, Int.cast_one, mul_one]⟩

@[simp]
/--
theorem `neg_coe_pi` / 定理 `neg_coe_pi`

English:
theorem neg_coe_pi
  statement: -(π : Angle) = π
  proof: by
  rw [← coe_neg]; rw [angle_eq_iff_two_pi_dvd_sub]
  use -1
  simp [two_mul, sub_eq_add_neg]

@[simp]

中文:
定理 neg_coe_pi
  结论: -(π : Angle) = π
  证明: by
  rw [← coe_neg]; rw [angle_eq_iff_two_pi_dvd_sub]
  use -1
  simp [two_mul, sub_eq_add_neg]

@[simp]

Depends on / 依赖: angle_eq_iff_two_pi_dvd_sub, coe_neg, sub_eq_add_neg, two_mul
-/
theorem neg_coe_pi : -(π : Angle) = π := by
  rw [← coe_neg]; rw [angle_eq_iff_two_pi_dvd_sub]
  use -1
  simp [two_mul, sub_eq_add_neg]

@[simp]
/--
theorem `two_nsmul_coe_div_two` / 定理 `two_nsmul_coe_div_two`

English:
theorem two_nsmul_coe_div_two
  given: (θ : Real)
  statement: (2 : Nat) • (↑(θ / 2) : Angle) = θ
  proof: by
  rw [← coe_nsmul]; rw [two_nsmul]; rw [add_halves]

@[simp]

中文:
定理 two_nsmul_coe_div_two
  条件: (θ : 实数)
  结论: (2 : 自然数) • (↑(θ / 2) : Angle) = θ
  证明: by
  rw [← coe_nsmul]; rw [two_nsmul]; rw [add_halves]

@[simp]

Depends on / 依赖: add_halves, coe_nsmul, two_nsmul
-/
theorem two_nsmul_coe_div_two (θ : Real) : (2 : Nat) • (↑(θ / 2) : Angle) = θ := by
  rw [← coe_nsmul]; rw [two_nsmul]; rw [add_halves]

@[simp]
/--
theorem `two_zsmul_coe_div_two` / 定理 `two_zsmul_coe_div_two`

English:
theorem two_zsmul_coe_div_two
  given: (θ : Real)
  statement: (2 : Int) • (↑(θ / 2) : Angle) = θ
  proof: by
  rw [← coe_zsmul]; rw [two_zsmul]; rw [add_halves]

中文:
定理 two_zsmul_coe_div_two
  条件: (θ : 实数)
  结论: (2 : 整数) • (↑(θ / 2) : Angle) = θ
  证明: by
  rw [← coe_zsmul]; rw [two_zsmul]; rw [add_halves]

Depends on / 依赖: add_halves, coe_zsmul, two_zsmul
-/
theorem two_zsmul_coe_div_two (θ : Real) : (2 : Int) • (↑(θ / 2) : Angle) = θ := by
  rw [← coe_zsmul]; rw [two_zsmul]; rw [add_halves]

/--
theorem `two_nsmul_neg_pi_div_two` / 定理 `two_nsmul_neg_pi_div_two`

English:
theorem two_nsmul_neg_pi_div_two
  statement: (2 : Nat) • (↑(-π / 2) : Angle) = π
  proof: by
  rw [two_nsmul_coe_div_two]; rw [coe_neg]; rw [neg_coe_pi]

中文:
定理 two_nsmul_neg_pi_div_two
  结论: (2 : 自然数) • (↑(-π / 2) : Angle) = π
  证明: by
  rw [two_nsmul_coe_div_two]; rw [coe_neg]; rw [neg_coe_pi]

Depends on / 依赖: coe_neg, neg_coe_pi, two_nsmul_coe_div_two
-/
theorem two_nsmul_neg_pi_div_two : (2 : Nat) • (↑(-π / 2) : Angle) = π := by
  rw [two_nsmul_coe_div_two]; rw [coe_neg]; rw [neg_coe_pi]

/--
theorem `two_zsmul_neg_pi_div_two` / 定理 `two_zsmul_neg_pi_div_two`

English:
theorem two_zsmul_neg_pi_div_two
  statement: (2 : Int) • (↑(-π / 2) : Angle) = π
  proof: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_neg_pi_div_two]

中文:
定理 two_zsmul_neg_pi_div_two
  结论: (2 : 整数) • (↑(-π / 2) : Angle) = π
  证明: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_neg_pi_div_two]

Depends on / 依赖: two_nsmul, two_nsmul_neg_pi_div_two, two_zsmul
-/
theorem two_zsmul_neg_pi_div_two : (2 : Int) • (↑(-π / 2) : Angle) = π := by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_neg_pi_div_two]

/--
theorem `sub_coe_pi_eq_add_coe_pi` / 定理 `sub_coe_pi_eq_add_coe_pi`

English:
theorem sub_coe_pi_eq_add_coe_pi
  given: (θ : Angle)
  statement: θ - π = θ + π
  proof: by
  rw [sub_eq_add_neg]; rw [neg_coe_pi]

@[simp]

中文:
定理 sub_coe_pi_eq_add_coe_pi
  条件: (θ : Angle)
  结论: θ - π = θ + π
  证明: by
  rw [sub_eq_add_neg]; rw [neg_coe_pi]

@[simp]

Depends on / 依赖: neg_coe_pi, sub_eq_add_neg
-/
theorem sub_coe_pi_eq_add_coe_pi (θ : Angle) : θ - π = θ + π := by
  rw [sub_eq_add_neg]; rw [neg_coe_pi]

@[simp]
/--
theorem `two_nsmul_coe_pi` / 定理 `two_nsmul_coe_pi`

English:
theorem two_nsmul_coe_pi
  statement: (2 : Nat) • (π : Angle) = 0
  proof: by simp [← natCast_mul_eq_nsmul]

@[simp]

中文:
定理 two_nsmul_coe_pi
  结论: (2 : 自然数) • (π : Angle) = 0
  证明: by simp [← natCast_mul_eq_nsmul]

@[simp]

Depends on / 依赖: natCast_mul_eq_nsmul
-/
theorem two_nsmul_coe_pi : (2 : Nat) • (π : Angle) = 0 := by simp [← natCast_mul_eq_nsmul]

@[simp]
/--
theorem `two_zsmul_coe_pi` / 定理 `two_zsmul_coe_pi`

English:
theorem two_zsmul_coe_pi
  statement: (2 : Int) • (π : Angle) = 0
  proof: by simp [← intCast_mul_eq_zsmul]

@[simp, grind =]

中文:
定理 two_zsmul_coe_pi
  结论: (2 : 整数) • (π : Angle) = 0
  证明: by simp [← intCast_mul_eq_zsmul]

@[simp, grind =]

Depends on / 依赖: intCast_mul_eq_zsmul
-/
theorem two_zsmul_coe_pi : (2 : Int) • (π : Angle) = 0 := by simp [← intCast_mul_eq_zsmul]

@[simp, grind =]
/--
theorem `coe_pi_add_coe_pi` / 定理 `coe_pi_add_coe_pi`

English:
theorem coe_pi_add_coe_pi
  statement: (π : Real.Angle) + π = 0
  proof: by rw [← two_nsmul, two_nsmul_coe_pi]

中文:
定理 coe_pi_add_coe_pi
  结论: (π : 实数.Angle) + π = 0
  证明: by rw [← two_nsmul, two_nsmul_coe_pi]

Depends on / 依赖: two_nsmul, two_nsmul_coe_pi
-/
theorem coe_pi_add_coe_pi : (π : Real.Angle) + π = 0 := by rw [← two_nsmul, two_nsmul_coe_pi]

/--
theorem `zsmul_eq_iff` / 定理 `zsmul_eq_iff`

English:
theorem zsmul_eq_iff
  given: {ψ θ : Angle} {z : Int} (hz : z != 0)
  proof: QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff hz

中文:
定理 zsmul_eq_iff
  条件: {ψ θ : Angle} {z : 整数} (hz : z != 0)
  证明: QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff hz

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff, zmultiples_zsmul_eq_zsmul_iff
-/
theorem zsmul_eq_iff {ψ θ : Angle} {z : Int} (hz : z != 0) :
    z • ψ = z • θ ↔ exists k : Fin z.natAbs, ψ = θ + (k : Nat) • (2 * π / z : Real) :=
  QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff hz

/--
theorem `nsmul_eq_iff` / 定理 `nsmul_eq_iff`

English:
theorem nsmul_eq_iff
  given: {ψ θ : Angle} {n : Nat} (hz : n != 0)
  proof: QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff hz

中文:
定理 nsmul_eq_iff
  条件: {ψ θ : Angle} {n : 自然数} (hz : n != 0)
  证明: QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff hz

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff, zmultiples_nsmul_eq_nsmul_iff
-/
theorem nsmul_eq_iff {ψ θ : Angle} {n : Nat} (hz : n != 0) :
    n • ψ = n • θ ↔ exists k : Fin n, ψ = θ + (k : Nat) • (2 * π / n : Real) :=
  QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff hz

/--
theorem `two_zsmul_eq_iff` / 定理 `two_zsmul_eq_iff`

English:
theorem two_zsmul_eq_iff
  given: {ψ θ : Angle}
  statement: (2 : Int) • ψ = (2 : Int) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
  proof: by
  have : Int.natAbs 2 = 2 := rfl
  rw [zsmul_eq_iff two_ne_zero]; rw [this]; rw [Fin.exists_fin_two]; rw [Fin.val_zero]; rw [Fin.val_one]; rw [zero_smul]; rw [add_zero]; rw [one_smul]; rw [Int.cast_two]; rw [mul_div_cancel_left₀ (_ : Real) two_ne_zero]

中文:
定理 two_zsmul_eq_iff
  条件: {ψ θ : Angle}
  结论: (2 : 整数) • ψ = (2 : 整数) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
  证明: by
  have : Int.natAbs 2 = 2 := rfl
  rw [zsmul_eq_iff two_ne_zero]; rw [this]; rw [Fin.exists_fin_two]; rw [Fin.val_zero]; rw [Fin.val_one]; rw [zero_smul]; rw [add_zero]; rw [one_smul]; rw [Int.cast_two]; rw [mul_div_cancel_left₀ (_ : Real) two_ne_zero]

Depends on / 依赖: Fin.exists_fin_two, Fin.val_one, Fin.val_zero, Int.cast_two, Int.natAbs, add_zero, cast_two, exists_fin_two, natAbs, one_smul, two_ne_zero, val_one, val_zero, zero_smul, zsmul_eq_iff
-/
theorem two_zsmul_eq_iff {ψ θ : Angle} : (2 : Int) • ψ = (2 : Int) • θ ↔ ψ = θ ∨ ψ = θ + ↑π := by
  have : Int.natAbs 2 = 2 := rfl
  rw [zsmul_eq_iff two_ne_zero]; rw [this]; rw [Fin.exists_fin_two]; rw [Fin.val_zero]; rw [Fin.val_one]; rw [zero_smul]; rw [add_zero]; rw [one_smul]; rw [Int.cast_two]; rw [mul_div_cancel_left₀ (_ : Real) two_ne_zero]

/--
theorem `two_nsmul_eq_iff` / 定理 `two_nsmul_eq_iff`

English:
theorem two_nsmul_eq_iff
  given: {ψ θ : Angle}
  statement: (2 : Nat) • ψ = (2 : Nat) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
  proof: by
  simp_rw [← natCast_zsmul, Nat.cast_ofNat, two_zsmul_eq_iff]

中文:
定理 two_nsmul_eq_iff
  条件: {ψ θ : Angle}
  结论: (2 : 自然数) • ψ = (2 : 自然数) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
  证明: by
  simp_rw [← natCast_zsmul, Nat.cast_ofNat, two_zsmul_eq_iff]

Depends on / 依赖: Nat.cast_ofNat, cast_ofNat, natCast_zsmul, simp_rw, two_zsmul_eq_iff
-/
theorem two_nsmul_eq_iff {ψ θ : Angle} : (2 : Nat) • ψ = (2 : Nat) • θ ↔ ψ = θ ∨ ψ = θ + ↑π := by
  simp_rw [← natCast_zsmul, Nat.cast_ofNat, two_zsmul_eq_iff]

/--
theorem `two_nsmul_eq_zero_iff` / 定理 `two_nsmul_eq_zero_iff`

English:
theorem two_nsmul_eq_zero_iff
  given: {θ : Angle}
  statement: (2 : Nat) • θ = 0 ↔ θ = 0 ∨ θ = π
  proof: by
  convert! two_nsmul_eq_iff <;> simp

中文:
定理 two_nsmul_eq_zero_iff
  条件: {θ : Angle}
  结论: (2 : 自然数) • θ = 0 ↔ θ = 0 ∨ θ = π
  证明: by
  convert! two_nsmul_eq_iff <;> simp

Depends on / 依赖: convert, two_nsmul_eq_iff
-/
theorem two_nsmul_eq_zero_iff {θ : Angle} : (2 : Nat) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  convert! two_nsmul_eq_iff <;> simp

/--
theorem `two_nsmul_ne_zero_iff` / 定理 `two_nsmul_ne_zero_iff`

English:
theorem two_nsmul_ne_zero_iff
  given: {θ : Angle}
  statement: (2 : Nat) • θ != 0 ↔ θ != 0 ∧ θ != π
  proof: by
  rw [← not_or]; rw [← two_nsmul_eq_zero_iff]

中文:
定理 two_nsmul_ne_zero_iff
  条件: {θ : Angle}
  结论: (2 : 自然数) • θ != 0 ↔ θ != 0 ∧ θ != π
  证明: by
  rw [← not_or]; rw [← two_nsmul_eq_zero_iff]

Depends on / 依赖: not_or, two_nsmul_eq_zero_iff
-/
theorem two_nsmul_ne_zero_iff {θ : Angle} : (2 : Nat) • θ != 0 ↔ θ != 0 ∧ θ != π := by
  rw [← not_or]; rw [← two_nsmul_eq_zero_iff]

/--
theorem `two_zsmul_eq_zero_iff` / 定理 `two_zsmul_eq_zero_iff`

English:
theorem two_zsmul_eq_zero_iff
  given: {θ : Angle}
  statement: (2 : Int) • θ = 0 ↔ θ = 0 ∨ θ = π
  proof: by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_zero_iff]

中文:
定理 two_zsmul_eq_zero_iff
  条件: {θ : Angle}
  结论: (2 : 整数) • θ = 0 ↔ θ = 0 ∨ θ = π
  证明: by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_zero_iff]

Depends on / 依赖: simp_rw, two_nsmul, two_nsmul_eq_zero_iff, two_zsmul
-/
theorem two_zsmul_eq_zero_iff {θ : Angle} : (2 : Int) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_zero_iff]

/--
theorem `two_zsmul_ne_zero_iff` / 定理 `two_zsmul_ne_zero_iff`

English:
theorem two_zsmul_ne_zero_iff
  given: {θ : Angle}
  statement: (2 : Int) • θ != 0 ↔ θ != 0 ∧ θ != π
  proof: by
  rw [← not_or]; rw [← two_zsmul_eq_zero_iff]

中文:
定理 two_zsmul_ne_zero_iff
  条件: {θ : Angle}
  结论: (2 : 整数) • θ != 0 ↔ θ != 0 ∧ θ != π
  证明: by
  rw [← not_or]; rw [← two_zsmul_eq_zero_iff]

Depends on / 依赖: not_or, two_zsmul_eq_zero_iff
-/
theorem two_zsmul_ne_zero_iff {θ : Angle} : (2 : Int) • θ != 0 ↔ θ != 0 ∧ θ != π := by
  rw [← not_or]; rw [← two_zsmul_eq_zero_iff]

/--
theorem `eq_neg_self_iff` / 定理 `eq_neg_self_iff`

English:
theorem eq_neg_self_iff
  given: {θ : Angle}
  statement: θ = -θ ↔ θ = 0 ∨ θ = π
  proof: by
  rw [← add_eq_zero_iff_eq_neg]; rw [← two_nsmul]; rw [two_nsmul_eq_zero_iff]

中文:
定理 eq_neg_self_iff
  条件: {θ : Angle}
  结论: θ = -θ ↔ θ = 0 ∨ θ = π
  证明: by
  rw [← add_eq_zero_iff_eq_neg]; rw [← two_nsmul]; rw [two_nsmul_eq_zero_iff]

Depends on / 依赖: add_eq_zero_iff_eq_neg, two_nsmul, two_nsmul_eq_zero_iff
-/
theorem eq_neg_self_iff {θ : Angle} : θ = -θ ↔ θ = 0 ∨ θ = π := by
  rw [← add_eq_zero_iff_eq_neg]; rw [← two_nsmul]; rw [two_nsmul_eq_zero_iff]

/--
theorem `ne_neg_self_iff` / 定理 `ne_neg_self_iff`

English:
theorem ne_neg_self_iff
  given: {θ : Angle}
  statement: θ != -θ ↔ θ != 0 ∧ θ != π
  proof: by
  rw [← not_or]; rw [← eq_neg_self_iff.not]

中文:
定理 ne_neg_self_iff
  条件: {θ : Angle}
  结论: θ != -θ ↔ θ != 0 ∧ θ != π
  证明: by
  rw [← not_or]; rw [← eq_neg_self_iff.not]

Depends on / 依赖: eq_neg_self_iff, eq_neg_self_iff.not, not_or
-/
theorem ne_neg_self_iff {θ : Angle} : θ != -θ ↔ θ != 0 ∧ θ != π := by
  rw [← not_or]; rw [← eq_neg_self_iff.not]

/--
theorem `neg_eq_self_iff` / 定理 `neg_eq_self_iff`

English:
theorem neg_eq_self_iff
  given: {θ : Angle}
  statement: -θ = θ ↔ θ = 0 ∨ θ = π
  proof: by rw [eq_comm, eq_neg_self_iff]

中文:
定理 neg_eq_self_iff
  条件: {θ : Angle}
  结论: -θ = θ ↔ θ = 0 ∨ θ = π
  证明: by rw [eq_comm, eq_neg_self_iff]

Depends on / 依赖: eq_comm, eq_neg_self_iff
-/
theorem neg_eq_self_iff {θ : Angle} : -θ = θ ↔ θ = 0 ∨ θ = π := by rw [eq_comm, eq_neg_self_iff]

/--
theorem `neg_ne_self_iff` / 定理 `neg_ne_self_iff`

English:
theorem neg_ne_self_iff
  given: {θ : Angle}
  statement: -θ != θ ↔ θ != 0 ∧ θ != π
  proof: by
  rw [← not_or]; rw [← neg_eq_self_iff.not]

中文:
定理 neg_ne_self_iff
  条件: {θ : Angle}
  结论: -θ != θ ↔ θ != 0 ∧ θ != π
  证明: by
  rw [← not_or]; rw [← neg_eq_self_iff.not]

Depends on / 依赖: neg_eq_self_iff, neg_eq_self_iff.not, not_or
-/
theorem neg_ne_self_iff {θ : Angle} : -θ != θ ↔ θ != 0 ∧ θ != π := by
  rw [← not_or]; rw [← neg_eq_self_iff.not]

/--
theorem `two_nsmul_eq_pi_iff` / 定理 `two_nsmul_eq_pi_iff`

English:
theorem two_nsmul_eq_pi_iff
  given: {θ : Angle}
  statement: (2 : Nat) • θ = π ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real)
  proof: by
  have h : (π : Angle) = ((2 : Nat) • (π / 2 : Real) :) := by rw [two_nsmul, add_halves]
  nth_rw 1 [h]
  rw [coe_nsmul]; rw [two_nsmul_eq_iff]
  apply iff_of_eq -- `congr` only works on `Eq`, so rewrite from `Iff` to `Eq`.
  congr
  rw [add_comm]; rw [← coe_add]; rw [← sub_eq_zero]; rw [← coe_sub]; rw [neg_div]; rw [sub_neg_eq_add]; rw [add_assoc]; rw [add_halves]; rw [← two_mul]; rw [coe_two_pi]

中文:
定理 two_nsmul_eq_pi_iff
  条件: {θ : Angle}
  结论: (2 : 自然数) • θ = π ↔ θ = (π / 2 : 实数) ∨ θ = (-π / 2 : 实数)
  证明: by
  have h : (π : Angle) = ((2 : Nat) • (π / 2 : Real) :) := by rw [two_nsmul, add_halves]
  nth_rw 1 [h]
  rw [coe_nsmul]; rw [two_nsmul_eq_iff]
  apply iff_of_eq -- `congr` only works on `Eq`, so rewrite from `Iff` to `Eq`.
  congr
  rw [add_comm]; rw [← coe_add]; rw [← sub_eq_zero]; rw [← coe_sub]; rw [neg_div]; rw [sub_neg_eq_add]; rw [add_assoc]; rw [add_halves]; rw [← two_mul]; rw [coe_two_pi]

Depends on / 依赖: add_assoc, add_comm, add_halves, coe_add, coe_nsmul, coe_sub, coe_two_pi, iff_of_eq, neg_div, nth_rw, rewrite, sub_eq_zero, sub_neg_eq_add, two_mul, two_nsmul, two_nsmul_eq_iff
-/
theorem two_nsmul_eq_pi_iff {θ : Angle} : (2 : Nat) • θ = π ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real) := by
  have h : (π : Angle) = ((2 : Nat) • (π / 2 : Real) :) := by rw [two_nsmul, add_halves]
  nth_rw 1 [h]
  rw [coe_nsmul]; rw [two_nsmul_eq_iff]
  apply iff_of_eq -- `congr` only works on `Eq`, so rewrite from `Iff` to `Eq`.
  congr
  rw [add_comm]; rw [← coe_add]; rw [← sub_eq_zero]; rw [← coe_sub]; rw [neg_div]; rw [sub_neg_eq_add]; rw [add_assoc]; rw [add_halves]; rw [← two_mul]; rw [coe_two_pi]

/--
theorem `two_zsmul_eq_pi_iff` / 定理 `two_zsmul_eq_pi_iff`

English:
theorem two_zsmul_eq_pi_iff
  given: {θ : Angle}
  statement: (2 : Int) • θ = π ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real)
  proof: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_eq_pi_iff]

中文:
定理 two_zsmul_eq_pi_iff
  条件: {θ : Angle}
  结论: (2 : 整数) • θ = π ↔ θ = (π / 2 : 实数) ∨ θ = (-π / 2 : 实数)
  证明: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_eq_pi_iff]

Depends on / 依赖: two_nsmul, two_nsmul_eq_pi_iff, two_zsmul
-/
theorem two_zsmul_eq_pi_iff {θ : Angle} : (2 : Int) • θ = π ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real) := by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_eq_pi_iff]

/--
theorem `cos_eq_iff_coe_eq_or_eq_neg` / 定理 `cos_eq_iff_coe_eq_or_eq_neg`

English:
theorem cos_eq_iff_coe_eq_or_eq_neg
  given: {θ ψ : Real}
  proof: by
  constructor
  · intro Hcos
    rw [← sub_eq_zero]; rw [cos_sub_cos]; rw [mul_eq_zero]; rw [mul_eq_zero]; rw [neg_eq_zero]; rw [eq_false (two_ne_zero' Real)]; rw [false_or]; rw [sin_eq_zero_iff]; rw [sin_eq_zero_iff] at Hcos
    rcases Hcos with (⟨n, hn⟩ | ⟨n, hn⟩)
    · right
      rw [eq_div_iff_mul_eq (two_ne_zero' Real)]; rw [← sub_eq_iff_eq_add] at hn
      rw [← hn]; rw [coe_sub]; rw [eq_neg_iff_add_eq_zero]; rw [sub_add_cancel]; rw [mul_assoc]; rw [intCast_mul_eq_zsmul]; rw [mul_comm]; rw [coe_two_pi]; rw [zsmul_zero]
    · left
      rw [eq_div_iff_mul_eq (two_ne_zero' Real)]; rw [eq_sub_iff_add_eq] at hn
      rw [← hn]; rw [coe_add]; rw [mul_assoc]; rw [intCast_mul_eq_zsmul]; rw [mul_comm]; rw [coe_two_pi]; rw [zsmul_zero]; rw [zero_add]
  · rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' Real),
        mul_comm π _, sin_int_mul_pi, mul_zero]
    rw [← sub_eq_zero]; rw [cos_sub_cos]; rw [← sub_neg_eq_add]; rw [H]; rw [mul_assoc 2 π k]; rw [mul_div_cancel_left₀ _ (two_ne_zero' Real)]; rw [mul_comm π _]; rw [sin_int_mul_pi]; rw [mul_zero]; rw [zero_mul]

中文:
定理 cos_eq_iff_coe_eq_or_eq_neg
  条件: {θ ψ : 实数}
  证明: by
  constructor
  · intro Hcos
    rw [← sub_eq_zero]; rw [cos_sub_cos]; rw [mul_eq_zero]; rw [mul_eq_zero]; rw [neg_eq_zero]; rw [eq_false (two_ne_zero' Real)]; rw [false_or]; rw [sin_eq_zero_iff]; rw [sin_eq_zero_iff] at Hcos
    rcases Hcos with (⟨n, hn⟩ | ⟨n, hn⟩)
    · right
      rw [eq_div_iff_mul_eq (two_ne_zero' Real)]; rw [← sub_eq_iff_eq_add] at hn
      rw [← hn]; rw [coe_sub]; rw [eq_neg_iff_add_eq_zero]; rw [sub_add_cancel]; rw [mul_assoc]; rw [intCast_mul_eq_zsmul]; rw [mul_comm]; rw [coe_two_pi]; rw [zsmul_zero]
    · left
      rw [eq_div_iff_mul_eq (two_ne_zero' Real)]; rw [eq_sub_iff_add_eq] at hn
      rw [← hn]; rw [coe_add]; rw [mul_assoc]; rw [intCast_mul_eq_zsmul]; rw [mul_comm]; rw [coe_two_pi]; rw [zsmul_zero]; rw [zero_add]
  · rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' Real),
        mul_comm π _, sin_int_mul_pi, mul_zero]
    rw [← sub_eq_zero]; rw [cos_sub_cos]; rw [← sub_neg_eq_add]; rw [H]; rw [mul_assoc 2 π k]; rw [mul_div_cancel_left₀ _ (two_ne_zero' Real)]; rw [mul_comm π _]; rw [sin_int_mul_pi]; rw [mul_zero]; rw [zero_mul]

Depends on / 依赖: coe_sub, coe_two_pi, cos_sub_cos, eq_div_iff_mul_eq, eq_false, eq_neg_iff_add_eq_zero, false_or, intCast_mul_eq_zsmul, mul_assoc, mul_comm, mul_eq_zero, neg_eq_zero, sin_eq_zero_iff, sub_add_cancel, sub_eq_iff_eq_add, sub_eq_zero, two_ne_zero
-/
theorem cos_eq_iff_coe_eq_or_eq_neg {θ ψ : Real} :
    cos θ = cos ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) = -ψ := by
  constructor
  · intro Hcos
    rw [← sub_eq_zero]; rw [cos_sub_cos]; rw [mul_eq_zero]; rw [mul_eq_zero]; rw [neg_eq_zero]; rw [eq_false (two_ne_zero' Real)]; rw [false_or]; rw [sin_eq_zero_iff]; rw [sin_eq_zero_iff] at Hcos
    rcases Hcos with (⟨n, hn⟩ | ⟨n, hn⟩)
    · right
      rw [eq_div_iff_mul_eq (two_ne_zero' Real)]; rw [← sub_eq_iff_eq_add] at hn
      rw [← hn]; rw [coe_sub]; rw [eq_neg_iff_add_eq_zero]; rw [sub_add_cancel]; rw [mul_assoc]; rw [intCast_mul_eq_zsmul]; rw [mul_comm]; rw [coe_two_pi]; rw [zsmul_zero]
    · left
      rw [eq_div_iff_mul_eq (two_ne_zero' Real)]; rw [eq_sub_iff_add_eq] at hn
      rw [← hn]; rw [coe_add]; rw [mul_assoc]; rw [intCast_mul_eq_zsmul]; rw [mul_comm]; rw [coe_two_pi]; rw [zsmul_zero]; rw [zero_add]
  · rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' Real),
        mul_comm π _, sin_int_mul_pi, mul_zero]
    rw [← sub_eq_zero]; rw [cos_sub_cos]; rw [← sub_neg_eq_add]; rw [H]; rw [mul_assoc 2 π k]; rw [mul_div_cancel_left₀ _ (two_ne_zero' Real)]; rw [mul_comm π _]; rw [sin_int_mul_pi]; rw [mul_zero]; rw [zero_mul]

/--
theorem `sin_eq_iff_coe_eq_or_add_eq_pi` / 定理 `sin_eq_iff_coe_eq_or_add_eq_pi`

English:
theorem sin_eq_iff_coe_eq_or_add_eq_pi
  given: {θ ψ : Real}
  proof: by
  constructor
  · intro Hsin
    rw [← cos_pi_div_two_sub]; rw [← cos_pi_div_two_sub] at Hsin
    rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hsin with h | h
    · left
      rw [coe_sub]; rw [coe_sub] at h
      exact sub_right_inj.1 h
    right
    rw [coe_sub]; rw [coe_sub]; rw [eq_neg_iff_add_eq_zero]; rw [add_sub]; rw [sub_add_eq_add_sub]; rw [← coe_add]; rw [add_halves]; rw [sub_sub]; rw [sub_eq_zero] at h
    exact h.symm
  · rw [angle_eq_iff_two_pi_dvd_sub, ← eq_sub_iff_add_eq, ← coe_sub, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, sin_sub_sin, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' Real),
        mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul]
    have H' : θ + ψ = 2 * k * π + π := by
      rwa [← sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add, mul_assoc, mul_comm π _, ←
        mul_assoc] at H
    rw [← sub_eq_zero]; rw [sin_sub_sin]; rw [H']; rw [add_div]; rw [mul_assoc 2 _ π]; rw [mul_div_cancel_left₀ _ (two_ne_zero' Real)]; rw [cos_add_pi_div_two]; rw [sin_int_mul_pi]; rw [neg_zero]; rw [mul_zero]

中文:
定理 sin_eq_iff_coe_eq_or_add_eq_pi
  条件: {θ ψ : 实数}
  证明: by
  constructor
  · intro Hsin
    rw [← cos_pi_div_two_sub]; rw [← cos_pi_div_two_sub] at Hsin
    rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hsin with h | h
    · left
      rw [coe_sub]; rw [coe_sub] at h
      exact sub_right_inj.1 h
    right
    rw [coe_sub]; rw [coe_sub]; rw [eq_neg_iff_add_eq_zero]; rw [add_sub]; rw [sub_add_eq_add_sub]; rw [← coe_add]; rw [add_halves]; rw [sub_sub]; rw [sub_eq_zero] at h
    exact h.symm
  · rw [angle_eq_iff_two_pi_dvd_sub, ← eq_sub_iff_add_eq, ← coe_sub, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, sin_sub_sin, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' Real),
        mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul]
    have H' : θ + ψ = 2 * k * π + π := by
      rwa [← sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add, mul_assoc, mul_comm π _, ←
        mul_assoc] at H
    rw [← sub_eq_zero]; rw [sin_sub_sin]; rw [H']; rw [add_div]; rw [mul_assoc 2 _ π]; rw [mul_div_cancel_left₀ _ (two_ne_zero' Real)]; rw [cos_add_pi_div_two]; rw [sin_int_mul_pi]; rw [neg_zero]; rw [mul_zero]

Depends on / 依赖: add_halves, add_sub, angle_eq_iff_two_pi_dvd_sub, coe_add, coe_sub, cos_eq_iff_coe_eq_or_eq_neg, cos_eq_iff_coe_eq_or_eq_neg.mp, cos_pi_div_two_sub, eq_neg_iff_add_eq_zero, eq_sub_iff_add_eq, h.symm, sub_add_eq_add_sub, sub_eq_zero, sub_right_inj, sub_sub
-/
theorem sin_eq_iff_coe_eq_or_add_eq_pi {θ ψ : Real} :
    sin θ = sin ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) + ψ = π := by
  constructor
  · intro Hsin
    rw [← cos_pi_div_two_sub]; rw [← cos_pi_div_two_sub] at Hsin
    rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hsin with h | h
    · left
      rw [coe_sub]; rw [coe_sub] at h
      exact sub_right_inj.1 h
    right
    rw [coe_sub]; rw [coe_sub]; rw [eq_neg_iff_add_eq_zero]; rw [add_sub]; rw [sub_add_eq_add_sub]; rw [← coe_add]; rw [add_halves]; rw [sub_sub]; rw [sub_eq_zero] at h
    exact h.symm
  · rw [angle_eq_iff_two_pi_dvd_sub, ← eq_sub_iff_add_eq, ← coe_sub, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, sin_sub_sin, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' Real),
        mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul]
    have H' : θ + ψ = 2 * k * π + π := by
      rwa [← sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add, mul_assoc, mul_comm π _, ←
        mul_assoc] at H
    rw [← sub_eq_zero]; rw [sin_sub_sin]; rw [H']; rw [add_div]; rw [mul_assoc 2 _ π]; rw [mul_div_cancel_left₀ _ (two_ne_zero' Real)]; rw [cos_add_pi_div_two]; rw [sin_int_mul_pi]; rw [neg_zero]; rw [mul_zero]

/--
theorem `cos_sin_inj` / 定理 `cos_sin_inj`

English:
theorem cos_sin_inj
  given: {θ ψ : Real} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ)
  statement: (θ : Angle) = ψ
  proof: by
  rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hcos with hc | hc; · exact hc
  rcases sin_eq_iff_coe_eq_or_add_eq_pi.mp Hsin with hs | hs; · exact hs
  rw [eq_neg_iff_add_eq_zero]; rw [hs] at hc
  obtain ⟨n, hn⟩ : exists n, n • _ = _ := QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hc)
  rw [← neg_one_mul]; rw [add_zero]; rw [← sub_eq_zero]; rw [zsmul_eq_mul]; rw [← mul_assoc]; rw [← sub_mul]; rw [mul_eq_zero]; rw [eq_false (ne_of_gt pi_pos)]; rw [or_false]; rw [sub_neg_eq_add]; rw [← Int.cast_zero]; rw [← Int.cast_one]; rw [← Int.cast_ofNat]; rw [← Int.cast_mul]; rw [← Int.cast_add]; rw [Int.cast_inj] at hn
  have : (n * 2 + 1) % (2 : Int) = 0 % (2 : Int) := congr_arg (· % (2 : Int)) hn
  rw [add_comm]; rw [Int.add_mul_emod_self_right] at this
  exact absurd this one_ne_zero

中文:
定理 cos_sin_inj
  条件: {θ ψ : 实数} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ)
  结论: (θ : Angle) = ψ
  证明: by
  rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hcos with hc | hc; · exact hc
  rcases sin_eq_iff_coe_eq_or_add_eq_pi.mp Hsin with hs | hs; · exact hs
  rw [eq_neg_iff_add_eq_zero]; rw [hs] at hc
  obtain ⟨n, hn⟩ : exists n, n • _ = _ := QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hc)
  rw [← neg_one_mul]; rw [add_zero]; rw [← sub_eq_zero]; rw [zsmul_eq_mul]; rw [← mul_assoc]; rw [← sub_mul]; rw [mul_eq_zero]; rw [eq_false (ne_of_gt pi_pos)]; rw [or_false]; rw [sub_neg_eq_add]; rw [← Int.cast_zero]; rw [← Int.cast_one]; rw [← Int.cast_ofNat]; rw [← Int.cast_mul]; rw [← Int.cast_add]; rw [Int.cast_inj] at hn
  have : (n * 2 + 1) % (2 : Int) = 0 % (2 : Int) := congr_arg (· % (2 : Int)) hn
  rw [add_comm]; rw [Int.add_mul_emod_self_right] at this
  exact absurd this one_ne_zero

Depends on / 依赖: Int.cast_zero, Quotient, Quotient.exact, QuotientAddGroup, QuotientAddGroup.leftRel_apply.mp, add_zero, cast_zero, cos_eq_iff_coe_eq_or_eq_neg, cos_eq_iff_coe_eq_or_eq_neg.mp, eq_false, eq_neg_iff_add_eq_zero, leftRel_apply, mul_assoc, mul_eq_zero, ne_of_gt, neg_one_mul, or_false, pi_pos, sin_eq_iff_coe_eq_or_add_eq_pi, sin_eq_iff_coe_eq_or_add_eq_pi.mp
-/
theorem cos_sin_inj {θ ψ : Real} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : Angle) = ψ := by
  rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hcos with hc | hc; · exact hc
  rcases sin_eq_iff_coe_eq_or_add_eq_pi.mp Hsin with hs | hs; · exact hs
  rw [eq_neg_iff_add_eq_zero]; rw [hs] at hc
  obtain ⟨n, hn⟩ : exists n, n • _ = _ := QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hc)
  rw [← neg_one_mul]; rw [add_zero]; rw [← sub_eq_zero]; rw [zsmul_eq_mul]; rw [← mul_assoc]; rw [← sub_mul]; rw [mul_eq_zero]; rw [eq_false (ne_of_gt pi_pos)]; rw [or_false]; rw [sub_neg_eq_add]; rw [← Int.cast_zero]; rw [← Int.cast_one]; rw [← Int.cast_ofNat]; rw [← Int.cast_mul]; rw [← Int.cast_add]; rw [Int.cast_inj] at hn
  have : (n * 2 + 1) % (2 : Int) = 0 % (2 : Int) := congr_arg (· % (2 : Int)) hn
  rw [add_comm]; rw [Int.add_mul_emod_self_right] at this
  exact absurd this one_ne_zero

/--
Definition of `sin` / `sin` 的定义

English:
definition sin
  signature: (θ : Angle)
  body: sin_periodic.lift θ

@[simp]

中文:
定义 sin
  签名: (θ : Angle)
  定义体: sin_periodic.lift θ

@[simp]

Depends on / 依赖: sin_periodic, sin_periodic.lift
-/
def sin (θ : Angle) : Real :=
  sin_periodic.lift θ

@[simp]
/--
theorem `sin_coe` / 定理 `sin_coe`

English:
theorem sin_coe
  given: (x : Real)
  statement: sin (x : Angle) = Real.sin x
  proof: rfl

@[continuity]

中文:
定理 sin_coe
  条件: (x : 实数)
  结论: sin (x : Angle) = 实数.sin x
  证明: rfl

@[continuity]
-/
theorem sin_coe (x : Real) : sin (x : Angle) = Real.sin x :=
  rfl

@[continuity]
/--
theorem `continuous_sin` / 定理 `continuous_sin`

English:
theorem continuous_sin
  statement: Continuous sin
  proof: Real.continuous_sin.quotient_liftOn' _

中文:
定理 continuous_sin
  结论: 连续 sin
  证明: Real.continuous_sin.quotient_liftOn' _

Depends on / 依赖: Real.continuous_sin.quotient_liftOn, continuous_sin, quotient_liftOn
-/
theorem continuous_sin : Continuous sin :=
  Real.continuous_sin.quotient_liftOn' _

/--
Definition of `cos` / `cos` 的定义

English:
definition cos
  signature: (θ : Angle)
  body: cos_periodic.lift θ

@[simp]

中文:
定义 cos
  签名: (θ : Angle)
  定义体: cos_periodic.lift θ

@[simp]

Depends on / 依赖: cos_periodic, cos_periodic.lift
-/
def cos (θ : Angle) : Real :=
  cos_periodic.lift θ

@[simp]
/--
theorem `cos_coe` / 定理 `cos_coe`

English:
theorem cos_coe
  given: (x : Real)
  statement: cos (x : Angle) = Real.cos x
  proof: rfl

@[continuity]

中文:
定理 cos_coe
  条件: (x : 实数)
  结论: cos (x : Angle) = 实数.cos x
  证明: rfl

@[continuity]
-/
theorem cos_coe (x : Real) : cos (x : Angle) = Real.cos x :=
  rfl

@[continuity]
/--
theorem `continuous_cos` / 定理 `continuous_cos`

English:
theorem continuous_cos
  statement: Continuous cos
  proof: Real.continuous_cos.quotient_liftOn' _

中文:
定理 continuous_cos
  结论: 连续 cos
  证明: Real.continuous_cos.quotient_liftOn' _

Depends on / 依赖: Real.continuous_cos.quotient_liftOn, continuous_cos, quotient_liftOn
-/
theorem continuous_cos : Continuous cos :=
  Real.continuous_cos.quotient_liftOn' _

/--
theorem `cos_eq_real_cos_iff_eq_or_eq_neg` / 定理 `cos_eq_real_cos_iff_eq_or_eq_neg`

English:
theorem cos_eq_real_cos_iff_eq_or_eq_neg
  given: {θ : Angle} {ψ : Real}
  proof: by
  induction θ using Real.Angle.induction_on
  exact cos_eq_iff_coe_eq_or_eq_neg

中文:
定理 cos_eq_real_cos_iff_eq_or_eq_neg
  条件: {θ : Angle} {ψ : 实数}
  证明: by
  induction θ using Real.Angle.induction_on
  exact cos_eq_iff_coe_eq_or_eq_neg

Depends on / 依赖: Real.Angle.induction_on, cos_eq_iff_coe_eq_or_eq_neg, induction_on
-/
theorem cos_eq_real_cos_iff_eq_or_eq_neg {θ : Angle} {ψ : Real} :
    cos θ = Real.cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction θ using Real.Angle.induction_on
  exact cos_eq_iff_coe_eq_or_eq_neg

/--
theorem `cos_eq_iff_eq_or_eq_neg` / 定理 `cos_eq_iff_eq_or_eq_neg`

English:
theorem cos_eq_iff_eq_or_eq_neg
  given: {θ ψ : Angle}
  statement: cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ
  proof: by
  induction ψ using Real.Angle.induction_on
  exact cos_eq_real_cos_iff_eq_or_eq_neg

中文:
定理 cos_eq_iff_eq_or_eq_neg
  条件: {θ ψ : Angle}
  结论: cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ
  证明: by
  induction ψ using Real.Angle.induction_on
  exact cos_eq_real_cos_iff_eq_or_eq_neg

Depends on / 依赖: Real.Angle.induction_on, cos_eq_real_cos_iff_eq_or_eq_neg, induction_on
-/
theorem cos_eq_iff_eq_or_eq_neg {θ ψ : Angle} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction ψ using Real.Angle.induction_on
  exact cos_eq_real_cos_iff_eq_or_eq_neg

/--
theorem `sin_eq_real_sin_iff_eq_or_add_eq_pi` / 定理 `sin_eq_real_sin_iff_eq_or_add_eq_pi`

English:
theorem sin_eq_real_sin_iff_eq_or_add_eq_pi
  given: {θ : Angle} {ψ : Real}
  proof: by
  induction θ using Real.Angle.induction_on
  exact sin_eq_iff_coe_eq_or_add_eq_pi

中文:
定理 sin_eq_real_sin_iff_eq_or_add_eq_pi
  条件: {θ : Angle} {ψ : 实数}
  证明: by
  induction θ using Real.Angle.induction_on
  exact sin_eq_iff_coe_eq_or_add_eq_pi

Depends on / 依赖: Real.Angle.induction_on, induction_on, sin_eq_iff_coe_eq_or_add_eq_pi
-/
theorem sin_eq_real_sin_iff_eq_or_add_eq_pi {θ : Angle} {ψ : Real} :
    sin θ = Real.sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction θ using Real.Angle.induction_on
  exact sin_eq_iff_coe_eq_or_add_eq_pi

/--
theorem `sin_eq_iff_eq_or_add_eq_pi` / 定理 `sin_eq_iff_eq_or_add_eq_pi`

English:
theorem sin_eq_iff_eq_or_add_eq_pi
  given: {θ ψ : Angle}
  statement: sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π
  proof: by
  induction ψ using Real.Angle.induction_on
  exact sin_eq_real_sin_iff_eq_or_add_eq_pi

@[simp]

中文:
定理 sin_eq_iff_eq_or_add_eq_pi
  条件: {θ ψ : Angle}
  结论: sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π
  证明: by
  induction ψ using Real.Angle.induction_on
  exact sin_eq_real_sin_iff_eq_or_add_eq_pi

@[simp]

Depends on / 依赖: Real.Angle.induction_on, induction_on, sin_eq_real_sin_iff_eq_or_add_eq_pi
-/
theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : Angle} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction ψ using Real.Angle.induction_on
  exact sin_eq_real_sin_iff_eq_or_add_eq_pi

@[simp]
/--
theorem `sin_zero` / 定理 `sin_zero`

English:
theorem sin_zero
  statement: sin (0 : Angle) = 0
  proof: by rw [← coe_zero, sin_coe, Real.sin_zero]

中文:
定理 sin_zero
  结论: sin (0 : Angle) = 0
  证明: by rw [← coe_zero, sin_coe, Real.sin_zero]

Depends on / 依赖: Real.sin_zero, coe_zero, sin_coe, sin_zero
-/
theorem sin_zero : sin (0 : Angle) = 0 := by rw [← coe_zero, sin_coe, Real.sin_zero]

/--
theorem `sin_coe_pi` / 定理 `sin_coe_pi`

English:
theorem sin_coe_pi
  statement: sin (π : Angle) = 0
  proof: by rw [sin_coe, Real.sin_pi]

中文:
定理 sin_coe_pi
  结论: sin (π : Angle) = 0
  证明: by rw [sin_coe, Real.sin_pi]

Depends on / 依赖: Real.sin_pi, sin_coe, sin_pi
-/
theorem sin_coe_pi : sin (π : Angle) = 0 := by rw [sin_coe, Real.sin_pi]

/--
theorem `sin_eq_zero_iff` / 定理 `sin_eq_zero_iff`

English:
theorem sin_eq_zero_iff
  given: {θ : Angle}
  statement: sin θ = 0 ↔ θ = 0 ∨ θ = π
  proof: by
  nth_rw 1 [← sin_zero]
  rw [sin_eq_iff_eq_or_add_eq_pi]
  simp

中文:
定理 sin_eq_zero_iff
  条件: {θ : Angle}
  结论: sin θ = 0 ↔ θ = 0 ∨ θ = π
  证明: by
  nth_rw 1 [← sin_zero]
  rw [sin_eq_iff_eq_or_add_eq_pi]
  simp

Depends on / 依赖: nth_rw, sin_eq_iff_eq_or_add_eq_pi, sin_zero
-/
theorem sin_eq_zero_iff {θ : Angle} : sin θ = 0 ↔ θ = 0 ∨ θ = π := by
  nth_rw 1 [← sin_zero]
  rw [sin_eq_iff_eq_or_add_eq_pi]
  simp

/--
theorem `sin_ne_zero_iff` / 定理 `sin_ne_zero_iff`

English:
theorem sin_ne_zero_iff
  given: {θ : Angle}
  statement: sin θ != 0 ↔ θ != 0 ∧ θ != π
  proof: by
  rw [← not_or]; rw [← sin_eq_zero_iff]

@[simp]

中文:
定理 sin_ne_zero_iff
  条件: {θ : Angle}
  结论: sin θ != 0 ↔ θ != 0 ∧ θ != π
  证明: by
  rw [← not_or]; rw [← sin_eq_zero_iff]

@[simp]

Depends on / 依赖: not_or, sin_eq_zero_iff
-/
theorem sin_ne_zero_iff {θ : Angle} : sin θ != 0 ↔ θ != 0 ∧ θ != π := by
  rw [← not_or]; rw [← sin_eq_zero_iff]

@[simp]
/--
theorem `sin_neg` / 定理 `sin_neg`

English:
theorem sin_neg
  given: (θ : Angle)
  statement: sin (-θ) = -sin θ
  proof: by
  induction θ using Real.Angle.induction_on
  exact Real.sin_neg _

中文:
定理 sin_neg
  条件: (θ : Angle)
  结论: sin (-θ) = -sin θ
  证明: by
  induction θ using Real.Angle.induction_on
  exact Real.sin_neg _

Depends on / 依赖: Real.Angle.induction_on, Real.sin_neg, induction_on, sin_neg
-/
theorem sin_neg (θ : Angle) : sin (-θ) = -sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_neg _

/--
theorem `sin_antiperiodic` / 定理 `sin_antiperiodic`

English:
theorem sin_antiperiodic
  statement: Function.Antiperiodic sin (π : Angle)
  proof: by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.sin_antiperiodic _

@[simp]

中文:
定理 sin_antiperiodic
  结论: 函数.Antiperiodic sin (π : Angle)
  证明: by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.sin_antiperiodic _

@[simp]

Depends on / 依赖: Real.Angle.induction_on, Real.sin_antiperiodic, induction_on, sin_antiperiodic
-/
theorem sin_antiperiodic : Function.Antiperiodic sin (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.sin_antiperiodic _

@[simp]
/--
theorem `sin_add_pi` / 定理 `sin_add_pi`

English:
theorem sin_add_pi
  given: (θ : Angle)
  statement: sin (θ + π) = -sin θ
  proof: sin_antiperiodic θ

@[simp]

中文:
定理 sin_add_pi
  条件: (θ : Angle)
  结论: sin (θ + π) = -sin θ
  证明: sin_antiperiodic θ

@[simp]

Depends on / 依赖: sin_antiperiodic
-/
theorem sin_add_pi (θ : Angle) : sin (θ + π) = -sin θ :=
  sin_antiperiodic θ

@[simp]
/--
theorem `sin_sub_pi` / 定理 `sin_sub_pi`

English:
theorem sin_sub_pi
  given: (θ : Angle)
  statement: sin (θ - π) = -sin θ
  proof: sin_antiperiodic.sub_eq θ

@[simp]

中文:
定理 sin_sub_pi
  条件: (θ : Angle)
  结论: sin (θ - π) = -sin θ
  证明: sin_antiperiodic.sub_eq θ

@[simp]

Depends on / 依赖: sin_antiperiodic, sin_antiperiodic.sub_eq, sub_eq
-/
theorem sin_sub_pi (θ : Angle) : sin (θ - π) = -sin θ :=
  sin_antiperiodic.sub_eq θ

@[simp]
/--
theorem `cos_zero` / 定理 `cos_zero`

English:
theorem cos_zero
  statement: cos (0 : Angle) = 1
  proof: by rw [← coe_zero, cos_coe, Real.cos_zero]

中文:
定理 cos_zero
  结论: cos (0 : Angle) = 1
  证明: by rw [← coe_zero, cos_coe, Real.cos_zero]

Depends on / 依赖: Real.cos_zero, coe_zero, cos_coe, cos_zero
-/
theorem cos_zero : cos (0 : Angle) = 1 := by rw [← coe_zero, cos_coe, Real.cos_zero]

/--
theorem `cos_coe_pi` / 定理 `cos_coe_pi`

English:
theorem cos_coe_pi
  statement: cos (π : Angle) = -1
  proof: by rw [cos_coe, Real.cos_pi]

@[simp]

中文:
定理 cos_coe_pi
  结论: cos (π : Angle) = -1
  证明: by rw [cos_coe, Real.cos_pi]

@[simp]

Depends on / 依赖: Real.cos_pi, cos_coe, cos_pi
-/
theorem cos_coe_pi : cos (π : Angle) = -1 := by rw [cos_coe, Real.cos_pi]

@[simp]
/--
theorem `cos_neg` / 定理 `cos_neg`

English:
theorem cos_neg
  given: (θ : Angle)
  statement: cos (-θ) = cos θ
  proof: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_neg _

中文:
定理 cos_neg
  条件: (θ : Angle)
  结论: cos (-θ) = cos θ
  证明: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_neg _

Depends on / 依赖: Real.Angle.induction_on, Real.cos_neg, cos_neg, induction_on
-/
theorem cos_neg (θ : Angle) : cos (-θ) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_neg _

/--
theorem `cos_antiperiodic` / 定理 `cos_antiperiodic`

English:
theorem cos_antiperiodic
  statement: Function.Antiperiodic cos (π : Angle)
  proof: by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.cos_antiperiodic _

@[simp]

中文:
定理 cos_antiperiodic
  结论: 函数.Antiperiodic cos (π : Angle)
  证明: by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.cos_antiperiodic _

@[simp]

Depends on / 依赖: Real.Angle.induction_on, Real.cos_antiperiodic, cos_antiperiodic, induction_on
-/
theorem cos_antiperiodic : Function.Antiperiodic cos (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.cos_antiperiodic _

@[simp]
/--
theorem `cos_add_pi` / 定理 `cos_add_pi`

English:
theorem cos_add_pi
  given: (θ : Angle)
  statement: cos (θ + π) = -cos θ
  proof: cos_antiperiodic θ

@[simp]

中文:
定理 cos_add_pi
  条件: (θ : Angle)
  结论: cos (θ + π) = -cos θ
  证明: cos_antiperiodic θ

@[simp]

Depends on / 依赖: cos_antiperiodic
-/
theorem cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ :=
  cos_antiperiodic θ

@[simp]
/--
theorem `cos_sub_pi` / 定理 `cos_sub_pi`

English:
theorem cos_sub_pi
  given: (θ : Angle)
  statement: cos (θ - π) = -cos θ
  proof: cos_antiperiodic.sub_eq θ

中文:
定理 cos_sub_pi
  条件: (θ : Angle)
  结论: cos (θ - π) = -cos θ
  证明: cos_antiperiodic.sub_eq θ

Depends on / 依赖: cos_antiperiodic, cos_antiperiodic.sub_eq, sub_eq
-/
theorem cos_sub_pi (θ : Angle) : cos (θ - π) = -cos θ :=
  cos_antiperiodic.sub_eq θ

/--
theorem `cos_eq_zero_iff` / 定理 `cos_eq_zero_iff`

English:
theorem cos_eq_zero_iff
  given: {θ : Angle}
  statement: cos θ = 0 ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real)
  proof: by
  rw [← cos_pi_div_two]; rw [← cos_coe]; rw [cos_eq_iff_eq_or_eq_neg]; rw [← coe_neg]; rw [← neg_div]

中文:
定理 cos_eq_zero_iff
  条件: {θ : Angle}
  结论: cos θ = 0 ↔ θ = (π / 2 : 实数) ∨ θ = (-π / 2 : 实数)
  证明: by
  rw [← cos_pi_div_two]; rw [← cos_coe]; rw [cos_eq_iff_eq_or_eq_neg]; rw [← coe_neg]; rw [← neg_div]

Depends on / 依赖: coe_neg, cos_coe, cos_eq_iff_eq_or_eq_neg, cos_pi_div_two, neg_div
-/
theorem cos_eq_zero_iff {θ : Angle} : cos θ = 0 ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real) := by
  rw [← cos_pi_div_two]; rw [← cos_coe]; rw [cos_eq_iff_eq_or_eq_neg]; rw [← coe_neg]; rw [← neg_div]

/--
theorem `sin_add` / 定理 `sin_add`

English:
theorem sin_add
  given: (θ₁ θ₂ : Real.Angle)
  statement: sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * sin θ₂
  proof: by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact Real.sin_add _ _

中文:
定理 sin_add
  条件: (θ₁ θ₂ : 实数.Angle)
  结论: sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * sin θ₂
  证明: by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact Real.sin_add _ _

Depends on / 依赖: Real.Angle.induction_on, Real.sin_add, induction_on, sin_add
-/
theorem sin_add (θ₁ θ₂ : Real.Angle) : sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * sin θ₂ := by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact Real.sin_add _ _

/--
theorem `cos_add` / 定理 `cos_add`

English:
theorem cos_add
  given: (θ₁ θ₂ : Real.Angle)
  statement: cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂
  proof: by
  induction θ₂ using Real.Angle.induction_on
  induction θ₁ using Real.Angle.induction_on
  exact Real.cos_add _ _

中文:
定理 cos_add
  条件: (θ₁ θ₂ : 实数.Angle)
  结论: cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂
  证明: by
  induction θ₂ using Real.Angle.induction_on
  induction θ₁ using Real.Angle.induction_on
  exact Real.cos_add _ _

Depends on / 依赖: Real.Angle.induction_on, Real.cos_add, cos_add, induction_on
-/
theorem cos_add (θ₁ θ₂ : Real.Angle) : cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂ := by
  induction θ₂ using Real.Angle.induction_on
  induction θ₁ using Real.Angle.induction_on
  exact Real.cos_add _ _

/--
theorem `sin_two_nsmul` / 定理 `sin_two_nsmul`

English:
theorem sin_two_nsmul
  given: (θ : Angle)
  statement: sin (2 • θ) = 2 • (sin θ * cos θ)
  proof: by
  simp [two_nsmul, two_mul, sin_add, mul_comm]

@[simp]

中文:
定理 sin_two_nsmul
  条件: (θ : Angle)
  结论: sin (2 • θ) = 2 • (sin θ * cos θ)
  证明: by
  simp [two_nsmul, two_mul, sin_add, mul_comm]

@[simp]

Depends on / 依赖: mul_comm, sin_add, two_mul, two_nsmul
-/
theorem sin_two_nsmul (θ : Angle) : sin (2 • θ) = 2 • (sin θ * cos θ) := by
  simp [two_nsmul, two_mul, sin_add, mul_comm]

@[simp]
/--
theorem `cos_sq_add_sin_sq` / 定理 `cos_sq_add_sin_sq`

English:
theorem cos_sq_add_sin_sq
  given: (θ : Real.Angle)
  statement: cos θ ^ 2 + sin θ ^ 2 = 1
  proof: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sq_add_sin_sq _

中文:
定理 cos_sq_add_sin_sq
  条件: (θ : 实数.Angle)
  结论: cos θ ^ 2 + sin θ ^ 2 = 1
  证明: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sq_add_sin_sq _

Depends on / 依赖: Real.Angle.induction_on, Real.cos_sq_add_sin_sq, cos_sq_add_sin_sq, induction_on
-/
theorem cos_sq_add_sin_sq (θ : Real.Angle) : cos θ ^ 2 + sin θ ^ 2 = 1 := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sq_add_sin_sq _

/--
theorem `sin_add_pi_div_two` / 定理 `sin_add_pi_div_two`

English:
theorem sin_add_pi_div_two
  given: (θ : Angle)
  statement: sin (θ + ↑(π / 2)) = cos θ
  proof: by
  induction θ using Real.Angle.induction_on
  exact Real.sin_add_pi_div_two _

中文:
定理 sin_add_pi_div_two
  条件: (θ : Angle)
  结论: sin (θ + ↑(π / 2)) = cos θ
  证明: by
  induction θ using Real.Angle.induction_on
  exact Real.sin_add_pi_div_two _

Depends on / 依赖: Real.Angle.induction_on, Real.sin_add_pi_div_two, induction_on, sin_add_pi_div_two
-/
theorem sin_add_pi_div_two (θ : Angle) : sin (θ + ↑(π / 2)) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_add_pi_div_two _

/--
theorem `sin_sub_pi_div_two` / 定理 `sin_sub_pi_div_two`

English:
theorem sin_sub_pi_div_two
  given: (θ : Angle)
  statement: sin (θ - ↑(π / 2)) = -cos θ
  proof: by
  induction θ using Real.Angle.induction_on
  exact Real.sin_sub_pi_div_two _

中文:
定理 sin_sub_pi_div_two
  条件: (θ : Angle)
  结论: sin (θ - ↑(π / 2)) = -cos θ
  证明: by
  induction θ using Real.Angle.induction_on
  exact Real.sin_sub_pi_div_two _

Depends on / 依赖: Real.Angle.induction_on, Real.sin_sub_pi_div_two, induction_on, sin_sub_pi_div_two
-/
theorem sin_sub_pi_div_two (θ : Angle) : sin (θ - ↑(π / 2)) = -cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_sub_pi_div_two _

/--
theorem `sin_pi_div_two_sub` / 定理 `sin_pi_div_two_sub`

English:
theorem sin_pi_div_two_sub
  given: (θ : Angle)
  statement: sin (↑(π / 2) - θ) = cos θ
  proof: by
  induction θ using Real.Angle.induction_on
  exact Real.sin_pi_div_two_sub _

中文:
定理 sin_pi_div_two_sub
  条件: (θ : Angle)
  结论: sin (↑(π / 2) - θ) = cos θ
  证明: by
  induction θ using Real.Angle.induction_on
  exact Real.sin_pi_div_two_sub _

Depends on / 依赖: Real.Angle.induction_on, Real.sin_pi_div_two_sub, induction_on, sin_pi_div_two_sub
-/
theorem sin_pi_div_two_sub (θ : Angle) : sin (↑(π / 2) - θ) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_pi_div_two_sub _

/--
theorem `cos_add_pi_div_two` / 定理 `cos_add_pi_div_two`

English:
theorem cos_add_pi_div_two
  given: (θ : Angle)
  statement: cos (θ + ↑(π / 2)) = -sin θ
  proof: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_add_pi_div_two _

中文:
定理 cos_add_pi_div_two
  条件: (θ : Angle)
  结论: cos (θ + ↑(π / 2)) = -sin θ
  证明: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_add_pi_div_two _

Depends on / 依赖: Real.Angle.induction_on, Real.cos_add_pi_div_two, cos_add_pi_div_two, induction_on
-/
theorem cos_add_pi_div_two (θ : Angle) : cos (θ + ↑(π / 2)) = -sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_add_pi_div_two _

/--
theorem `cos_sub_pi_div_two` / 定理 `cos_sub_pi_div_two`

English:
theorem cos_sub_pi_div_two
  given: (θ : Angle)
  statement: cos (θ - ↑(π / 2)) = sin θ
  proof: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sub_pi_div_two _

中文:
定理 cos_sub_pi_div_two
  条件: (θ : Angle)
  结论: cos (θ - ↑(π / 2)) = sin θ
  证明: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sub_pi_div_two _

Depends on / 依赖: Real.Angle.induction_on, Real.cos_sub_pi_div_two, cos_sub_pi_div_two, induction_on
-/
theorem cos_sub_pi_div_two (θ : Angle) : cos (θ - ↑(π / 2)) = sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sub_pi_div_two _

/--
theorem `cos_pi_div_two_sub` / 定理 `cos_pi_div_two_sub`

English:
theorem cos_pi_div_two_sub
  given: (θ : Angle)
  statement: cos (↑(π / 2) - θ) = sin θ
  proof: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_pi_div_two_sub _

中文:
定理 cos_pi_div_two_sub
  条件: (θ : Angle)
  结论: cos (↑(π / 2) - θ) = sin θ
  证明: by
  induction θ using Real.Angle.induction_on
  exact Real.cos_pi_div_two_sub _

Depends on / 依赖: Real.Angle.induction_on, Real.cos_pi_div_two_sub, cos_pi_div_two_sub, induction_on
-/
theorem cos_pi_div_two_sub (θ : Angle) : cos (↑(π / 2) - θ) = sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_pi_div_two_sub _

/--
theorem `abs_sin_eq_of_two_nsmul_eq` / 定理 `abs_sin_eq_of_two_nsmul_eq`

English:
theorem abs_sin_eq_of_two_nsmul_eq
  given: {θ ψ : Angle} (h : (2 : Nat) • θ = (2 : Nat) • ψ)
  proof: by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [sin_add_pi, abs_neg]

中文:
定理 abs_sin_eq_of_two_nsmul_eq
  条件: {θ ψ : Angle} (h : (2 : 自然数) • θ = (2 : 自然数) • ψ)
  证明: by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [sin_add_pi, abs_neg]

Depends on / 依赖: abs_neg, sin_add_pi, two_nsmul_eq_iff
-/
theorem abs_sin_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : Nat) • θ = (2 : Nat) • ψ) :
    |sin θ| = |sin ψ| := by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [sin_add_pi, abs_neg]

/--
theorem `abs_sin_eq_of_two_zsmul_eq` / 定理 `abs_sin_eq_of_two_zsmul_eq`

English:
theorem abs_sin_eq_of_two_zsmul_eq
  given: {θ ψ : Angle} (h : (2 : Int) • θ = (2 : Int) • ψ)
  proof: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_sin_eq_of_two_nsmul_eq h

中文:
定理 abs_sin_eq_of_two_zsmul_eq
  条件: {θ ψ : Angle} (h : (2 : 整数) • θ = (2 : 整数) • ψ)
  证明: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_sin_eq_of_two_nsmul_eq h

Depends on / 依赖: abs_sin_eq_of_two_nsmul_eq, simp_rw, two_nsmul, two_zsmul
-/
theorem abs_sin_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : Int) • θ = (2 : Int) • ψ) :
    |sin θ| = |sin ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_sin_eq_of_two_nsmul_eq h

/--
theorem `abs_cos_eq_of_two_nsmul_eq` / 定理 `abs_cos_eq_of_two_nsmul_eq`

English:
theorem abs_cos_eq_of_two_nsmul_eq
  given: {θ ψ : Angle} (h : (2 : Nat) • θ = (2 : Nat) • ψ)
  proof: by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [cos_add_pi, abs_neg]

中文:
定理 abs_cos_eq_of_two_nsmul_eq
  条件: {θ ψ : Angle} (h : (2 : 自然数) • θ = (2 : 自然数) • ψ)
  证明: by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [cos_add_pi, abs_neg]

Depends on / 依赖: abs_neg, cos_add_pi, two_nsmul_eq_iff
-/
theorem abs_cos_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : Nat) • θ = (2 : Nat) • ψ) :
    |cos θ| = |cos ψ| := by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [cos_add_pi, abs_neg]

/--
theorem `abs_cos_eq_of_two_zsmul_eq` / 定理 `abs_cos_eq_of_two_zsmul_eq`

English:
theorem abs_cos_eq_of_two_zsmul_eq
  given: {θ ψ : Angle} (h : (2 : Int) • θ = (2 : Int) • ψ)
  proof: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_of_two_nsmul_eq h

@[simp]

中文:
定理 abs_cos_eq_of_two_zsmul_eq
  条件: {θ ψ : Angle} (h : (2 : 整数) • θ = (2 : 整数) • ψ)
  证明: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_of_two_nsmul_eq h

@[simp]

Depends on / 依赖: abs_cos_eq_of_two_nsmul_eq, simp_rw, two_nsmul, two_zsmul
-/
theorem abs_cos_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : Int) • θ = (2 : Int) • ψ) :
    |cos θ| = |cos ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_of_two_nsmul_eq h

@[simp]
/--
theorem `coe_toIcoMod` / 定理 `coe_toIcoMod`

English:
theorem coe_toIcoMod
  given: (θ ψ : Real)
  statement: ↑(toIcoMod two_pi_pos ψ θ) = (θ : Angle)
  proof: by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIcoDiv two_pi_pos ψ θ, ?_⟩
  rw [toIcoMod_sub_self]; rw [zsmul_eq_mul]; rw [mul_comm]

@[simp]

中文:
定理 coe_toIcoMod
  条件: (θ ψ : 实数)
  结论: ↑(toIcoMod two_pi_pos ψ θ) = (θ : Angle)
  证明: by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIcoDiv two_pi_pos ψ θ, ?_⟩
  rw [toIcoMod_sub_self]; rw [zsmul_eq_mul]; rw [mul_comm]

@[simp]

Depends on / 依赖: angle_eq_iff_two_pi_dvd_sub, mul_comm, toIcoDiv, toIcoMod_sub_self, two_pi_pos, zsmul_eq_mul
-/
theorem coe_toIcoMod (θ ψ : Real) : ↑(toIcoMod two_pi_pos ψ θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIcoDiv two_pi_pos ψ θ, ?_⟩
  rw [toIcoMod_sub_self]; rw [zsmul_eq_mul]; rw [mul_comm]

@[simp]
/--
theorem `coe_toIocMod` / 定理 `coe_toIocMod`

English:
theorem coe_toIocMod
  given: (θ ψ : Real)
  statement: ↑(toIocMod two_pi_pos ψ θ) = (θ : Angle)
  proof: by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIocDiv two_pi_pos ψ θ, ?_⟩
  rw [toIocMod_sub_self]; rw [zsmul_eq_mul]; rw [mul_comm]

中文:
定理 coe_toIocMod
  条件: (θ ψ : 实数)
  结论: ↑(toIocMod two_pi_pos ψ θ) = (θ : Angle)
  证明: by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIocDiv two_pi_pos ψ θ, ?_⟩
  rw [toIocMod_sub_self]; rw [zsmul_eq_mul]; rw [mul_comm]

Depends on / 依赖: angle_eq_iff_two_pi_dvd_sub, mul_comm, toIocDiv, toIocMod_sub_self, two_pi_pos, zsmul_eq_mul
-/
theorem coe_toIocMod (θ ψ : Real) : ↑(toIocMod two_pi_pos ψ θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIocDiv two_pi_pos ψ θ, ?_⟩
  rw [toIocMod_sub_self]; rw [zsmul_eq_mul]; rw [mul_comm]

/--
Definition of `toReal` / `toReal` 的定义

English:
definition toReal
  signature: (θ : Angle)
  body: (toIocMod_periodic two_pi_pos (-π)).lift θ

中文:
定义 to实数
  签名: (θ : Angle)
  定义体: (toIocMod_periodic two_pi_pos (-π)).lift θ

Depends on / 依赖: toIocMod_periodic, two_pi_pos
-/
def toReal (θ : Angle) : Real :=
  (toIocMod_periodic two_pi_pos (-π)).lift θ

/--
theorem `toReal_coe` / 定理 `toReal_coe`

English:
theorem toReal_coe
  given: (θ : Real)
  statement: (θ : Angle).toReal = toIocMod two_pi_pos (-π) θ
  proof: rfl

中文:
定理 to实数_coe
  条件: (θ : 实数)
  结论: (θ : Angle).to实数 = toIocMod two_pi_pos (-π) θ
  证明: rfl
-/
theorem toReal_coe (θ : Real) : (θ : Angle).toReal = toIocMod two_pi_pos (-π) θ :=
  rfl

/--
theorem `toReal_coe_eq_self_iff` / 定理 `toReal_coe_eq_self_iff`

English:
theorem toReal_coe_eq_self_iff
  given: {θ : Real}
  statement: (θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π
  proof: by
  rw [toReal_coe]; rw [toIocMod_eq_self two_pi_pos]
  ring_nf
  rfl

中文:
定理 to实数_coe_eq_self_iff
  条件: {θ : 实数}
  结论: (θ : Angle).to实数 = θ ↔ -π < θ ∧ θ <= π
  证明: by
  rw [toReal_coe]; rw [toIocMod_eq_self two_pi_pos]
  ring_nf
  rfl

Depends on / 依赖: ring_nf, toIocMod_eq_self, toReal_coe, two_pi_pos
-/
theorem toReal_coe_eq_self_iff {θ : Real} : (θ : Angle).toReal = θ ↔ -π < θ ∧ θ <= π := by
  rw [toReal_coe]; rw [toIocMod_eq_self two_pi_pos]
  ring_nf
  rfl

/--
theorem `toReal_coe_eq_self_iff_mem_Ioc` / 定理 `toReal_coe_eq_self_iff_mem_Ioc`

English:
theorem toReal_coe_eq_self_iff_mem_Ioc
  given: {θ : Real}
  statement: (θ : Angle).toReal = θ ↔ θ in Set.Ioc (-π) π
  proof: by
  rw [toReal_coe_eq_self_iff]; rw [← Set.mem_Ioc]

@[grind inj]

中文:
定理 to实数_coe_eq_self_iff_mem_Ioc
  条件: {θ : 实数}
  结论: (θ : Angle).to实数 = θ ↔ θ in 集合.左开右闭区间 (-π) π
  证明: by
  rw [toReal_coe_eq_self_iff]; rw [← Set.mem_Ioc]

@[grind inj]

Depends on / 依赖: Set.mem_Ioc, mem_Ioc, toReal_coe_eq_self_iff
-/
theorem toReal_coe_eq_self_iff_mem_Ioc {θ : Real} : (θ : Angle).toReal = θ ↔ θ in Set.Ioc (-π) π := by
  rw [toReal_coe_eq_self_iff]; rw [← Set.mem_Ioc]

@[grind inj]
/--
theorem `toReal_injective` / 定理 `toReal_injective`

English:
theorem toReal_injective
  statement: Function.Injective toReal
  proof: by
  intro θ ψ h
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  simpa [toReal_coe, toIocMod_eq_toIocMod, zsmul_eq_mul, mul_comm _ (2 * π), ←
    angle_eq_iff_two_pi_dvd_sub, eq_comm] using h

@[simp]

中文:
定理 to实数_injective
  结论: 函数.单射 to实数
  证明: by
  intro θ ψ h
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  simpa [toReal_coe, toIocMod_eq_toIocMod, zsmul_eq_mul, mul_comm _ (2 * π), ←
    angle_eq_iff_two_pi_dvd_sub, eq_comm] using h

@[simp]

Depends on / 依赖: Real.Angle.induction_on, angle_eq_iff_two_pi_dvd_sub, eq_comm, induction_on, mul_comm, toIocMod_eq_toIocMod, toReal_coe, zsmul_eq_mul
-/
theorem toReal_injective : Function.Injective toReal := by
  intro θ ψ h
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  simpa [toReal_coe, toIocMod_eq_toIocMod, zsmul_eq_mul, mul_comm _ (2 * π), ←
    angle_eq_iff_two_pi_dvd_sub, eq_comm] using h

@[simp]
/--
theorem `toReal_inj` / 定理 `toReal_inj`

English:
theorem toReal_inj
  given: {θ ψ : Angle}
  statement: θ.toReal = ψ.toReal ↔ θ = ψ
  proof: toReal_injective.eq_iff

@[simp, grind =]

中文:
定理 to实数_inj
  条件: {θ ψ : Angle}
  结论: θ.to实数 = ψ.to实数 ↔ θ = ψ
  证明: toReal_injective.eq_iff

@[simp, grind =]

Depends on / 依赖: eq_iff, toReal_injective, toReal_injective.eq_iff
-/
theorem toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ θ = ψ :=
  toReal_injective.eq_iff

@[simp, grind =]
/--
theorem `coe_toReal` / 定理 `coe_toReal`

English:
theorem coe_toReal
  given: (θ : Angle)
  statement: (θ.toReal : Angle) = θ
  proof: by
  induction θ using Real.Angle.induction_on
  exact coe_toIocMod _ _

中文:
定理 coe_to实数
  条件: (θ : Angle)
  结论: (θ.to实数 : Angle) = θ
  证明: by
  induction θ using Real.Angle.induction_on
  exact coe_toIocMod _ _

Depends on / 依赖: Real.Angle.induction_on, coe_toIocMod, induction_on
-/
theorem coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ := by
  induction θ using Real.Angle.induction_on
  exact coe_toIocMod _ _

/--
theorem `neg_pi_lt_toReal` / 定理 `neg_pi_lt_toReal`

English:
theorem neg_pi_lt_toReal
  given: (θ : Angle)
  statement: -π < θ.toReal
  proof: by
  induction θ using Real.Angle.induction_on
  exact left_lt_toIocMod _ _ _

中文:
定理 neg_pi_lt_to实数
  条件: (θ : Angle)
  结论: -π < θ.to实数
  证明: by
  induction θ using Real.Angle.induction_on
  exact left_lt_toIocMod _ _ _

Depends on / 依赖: Real.Angle.induction_on, induction_on, left_lt_toIocMod
-/
theorem neg_pi_lt_toReal (θ : Angle) : -π < θ.toReal := by
  induction θ using Real.Angle.induction_on
  exact left_lt_toIocMod _ _ _

/--
theorem `toReal_le_pi` / 定理 `toReal_le_pi`

English:
theorem toReal_le_pi
  given: (θ : Angle)
  statement: θ.toReal <= π
  proof: by
  induction θ using Real.Angle.induction_on
  convert! toIocMod_le_right two_pi_pos _ _
  ring

中文:
定理 to实数_le_pi
  条件: (θ : Angle)
  结论: θ.to实数 <= π
  证明: by
  induction θ using Real.Angle.induction_on
  convert! toIocMod_le_right two_pi_pos _ _
  ring

Depends on / 依赖: Real.Angle.induction_on, convert, induction_on, toIocMod_le_right, two_pi_pos
-/
theorem toReal_le_pi (θ : Angle) : θ.toReal <= π := by
  induction θ using Real.Angle.induction_on
  convert! toIocMod_le_right two_pi_pos _ _
  ring

/--
theorem `abs_toReal_le_pi` / 定理 `abs_toReal_le_pi`

English:
theorem abs_toReal_le_pi
  given: (θ : Angle)
  statement: |θ.toReal| <= π
  proof: abs_le.2 ⟨(neg_pi_lt_toReal _).le, toReal_le_pi _⟩

中文:
定理 abs_to实数_le_pi
  条件: (θ : Angle)
  结论: |θ.to实数| <= π
  证明: abs_le.2 ⟨(neg_pi_lt_toReal _).le, toReal_le_pi _⟩

Depends on / 依赖: abs_le, neg_pi_lt_toReal, toReal_le_pi
-/
theorem abs_toReal_le_pi (θ : Angle) : |θ.toReal| <= π :=
  abs_le.2 ⟨(neg_pi_lt_toReal _).le, toReal_le_pi _⟩

/--
theorem `toReal_mem_Ioc` / 定理 `toReal_mem_Ioc`

English:
theorem toReal_mem_Ioc
  given: (θ : Angle)
  statement: θ.toReal in Set.Ioc (-π) π
  proof: ⟨neg_pi_lt_toReal _, toReal_le_pi _⟩

@[simp]

中文:
定理 to实数_mem_Ioc
  条件: (θ : Angle)
  结论: θ.to实数 in 集合.左开右闭区间 (-π) π
  证明: ⟨neg_pi_lt_toReal _, toReal_le_pi _⟩

@[simp]

Depends on / 依赖: neg_pi_lt_toReal, toReal_le_pi
-/
theorem toReal_mem_Ioc (θ : Angle) : θ.toReal in Set.Ioc (-π) π :=
  ⟨neg_pi_lt_toReal _, toReal_le_pi _⟩

@[simp]
/--
theorem `toIocMod_toReal` / 定理 `toIocMod_toReal`

English:
theorem toIocMod_toReal
  given: (θ : Angle)
  statement: toIocMod two_pi_pos (-π) θ.toReal = θ.toReal
  proof: by
  induction θ using Real.Angle.induction_on
  rw [toReal_coe]
  exact toIocMod_toIocMod _ _ _ _

@[simp, grind =]

中文:
定理 toIocMod_to实数
  条件: (θ : Angle)
  结论: toIocMod two_pi_pos (-π) θ.to实数 = θ.to实数
  证明: by
  induction θ using Real.Angle.induction_on
  rw [toReal_coe]
  exact toIocMod_toIocMod _ _ _ _

@[simp, grind =]

Depends on / 依赖: Real.Angle.induction_on, induction_on, toIocMod_toIocMod, toReal_coe
-/
theorem toIocMod_toReal (θ : Angle) : toIocMod two_pi_pos (-π) θ.toReal = θ.toReal := by
  induction θ using Real.Angle.induction_on
  rw [toReal_coe]
  exact toIocMod_toIocMod _ _ _ _

@[simp, grind =]
/--
theorem `toReal_zero` / 定理 `toReal_zero`

English:
theorem toReal_zero
  statement: (0 : Angle).toReal = 0
  proof: by
  rw [← coe_zero]; rw [toReal_coe_eq_self_iff]
  exact ⟨Left.neg_neg_iff.2 Real.pi_pos, Real.pi_pos.le⟩

@[simp]

中文:
定理 to实数_zero
  结论: (0 : Angle).to实数 = 0
  证明: by
  rw [← coe_zero]; rw [toReal_coe_eq_self_iff]
  exact ⟨Left.neg_neg_iff.2 Real.pi_pos, Real.pi_pos.le⟩

@[simp]

Depends on / 依赖: Left.neg_neg_iff, Real.pi_pos, Real.pi_pos.le, coe_zero, neg_neg_iff, pi_pos, toReal_coe_eq_self_iff
-/
theorem toReal_zero : (0 : Angle).toReal = 0 := by
  rw [← coe_zero]; rw [toReal_coe_eq_self_iff]
  exact ⟨Left.neg_neg_iff.2 Real.pi_pos, Real.pi_pos.le⟩

@[simp]
/--
theorem `toReal_eq_zero_iff` / 定理 `toReal_eq_zero_iff`

English:
theorem toReal_eq_zero_iff
  given: {θ : Angle}
  statement: θ.toReal = 0 ↔ θ = 0
  proof: by
  nth_rw 1 [← toReal_zero]
  exact toReal_inj

@[simp, grind =]

中文:
定理 to实数_eq_zero_iff
  条件: {θ : Angle}
  结论: θ.to实数 = 0 ↔ θ = 0
  证明: by
  nth_rw 1 [← toReal_zero]
  exact toReal_inj

@[simp, grind =]

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_iso, nth_rw, of_iso, preLeftIso, toReal_inj, toReal_zero
-/
theorem toReal_eq_zero_iff {θ : Angle} : θ.toReal = 0 ↔ θ = 0 := by
  nth_rw 1 [← toReal_zero]
  exact toReal_inj

@[simp, grind =]
/--
theorem `toReal_pi` / 定理 `toReal_pi`

English:
theorem toReal_pi
  statement: (π : Angle).toReal = π
  proof: by
  rw [toReal_coe_eq_self_iff]
  exact ⟨Left.neg_lt_self Real.pi_pos, le_refl _⟩

@[simp]

中文:
定理 to实数_pi
  结论: (π : Angle).to实数 = π
  证明: by
  rw [toReal_coe_eq_self_iff]
  exact ⟨Left.neg_lt_self Real.pi_pos, le_refl _⟩

@[simp]

Depends on / 依赖: Functor, Functor.Full.of_iso, Left.neg_lt_self, Real.pi_pos, le_refl, neg_lt_self, of_iso, pi_pos, preLeftIso, toReal_coe_eq_self_iff
-/
theorem toReal_pi : (π : Angle).toReal = π := by
  rw [toReal_coe_eq_self_iff]
  exact ⟨Left.neg_lt_self Real.pi_pos, le_refl _⟩

@[simp]
/--
theorem `toReal_eq_pi_iff` / 定理 `toReal_eq_pi_iff`

English:
theorem toReal_eq_pi_iff
  given: {θ : Angle}
  statement: θ.toReal = π ↔ θ = π
  proof: by rw [← toReal_inj, toReal_pi]

中文:
定理 to实数_eq_pi_iff
  条件: {θ : Angle}
  结论: θ.to实数 = π ↔ θ = π
  证明: by rw [← toReal_inj, toReal_pi]

Depends on / 依赖: Functor, Functor.essSurj_of_iso, essSurj_of_iso, preLeftIso, toReal_inj, toReal_pi
-/
theorem toReal_eq_pi_iff {θ : Angle} : θ.toReal = π ↔ θ = π := by rw [← toReal_inj, toReal_pi]

/--
lemma `toReal_neg_eq_neg_toReal_iff` / 引理 `toReal_neg_eq_neg_toReal_iff`

English:
lemma toReal_neg_eq_neg_toReal_iff
  given: {θ : Angle}
  statement: (-θ).toReal = -(θ.toReal) ↔ θ != π
  proof: by
  nth_rw 1 [← coe_toReal θ, ← coe_neg, toReal_coe_eq_self_iff]
  constructor
  · rintro ⟨h, h'⟩ rfl
    simp at h
  · intro h
    rw [neg_lt_neg_iff]
    have h' : θ.toReal != π := by simp [h]
    exact ⟨(toReal_le_pi θ).lt_of_ne h', by linarith [neg_pi_lt_toReal θ]⟩

中文:
引理 to实数_neg_eq_neg_to实数_iff
  条件: {θ : Angle}
  结论: (-θ).to实数 = -(θ.to实数) ↔ θ != π
  证明: by
  nth_rw 1 [← coe_toReal θ, ← coe_neg, toReal_coe_eq_self_iff]
  constructor
  · rintro ⟨h, h'⟩ rfl
    simp at h
  · intro h
    rw [neg_lt_neg_iff]
    have h' : θ.toReal != π := by simp [h]
    exact ⟨(toReal_le_pi θ).lt_of_ne h', by linarith [neg_pi_lt_toReal θ]⟩

Depends on / 依赖: coe_neg, coe_toReal, lt_of_ne, neg_lt_neg_iff, neg_pi_lt_toReal, nth_rw, toReal, toReal_coe_eq_self_iff, toReal_le_pi
-/
lemma toReal_neg_eq_neg_toReal_iff {θ : Angle} : (-θ).toReal = -(θ.toReal) ↔ θ != π := by
  nth_rw 1 [← coe_toReal θ, ← coe_neg, toReal_coe_eq_self_iff]
  constructor
  · rintro ⟨h, h'⟩ rfl
    simp at h
  · intro h
    rw [neg_lt_neg_iff]
    have h' : θ.toReal != π := by simp [h]
    exact ⟨(toReal_le_pi θ).lt_of_ne h', by linarith [neg_pi_lt_toReal θ]⟩

/--
lemma `abs_toReal_neg` / 引理 `abs_toReal_neg`

English:
lemma abs_toReal_neg
  given: (θ : Angle)
  statement: |(-θ).toReal| = |θ.toReal|
  proof: by
  rcases eq_or_ne θ π with rfl | h
  · simp
  · simp [toReal_neg_eq_neg_toReal_iff.2 h]

中文:
引理 abs_to实数_neg
  条件: (θ : Angle)
  结论: |(-θ).to实数| = |θ.to实数|
  证明: by
  rcases eq_or_ne θ π with rfl | h
  · simp
  · simp [toReal_neg_eq_neg_toReal_iff.2 h]
-/
@[simp] lemma abs_toReal_neg (θ : Angle) : |(-θ).toReal| = |θ.toReal| := by
  rcases eq_or_ne θ π with rfl | h
  · simp
  · simp [toReal_neg_eq_neg_toReal_iff.2 h]

/--
theorem `pi_ne_zero` / 定理 `pi_ne_zero`

English:
theorem pi_ne_zero
  statement: (π : Angle) != 0
  proof: by
  rw [← toReal_injective.ne_iff]; rw [toReal_pi]; rw [toReal_zero]
  exact Real.pi_ne_zero

@[simp, grind =]

中文:
定理 pi_ne_zero
  结论: (π : Angle) != 0
  证明: by
  rw [← toReal_injective.ne_iff]; rw [toReal_pi]; rw [toReal_zero]
  exact Real.pi_ne_zero

@[simp, grind =]

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_iso, Real.pi_ne_zero, ne_iff, of_iso, pi_ne_zero, postIso, toReal_injective, toReal_injective.ne_iff, toReal_pi, toReal_zero
-/
theorem pi_ne_zero : (π : Angle) != 0 := by
  rw [← toReal_injective.ne_iff]; rw [toReal_pi]; rw [toReal_zero]
  exact Real.pi_ne_zero

@[simp, grind =]
/--
theorem `toReal_pi_div_two` / 定理 `toReal_pi_div_two`

English:
theorem toReal_pi_div_two
  statement: ((π / 2 : Real) : Angle).toReal = π / 2
  proof: toReal_coe_eq_self_iff.2 by constructor <;> linarith [pi_pos]

@[simp]

中文:
定理 to实数_pi_div_two
  结论: ((π / 2 : 实数) : Angle).to实数 = π / 2
  证明: toReal_coe_eq_self_iff.2 by constructor <;> linarith [pi_pos]

@[simp]

Depends on / 依赖: Functor, Functor.Full.of_iso, of_iso, pi_pos, postIso, toReal_coe_eq_self_iff
-/
theorem toReal_pi_div_two : ((π / 2 : Real) : Angle).toReal = π / 2 :=
toReal_coe_eq_self_iff.2 by constructor <;> linarith [pi_pos]

@[simp]
/--
theorem `toReal_eq_pi_div_two_iff` / 定理 `toReal_eq_pi_div_two_iff`

English:
theorem toReal_eq_pi_div_two_iff
  given: {θ : Angle}
  statement: θ.toReal = π / 2 ↔ θ = (π / 2 : Real)
  proof: by
  rw [← toReal_inj]; rw [toReal_pi_div_two]

@[simp, grind =]

中文:
定理 to实数_eq_pi_div_two_iff
  条件: {θ : Angle}
  结论: θ.to实数 = π / 2 ↔ θ = (π / 2 : 实数)
  证明: by
  rw [← toReal_inj]; rw [toReal_pi_div_two]

@[simp, grind =]

Depends on / 依赖: Functor, Functor.essSurj_of_iso, essSurj_of_iso, postIso, toReal_inj, toReal_pi_div_two
-/
theorem toReal_eq_pi_div_two_iff {θ : Angle} : θ.toReal = π / 2 ↔ θ = (π / 2 : Real) := by
  rw [← toReal_inj]; rw [toReal_pi_div_two]

@[simp, grind =]
/--
theorem `toReal_neg_pi_div_two` / 定理 `toReal_neg_pi_div_two`

English:
theorem toReal_neg_pi_div_two
  statement: ((-π / 2 : Real) : Angle).toReal = -π / 2
  proof: toReal_coe_eq_self_iff.2 by constructor <;> linarith [pi_pos]

@[simp]

中文:
定理 to实数_neg_pi_div_two
  结论: ((-π / 2 : 实数) : Angle).to实数 = -π / 2
  证明: toReal_coe_eq_self_iff.2 by constructor <;> linarith [pi_pos]

@[simp]

Depends on / 依赖: pi_pos, toReal_coe_eq_self_iff
-/
theorem toReal_neg_pi_div_two : ((-π / 2 : Real) : Angle).toReal = -π / 2 :=
toReal_coe_eq_self_iff.2 by constructor <;> linarith [pi_pos]

@[simp]
/--
theorem `toReal_eq_neg_pi_div_two_iff` / 定理 `toReal_eq_neg_pi_div_two_iff`

English:
theorem toReal_eq_neg_pi_div_two_iff
  given: {θ : Angle}
  statement: θ.toReal = -π / 2 ↔ θ = (-π / 2 : Real)
  proof: by
  rw [← toReal_inj]; rw [toReal_neg_pi_div_two]

中文:
定理 to实数_eq_neg_pi_div_two_iff
  条件: {θ : Angle}
  结论: θ.to实数 = -π / 2 ↔ θ = (-π / 2 : 实数)
  证明: by
  rw [← toReal_inj]; rw [toReal_neg_pi_div_two]

Depends on / 依赖: toReal_inj, toReal_neg_pi_div_two
-/
theorem toReal_eq_neg_pi_div_two_iff {θ : Angle} : θ.toReal = -π / 2 ↔ θ = (-π / 2 : Real) := by
  rw [← toReal_inj]; rw [toReal_neg_pi_div_two]

/--
theorem `pi_div_two_ne_zero` / 定理 `pi_div_two_ne_zero`

English:
theorem pi_div_two_ne_zero
  statement: ((π / 2 : Real) : Angle) != 0
  proof: by
  rw [← toReal_injective.ne_iff]; rw [toReal_pi_div_two]; rw [toReal_zero]
  exact div_ne_zero Real.pi_ne_zero two_ne_zero

中文:
定理 pi_div_two_ne_zero
  结论: ((π / 2 : 实数) : Angle) != 0
  证明: by
  rw [← toReal_injective.ne_iff]; rw [toReal_pi_div_two]; rw [toReal_zero]
  exact div_ne_zero Real.pi_ne_zero two_ne_zero

Depends on / 依赖: Real.pi_ne_zero, div_ne_zero, ne_iff, pi_ne_zero, toReal_injective, toReal_injective.ne_iff, toReal_pi_div_two, toReal_zero, two_ne_zero
-/
theorem pi_div_two_ne_zero : ((π / 2 : Real) : Angle) != 0 := by
  rw [← toReal_injective.ne_iff]; rw [toReal_pi_div_two]; rw [toReal_zero]
  exact div_ne_zero Real.pi_ne_zero two_ne_zero

/--
theorem `neg_pi_div_two_ne_zero` / 定理 `neg_pi_div_two_ne_zero`

English:
theorem neg_pi_div_two_ne_zero
  statement: ((-π / 2 : Real) : Angle) != 0
  proof: by
  rw [← toReal_injective.ne_iff]; rw [toReal_neg_pi_div_two]; rw [toReal_zero]
  exact div_ne_zero (neg_ne_zero.2 Real.pi_ne_zero) two_ne_zero

中文:
定理 neg_pi_div_two_ne_zero
  结论: ((-π / 2 : 实数) : Angle) != 0
  证明: by
  rw [← toReal_injective.ne_iff]; rw [toReal_neg_pi_div_two]; rw [toReal_zero]
  exact div_ne_zero (neg_ne_zero.2 Real.pi_ne_zero) two_ne_zero

Depends on / 依赖: Real.pi_ne_zero, div_ne_zero, ne_iff, neg_ne_zero, pi_ne_zero, toReal_injective, toReal_injective.ne_iff, toReal_neg_pi_div_two, toReal_zero, two_ne_zero
-/
theorem neg_pi_div_two_ne_zero : ((-π / 2 : Real) : Angle) != 0 := by
  rw [← toReal_injective.ne_iff]; rw [toReal_neg_pi_div_two]; rw [toReal_zero]
  exact div_ne_zero (neg_ne_zero.2 Real.pi_ne_zero) two_ne_zero

/--
theorem `abs_toReal_coe_eq_self_iff` / 定理 `abs_toReal_coe_eq_self_iff`

English:
theorem abs_toReal_coe_eq_self_iff
  given: {θ : Real}
  statement: |(θ : Angle).toReal| = θ ↔ 0 <= θ ∧ θ <= π
  proof: ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h =>
    (toReal_coe_eq_self_iff.2 ⟨(Left.neg_neg_iff.2 Real.pi_pos).trans_le h.1, h.2⟩).symm ▸
      abs_eq_self.2 h.1⟩

中文:
定理 abs_to实数_coe_eq_self_iff
  条件: {θ : 实数}
  结论: |(θ : Angle).to实数| = θ ↔ 0 <= θ ∧ θ <= π
  证明: ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h =>
    (toReal_coe_eq_self_iff.2 ⟨(Left.neg_neg_iff.2 Real.pi_pos).trans_le h.1, h.2⟩).symm ▸
      abs_eq_self.2 h.1⟩

Depends on / 依赖: Left.neg_neg_iff, Real.pi_pos, abs_eq_self, abs_nonneg, abs_toReal_le_pi, neg_neg_iff, pi_pos, toReal_coe_eq_self_iff, trans_le
-/
theorem abs_toReal_coe_eq_self_iff {θ : Real} : |(θ : Angle).toReal| = θ ↔ 0 <= θ ∧ θ <= π :=
  ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h =>
    (toReal_coe_eq_self_iff.2 ⟨(Left.neg_neg_iff.2 Real.pi_pos).trans_le h.1, h.2⟩).symm ▸
      abs_eq_self.2 h.1⟩

/--
theorem `abs_toReal_neg_coe_eq_self_iff` / 定理 `abs_toReal_neg_coe_eq_self_iff`

English:
theorem abs_toReal_neg_coe_eq_self_iff
  given: {θ : Real}
  statement: |(-θ : Angle).toReal| = θ ↔ 0 <= θ ∧ θ <= π
  proof: by
  refine ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h => ?_⟩
  by_cases hnegpi : θ = π; · simp [hnegpi, Real.pi_pos.le]
  rw [← coe_neg]; rw [toReal_coe_eq_self_iff.2
      ⟨neg_lt_neg (lt_of_le_of_ne h.2 hnegpi)]; rw [(neg_nonpos.2 h.1).trans Real.pi_pos.le⟩]; rw [abs_neg]; rw [abs_eq_self.2 h.1]

中文:
定理 abs_to实数_neg_coe_eq_self_iff
  条件: {θ : 实数}
  结论: |(-θ : Angle).to实数| = θ ↔ 0 <= θ ∧ θ <= π
  证明: by
  refine ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h => ?_⟩
  by_cases hnegpi : θ = π; · simp [hnegpi, Real.pi_pos.le]
  rw [← coe_neg]; rw [toReal_coe_eq_self_iff.2
      ⟨neg_lt_neg (lt_of_le_of_ne h.2 hnegpi)]; rw [(neg_nonpos.2 h.1).trans Real.pi_pos.le⟩]; rw [abs_neg]; rw [abs_eq_self.2 h.1]

Depends on / 依赖: Real.pi_pos.le, abs_eq_self, abs_neg, abs_nonneg, abs_toReal_le_pi, coe_neg, hnegpi, lt_of_le_of_ne, neg_lt_neg, neg_nonpos, pi_pos, toReal_coe_eq_self_iff
-/
theorem abs_toReal_neg_coe_eq_self_iff {θ : Real} : |(-θ : Angle).toReal| = θ ↔ 0 <= θ ∧ θ <= π := by
  refine ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h => ?_⟩
  by_cases hnegpi : θ = π; · simp [hnegpi, Real.pi_pos.le]
  rw [← coe_neg]; rw [toReal_coe_eq_self_iff.2
      ⟨neg_lt_neg (lt_of_le_of_ne h.2 hnegpi)]; rw [(neg_nonpos.2 h.1).trans Real.pi_pos.le⟩]; rw [abs_neg]; rw [abs_eq_self.2 h.1]

/--
theorem `abs_toReal_eq_pi_div_two_iff` / 定理 `abs_toReal_eq_pi_div_two_iff`

English:
theorem abs_toReal_eq_pi_div_two_iff
  given: {θ : Angle}
  proof: by
  rw [abs_eq (div_nonneg Real.pi_pos.le two_pos.le)]; rw [← neg_div]; rw [toReal_eq_pi_div_two_iff]; rw [toReal_eq_neg_pi_div_two_iff]

中文:
定理 abs_to实数_eq_pi_div_two_iff
  条件: {θ : Angle}
  证明: by
  rw [abs_eq (div_nonneg Real.pi_pos.le two_pos.le)]; rw [← neg_div]; rw [toReal_eq_pi_div_two_iff]; rw [toReal_eq_neg_pi_div_two_iff]

Depends on / 依赖: Real.pi_pos.le, abs_eq, div_nonneg, neg_div, pi_pos, toReal_eq_neg_pi_div_two_iff, toReal_eq_pi_div_two_iff, two_pos, two_pos.le
-/
theorem abs_toReal_eq_pi_div_two_iff {θ : Angle} :
    |θ.toReal| = π / 2 ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real) := by
  rw [abs_eq (div_nonneg Real.pi_pos.le two_pos.le)]; rw [← neg_div]; rw [toReal_eq_pi_div_two_iff]; rw [toReal_eq_neg_pi_div_two_iff]

/--
theorem `nsmul_toReal_eq_mul` / 定理 `nsmul_toReal_eq_mul`

English:
theorem nsmul_toReal_eq_mul
  given: {n : Nat} (h : n != 0) {θ : Angle}
  proof: by
  nth_rw 1 [← coe_toReal θ]
  have h' : 0 < (n : Real) := mod_cast Nat.pos_of_ne_zero h
  rw [← coe_nsmul]; rw [nsmul_eq_mul]; rw [toReal_coe_eq_self_iff]; rw [Set.mem_Ioc]; rw [div_lt_iff₀' h']; rw [le_div_iff₀' h']

中文:
定理 nsmul_to实数_eq_mul
  条件: {n : 自然数} (h : n != 0) {θ : Angle}
  证明: by
  nth_rw 1 [← coe_toReal θ]
  have h' : 0 < (n : Real) := mod_cast Nat.pos_of_ne_zero h
  rw [← coe_nsmul]; rw [nsmul_eq_mul]; rw [toReal_coe_eq_self_iff]; rw [Set.mem_Ioc]; rw [div_lt_iff₀' h']; rw [le_div_iff₀' h']

Depends on / 依赖: Nat.pos_of_ne_zero, Set.mem_Ioc, coe_nsmul, coe_toReal, mem_Ioc, mod_cast, nsmul_eq_mul, nth_rw, pos_of_ne_zero, toReal_coe_eq_self_iff
-/
theorem nsmul_toReal_eq_mul {n : Nat} (h : n != 0) {θ : Angle} :
    (n • θ).toReal = n * θ.toReal ↔ θ.toReal in Set.Ioc (-π / n) (π / n) := by
  nth_rw 1 [← coe_toReal θ]
  have h' : 0 < (n : Real) := mod_cast Nat.pos_of_ne_zero h
  rw [← coe_nsmul]; rw [nsmul_eq_mul]; rw [toReal_coe_eq_self_iff]; rw [Set.mem_Ioc]; rw [div_lt_iff₀' h']; rw [le_div_iff₀' h']

/--
theorem `two_nsmul_toReal_eq_two_mul` / 定理 `two_nsmul_toReal_eq_two_mul`

English:
theorem two_nsmul_toReal_eq_two_mul
  given: {θ : Angle}
  proof: mod_cast nsmul_toReal_eq_mul two_ne_zero

中文:
定理 two_nsmul_to实数_eq_two_mul
  条件: {θ : Angle}
  证明: mod_cast nsmul_toReal_eq_mul two_ne_zero

Depends on / 依赖: mod_cast, nsmul_toReal_eq_mul, two_ne_zero
-/
theorem two_nsmul_toReal_eq_two_mul {θ : Angle} :
    ((2 : Nat) • θ).toReal = 2 * θ.toReal ↔ θ.toReal in Set.Ioc (-π / 2) (π / 2) :=
  mod_cast nsmul_toReal_eq_mul two_ne_zero

/--
theorem `two_zsmul_toReal_eq_two_mul` / 定理 `two_zsmul_toReal_eq_two_mul`

English:
theorem two_zsmul_toReal_eq_two_mul
  given: {θ : Angle}
  proof: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_toReal_eq_two_mul]

中文:
定理 two_zsmul_to实数_eq_two_mul
  条件: {θ : Angle}
  证明: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_toReal_eq_two_mul]

Depends on / 依赖: two_nsmul, two_nsmul_toReal_eq_two_mul, two_zsmul
-/
theorem two_zsmul_toReal_eq_two_mul {θ : Angle} :
    ((2 : Int) • θ).toReal = 2 * θ.toReal ↔ θ.toReal in Set.Ioc (-π / 2) (π / 2) := by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_toReal_eq_two_mul]

/--
theorem `toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff` / 定理 `toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff`

English:
theorem toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff
  given: {θ : Real} {k : Int}
  proof: by
  rw [← sub_zero (θ : Angle)]; rw [← zsmul_zero k]; rw [← coe_two_pi]; rw [← coe_zsmul]; rw [← coe_sub]; rw [zsmul_eq_mul]; rw [←
    mul_assoc]; rw [mul_comm (k : Real)]; rw [toReal_coe_eq_self_iff]; rw [Set.mem_Ioc]
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, by linarith⟩⟩

中文:
定理 to实数_coe_eq_self_sub_two_mul_int_mul_pi_iff
  条件: {θ : 实数} {k : 整数}
  证明: by
  rw [← sub_zero (θ : Angle)]; rw [← zsmul_zero k]; rw [← coe_two_pi]; rw [← coe_zsmul]; rw [← coe_sub]; rw [zsmul_eq_mul]; rw [←
    mul_assoc]; rw [mul_comm (k : Real)]; rw [toReal_coe_eq_self_iff]; rw [Set.mem_Ioc]
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, by linarith⟩⟩

Depends on / 依赖: Set.mem_Ioc, coe_sub, coe_two_pi, coe_zsmul, mem_Ioc, mul_assoc, mul_comm, sub_zero, toReal_coe_eq_self_iff, zsmul_eq_mul, zsmul_zero
-/
theorem toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff {θ : Real} {k : Int} :
    (θ : Angle).toReal = θ - 2 * k * π ↔ θ in Set.Ioc ((2 * k - 1 : Real) * π) ((2 * k + 1) * π) := by
  rw [← sub_zero (θ : Angle)]; rw [← zsmul_zero k]; rw [← coe_two_pi]; rw [← coe_zsmul]; rw [← coe_sub]; rw [zsmul_eq_mul]; rw [←
    mul_assoc]; rw [mul_comm (k : Real)]; rw [toReal_coe_eq_self_iff]; rw [Set.mem_Ioc]
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, by linarith⟩⟩

/--
theorem `toReal_coe_eq_self_sub_two_pi_iff` / 定理 `toReal_coe_eq_self_sub_two_pi_iff`

English:
theorem toReal_coe_eq_self_sub_two_pi_iff
  given: {θ : Real}
  proof: by
  convert! @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ 1 <;> norm_num

中文:
定理 to实数_coe_eq_self_sub_two_pi_iff
  条件: {θ : 实数}
  证明: by
  convert! @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ 1 <;> norm_num

Depends on / 依赖: convert, toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff
-/
theorem toReal_coe_eq_self_sub_two_pi_iff {θ : Real} :
    (θ : Angle).toReal = θ - 2 * π ↔ θ in Set.Ioc π (3 * π) := by
  convert! @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ 1 <;> norm_num

/--
theorem `toReal_coe_eq_self_add_two_pi_iff` / 定理 `toReal_coe_eq_self_add_two_pi_iff`

English:
theorem toReal_coe_eq_self_add_two_pi_iff
  given: {θ : Real}
  proof: by
  convert! @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ (-1) using 2 <;> norm_num

中文:
定理 to实数_coe_eq_self_add_two_pi_iff
  条件: {θ : 实数}
  证明: by
  convert! @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ (-1) using 2 <;> norm_num

Depends on / 依赖: convert, toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff
-/
theorem toReal_coe_eq_self_add_two_pi_iff {θ : Real} :
    (θ : Angle).toReal = θ + 2 * π ↔ θ in Set.Ioc (-3 * π) (-π) := by
  convert! @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ (-1) using 2 <;> norm_num

/--
theorem `two_nsmul_toReal_eq_two_mul_sub_two_pi` / 定理 `two_nsmul_toReal_eq_two_mul_sub_two_pi`

English:
theorem two_nsmul_toReal_eq_two_mul_sub_two_pi
  given: {θ : Angle}
  proof: by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul]; rw [two_nsmul]; rw [← two_mul]; rw [toReal_coe_eq_self_sub_two_pi_iff]; rw [Set.mem_Ioc]
  exact
    ⟨fun h => by linarith, fun h =>
      ⟨(div_lt_iff₀' (zero_lt_two' Real)).1 h, by linarith [pi_pos, toReal_le_pi θ]⟩⟩

中文:
定理 two_nsmul_to实数_eq_two_mul_sub_two_pi
  条件: {θ : Angle}
  证明: by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul]; rw [two_nsmul]; rw [← two_mul]; rw [toReal_coe_eq_self_sub_two_pi_iff]; rw [Set.mem_Ioc]
  exact
    ⟨fun h => by linarith, fun h =>
      ⟨(div_lt_iff₀' (zero_lt_two' Real)).1 h, by linarith [pi_pos, toReal_le_pi θ]⟩⟩

Depends on / 依赖: Set.mem_Ioc, coe_nsmul, coe_toReal, mem_Ioc, nth_rw, pi_pos, toReal_coe_eq_self_sub_two_pi_iff, toReal_le_pi, two_mul, two_nsmul, zero_lt_two
-/
theorem two_nsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} :
    ((2 : Nat) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal := by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul]; rw [two_nsmul]; rw [← two_mul]; rw [toReal_coe_eq_self_sub_two_pi_iff]; rw [Set.mem_Ioc]
  exact
    ⟨fun h => by linarith, fun h =>
      ⟨(div_lt_iff₀' (zero_lt_two' Real)).1 h, by linarith [pi_pos, toReal_le_pi θ]⟩⟩

/--
theorem `two_zsmul_toReal_eq_two_mul_sub_two_pi` / 定理 `two_zsmul_toReal_eq_two_mul_sub_two_pi`

English:
theorem two_zsmul_toReal_eq_two_mul_sub_two_pi
  given: {θ : Angle}
  proof: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_toReal_eq_two_mul_sub_two_pi]

中文:
定理 two_zsmul_to实数_eq_two_mul_sub_two_pi
  条件: {θ : Angle}
  证明: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_toReal_eq_two_mul_sub_two_pi]

Depends on / 依赖: two_nsmul, two_nsmul_toReal_eq_two_mul_sub_two_pi, two_zsmul
-/
theorem two_zsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} :
    ((2 : Int) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal := by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_toReal_eq_two_mul_sub_two_pi]

/--
theorem `two_nsmul_toReal_eq_two_mul_add_two_pi` / 定理 `two_nsmul_toReal_eq_two_mul_add_two_pi`

English:
theorem two_nsmul_toReal_eq_two_mul_add_two_pi
  given: {θ : Angle}
  proof: by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul]; rw [two_nsmul]; rw [← two_mul]; rw [toReal_coe_eq_self_add_two_pi_iff]; rw [Set.mem_Ioc]
  refine
    ⟨fun h => by linarith, fun h =>
      ⟨by linarith [pi_pos, neg_pi_lt_toReal θ], (le_div_iff₀' (zero_lt_two' Real)).1 h⟩⟩

中文:
定理 two_nsmul_to实数_eq_two_mul_add_two_pi
  条件: {θ : Angle}
  证明: by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul]; rw [two_nsmul]; rw [← two_mul]; rw [toReal_coe_eq_self_add_two_pi_iff]; rw [Set.mem_Ioc]
  refine
    ⟨fun h => by linarith, fun h =>
      ⟨by linarith [pi_pos, neg_pi_lt_toReal θ], (le_div_iff₀' (zero_lt_two' Real)).1 h⟩⟩

Depends on / 依赖: Set.mem_Ioc, coe_nsmul, coe_toReal, mem_Ioc, neg_pi_lt_toReal, nth_rw, pi_pos, toReal_coe_eq_self_add_two_pi_iff, two_mul, two_nsmul, zero_lt_two
-/
theorem two_nsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} :
    ((2 : Nat) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal <= -π / 2 := by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul]; rw [two_nsmul]; rw [← two_mul]; rw [toReal_coe_eq_self_add_two_pi_iff]; rw [Set.mem_Ioc]
  refine
    ⟨fun h => by linarith, fun h =>
      ⟨by linarith [pi_pos, neg_pi_lt_toReal θ], (le_div_iff₀' (zero_lt_two' Real)).1 h⟩⟩

/--
theorem `two_zsmul_toReal_eq_two_mul_add_two_pi` / 定理 `two_zsmul_toReal_eq_two_mul_add_two_pi`

English:
theorem two_zsmul_toReal_eq_two_mul_add_two_pi
  given: {θ : Angle}
  proof: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_toReal_eq_two_mul_add_two_pi]

@[simp, grind =]

中文:
定理 two_zsmul_to实数_eq_two_mul_add_two_pi
  条件: {θ : Angle}
  证明: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_toReal_eq_two_mul_add_two_pi]

@[simp, grind =]

Depends on / 依赖: two_nsmul, two_nsmul_toReal_eq_two_mul_add_two_pi, two_zsmul
-/
theorem two_zsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} :
    ((2 : Int) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal <= -π / 2 := by
  rw [two_zsmul]; rw [← two_nsmul]; rw [two_nsmul_toReal_eq_two_mul_add_two_pi]

@[simp, grind =]
/--
theorem `sin_toReal` / 定理 `sin_toReal`

English:
theorem sin_toReal
  given: (θ : Angle)
  statement: Real.sin θ.toReal = sin θ
  proof: by
  conv_rhs => rw [← coe_toReal θ, sin_coe]

@[simp, grind =]

中文:
定理 sin_to实数
  条件: (θ : Angle)
  结论: 实数.sin θ.to实数 = sin θ
  证明: by
  conv_rhs => rw [← coe_toReal θ, sin_coe]

@[simp, grind =]

Depends on / 依赖: coe_toReal, conv_rhs, sin_coe
-/
theorem sin_toReal (θ : Angle) : Real.sin θ.toReal = sin θ := by
  conv_rhs => rw [← coe_toReal θ, sin_coe]

@[simp, grind =]
/--
theorem `cos_toReal` / 定理 `cos_toReal`

English:
theorem cos_toReal
  given: (θ : Angle)
  statement: Real.cos θ.toReal = cos θ
  proof: by
  conv_rhs => rw [← coe_toReal θ, cos_coe]

中文:
定理 cos_to实数
  条件: (θ : Angle)
  结论: 实数.cos θ.to实数 = cos θ
  证明: by
  conv_rhs => rw [← coe_toReal θ, cos_coe]

Depends on / 依赖: Arrow.discreteEquiv, Finite, Finite.of_equiv, coe_toReal, conv_rhs, cos_coe, discreteEquiv, of_equiv
-/
theorem cos_toReal (θ : Angle) : Real.cos θ.toReal = cos θ := by
  conv_rhs => rw [← coe_toReal θ, cos_coe]

/--
theorem `cos_nonneg_iff_abs_toReal_le_pi_div_two` / 定理 `cos_nonneg_iff_abs_toReal_le_pi_div_two`

English:
theorem cos_nonneg_iff_abs_toReal_le_pi_div_two
  given: {θ : Angle}
  statement: 0 <= cos θ ↔ |θ.toReal| <= π / 2
  proof: by
  have : 0 < π / 2 := by positivity
  have := toReal_mem_Ioc θ
  rw [← cos_toReal]; rw [← cos_abs]
  grind [cos_neg_of_pi_div_two_lt_of_lt, cos_nonneg_of_mem_Icc]

中文:
定理 cos_nonneg_iff_abs_to实数_le_pi_div_two
  条件: {θ : Angle}
  结论: 0 <= cos θ ↔ |θ.to实数| <= π / 2
  证明: by
  have : 0 < π / 2 := by positivity
  have := toReal_mem_Ioc θ
  rw [← cos_toReal]; rw [← cos_abs]
  grind [cos_neg_of_pi_div_two_lt_of_lt, cos_nonneg_of_mem_Icc]

Depends on / 依赖: cos_abs, cos_neg_of_pi_div_two_lt_of_lt, cos_nonneg_of_mem_Icc, cos_toReal, toReal_mem_Ioc
-/
theorem cos_nonneg_iff_abs_toReal_le_pi_div_two {θ : Angle} : 0 <= cos θ ↔ |θ.toReal| <= π / 2 := by
  have : 0 < π / 2 := by positivity
  have := toReal_mem_Ioc θ
  rw [← cos_toReal]; rw [← cos_abs]
  grind [cos_neg_of_pi_div_two_lt_of_lt, cos_nonneg_of_mem_Icc]

/--
theorem `cos_pos_iff_abs_toReal_lt_pi_div_two` / 定理 `cos_pos_iff_abs_toReal_lt_pi_div_two`

English:
theorem cos_pos_iff_abs_toReal_lt_pi_div_two
  given: {θ : Angle}
  statement: 0 < cos θ ↔ |θ.toReal| < π / 2
  proof: by
  rw [lt_iff_le_and_ne]; rw [lt_iff_le_and_ne]; rw [cos_nonneg_iff_abs_toReal_le_pi_div_two]; rw [←
    and_congr_right]
  rintro -
  contrapose
  rw [@eq_comm Real 0]; rw [abs_toReal_eq_pi_div_two_iff]; rw [cos_eq_zero_iff]

中文:
定理 cos_pos_iff_abs_to实数_lt_pi_div_two
  条件: {θ : Angle}
  结论: 0 < cos θ ↔ |θ.to实数| < π / 2
  证明: by
  rw [lt_iff_le_and_ne]; rw [lt_iff_le_and_ne]; rw [cos_nonneg_iff_abs_toReal_le_pi_div_two]; rw [←
    and_congr_right]
  rintro -
  contrapose
  rw [@eq_comm Real 0]; rw [abs_toReal_eq_pi_div_two_iff]; rw [cos_eq_zero_iff]

Depends on / 依赖: abs_toReal_eq_pi_div_two_iff, and_congr_right, contrapose, cos_eq_zero_iff, cos_nonneg_iff_abs_toReal_le_pi_div_two, eq_comm, lt_iff_le_and_ne
-/
theorem cos_pos_iff_abs_toReal_lt_pi_div_two {θ : Angle} : 0 < cos θ ↔ |θ.toReal| < π / 2 := by
  rw [lt_iff_le_and_ne]; rw [lt_iff_le_and_ne]; rw [cos_nonneg_iff_abs_toReal_le_pi_div_two]; rw [←
    and_congr_right]
  rintro -
  contrapose
  rw [@eq_comm Real 0]; rw [abs_toReal_eq_pi_div_two_iff]; rw [cos_eq_zero_iff]

/--
lemma `two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two` / 引理 `two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two`

English:
lemma two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
  statement: {θ ψ : Angle} (hθ : |θ.toReal| < π / 2)
  proof: by
  suffices θ != ψ + π by simp [this, two_nsmul_eq_iff]
  rintro rfl
  simp only [← cos_pos_iff_abs_toReal_lt_pi_div_two, cos_add_pi] at hθ hψ
  grind

中文:
引理 two_nsmul_eq_iff_eq_of_abs_to实数_lt_pi_div_two
  结论: {θ ψ : Angle} (hθ : |θ.to实数| < π / 2)
  证明: by
  suffices θ != ψ + π by simp [this, two_nsmul_eq_iff]
  rintro rfl
  simp only [← cos_pos_iff_abs_toReal_lt_pi_div_two, cos_add_pi] at hθ hψ
  grind

Depends on / 依赖: cos_add_pi, cos_pos_iff_abs_toReal_lt_pi_div_two, two_nsmul_eq_iff
-/
lemma two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two {θ ψ : Angle} (hθ : |θ.toReal| < π / 2)
    (hψ : |ψ.toReal| < π / 2) : (2 : Nat) • θ = (2 : Nat) • ψ ↔ θ = ψ := by
  suffices θ != ψ + π by simp [this, two_nsmul_eq_iff]
  rintro rfl
  simp only [← cos_pos_iff_abs_toReal_lt_pi_div_two, cos_add_pi] at hθ hψ
  grind

/--
lemma `two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two` / 引理 `two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two`

English:
lemma two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
  statement: {θ ψ : Angle} (hθ : |θ.toReal| < π / 2)
  proof: by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two hθ hψ]

中文:
引理 two_zsmul_eq_iff_eq_of_abs_to实数_lt_pi_div_two
  结论: {θ ψ : Angle} (hθ : |θ.to实数| < π / 2)
  证明: by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two hθ hψ]

Depends on / 依赖: simp_rw, two_nsmul, two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two, two_zsmul
-/
lemma two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two {θ ψ : Angle} (hθ : |θ.toReal| < π / 2)
    (hψ : |ψ.toReal| < π / 2) : (2 : Int) • θ = (2 : Int) • ψ ↔ θ = ψ := by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two hθ hψ]

/--
theorem `cos_neg_iff_pi_div_two_lt_abs_toReal` / 定理 `cos_neg_iff_pi_div_two_lt_abs_toReal`

English:
theorem cos_neg_iff_pi_div_two_lt_abs_toReal
  given: {θ : Angle}
  statement: cos θ < 0 ↔ π / 2 < |θ.toReal|
  proof: by
  contrapose!; exact cos_nonneg_iff_abs_toReal_le_pi_div_two

中文:
定理 cos_neg_iff_pi_div_two_lt_abs_to实数
  条件: {θ : Angle}
  结论: cos θ < 0 ↔ π / 2 < |θ.to实数|
  证明: by
  contrapose!; exact cos_nonneg_iff_abs_toReal_le_pi_div_two

Depends on / 依赖: contrapose, cos_nonneg_iff_abs_toReal_le_pi_div_two
-/
theorem cos_neg_iff_pi_div_two_lt_abs_toReal {θ : Angle} : cos θ < 0 ↔ π / 2 < |θ.toReal| := by
  contrapose!; exact cos_nonneg_iff_abs_toReal_le_pi_div_two

/--
theorem `abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi` / 定理 `abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi`

English:
theorem abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi
  statement: {θ ψ : Angle}
  proof: by
  rw [← eq_sub_iff_add_eq]; rw [← two_nsmul_coe_div_two]; rw [← nsmul_sub]; rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl) <;> simp [cos_pi_div_two_sub]

中文:
定理 abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi
  结论: {θ ψ : Angle}
  证明: by
  rw [← eq_sub_iff_add_eq]; rw [← two_nsmul_coe_div_two]; rw [← nsmul_sub]; rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl) <;> simp [cos_pi_div_two_sub]

Depends on / 依赖: cos_pi_div_two_sub, eq_sub_iff_add_eq, nsmul_sub, two_nsmul_coe_div_two, two_nsmul_eq_iff
-/
theorem abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle}
    (h : (2 : Nat) • θ + (2 : Nat) • ψ = π) : |cos θ| = |sin ψ| := by
  rw [← eq_sub_iff_add_eq]; rw [← two_nsmul_coe_div_two]; rw [← nsmul_sub]; rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl) <;> simp [cos_pi_div_two_sub]

/--
theorem `abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi` / 定理 `abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi`

English:
theorem abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi
  statement: {θ ψ : Angle}
  proof: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi h

中文:
定理 abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi
  结论: {θ ψ : Angle}
  证明: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi h

Depends on / 依赖: abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi, simp_rw, two_nsmul, two_zsmul
-/
theorem abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle}
    (h : (2 : Int) • θ + (2 : Int) • ψ = π) : |cos θ| = |sin ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi h

/--
Definition of `tan` / `tan` 的定义

English:
definition tan
  signature: (θ : Angle)
  body: sin θ / cos θ

中文:
定义 tan
  签名: (θ : Angle)
  定义体: sin θ / cos θ
-/
def tan (θ : Angle) : Real :=
  sin θ / cos θ

/--
theorem `tan_eq_sin_div_cos` / 定理 `tan_eq_sin_div_cos`

English:
theorem tan_eq_sin_div_cos
  given: (θ : Angle)
  statement: tan θ = sin θ / cos θ
  proof: rfl

@[simp]

中文:
定理 tan_eq_sin_div_cos
  条件: (θ : Angle)
  结论: tan θ = sin θ / cos θ
  证明: rfl

@[simp]
-/
theorem tan_eq_sin_div_cos (θ : Angle) : tan θ = sin θ / cos θ :=
  rfl

@[simp]
/--
theorem `tan_coe` / 定理 `tan_coe`

English:
theorem tan_coe
  given: (x : Real)
  statement: tan (x : Angle) = Real.tan x
  proof: by
  rw [tan]; rw [sin_coe]; rw [cos_coe]; rw [Real.tan_eq_sin_div_cos]

@[simp]

中文:
定理 tan_coe
  条件: (x : 实数)
  结论: tan (x : Angle) = 实数.tan x
  证明: by
  rw [tan]; rw [sin_coe]; rw [cos_coe]; rw [Real.tan_eq_sin_div_cos]

@[simp]

Depends on / 依赖: Real.tan_eq_sin_div_cos, cos_coe, sin_coe, tan_eq_sin_div_cos
-/
theorem tan_coe (x : Real) : tan (x : Angle) = Real.tan x := by
  rw [tan]; rw [sin_coe]; rw [cos_coe]; rw [Real.tan_eq_sin_div_cos]

@[simp]
/--
theorem `tan_zero` / 定理 `tan_zero`

English:
theorem tan_zero
  statement: tan (0 : Angle) = 0
  proof: by rw [← coe_zero, tan_coe, Real.tan_zero]

中文:
定理 tan_zero
  结论: tan (0 : Angle) = 0
  证明: by rw [← coe_zero, tan_coe, Real.tan_zero]

Depends on / 依赖: Real.tan_zero, coe_zero, tan_coe, tan_zero
-/
theorem tan_zero : tan (0 : Angle) = 0 := by rw [← coe_zero, tan_coe, Real.tan_zero]

/--
theorem `tan_coe_pi` / 定理 `tan_coe_pi`

English:
theorem tan_coe_pi
  statement: tan (π : Angle) = 0
  proof: by rw [tan_coe, Real.tan_pi]

中文:
定理 tan_coe_pi
  结论: tan (π : Angle) = 0
  证明: by rw [tan_coe, Real.tan_pi]

Depends on / 依赖: Real.tan_pi, tan_coe, tan_pi
-/
theorem tan_coe_pi : tan (π : Angle) = 0 := by rw [tan_coe, Real.tan_pi]

/--
theorem `tan_periodic` / 定理 `tan_periodic`

English:
theorem tan_periodic
  statement: Function.Periodic tan (π : Angle)
  proof: by
  intro θ
  induction θ using Real.Angle.induction_on
  rw [← coe_add]; rw [tan_coe]; rw [tan_coe]
  exact Real.tan_periodic _

@[simp]

中文:
定理 tan_periodic
  结论: 函数.周期 tan (π : Angle)
  证明: by
  intro θ
  induction θ using Real.Angle.induction_on
  rw [← coe_add]; rw [tan_coe]; rw [tan_coe]
  exact Real.tan_periodic _

@[simp]

Depends on / 依赖: Real.Angle.induction_on, Real.tan_periodic, coe_add, induction_on, tan_coe, tan_periodic
-/
theorem tan_periodic : Function.Periodic tan (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  rw [← coe_add]; rw [tan_coe]; rw [tan_coe]
  exact Real.tan_periodic _

@[simp]
/--
theorem `tan_add_pi` / 定理 `tan_add_pi`

English:
theorem tan_add_pi
  given: (θ : Angle)
  statement: tan (θ + π) = tan θ
  proof: tan_periodic θ

@[simp]

中文:
定理 tan_add_pi
  条件: (θ : Angle)
  结论: tan (θ + π) = tan θ
  证明: tan_periodic θ

@[simp]

Depends on / 依赖: tan_periodic
-/
theorem tan_add_pi (θ : Angle) : tan (θ + π) = tan θ :=
  tan_periodic θ

@[simp]
/--
theorem `tan_sub_pi` / 定理 `tan_sub_pi`

English:
theorem tan_sub_pi
  given: (θ : Angle)
  statement: tan (θ - π) = tan θ
  proof: tan_periodic.sub_eq θ

@[simp]

中文:
定理 tan_sub_pi
  条件: (θ : Angle)
  结论: tan (θ - π) = tan θ
  证明: tan_periodic.sub_eq θ

@[simp]

Depends on / 依赖: sub_eq, tan_periodic, tan_periodic.sub_eq
-/
theorem tan_sub_pi (θ : Angle) : tan (θ - π) = tan θ :=
  tan_periodic.sub_eq θ

@[simp]
/--
theorem `tan_toReal` / 定理 `tan_toReal`

English:
theorem tan_toReal
  given: (θ : Angle)
  statement: Real.tan θ.toReal = tan θ
  proof: by
  conv_rhs => rw [← coe_toReal θ, tan_coe]

中文:
定理 tan_to实数
  条件: (θ : Angle)
  结论: 实数.tan θ.to实数 = tan θ
  证明: by
  conv_rhs => rw [← coe_toReal θ, tan_coe]

Depends on / 依赖: coe_toReal, conv_rhs, tan_coe
-/
theorem tan_toReal (θ : Angle) : Real.tan θ.toReal = tan θ := by
  conv_rhs => rw [← coe_toReal θ, tan_coe]

/--
theorem `tan_eq_of_two_nsmul_eq` / 定理 `tan_eq_of_two_nsmul_eq`

English:
theorem tan_eq_of_two_nsmul_eq
  given: {θ ψ : Angle} (h : (2 : Nat) • θ = (2 : Nat) • ψ)
  statement: tan θ = tan ψ
  proof: by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · exact tan_add_pi _

中文:
定理 tan_eq_of_two_nsmul_eq
  条件: {θ ψ : Angle} (h : (2 : 自然数) • θ = (2 : 自然数) • ψ)
  结论: tan θ = tan ψ
  证明: by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · exact tan_add_pi _

Depends on / 依赖: tan_add_pi, two_nsmul_eq_iff
-/
theorem tan_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : Nat) • θ = (2 : Nat) • ψ) : tan θ = tan ψ := by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · exact tan_add_pi _

/--
theorem `tan_eq_of_two_zsmul_eq` / 定理 `tan_eq_of_two_zsmul_eq`

English:
theorem tan_eq_of_two_zsmul_eq
  given: {θ ψ : Angle} (h : (2 : Int) • θ = (2 : Int) • ψ)
  statement: tan θ = tan ψ
  proof: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_of_two_nsmul_eq h

中文:
定理 tan_eq_of_two_zsmul_eq
  条件: {θ ψ : Angle} (h : (2 : 整数) • θ = (2 : 整数) • ψ)
  结论: tan θ = tan ψ
  证明: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_of_two_nsmul_eq h

Depends on / 依赖: simp_rw, tan_eq_of_two_nsmul_eq, two_nsmul, two_zsmul
-/
theorem tan_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : Int) • θ = (2 : Int) • ψ) : tan θ = tan ψ := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_of_two_nsmul_eq h

/--
theorem `tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi` / 定理 `tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi`

English:
theorem tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi
  statement: {θ ψ : Angle}
  proof: by
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  rw [← smul_add]; rw [← coe_add]; rw [← coe_nsmul]; rw [two_nsmul]; rw [← two_mul]; rw [angle_eq_iff_two_pi_dvd_sub] at h
  rcases h with ⟨k, h⟩
  rw [sub_eq_iff_eq_add]; rw [← mul_inv_cancel_left₀ two_ne_zero π]; rw [mul_assoc]; rw [← mul_add]; rw [mul_right_inj' (two_ne_zero' Real)]; rw [← eq_sub_iff_add_eq']; rw [mul_inv_cancel_left₀ two_ne_zero π]; rw [inv_mul_eq_div]; rw [mul_comm] at h
  rw [tan_coe]; rw [tan_coe]; rw [← tan_pi_div_two_sub]; rw [h]; rw [add_sub_assoc]; rw [add_comm]
  exact Real.tan_periodic.int_mul _ _

中文:
定理 tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi
  结论: {θ ψ : Angle}
  证明: by
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  rw [← smul_add]; rw [← coe_add]; rw [← coe_nsmul]; rw [two_nsmul]; rw [← two_mul]; rw [angle_eq_iff_two_pi_dvd_sub] at h
  rcases h with ⟨k, h⟩
  rw [sub_eq_iff_eq_add]; rw [← mul_inv_cancel_left₀ two_ne_zero π]; rw [mul_assoc]; rw [← mul_add]; rw [mul_right_inj' (two_ne_zero' Real)]; rw [← eq_sub_iff_add_eq']; rw [mul_inv_cancel_left₀ two_ne_zero π]; rw [inv_mul_eq_div]; rw [mul_comm] at h
  rw [tan_coe]; rw [tan_coe]; rw [← tan_pi_div_two_sub]; rw [h]; rw [add_sub_assoc]; rw [add_comm]
  exact Real.tan_periodic.int_mul _ _

Depends on / 依赖: Real.Angle.induction_on, angle_eq_iff_two_pi_dvd_sub, coe_add, coe_nsmul, eq_sub_iff_add_eq, induction_on, inv_mul_eq_div, mul_add, mul_assoc, mul_comm, mul_right_inj, smul_add, sub_eq_iff_eq_add, tan_c, tan_coe, two_mul, two_ne_zero, two_nsmul
-/
theorem tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle}
    (h : (2 : Nat) • θ + (2 : Nat) • ψ = π) : tan ψ = (tan θ)⁻¹ := by
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  rw [← smul_add]; rw [← coe_add]; rw [← coe_nsmul]; rw [two_nsmul]; rw [← two_mul]; rw [angle_eq_iff_two_pi_dvd_sub] at h
  rcases h with ⟨k, h⟩
  rw [sub_eq_iff_eq_add]; rw [← mul_inv_cancel_left₀ two_ne_zero π]; rw [mul_assoc]; rw [← mul_add]; rw [mul_right_inj' (two_ne_zero' Real)]; rw [← eq_sub_iff_add_eq']; rw [mul_inv_cancel_left₀ two_ne_zero π]; rw [inv_mul_eq_div]; rw [mul_comm] at h
  rw [tan_coe]; rw [tan_coe]; rw [← tan_pi_div_two_sub]; rw [h]; rw [add_sub_assoc]; rw [add_comm]
  exact Real.tan_periodic.int_mul _ _

/--
theorem `tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi` / 定理 `tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi`

English:
theorem tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi
  statement: {θ ψ : Angle}
  proof: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi h

中文:
定理 tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi
  结论: {θ ψ : Angle}
  证明: by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi h

Depends on / 依赖: simp_rw, tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi, two_nsmul, two_zsmul
-/
theorem tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle}
    (h : (2 : Int) • θ + (2 : Int) • ψ = π) : tan ψ = (tan θ)⁻¹ := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi h

/--
Definition of `sign` / `sign` 的定义

English:
definition sign
  signature: (θ : Angle)
  body: SignType.sign (sin θ)

@[simp, grind =]

中文:
定义 sign
  签名: (θ : Angle)
  定义体: SignType.sign (sin θ)

@[simp, grind =]

Depends on / 依赖: SignType, SignType.sign
-/
def sign (θ : Angle) : SignType :=
  SignType.sign (sin θ)

@[simp, grind =]
/--
theorem `sign_zero` / 定理 `sign_zero`

English:
theorem sign_zero
  statement: (0 : Angle).sign = 0
  proof: by
  rw [sign]; rw [sin_zero]; rw [_root_.sign_zero]

@[simp, grind =]

中文:
定理 sign_zero
  结论: (0 : Angle).sign = 0
  证明: by
  rw [sign]; rw [sin_zero]; rw [_root_.sign_zero]

@[simp, grind =]

Depends on / 依赖: _root_, _root_.sign_zero, sign_zero, sin_zero
-/
theorem sign_zero : (0 : Angle).sign = 0 := by
  rw [sign]; rw [sin_zero]; rw [_root_.sign_zero]

@[simp, grind =]
/--
theorem `sign_coe_pi` / 定理 `sign_coe_pi`

English:
theorem sign_coe_pi
  statement: (π : Angle).sign = 0
  proof: by rw [sign, sin_coe_pi, _root_.sign_zero]

@[simp, grind =]

中文:
定理 sign_coe_pi
  结论: (π : Angle).sign = 0
  证明: by rw [sign, sin_coe_pi, _root_.sign_zero]

@[simp, grind =]

Depends on / 依赖: _root_, _root_.sign_zero, sign_zero, sin_coe_pi
-/
theorem sign_coe_pi : (π : Angle).sign = 0 := by rw [sign, sin_coe_pi, _root_.sign_zero]

@[simp, grind =]
/--
theorem `sign_neg` / 定理 `sign_neg`

English:
theorem sign_neg
  given: (θ : Angle)
  statement: (-θ).sign = -θ.sign
  proof: by
  simp_rw [sign, sin_neg, Left.sign_neg]

中文:
定理 sign_neg
  条件: (θ : Angle)
  结论: (-θ).sign = -θ.sign
  证明: by
  simp_rw [sign, sin_neg, Left.sign_neg]

Depends on / 依赖: Left.sign_neg, sign_neg, simp_rw, sin_neg
-/
theorem sign_neg (θ : Angle) : (-θ).sign = -θ.sign := by
  simp_rw [sign, sin_neg, Left.sign_neg]

/--
theorem `sign_antiperiodic` / 定理 `sign_antiperiodic`

English:
theorem sign_antiperiodic
  statement: Function.Antiperiodic sign (π : Angle)
  proof: fun θ => by
  rw [sign]; rw [sign]; rw [sin_add_pi]; rw [Left.sign_neg]

@[simp, grind =]

中文:
定理 sign_antiperiodic
  结论: 函数.Antiperiodic sign (π : Angle)
  证明: fun θ => by
  rw [sign]; rw [sign]; rw [sin_add_pi]; rw [Left.sign_neg]

@[simp, grind =]

Depends on / 依赖: Left.sign_neg, sign_neg, sin_add_pi
-/
theorem sign_antiperiodic : Function.Antiperiodic sign (π : Angle) := fun θ => by
  rw [sign]; rw [sign]; rw [sin_add_pi]; rw [Left.sign_neg]

@[simp, grind =]
/--
theorem `sign_add_pi` / 定理 `sign_add_pi`

English:
theorem sign_add_pi
  given: (θ : Angle)
  statement: (θ + π).sign = -θ.sign
  proof: sign_antiperiodic θ

@[simp, grind =]

中文:
定理 sign_add_pi
  条件: (θ : Angle)
  结论: (θ + π).sign = -θ.sign
  证明: sign_antiperiodic θ

@[simp, grind =]

Depends on / 依赖: sign_antiperiodic
-/
theorem sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign :=
  sign_antiperiodic θ

@[simp, grind =]
/--
theorem `sign_pi_add` / 定理 `sign_pi_add`

English:
theorem sign_pi_add
  given: (θ : Angle)
  statement: ((π : Angle) + θ).sign = -θ.sign
  proof: by rw [add_comm, sign_add_pi]

@[simp, grind =]

中文:
定理 sign_pi_add
  条件: (θ : Angle)
  结论: ((π : Angle) + θ).sign = -θ.sign
  证明: by rw [add_comm, sign_add_pi]

@[simp, grind =]

Depends on / 依赖: add_comm, sign_add_pi
-/
theorem sign_pi_add (θ : Angle) : ((π : Angle) + θ).sign = -θ.sign := by rw [add_comm, sign_add_pi]

@[simp, grind =]
/--
theorem `sign_sub_pi` / 定理 `sign_sub_pi`

English:
theorem sign_sub_pi
  given: (θ : Angle)
  statement: (θ - π).sign = -θ.sign
  proof: sign_antiperiodic.sub_eq θ

@[simp, grind =]

中文:
定理 sign_sub_pi
  条件: (θ : Angle)
  结论: (θ - π).sign = -θ.sign
  证明: sign_antiperiodic.sub_eq θ

@[simp, grind =]

Depends on / 依赖: sign_antiperiodic, sign_antiperiodic.sub_eq, sub_eq
-/
theorem sign_sub_pi (θ : Angle) : (θ - π).sign = -θ.sign :=
  sign_antiperiodic.sub_eq θ

@[simp, grind =]
/--
theorem `sign_pi_sub` / 定理 `sign_pi_sub`

English:
theorem sign_pi_sub
  given: (θ : Angle)
  statement: ((π : Angle) - θ).sign = θ.sign
  proof: by
  simp [sign_antiperiodic.sub_eq']

@[grind =]

中文:
定理 sign_pi_sub
  条件: (θ : Angle)
  结论: ((π : Angle) - θ).sign = θ.sign
  证明: by
  simp [sign_antiperiodic.sub_eq']

@[grind =]

Depends on / 依赖: sign_antiperiodic, sign_antiperiodic.sub_eq, sub_eq
-/
theorem sign_pi_sub (θ : Angle) : ((π : Angle) - θ).sign = θ.sign := by
  simp [sign_antiperiodic.sub_eq']

@[grind =]
/--
theorem `sign_eq_zero_iff` / 定理 `sign_eq_zero_iff`

English:
theorem sign_eq_zero_iff
  given: {θ : Angle}
  statement: θ.sign = 0 ↔ θ = 0 ∨ θ = π
  proof: by
  rw [sign]; rw [_root_.sign_eq_zero_iff]; rw [sin_eq_zero_iff]

@[grind =]

中文:
定理 sign_eq_zero_iff
  条件: {θ : Angle}
  结论: θ.sign = 0 ↔ θ = 0 ∨ θ = π
  证明: by
  rw [sign]; rw [_root_.sign_eq_zero_iff]; rw [sin_eq_zero_iff]

@[grind =]

Depends on / 依赖: Over.Hom, _root_, _root_.sign_eq_zero_iff, sign_eq_zero_iff, sin_eq_zero_iff
-/
theorem sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔ θ = 0 ∨ θ = π := by
  rw [sign]; rw [_root_.sign_eq_zero_iff]; rw [sin_eq_zero_iff]

@[grind =]
/--
theorem `sign_ne_zero_iff` / 定理 `sign_ne_zero_iff`

English:
theorem sign_ne_zero_iff
  given: {θ : Angle}
  statement: θ.sign != 0 ↔ θ != 0 ∧ θ != π
  proof: by
  rw [← not_or]; rw [← sign_eq_zero_iff]

中文:
定理 sign_ne_zero_iff
  条件: {θ : Angle}
  结论: θ.sign != 0 ↔ θ != 0 ∧ θ != π
  证明: by
  rw [← not_or]; rw [← sign_eq_zero_iff]

Depends on / 依赖: not_or, sign_eq_zero_iff
-/
theorem sign_ne_zero_iff {θ : Angle} : θ.sign != 0 ↔ θ != 0 ∧ θ != π := by
  rw [← not_or]; rw [← sign_eq_zero_iff]

/--
theorem `toReal_neg_iff_sign_neg` / 定理 `toReal_neg_iff_sign_neg`

English:
theorem toReal_neg_iff_sign_neg
  given: {θ : Angle}
  statement: θ.toReal < 0 ↔ θ.sign = -1
  proof: by
  rw [sign]; rw [← sin_toReal]; rw [sign_eq_neg_one_iff]
  grind [sin_nonneg_of_nonneg_of_le_pi, sin_neg_of_neg_of_neg_pi_lt, toReal_mem_Ioc]

中文:
定理 to实数_neg_iff_sign_neg
  条件: {θ : Angle}
  结论: θ.to实数 < 0 ↔ θ.sign = -1
  证明: by
  rw [sign]; rw [← sin_toReal]; rw [sign_eq_neg_one_iff]
  grind [sin_nonneg_of_nonneg_of_le_pi, sin_neg_of_neg_of_neg_pi_lt, toReal_mem_Ioc]

Depends on / 依赖: sign_eq_neg_one_iff, sin_neg_of_neg_of_neg_pi_lt, sin_nonneg_of_nonneg_of_le_pi, sin_toReal, toReal_mem_Ioc
-/
theorem toReal_neg_iff_sign_neg {θ : Angle} : θ.toReal < 0 ↔ θ.sign = -1 := by
  rw [sign]; rw [← sin_toReal]; rw [sign_eq_neg_one_iff]
  grind [sin_nonneg_of_nonneg_of_le_pi, sin_neg_of_neg_of_neg_pi_lt, toReal_mem_Ioc]

/--
theorem `toReal_nonneg_iff_sign_nonneg` / 定理 `toReal_nonneg_iff_sign_nonneg`

English:
theorem toReal_nonneg_iff_sign_nonneg
  given: {θ : Angle}
  statement: 0 <= θ.toReal ↔ 0 <= θ.sign
  proof: by
  simp only [sign, ← sin_toReal, sign_nonneg_iff]
  grind [sin_nonneg_of_nonneg_of_le_pi, sin_neg_of_neg_of_neg_pi_lt, toReal_mem_Ioc]

@[simp]

中文:
定理 to实数_nonneg_iff_sign_nonneg
  条件: {θ : Angle}
  结论: 0 <= θ.to实数 ↔ 0 <= θ.sign
  证明: by
  simp only [sign, ← sin_toReal, sign_nonneg_iff]
  grind [sin_nonneg_of_nonneg_of_le_pi, sin_neg_of_neg_of_neg_pi_lt, toReal_mem_Ioc]

@[simp]

Depends on / 依赖: sign_nonneg_iff, sin_neg_of_neg_of_neg_pi_lt, sin_nonneg_of_nonneg_of_le_pi, sin_toReal, toReal_mem_Ioc
-/
theorem toReal_nonneg_iff_sign_nonneg {θ : Angle} : 0 <= θ.toReal ↔ 0 <= θ.sign := by
  simp only [sign, ← sin_toReal, sign_nonneg_iff]
  grind [sin_nonneg_of_nonneg_of_le_pi, sin_neg_of_neg_of_neg_pi_lt, toReal_mem_Ioc]

@[simp]
/--
theorem `sign_toReal` / 定理 `sign_toReal`

English:
theorem sign_toReal
  given: {θ : Angle} (h : θ != π)
  statement: SignType.sign θ.toReal = θ.sign
  proof: by
  rcases lt_trichotomy θ.toReal 0 with (ht | ht | ht)
  · simp [ht, toReal_neg_iff_sign_neg.1 ht]
  · simp [sign, ht, ← sin_toReal]
  · rw [sign, ← sin_toReal, sign_pos ht,
      sign_pos
        (sin_pos_of_pos_of_lt_pi ht ((toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)))]

中文:
定理 sign_to实数
  条件: {θ : Angle} (h : θ != π)
  结论: SignType.sign θ.to实数 = θ.sign
  证明: by
  rcases lt_trichotomy θ.toReal 0 with (ht | ht | ht)
  · simp [ht, toReal_neg_iff_sign_neg.1 ht]
  · simp [sign, ht, ← sin_toReal]
  · rw [sign, ← sin_toReal, sign_pos ht,
      sign_pos
        (sin_pos_of_pos_of_lt_pi ht ((toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)))]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, lt_of_ne, lt_trichotomy, sign_pos, sin_pos_of_pos_of_lt_pi, sin_toReal, toReal, toReal_eq_pi_iff, toReal_eq_pi_iff.not, toReal_le_pi, toReal_neg_iff_sign_neg
-/
theorem sign_toReal {θ : Angle} (h : θ != π) : SignType.sign θ.toReal = θ.sign := by
  rcases lt_trichotomy θ.toReal 0 with (ht | ht | ht)
  · simp [ht, toReal_neg_iff_sign_neg.1 ht]
  · simp [sign, ht, ← sin_toReal]
  · rw [sign, ← sin_toReal, sign_pos ht,
      sign_pos
        (sin_pos_of_pos_of_lt_pi ht ((toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)))]

/--
lemma `toReal_mem_Ioo_iff_sign_pos` / 引理 `toReal_mem_Ioo_iff_sign_pos`

English:
lemma toReal_mem_Ioo_iff_sign_pos
  given: {θ : Angle}
  proof: by
  rcases eq_or_ne θ π with rfl | h
  · simp
  · simp only [Set.mem_Ioo, ← sign_toReal h, sign_eq_one_iff, and_iff_left_iff_imp]
    exact fun _ => (toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)

中文:
引理 to实数_mem_Ioo_iff_sign_pos
  条件: {θ : Angle}
  证明: by
  rcases eq_or_ne θ π with rfl | h
  · simp
  · simp only [Set.mem_Ioo, ← sign_toReal h, sign_eq_one_iff, and_iff_left_iff_imp]
    exact fun _ => (toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)

Depends on / 依赖: Set.mem_Ioo, and_iff_left_iff_imp, eq_or_ne, lt_of_ne, mem_Ioo, sign_eq_one_iff, sign_toReal, toReal_eq_pi_iff, toReal_eq_pi_iff.not, toReal_le_pi
-/
lemma toReal_mem_Ioo_iff_sign_pos {θ : Angle} :
    θ.toReal in Set.Ioo 0 π ↔ θ.sign = 1 := by
  rcases eq_or_ne θ π with rfl | h
  · simp
  · simp only [Set.mem_Ioo, ← sign_toReal h, sign_eq_one_iff, and_iff_left_iff_imp]
    exact fun _ => (toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)

/--
theorem `coe_abs_toReal_of_sign_nonneg` / 定理 `coe_abs_toReal_of_sign_nonneg`

English:
theorem coe_abs_toReal_of_sign_nonneg
  given: {θ : Angle} (h : 0 <= θ.sign)
  statement: ↑|θ.toReal| = θ
  proof: by
  rw [abs_eq_self.2 (toReal_nonneg_iff_sign_nonneg.2 h)]; rw [coe_toReal]

中文:
定理 coe_abs_to实数_of_sign_nonneg
  条件: {θ : Angle} (h : 0 <= θ.sign)
  结论: ↑|θ.to实数| = θ
  证明: by
  rw [abs_eq_self.2 (toReal_nonneg_iff_sign_nonneg.2 h)]; rw [coe_toReal]

Depends on / 依赖: abs_eq_self, coe_toReal, toReal_nonneg_iff_sign_nonneg
-/
theorem coe_abs_toReal_of_sign_nonneg {θ : Angle} (h : 0 <= θ.sign) : ↑|θ.toReal| = θ := by
  rw [abs_eq_self.2 (toReal_nonneg_iff_sign_nonneg.2 h)]; rw [coe_toReal]

/--
theorem `neg_coe_abs_toReal_of_sign_nonpos` / 定理 `neg_coe_abs_toReal_of_sign_nonpos`

English:
theorem neg_coe_abs_toReal_of_sign_nonpos
  given: {θ : Angle} (h : θ.sign <= 0)
  statement: -↑|θ.toReal| = θ
  proof: by
  rw [SignType.nonpos_iff] at h
  rcases h with (h | h)
  · rw [abs_of_neg (toReal_neg_iff_sign_neg.2 h), coe_neg, neg_neg, coe_toReal]
  · rw [sign_eq_zero_iff] at h
    rcases h with (rfl | rfl) <;> simp [abs_of_pos Real.pi_pos]

中文:
定理 neg_coe_abs_to实数_of_sign_nonpos
  条件: {θ : Angle} (h : θ.sign <= 0)
  结论: -↑|θ.to实数| = θ
  证明: by
  rw [SignType.nonpos_iff] at h
  rcases h with (h | h)
  · rw [abs_of_neg (toReal_neg_iff_sign_neg.2 h), coe_neg, neg_neg, coe_toReal]
  · rw [sign_eq_zero_iff] at h
    rcases h with (rfl | rfl) <;> simp [abs_of_pos Real.pi_pos]

Depends on / 依赖: Real.pi_pos, SignType, SignType.nonpos_iff, abs_of_neg, abs_of_pos, coe_neg, coe_toReal, neg_neg, nonpos_iff, pi_pos, sign_eq_zero_iff, toReal_neg_iff_sign_neg
-/
theorem neg_coe_abs_toReal_of_sign_nonpos {θ : Angle} (h : θ.sign <= 0) : -↑|θ.toReal| = θ := by
  rw [SignType.nonpos_iff] at h
  rcases h with (h | h)
  · rw [abs_of_neg (toReal_neg_iff_sign_neg.2 h), coe_neg, neg_neg, coe_toReal]
  · rw [sign_eq_zero_iff] at h
    rcases h with (rfl | rfl) <;> simp [abs_of_pos Real.pi_pos]

/--
theorem `eq_iff_sign_eq_and_abs_toReal_eq` / 定理 `eq_iff_sign_eq_and_abs_toReal_eq`

English:
theorem eq_iff_sign_eq_and_abs_toReal_eq
  given: {θ ψ : Angle}
  proof: by
  grind [toReal_neg_iff_sign_neg]

中文:
定理 eq_iff_sign_eq_and_abs_to实数_eq
  条件: {θ ψ : Angle}
  证明: by
  grind [toReal_neg_iff_sign_neg]

Depends on / 依赖: toReal_neg_iff_sign_neg
-/
theorem eq_iff_sign_eq_and_abs_toReal_eq {θ ψ : Angle} :
    θ = ψ ↔ θ.sign = ψ.sign ∧ |θ.toReal| = |ψ.toReal| := by
  grind [toReal_neg_iff_sign_neg]

/--
theorem `eq_iff_abs_toReal_eq_of_sign_eq` / 定理 `eq_iff_abs_toReal_eq_of_sign_eq`

English:
theorem eq_iff_abs_toReal_eq_of_sign_eq
  given: {θ ψ : Angle} (h : θ.sign = ψ.sign)
  proof: by simpa [h] using @eq_iff_sign_eq_and_abs_toReal_eq θ ψ

@[simp]

中文:
定理 eq_iff_abs_to实数_eq_of_sign_eq
  条件: {θ ψ : Angle} (h : θ.sign = ψ.sign)
  证明: by simpa [h] using @eq_iff_sign_eq_and_abs_toReal_eq θ ψ

@[simp]

Depends on / 依赖: eq_iff_sign_eq_and_abs_toReal_eq
-/
theorem eq_iff_abs_toReal_eq_of_sign_eq {θ ψ : Angle} (h : θ.sign = ψ.sign) :
    θ = ψ ↔ |θ.toReal| = |ψ.toReal| := by simpa [h] using @eq_iff_sign_eq_and_abs_toReal_eq θ ψ

@[simp]
/--
theorem `sign_coe_pi_div_two` / 定理 `sign_coe_pi_div_two`

English:
theorem sign_coe_pi_div_two
  statement: (↑(π / 2) : Angle).sign = 1
  proof: by
  rw [sign]; rw [sin_coe]; rw [sin_pi_div_two]; rw [sign_one]

@[simp]

中文:
定理 sign_coe_pi_div_two
  结论: (↑(π / 2) : Angle).sign = 1
  证明: by
  rw [sign]; rw [sin_coe]; rw [sin_pi_div_two]; rw [sign_one]

@[simp]

Depends on / 依赖: sign_one, sin_coe, sin_pi_div_two
-/
theorem sign_coe_pi_div_two : (↑(π / 2) : Angle).sign = 1 := by
  rw [sign]; rw [sin_coe]; rw [sin_pi_div_two]; rw [sign_one]

@[simp]
/--
theorem `sign_coe_neg_pi_div_two` / 定理 `sign_coe_neg_pi_div_two`

English:
theorem sign_coe_neg_pi_div_two
  statement: (↑(-π / 2) : Angle).sign = -1
  proof: by
  rw [sign]; rw [sin_coe]; rw [neg_div]; rw [Real.sin_neg]; rw [sin_pi_div_two]; rw [Left.sign_neg]; rw [sign_one]

中文:
定理 sign_coe_neg_pi_div_two
  结论: (↑(-π / 2) : Angle).sign = -1
  证明: by
  rw [sign]; rw [sin_coe]; rw [neg_div]; rw [Real.sin_neg]; rw [sin_pi_div_two]; rw [Left.sign_neg]; rw [sign_one]

Depends on / 依赖: Left.sign_neg, Real.sin_neg, neg_div, sign_neg, sign_one, sin_coe, sin_neg, sin_pi_div_two
-/
theorem sign_coe_neg_pi_div_two : (↑(-π / 2) : Angle).sign = -1 := by
  rw [sign]; rw [sin_coe]; rw [neg_div]; rw [Real.sin_neg]; rw [sin_pi_div_two]; rw [Left.sign_neg]; rw [sign_one]

/--
theorem `sign_coe_nonneg_of_nonneg_of_le_pi` / 定理 `sign_coe_nonneg_of_nonneg_of_le_pi`

English:
theorem sign_coe_nonneg_of_nonneg_of_le_pi
  given: {θ : Real} (h0 : 0 <= θ) (hpi : θ <= π)
  proof: by
  rw [sign]; rw [sign_nonneg_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi

中文:
定理 sign_coe_nonneg_of_nonneg_of_le_pi
  条件: {θ : 实数} (h0 : 0 <= θ) (hpi : θ <= π)
  证明: by
  rw [sign]; rw [sign_nonneg_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi

Depends on / 依赖: sign_nonneg_iff, sin_nonneg_of_nonneg_of_le_pi
-/
theorem sign_coe_nonneg_of_nonneg_of_le_pi {θ : Real} (h0 : 0 <= θ) (hpi : θ <= π) :
    0 <= (θ : Angle).sign := by
  rw [sign]; rw [sign_nonneg_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi

/--
theorem `sign_neg_coe_nonpos_of_nonneg_of_le_pi` / 定理 `sign_neg_coe_nonpos_of_nonneg_of_le_pi`

English:
theorem sign_neg_coe_nonpos_of_nonneg_of_le_pi
  given: {θ : Real} (h0 : 0 <= θ) (hpi : θ <= π)
  proof: by
  rw [sign]; rw [sign_nonpos_iff]; rw [sin_neg]; rw [Left.neg_nonpos_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi

中文:
定理 sign_neg_coe_nonpos_of_nonneg_of_le_pi
  条件: {θ : 实数} (h0 : 0 <= θ) (hpi : θ <= π)
  证明: by
  rw [sign]; rw [sign_nonpos_iff]; rw [sin_neg]; rw [Left.neg_nonpos_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi

Depends on / 依赖: Left.neg_nonpos_iff, neg_nonpos_iff, sign_nonpos_iff, sin_neg, sin_nonneg_of_nonneg_of_le_pi
-/
theorem sign_neg_coe_nonpos_of_nonneg_of_le_pi {θ : Real} (h0 : 0 <= θ) (hpi : θ <= π) :
    (-θ : Angle).sign <= 0 := by
  rw [sign]; rw [sign_nonpos_iff]; rw [sin_neg]; rw [Left.neg_nonpos_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi

/--
theorem `sign_two_nsmul_eq_sign_iff` / 定理 `sign_two_nsmul_eq_sign_iff`

English:
theorem sign_two_nsmul_eq_sign_iff
  given: {θ : Angle}
  proof: by
  simp only [sign, sin_two_nsmul, nsmul_eq_mul, Nat.cast_ofNat, sign_mul, Nat.ofNat_pos, sign_pos,
    one_mul, mul_right_eq_self₀, _root_.sign_eq_zero_iff, sign_eq_one_iff, sin_eq_zero_iff,
    cos_pos_iff_abs_toReal_lt_pi_div_two]
  have : 0 < π / 2 := by positivity
  grind

中文:
定理 sign_two_nsmul_eq_sign_iff
  条件: {θ : Angle}
  证明: by
  simp only [sign, sin_two_nsmul, nsmul_eq_mul, Nat.cast_ofNat, sign_mul, Nat.ofNat_pos, sign_pos,
    one_mul, mul_right_eq_self₀, _root_.sign_eq_zero_iff, sign_eq_one_iff, sin_eq_zero_iff,
    cos_pos_iff_abs_toReal_lt_pi_div_two]
  have : 0 < π / 2 := by positivity
  grind

Depends on / 依赖: Nat.cast_ofNat, Nat.ofNat_pos, _root_, _root_.sign_eq_zero_iff, cast_ofNat, cos_pos_iff_abs_toReal_lt_pi_div_two, nsmul_eq_mul, ofNat_pos, one_mul, sign_eq_one_iff, sign_eq_zero_iff, sign_mul, sign_pos, sin_eq_zero_iff, sin_two_nsmul
-/
theorem sign_two_nsmul_eq_sign_iff {θ : Angle} :
    ((2 : Nat) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 := by
  simp only [sign, sin_two_nsmul, nsmul_eq_mul, Nat.cast_ofNat, sign_mul, Nat.ofNat_pos, sign_pos,
    one_mul, mul_right_eq_self₀, _root_.sign_eq_zero_iff, sign_eq_one_iff, sin_eq_zero_iff,
    cos_pos_iff_abs_toReal_lt_pi_div_two]
  have : 0 < π / 2 := by positivity
  grind

/--
theorem `sign_two_zsmul_eq_sign_iff` / 定理 `sign_two_zsmul_eq_sign_iff`

English:
theorem sign_two_zsmul_eq_sign_iff
  given: {θ : Angle}
  proof: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [sign_two_nsmul_eq_sign_iff]

中文:
定理 sign_two_zsmul_eq_sign_iff
  条件: {θ : Angle}
  证明: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [sign_two_nsmul_eq_sign_iff]

Depends on / 依赖: sign_two_nsmul_eq_sign_iff, two_nsmul, two_zsmul
-/
theorem sign_two_zsmul_eq_sign_iff {θ : Angle} :
    ((2 : Int) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 := by
  rw [two_zsmul]; rw [← two_nsmul]; rw [sign_two_nsmul_eq_sign_iff]

/--
lemma `sign_two_nsmul_eq_neg_sign_iff` / 引理 `sign_two_nsmul_eq_neg_sign_iff`

English:
lemma sign_two_nsmul_eq_neg_sign_iff
  given: {θ : Angle}
  proof: by
  simpa [← cos_pos_iff_abs_toReal_lt_pi_div_two, ← cos_neg_iff_pi_div_two_lt_abs_toReal]
    using sign_two_nsmul_eq_sign_iff (θ := θ + π)

中文:
引理 sign_two_nsmul_eq_neg_sign_iff
  条件: {θ : Angle}
  证明: by
  simpa [← cos_pos_iff_abs_toReal_lt_pi_div_two, ← cos_neg_iff_pi_div_two_lt_abs_toReal]
    using sign_two_nsmul_eq_sign_iff (θ := θ + π)

Depends on / 依赖: cos_neg_iff_pi_div_two_lt_abs_toReal, cos_pos_iff_abs_toReal_lt_pi_div_two, sign_two_nsmul_eq_sign_iff
-/
lemma sign_two_nsmul_eq_neg_sign_iff {θ : Angle} :
    ((2 : Nat) • θ).sign = -θ.sign ↔ θ = 0 ∨ π / 2 < |θ.toReal| := by
  simpa [← cos_pos_iff_abs_toReal_lt_pi_div_two, ← cos_neg_iff_pi_div_two_lt_abs_toReal]
    using sign_two_nsmul_eq_sign_iff (θ := θ + π)

/--
lemma `sign_two_zsmul_eq_neg_sign_iff` / 引理 `sign_two_zsmul_eq_neg_sign_iff`

English:
lemma sign_two_zsmul_eq_neg_sign_iff
  given: {θ : Angle}
  proof: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [sign_two_nsmul_eq_neg_sign_iff]

中文:
引理 sign_two_zsmul_eq_neg_sign_iff
  条件: {θ : Angle}
  证明: by
  rw [two_zsmul]; rw [← two_nsmul]; rw [sign_two_nsmul_eq_neg_sign_iff]

Depends on / 依赖: sign_two_nsmul_eq_neg_sign_iff, two_nsmul, two_zsmul
-/
lemma sign_two_zsmul_eq_neg_sign_iff {θ : Angle} :
    ((2 : Int) • θ).sign = -θ.sign ↔ θ = 0 ∨ π / 2 < |θ.toReal| := by
  rw [two_zsmul]; rw [← two_nsmul]; rw [sign_two_nsmul_eq_neg_sign_iff]

/--
theorem `eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg` / 定理 `eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg`

English:
theorem eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg
  statement: (a b : Real.Angle) (h : (2 : Int) • a = (2 : Int) • b)
  proof: by
  have h1 := Real.Angle.two_zsmul_eq_iff.mp h
  refine h1.resolve_left ?_
  rintro rfl
  simp only [SignType.self_eq_neg_iff] at h_sign
  rw [h_sign] at h_ne
  contradiction

中文:
定理 eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg
  结论: (a b : 实数.Angle) (h : (2 : 整数) • a = (2 : 整数) • b)
  证明: by
  have h1 := Real.Angle.two_zsmul_eq_iff.mp h
  refine h1.resolve_left ?_
  rintro rfl
  simp only [SignType.self_eq_neg_iff] at h_sign
  rw [h_sign] at h_ne
  contradiction

Depends on / 依赖: Real.Angle.two_zsmul_eq_iff.mp, SignType, SignType.self_eq_neg_iff, h1.resolve_left, h_ne, h_sign, resolve_left, self_eq_neg_iff, two_zsmul_eq_iff
-/
theorem eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg (a b : Real.Angle) (h : (2 : Int) • a = (2 : Int) • b)
    (h_sign : a.sign = -b.sign) (h_ne : b.sign != 0) : a = b + π := by
  have h1 := Real.Angle.two_zsmul_eq_iff.mp h
  refine h1.resolve_left ?_
  rintro rfl
  simp only [SignType.self_eq_neg_iff] at h_sign
  rw [h_sign] at h_ne
  contradiction

/--
theorem `sub_ne_pi_of_sign_eq_of_sign_ne_zero` / 定理 `sub_ne_pi_of_sign_eq_of_sign_ne_zero`

English:
theorem sub_ne_pi_of_sign_eq_of_sign_ne_zero
  statement: (a b : Real.Angle) (h_sign : a.sign = b.sign)
  proof: by
  intro h
  have h' : a = b + π := by
    simp [← h]
  have h_sign' := h_sign
  rw [h']; rw [Real.Angle.sign_add_pi] at h_sign'
  simp only [SignType.neg_eq_self_iff] at h_sign'
  contradiction

中文:
定理 sub_ne_pi_of_sign_eq_of_sign_ne_zero
  结论: (a b : 实数.Angle) (h_sign : a.sign = b.sign)
  证明: by
  intro h
  have h' : a = b + π := by
    simp [← h]
  have h_sign' := h_sign
  rw [h']; rw [Real.Angle.sign_add_pi] at h_sign'
  simp only [SignType.neg_eq_self_iff] at h_sign'
  contradiction

Depends on / 依赖: Real.Angle.sign_add_pi, SignType, SignType.neg_eq_self_iff, h_sign, neg_eq_self_iff, sign_add_pi
-/
theorem sub_ne_pi_of_sign_eq_of_sign_ne_zero (a b : Real.Angle) (h_sign : a.sign = b.sign)
    (h_ne : b.sign != 0) : a - b != π := by
  intro h
  have h' : a = b + π := by
    simp [← h]
  have h_sign' := h_sign
  rw [h']; rw [Real.Angle.sign_add_pi] at h_sign'
  simp only [SignType.neg_eq_self_iff] at h_sign'
  contradiction

/--
theorem `two_zsmul_eq_iff_eq` / 定理 `two_zsmul_eq_iff_eq`

English:
theorem two_zsmul_eq_iff_eq
  given: {a b : Real.Angle} (ha : a.sign != 0) (h : a.sign = b.sign)
  proof: by
  rw [Real.Angle.two_zsmul_eq_iff]
  constructor
  · intro h
    rcases h with h1 | h2
    · exact h1
    · have : a.sign = (b + π).sign := by aesop
      rw [Real.Angle.sign_add_pi] at this
      have := congr_arg (· = b.sign) this
      aesop
  · intro h
    aesop

中文:
定理 two_zsmul_eq_iff_eq
  条件: {a b : 实数.Angle} (ha : a.sign != 0) (h : a.sign = b.sign)
  证明: by
  rw [Real.Angle.two_zsmul_eq_iff]
  constructor
  · intro h
    rcases h with h1 | h2
    · exact h1
    · have : a.sign = (b + π).sign := by aesop
      rw [Real.Angle.sign_add_pi] at this
      have := congr_arg (· = b.sign) this
      aesop
  · intro h
    aesop

Depends on / 依赖: Real.Angle.sign_add_pi, Real.Angle.two_zsmul_eq_iff, a.sign, b.sign, congr_arg, sign_add_pi, two_zsmul_eq_iff
-/
theorem two_zsmul_eq_iff_eq {a b : Real.Angle} (ha : a.sign != 0) (h : a.sign = b.sign) :
    (2 : Int) • a = (2 : Int) • b ↔ a = b := by
  rw [Real.Angle.two_zsmul_eq_iff]
  constructor
  · intro h
    rcases h with h1 | h2
    · exact h1
    · have : a.sign = (b + π).sign := by aesop
      rw [Real.Angle.sign_add_pi] at this
      have := congr_arg (· = b.sign) this
      aesop
  · intro h
    aesop

/--
lemma `abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq` / 引理 `abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq`

English:
lemma abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq
  statement: {θ ψ : Angle}
  proof: by
  rcases two_nsmul_eq_zero_iff.mp h with h | h
  · simp_all [add_eq_zero_iff_eq_neg.mp h]
  rw [← coe_toReal θ]; rw [← coe_toReal ψ]; rw [← coe_add] at h
  suffices |θ.toReal + ψ.toReal| = π by grind [toReal_neg_iff_sign_neg, abs_add_eq_add_abs_iff]
  rw [abs_eq pi_nonneg]
  rcases angle_eq_iff_two_pi_dvd_sub.mp h with ⟨k, hk⟩
  rw [sub_eq_iff_eq_add] at hk
  have : k in Finset.Icc (-1) 0 :=
IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo two_pi_pos by grind [toReal_mem_Ioc]
  fin_cases this
  all_goals simp at hk; grind

中文:
引理 abs_to实数_add_abs_to实数_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq
  结论: {θ ψ : Angle}
  证明: by
  rcases two_nsmul_eq_zero_iff.mp h with h | h
  · simp_all [add_eq_zero_iff_eq_neg.mp h]
  rw [← coe_toReal θ]; rw [← coe_toReal ψ]; rw [← coe_add] at h
  suffices |θ.toReal + ψ.toReal| = π by grind [toReal_neg_iff_sign_neg, abs_add_eq_add_abs_iff]
  rw [abs_eq pi_nonneg]
  rcases angle_eq_iff_two_pi_dvd_sub.mp h with ⟨k, hk⟩
  rw [sub_eq_iff_eq_add] at hk
  have : k in Finset.Icc (-1) 0 :=
IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo two_pi_pos by grind [toReal_mem_Ioc]
  fin_cases this
  all_goals simp at hk; grind

Depends on / 依赖: Finset, Finset.Icc, IsStrictOrderedRing, IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo, abs_add_eq_add_abs_iff, abs_eq, add_eq_zero_iff_eq_neg, add_eq_zero_iff_eq_neg.mp, all_goals, angle_eq_iff_two_pi_dvd_sub, angle_eq_iff_two_pi_dvd_sub.mp, coe_add, coe_toReal, fin_cases, int_mem_Icc_of_mul_mem_Ioo, pi_nonneg, sub_eq_iff_eq_add, toReal, toReal_mem_Ioc, toReal_neg_iff_sign_neg
-/
lemma abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq {θ ψ : Angle}
    (h : (2 : Nat) • (θ + ψ) = 0) (hs : θ.sign = ψ.sign) (h0 : θ.sign != 0) :
    |θ.toReal| + |ψ.toReal| = π := by
  rcases two_nsmul_eq_zero_iff.mp h with h | h
  · simp_all [add_eq_zero_iff_eq_neg.mp h]
  rw [← coe_toReal θ]; rw [← coe_toReal ψ]; rw [← coe_add] at h
  suffices |θ.toReal + ψ.toReal| = π by grind [toReal_neg_iff_sign_neg, abs_add_eq_add_abs_iff]
  rw [abs_eq pi_nonneg]
  rcases angle_eq_iff_two_pi_dvd_sub.mp h with ⟨k, hk⟩
  rw [sub_eq_iff_eq_add] at hk
  have : k in Finset.Icc (-1) 0 :=
IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo two_pi_pos by grind [toReal_mem_Ioc]
  fin_cases this
  all_goals simp at hk; grind

/--
lemma `abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq` / 引理 `abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq`

English:
lemma abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq
  statement: {θ ψ : Angle}
  proof: by
  rw [two_zsmul]; rw [← two_nsmul] at h
  exact abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq h hs h0

中文:
引理 abs_to实数_add_abs_to实数_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq
  结论: {θ ψ : Angle}
  证明: by
  rw [two_zsmul]; rw [← two_nsmul] at h
  exact abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq h hs h0

Depends on / 依赖: abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq, two_nsmul, two_zsmul
-/
lemma abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq {θ ψ : Angle}
    (h : (2 : Int) • (θ + ψ) = 0) (hs : θ.sign = ψ.sign) (h0 : θ.sign != 0) :
    |θ.toReal| + |ψ.toReal| = π := by
  rw [two_zsmul]; rw [← two_nsmul] at h
  exact abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq h hs h0

/--
lemma `toReal_add_of_sign_pos_sign_neg` / 引理 `toReal_add_of_sign_pos_sign_neg`

English:
lemma toReal_add_of_sign_pos_sign_neg
  statement: {θ ψ : Angle}
  proof: by
  suffices ((θ.toReal + ψ.toReal : Real) : Angle).toReal = θ.toReal + ψ.toReal by simpa using this
  rw [toReal_coe_eq_self_iff]
  grind [toReal_mem_Ioc, toReal_neg_iff_sign_neg, toReal_mem_Ioo_iff_sign_pos]

中文:
引理 to实数_add_of_sign_pos_sign_neg
  结论: {θ ψ : Angle}
  证明: by
  suffices ((θ.toReal + ψ.toReal : Real) : Angle).toReal = θ.toReal + ψ.toReal by simpa using this
  rw [toReal_coe_eq_self_iff]
  grind [toReal_mem_Ioc, toReal_neg_iff_sign_neg, toReal_mem_Ioo_iff_sign_pos]

Depends on / 依赖: toReal, toReal_coe_eq_self_iff, toReal_mem_Ioc, toReal_mem_Ioo_iff_sign_pos, toReal_neg_iff_sign_neg
-/
lemma toReal_add_of_sign_pos_sign_neg {θ ψ : Angle}
    (hθ : θ.sign = 1) (hψ : ψ.sign = -1) : (θ + ψ).toReal = θ.toReal + ψ.toReal := by
  suffices ((θ.toReal + ψ.toReal : Real) : Angle).toReal = θ.toReal + ψ.toReal by simpa using this
  rw [toReal_coe_eq_self_iff]
  grind [toReal_mem_Ioc, toReal_neg_iff_sign_neg, toReal_mem_Ioo_iff_sign_pos]

/--
lemma `toReal_add_of_sign_eq_neg_sign` / 引理 `toReal_add_of_sign_eq_neg_sign`

English:
lemma toReal_add_of_sign_eq_neg_sign
  statement: {θ ψ : Angle} (hψ : θ != π ∨ ψ != π)
  proof: by
  obtain (h | h | h) := ψ.sign.trichotomy
  all_goals grind [neg_neg, add_comm, toReal_add_of_sign_pos_sign_neg]

中文:
引理 to实数_add_of_sign_eq_neg_sign
  结论: {θ ψ : Angle} (hψ : θ != π ∨ ψ != π)
  证明: by
  obtain (h | h | h) := ψ.sign.trichotomy
  all_goals grind [neg_neg, add_comm, toReal_add_of_sign_pos_sign_neg]

Depends on / 依赖: add_comm, all_goals, neg_neg, sign.trichotomy, toReal_add_of_sign_pos_sign_neg, trichotomy
-/
lemma toReal_add_of_sign_eq_neg_sign {θ ψ : Angle} (hψ : θ != π ∨ ψ != π)
    (hs : θ.sign = -ψ.sign) : (θ + ψ).toReal = θ.toReal + ψ.toReal := by
  obtain (h | h | h) := ψ.sign.trichotomy
  all_goals grind [neg_neg, add_comm, toReal_add_of_sign_pos_sign_neg]

/--
lemma `toReal_add_eq_toReal_add_toReal` / 引理 `toReal_add_eq_toReal_add_toReal`

English:
lemma toReal_add_eq_toReal_add_toReal
  statement: {θ ψ : Angle} (hθ : θ != π) (hψ : ψ != π)
  proof: by
  obtain (hs | hs) := hs
  · obtain (h | h | h) := ψ.sign.trichotomy <;> obtain (h | h | h) := θ.sign.trichotomy
    all_goals grind [add_comm, toReal_add_of_sign_pos_sign_neg, sign_eq_zero_iff]
  · rw [← neg_neg θ.sign, ← sign_neg] at hs
    have := toReal_add_of_sign_eq_neg_sign (.inr <| by simpa [neg_eq_iff_eq_neg]) hs.symm
    simpa [toReal_neg_eq_neg_toReal_iff.mpr, hθ, ← sub_eq_add_neg, eq_sub_iff_add_eq', eq_comm]

中文:
引理 to实数_add_eq_to实数_add_to实数
  结论: {θ ψ : Angle} (hθ : θ != π) (hψ : ψ != π)
  证明: by
  obtain (hs | hs) := hs
  · obtain (h | h | h) := ψ.sign.trichotomy <;> obtain (h | h | h) := θ.sign.trichotomy
    all_goals grind [add_comm, toReal_add_of_sign_pos_sign_neg, sign_eq_zero_iff]
  · rw [← neg_neg θ.sign, ← sign_neg] at hs
    have := toReal_add_of_sign_eq_neg_sign (.inr <| by simpa [neg_eq_iff_eq_neg]) hs.symm
    simpa [toReal_neg_eq_neg_toReal_iff.mpr, hθ, ← sub_eq_add_neg, eq_sub_iff_add_eq', eq_comm]

Depends on / 依赖: add_comm, all_goals, eq_comm, eq_sub_iff_add_eq, hs.symm, neg_eq_iff_eq_neg, neg_neg, sign.trichotomy, sign_eq_zero_iff, sign_neg, sub_eq_add_neg, toReal_add_of_sign_eq_neg_sign, toReal_add_of_sign_pos_sign_neg, toReal_neg_eq_neg_toReal_iff, toReal_neg_eq_neg_toReal_iff.mpr, trichotomy
-/
lemma toReal_add_eq_toReal_add_toReal {θ ψ : Angle} (hθ : θ != π) (hψ : ψ != π)
    (hs : θ.sign != ψ.sign ∨ θ.sign = (θ + ψ).sign) : (θ + ψ).toReal = θ.toReal + ψ.toReal := by
  obtain (hs | hs) := hs
  · obtain (h | h | h) := ψ.sign.trichotomy <;> obtain (h | h | h) := θ.sign.trichotomy
    all_goals grind [add_comm, toReal_add_of_sign_pos_sign_neg, sign_eq_zero_iff]
  · rw [← neg_neg θ.sign, ← sign_neg] at hs
    have := toReal_add_of_sign_eq_neg_sign (.inr <| by simpa [neg_eq_iff_eq_neg]) hs.symm
    simpa [toReal_neg_eq_neg_toReal_iff.mpr, hθ, ← sub_eq_add_neg, eq_sub_iff_add_eq', eq_comm]

/--
lemma `abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux` / 引理 `abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux`

English:
lemma abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux
  statement: {θ ψ : Angle}
  proof: by
  rw [← toReal_mem_Ioo_iff_sign_pos] at hθs hψs
  have : ((θ + ψ).toReal : Angle) = ↑(θ.toReal + ψ.toReal) := by simp
  obtain ⟨k, hk⟩ := angle_eq_iff_two_pi_dvd_sub.mp this
  obtain (h | h) : (θ + ψ).toReal <= 0 ∨ θ + ψ = π := by
    have := (θ + ψ).sign.trichotomy
    grind [sign_eq_zero_iff, toReal_eq_zero_iff, toReal_neg_iff_sign_neg]
· obtain rfl : k = -1 := IsStrictOrderedRing.int_eq_of_mul_mem_Ioo two_pi_pos by
      grind [toReal_mem_Ioc]
    grind [abs_of_nonpos]
  · simp_all only [sign_coe_pi, ne_eq, zero_ne_one, not_false_eq_true, toReal_pi, coe_add,
      coe_toReal, pi_pos, abs_of_pos]
    obtain rfl : k = 0 := IsStrictOrderedRing.int_eq_of_mul_mem_Ioo two_pi_pos (by grind)
    grind

中文:
引理 abs_to实数_add_eq_two_pi_sub_abs_to实数_add_abs_to实数_aux
  结论: {θ ψ : Angle}
  证明: by
  rw [← toReal_mem_Ioo_iff_sign_pos] at hθs hψs
  have : ((θ + ψ).toReal : Angle) = ↑(θ.toReal + ψ.toReal) := by simp
  obtain ⟨k, hk⟩ := angle_eq_iff_two_pi_dvd_sub.mp this
  obtain (h | h) : (θ + ψ).toReal <= 0 ∨ θ + ψ = π := by
    have := (θ + ψ).sign.trichotomy
    grind [sign_eq_zero_iff, toReal_eq_zero_iff, toReal_neg_iff_sign_neg]
· obtain rfl : k = -1 := IsStrictOrderedRing.int_eq_of_mul_mem_Ioo two_pi_pos by
      grind [toReal_mem_Ioc]
    grind [abs_of_nonpos]
  · simp_all only [sign_coe_pi, ne_eq, zero_ne_one, not_false_eq_true, toReal_pi, coe_add,
      coe_toReal, pi_pos, abs_of_pos]
    obtain rfl : k = 0 := IsStrictOrderedRing.int_eq_of_mul_mem_Ioo two_pi_pos (by grind)
    grind
-/
private lemma abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux {θ ψ : Angle}
    (hθs : θ.sign = 1) (hψs : ψ.sign = 1)
    (hsa : (θ + ψ).sign != 1) : |(θ + ψ).toReal| = 2 * π - (|θ.toReal| + |ψ.toReal|) := by
  rw [← toReal_mem_Ioo_iff_sign_pos] at hθs hψs
  have : ((θ + ψ).toReal : Angle) = ↑(θ.toReal + ψ.toReal) := by simp
  obtain ⟨k, hk⟩ := angle_eq_iff_two_pi_dvd_sub.mp this
  obtain (h | h) : (θ + ψ).toReal <= 0 ∨ θ + ψ = π := by
    have := (θ + ψ).sign.trichotomy
    grind [sign_eq_zero_iff, toReal_eq_zero_iff, toReal_neg_iff_sign_neg]
· obtain rfl : k = -1 := IsStrictOrderedRing.int_eq_of_mul_mem_Ioo two_pi_pos by
      grind [toReal_mem_Ioc]
    grind [abs_of_nonpos]
  · simp_all only [sign_coe_pi, ne_eq, zero_ne_one, not_false_eq_true, toReal_pi, coe_add,
      coe_toReal, pi_pos, abs_of_pos]
    obtain rfl : k = 0 := IsStrictOrderedRing.int_eq_of_mul_mem_Ioo two_pi_pos (by grind)
    grind

/--
lemma `abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal` / 引理 `abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal`

English:
lemma abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal
  statement: {θ ψ : Angle} (hs : θ.sign = ψ.sign)
  proof: by
  obtain h | h | h := θ.sign.trichotomy
  · obtain ⟨hθ', hψ'⟩ : (-θ).sign = 1 ∧ (-ψ).sign = 1 := by grind [sign_neg, neg_neg]
    have hsa' : (-θ + -ψ).sign != 1 := by
      rwa [← hθ', ne_comm, ← neg_add, sign_neg, sign_neg, neg_injective.ne_iff]
    convert! abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux hθ' hψ' hsa' using 1
    all_goals simp [-neg_add_rev, ← neg_add, abs_toReal_neg]
  · grind [sign_eq_zero_iff, coe_pi_add_coe_pi]
  · exact abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux h (hs ▸ h) (h ▸ hsa.symm)

中文:
引理 abs_to实数_add_eq_two_pi_sub_abs_to实数_add_abs_to实数
  结论: {θ ψ : Angle} (hs : θ.sign = ψ.sign)
  证明: by
  obtain h | h | h := θ.sign.trichotomy
  · obtain ⟨hθ', hψ'⟩ : (-θ).sign = 1 ∧ (-ψ).sign = 1 := by grind [sign_neg, neg_neg]
    have hsa' : (-θ + -ψ).sign != 1 := by
      rwa [← hθ', ne_comm, ← neg_add, sign_neg, sign_neg, neg_injective.ne_iff]
    convert! abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux hθ' hψ' hsa' using 1
    all_goals simp [-neg_add_rev, ← neg_add, abs_toReal_neg]
  · grind [sign_eq_zero_iff, coe_pi_add_coe_pi]
  · exact abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux h (hs ▸ h) (h ▸ hsa.symm)

Depends on / 依赖: abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux, abs_toReal_neg, all_goals, coe_pi_add_coe_pi, convert, ne_comm, ne_iff, neg_add, neg_add_rev, neg_injective, neg_injective.ne_iff, neg_neg, sign.trichotomy, sign_eq_zero_iff, sign_neg, trichotomy
-/
lemma abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal {θ ψ : Angle} (hs : θ.sign = ψ.sign)
    (hsa : θ.sign != (θ + ψ).sign) : |(θ + ψ).toReal| = 2 * π - (|θ.toReal| + |ψ.toReal|) := by
  obtain h | h | h := θ.sign.trichotomy
  · obtain ⟨hθ', hψ'⟩ : (-θ).sign = 1 ∧ (-ψ).sign = 1 := by grind [sign_neg, neg_neg]
    have hsa' : (-θ + -ψ).sign != 1 := by
      rwa [← hθ', ne_comm, ← neg_add, sign_neg, sign_neg, neg_injective.ne_iff]
    convert! abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux hθ' hψ' hsa' using 1
    all_goals simp [-neg_add_rev, ← neg_add, abs_toReal_neg]
  · grind [sign_eq_zero_iff, coe_pi_add_coe_pi]
  · exact abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux h (hs ▸ h) (h ▸ hsa.symm)

/--
theorem `continuousAt_sign` / 定理 `continuousAt_sign`

English:
theorem continuousAt_sign
  given: {θ : Angle} (h0 : θ != 0) (hpi : θ != π)
  statement: ContinuousAt sign θ
  proof: (continuousAt_sign_of_ne_zero (sin_ne_zero_iff.2 ⟨h0, hpi⟩)).comp continuous_sin.continuousAt

中文:
定理 continuousAt_sign
  条件: {θ : Angle} (h0 : θ != 0) (hpi : θ != π)
  结论: ContinuousAt sign θ
  证明: (continuousAt_sign_of_ne_zero (sin_ne_zero_iff.2 ⟨h0, hpi⟩)).comp continuous_sin.continuousAt

Depends on / 依赖: continuousAt, continuousAt_sign_of_ne_zero, continuous_sin, continuous_sin.continuousAt, sin_ne_zero_iff
-/
theorem continuousAt_sign {θ : Angle} (h0 : θ != 0) (hpi : θ != π) : ContinuousAt sign θ :=
  (continuousAt_sign_of_ne_zero (sin_ne_zero_iff.2 ⟨h0, hpi⟩)).comp continuous_sin.continuousAt

/--
theorem `_root_.ContinuousOn.angle_sign_comp` / 定理 `_root_.ContinuousOn.angle_sign_comp`

English:
theorem _root_.ContinuousOn.angle_sign_comp
  statement: {α : Type*} [TopologicalSpace α] {f : α -> Angle}
  proof: by
  refine (continuousOn_of_forall_continuousAt fun θ hθ => ?_).comp hf (Set.mapsTo_image f s)
  obtain ⟨z, hz, rfl⟩ := hθ
  exact continuousAt_sign (hs _ hz).1 (hs _ hz).2

中文:
定理 _root_.ContinuousOn.angle_sign_comp
  结论: {α : 类型} [拓扑空间 α] {f : α -> Angle}
  证明: by
  refine (continuousOn_of_forall_continuousAt fun θ hθ => ?_).comp hf (Set.mapsTo_image f s)
  obtain ⟨z, hz, rfl⟩ := hθ
  exact continuousAt_sign (hs _ hz).1 (hs _ hz).2

Depends on / 依赖: Set.mapsTo_image, continuousAt_sign, continuousOn_of_forall_continuousAt, mapsTo_image
-/
theorem _root_.ContinuousOn.angle_sign_comp {α : Type*} [TopologicalSpace α] {f : α -> Angle}
    {s : Set α} (hf : ContinuousOn f s) (hs : forall z in s, f z != 0 ∧ f z != π) :
    ContinuousOn (sign ∘ f) s := by
  refine (continuousOn_of_forall_continuousAt fun θ hθ => ?_).comp hf (Set.mapsTo_image f s)
  obtain ⟨z, hz, rfl⟩ := hθ
  exact continuousAt_sign (hs _ hz).1 (hs _ hz).2

/--
theorem `sign_eq_of_continuousOn` / 定理 `sign_eq_of_continuousOn`

English:
theorem sign_eq_of_continuousOn
  statement: {α : Type*} [TopologicalSpace α] {f : α -> Angle} {s : Set α}
  proof: (hc.image _ (hf.angle_sign_comp hs)).isPreconnected.subsingleton (Set.mem_image_of_mem _ hy)
    (Set.mem_image_of_mem _ hx)

中文:
定理 sign_eq_of_continuousOn
  结论: {α : 类型} [拓扑空间 α] {f : α -> Angle} {s : 集合 α}
  证明: (hc.image _ (hf.angle_sign_comp hs)).isPreconnected.subsingleton (Set.mem_image_of_mem _ hy)
    (Set.mem_image_of_mem _ hx)

Depends on / 依赖: Set.mem_image_of_mem, angle_sign_comp, hc.image, hf.angle_sign_comp, isPreconnected, isPreconnected.subsingleton, mem_image_of_mem, subsingleton
-/
theorem sign_eq_of_continuousOn {α : Type*} [TopologicalSpace α] {f : α -> Angle} {s : Set α}
    {x y : α} (hc : IsConnected s) (hf : ContinuousOn f s) (hs : forall z in s, f z != 0 ∧ f z != π)
    (hx : x in s) (hy : y in s) : (f y).sign = (f x).sign :=
  (hc.image _ (hf.angle_sign_comp hs)).isPreconnected.subsingleton (Set.mem_image_of_mem _ hy)
    (Set.mem_image_of_mem _ hx)

end Angle

end Real
