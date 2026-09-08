/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Sphere.Tangent

/-!
# Angles in circles and spheres

This file proves results about angles in circles and spheres.

-/

public section


noncomputable section

open Module Complex

open scoped EuclideanGeometry Real RealInnerProductSpace ComplexConjugate

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- The angle at the center of a circle equals twice the angle at the circumference, oriented vector
angle form. -/
/-
**Orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq** 是 Mathlib 中的一个定理，位于命名空
间 `Orientation`。
形式化陈述：oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x != y) (hx
zne : x != z) (hxy : ‖x‖ = ‖y‖) (hxz : ‖x‖ = ‖z‖) : o.oangle y z = (2 : Int) • o
.oangle (y - x) (z - x)
参数：hxyne : x != y；hxzne : x != z；hxy : ‖x‖ = ‖y‖；hxz : ‖x‖ = ‖z‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Orientation.oangle_sub_left`：oangle_sub_left {x y z : V} (hx : x != 0) (
hy : y != 0) (hz : z != 0) : o.oangle x z - o.oangle x y = o.oangle y z
· 使用定理 `Orientation.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq`：oangle_eq_
pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x != y) (h : ‖x‖ = ‖y‖) :
 o.oangle y x = π - (2 : Int) • o.oangle (y - x) y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `_private.Mathlib.Geometry.Euclidean.Angle.Sphere.0.Orientation.oangle_eq
_two_zsmul_oangle_sub_of_norm_eq._abel_1_1`：∀ {V : Type u_1} [inst : NormedAddCo
mmGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V =
 2)]   (o : Orientation …
· 使用定理 `Orientation.oangle_sub_right`：oangle_sub_right {x y z : V} (hx : x != 0)
 (hy : y != 0) (hz : z != 0) : o.oangle x z - o.oangle y z = o.oangle x y
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `Orientation.oangle_neg_neg`：oangle_neg_neg (x y : V) : o.oangle (-x) (-y
) = o.oangle x y
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a

--- 原说明 ---
The angle at the center of a circle equals twice the angle at the circumference,
 oriented vector
angle form.
-/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
    (hxy : ‖x‖ = ‖y‖) (hxz : ‖x‖ = ‖z‖) : o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at hxy
    exact hxyne hxy
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy)
  have hz : z ≠ 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx)
  calc
    o.oangle y z = o.oangle x z - o.oangle x y := (o.oangle_sub_left hx hy hz).symm
    _ = π - (2 : ℤ) • o.oangle (x - z) x - (π - (2 : ℤ) • o.oangle (x - y) x) := by
      rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxzne.symm hxz.symm,
        o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxyne.symm hxy.symm]
    _ = (2 : ℤ) • (o.oangle (x - y) x - o.oangle (x - z) x) := by abel
    _ = (2 : ℤ) • o.oangle (x - y) (x - z) := by
      rw [o.oangle_sub_right (sub_ne_zero_of_ne hxyne) (sub_ne_zero_of_ne hxzne) hx]
    _ = (2 : ℤ) • o.oangle (y - x) (z - x) := by rw [← oangle_neg_neg, neg_sub, neg_sub]

/-- The angle at the center of a circle equals twice the angle at the circumference, oriented vector
angle form with the radius specified. -/
/-
**Orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real** 是 Mathlib 中的一个定理，
位于命名空间 `Orientation`。
形式化陈述：oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x != y
) (hxzne : x != z) {r : Real} (hx : ‖x‖ = r) (hy : ‖y‖ = r) (hz : ‖z‖ = r) : o.o
angle y z = (2 : Int) • o.oangle (y - x) (z - x)
参数：hxyne : x != y；hxzne : x != z；hx : ‖x‖ = r；hy : ‖y‖ = r；hz : ‖z‖ = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq`：oangle_eq_two_zsm
ul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x != y) (hxzne : x != z) (hxy : ‖x
‖ = ‖y‖) (hxz : ‖x‖ = ‖z‖) : o.oangle y z =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The angle at the center of a circle equals twice the angle at the circumference,
 oriented vector
angle form with the radius specified.
-/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
    {r : ℝ} (hx : ‖x‖ = r) (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
    o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)

/-- Oriented vector angle version of "angles in same segment are equal" and "opposite angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same
result), represented here as equality of twice the angles. -/
/-
**Orientation.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq** 是 Mathli
b 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (h
x₁yne : x₁ != y) (hx₁zne : x₁ != z) (hx₂yne : x₂ != y) (hx₂zne : x₂ != z) {r : R
eal} (hx₁ : ‖x₁‖ = r) (hx₂ : ‖x₂‖ = r) (hy : ‖y‖ = r) (hz : ‖z‖ = r) : (2 : Int)
 • o.oangle (y - x₁) (z - x₁) = (2 : Int) • o.oangle (y - x₂) (z - x₂)
参数：hx₁yne : x₁ != y；hx₁zne : x₁ != z；hx₂yne : x₂ != y；hx₂zne : x₂ != z；hx₁ : ‖x₁
‖ = r；hx₂ : ‖x₂‖ = r；hy : ‖y‖ = r；hz : ‖z‖ = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real`：oangle_eq_tw
o_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x != y) (hxzne : x != z)
 {r : Real} (hx : ‖x‖ = r) (hy : ‖y‖ = r) (hz : …

--- 原说明 ---
Oriented vector angle version of "angles in same segment are equal" and "opposit
e angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are
 the same
result), represented here as equality of twice the angles.
-/
theorem two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ ≠ y)
    (hx₁zne : x₁ ≠ z) (hx₂yne : x₂ ≠ y) (hx₂zne : x₂ ≠ z) {r : ℝ} (hx₁ : ‖x₁‖ = r) (hx₂ : ‖x₂‖ = r)
    (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
    (2 : ℤ) • o.oangle (y - x₁) (z - x₁) = (2 : ℤ) • o.oangle (y - x₂) (z - x₂) :=
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
    o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz

end Orientation

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Sphere

open Real InnerProductSpace InnerProductGeometry

/-- **Thales' theorem**: The angle inscribed in a semicircle is a right angle. -/
/-
**EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter** 是 
Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter {p₁ p₂ p₃ : P} {s : Spher
e P} (hd : s.IsDiameter p₁ p₃) : ∠ p₁ p₂ p₃ = π / 2 ↔ p₂ in s
参数：hd : s.IsDiameter p₁ p₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.midpoint_eq_center`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAddTorso…
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `left_vsub_midpoint`：left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁
 p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
· 使用定理 `right_vsub_midpoint`：right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R 
p₁ p₂ = (⅟2 : R) • (p₂ -ᵥ p₁)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
**Thales' theorem**: The angle inscribed in a semicircle is a right angle.
-/
theorem angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter {p₁ p₂ p₃ : P} {s : Sphere P}
    (hd : s.IsDiameter p₁ p₃) :
    ∠ p₁ p₂ p₃ = π / 2 ↔ p₂ ∈ s := by
  rw [mem_sphere', EuclideanGeometry.angle,
    ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  let o := s.center
  have h_center : o = midpoint ℝ p₁ p₃ := hd.midpoint_eq_center.symm
  rw [← vsub_add_vsub_cancel p₁ o p₂, ← vsub_add_vsub_cancel p₃ o p₂,
    inner_add_left, inner_add_right, inner_add_right]
  have h_opp : p₁ -ᵥ o = -(p₃ -ᵥ o) := by
    rw [h_center, left_vsub_midpoint, right_vsub_midpoint, ← smul_neg, neg_vsub_eq_vsub_rev]
  rw [h_opp, inner_neg_left, inner_neg_left, real_inner_comm (p₃ -ᵥ o) (o -ᵥ p₂)]
  ring_nf
  rw [neg_add_eq_zero, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub,
    real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub, sq_eq_sq₀ dist_nonneg dist_nonneg,
    mem_sphere.mp hd.right_mem]
  exact eq_comm

/-- **Thales' theorem**: For three distinct points, the angle at the second point
is a right angle if and only if the second point lies on the sphere having the first and third
points as diameter endpoints. -/
/-
**EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter** 是 Mat
hlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：angle_eq_pi_div_two_iff_mem_sphere_ofDiameter {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ 
= π / 2 ↔ p₂ in Sphere.ofDiameter p₁ p₃
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_of_isDiamete
r`：angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter {p₁ p₂ p₃ : P} {s : Sphere P
} (hd : s.IsDiameter p₁ p₃) : ∠ p₁ p₂ p₃ = π / 2 ↔ p₂ in s
· 使用引理 `EuclideanGeometry.Sphere.isDiameter_ofDiameter`：isDiameter_ofDiameter (p
₁ p₂ : P) : (Sphere.ofDiameter p₁ p₂).IsDiameter p₁ p₂

--- 原说明 ---
**Thales' theorem**: For three distinct points, the angle at the second point
is a right angle if and only if the second point lies on the sphere having the f
irst and third
points as diameter endpoints.
-/
theorem angle_eq_pi_div_two_iff_mem_sphere_ofDiameter {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = π / 2 ↔ p₂ ∈ Sphere.ofDiameter p₁ p₃ :=
  angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter (Sphere.isDiameter_ofDiameter p₁ p₃)

alias thales_theorem := angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter

/-- Converse of Thales' theorem in 2D: if three distinct points on a circle
    form a right angle, then the chord is a diameter. -/
/-
**EuclideanGeometry.Sphere.isDiameter_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：isDiameter_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} {s : Sphere P} [Fact (fin
rank Real V = 2)] (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hne₁₂ : p₁ !=
 p₂) (hne₂₃ : p₂ != p₃) (hangle : ∠ p₁ p₂ p₃ = π / 2) : s.IsDiameter p₁ p₃
参数：finrank Real V = 2；hp₁ : p₁ in s；hp₂ : p₂ in s；hp₃ : p₃ in s；hne₁₂ : p₁ != p₂
；hne₂₃ : p₂ != p₃；hangle : ∠ p₁ p₂ p₃ = π / 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FiniteDimensional.of_finrank_eq_succ`：of_finrank_eq_succ {n : Nat} (hn :
 finrank K V = n.succ) : FiniteDimensional K V
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
Converse of Thales' theorem in 2D: if three distinct points on a circle
    form a right angle, then the chord is a diameter.
-/
theorem isDiameter_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} {s : Sphere P}
    [Fact (finrank ℝ V = 2)]
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s)
    (hne₁₂ : p₁ ≠ p₂) (hne₂₃ : p₂ ≠ p₃)
    (hangle : ∠ p₁ p₂ p₃ = π / 2) :
    s.IsDiameter p₁ p₃ := by
  have : FiniteDimensional ℝ V := .of_finrank_eq_succ (Fact.out : finrank ℝ V = 2)
  have hne₁₃ : p₁ ≠ p₃ := fun h ↦ by
    rw [h, angle_self_of_ne hne₂₃.symm] at hangle; linarith [Real.pi_pos]
  have hd := Sphere.isDiameter_ofDiameter p₁ p₃
  have h_eq : s = Sphere.ofDiameter p₁ p₃ := by
    by_contra hne
    have := eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (Fact.out : finrank ℝ V = 2) hne hne₁₃ hp₁ hp₃ hp₂
      hd.left_mem hd.right_mem (angle_eq_pi_div_two_iff_mem_sphere_ofDiameter.mp hangle)
    exact this.elim hne₁₂.symm hne₂₃
  exact h_eq ▸ hd

/-- On a sphere of nonzero radius, the central angle `∠ p₁ s.center p₂` equals `π` iff
`p₁` and `p₂` are diametrically opposite. -/
/-
**EuclideanGeometry.Sphere.angle_center_eq_pi_iff_isDiameter** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：angle_center_eq_pi_iff_isDiameter {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in 
s) (hp₂ : p₂ in s) (hr : s.radius != 0) : ∠ p₁ s.center p₂ = π ↔ s.IsDiameter p₁
 p₂
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；hr : s.radius != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_eq_pi_iff_sbtw`：angle_eq_pi_iff_sbtw {p₁ p₂ p₃ :
 P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EuclideanGeometry.Sphere.isDiameter_iff_mem_and_mem_and_wbtw`：isDiameter
_iff_mem_and_mem_and_wbtw : s.IsDiameter p₁ p₂ ↔ p₁ in s ∧ p₂ in s ∧ Wbtw Real p
₁ s.center p₂
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.sbtw`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAddTorso…

--- 原说明 ---
On a sphere of nonzero radius, the central angle `∠ p₁ s.center p₂` equals `π` i
ff
`p₁` and `p₂` are diametrically opposite.
-/
theorem angle_center_eq_pi_iff_isDiameter {s : Sphere P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hr : s.radius ≠ 0) :
    ∠ p₁ s.center p₂ = π ↔ s.IsDiameter p₁ p₂ := by
  rw [angle_eq_pi_iff_sbtw]
  exact ⟨fun h => isDiameter_iff_mem_and_mem_and_wbtw.2 ⟨hp₁, hp₂, h.wbtw⟩, fun h => h.sbtw hr⟩

/-- On a sphere of nonzero radius, the central angle `∠ p₁ s.center p₂` equals zero iff
`p₁ = p₂`. -/
/-
**EuclideanGeometry.Sphere.angle_center_eq_zero_iff_eq** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry.Sphere`。
形式化陈述：angle_center_eq_zero_iff_eq {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp
₂ : p₂ in s) (hr : s.radius != 0) : ∠ p₁ s.center p₂ = 0 ↔ p₁ = p₂
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；hr : s.radius != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_left_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T
 : AddTorsor G P] {p₁ p₂ p : P}, p₁ -ᵥ p = p₂ -ᵥ p → p₁ = p₂
· 使用引理 `InnerProductGeometry.eq_of_angle_eq_zero_of_norm_eq`：eq_of_angle_eq_zero
_of_norm_eq {x y : V} (hxy : angle x y = 0) (h : ‖x‖ = ‖y‖) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.norm_vsub_center_eq_radius`：norm_vsub_center_eq_radius
 {s : Sphere P} {p : P} (hp : p in s) : ‖p -ᵥ s.center‖ = s.radius
· 使用定理 `EuclideanGeometry.angle_self_of_ne`：angle_self_of_ne (h : p != p₀) : ∠ p
 p₀ p = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.Sphere.center_mem_iff`：∀ {P : Type u_2} [inst : Metric
Space P] {s : EuclideanGeometry.Sphere P}, s.center ∈ s ↔ s.radius = 0

--- 原说明 ---
On a sphere of nonzero radius, the central angle `∠ p₁ s.center p₂` equals zero 
iff
`p₁ = p₂`.
-/
theorem angle_center_eq_zero_iff_eq {s : Sphere P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hr : s.radius ≠ 0) :
    ∠ p₁ s.center p₂ = 0 ↔ p₁ = p₂ := by
  constructor
  · intro h
    refine vsub_left_cancel (eq_of_angle_eq_zero_of_norm_eq (by simpa [angle] using h) ?_)
    rw [norm_vsub_center_eq_radius hp₁, norm_vsub_center_eq_radius hp₂]
  · rintro rfl
    exact angle_self_of_ne fun h => hr (center_mem_iff.mp (h ▸ hp₁))

/-- For a tangent line to a sphere, the angle between the line and the radius at the tangent point
equals `π / 2`. -/
/-
**EuclideanGeometry.Sphere.IsTangentAt.angle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p q : P} {as : AffineSubspace ℝ P},   s.IsTange
ntAt p as → q ∈ as → EuclideanGeometry.angle q p s.center = Real.pi / 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.inner_left_eq_zero_of_mem`：∀ {V : T
ype u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpac
e ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `InnerProductGeometry.angle_neg_right`：angle_neg_right (x y : V) : angle 
x (-y) = π - angle x y
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
For a tangent line to a sphere, the angle between the line and the radius at the
 tangent point
equals `π / 2`.
-/
theorem IsTangentAt.angle_eq_pi_div_two {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) (hq_mem : q ∈ as) :
    ∠ q p s.center = π / 2 := by
  have h1 := IsTangentAt.inner_left_eq_zero_of_mem h hq_mem
  rw [inner_eq_zero_iff_angle_eq_pi_div_two] at h1
  rw [angle, ← neg_vsub_eq_vsub_rev _ s.center, angle_neg_right, h1]
  linarith

/-- If the angle between the line `p q` and the radius at `p` equals `π / 2`, then the line `p q` is
tangent to the sphere at `p`. -/
/-
**EuclideanGeometry.Sphere.IsTangentAt_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：IsTangentAt_of_angle_eq_pi_div_two {s : Sphere P} {p q : P} (h : ∠ q p s.c
enter = π / 2) (hp : p in s) : s.IsTangentAt p line[Real, p, q]
参数：h : ∠ q p s.center = π / 2；hp : p in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `affineSpan_le`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ri
ng k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V 
P] …

--- 原说明 ---
If the angle between the line `p q` and the radius at `p` equals `π / 2`, then t
he line `p q` is
tangent to the sphere at `p`.
-/
theorem IsTangentAt_of_angle_eq_pi_div_two {s : Sphere P} {p q : P} (h : ∠ q p s.center = π / 2)
    (hp : p ∈ s) :
    s.IsTangentAt p line[ℝ, p, q] := by
  have hp_mem := left_mem_affineSpan_pair ℝ p q
  refine ⟨hp, hp_mem, ?_⟩
  have h_ortho : ⟪q -ᵥ p, p -ᵥ s.center⟫ = 0 := by
    rwa [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, ← neg_vsub_eq_vsub_rev p s.center,
      inner_neg_right, neg_eq_zero] at h
  have hq : q ∈ s.orthRadius p := by
    simp [Sphere.mem_orthRadius_iff_inner_left, h_ortho]
  rw [affineSpan_le]
  have hp : p ∈ s.orthRadius p := by
    simp [Sphere.self_mem_orthRadius]
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hp, hq⟩

/-- A line through `p` is tangent to the sphere at `p` if and only if the angle between the line and
the radius at `p` equals `π / 2`. -/
/-
**EuclideanGeometry.Sphere.IsTangentAt_iff_angle_eq_pi_div_two** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：IsTangentAt_iff_angle_eq_pi_div_two {s : Sphere P} {p q : P} (hp : p in s)
 : s.IsTangentAt p line[Real, p, q] ↔ ∠ q p s.center = π / 2
参数：hp : p in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.angle_eq_pi_div_two`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt_of_angle_eq_pi_div_two`：IsTangentAt
_of_angle_eq_pi_div_two {s : Sphere P} {p q : P} (h : ∠ q p s.center = π / 2) (h
p : p in s) : s.IsTangentAt p line[Real, p, q]

--- 原说明 ---
A line through `p` is tangent to the sphere at `p` if and only if the angle betw
een the line and
the radius at `p` equals `π / 2`.
-/
theorem IsTangentAt_iff_angle_eq_pi_div_two {s : Sphere P} {p q : P} (hp : p ∈ s) :
    s.IsTangentAt p line[ℝ, p, q] ↔ ∠ q p s.center = π / 2 := by
  exact ⟨fun h ↦ IsTangentAt.angle_eq_pi_div_two h (right_mem_affineSpan_pair ℝ p q),
    fun h ↦ IsTangentAt_of_angle_eq_pi_div_two h hp⟩

end Sphere

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

local notation "o" => Module.Oriented.positiveOrientation

namespace Sphere

/-- The angle at the center of a circle equals twice the angle at the circumference, oriented angle
version. -/
/-
**EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：oangle_center_eq_two_zsmul_oangle {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ 
in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₂p₁ : p₂ != p₁) (hp₂p₃ : p₂ != p₃) : ∡ 
p₁ s.center p₃ = (2 : Int) • ∡ p₁ p₂ p₃
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；hp₃ : p₃ in s；hp₂p₁ : p₂ != p₁；hp₂p₃ : p₂ != p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `Orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real`：oangle_eq_tw
o_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x != y) (hxzne : x != z)
 {r : Real} (hx : ‖x‖ = r) (hy : ‖y‖ = r) (hz : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The angle at the center of a circle equals twice the angle at the circumference,
 oriented angle
version.
-/
theorem oangle_center_eq_two_zsmul_oangle {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃) :
    ∡ p₁ s.center p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃ := by
  rw [mem_sphere, @dist_eq_norm_vsub V] at hp₁ hp₂ hp₃
  rw [oangle, oangle, o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real _ _ hp₂ hp₁ hp₃] <;>
    simp [hp₂p₁, hp₂p₃]

/-- Oriented angle version of "angles in same segment are equal" and "opposite angles of a
cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result),
represented here as equality of twice the angles. -/
/-
**EuclideanGeometry.Sphere.two_zsmul_oangle_eq** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry.Sphere`。
形式化陈述：two_zsmul_oangle_eq {s : Sphere P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in s) (hp₂ 
: p₂ in s) (hp₃ : p₃ in s) (hp₄ : p₄ in s) (hp₂p₁ : p₂ != p₁) (hp₂p₄ : p₂ != p₄)
 (hp₃p₁ : p₃ != p₁) (hp₃p₄ : p₃ != p₄) : (2 : Int) • ∡ p₁ p₂ p₄ = (2 : Int) • ∡ 
p₁ p₃ p₄
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；hp₃ : p₃ in s；hp₄ : p₄ in s；hp₂p₁ : p₂ != p₁；hp₂p
₄ : p₂ != p₄；hp₃p₁ : p₃ != p₁；hp₃p₄ : p₃ != p₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Orientation.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq`：two
_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x
₁ != y) (hx₁zne : x₁ != z) (hx₂yne : x₂ != y) (hx₂zne : x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Oriented angle version of "angles in same segment are equal" and "opposite angle
s of a
cyclic quadrilateral add to π", for oriented angles mod π (for which those are t
he same result),
represented here as equality of twice the angles.
-/
theorem two_zsmul_oangle_eq {s : Sphere P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (hp₃ : p₃ ∈ s) (hp₄ : p₄ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₄ : p₂ ≠ p₄) (hp₃p₁ : p₃ ≠ p₁)
    (hp₃p₄ : p₃ ≠ p₄) : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄ := by
  rw [mem_sphere, @dist_eq_norm_vsub V] at hp₁ hp₂ hp₃ hp₄
  rw [oangle, oangle, ← vsub_sub_vsub_cancel_right p₁ p₂ s.center, ←
      vsub_sub_vsub_cancel_right p₄ p₂ s.center,
      o.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq _ _ _ _ hp₂ hp₃ hp₁ hp₄] <;>
    simp [hp₂p₁, hp₂p₄, hp₃p₁, hp₃p₄]

end Sphere

/-- Oriented angle version of "angles in same segment are equal" and "opposite angles of a
cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result),
represented here as equality of twice the angles. -/
/-
**EuclideanGeometry.Cospherical.two_zsmul_oangle_eq** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry.Cospherical`。
形式化陈述：∀ {V : Type u_3} {P : Type u_4} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] [
hd2 : Fact (Module.finrank ℝ V = 2)] [inst_4 : Module.Oriented ℝ V (Fin 2)]   {p
₁ p₂ p₃ p₄ : P},   EuclideanGeometry.Cospherical {p₁, p₂, p₃, p₄} →     p₂ ≠ p₁ 
→       p₂ ≠ p₄ → p₃ ≠ p₁ → p₃ ≠ p₄ → 2 • EuclideanGeometry.oangle p₁ p₂ p₄ = 2 
• EuclideanGeometry.oangle p₁ p₃ p₄
参数：Module.finrank ℝ V = 2；Fin 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.cospherical_iff_exists_sphere`：cospherical_iff_exists_
sphere {ps : Set P} : Cospherical ps ↔ exists s : Sphere P, ps subseteq (s : Set
 P)
· 使用定理 `EuclideanGeometry.Sphere.two_zsmul_oangle_eq`：two_zsmul_oangle_eq {s : S
phere P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₄ 
: p₄ in s) (hp₂p₁ : p₂ != p₁) (hp₂…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Oriented angle version of "angles in same segment are equal" and "opposite angle
s of a
cyclic quadrilateral add to π", for oriented angles mod π (for which those are t
he same result),
represented here as equality of twice the angles.
-/
theorem Cospherical.two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : Cospherical ({p₁, p₂, p₃, p₄} : Set P)) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₄ : p₂ ≠ p₄)
    (hp₃p₁ : p₃ ≠ p₁) (hp₃p₄ : p₃ ≠ p₄) : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄ := by
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.1 h
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff, Sphere.mem_coe] at hs
  exact Sphere.two_zsmul_oangle_eq hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hp₂p₁ hp₂p₄ hp₃p₁ hp₃p₄

namespace Sphere

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form where the apex is given as the center of a circle. -/
/-
**EuclideanGeometry.Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left** 是 Mat
hlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：oangle_eq_pi_sub_two_zsmul_oangle_center_left {s : Sphere P} {p₁ p₂ : P} (
hp₁ : p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : ∡ p₁ s.center p₂ = π - (2 : Int)
 • ∡ s.center p₂ p₁
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；h : p₁ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq`：oangle_e
q_pi_sub_two_zsmul_oangle_of_dist_eq {p₁ p₂ p₃ : P} (hn : p₂ != p₃) (h : dist p₁
 p₂ = dist p₁ p₃) : ∡ p₃ p₁ p₂ = π - (2 : Int) • ∡ p…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere'`：dist_center
_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s) (hp₂ :
 p₂ in s) : dist s.center p₁ = dist s.center p₂

--- 原说明 ---
The angle at the apex of an isosceles triangle is `π` minus twice a base angle, 
oriented
angle-at-point form where the apex is given as the center of a circle.
-/
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_left {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : ∡ p₁ s.center p₂ = π - (2 : ℤ) • ∡ s.center p₂ p₁ := by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq h.symm
      (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form where the apex is given as the center of a circle. -/
/-
**EuclideanGeometry.Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_right** 是 Ma
thlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：oangle_eq_pi_sub_two_zsmul_oangle_center_right {s : Sphere P} {p₁ p₂ : P} 
(hp₁ : p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : ∡ p₁ s.center p₂ = π - (2 : Int
) • ∡ p₂ p₁ s.center
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；h : p₁ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left`：
oangle_eq_pi_sub_two_zsmul_oangle_center_left {s : Sphere P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : ∡ p₁ s.center p₂ =…
· 使用定理 `EuclideanGeometry.oangle_eq_oangle_of_dist_eq`：oangle_eq_oangle_of_dist_
eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) : ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁
· 使用定理 `EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere'`：dist_center
_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s) (hp₂ :
 p₂ in s) : dist s.center p₁ = dist s.center p₂

--- 原说明 ---
The angle at the apex of an isosceles triangle is `π` minus twice a base angle, 
oriented
angle-at-point form where the apex is given as the center of a circle.
-/
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_right {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : ∡ p₁ s.center p₂ = π - (2 : ℤ) • ∡ p₂ p₁ s.center := by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_center_left hp₁ hp₂ h,
    oangle_eq_oangle_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

/-- Twice a base angle of an isosceles triangle with apex at the center of a circle, plus twice
the angle at the apex of a triangle with the same base but apex on the circle, equals `π`. -/
/-
**EuclideanGeometry.Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi** 
是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi {s : Sphere P} {p₁ p₂ p
₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₂p₁ : p₂ != p₁) (hp₂p₃
 : p₂ != p₃) (hp₁p₃ : p₁ != p₃) : (2 : Int) • ∡ p₃ p₁ s.center + (2 : Int) • ∡ p
₁ p₂ p₃ = π
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；hp₃ : p₃ in s；hp₂p₁ : p₂ != p₁；hp₂p₃ : p₂ != p₃；h
p₁p₃ : p₁ != p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle`：oangle_cente
r_eq_two_zsmul_oangle {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in
 s) (hp₃ : p₃ in s) (hp₂p₁ : p₂ != p₁) (hp₂p₃ : …
· 使用定理 `EuclideanGeometry.Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_right`
：oangle_eq_pi_sub_two_zsmul_oangle_center_right {s : Sphere P} {p₁ p₂ : P} (hp₁ 
: p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : ∡ p₁ s.center p₂ …
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
Twice a base angle of an isosceles triangle with apex at the center of a circle,
 plus twice
the angle at the apex of a triangle with the same base but apex on the circle, e
quals `π`.
-/
theorem two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi {s : Sphere P} {p₁ p₂ p₃ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃)
    (hp₁p₃ : p₁ ≠ p₃) : (2 : ℤ) • ∡ p₃ p₁ s.center + (2 : ℤ) • ∡ p₁ p₂ p₃ = π := by
  rw [← oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃,
    oangle_eq_pi_sub_two_zsmul_oangle_center_right hp₁ hp₃ hp₁p₃, add_sub_cancel]

/-- A base angle of an isosceles triangle with apex at the center of a circle is acute. -/
/-
**EuclideanGeometry.Sphere.abs_oangle_center_left_toReal_lt_pi_div_two** 是 Mathl
ib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：abs_oangle_center_left_toReal_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp
₁ : p₁ in s) (hp₂ : p₂ in s) : |(∡ s.center p₂ p₁).toReal| < π / 2
参数：hp₁ : p₁ in s；hp₂ : p₂ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq`：abs_
oangle_right_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = di
st p₁ p₃) : |(∡ p₁ p₂ p₃).toReal| < π / 2
· 使用定理 `EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere'`：dist_center
_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s) (hp₂ :
 p₂ in s) : dist s.center p₁ = dist s.center p₂

--- 原说明 ---
A base angle of an isosceles triangle with apex at the center of a circle is acu
te.
-/
theorem abs_oangle_center_left_toReal_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : |(∡ s.center p₂ p₁).toReal| < π / 2 :=
  abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

/-- A base angle of an isosceles triangle with apex at the center of a circle is acute. -/
/-
**EuclideanGeometry.Sphere.abs_oangle_center_right_toReal_lt_pi_div_two** 是 Math
lib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：abs_oangle_center_right_toReal_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (h
p₁ : p₁ in s) (hp₂ : p₂ in s) : |(∡ p₂ p₁ s.center).toReal| < π / 2
参数：hp₁ : p₁ in s；hp₂ : p₂ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq`：abs_o
angle_left_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist
 p₁ p₃) : |(∡ p₂ p₃ p₁).toReal| < π / 2
· 使用定理 `EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere'`：dist_center
_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s) (hp₂ :
 p₂ in s) : dist s.center p₁ = dist s.center p₂

--- 原说明 ---
A base angle of an isosceles triangle with apex at the center of a circle is acu
te.
-/
theorem abs_oangle_center_right_toReal_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : |(∡ p₂ p₁ s.center).toReal| < π / 2 :=
  abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

/-- Given two points on a circle, the center of that circle may be expressed explicitly as a
multiple (by half the tangent of the angle between the chord and the radius at one of those
points) of a `π / 2` rotation of the vector between those points, plus the midpoint of those
points. -/
/-
**EuclideanGeometry.Sphere.tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq
_center** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : Sphere P
} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : (Real.Angle.tan (
∡ p₂ p₁ s.center) / 2) • o.rotation (π / 2 : Real) (p₂ -ᵥ p₁) +ᵥ midpoint Real p
₁ p₂ = s.center
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；h : p₁ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint`
：dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint {p₁ p₂ p : P} (h : p₁ != 
p₂) : dist p₁ p = dist p₂ p ↔ exists r : Real, r • o.rotation…
· 使用定理 `EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere`：dist_center_
eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s) (hp₂ : p
₂ in s) : dist p₁ s.center = dist p₂ s.center
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_midpoint_rev_left`：oangle_midpoint_rev_left (p₁
 p₂ p₃ : P) : ∡ (midpoint Real p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.oangle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `midpoint_vsub_left`：midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ
 p₁ = (⅟2 : R) • (p₂ -ᵥ p₁)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.tan_oangle_add_right_smul_rotation_pi_div_two`：tan_oangle_ad
d_right_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) : Real.Angle.ta
n (o.oangle x (x + r • o.rotation (π / 2 : Real…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0

--- 原说明 ---
Given two points on a circle, the center of that circle may be expressed explici
tly as a
multiple (by half the tangent of the angle between the chord and the radius at o
ne of those
points) of a `π / 2` rotation of the vector between those points, plus the midpo
int of those
points.
-/
theorem tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : Sphere P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) :
    (Real.Angle.tan (∡ p₂ p₁ s.center) / 2) • o.rotation (π / 2 : ℝ) (p₂ -ᵥ p₁) +ᵥ
      midpoint ℝ p₁ p₂ = s.center := by
  obtain ⟨r, hr⟩ := (dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint h).1
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)
  rw [← hr, ← oangle_midpoint_rev_left, oangle, vadd_vsub_assoc]
  nth_rw 1 [show p₂ -ᵥ p₁ = (2 : ℝ) • (midpoint ℝ p₁ p₂ -ᵥ p₁) by simp]
  rw [map_smul, smul_smul, add_comm, o.tan_oangle_add_right_smul_rotation_pi_div_two,
    mul_div_cancel_right₀ _ (two_ne_zero' ℝ)]
  simpa using h.symm

/-- Given three points on a circle, the center of that circle may be expressed explicitly as a
multiple (by half the inverse of the tangent of the angle at one of those points) of a `π / 2`
rotation of the vector between the other two points, plus the midpoint of those points. -/
/-
**EuclideanGeometry.Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoin
t_eq_center** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : Sphe
re P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁
 != p₂) (hp₁p₃ : p₁ != p₃) (hp₂p₃ : p₂ != p₃) : ((Real.Angle.tan (∡ p₁ p₂ p₃))⁻¹
 / 2) • o.rotation (π / 2 : Real) (p₃ -ᵥ p₁) +ᵥ midpoint Real p₁ p₃ = s.center
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；hp₃ : p₃ in s；hp₁p₂ : p₁ != p₂；hp₁p₃ : p₁ != p₃；h
p₂p₃ : p₂ != p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi`：tan_eq_inv_of_tw
o_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle} (h : (2 : Int) • θ + (2 : Int) • ψ = π
) : tan ψ = (tan θ)⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `EuclideanGeometry.Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq
_pi`：two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi {s : Sphere P} {p₁ p₂ p₃
 : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₂p₁ : p₂…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `EuclideanGeometry.Sphere.tan_div_two_smul_rotation_pi_div_two_vadd_midpo
int_eq_center`：tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s :
 Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : (Re…

--- 原说明 ---
Given three points on a circle, the center of that circle may be expressed expli
citly as a
multiple (by half the inverse of the tangent of the angle at one of those points
) of a `π / 2`
rotation of the vector between the other two points, plus the midpoint of those 
points.
-/
theorem inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : Sphere P}
    {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃)
    (hp₂p₃ : p₂ ≠ p₃) :
    ((Real.Angle.tan (∡ p₁ p₂ p₃))⁻¹ / 2) • o.rotation (π / 2 : ℝ) (p₃ -ᵥ p₁) +ᵥ midpoint ℝ p₁ p₃ =
      s.center := by
  convert! tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₃ hp₁p₃
  convert! (Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi _).symm
  rw [add_comm,
    two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃]

/-- Given two points on a circle, the radius of that circle may be expressed explicitly as half
the distance between those two points divided by the cosine of the angle between the chord and
the radius at one of those points. -/
/-
**EuclideanGeometry.Sphere.dist_div_cos_oangle_center_div_two_eq_radius** 是 Math
lib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：dist_div_cos_oangle_center_div_two_eq_radius {s : Sphere P} {p₁ p₂ : P} (h
p₁ : p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : dist p₁ p₂ / Real.Angle.cos (∡ p₂
 p₁ s.center) / 2 = s.radius
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；h : p₁ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_right_comm`：div_right_comm : a / b / c = a / c / b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_left_midpoint`：dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜
 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `EuclideanGeometry.Sphere.tan_div_two_smul_rotation_pi_div_two_vadd_midpo
int_eq_center`：tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s :
 Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : (Re…
· 使用定理 `EuclideanGeometry.oangle_midpoint_rev_left`：oangle_midpoint_rev_left (p₁
 p₂ p₃ : P) : ∡ (midpoint Real p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.oangle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `midpoint_vsub_left`：midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ
 p₁ = (⅟2 : R) • (p₂ -ᵥ p₁)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
（共 92 条，此处仅展示前 30 条）

--- 原说明 ---
Given two points on a circle, the radius of that circle may be expressed explici
tly as half
the distance between those two points divided by the cosine of the angle between
 the chord and
the radius at one of those points.
-/
theorem dist_div_cos_oangle_center_div_two_eq_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) :
    dist p₁ p₂ / Real.Angle.cos (∡ p₂ p₁ s.center) / 2 = s.radius := by
  rw [div_right_comm, div_eq_mul_inv _ (2 : ℝ), mul_comm,
    show (2 : ℝ)⁻¹ * dist p₁ p₂ = dist p₁ (midpoint ℝ p₁ p₂) by simp, ← mem_sphere.1 hp₁, ←
    tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₂ h, ←
    oangle_midpoint_rev_left, oangle, vadd_vsub_assoc,
    show p₂ -ᵥ p₁ = (2 : ℝ) • (midpoint ℝ p₁ p₂ -ᵥ p₁) by simp, map_smul, smul_smul,
    div_mul_cancel₀ _ (two_ne_zero' ℝ), @dist_eq_norm_vsub' V, @dist_eq_norm_vsub' V,
    vadd_vsub_assoc, add_comm, o.oangle_add_right_smul_rotation_pi_div_two, Real.Angle.cos_coe,
    Real.cos_arctan]
  · norm_cast
    rw [one_div, div_inv_eq_mul, ← mul_self_inj (by positivity) (by positivity),
      norm_add_sq_eq_norm_sq_add_norm_sq_real (o.inner_smul_rotation_pi_div_two_right _ _),
      ← mul_assoc, mul_comm, mul_comm _ (√_), ← mul_assoc, ← mul_assoc,
      Real.mul_self_sqrt (by positivity), norm_smul, LinearIsometryEquiv.norm_map]
    conv_rhs =>
      rw [← mul_assoc, mul_comm _ ‖Real.Angle.tan _‖, ← mul_assoc, Real.norm_eq_abs,
        abs_mul_abs_self]
    ring
  · simpa using h.symm

/-- Given two points on a circle, twice the radius of that circle may be expressed explicitly as
the distance between those two points divided by the cosine of the angle between the chord and
the radius at one of those points. -/
/-
**EuclideanGeometry.Sphere.dist_div_cos_oangle_center_eq_two_mul_radius** 是 Math
lib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：dist_div_cos_oangle_center_eq_two_mul_radius {s : Sphere P} {p₁ p₂ : P} (h
p₁ : p₁ in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : dist p₁ p₂ / Real.Angle.cos (∡ p₂
 p₁ s.center) = 2 * s.radius
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；h : p₁ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.dist_div_cos_oangle_center_div_two_eq_radius`：d
ist_div_cos_oangle_center_div_two_eq_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁
 in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : dist p₁ p₂ / Real.A…
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
Given two points on a circle, twice the radius of that circle may be expressed e
xplicitly as
the distance between those two points divided by the cosine of the angle between
 the chord and
the radius at one of those points.
-/
theorem dist_div_cos_oangle_center_eq_two_mul_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) :
    dist p₁ p₂ / Real.Angle.cos (∡ p₂ p₁ s.center) = 2 * s.radius := by
  rw [← dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₂ h, mul_div_cancel₀ _ (two_ne_zero' ℝ)]

/-- Given three points on a circle, the radius of that circle may be expressed explicitly as half
the distance between two of those points divided by the absolute value of the sine of the angle
at the third point (a version of the law of sines or sine rule). -/
/-
**EuclideanGeometry.Sphere.dist_div_sin_oangle_div_two_eq_radius** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：dist_div_sin_oangle_div_two_eq_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ :
 p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) (hp₁p₃ : p₁ != p₃) 
(hp₂p₃ : p₂ != p₃) : dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| / 2 = s.radius
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；hp₃ : p₃ in s；hp₁p₂ : p₁ != p₂；hp₁p₃ : p₁ != p₃；h
p₂p₃ : p₂ != p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi`：abs_cos_
eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle} (h : (2 : Int) • θ + (
2 : Int) • ψ = π) : |cos θ| = |sin ψ|
· 使用定理 `EuclideanGeometry.Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq
_pi`：two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi {s : Sphere P} {p₁ p₂ p₃
 : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₂p₁ : p₂…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two`：cos_nonneg_iff_abs_t
oReal_le_pi_div_two {θ : Angle} : 0 <= cos θ ↔ |θ.toReal| <= π / 2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `EuclideanGeometry.Sphere.abs_oangle_center_right_toReal_lt_pi_div_two`：a
bs_oangle_center_right_toReal_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁
 in s) (hp₂ : p₂ in s) : |(∡ p₂ p₁ s.center).toReal| < π / …
· 使用定理 `EuclideanGeometry.Sphere.dist_div_cos_oangle_center_div_two_eq_radius`：d
ist_div_cos_oangle_center_div_two_eq_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁
 in s) (hp₂ : p₂ in s) (h : p₁ != p₂) : dist p₁ p₂ / Real.A…

--- 原说明 ---
Given three points on a circle, the radius of that circle may be expressed expli
citly as half
the distance between two of those points divided by the absolute value of the si
ne of the angle
at the third point (a version of the law of sines or sine rule).
-/
theorem dist_div_sin_oangle_div_two_eq_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| / 2 = s.radius := by
  convert! dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₃ hp₁p₃
  rw [← Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi
    (two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃),
    abs_of_nonneg (Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two.2 _)]
  exact (abs_oangle_center_right_toReal_lt_pi_div_two hp₁ hp₃).le

/-- Given three points on a circle, twice the radius of that circle may be expressed explicitly as
the distance between two of those points divided by the absolute value of the sine of the angle
at the third point (a version of the law of sines or sine rule). -/
/-
**EuclideanGeometry.Sphere.dist_div_sin_oangle_eq_two_mul_radius** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：dist_div_sin_oangle_eq_two_mul_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ :
 p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) (hp₁p₃ : p₁ != p₃) 
(hp₂p₃ : p₂ != p₃) : dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| = 2 * s.radius
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；hp₃ : p₃ in s；hp₁p₂ : p₁ != p₂；hp₁p₃ : p₁ != p₃；h
p₂p₃ : p₂ != p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.dist_div_sin_oangle_div_two_eq_radius`：dist_div
_sin_oangle_div_two_eq_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂
 : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) (hp₁p…
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
Given three points on a circle, twice the radius of that circle may be expressed
 explicitly as
the distance between two of those points divided by the absolute value of the si
ne of the angle
at the third point (a version of the law of sines or sine rule).
-/
theorem dist_div_sin_oangle_eq_two_mul_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| = 2 * s.radius := by
  rw [← dist_div_sin_oangle_div_two_eq_radius hp₁ hp₂ hp₃ hp₁p₂ hp₁p₃ hp₂p₃,
    mul_div_cancel₀ _ (two_ne_zero' ℝ)]

end Sphere

end EuclideanGeometry

namespace Affine

namespace Triangle

open EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

section Oriented

variable [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

local notation "o" => Module.Oriented.positiveOrientation

/-- The circumcenter of a triangle may be expressed explicitly as a multiple (by half the inverse
of the tangent of the angle at one of the vertices) of a `π / 2` rotation of the vector between
the other two vertices, plus the midpoint of those vertices. -/
/-
**Affine.Triangle.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circ
umcenter** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Triangle`。
形式化陈述：inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter (t 
: Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i
₂ != i₃) : ((Real.Angle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2
) • o.rotation (π / 2 : Real) (t.points i₃ -ᵥ t.points i₁) +ᵥ midpoint Real (t.p
oints i₁) (t.points i₃) = t.circumcenter
参数：t : Triangle Real P；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_m
idpoint_eq_center`：inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_cen
ter {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in …
· 使用定理 `Affine.Simplex.mem_circumsphere`：mem_circumsphere {n : Nat} (s : Simplex
 Real P n) (i : Fin (n + 1)) : s.points i in s.circumsphere
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …

--- 原说明 ---
The circumcenter of a triangle may be expressed explicitly as a multiple (by hal
f the inverse
of the tangent of the angle at one of the vertices) of a `π / 2` rotation of the
 vector between
the other two vertices, plus the midpoint of those vertices.
-/
theorem inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter (t : Triangle ℝ P)
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    ((Real.Angle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2) •
      o.rotation (π / 2 : ℝ) (t.points i₃ -ᵥ t.points i₁) +ᵥ
        midpoint ℝ (t.points i₁) (t.points i₃) = t.circumcenter :=
  Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.mem_circumsphere _) (t.independent.injective.ne h₁₂)
    (t.independent.injective.ne h₁₃) (t.independent.injective.ne h₂₃)

/-- The circumradius of a triangle may be expressed explicitly as half the length of a side
divided by the absolute value of the sine of the angle at the third point (a version of the law
of sines or sine rule). -/
/-
**Affine.Triangle.dist_div_sin_oangle_div_two_eq_circumradius** 是 Mathlib 中的一个定理
，位于命名空间 `Affine.Triangle`。
形式化陈述：dist_div_sin_oangle_div_two_eq_circumradius (t : Triangle Real P) {i₁ i₂ i
₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : dist (t.points i
₁) (t.points i₃) / |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))
| / 2 = t.circumradius
参数：t : Triangle Real P；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.dist_div_sin_oangle_div_two_eq_radius`：dist_div
_sin_oangle_div_two_eq_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂
 : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) (hp₁p…
· 使用定理 `Affine.Simplex.mem_circumsphere`：mem_circumsphere {n : Nat} (s : Simplex
 Real P n) (i : Fin (n + 1)) : s.points i in s.circumsphere
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …

--- 原说明 ---
The circumradius of a triangle may be expressed explicitly as half the length of
 a side
divided by the absolute value of the sine of the angle at the third point (a ver
sion of the law
of sines or sine rule).
-/
theorem dist_div_sin_oangle_div_two_eq_circumradius (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) : dist (t.points i₁) (t.points i₃) /
      |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| / 2 = t.circumradius :=
  Sphere.dist_div_sin_oangle_div_two_eq_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
    (t.independent.injective.ne h₂₃)

/-- Twice the circumradius of a triangle may be expressed explicitly as the length of a side
divided by the absolute value of the sine of the angle at the third point (a version of the law
of sines or sine rule). -/
/-
**Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius** 是 Mathlib 中的一个定理
，位于命名空间 `Affine.Triangle`。
形式化陈述：dist_div_sin_oangle_eq_two_mul_circumradius (t : Triangle Real P) {i₁ i₂ i
₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : dist (t.points i
₁) (t.points i₃) / |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))
| = 2 * t.circumradius
参数：t : Triangle Real P；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.dist_div_sin_oangle_eq_two_mul_radius`：dist_div
_sin_oangle_eq_two_mul_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂
 : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) (hp₁p…
· 使用定理 `Affine.Simplex.mem_circumsphere`：mem_circumsphere {n : Nat} (s : Simplex
 Real P n) (i : Fin (n + 1)) : s.points i in s.circumsphere
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …

--- 原说明 ---
Twice the circumradius of a triangle may be expressed explicitly as the length o
f a side
divided by the absolute value of the sine of the angle at the third point (a ver
sion of the law
of sines or sine rule).
-/
theorem dist_div_sin_oangle_eq_two_mul_circumradius (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) : dist (t.points i₁) (t.points i₃) /
      |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| = 2 * t.circumradius :=
  Sphere.dist_div_sin_oangle_eq_two_mul_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
    (t.independent.injective.ne h₂₃)

/-- The circumsphere of a triangle may be expressed explicitly in terms of two points and the
angle at the third point. -/
/-
**Affine.Triangle.circumsphere_eq_of_dist_of_oangle** 是 Mathlib 中的一个定理，位于命名空间 `A
ffine.Triangle`。
形式化陈述：circumsphere_eq_of_dist_of_oangle (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3}
 (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : t.circumsphere = ⟨((Real.A
ngle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2) • o.rotation (π /
 2 : Real) (t.points i₃ -ᵥ t.points i₁) +ᵥ midpoint Real (t.points i₁) (t.points
 i₃), dist (t.points i₁) (t.points i₃) / |Real.Angle.sin (∡ (t.points i₁) (t.poi
nts i₂) (t.points i₃))| / 2⟩
参数：t : Triangle Real P；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.ext`：∀ {P : Type u_2} {inst : MetricSpace P} {x
 y : EuclideanGeometry.Sphere P},   x.center = y.center → x.radius = y.radius → 
x = y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Triangle.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_e
q_circumcenter`：inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circum
center (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ !…
· 使用定理 `Affine.Triangle.dist_div_sin_oangle_div_two_eq_circumradius`：dist_div_si
n_oangle_div_two_eq_circumradius (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ :
 i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : di…

--- 原说明 ---
The circumsphere of a triangle may be expressed explicitly in terms of two point
s and the
angle at the third point.
-/
theorem circumsphere_eq_of_dist_of_oangle (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) : t.circumsphere =
    ⟨((Real.Angle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2) •
      o.rotation (π / 2 : ℝ) (t.points i₃ -ᵥ t.points i₁) +ᵥ midpoint ℝ (t.points i₁) (t.points i₃),
      dist (t.points i₁) (t.points i₃) /
        |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| / 2⟩ :=
  t.circumsphere.ext
    (t.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter h₁₂ h₁₃ h₂₃).symm
    (t.dist_div_sin_oangle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃).symm

/-- If two triangles have two points the same, and twice the angle at the third point the same,
they have the same circumsphere. -/
/-
**Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_e
q** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Triangle`。
形式化陈述：circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq {t₁ t₂ : T
riangle Real P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ !
= i₃) (h₁ : t₁.points i₁ = t₂.points i₁) (h₃ : t₁.points i₃ = t₂.points i₃) (h₂ 
: (2 : Int) • ∡ (t₁.points i₁) (t₁.points i₂) (t₁.points i₃) = (2 : Int) • ∡ (t₂
.points i₁) (t₂.points i₂) (t₂.points i₃)) : t₁.circumsphere = t₂.circumsphere
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃；h₁ : t₁.points i₁ = t₂.points i₁
；h₃ : t₁.points i₃ = t₂.points i₃；h₂ : (2 : Int) • ∡ (t₁.points i₁) (t₁.points i
₂) (t₁.points i₃) = (2 : Int) • ∡ (t₂.points i₁) (t₂.points i₂) (t₂.points i₃)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Triangle.circumsphere_eq_of_dist_of_oangle`：circumsphere_eq_of_di
st_of_oangle (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁
 != i₃) (h₂₃ : i₂ != i₃) : t.circumsphe…
· 使用定理 `Real.Angle.tan_eq_of_two_zsmul_eq`：tan_eq_of_two_zsmul_eq {θ ψ : Angle} 
(h : (2 : Int) • θ = (2 : Int) • ψ) : tan θ = tan ψ
· 使用定理 `Real.Angle.abs_sin_eq_of_two_zsmul_eq`：abs_sin_eq_of_two_zsmul_eq {θ ψ :
 Angle} (h : (2 : Int) • θ = (2 : Int) • ψ) : |sin θ| = |sin ψ|

--- 原说明 ---
If two triangles have two points the same, and twice the angle at the third poin
t the same,
they have the same circumsphere.
-/
theorem circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq {t₁ t₂ : Triangle ℝ P}
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h₁ : t₁.points i₁ = t₂.points i₁) (h₃ : t₁.points i₃ = t₂.points i₃)
    (h₂ : (2 : ℤ) • ∡ (t₁.points i₁) (t₁.points i₂) (t₁.points i₃) =
      (2 : ℤ) • ∡ (t₂.points i₁) (t₂.points i₂) (t₂.points i₃)) :
    t₁.circumsphere = t₂.circumsphere := by
  rw [t₁.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃,
    t₂.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃,
    Real.Angle.tan_eq_of_two_zsmul_eq h₂, Real.Angle.abs_sin_eq_of_two_zsmul_eq h₂, h₁, h₃]

/-- Given a triangle, and a fourth point such that twice the angle between two points of the
triangle at that fourth point equals twice the third angle of the triangle, the fourth point
lies in the circumsphere of the triangle. -/
/-
**Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq** 是 Mathlib 中的一个定理，位于命
名空间 `Affine.Triangle`。
形式化陈述：mem_circumsphere_of_two_zsmul_oangle_eq {t : Triangle Real P} {p : P} {i₁ 
i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) (h : (2 : Int)
 • ∡ (t.points i₁) p (t.points i₃) = (2 : Int) • ∡ (t.points i₁) (t.points i₂) (
t.points i₃)) : p in t.circumsphere
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃；h : (2 : Int) • ∡ (t.points i₁) 
p (t.points i₃) = (2 : Int) • ∡ (t.points i₁) (t.points i₂) (t.points i₃)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `affineIndependent_iff_not_collinear_of_ne`：affineIndependent_iff_not_col
linear_of_ne {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i
₃) (h₂₃ : i₂ != i₃) : AffineInd…
· 使用定理 `EuclideanGeometry.collinear_iff_of_two_zsmul_oangle_eq`：collinear_iff_of
_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : (2 : Int) • ∡ p₁ p₂ p₃ = (2 : 
Int) • ∡ p₄ p₅ p₆) : Collinear Real ({p₁, p₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oa
ngle_eq`：circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq {t₁ t₂ 
: Triangle Real P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i…
· 使用定理 `Affine.Simplex.mem_circumsphere`：mem_circumsphere {n : Nat} (s : Simplex
 Real P n) (i : Fin (n + 1)) : s.points i in s.circumsphere

--- 原说明 ---
Given a triangle, and a fourth point such that twice the angle between two point
s of the
triangle at that fourth point equals twice the third angle of the triangle, the 
fourth point
lies in the circumsphere of the triangle.
-/
theorem mem_circumsphere_of_two_zsmul_oangle_eq {t : Triangle ℝ P} {p : P} {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h : (2 : ℤ) • ∡ (t.points i₁) p (t.points i₃) =
      (2 : ℤ) • ∡ (t.points i₁) (t.points i₂) (t.points i₃)) : p ∈ t.circumsphere := by
  let t'p : Fin 3 → P := Function.update t.points i₂ p
  have h₁ : t'p i₁ = t.points i₁ := by simp [t'p, h₁₂]
  have h₂ : t'p i₂ = p := by simp [t'p]
  have h₃ : t'p i₃ = t.points i₃ := by simp [t'p, h₂₃.symm]
  have ha : AffineIndependent ℝ t'p := by
    rw [affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃, h₁, h₂, h₃,
      collinear_iff_of_two_zsmul_oangle_eq h, ←
      affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃]
    exact t.independent
  let t' : Triangle ℝ P := ⟨t'p, ha⟩
  have h₁' : t'.points i₁ = t.points i₁ := h₁
  have h₂' : t'.points i₂ = p := h₂
  have h₃' : t'.points i₃ = t.points i₃ := h₃
  have h' : (2 : ℤ) • ∡ (t'.points i₁) (t'.points i₂) (t'.points i₃) =
      (2 : ℤ) • ∡ (t.points i₁) (t.points i₂) (t.points i₃) := by rwa [h₁', h₂', h₃']
  rw [← circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ h₁' h₃' h', ←
    h₂']
  exact Simplex.mem_circumsphere _ _

end Oriented

/-- The circumradius of a triangle may be expressed explicitly as half the length of a side
divided by the sine of the angle at the third point (a version of the law of sines or sine rule). -/
/-
**Affine.Triangle.dist_div_sin_angle_div_two_eq_circumradius** 是 Mathlib 中的一个定理，
位于命名空间 `Affine.Triangle`。
形式化陈述：dist_div_sin_angle_div_two_eq_circumradius (t : Triangle Real P) {i₁ i₂ i₃
 : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : dist (t.points i₁
) (t.points i₃) / Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) / 2 = t
.circumradius
参数：t : Triangle Real P；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `AffineIndependent.finrank_vectorSpan`：AffineIndependent.finrank_vectorSp
an [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) {n : Nat} (hc : Fintype
.card ι = n + 1) : finrank…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.sin_toReal`：sin_toReal (θ : Angle) : Real.sin θ.toReal = sin 
θ
· 使用引理 `Real.abs_sin_eq_sin_abs_of_abs_le_pi`：abs_sin_eq_sin_abs_of_abs_le_pi {x
 : Real} (hx : |x| <= π) : |sin x| = sin |x|
· 使用定理 `Real.Angle.abs_toReal_le_pi`：abs_toReal_le_pi (θ : Angle) : |θ.toReal| <
= π
· 使用定理 `EuclideanGeometry.angle_eq_abs_oangle_toReal`：angle_eq_abs_oangle_toReal
 {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) : ∠ p₁ p p₂ = |(∡ p₁ p p₂).toReal
|
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Affine.Simplex.circumradius_restrict`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Triangle.dist_div_sin_oangle_div_two_eq_circumradius`：dist_div_si
n_oangle_div_two_eq_circumradius (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ :
 i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : di…

--- 原说明 ---
The circumradius of a triangle may be expressed explicitly as half the length of
 a side
divided by the sine of the angle at the third point (a version of the law of sin
es or sine rule).
-/
theorem dist_div_sin_angle_div_two_eq_circumradius (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) (t.points i₃) / Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) / 2 =
      t.circumradius := by
  set S : AffineSubspace ℝ P := affineSpan ℝ (Set.range t.points) with hS
  let t' : Triangle ℝ S := t.restrict S le_rfl
  have hf2 : Fact (finrank ℝ S.direction = 2) := ⟨by
    rw [hS, direction_affineSpan, t.independent.finrank_vectorSpan]
    simp⟩
  have : Module.Oriented ℝ S.direction (Fin 2) :=
    ⟨Basis.orientation (finBasisOfFinrankEq _ _ hf2.out)⟩
  convert! t'.dist_div_sin_oangle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃ using 3
  · rw [← Real.Angle.sin_toReal,
      Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
      ← angle_eq_abs_oangle_toReal (t'.independent.injective.ne h₁₂)
        (t'.independent.injective.ne h₂₃.symm)]
    congr
  · simp [t']

/-- Twice the circumradius of a triangle may be expressed explicitly as the length of a side
divided by the sine of the angle at the third point (a version of the law of sines or sine rule). -/
/-
**Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius** 是 Mathlib 中的一个定理，
位于命名空间 `Affine.Triangle`。
形式化陈述：dist_div_sin_angle_eq_two_mul_circumradius (t : Triangle Real P) {i₁ i₂ i₃
 : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : dist (t.points i₁
) (t.points i₃) / Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) = 2 * t
.circumradius
参数：t : Triangle Real P；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Triangle.dist_div_sin_angle_div_two_eq_circumradius`：dist_div_sin
_angle_div_two_eq_circumradius (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i
₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : dis…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Twice the circumradius of a triangle may be expressed explicitly as the length o
f a side
divided by the sine of the angle at the third point (a version of the law of sin
es or sine rule).
-/
theorem dist_div_sin_angle_eq_two_mul_circumradius (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) : dist (t.points i₁) (t.points i₃) /
      Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) = 2 * t.circumradius := by
  rw [← t.dist_div_sin_angle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃]
  ring

end Triangle

end Affine

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

local notation "o" => Module.Oriented.positiveOrientation

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π. -/
theorem cospherical_of_two_zsmul_oangle_eq_of_not_collinear {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬Collinear ℝ ({p₁, p₂, p₄} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have hn' : ¬Collinear ℝ ({p₁, p₃, p₄} : Set P) := by
    rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
  let t₁ : Affine.Triangle ℝ P := ⟨![p₁, p₂, p₄], affineIndependent_iff_not_collinear_set.2 hn⟩
  let t₂ : Affine.Triangle ℝ P := ⟨![p₁, p₃, p₄], affineIndependent_iff_not_collinear_set.2 hn'⟩
  rw [cospherical_iff_exists_sphere]
  refine ⟨t₂.circumsphere, ?_⟩
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨t₂.mem_circumsphere 0, ?_, t₂.mem_circumsphere 1, t₂.mem_circumsphere 2⟩
  rw [Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq
    (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2) (by decide)
    (show t₂.points 0 = t₁.points 0 from rfl) rfl h.symm]
  exact t₁.mem_circumsphere 1

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "concyclic" conclusion. -/
theorem concyclic_of_two_zsmul_oangle_eq_of_not_collinear {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬Collinear ℝ ({p₁, p₂, p₄} : Set P)) :
    Concyclic ({p₁, p₂, p₃, p₄} : Set P) :=
  ⟨cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hn, coplanar_of_fact_finrank_eq_two _⟩

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "cospherical or collinear" conclusion. -/
theorem cospherical_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) ∨ Collinear ℝ ({p₁, p₂, p₃, p₄} : Set P) := by
  by_cases hc : Collinear ℝ ({p₁, p₂, p₄} : Set P)
  · by_cases he : p₁ = p₄
    · rw [he, Set.insert_eq_self.2
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))]
      by_cases hl : Collinear ℝ ({p₂, p₃, p₄} : Set P); · exact Or.inr hl
      rw [or_iff_left hl]
      let t : Affine.Triangle ℝ P := ⟨![p₂, p₃, p₄], affineIndependent_iff_not_collinear_set.2 hl⟩
      rw [cospherical_iff_exists_sphere]
      refine ⟨t.circumsphere, ?_⟩
      simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨t.mem_circumsphere 0, t.mem_circumsphere 1, t.mem_circumsphere 2⟩
    have hc' : Collinear ℝ ({p₁, p₃, p₄} : Set P) := by
      rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
    refine Or.inr ?_
    rw [Set.insert_comm p₁ p₂] at hc
    rwa [Set.insert_comm p₁ p₂, hc'.collinear_insert_iff_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) he]
  · exact Or.inl (cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hc)

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "concyclic or collinear" conclusion. -/
theorem concyclic_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) :
    Concyclic ({p₁, p₂, p₃, p₄} : Set P) ∨ Collinear ℝ ({p₁, p₂, p₃, p₄} : Set P) := by
  rcases cospherical_or_collinear_of_two_zsmul_oangle_eq h with (hc | hc)
  · exact Or.inl ⟨hc, coplanar_of_fact_finrank_eq_two _⟩
  · exact Or.inr hc

end EuclideanGeometry

