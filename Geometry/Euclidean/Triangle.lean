/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Tactic.IntervalCases

/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces. More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files. Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`LinearAlgebra.AffineSpace`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle
* https://en.wikipedia.org/wiki/Law_of_sines

-/

public section

noncomputable section

open scoped CharZero Real RealInnerProductSpace

namespace InnerProductGeometry

/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Law of cosines** (cosine rule), vector angle form. -/
/-
**InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_n
orm_mul_cos_angle** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
 (x y : V) : ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * ‖x‖ * ‖y‖ * Real.co
s (angle x y)
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `InnerProductGeometry.cos_angle_mul_norm_mul_norm`：cos_angle_mul_norm_mul
_norm (x y : V) : Real.cos (angle x y) * (‖x‖ * ‖y‖) = ⟪x, y⟫
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
· 使用定理 `real_inner_sub_sub_self`：real_inner_sub_sub_self (x y : F) : ⟪x - y, x -
 y⟫_Real = ⟪x, x⟫_Real - 2 * ⟪x, y⟫_Real + ⟪y, y⟫_Real
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b

--- 原说明 ---
**Law of cosines** (cosine rule), vector angle form.
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (x y : V) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) := by
  rw [show 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) = 2 * (Real.cos (angle x y) * (‖x‖ * ‖y‖)) by ring,
    cos_angle_mul_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, ←
    real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, real_inner_sub_sub_self,
    sub_add_eq_add_sub]

/-- **Law of sines** (sine rule), vector angle form. -/
/-
**InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：sin_angle_mul_norm_eq_sin_angle_mul_norm (x y : V) : Real.sin (angle x y) 
* ‖x‖ = Real.sin (angle y (x - y)) * ‖x - y‖
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `InnerProductGeometry.angle_zero_right`：angle_zero_right (x : V) : angle 
x 0 = π / 2
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `InnerProductGeometry.angle_neg_right`：angle_neg_right (x y : V) : angle 
x (-y) = π - angle x y
· 使用定理 `InnerProductGeometry.angle_self`：angle_self {x : V} (hx : x != 0) : angl
e x x = 0
· 使用定理 `Real.sin_pi`：sin_pi : sin π = 0
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
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
（共 118 条，此处仅展示前 30 条）

--- 原说明 ---
**Law of sines** (sine rule), vector angle form.
-/
theorem sin_angle_mul_norm_eq_sin_angle_mul_norm (x y : V) :
    Real.sin (angle x y) * ‖x‖ = Real.sin (angle y (x - y)) * ‖x - y‖ := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  obtain rfl | hx := eq_or_ne x 0
  · simp [angle_neg_right, angle_self hy]
  obtain rfl | hxy := eq_or_ne x y
  · simp [angle_self hx]
  have h_sin (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
      Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) / (‖x‖ * ‖y‖) := by
    simp [field, mul_assoc, sin_angle_mul_norm_mul_norm]
  rw [h_sin x y hx hy, h_sin y (x - y) hy (sub_ne_zero_of_ne hxy)]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm x y]
  have hsub : x - y ≠ 0 := sub_ne_zero_of_ne hxy
  field_simp
  ring_nf

/-- A variant of the law of sines, (two given sides are nonzero), vector angle form. -/
/-
**InnerProductGeometry.sin_angle_div_norm_eq_sin_angle_div_norm** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：sin_angle_div_norm_eq_sin_angle_div_norm (x y : V) (hx : x != 0) (hxy : x 
- y != 0) : Real.sin (angle x y) / ‖x - y‖ = Real.sin (angle y (x - y)) / ‖x‖
参数：x y : V；hx : x != 0；hxy : x - y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_ne_zero`：cons_ne_zero [GroupWithZero M]
 (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) : ((r, x) ::ᵣ l).
eval != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm`：sin_angle
_mul_norm_eq_sin_angle_mul_norm (x y : V) : Real.sin (angle x y) * ‖x‖ = Real.si
n (angle y (x - y)) * ‖x - y‖
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A variant of the law of sines, (two given sides are nonzero), vector angle form.
-/
theorem sin_angle_div_norm_eq_sin_angle_div_norm (x y : V) (hx : x ≠ 0) (hxy : x - y ≠ 0) :
    Real.sin (angle x y) / ‖x - y‖ = Real.sin (angle y (x - y)) / ‖x‖ := by
  simp [field, sin_angle_mul_norm_eq_sin_angle_mul_norm x y]

/-- **Pons asinorum**, vector angle form. -/
/-
**InnerProductGeometry.angle_sub_eq_angle_sub_rev_of_norm_eq** 是 Mathlib 中的一个定理，
位于命名空间 `InnerProductGeometry`。
形式化陈述：angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : angle x 
(x - y) = angle y (y - x)
参数：h : ‖x‖ = ‖y‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.injOn_cos`：injOn_cos : InjOn cos (Icc 0 π)
· 使用定理 `InnerProductGeometry.angle_nonneg`：angle_nonneg (x y : V) : 0 <= angle x
 y
· 使用定理 `InnerProductGeometry.angle_le_pi`：angle_le_pi (x y : V) : angle x y <= π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.cos_angle`：cos_angle (x y : V) : Real.cos (angle x 
y) = ⟪x, y⟫ / (‖x‖ * ‖y‖)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real

--- 原说明 ---
**Pons asinorum**, vector angle form.
-/
theorem angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    angle x (x - y) = angle y (y - x) := by
  refine Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ?_
  rw [cos_angle, cos_angle, h, ← neg_sub, norm_neg, neg_sub, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm, h, real_inner_comm x y]

/-- **Converse of pons asinorum**, vector angle form. -/
/-
**InnerProductGeometry.norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi** 是 
Mathlib 中的一个定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V} (h : angle 
x (x - y) = angle y (y - x)) (hpi : angle x y != π) : ‖x‖ = ‖y‖
参数：h : angle x (x - y) = angle y (y - x)；hpi : angle x y != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.arccos_injOn`：arccos_injOn : InjOn arccos (Icc (-1) 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `abs_real_inner_div_norm_mul_norm_le_one`：abs_real_inner_div_norm_mul_nor
m_le_one (x y : F) : |⟪x, y⟫_Real / (‖x‖ * ‖y‖)| <= 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `mul_sub_left_distrib`：mul_sub_left_distrib (a b c : α) : a * (b - c) = a
 * b - a * c
· 使用定理 `sub_eq_sub_iff_sub_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b
 c d : G}, a - b = c - d ↔ a - c = b - d
· 使用定理 `mul_self_mul_inv`：mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a
· 使用定理 `mul_sub_right_distrib`：mul_sub_right_distrib (a b c : α) : (a - b) * c =
 a * c - b * c
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
**Converse of pons asinorum**, vector angle form.
-/
theorem norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y ≠ π) : ‖x‖ = ‖y‖ := by
  replace h := Real.arccos_injOn (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x (x - y)))
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one y (y - x))) h
  by_cases hxy : x = y
  · rw [hxy]
  · rw [← norm_neg (y - x), neg_sub, mul_comm, mul_comm ‖y‖, div_eq_mul_inv, div_eq_mul_inv,
      mul_inv_rev, mul_inv_rev, ← mul_assoc, ← mul_assoc] at h
    replace h :=
      mul_right_cancel₀ (inv_ne_zero fun hz => hxy (eq_of_sub_eq_zero (norm_eq_zero.1 hz))) h
    rw [inner_sub_right, inner_sub_right, real_inner_comm x y, real_inner_self_eq_norm_mul_norm,
      real_inner_self_eq_norm_mul_norm, mul_sub_right_distrib, mul_sub_right_distrib,
      mul_self_mul_inv, mul_self_mul_inv, sub_eq_sub_iff_sub_eq_sub, ← mul_sub_left_distrib] at h
    by_cases hx0 : x = 0
    · rw [hx0, norm_zero, inner_zero_left, zero_mul, zero_sub, neg_eq_zero] at h
      rw [hx0, norm_zero, h]
    · by_cases hy0 : y = 0
      · rw [hy0, norm_zero, inner_zero_right, zero_mul, sub_zero] at h
        rw [hy0, norm_zero, h]
      · rw [inv_sub_inv (fun hz => hx0 (norm_eq_zero.1 hz)) fun hz => hy0 (norm_eq_zero.1 hz), ←
          neg_sub, ← mul_div_assoc, mul_comm, mul_div_assoc, ← mul_neg_one] at h
        symm
        by_contra hyx
        replace h := (mul_left_cancel₀ (sub_ne_zero_of_ne hyx) h).symm
        rw [real_inner_div_norm_mul_norm_eq_neg_one_iff, ← angle_eq_pi_iff] at h
        exact hpi h

/-- The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
/-
**InnerProductGeometry.cos_angle_eq_cos_angle_add_add_angle_add** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form.
-/
private theorem cos_angle_eq_cos_angle_add_add_angle_add {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.cos (angle x y) = Real.cos (angle x (x + y) + angle y (y + x)) := by
  rcases eq_or_ne x (-y) with (rfl | hxy)
  · simp [hy]
  · rw [Real.cos_add, cos_angle, cos_angle, cos_angle, sin_angle_add hx (by grind),
      sin_angle_add hy (by grind), mul_comm ⟪y, y⟫ ⟪x, x⟫, real_inner_comm x y, add_comm y x]
    have : x + y ≠ 0 := by grind
    simp only [field] -- non-recursive `field_simp`
    rw [Real.sq_sqrt (sub_nonneg_of_le (real_inner_mul_inner_self_le x y))]
    simp only [← real_inner_self_eq_norm_sq, inner_add_right, inner_add_left, real_inner_comm]
    ring

/-- The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
/-
**InnerProductGeometry.sin_angle_eq_sin_angle_add_add_angle_add** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form.
-/
private theorem sin_angle_eq_sin_angle_add_add_angle_add {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.sin (angle x y) = Real.sin (angle x (x + y) + angle y (y + x)) := by
  rcases eq_or_ne x (-y) with (rfl | hxy)
  · simp [hy]
  · rw [Real.sin_add, cos_angle, cos_angle, sin_angle_add hx (by grind),
      sin_angle_add hy (by grind), sin_angle hx hy, add_comm y x]
    have : x + y ≠ 0 := by grind
    simp only [field] -- non-recursive `field_simp`
    simp only [← real_inner_self_eq_norm_sq, inner_add_right, inner_add_left, real_inner_comm]
    ring_nf

/-- In a parallelogram, the two parts of the inner angle add to the inner angle,
vector angle form. -/
/-
**InnerProductGeometry.angle_eq_angle_add_add_angle_add** 是 Mathlib 中的一个定理，位于命名空
间 `InnerProductGeometry`。
形式化陈述：angle_eq_angle_add_add_angle_add (x : V) {y : V} (hy : y != 0) : angle x y
 = angle x (x + y) + angle y (x + y)
参数：x : V；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `InnerProductGeometry.angle_self`：angle_self {x : V} (hx : x != 0) : angl
e x x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.cos_sin_inj`：cos_sin_inj {θ ψ : Real} (Hcos : cos θ = cos ψ) 
(Hsin : sin θ = sin ψ) : (θ : Angle) = ψ
· 使用定理 `_private.Mathlib.Geometry.Euclidean.Triangle.0.InnerProductGeometry.cos_
angle_eq_cos_angle_add_add_angle_add`：∀ {V : Type u_1} [inst : NormedAddCommGrou
p V] [inst_1 : InnerProductSpace ℝ V] {x y : V},   x ≠ 0 →     y ≠ 0 →       Rea
l.cos (InnerProduc…
· 使用定理 `_private.Mathlib.Geometry.Euclidean.Triangle.0.InnerProductGeometry.sin_
angle_eq_sin_angle_add_add_angle_add`：∀ {V : Type u_1} [inst : NormedAddCommGrou
p V] [inst_1 : InnerProductSpace ℝ V] {x y : V},   x ≠ 0 →     y ≠ 0 →       Rea
l.sin (InnerProduc…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `QuotientAddGroup.mk'_eq_mk'`：∀ {G : Type u_1} [inst : AddGroup G] (N : A
ddSubgroup G) [nN : N.Normal] {x y : G},   (QuotientAddGroup.mk' N) x = (Quotien
tAddGroup.mk' N) …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 116 条，此处仅展示前 30 条）

--- 原说明 ---
In a parallelogram, the two parts of the inner angle add to the inner angle,
vector angle form.
-/
theorem angle_eq_angle_add_add_angle_add (x : V) {y : V} (hy : y ≠ 0) :
    angle x y = angle x (x + y) + angle y (x + y) := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp [hy]
  have h := Real.Angle.cos_sin_inj
    (cos_angle_eq_cos_angle_add_add_angle_add hx hy)
    (sin_angle_eq_sin_angle_add_add_angle_add hx hy)
  rw [add_comm y x] at h
  obtain ⟨_, ⟨n, rfl⟩, h⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp h
  simp only at h
  have : -1 < n := by
    replace h := h.ge
    contrapose! h
    grw [h, neg_smul, one_smul, angle_le_pi, ← angle_nonneg, ← angle_nonneg]
    linear_combination Real.pi_pos
  have : n < 1 := by
    replace h := h.le
    by_contra! hn
    grw [← hn, one_smul, ← angle_nonneg x y, zero_add, two_mul] at h
    have h' := h.trans_eq (add_comm _ _)
    grw [angle_le_pi] at h' h
    rw [add_le_add_iff_left, (angle_le_pi _ _).ge_iff_eq, angle_comm, angle_eq_pi_iff] at h' h
    obtain ⟨hxy, r₁, r₁_pos, hr₁⟩ := h'
    obtain ⟨-, r₂, r₂_pos, hr₂⟩ := h
    have : (r₁ + r₂ - 1) • (x + y) = 0 := by
      rw [sub_smul, add_smul, one_smul, ← hr₁, ← hr₂, sub_eq_zero]
    cases smul_eq_zero.1 this
    · linarith
    · contradiction
  obtain rfl : n = 0 := by lia
  simpa using h

/-- The sum of the angles of a possibly degenerate triangle (where one of the
two given sides is nonzero), vector angle form. -/
/-
**InnerProductGeometry.angle_add_angle_sub_add_angle_sub_eq_pi** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：angle_add_angle_sub_add_angle_sub_eq_pi (x : V) {y : V} (hy : y != 0) : an
gle x y + angle x (x - y) + angle y (y - x) = π
参数：x : V；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductGeometry.angle_eq_angle_add_add_angle_add`：angle_eq_angle_ad
d_add_angle_add (x : V) {y : V} (hy : y != 0) : angle x y = angle x (x + y) + an
gle y (x + y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `InnerProductGeometry.angle_neg_right`：angle_neg_right (x y : V) : angle 
x (-y) = π - angle x y
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `InnerProductGeometry.angle_comm`：angle_comm (x y : V) : angle x y = angl
e y x
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The sum of the angles of a possibly degenerate triangle (where one of the
two given sides is nonzero), vector angle form.
-/
theorem angle_add_angle_sub_add_angle_sub_eq_pi (x : V) {y : V} (hy : y ≠ 0) :
    angle x y + angle x (x - y) + angle y (y - x) = π := by
  have h := angle_eq_angle_add_add_angle_add (x - y) hy
  rw [sub_add_cancel] at h
  rw [← neg_sub x y, angle_neg_right]
  simp only [angle_comm] at h ⊢
  linear_combination -h

end InnerProductGeometry

namespace Orientation

open Module InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]
variable (o : Orientation ℝ V (Fin 2))

/-- **Converse of pons asinorum**, oriented vector angle form (given equality of angles mod `π`). -/
/-
**Orientation.norm_eq_of_two_zsmul_oangle_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Orie
ntation`。
形式化陈述：norm_eq_of_two_zsmul_oangle_sub_eq {x y : V} (h : (2 : Int) • o.oangle x (
x - y) = (2 : Int) • o.oangle (y - x) y) (h0 : o.oangle x y != 0) (hpi : o.oangl
e x y != π) : ‖x‖ = ‖y‖
参数：h : (2 : Int) • o.oangle x (x - y) = (2 : Int) • o.oangle (y - x) y；h0 : o.oa
ngle x y != 0；hpi : o.oangle x y != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Orientation.oangle_sign_sub_left_swap`：oangle_sign_sub_left_swap (x y : 
V) : (o.oangle (x - y) x).sign = (o.oangle x y).sign
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.Angle.two_zsmul_eq_iff`：two_zsmul_eq_iff {ψ θ : Angle} : (2 : Int) 
• ψ = (2 : Int) • θ ↔ ψ = θ ∨ ψ = θ + ↑π
· 使用定理 `InnerProductGeometry.norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_p
i`：norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V} (h : angle x (
x - y) = angle y (y - x)) (hpi : angle x y != π) : ‖x‖ = ‖y‖
· 使用定理 `InnerProductGeometry.angle_comm`：angle_comm (x y : V) : angle x y = angl
e y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.angle_eq_iff_oangle_eq_of_sign_eq`：angle_eq_iff_oangle_eq_of
_sign_eq {w x y z : V} (hw : w != 0) (hx : x != 0) (hy : y != 0) (hz : z != 0) (
hs : (o.oangle w x).sign = (o.oangl…
· 使用定理 `Orientation.left_ne_zero_of_oangle_ne_zero`：left_ne_zero_of_oangle_ne_ze
ro {x y : V} (h : o.oangle x y != 0) : x != 0
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `Orientation.ne_of_oangle_ne_zero`：ne_of_oangle_ne_zero {x y : V} (h : o.
oangle x y != 0) : x != y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Orientation.right_ne_zero_of_oangle_ne_zero`：right_ne_zero_of_oangle_ne_
zero {x y : V} (h : o.oangle x y != 0) : y != 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Orientation.oangle_eq_pi_iff_angle_eq_pi`：oangle_eq_pi_iff_angle_eq_pi {
x y : V} : o.oangle x y = π ↔ InnerProductGeometry.angle x y = π
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Real.Angle.sign_eq_zero_iff`：sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔
 θ = 0 ∨ θ = π
· 使用定理 `SignType.neg_eq_zero_iff`：neg_eq_zero_iff {a : SignType} : -a = 0 ↔ a = 
0
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `SignType.neg_eq_self_iff`：neg_eq_self_iff {a : SignType} : -a = a ↔ a = 
0
· 使用定理 `Real.Angle.sign_add_pi`：sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign

--- 原说明 ---
**Converse of pons asinorum**, oriented vector angle form (given equality of ang
les mod `π`).
-/
theorem norm_eq_of_two_zsmul_oangle_sub_eq {x y : V}
    (h : (2 : ℤ) • o.oangle x (x - y) = (2 : ℤ) • o.oangle (y - x) y) (h0 : o.oangle x y ≠ 0)
    (hpi : o.oangle x y ≠ π) : ‖x‖ = ‖y‖ := by
  have hs : (o.oangle x (x - y)).sign = (o.oangle (y - x) y).sign := by simp
  rw [Real.Angle.two_zsmul_eq_iff] at h
  rcases h with h | h
  · rw [← o.angle_eq_iff_oangle_eq_of_sign_eq (o.left_ne_zero_of_oangle_ne_zero h0)
      (sub_ne_zero_of_ne (o.ne_of_oangle_ne_zero h0))
      (sub_ne_zero_of_ne (o.ne_of_oangle_ne_zero h0).symm)
      (o.right_ne_zero_of_oangle_ne_zero h0) hs, angle_comm (y - x)] at h
    refine norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h ?_
    rw [ne_eq, ← o.oangle_eq_pi_iff_angle_eq_pi]
    exact hpi
  · rw [h, Real.Angle.sign_add_pi, SignType.neg_eq_self_iff, oangle_sign_sub_left_swap,
      o.oangle_rev, Real.Angle.sign_neg, SignType.neg_eq_zero_iff,
      Real.Angle.sign_eq_zero_iff] at hs
    simp [h0, hpi] at hs

end Orientation

namespace EuclideanGeometry

/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possibly degenerate) triangles in Euclidean affine spaces.
-/

open InnerProductGeometry
open scoped EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Law of cosines** (cosine rule), angle-at-point form. -/
/-
**EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul
_cos_angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (p₁
 p₂ p₃ : P) : dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * d
ist p₃ p₂ - 2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃)
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm
_mul_norm_mul_cos_angle`：norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul
_norm_mul_cos_angle (x y : V) : ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * 
‖x‖ *…

--- 原说明 ---
**Law of cosines** (cosine rule), angle-at-point form.
-/
theorem dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ -
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) := by
  rw [dist_eq_norm_vsub V p₁ p₃, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₃ p₂]
  unfold angle
  convert!
    norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (p₁ -ᵥ p₂ : V)
      (p₃ -ᵥ p₂ : V)
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm

alias law_cos := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle

/-- **Law of sines** (sine rule), angle-at-point form. -/
/-
**EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：sin_angle_mul_dist_eq_sin_angle_mul_dist (p₁ p₂ p₃ : P) : Real.sin (∠ p₁ p
₂ p₃) * dist p₂ p₃ = Real.sin (∠ p₃ p₁ p₂) * dist p₃ p₁
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `InnerProductGeometry.angle_comm`：angle_comm (x y : V) : angle x y = angl
e y x
· 使用定理 `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm`：sin_angle
_mul_norm_eq_sin_angle_mul_norm (x y : V) : Real.sin (angle x y) * ‖x‖ = Real.si
n (angle y (x - y)) * ‖x - y‖
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `mul_eq_mul_right_iff`：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsRigh
tCancelMulZero M₀] {a b c : M₀}, a * c = b * c ↔ a = b ∨ c = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `InnerProductGeometry.angle_neg_right`：angle_neg_right (x y : V) : angle 
x (-y) = π - angle x y
· 使用定理 `Real.sin_pi_sub`：sin_pi_sub (x : Real) : sin (π - x) = sin x

--- 原说明 ---
**Law of sines** (sine rule), angle-at-point form.
-/
theorem sin_angle_mul_dist_eq_sin_angle_mul_dist (p₁ p₂ p₃ : P) :
    Real.sin (∠ p₁ p₂ p₃) * dist p₂ p₃ = Real.sin (∠ p₃ p₁ p₂) * dist p₃ p₁ := by
  simp only [dist_comm p₂ p₃, angle]
  rw [dist_eq_norm_vsub V p₃ p₂, dist_eq_norm_vsub V p₃ p₁, InnerProductGeometry.angle_comm,
    sin_angle_mul_norm_eq_sin_angle_mul_norm, vsub_sub_vsub_cancel_right, mul_eq_mul_right_iff]
  left
  rw [InnerProductGeometry.angle_comm, ← neg_vsub_eq_vsub_rev p₁ p₂, angle_neg_right,
    Real.sin_pi_sub]

alias law_sin := sin_angle_mul_dist_eq_sin_angle_mul_dist

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- A variant of the law of sines, angle-at-point form. -/
/-
**EuclideanGeometry.sin_angle_div_dist_eq_sin_angle_div_dist** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：sin_angle_div_dist_eq_sin_angle_div_dist {p₁ p₂ p₃ : P} (h23 : p₂ != p₃) (
h31 : p₃ != p₁) : Real.sin (∠ p₁ p₂ p₃) / dist p₃ p₁ = Real.sin (∠ p₃ p₁ p₂) / d
ist p₂ p₃
参数：h23 : p₂ != p₃；h31 : p₃ != p₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_ne_zero`：dist_ne_zero {x y : γ} : dist x y != 0 ↔ x != y
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_ne_zero`：cons_ne_zero [GroupWithZero M]
 (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) : ((r, x) ::ᵣ l).
eval != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A variant of the law of sines, angle-at-point form.
-/
theorem sin_angle_div_dist_eq_sin_angle_div_dist {p₁ p₂ p₃ : P} (h23 : p₂ ≠ p₃) (h31 : p₃ ≠ p₁) :
    Real.sin (∠ p₁ p₂ p₃) / dist p₃ p₁ = Real.sin (∠ p₃ p₁ p₂) / dist p₂ p₃ := by
  simp [field, dist_ne_zero.mpr h23, dist_ne_zero.mpr h31, mul_comm (dist ..), ← law_sin]

/-- A variant of the law of sines, requiring that the points not be collinear. -/
/-
**EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_eq_dist_mul_sin_angle_div_sin_angle {p₁ p₂ p₃ : P} (h : ¬Collinear Re
al ({p₁, p₂, p₃} : Set P)) : dist p₁ p₂ = dist p₃ p₁ * Real.sin (∠ p₂ p₃ p₁) / R
eal.sin (∠ p₁ p₂ p₃)
参数：h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.sin_pos_of_not_collinear`：sin_pos_of_not_collinear {p₁
 p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) : 0 < Real.sin (∠ p₁ p₂
 p₃)
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_ne_zero`：cons_ne_zero [GroupWithZero M]
 (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) : ((r, x) ::ᵣ l).
eval != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanGeometry.law_sin`：∀ {V : Type u_1} {P : Type u_2} [inst : Norme
dAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [in
st_3 : NormedAd…

--- 原说明 ---
A variant of the law of sines, requiring that the points not be collinear.
-/
theorem dist_eq_dist_mul_sin_angle_div_sin_angle {p₁ p₂ p₃ : P}
    (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    dist p₁ p₂ = dist p₃ p₁ * Real.sin (∠ p₂ p₃ p₁) / Real.sin (∠ p₁ p₂ p₃) := by
  have sin_gt_zero : 0 < Real.sin (∠ p₁ p₂ p₃) := sin_pos_of_not_collinear h
  field_simp
  rw [mul_comm, mul_comm (dist p₃ p₁), law_sin]

/-- **Isosceles Triangle Theorem**: Pons asinorum, angle-at-point form. -/
/-
**EuclideanGeometry.angle_eq_angle_of_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anGeometry`。
形式化陈述：angle_eq_angle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) : ∠
 p₁ p₂ p₃ = ∠ p₁ p₃ p₂
参数：h : dist p₁ p₂ = dist p₁ p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `InnerProductGeometry.angle_sub_eq_angle_sub_rev_of_norm_eq`：angle_sub_eq
_angle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : angle x (x - y) = angle y 
(y - x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖

--- 原说明 ---
**Isosceles Triangle Theorem**: Pons asinorum, angle-at-point form.
-/
theorem angle_eq_angle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂ := by
  rw [dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃] at h
  unfold angle
  convert! angle_sub_eq_angle_sub_rev_of_norm_eq h
  · exact (vsub_sub_vsub_cancel_left p₃ p₂ p₁).symm
  · exact (vsub_sub_vsub_cancel_left p₂ p₃ p₁).symm

/-- Converse of pons asinorum, angle-at-point form. -/
/-
**EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_eq_of_angle_eq_angle_of_angle_ne_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 
∠ p₁ p₃ p₂) (hpi : ∠ p₂ p₁ p₃ != π) : dist p₁ p₂ = dist p₁ p₃
参数：h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂；hpi : ∠ p₂ p₁ p₃ != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `InnerProductGeometry.norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_p
i`：norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V} (h : angle x (
x - y) = angle y (y - x)) (hpi : angle x y != π) : ‖x‖ = ‖y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `InnerProductGeometry.angle_neg_neg`：angle_neg_neg (x y : V) : angle (-x)
 (-y) = angle x y

--- 原说明 ---
Converse of pons asinorum, angle-at-point form.
-/
theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂)
    (hpi : ∠ p₂ p₁ p₃ ≠ π) : dist p₁ p₂ = dist p₁ p₃ := by
  unfold angle at h hpi
  rw [dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃]
  rw [← angle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hpi
  rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁, ← vsub_sub_vsub_cancel_left p₂ p₃ p₁] at h
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h hpi

/-- Converse of pons asinorum, oriented angle-at-point form (given equality of angles mod `π`). -/
/-
**EuclideanGeometry.dist_eq_of_two_zsmul_oangle_eq** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：dist_eq_of_two_zsmul_oangle_eq [Module.Oriented Real V (Fin 2)] [Fact (Mod
ule.finrank Real V = 2)] {p₁ p₂ p₃ : P} (h : (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) 
• ∡ p₂ p₃ p₁) (h0 : ∡ p₃ p₁ p₂ != 0) (hpi : ∡ p₃ p₁ p₂ != π) : dist p₁ p₂ = dist
 p₁ p₃
参数：Fin 2；Module.finrank Real V = 2；h : (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₂
 p₃ p₁；h0 : ∡ p₃ p₁ p₂ != 0；hpi : ∡ p₃ p₁ p₂ != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `Orientation.norm_eq_of_two_zsmul_oangle_sub_eq`：norm_eq_of_two_zsmul_oan
gle_sub_eq {x y : V} (h : (2 : Int) • o.oangle x (x - y) = (2 : Int) • o.oangle 
(y - x) y) (h0 : o.oangle x y != 0) …
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_neg`：oangle_neg_neg (x y : V) : o.oangle (-x) (-y
) = o.oangle x y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂

--- 原说明 ---
Converse of pons asinorum, oriented angle-at-point form (given equality of angle
s mod `π`).
-/
theorem dist_eq_of_two_zsmul_oangle_eq [Module.Oriented ℝ V (Fin 2)]
    [Fact (Module.finrank ℝ V = 2)] {p₁ p₂ p₃ : P} (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₂ p₃ p₁)
    (h0 : ∡ p₃ p₁ p₂ ≠ 0) (hpi : ∡ p₃ p₁ p₂ ≠ π) : dist p₁ p₂ = dist p₁ p₃ := by
  convert!
    (Orientation.norm_eq_of_two_zsmul_oangle_sub_eq (x := p₃ -ᵥ p₁) (y := p₂ -ᵥ p₁) ?_ ?_ h0
        hpi).symm
  · rw [dist_eq_norm_vsub']
  · rw [dist_eq_norm_vsub']
  · rw [eq_comm, o.oangle_rev, ← o.oangle_neg_neg]
    nth_rw 2 [o.oangle_rev, ← o.oangle_neg_neg]
    simp_rw [smul_neg, neg_inj]
    simp_rw [oangle] at h
    convert! h <;> simp

/-- The **sum of the angles of a triangle** (possibly degenerate, where two
given vertices are distinct), angle-at-point. -/
/-
**EuclideanGeometry.angle_add_angle_add_angle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：angle_add_angle_add_angle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ != p₁) : ∠ p₁
 p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π
参数：p₃ : P；h : p₂ != p₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductGeometry.angle_neg_neg`：angle_neg_neg (x y : V) : angle (-x)
 (-y) = angle x y
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `InnerProductGeometry.angle_add_angle_sub_add_angle_sub_eq_pi`：angle_add_
angle_sub_add_angle_sub_eq_pi (x : V) {y : V} (hy : y != 0) : angle x y + angle 
x (x - y) + angle y (y - x) = π
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂

--- 原说明 ---
The **sum of the angles of a triangle** (possibly degenerate, where two
given vertices are distinct), angle-at-point.
-/
theorem angle_add_angle_add_angle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π := by
  rw [add_assoc, add_comm, add_comm (∠ p₂ p₃ p₁), angle_comm p₂ p₃ p₁]
  unfold angle
  rw [← angle_neg_neg (p₁ -ᵥ p₃), ← angle_neg_neg (p₁ -ᵥ p₂), neg_vsub_eq_vsub_rev,
    neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, ←
    vsub_sub_vsub_cancel_right p₃ p₂ p₁, ← vsub_sub_vsub_cancel_right p₂ p₃ p₁]
  exact angle_add_angle_sub_add_angle_sub_eq_pi _ fun he => h (vsub_eq_zero_iff_eq.1 he)

/-- The **Exterior angle theorem**. an exterior angle of a triangle is equal to the sum of the
measures of the remote interior angles. -/
/-
**EuclideanGeometry.exterior_angle_eq_angle_add_angle** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：exterior_angle_eq_angle_add_angle {p₁ p₂ p₃ : P} (p : P) (h : Sbtw Real p 
p₁ p₂) : ∠ p₃ p₁ p = ∠ p₁ p₃ p₂ + ∠ p₃ p₂ p₁
参数：p : P；h : Sbtw Real p p₁ p₂。
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The **Exterior angle theorem**. an exterior angle of a triangle is equal to the 
sum of the
measures of the remote interior angles.
-/
theorem exterior_angle_eq_angle_add_angle {p₁ p₂ p₃ : P} (p : P) (h : Sbtw ℝ p p₁ p₂) :
    ∠ p₃ p₁ p = ∠ p₁ p₃ p₂ + ∠ p₃ p₂ p₁ := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₃ h.angle₁₂₃_eq_pi,
    angle_add_angle_add_angle_eq_pi p₃ h.right_ne.symm, angle_comm p₃ p₁ p₂]

/-- The **sum of the angles of a triangle** (possibly degenerate, where the triangle is a line),
oriented angles at point. -/
/-
**EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry`。
形式化陈述：oangle_add_oangle_add_oangle_eq_pi [Module.Oriented Real V (Fin 2)] [Fact 
(Module.finrank Real V = 2)] {p₁ p₂ p₃ : P} (h21 : p₂ != p₁) (h32 : p₃ != p₂) (h
13 : p₁ != p₃) : ∡ p₁ p₂ p₃ + ∡ p₂ p₃ p₁ + ∡ p₃ p₁ p₂ = π
参数：Fin 2；Module.finrank Real V = 2；h21 : p₂ != p₁；h32 : p₃ != p₂；h13 : p₁ != p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Orientation.oangle_add_cyc3_neg_left`：oangle_add_cyc3_neg_left {x y z : 
V} (hx : x != 0) (hy : y != 0) (hz : z != 0) : o.oangle (-x) y + o.oangle (-y) z
 + o.oangle (-z) x = π
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
The **sum of the angles of a triangle** (possibly degenerate, where the triangle
 is a line),
oriented angles at point.
-/
theorem oangle_add_oangle_add_oangle_eq_pi [Module.Oriented ℝ V (Fin 2)]
    [Fact (Module.finrank ℝ V = 2)] {p₁ p₂ p₃ : P} (h21 : p₂ ≠ p₁) (h32 : p₃ ≠ p₂)
    (h13 : p₁ ≠ p₃) : ∡ p₁ p₂ p₃ + ∡ p₂ p₃ p₁ + ∡ p₃ p₁ p₂ = π := by
  simpa only [neg_vsub_eq_vsub_rev] using!
    positiveOrientation.oangle_add_cyc3_neg_left (vsub_ne_zero.mpr h21) (vsub_ne_zero.mpr h32)
      (vsub_ne_zero.mpr h13)

/-- Given a triangle `ABC` with `A ≠ B` and `A ≠ C` and a point `P` on `BC`,
`∠ B A P + ∠ P A C = ∠ B A C`. -/
/-
**EuclideanGeometry.angle_add_of_ne_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：angle_add_of_ne_of_ne {a b c p : P} (hb : a != b) (hc : a != c) (hp : Wbtw
 Real b p c) : ∠ b a p + ∠ p a c = ∠ b a c
参数：hb : a != b；hc : a != c；hp : Wbtw Real b p c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `EuclideanGeometry.angle_self_of_ne`：angle_self_of_ne (h : p != p₀) : ∠ p
 p₀ p = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`：angle_add_angle_add_a
ngle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ != p₁) : ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ 
p₁ p₂ = π
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.angle_eq_pi_iff_sbtw`：angle_eq_pi_iff_sbtw {p₁ p₂ p₃ :
 P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
Given a triangle `ABC` with `A ≠ B` and `A ≠ C` and a point `P` on `BC`,
`∠ B A P + ∠ P A C = ∠ B A C`.
-/
lemma angle_add_of_ne_of_ne {a b c p : P} (hb : a ≠ b) (hc : a ≠ c) (hp : Wbtw ℝ b p c) :
    ∠ b a p + ∠ p a c = ∠ b a c := by
  by_cases pb : p = b; · simpa [pb] using angle_self_of_ne hb.symm
  by_cases pc : p = c; · simpa [pc] using angle_self_of_ne hc.symm
  have ea := angle_add_angle_add_angle_eq_pi c hb
  have eb := angle_add_angle_add_angle_eq_pi p hb
  have ec := angle_add_angle_add_angle_eq_pi p hc.symm
  replace hp : ∠ b p c = π := angle_eq_pi_iff_sbtw.mpr ⟨hp, pb, pc⟩
  have hp' : ∠ c p b = π := by rwa [angle_comm] at hp
  rw [angle_comm p b a, angle_eq_angle_of_angle_eq_pi a hp, angle_comm a b c] at eb
  rw [angle_eq_angle_of_angle_eq_pi a hp', angle_comm c p a] at ec
  have ep := angle_add_angle_eq_pi_of_angle_eq_pi a hp
  linarith only [ea, eb, ec, ep]

/-- If `X` lies strictly between `A` and `C`, then `∠ A P X + ∠ X P C = ∠ A P C`,
with no nondegeneracy assumption on the point `P`. -/
/-
**EuclideanGeometry.angle_add_angle_eq_of_sbtw** 是 Mathlib 中的一个引理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：angle_add_angle_eq_of_sbtw {a c p x : P} (hx : Sbtw Real a x c) : ∠ a p x 
+ ∠ x p c = ∠ a p c
参数：hx : Sbtw Real a x c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_self_left`：∀ {V : Type u_1} {P : Type u_2} [inst
 : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sbtw.angle_eq_right`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCo
mmGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 :
 NormedAd…
· 使用定理 `EuclideanGeometry.angle_self_of_ne`：angle_self_of_ne (h : p != p₀) : ∠ p
 p₀ p = 0
· 使用定理 `Sbtw.ne_left`：Sbtw.ne_left {x y z : P} (h : Sbtw R x y z) : y != x
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Sbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `Sbtw.left_ne_right`：Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : 
x != z
· 使用定理 `EuclideanGeometry.angle_self_right`：∀ {V : Type u_1} {P : Type u_2} [ins
t : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAd…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `EuclideanGeometry.angle_add_of_ne_of_ne`：angle_add_of_ne_of_ne {a b c p 
: P} (hb : a != b) (hc : a != c) (hp : Wbtw Real b p c) : ∠ b a p + ∠ p a c = ∠ 
b a c
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z

--- 原说明 ---
If `X` lies strictly between `A` and `C`, then `∠ A P X + ∠ X P C = ∠ A P C`,
with no nondegeneracy assumption on the point `P`.
-/
lemma angle_add_angle_eq_of_sbtw {a c p x : P} (hx : Sbtw ℝ a x c) :
    ∠ a p x + ∠ x p c = ∠ a p c := by
  rcases eq_or_ne p a with rfl | hpa
  · simp [(hx.angle_eq_right x).symm.trans (angle_self_of_ne hx.ne_left)]
  rcases eq_or_ne p c with rfl | hpc
  · simp [(hx.symm.angle_eq_right a).trans (angle_self_of_ne hx.left_ne_right)]
  exact angle_add_of_ne_of_ne hpa hpc hx.wbtw

/-- If `B` lies on the same ray from `P` as a point `X` strictly between `A` and `C`,
then `∠ A P B + ∠ B P C = ∠ A P C`. -/
/-
**EuclideanGeometry.angle_add_angle_eq_of_sbtw_of_sameRay** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：angle_add_angle_eq_of_sbtw_of_sameRay {a b c p x : P} (hx : Sbtw Real a x 
c) (hxb : SameRay Real (x -ᵥ p) (b -ᵥ p)) (hb : b != p) : ∠ a p b + ∠ b p c = ∠ 
a p c
参数：hx : Sbtw Real a x c；hxb : SameRay Real (x -ᵥ p) (b -ᵥ p)；hb : b != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Sbtw.angle₁₂₃_eq_pi`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCo
mmGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 :
 NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_pos_left_iff_sameRay`：exists_pos_left_iff_sameRay (hx : x != 0) (
hy : y != 0) : (exists r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EuclideanGeometry.angle_smul_right_of_pos`：angle_smul_right_of_pos (p₁ :
 P) {p₂ p₃ p₄ : P} {r : Real} (hr : 0 < r) (hrv : r • (p₄ -ᵥ p₂) = p₃ -ᵥ p₂) : ∠
 p₁ p₂ p₃ = ∠ p₁ p₂ p₄
· 使用定理 `EuclideanGeometry.angle_smul_left_of_pos`：angle_smul_left_of_pos {p₁ p₂ 
p₄ : P} (p₃ : P) {r : Real} (hr : 0 < r) (hrv : r • (p₄ -ᵥ p₂) = p₁ -ᵥ p₂) : ∠ p
₁ p₂ p₃ = ∠ p₄ p₂ p₃
· 使用引理 `EuclideanGeometry.angle_add_angle_eq_of_sbtw`：angle_add_angle_eq_of_sbtw
 {a c p x : P} (hx : Sbtw Real a x c) : ∠ a p x + ∠ x p c = ∠ a p c

--- 原说明 ---
If `B` lies on the same ray from `P` as a point `X` strictly between `A` and `C`
,
then `∠ A P B + ∠ B P C = ∠ A P C`.
-/
theorem angle_add_angle_eq_of_sbtw_of_sameRay {a b c p x : P}
    (hx : Sbtw ℝ a x c) (hxb : SameRay ℝ (x -ᵥ p) (b -ᵥ p)) (hb : b ≠ p) :
    ∠ a p b + ∠ b p c = ∠ a p c := by
  rcases eq_or_ne p x with rfl | hpx
  · have hpi : ∠ a p c = π := hx.angle₁₂₃_eq_pi
    rw [hpi, angle_comm a p b]
    exact angle_add_angle_eq_pi_of_angle_eq_pi b hpi
  obtain ⟨r, hr, hrb⟩ := (exists_pos_left_iff_sameRay (by aesop) (by aesop)).2 hxb
  have hab : ∠ a p b = ∠ a p x := angle_smul_right_of_pos a hr hrb
  have hbc : ∠ b p c = ∠ x p c := angle_smul_left_of_pos c hr hrb
  rw [hab, hbc]
  exact angle_add_angle_eq_of_sbtw hx

/-- **Stewart's Theorem**. -/
/-
**EuclideanGeometry.dist_sq_mul_dist_add_dist_sq_mul_dist** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) : di
st a b ^ 2 * dist c p + dist a c ^ 2 * dist b p = dist b c * (dist a p ^ 2 + dis
t b p * dist c p)
参数：a b c p : P；h : ∠ b p c = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.law_cos`：∀ {V : Type u_1} {P : Type u_2} [inst : Norme
dAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [in
st_3 : NormedAd…
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用定理 `EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Real.cos_pi_sub`：cos_pi_sub (x : Real) : cos (π - x) = -cos x
· 使用定理 `EuclideanGeometry.dist_eq_add_dist_of_angle_eq_pi`：dist_eq_add_dist_of_a
ngle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : dist p₁ p₃ = dist p₁ p₂ + dist 
p₃ p₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
**Stewart's Theorem**.
-/
theorem dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) :
    dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p =
    dist b c * (dist a p ^ 2 + dist b p * dist c p) := by
  rw [pow_two, pow_two, law_cos a p b, law_cos a p c,
    eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a h), Real.cos_pi_sub,
    dist_eq_add_dist_of_angle_eq_pi h]
  ring

/-- **Apollonius's Theorem**. -/
/-
**EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dis
t_sq** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : 
P) : dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint Real b c) ^ 2 + (dist b
 c / 2) ^ 2)
参数：a b c : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `midpoint_self`：midpoint_self (x : P) : midpoint R x x = x
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_pos`：dist_pos {x y : γ} : 0 < dist x y ↔ x != y
· 使用定理 `EuclideanGeometry.dist_sq_mul_dist_add_dist_sq_mul_dist`：dist_sq_mul_dis
t_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) : dist a b ^ 2 * dist c p
 + dist a c ^ 2 * dist b p = dist b c * (dist…
· 使用定理 `EuclideanGeometry.angle_midpoint_eq_pi`：angle_midpoint_eq_pi (p₁ p₂ : P)
 (hp₁p₂ : p₁ != p₂) : ∠ p₁ (midpoint Real p₁ p₂) p₂ = π
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
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
（共 103 条，此处仅展示前 30 条）

--- 原说明 ---
**Apollonius's Theorem**.
-/
theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by
  by_cases hbc : b = c
  · simp [hbc, midpoint_self, dist_self, two_mul]
  · let m := midpoint ℝ b c
    have : dist b c ≠ 0 := (dist_pos.mpr hbc).ne'
    have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc)
    simp only [m, dist_left_midpoint, dist_right_midpoint, Real.norm_two] at hm
    calc
      dist a b ^ 2 + dist a c ^ 2 = 2 / dist b c * (dist a b ^ 2 *
        ((2 : ℝ)⁻¹ * dist b c) + dist a c ^ 2 * (2⁻¹ * dist b c)) := by
        field
      _ = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by
        rw [hm]
        field
/-
**EuclideanGeometry.dist_mul_of_eq_angle_of_dist_mul** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : Real) (h : ∠ a'
 b' c' = ∠ a b c) (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist
 c b) : dist a' c' = r * dist a c
参数：a b c a' b' c' : P；r : Real；h : ∠ a' b' c' = ∠ a b c；hab : dist a' b' = r * d
ist a b；hcb : dist c' b' = r * dist c b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `EuclideanGeometry.law_cos`：∀ {V : Type u_1} {P : Type u_2} [inst : Norme
dAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [in
st_3 : NormedAd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
（共 63 条，此处仅展示前 30 条）
-/
theorem dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : ℝ) (h : ∠ a' b' c' = ∠ a b c)
    (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist c b) :
    dist a' c' = r * dist a c := by
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2 := calc
    dist a' c' ^ 2 =
        dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * Real.cos (∠ a' b' c') := by
      simp [pow_two, law_cos a' b' c']
    _ = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * Real.cos (∠ a b c)) := by
      rw [h, hab, hcb]; ring
    _ = (r * dist a c) ^ 2 := by simp [pow_two, ← law_cos a b c]; ring
  by_cases hab₁ : a = b
  · have hab'₁ : a' = b' := by
      rw [← dist_eq_zero, hab, dist_eq_zero.mpr hab₁, mul_zero r]
    rw [hab₁, hab'₁, dist_comm b' c', dist_comm b c, hcb]
  · have h1 : 0 ≤ r * dist a b := by rw [← hab]; exact dist_nonneg
    have h2 : 0 ≤ r := nonneg_of_mul_nonneg_left h1 (dist_pos.mpr hab₁)
    exact (sq_eq_sq₀ dist_nonneg (mul_nonneg h2 dist_nonneg)).mp h'

/-- In a triangle, the smaller angle is opposite the smaller side. -/
/-
**EuclideanGeometry.dist_lt_of_angle_lt** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeom
etry`。
形式化陈述：dist_lt_of_angle_lt {a b c : P} (h : ¬Collinear Real ({a, b, c} : Set P)) 
: ∠ a c b < ∠ a b c -> dist a b < dist a c
参数：h : ¬Collinear Real ({a, b, c} : Set P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.law_sin`：∀ {V : Type u_1} {P : Type u_2} [inst : Norme
dAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [in
st_3 : NormedAd…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_pos`：dist_pos {x y : γ} : 0 < dist x y ↔ x != y
· 使用定理 `ne₁₃_of_not_collinear`：ne₁₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collin
ear k ({p₁, p₂, p₃} : Set P)) : p₁ != p₃
· 使用定理 `Real.sin_nonneg_of_mem_Icc`：sin_nonneg_of_mem_Icc {x : Real} (hx : x in 
Icc 0 π) : 0 <= sin x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.sin_lt_sin_of_lt_of_le_pi_div_two`：sin_lt_sin_of_lt_of_le_pi_div_tw
o {x y : Real} (hx₁ : -(π / 2) <= x) (hy₂ : y <= π / 2) (hxy : x < y) : sin x < 
sin y
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
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
（共 94 条，此处仅展示前 30 条）

--- 原说明 ---
In a triangle, the smaller angle is opposite the smaller side.
-/
theorem dist_lt_of_angle_lt {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b < ∠ a b c → dist a b < dist a c := by
  have hsin := law_sin c b a
  rw [dist_comm b a, angle_comm c b a] at hsin
  have hac : dist a c > 0 := dist_pos.mpr (ne₁₃_of_not_collinear h)
  have hsinabc : Real.sin (∠ a b c) ≥ 0 := by
    apply Real.sin_nonneg_of_mem_Icc
    simp [angle_nonneg, angle_le_pi]
  intro h1
  by_cases! h2 : ∠ a b c ≤ π / 2
  · have h3 : Real.sin (∠ a c b) < Real.sin (∠ a b c) := by
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [angle_nonneg a c b]) h2 h1
    by_contra! w
    have h4 : Real.sin (∠ a c b) * dist a c < Real.sin (∠ a b c) * dist a b := by
      exact mul_lt_mul h3 w hac hsinabc
    linarith
  · by_contra! w
    have h3 : Real.sin (∠ a b c) ≤ Real.sin (∠ a c b) := by
      by_contra! w1
      have h4 : Real.sin (∠ a c b) * dist a c < Real.sin (∠ a b c) * dist a b := by
        exact mul_lt_mul w1 w hac hsinabc
      linarith
    rw [← Real.sin_pi_sub (∠ a b c)] at h3
    have h5 : π - ∠ a b c < π / 2 := by linarith
    have h6 : π - ∠ a b c ≤ ∠ a c b := by
      by_contra! w1
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [angle_nonneg a c b]) h5.le w1
      linarith
    have h7 := angle_add_angle_add_angle_eq_pi c (ne₁₂_of_not_collinear h).symm
    rw [angle_comm b c a] at h7
    have h8 : ∠ c a b > 0 := by
      rw [angle_comm]
      rw [show ({a, b, c} : Set P) = {b, a, c} by exact Set.insert_comm a b {c}] at h
      exact angle_pos_of_not_collinear h
    linarith
/-
**EuclideanGeometry.angle_lt_iff_dist_lt** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeo
metry`。
形式化陈述：angle_lt_iff_dist_lt {a b c : P} (h : ¬Collinear Real ({a, b, c} : Set P))
 : ∠ a c b < ∠ a b c ↔ dist a b < dist a c
参数：h : ¬Collinear Real ({a, b, c} : Set P)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.dist_lt_of_angle_lt`：dist_lt_of_angle_lt {a b c : P} (
h : ¬Collinear Real ({a, b, c} : Set P)) : ∠ a c b < ∠ a b c -> dist a b < dist 
a c
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi`：dist_eq_of_a
ngle_eq_angle_of_angle_ne_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂) (hpi :
 ∠ p₂ p₁ p₃ != π) : dist p₁ p₂ = dist p₁ p₃
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
（共 43 条，此处仅展示前 30 条）
-/
theorem angle_lt_iff_dist_lt {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b < ∠ a b c ↔ dist a b < dist a c := by
  constructor
  case mp =>
    exact dist_lt_of_angle_lt h
  case mpr =>
    intro h1
    by_contra! w
    rcases w.eq_or_lt with h2 | h3
    · have h4 : dist a b = dist a c := by
        apply dist_eq_of_angle_eq_angle_of_angle_ne_pi h2
        rw [show ({a, b, c} : Set P) = {b, a, c} by exact Set.insert_comm a b {c}] at h
        linarith [angle_lt_pi_of_not_collinear h]
      linarith
    · rw [show ({a, b, c} : Set P) = {a, c, b} by grind] at h
      have h5 := dist_lt_of_angle_lt h h3
      linarith
/-
**EuclideanGeometry.angle_le_iff_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeo
metry`。
形式化陈述：angle_le_iff_dist_le {a b c : P} (h : ¬Collinear Real ({a, b, c} : Set P))
 : ∠ a c b <= ∠ a b c ↔ dist a b <= dist a c
参数：h : ¬Collinear Real ({a, b, c} : Set P)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `EuclideanGeometry.angle_lt_iff_dist_lt`：angle_lt_iff_dist_lt {a b c : P}
 (h : ¬Collinear Real ({a, b, c} : Set P)) : ∠ a c b < ∠ a b c ↔ dist a b < dist
 a c
-/
theorem angle_le_iff_dist_le {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b ≤ ∠ a b c ↔ dist a b ≤ dist a c := by
  rw [show ({a, b, c} : Set P) = {a, c, b} by grind] at h
  simpa using (angle_lt_iff_dist_lt h).not

/-- The greatest angle of a possibly degenerate triangle is at least `π / 3`. -/
/-
**EuclideanGeometry.pi_div_three_le_angle_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：pi_div_three_le_angle_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ <= ∠ p
₁ p₂ p₃) (h₃₁₂ : ∠ p₃ p₁ p₂ <= ∠ p₁ p₂ p₃) : π / 3 <= ∠ p₁ p₂ p₃
参数：h₂₃₁ : ∠ p₂ p₃ p₁ <= ∠ p₁ p₂ p₃；h₃₁₂ : ∠ p₃ p₁ p₂ <= ∠ p₁ p₂ p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_self_left`：∀ {V : Type u_1} {P : Type u_2} [inst
 : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAd…
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
（共 67 条，此处仅展示前 30 条）

--- 原说明 ---
The greatest angle of a possibly degenerate triangle is at least `π / 3`.
-/
lemma pi_div_three_le_angle_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ ≤ ∠ p₁ p₂ p₃)
    (h₃₁₂ : ∠ p₃ p₁ p₂ ≤ ∠ p₁ p₂ p₃) : π / 3 ≤ ∠ p₁ p₂ p₃ := by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

/-- The greatest angle of a possibly degenerate triangle is more than `π / 3`, unless all angles
are equal. -/
/-
**EuclideanGeometry.pi_div_three_lt_angle_of_le_of_le_of_ne** 是 Mathlib 中的一个引理，位
于命名空间 `EuclideanGeometry`。
形式化陈述：pi_div_three_lt_angle_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ 
<= ∠ p₁ p₂ p₃) (h₃₁₂ : ∠ p₃ p₁ p₂ <= ∠ p₁ p₂ p₃) (hne : ∠ p₁ p₂ p₃ != ∠ p₂ p₃ p₁
 ∨ ∠ p₁ p₂ p₃ != ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ != ∠ p₃ p₁ p₂) : π / 3 < ∠ p₁ p₂ p₃
参数：h₂₃₁ : ∠ p₂ p₃ p₁ <= ∠ p₁ p₂ p₃；h₃₁₂ : ∠ p₃ p₁ p₂ <= ∠ p₁ p₂ p₃；hne : ∠ p₁ p₂
 p₃ != ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ != ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ != ∠ p₃ p₁ p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_self_left`：∀ {V : Type u_1} {P : Type u_2} [inst
 : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAd…
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
The greatest angle of a possibly degenerate triangle is more than `π / 3`, unles
s all angles
are equal.
-/
lemma pi_div_three_lt_angle_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ ≤ ∠ p₁ p₂ p₃)
    (h₃₁₂ : ∠ p₃ p₁ p₂ ≤ ∠ p₁ p₂ p₃)
    (hne : ∠ p₁ p₂ p₃ ≠ ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ ≠ ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ ≠ ∠ p₃ p₁ p₂) :
    π / 3 < ∠ p₁ p₂ p₃ := by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

/-- The least angle of a possibly degenerate triangle is at most `π / 3`, unless all three vertices
are equal. -/
/-
**EuclideanGeometry.angle_le_pi_div_three_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：angle_le_pi_div_three_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ <= ∠ p
₂ p₃ p₁) (h₃₁₂ : ∠ p₁ p₂ p₃ <= ∠ p₃ p₁ p₂) (hnd : p₁ != p₂ ∨ p₁ != p₃ ∨ p₂ != p₃
) : ∠ p₁ p₂ p₃ <= π / 3
参数：h₂₃₁ : ∠ p₁ p₂ p₃ <= ∠ p₂ p₃ p₁；h₃₁₂ : ∠ p₁ p₂ p₃ <= ∠ p₃ p₁ p₂；hnd : p₁ != p
₂ ∨ p₁ != p₃ ∨ p₂ != p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_self_left`：∀ {V : Type u_1} {P : Type u_2} [inst
 : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAd…
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 75 条，此处仅展示前 30 条）

--- 原说明 ---
The least angle of a possibly degenerate triangle is at most `π / 3`, unless all
 three vertices
are equal.
-/
lemma angle_le_pi_div_three_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ ≤ ∠ p₂ p₃ p₁)
    (h₃₁₂ : ∠ p₁ p₂ p₃ ≤ ∠ p₃ p₁ p₂) (hnd : p₁ ≠ p₂ ∨ p₁ ≠ p₃ ∨ p₂ ≠ p₃) :
    ∠ p₁ p₂ p₃ ≤ π / 3 := by
  by_cases h : p₂ = p₁
  · subst h
    simp_all [angle_self_of_ne]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

/-- The least angle of a possibly degenerate triangle is less than `π / 3`, unless all angles are
equal. -/
/-
**EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne** 是 Mathlib 中的一个引理，位
于命名空间 `EuclideanGeometry`。
形式化陈述：angle_lt_pi_div_three_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ 
<= ∠ p₂ p₃ p₁) (h₃₁₂ : ∠ p₁ p₂ p₃ <= ∠ p₃ p₁ p₂) (hne : ∠ p₁ p₂ p₃ != ∠ p₂ p₃ p₁
 ∨ ∠ p₁ p₂ p₃ != ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ != ∠ p₃ p₁ p₂) : ∠ p₁ p₂ p₃ < π / 3
参数：h₂₃₁ : ∠ p₁ p₂ p₃ <= ∠ p₂ p₃ p₁；h₃₁₂ : ∠ p₁ p₂ p₃ <= ∠ p₃ p₁ p₂；hne : ∠ p₁ p₂
 p₃ != ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ != ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ != ∠ p₃ p₁ p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_self_left`：∀ {V : Type u_1} {P : Type u_2} [inst
 : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
The least angle of a possibly degenerate triangle is less than `π / 3`, unless a
ll angles are
equal.
-/
lemma angle_lt_pi_div_three_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ ≤ ∠ p₂ p₃ p₁)
    (h₃₁₂ : ∠ p₁ p₂ p₃ ≤ ∠ p₃ p₁ p₂)
    (hne : ∠ p₁ p₂ p₃ ≠ ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ ≠ ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ ≠ ∠ p₃ p₁ p₂) :
    ∠ p₁ p₂ p₃ < π / 3 := by
  by_cases h : p₂ = p₁
  · subst h
    by_cases h₂₃ : p₂ = p₃
    · subst h₂₃
      simp at hne
    · simp_all [angle_self_of_ne]
      linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

end EuclideanGeometry

