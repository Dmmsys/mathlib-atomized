/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson
-/
module

public import Mathlib.Geometry.Euclidean.Sphere.Power
public import Mathlib.Geometry.Euclidean.Triangle

/-!
# Ptolemy's theorem

This file proves Ptolemy's theorem on the lengths of the diagonals and sides of a cyclic
quadrilateral.

## Main theorems

* `mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`: Ptolemy’s Theorem (Freek No. 95).

TODO: The current statement of Ptolemy’s theorem works around the lack of a "cyclic polygon" concept
in mathlib, which is what the theorem statement would naturally use (or two such concepts, since
both a strict version, where all vertices must be distinct, and a weak version, where consecutive
vertices may be equal, would be useful; Ptolemy's theorem should then use the weak one).

An API needs to be built around that concept, which would include:
- strict cyclic implies weak cyclic,
- weak cyclic and consecutive points distinct implies strict cyclic,
- weak/strict cyclic implies weak/strict cyclic for any subsequence,
- any three points on a sphere are weakly or strictly cyclic according to whether they are distinct,
- any number of points on a sphere intersected with a two-dimensional affine subspace are cyclic in
  some order,
- a list of points is cyclic if and only if its reversal is,
- a list of points is cyclic if and only if any cyclic permutation is, while other permutations
  are not when the points are distinct,
- a point P where the diagonals of a cyclic polygon cross exists (and is unique) with weak/strict
  betweenness depending on weak/strict cyclicity,
- four points on a sphere with such a point P are cyclic in the appropriate order,

and so on.
-/

public section


open Real

open scoped EuclideanGeometry RealInnerProductSpace Real

namespace EuclideanGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- **Ptolemy’s Theorem**. -/
/-
**EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：mul_dist_add_mul_dist_eq_mul_dist_of_cospherical {a b c d p : P} (h : Cosp
herical ({a, b, c, d} : Set P)) (hapc : ∠ a p c = π) (hbpd : ∠ b p d = π) : dist
 a b * dist c d + dist b c * dist d a = dist a c * dist b d
参数：h : Cospherical ({a, b, c, d} : Set P)；hapc : ∠ a p c = π；hbpd : ∠ b p d = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`：mu
l_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P} (h : Cospherica
l ({a, b, c, d} : Set P)) (hapb : ∠ a p b = π) (hcpd : ∠ c…
· 使用定理 `EuclideanGeometry.left_dist_ne_zero_of_angle_eq_pi`：left_dist_ne_zero_of
_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : dist p₁ p₂ != 0
· 使用定理 `EuclideanGeometry.dist_mul_of_eq_angle_of_dist_mul`：dist_mul_of_eq_angle
_of_dist_mul (a b c a' b' c' : P) (r : Real) (h : ∠ a' b' c' = ∠ a b c) (hab : d
ist a' b' = r * dist a b) (hcb : dist c'…
· 使用定理 `EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi`：angle_eq
_angle_of_angle_eq_pi_of_angle_eq_pi {p₁ p₂ p₃ p₄ p₅ : P} (hapc : ∠ p₁ p₅ p₃ = π
) (hbpd : ∠ p₂ p₅ p₄ = π) : ∠ p₁ p₅ p₂ = ∠ p₃ p₅ p₄
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
**Ptolemy’s Theorem**.
-/
theorem mul_dist_add_mul_dist_eq_mul_dist_of_cospherical {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapc : ∠ a p c = π) (hbpd : ∠ b p d = π) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d := by
  have h' : Cospherical ({a, c, b, d} : Set P) := by rwa [Set.insert_comm c b {d}]
  have hmul := mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi h' hapc hbpd
  have hbp := left_dist_ne_zero_of_angle_eq_pi hbpd
  have h₁ : dist c d = dist c p / dist b p * dist a b := by
    rw [dist_mul_of_eq_angle_of_dist_mul b p a c p d, dist_comm a b]
    · rw [angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hbpd hapc, angle_comm]
    all_goals simp [field, mul_comm, hmul]
  have h₂ : dist d a = dist a p / dist b p * dist b c := by
    rw [dist_mul_of_eq_angle_of_dist_mul c p b d p a, dist_comm c b]
    · rwa [angle_comm, angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi]; rwa [angle_comm]
    all_goals simp [field, mul_comm, hmul]
  have h₃ : dist d p = dist a p * dist c p / dist b p := by simp [field, hmul]
  have h₄ : ∀ x y : ℝ, x * (y * x) = x * x * y := fun x y => by rw [mul_left_comm, mul_comm]
  simp [field, h₁, h₂, dist_eq_add_dist_of_angle_eq_pi hbpd, h₃, dist_comm a b, h₄, ← sq,
    dist_sq_mul_dist_add_dist_sq_mul_dist b, hapc]

end EuclideanGeometry

