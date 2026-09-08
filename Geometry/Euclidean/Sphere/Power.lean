/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson, Li Jiale
-/
module


public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Tangent

import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Similarity

/-!
# Power of a point (intersecting chords and secants)

This file proves basic geometrical results about power of a point (intersecting chords and
secants) in spheres in real inner product spaces and Euclidean affine spaces.

## Main definitions

* `Sphere.power`: The power of a point with respect to a sphere.

## Main theorems

* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`: Intersecting Chords Theorem (Freek No. 55).
* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`: Intersecting Secants Theorem.
* `Sphere.mul_dist_eq_abs_power`: The product of distances equals the absolute value of power.
* `Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant`: Tangent-Secant Theorem.
-/

@[expose] public section


open Real EuclideanGeometry RealInnerProductSpace Real Module FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace InnerProductGeometry

/-!
### Geometrical results on spheres in real inner product spaces

This section develops some results on spheres in real inner product spaces,
which are used to deduce corresponding results for Euclidean affine spaces.
-/


/-
**InnerProductGeometry.mul_norm_eq_abs_sub_sq_norm** 是 Mathlib 中的一个定理，位于命名空间 `In
nerProductGeometry`。
形式化陈述：mul_norm_eq_abs_sub_sq_norm {x y z : V} (h₁ : exists k : Real, x = k • y) 
(h₃ : ‖z - y‖ = ‖z + y‖) : ‖x - y‖ * ‖x + y‖ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2|
参数：h₁ : exists k : Real, x = k • y；h₃ : ‖z - y‖ = ‖z + y‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductGeometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two`：norm_
add_eq_norm_sub_iff_angle_eq_pi_div_two (x y : V) : ‖x + y‖ = ‖x - y‖ ↔ angle x 
y = π / 2
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 78 条，此处仅展示前 30 条）

--- 原说明 ---
### Geometrical results on spheres in real inner product spaces

This section develops some results on spheres in real inner product spaces,
which are used to deduce corresponding results for Euclidean affine spaces.
-/
theorem mul_norm_eq_abs_sub_sq_norm {x y z : V} (h₁ : ∃ k : ℝ, x = k • y)
    (h₃ : ‖z - y‖ = ‖z + y‖) : ‖x - y‖ * ‖x + y‖ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| := by
  obtain ⟨r, hr⟩ := h₁
  have hzy : ⟪z, y⟫ = 0 := by
    rwa [inner_eq_zero_iff_angle_eq_pi_div_two, ← norm_add_eq_norm_sub_iff_angle_eq_pi_div_two,
      eq_comm]
  have hzx : ⟪z, x⟫ = 0 := by rw [hr, inner_smul_right, hzy, mul_zero]
  calc
    ‖x - y‖ * ‖x + y‖ = ‖(r - 1) • y‖ * ‖(r + 1) • y‖ := by simp [sub_smul, add_smul, hr]
    _ = ‖r - 1‖ * ‖y‖ * (‖r + 1‖ * ‖y‖) := by simp_rw [norm_smul]
    _ = ‖r - 1‖ * ‖r + 1‖ * ‖y‖ ^ 2 := by ring
    _ = |(r - 1) * (r + 1) * ‖y‖ ^ 2| := by simp [abs_mul]
    _ = |r ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2| := by ring_nf
    _ = |‖x‖ ^ 2 - ‖y‖ ^ 2| := by simp [hr, norm_smul, mul_pow, sq_abs]
    _ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| := by
      simp [norm_add_sq_real, norm_sub_sq_real, hzy, hzx, abs_sub_comm]

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on spheres in Euclidean affine spaces

This section develops some results on spheres in Euclidean affine spaces.
-/


open InnerProductGeometry EuclideanGeometry

variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- If `P` is a point on the line `AB` and `Q` is equidistant from `A` and `B`, then
`AP * BP = abs (BQ ^ 2 - PQ ^ 2)`. -/
/-
**EuclideanGeometry.mul_dist_eq_abs_sub_sq_dist** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
形式化陈述：mul_dist_eq_abs_sub_sq_dist {a b p q : P} (hp : p in line[Real, a, b]) (hq
 : dist a q = dist b q) : dist a p * dist b p = |dist b q ^ 2 - dist p q ^ 2|
参数：hp : p in line[Real, a, b]；hq : dist a q = dist b q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_vsub_left`：midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ
 p₁ = (⅟2 : R) • (p₂ -ᵥ p₁)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `right_vsub_midpoint`：right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R 
p₁ p₂ = (⅟2 : R) • (p₂ -ᵥ p₁)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `InnerProductGeometry.mul_norm_eq_abs_sub_sq_norm`：mul_norm_eq_abs_sub_sq
_norm {x y z : V} (h₁ : exists k : Real, x = k • y) (h₃ : ‖z - y‖ = ‖z + y‖) : ‖
x - y‖ * ‖x + y‖ = |‖z + y‖ ^ 2 - ‖z -…
· 使用定理 `vadd_left_mem_affineSpan_pair`：vadd_left_mem_affineSpan_pair {p₁ p₂ : P}
 {v : V} : v +ᵥ p₁ in line[k, p₁, p₂] ↔ exists r : k, r • (p₂ -ᵥ p₁) = v
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
If `P` is a point on the line `AB` and `Q` is equidistant from `A` and `B`, then
`AP * BP = abs (BQ ^ 2 - PQ ^ 2)`.
-/
theorem mul_dist_eq_abs_sub_sq_dist {a b p q : P} (hp : p ∈ line[ℝ, a, b])
    (hq : dist a q = dist b q) : dist a p * dist b p = |dist b q ^ 2 - dist p q ^ 2| := by
  let m : P := midpoint ℝ a b
  have h1 := vsub_sub_vsub_cancel_left a p m
  have h1' := vsub_sub_vsub_cancel_left p a m
  have h2 := vsub_sub_vsub_cancel_left p q m
  have h3 := vsub_sub_vsub_cancel_left a q m
  have h : ∀ r, b -ᵥ r = m -ᵥ r + (m -ᵥ a) := fun r => by
    rw [midpoint_vsub_left, ← right_vsub_midpoint, add_comm, vsub_add_vsub_cancel]
  iterate 4 rw [dist_eq_norm_vsub V]
  rw [← h1, ← h2, h, h]
  rw [dist_eq_norm_vsub V a q, dist_eq_norm_vsub V b q, ← h3, h] at hq
  refine mul_norm_eq_abs_sub_sq_norm ?_ hq
  -- TODO: factor this out as a separate lemma?
  · rw [← vsub_vadd p a, vadd_left_mem_affineSpan_pair] at hp
    rcases hp with ⟨r, hr⟩
    rw [h, ← h1', eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at hr
    rw [hr]
    use 1 - r * 2
    match_scalars
    ring

/-- If `A`, `B`, `C`, `D` are cospherical and `P` is on both lines `AB` and `CD`, then
`AP * BP = CP * DP`. -/
/-
**EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry`。
形式化陈述：mul_dist_eq_mul_dist_of_cospherical {a b c d p : P} (h : Cospherical ({a, 
b, c, d} : Set P)) (hapb : p in line[Real, a, b]) (hcpd : p in line[Real, c, d])
 : dist a p * dist b p = dist c p * dist d p
参数：h : Cospherical ({a, b, c, d} : Set P)；hapb : p in line[Real, a, b]；hcpd : p 
in line[Real, c, d]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.cospherical_def`：cospherical_def (ps : Set P) : Cosphe
rical ps ↔ exists (center : P) (radius : Real), forall p in ps, dist p center = 
radius
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.mul_dist_eq_abs_sub_sq_dist`：mul_dist_eq_abs_sub_sq_di
st {a b p q : P} (hp : p in line[Real, a, b]) (hq : dist a q = dist b q) : dist 
a p * dist b p = |dist b q ^ 2 - di…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
If `A`, `B`, `C`, `D` are cospherical and `P` is on both lines `AB` and `CD`, th
en
`AP * BP = CP * DP`.
-/
theorem mul_dist_eq_mul_dist_of_cospherical {a b c d p : P} (h : Cospherical ({a, b, c, d} : Set P))
    (hapb : p ∈ line[ℝ, a, b]) (hcpd : p ∈ line[ℝ, c, d]) :
    dist a p * dist b p = dist c p * dist d p := by
  obtain ⟨q, r, h'⟩ := (cospherical_def {a, b, c, d}).mp h
  obtain ⟨ha, hb, hc, hd⟩ := h' a (by simp), h' b (by simp), h' c (by simp), h' d (by simp)
  rw [← hd] at hc
  rw [← hb] at ha
  rw [mul_dist_eq_abs_sub_sq_dist hapb ha, hb, mul_dist_eq_abs_sub_sq_dist hcpd hc, hd]

/-- **Intersecting Chords Theorem**. -/
/-
**EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi** 是 Mathl
ib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P} (h : Co
spherical ({a, b, c, d} : Set P)) (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) : di
st a p * dist b p = dist c p * dist d p
参数：h : Cospherical ({a, b, c, d} : Set P)；hapb : ∠ a p b = π；hcpd : ∠ c p d = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical`：mul_dist_eq_mul_d
ist_of_cospherical {a b c d p : P} (h : Cospherical ({a, b, c, d} : Set P)) (hap
b : p in line[Real, a, b]) (hcpd : p in lin…
· 使用定理 `Wbtw.mem_affineSpan`：Wbtw.mem_affineSpan {x y z : P} (h : Wbtw R x y z) 
: y in line[R, x, z]
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_eq_pi_iff_sbtw`：angle_eq_pi_iff_sbtw {p₁ p₂ p₃ :
 P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃

--- 原说明 ---
**Intersecting Chords Theorem**.
-/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p := by
  rw [EuclideanGeometry.angle_eq_pi_iff_sbtw] at hapb hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h hapb.wbtw.mem_affineSpan hcpd.wbtw.mem_affineSpan
/-
**EuclideanGeometry.cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi_aux** 是 M
athlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi_aux
    [Fact (finrank ℝ V = 2)] [Oriented ℝ V (Fin 2)] {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (hp₁p₂ : ∠ p₁ p p₂ = π) (hp₃p₄ : ∠ p₃ p p₄ = π) (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  suffices h_equiv : Cospherical ({p₁, p₂, p₄, p₃} : Set P) by grind [Set.pair_comm p₄ p₃]
  have h_angle_eq : ∠ p₁ p p₄ = ∠ p₃ p p₂ := by
    grind [angle_comm, angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hp₃p₄]
  rw [angle_eq_pi_iff_sbtw] at hp₁p₂ hp₃p₄
  have hcol_p₁pp₂ := hp₁p₂.wbtw.collinear
  have hcol_p₃pp₄ := hp₃p₄.wbtw.collinear
  have h_notcol_p₁p₂p₃ : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
    have : AffineIndependent ℝ ![p₁, p, p₃] := affineIndependent_iff_not_collinear_set.mpr hn
    rw [← affineIndependent_iff_not_collinear_set]
    grind [hp₁p₂.left_ne_right, affineIndependent_of_affineIndependent_collinear_ne,
      AffineIndependent.comm_left, AffineIndependent.comm_right]
  apply cospherical_of_two_zsmul_oangle_eq_of_not_collinear ?_ h_notcol_p₁p₂p₃
  suffices ∡ p₁ p₂ p₃ = ∡ p₁ p₄ p₃ by grind
  suffices ∠ p₁ p₂ p₃ = ∠ p₁ p₄ p₃ by
    grind [oangle_eq_of_angle_eq_of_sign_eq, Sbtw.oangle_sign_eq_of_sbtw]
  rw [angle_comm, ← angle_eq_angle_of_angle_eq_pi p₃ hp₁p₂.angle₃₂₁_eq_pi,
    ← angle_eq_angle_of_angle_eq_pi p₁ hp₃p₄.angle₃₂₁_eq_pi]
  suffices h_sim : Similar ![p₁, p, p₄] ![p₃, p, p₂] by
    grind [angle_comm, h_sim.angle_eq_all.right.left]
  have h_notcol_p₁pp₄ : ¬ Collinear ℝ ({p₁, p, p₄} : Set P) := by
    intro hcol
    suffices hcol : Collinear ℝ ({p₁, p, p₃} : Set P) by grind
    suffices hcol : Collinear ℝ ({p₁, p₃, p, p₄} : Set P) by grind [Collinear.subset _ hcol]
    have hne_pp₄ := hp₃p₄.ne_right
    grind [collinear_insert_insert_of_mem_affineSpan_pair, Collinear.mem_affineSpan_of_mem_of_ne]
  have h_notcol_p₃pp₂ : ¬ Collinear ℝ ({p₃, p, p₂} : Set P) := by
    intro hcol
    suffices hcol : Collinear ℝ ({p₁, p, p₃} : Set P) by grind
    suffices hcol : Collinear ℝ ({p₃, p₁, p, p₂} : Set P) by grind [Collinear.subset _ hcol]
    have hne_pp₂ := hp₁p₂.ne_right
    grind [collinear_insert_insert_of_mem_affineSpan_pair, Collinear.mem_affineSpan_of_mem_of_ne]
  apply similar_of_side_angle_side h_notcol_p₁pp₄ h_notcol_p₃pp₂ h_angle_eq ?_
  grind [dist_comm]

/-- If `p` lies strictly between `p₁` and `p₂` on one line and strictly between `p₃` and `p₄`
on another line, and if `dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p`,
then the points `p₁`, `p₂`, `p₃`, and `p₄` are cospherical. -/
/-
**EuclideanGeometry.cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi** 是 Mathl
ib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi {p₁ p₂ p₃ p₄ p : P} (h 
: dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p) (hp₁p₂ : ∠ p₁ p p₂ = π) (hp₃p₄ 
: ∠ p₃ p p₄ = π) (hn : ¬ Collinear Real ({p₁, p, p₃} : Set P)) : Cospherical ({p
₁, p₂, p₃, p₄} : Set P)
参数：h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p；hp₁p₂ : ∠ p₁ p p₂ = π；hp₃p₄
 : ∠ p₃ p p₄ = π；hn : ¬ Collinear Real ({p₁, p, p₃} : Set P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.angle_eq_pi_iff_sbtw`：angle_eq_pi_iff_sbtw {p₁ p₂ p₃ :
 P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `affineIndependent_iff_not_collinear_set`：affineIndependent_iff_not_colli
near_set {p₁ p₂ p₃ : P} : AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁,
 p₂, p₃} : Set P)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Collinear.mem_affineSpan_of_mem_of_ne`：Collinear.mem_affineSpan_of_mem_o
f_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in
 s) (hp₃ : p₃ in s) (hp₁p₂ …
· 使用定理 `Wbtw.collinear`：Wbtw.collinear {x y z : P} (h : Wbtw R x y z) : Collinea
r R ({x, y, z} : Set P)
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Sbtw.left_ne`：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` lies strictly between `p₁` and `p₂` on one line and strictly between `p₃`
 and `p₄`
on another line, and if `dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p`,
then the points `p₁`, `p₂`, `p₃`, and `p₄` are cospherical.
-/
theorem cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (hp₁p₂ : ∠ p₁ p p₂ = π) (hp₃p₄ : ∠ p₃ p p₄ = π) (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have hp₁p₂_sbtw : Sbtw ℝ p₁ p p₂ := angle_eq_pi_iff_sbtw.mp hp₁p₂
  have hp₃p₄_sbtw : Sbtw ℝ p₃ p p₄ := angle_eq_pi_iff_sbtw.mp hp₃p₄
  have hindep : AffineIndependent ℝ ![p₁, p, p₃] := affineIndependent_iff_not_collinear_set.mpr hn
  set t : Affine.Triangle ℝ P := ⟨_, hindep⟩ with ht
  set S : AffineSubspace ℝ P := affineSpan ℝ (Set.range t.points) with hS
  have hp₂ : p₂ ∈ S := by
    suffices hmem : p₂ ∈ affineSpan ℝ {p₁, p} by exact affineSpan_mono ℝ (by simp [ht]; grind) hmem
    simp [hp₁p₂_sbtw.wbtw.collinear.mem_affineSpan_of_mem_of_ne _ _ _ hp₁p₂_sbtw.left_ne]
  have hp₄ : p₄ ∈ S := by
    suffices hmem : p₄ ∈ affineSpan ℝ {p₃, p} by exact affineSpan_mono ℝ (by simp [ht]; grind) hmem
    simp [hp₃p₄_sbtw.wbtw.collinear.mem_affineSpan_of_mem_of_ne _ _ _ hp₃p₄_sbtw.left_ne]
  let s_isom : AffineIsometry ℝ S P := S.subtypeₐᵢ
  let p₁' : S := ⟨p₁, mem_affineSpan ℝ (s := Set.range t.points) (by aesop)⟩
  let p' : S := ⟨p, mem_affineSpan ℝ (s := Set.range t.points) (by aesop)⟩
  let p₃' : S := ⟨p₃, mem_affineSpan ℝ (s := Set.range t.points) (by aesop)⟩
  let p₂' : S := ⟨p₂, hp₂⟩
  let p₄' : S := ⟨p₄, hp₄⟩
  have h_dist' : dist p₁' p' * dist p₂' p' = dist p₃' p' * dist p₄' p' := by
    simpa [dist_eq_norm_vsub, ← s_isom.dist_map] using h
  have hp₁'p₂' : ∠ p₁' p' p₂' = π := by simpa [AffineIsometry.angle_map s_isom]
  have hp₃'p₄' : ∠ p₃' p' p₄' = π := by simpa [AffineIsometry.angle_map s_isom]
  suffices h_cospherical' : Cospherical {p₁', p₂', p₃', p₄'} by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was:
    `grind [Set.image_insert_eq, Set.image_singleton]` -/
    simpa [Set.image_insert_eq, Set.image_singleton] using Cospherical.subtype_val h_cospherical'
  have hf2 : Fact (finrank ℝ S.direction = 2) := ⟨by
    rw [hS, direction_affineSpan, t.independent.finrank_vectorSpan]
    simp⟩
  let : Module.Oriented ℝ S.direction (Fin 2) :=
    ⟨Basis.orientation (finBasisOfFinrankEq _ _ hf2.out)⟩
  have hncol : ¬ Collinear ℝ {p₁', p', p₃'} := by
    rw [← affineIndependent_iff_not_collinear_set,
      ← s_isom.toAffineMap.affineIndependent_iff s_isom.injective]
    convert! hindep
    ext i; fin_cases i <;> rfl
  exact cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi_aux h_dist' hp₁'p₂' hp₃'p₄' hncol

/-- **Intersecting Secants Theorem**. -/
/-
**EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero** 是 Mat
hlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P} (h : 
Cospherical ({a, b, c, d} : Set P)) (hab : a != b) (hcd : c != d) (hapb : ∠ a p 
b = 0) (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p
参数：h : Cospherical ({a, b, c, d} : Set P)；hab : a != b；hcd : c != d；hapb : ∠ a p
 b = 0；hcpd : ∠ c p d = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical`：mul_dist_eq_mul_d
ist_of_cospherical {a b c d p : P} (h : Cospherical ({a, b, c, d} : Set P)) (hap
b : p in line[Real, a, b]) (hcpd : p in lin…
· 使用定理 `Collinear.mem_affineSpan_of_mem_of_ne`：Collinear.mem_affineSpan_of_mem_o
f_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in
 s) (hp₃ : p₃ in s) (hp₁p₂ …
· 使用定理 `EuclideanGeometry.collinear_of_angle_eq_zero`：collinear_of_angle_eq_zero
 {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) : Collinear Real ({p₁, p₂, p₃} : Set P)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
**Intersecting Secants Theorem**.
-/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hab : a ≠ b) (hcd : c ≠ d) (hapb : ∠ a p b = 0)
    (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p := by
  apply collinear_of_angle_eq_zero at hapb
  apply collinear_of_angle_eq_zero at hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h
    (hapb.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab)
    (hcpd.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hcd)

namespace Sphere

/-- The power of a point with respect to a sphere. For a point and a sphere,
this is defined as the square of the distance from the point to the center
minus the square of the radius. This value is positive if the point is outside
the sphere, negative if inside, and zero if on the sphere. -/
/-
**EuclideanGeometry.Sphere.power** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeometry.Sp
here`。
形式化陈述：power (s : Sphere P) (p : P) : Real
参数：s : Sphere P；p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power of a point with respect to a sphere. For a point and a sphere,
this is defined as the square of the distance from the point to the center
minus the square of the radius. This value is positive if the point is outside
the sphere, negative if inside, and zero if on the sphere.
-/
def power (s : Sphere P) (p : P) : ℝ :=
  dist p s.center ^ 2 - s.radius ^ 2

/-- A point lies on the sphere if and only if its power with respect to
the sphere is zero. -/
/-
**EuclideanGeometry.Sphere.power_eq_zero_iff_mem_sphere** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry.Sphere`。
形式化陈述：power_eq_zero_iff_mem_sphere {s : Sphere P} {p : P} (hr : 0 <= s.radius) :
 s.power p = 0 ↔ p in s
参数：hr : 0 <= s.radius。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.power.eq_1`：∀ {P : Type u_2} [inst : MetricSpac
e P] (s : EuclideanGeometry.Sphere P) (p : P),   s.power p = dist p s.center ^ 2
 - s.radius ^ 2
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `pow_left_inj₀`：pow_left_inj₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b)
 (hn : n != 0) : a ^ n = b ^ n ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A point lies on the sphere if and only if its power with respect to
the sphere is zero.
-/
theorem power_eq_zero_iff_mem_sphere {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    s.power p = 0 ↔ p ∈ s := by
  rw [power, mem_sphere, sub_eq_zero, pow_left_inj₀ dist_nonneg hr two_ne_zero]

/-- The power of a point is positive if and only if the point lies outside the sphere. -/
/-
**EuclideanGeometry.Sphere.power_pos_iff_radius_lt_dist_center** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：power_pos_iff_radius_lt_dist_center {s : Sphere P} {p : P} (hr : 0 <= s.ra
dius) : 0 < s.power p ↔ s.radius < dist p s.center
参数：hr : 0 <= s.radius。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.power.eq_1`：∀ {P : Type u_2} [inst : MetricSpac
e P] (s : EuclideanGeometry.Sphere P) (p : P),   s.power p = dist p s.center ^ 2
 - s.radius ^ 2
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `pow_lt_pow_iff_left₀`：pow_lt_pow_iff_left₀ [MulPosMono M₀] (ha : 0 <= a)
 (hb : 0 <= b) (hn : n != 0) : a ^ n < b ^ n ↔ a < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The power of a point is positive if and only if the point lies outside the spher
e.
-/
theorem power_pos_iff_radius_lt_dist_center {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    0 < s.power p ↔ s.radius < dist p s.center := by
  rw [power, sub_pos, pow_lt_pow_iff_left₀ hr dist_nonneg two_ne_zero]

/-- The power of a point is negative if and only if the point lies inside the sphere. -/
/-
**EuclideanGeometry.Sphere.power_neg_iff_dist_center_lt_radius** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：power_neg_iff_dist_center_lt_radius {s : Sphere P} {p : P} (hr : 0 <= s.ra
dius) : s.power p < 0 ↔ dist p s.center < s.radius
参数：hr : 0 <= s.radius。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.power.eq_1`：∀ {P : Type u_2} [inst : MetricSpac
e P] (s : EuclideanGeometry.Sphere P) (p : P),   s.power p = dist p s.center ^ 2
 - s.radius ^ 2
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `pow_lt_pow_iff_left₀`：pow_lt_pow_iff_left₀ [MulPosMono M₀] (ha : 0 <= a)
 (hb : 0 <= b) (hn : n != 0) : a ^ n < b ^ n ↔ a < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The power of a point is negative if and only if the point lies inside the sphere
.
-/
theorem power_neg_iff_dist_center_lt_radius {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
  s.power p < 0 ↔ dist p s.center < s.radius := by
  rw [power, sub_neg, pow_lt_pow_iff_left₀ dist_nonneg hr two_ne_zero]

/-- The power of a point is nonnegative if and only if the point lies outside or on the sphere. -/
/-
**EuclideanGeometry.Sphere.power_nonneg_iff_radius_le_dist_center** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：power_nonneg_iff_radius_le_dist_center {s : Sphere P} {p : P} (hr : 0 <= s
.radius) : 0 <= s.power p ↔ s.radius <= dist p s.center
参数：hr : 0 <= s.radius。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.power.eq_1`：∀ {P : Type u_2} [inst : MetricSpac
e P] (s : EuclideanGeometry.Sphere P) (p : P),   s.power p = dist p s.center ^ 2
 - s.radius ^ 2
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `pow_le_pow_iff_left₀`：pow_le_pow_iff_left₀ [MulPosMono M₀] (ha : 0 <= a)
 (hb : 0 <= b) (hn : n != 0) : a ^ n <= b ^ n ↔ a <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The power of a point is nonnegative if and only if the point lies outside or on 
the sphere.
-/
theorem power_nonneg_iff_radius_le_dist_center {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    0 ≤ s.power p ↔ s.radius ≤ dist p s.center := by
  rw [power, sub_nonneg, pow_le_pow_iff_left₀ hr dist_nonneg two_ne_zero]

/-- The power of a point is nonpositive if and only if the point lies inside or on the sphere. -/
/-
**EuclideanGeometry.Sphere.power_nonpos_iff_dist_center_le_radius** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：power_nonpos_iff_dist_center_le_radius {s : Sphere P} {p : P} (hr : 0 <= s
.radius) : s.power p <= 0 ↔ dist p s.center <= s.radius
参数：hr : 0 <= s.radius。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.power.eq_1`：∀ {P : Type u_2} [inst : MetricSpac
e P] (s : EuclideanGeometry.Sphere P) (p : P),   s.power p = dist p s.center ^ 2
 - s.radius ^ 2
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `pow_le_pow_iff_left₀`：pow_le_pow_iff_left₀ [MulPosMono M₀] (ha : 0 <= a)
 (hb : 0 <= b) (hn : n != 0) : a ^ n <= b ^ n ↔ a <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The power of a point is nonpositive if and only if the point lies inside or on t
he sphere.
-/
theorem power_nonpos_iff_dist_center_le_radius {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    s.power p ≤ 0 ↔ dist p s.center ≤ s.radius := by
  rw [power, sub_nonpos, pow_le_pow_iff_left₀ dist_nonneg hr two_ne_zero]

/-- For any point, the product of distances to two intersection
points on a line through the point equals the absolute value of the power of the point. -/
/-
**EuclideanGeometry.Sphere.mul_dist_eq_abs_power** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry.Sphere`。
形式化陈述：mul_dist_eq_abs_power {s : Sphere P} {p a b : P} (hp : p in line[Real, a, 
b]) (ha : a in s) (hb : b in s) : dist p a * dist p b = |s.power p|
参数：hp : p in line[Real, a, b]；ha : a in s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `EuclideanGeometry.mul_dist_eq_abs_sub_sq_dist`：mul_dist_eq_abs_sub_sq_di
st {a b p q : P} (hp : p in line[Real, a, b]) (hq : dist a q = dist b q) : dist 
a p * dist b p = |dist b q ^ 2 - di…
· 使用定理 `EuclideanGeometry.Sphere.power.eq_1`：∀ {P : Type u_2} [inst : MetricSpac
e P] (s : EuclideanGeometry.Sphere P) (p : P),   s.power p = dist p s.center ^ 2
 - s.radius ^ 2
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|

--- 原说明 ---
For any point, the product of distances to two intersection
points on a line through the point equals the absolute value of the power of the
 point.
-/
theorem mul_dist_eq_abs_power {s : Sphere P} {p a b : P}
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s) :
    dist p a * dist p b = |s.power p| := by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha, mem_sphere.mp hb]
  rw [dist_comm p a, dist_comm p b, mul_dist_eq_abs_sub_sq_dist hp hq,
    mem_sphere.mp hb, power, abs_sub_comm]

/-- For a point on the sphere, the product of distances to two other intersection
points on a line through the point is zero. -/
/-
**EuclideanGeometry.Sphere.mul_dist_eq_zero_of_mem_sphere** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry.Sphere`。
形式化陈述：mul_dist_eq_zero_of_mem_sphere {s : Sphere P} {p a b : P} (hp : p in line[
Real, a, b]) (ha : a in s) (hb : b in s) (hp_on : p in s) : dist p a * dist p b 
= 0
参数：hp : p in line[Real, a, b]；ha : a in s；hb : b in s；hp_on : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `EuclideanGeometry.mul_dist_eq_abs_sub_sq_dist`：mul_dist_eq_abs_sub_sq_di
st {a b p q : P} (hp : p in line[Real, a, b]) (hq : dist a q = dist b q) : dist 
a p * dist b p = |dist b q ^ 2 - di…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
For a point on the sphere, the product of distances to two other intersection
points on a line through the point is zero.
-/
theorem mul_dist_eq_zero_of_mem_sphere {s : Sphere P} {p a b : P}
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s)
    (hp_on : p ∈ s) :
    dist p a * dist p b = 0 := by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha, mem_sphere.mp hb]
  rw [dist_comm p a, dist_comm p b, mul_dist_eq_abs_sub_sq_dist hp hq,
      mem_sphere.mp hb, mem_sphere.mp hp_on, sub_self, abs_zero]

/-- For a point outside or on the sphere, the product of distances to two intersection
points on a line through the point equals the power of the point. -/
/-
**EuclideanGeometry.Sphere.mul_dist_eq_power_of_radius_le_dist_center** 是 Mathli
b 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：mul_dist_eq_power_of_radius_le_dist_center {s : Sphere P} {p a b : P} (hr 
: 0 <= s.radius) (hp : p in line[Real, a, b]) (ha : a in s) (hb : b in s) (hle :
 s.radius <= dist p s.center) : dist p a * dist p b = s.power p
参数：hr : 0 <= s.radius；hp : p in line[Real, a, b]；ha : a in s；hb : b in s；hle : s
.radius <= dist p s.center。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.mul_dist_eq_abs_power`：mul_dist_eq_abs_power {s
 : Sphere P} {p a b : P} (hp : p in line[Real, a, b]) (ha : a in s) (hb : b in s
) : dist p a * dist p b = |s.power p…
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.Sphere.power_nonneg_iff_radius_le_dist_center`：power_n
onneg_iff_radius_le_dist_center {s : Sphere P} {p : P} (hr : 0 <= s.radius) : 0 
<= s.power p ↔ s.radius <= dist p s.center

--- 原说明 ---
For a point outside or on the sphere, the product of distances to two intersecti
on
points on a line through the point equals the power of the point.
-/
theorem mul_dist_eq_power_of_radius_le_dist_center {s : Sphere P} {p a b : P}
    (hr : 0 ≤ s.radius)
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s)
    (hle : s.radius ≤ dist p s.center) :
    dist p a * dist p b = s.power p := by
  rw [mul_dist_eq_abs_power hp ha hb,
    abs_of_nonneg <| (power_nonneg_iff_radius_le_dist_center hr).mpr hle]

/-- For a point inside or on the sphere, the product of distances to two intersection
points on a line through the point equals the negative of the power of the point. -/
/-
**EuclideanGeometry.Sphere.mul_dist_eq_neg_power_of_dist_center_le_radius** 是 Ma
thlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：mul_dist_eq_neg_power_of_dist_center_le_radius {s : Sphere P} {p a b : P} 
(hr : 0 <= s.radius) (hp : p in line[Real, a, b]) (ha : a in s) (hb : b in s) (h
le : dist p s.center <= s.radius) : dist p a * dist p b = -s.power p
参数：hr : 0 <= s.radius；hp : p in line[Real, a, b]；ha : a in s；hb : b in s；hle : d
ist p s.center <= s.radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.mul_dist_eq_abs_power`：mul_dist_eq_abs_power {s
 : Sphere P} {p a b : P} (hp : p in line[Real, a, b]) (ha : a in s) (hb : b in s
) : dist p a * dist p b = |s.power p…
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.Sphere.power_nonpos_iff_dist_center_le_radius`：power_n
onpos_iff_dist_center_le_radius {s : Sphere P} {p : P} (hr : 0 <= s.radius) : s.
power p <= 0 ↔ dist p s.center <= s.radius

--- 原说明 ---
For a point inside or on the sphere, the product of distances to two intersectio
n
points on a line through the point equals the negative of the power of the point
.
-/
theorem mul_dist_eq_neg_power_of_dist_center_le_radius {s : Sphere P} {p a b : P}
    (hr : 0 ≤ s.radius)
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s)
    (hle : dist p s.center ≤ s.radius) :
    dist p a * dist p b = -s.power p := by
  rw [mul_dist_eq_abs_power hp ha hb,
    abs_of_nonpos <| (power_nonpos_iff_dist_center_le_radius hr).mpr hle]

/-- **Tangent-Secant Theorem**. The square of the tangent length equals
    the product of secant segment lengths. -/
/-
**EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：dist_sq_eq_mul_dist_of_tangent_and_secant {a b t p : P} {s : Sphere P} (ha
 : a in s) (hb : b in s) (hp : p in line[Real, a, b]) (h_tangent : s.IsTangentAt
 t (line[Real, p, t])) : dist p t ^ 2 = dist p a * dist p b
参数：ha : a in s；hb : b in s；hp : p in line[Real, a, b]；h_tangent : s.IsTangentAt 
t (line[Real, p, t])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.radius_nonneg_of_mem`：∀ {P : Type u_2} [inst : 
MetricSpace P] {s : EuclideanGeometry.Sphere P} {p : P}, p ∈ s → 0 ≤ s.radius
· 使用定理 `EuclideanGeometry.Sphere.IsTangent.radius_le_dist_center`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.isTangent`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.mul_dist_eq_power_of_radius_le_dist_center`：mul
_dist_eq_power_of_radius_le_dist_center {s : Sphere P} {p a b : P} (hr : 0 <= s.
radius) (hp : p in line[Real, a, b]) (ha : a in s) (hb : …
· 使用定理 `EuclideanGeometry.Sphere.power.eq_1`：∀ {P : Type u_2} [inst : MetricSpac
e P] (s : EuclideanGeometry.Sphere P) (p : P),   s.power p = dist p s.center ^ 2
 - s.radius ^ 2
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
**Tangent-Secant Theorem**. The square of the tangent length equals
    the product of secant segment lengths.
-/
theorem dist_sq_eq_mul_dist_of_tangent_and_secant {a b t p : P} {s : Sphere P}
    (ha : a ∈ s) (hb : b ∈ s)
    (hp : p ∈ line[ℝ, a, b])
    (h_tangent : s.IsTangentAt t (line[ℝ, p, t])) :
    dist p t ^ 2 = dist p a * dist p b := by
  have hr := radius_nonneg_of_mem ha
  have radius_le_dist := h_tangent.isTangent.radius_le_dist_center (left_mem_affineSpan_pair ℝ p t)
  rw [mul_dist_eq_power_of_radius_le_dist_center hr hp ha hb radius_le_dist,
    Sphere.power, h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ p t)]
  ring

/-- The power of a point with respect to a sphere equals the square of its tangent length. -/
/-
**EuclideanGeometry.Sphere.IsTangentAt.power_eq_dist_sq** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace
 ℝ V] {P : Type u_2} [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {t p : P},   s.IsTangentAt t line[ℝ, p, t] → s.p
ower p = dist p t ^ 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.power.eq_1`：∀ {P : Type u_2} [inst : MetricSpac
e P] (s : EuclideanGeometry.Sphere P) (p : P),   s.power p = dist p s.center ^ 2
 - s.radius ^ 2
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
The power of a point with respect to a sphere equals the square of its tangent l
ength.
-/
theorem IsTangentAt.power_eq_dist_sq {s : Sphere P} {t p : P}
    (h_tangent : s.IsTangentAt t (line[ℝ, p, t])) :
    s.power p = dist p t ^ 2 := by
  rw [Sphere.power, h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ p t)]
  ring_nf

/-- A line through a point on a sphere is tangent if and only if the squared distance
from the external point to the tangent point equals the power of the point. -/
/-
**EuclideanGeometry.Sphere.isTangentAt_iff_dist_sq_eq_power** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：isTangentAt_iff_dist_sq_eq_power {t p : P} {s : Sphere P} (ht : t in s) : 
s.IsTangentAt t (line[Real, p, t]) ↔ dist p t ^ 2 = s.power p
参数：ht : t in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.power_eq_dist_sq`：∀ {V : Type u_1} 
[inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] {P : Type u_2} [i
nst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`：norm_add_sq_e
q_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
A line through a point on a sphere is tangent if and only if the squared distanc
e
from the external point to the tangent point equals the power of the point.
-/
theorem isTangentAt_iff_dist_sq_eq_power {t p : P} {s : Sphere P} (ht : t ∈ s) :
    s.IsTangentAt t (line[ℝ, p, t]) ↔ dist p t ^ 2 = s.power p :=
  ⟨fun h ↦ h.power_eq_dist_sq.symm, fun h_dist_eq ↦ by
    have h_orth : ⟪p -ᵥ t, t -ᵥ s.center⟫ = 0 := by
      simp only [Sphere.power, ← mem_sphere.mp ht, dist_eq_norm_vsub V, sq,
                 ← vsub_add_vsub_cancel p t s.center] at h_dist_eq
      exact (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero _ _).mp (by linarith)
    refine ⟨ht, right_mem_affineSpan_pair ℝ p t, fun x hx ↦ ?_⟩
    rw [mem_orthRadius_iff_inner_left]
    obtain ⟨r, hr⟩ := (vadd_right_mem_affineSpan_pair (k := ℝ)).mp (vsub_vadd x t ▸ hx)
    rw [← hr, inner_smul_left, h_orth, mul_zero]⟩

alias ⟨_, isTangentAt_of_dist_sq_eq_power⟩ := isTangentAt_iff_dist_sq_eq_power

end Sphere

end EuclideanGeometry

