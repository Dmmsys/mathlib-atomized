/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Ray
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Strictly convex spaces

This file defines strictly convex spaces. A normed space is strictly convex if all closed balls are
strictly convex. This does **not** mean that the norm is strictly convex (in fact, it never is).

## Main definitions

`StrictConvexSpace`: a typeclass saying that a given normed space over a normed linear ordered
field (e.g., `ℝ` or `ℚ`) is strictly convex. The definition requires strict convexity of a closed
ball of positive radius with center at the origin; strict convexity of any other closed ball follows
from this assumption.

## Main results

In a strictly convex space, we prove

- `strictConvex_closedBall`: a closed ball is strictly convex.
- `combo_mem_ball_of_ne`, `openSegment_subset_ball_of_ne`, `norm_combo_lt_of_ne`:
  a nontrivial convex combination of two points in a closed ball belong to the corresponding open
  ball;
- `norm_add_lt_of_not_sameRay`, `sameRay_iff_norm_add`, `dist_add_dist_eq_iff`:
  the triangle inequality `dist x y + dist y z ≤ dist x z` is a strict inequality unless `y` belongs
  to the segment `[x -[ℝ] z]`.
- `Isometry.affineIsometryOfStrictConvexSpace`: an isometry of `NormedAddTorsor`s for real
  normed spaces, strictly convex in the case of the codomain, is an affine isometry.

We also provide several lemmas that can be used as alternative constructors for `StrictConvex ℝ E`:

- `StrictConvexSpace.of_strictConvex_unitClosedBall`: if `closed_ball (0 : E) 1` is strictly
  convex, then `E` is a strictly convex space;

- `StrictConvexSpace.of_norm_add`: if `‖x + y‖ = ‖x‖ + ‖y‖` implies `SameRay ℝ x y` for all
  nonzero `x y : E`, then `E` is a strictly convex space.

## Implementation notes

While the definition is formulated for any normed linear ordered field, most of the lemmas are
formulated only for the case `𝕜 = ℝ`.

## Tags

convex, strictly convex
-/

public section

open Convex Pointwise Set Metric

/-- A *strictly convex space* is a normed space where the closed balls are strictly convex. We only
require balls of positive radius with center at the origin to be strictly convex in the definition,
then prove that any closed ball is strictly convex in `strictConvex_closedBall` below.

See also `StrictConvexSpace.of_strictConvex_unitClosedBall`. -/
@[mk_iff]
/-
**StrictConvexSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_1) →   (E : Type u_2) →     [inst : NormedField 𝕜] → [PartialO
rder 𝕜] → [inst_2 : NormedAddCommGroup E] → [NormedSpace 𝕜 E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *strictly convex space* is a normed space where the closed balls are strictly 
convex. We only
require balls of positive radius with center at the origin to be strictly convex
 in the definition,
then prove that any closed ball is strictly convex in `strictConvex_closedBall` 
below.

See also `StrictConvexSpace.of_strictConvex_unitClosedBall`.
-/
class StrictConvexSpace (𝕜 E : Type*) [NormedField 𝕜] [PartialOrder 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop where
  strictConvex_closedBall : ∀ r : ℝ, 0 < r → StrictConvex 𝕜 (closedBall (0 : E) r)

variable (𝕜 : Type*) {E : Type*} [NormedField 𝕜] [PartialOrder 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A closed ball in a strictly convex space is strictly convex. -/
/-
**strictConvex_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_closedBall [StrictConvexSpace 𝕜 E] (x : E) (r : Real) : Stric
tConvex 𝕜 (closedBall x r)
参数：x : E；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Set.Subsingleton.strictConvex`：Set.Subsingleton.strictConvex (hs : s.Sub
singleton) : StrictConvex 𝕜 s
· 使用定理 `Metric.subsingleton_closedBall`：subsingleton_closedBall (x : γ) {r : Rea
l} (hr : r <= 0) : (closedBall x r).Subsingleton
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_closedBall_zero`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E]
 (δ : ℝ) (x : E), x +ᵥ Metric.closedBall 0 δ = Metric.closedBall x δ
· 使用定理 `StrictConvex.vadd`：StrictConvex.vadd (hs : StrictConvex 𝕜 s) (x : E) : S
trictConvex 𝕜 (x +ᵥ s)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `StrictConvexSpace.strictConvex_closedBall`：∀ {𝕜 : Type u_1} {E : Type u_
2} {inst : NormedField 𝕜} {inst_1 : PartialOrder 𝕜} {inst_2 : NormedAddCommGroup
 E}   {inst_3 : NormedSpace 𝕜 E…

--- 原说明 ---
A closed ball in a strictly convex space is strictly convex.
-/
theorem strictConvex_closedBall [StrictConvexSpace 𝕜 E] (x : E) (r : ℝ) :
    StrictConvex 𝕜 (closedBall x r) := by
  rcases le_or_gt r 0 with hr | hr
  · exact (subsingleton_closedBall x hr).strictConvex
  rw [← vadd_closedBall_zero]
  exact (StrictConvexSpace.strictConvex_closedBall r hr).vadd _

variable [NormedSpace ℝ E]

/-- A real normed vector space is strictly convex provided that the unit ball is strictly convex. -/
/-
**StrictConvexSpace.of_strictConvex_unitClosedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexSpace.of_strictConvex_unitClosedBall [LinearMap.CompatibleSMul
 E E 𝕜 Real] (h : StrictConvex 𝕜 (closedBall (0 : E) 1)) : StrictConvexSpace 𝕜 E
参数：h : StrictConvex 𝕜 (closedBall (0 : E) 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_unitClosedBall_of_nonneg`：smul_unitClosedBall_of_nonneg {r : Real} 
(hr : 0 <= r) : r • closedBall (0 : E) 1 = closedBall (0 : E) r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `StrictConvex.smul`：StrictConvex.smul (hs : StrictConvex 𝕜 s) (c : 𝕝) : S
trictConvex 𝕜 (c • s)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
A real normed vector space is strictly convex provided that the unit ball is str
ictly convex.
-/
theorem StrictConvexSpace.of_strictConvex_unitClosedBall [LinearMap.CompatibleSMul E E 𝕜 ℝ]
    (h : StrictConvex 𝕜 (closedBall (0 : E) 1)) : StrictConvexSpace 𝕜 E :=
  ⟨fun r hr => by simpa only [smul_unitClosedBall_of_nonneg hr.le] using h.smul r⟩

/-- Strict convexity is equivalent to `‖a • x + b • y‖ < 1` for all `x` and `y` of norm at most `1`
and all strictly positive `a` and `b` such that `a + b = 1`. This lemma shows that it suffices to
check this for points of norm one and some `a`, `b` such that `a + b = 1`. -/
/-
**StrictConvexSpace.of_norm_combo_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexSpace.of_norm_combo_lt_one (h : forall x y : E, ‖x‖ = 1 -> ‖y‖
 = 1 -> x != y -> exists a b : Real, a + b = 1 ∧ ‖a • x + b • y‖ < 1) : StrictCo
nvexSpace Real E
参数：h : forall x y : E, ‖x‖ = 1 -> ‖y‖ = 1 -> x != y -> exists a b : Real, a + b 
= 1 ∧ ‖a • x + b • y‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexSpace.of_strictConvex_unitClosedBall`：StrictConvexSpace.of_s
trictConvex_unitClosedBall [LinearMap.CompatibleSMul E E 𝕜 Real] (h : StrictConv
ex 𝕜 (closedBall (0 : E) 1)) : StrictC…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Convex.strictConvex'`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [
inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : AddCommGroup E] [ins
t_4 : _roo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_sphere_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E]
 {a : E} {r : ℝ}, a ∈ Metric.sphere 0 r ↔ ‖a‖ = r
· 使用定理 `Metric.closedBall_sdiff_ball`：closedBall_sdiff_ball : closedBall x ε \ b
all x ε = sphere x ε
· 使用定理 `interior_closedBall`：interior_closedBall (x : E) {r : Real} (hr : r != 0
) : interior (closedBall x r) = ball x r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `AffineMap.lineMap_apply_module`：lineMap_apply_module (p₀ p₁ : V1) (c : k
) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Strict convexity is equivalent to `‖a • x + b • y‖ < 1` for all `x` and `y` of n
orm at most `1`
and all strictly positive `a` and `b` such that `a + b = 1`. This lemma shows th
at it suffices to
check this for points of norm one and some `a`, `b` such that `a + b = 1`.
-/
theorem StrictConvexSpace.of_norm_combo_lt_one
    (h : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ∃ a b : ℝ, a + b = 1 ∧ ‖a • x + b • y‖ < 1) :
    StrictConvexSpace ℝ E := by
  refine
    StrictConvexSpace.of_strictConvex_unitClosedBall ℝ
      ((convex_closedBall _ _).strictConvex' fun x hx y hy hne => ?_)
  rw [interior_closedBall (0 : E) one_ne_zero, closedBall_sdiff_ball,
    mem_sphere_zero_iff_norm] at hx hy
  rcases h x y hx hy hne with ⟨a, b, hab, hlt⟩
  use b
  rwa [AffineMap.lineMap_apply_module, interior_closedBall (0 : E) one_ne_zero, mem_ball_zero_iff,
    sub_eq_iff_eq_add.2 hab.symm]
/-
**StrictConvexSpace.of_norm_combo_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexSpace.of_norm_combo_ne_one (h : forall x y : E, ‖x‖ = 1 -> ‖y‖
 = 1 -> x != y -> exists a b : Real, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ ‖a • x + b • 
y‖ != 1) : StrictConvexSpace Real E
参数：h : forall x y : E, ‖x‖ = 1 -> ‖y‖ = 1 -> x != y -> exists a b : Real, 0 <= a
 ∧ 0 <= b ∧ a + b = 1 ∧ ‖a • x + b • y‖ != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexSpace.of_strictConvex_unitClosedBall`：StrictConvexSpace.of_s
trictConvex_unitClosedBall [LinearMap.CompatibleSMul E E 𝕜 Real] (h : StrictConv
ex 𝕜 (closedBall (0 : E) 1)) : StrictC…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Convex.strictConvex`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [i
nst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : AddCommGroup E] [inst
_4 : _roo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_closedBall`：interior_closedBall (x : E) {r : Real} (hr : r != 0
) : interior (closedBall x r) = ball x r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Metric.closedBall_sdiff_ball`：closedBall_sdiff_ball : closedBall x ε \ b
all x ε = sphere x ε
· 使用定理 `frontier_closedBall`：frontier_closedBall (x : E) {r : Real} (hr : r != 0
) : frontier (closedBall x r) = sphere x r
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_sphere_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E]
 {a : E} {r : ℝ}, a ∈ Metric.sphere 0 r ↔ ‖a‖ = r
-/
theorem StrictConvexSpace.of_norm_combo_ne_one
    (h :
      ∀ x y : E,
        ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ ‖a • x + b • y‖ ≠ 1) :
    StrictConvexSpace ℝ E := by
  refine StrictConvexSpace.of_strictConvex_unitClosedBall ℝ
    ((convex_closedBall _ _).strictConvex ?_)
  simp only [interior_closedBall _ one_ne_zero, closedBall_sdiff_ball, Set.Pairwise,
    frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
  intro x hx y hy hne
  rcases h x y hx hy hne with ⟨a, b, ha, hb, hab, hne'⟩
  exact ⟨_, ⟨a, b, ha, hb, hab, rfl⟩, mt mem_sphere_zero_iff_norm.1 hne'⟩
/-
**StrictConvexSpace.of_norm_add_ne_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexSpace.of_norm_add_ne_two (h : forall ⦃x y : E⦄, ‖x‖ = 1 -> ‖y‖
 = 1 -> x != y -> ‖x + y‖ != 2) : StrictConvexSpace Real E
参数：h : forall ⦃x y : E⦄, ‖x‖ = 1 -> ‖y‖ = 1 -> x != y -> ‖x + y‖ != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `StrictConvexSpace.of_norm_combo_ne_one`：StrictConvexSpace.of_norm_combo_
ne_one (h : forall x y : E, ‖x‖ = 1 -> ‖y‖ = 1 -> x != y -> exists a b : Real, 0
 <= a ∧ 0 <= b ∧ a + b = 1 ∧…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `div_eq_one_iff_eq`：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
-/
theorem StrictConvexSpace.of_norm_add_ne_two
    (h : ∀ ⦃x y : E⦄, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ‖x + y‖ ≠ 2) : StrictConvexSpace ℝ E := by
  refine
    StrictConvexSpace.of_norm_combo_ne_one fun x y hx hy hne =>
      ⟨1 / 2, 1 / 2, one_half_pos.le, one_half_pos.le, add_halves _, ?_⟩
  rw [← smul_add, norm_smul, Real.norm_of_nonneg one_half_pos.le, one_div, ← div_eq_inv_mul, Ne,
    div_eq_one_iff_eq (two_ne_zero' ℝ)]
  exact h hx hy hne
/-
**StrictConvexSpace.of_pairwise_sphere_norm_ne_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexSpace.of_pairwise_sphere_norm_ne_two (h : (sphere (0 : E) 1).P
airwise fun x y => ‖x + y‖ != 2) : StrictConvexSpace Real E
参数：h : (sphere (0 : E) 1).Pairwise fun x y => ‖x + y‖ != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `StrictConvexSpace.of_norm_add_ne_two`：StrictConvexSpace.of_norm_add_ne_t
wo (h : forall ⦃x y : E⦄, ‖x‖ = 1 -> ‖y‖ = 1 -> x != y -> ‖x + y‖ != 2) : Strict
ConvexSpace Real E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_sphere_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E]
 {a : E} {r : ℝ}, a ∈ Metric.sphere 0 r ↔ ‖a‖ = r
-/
theorem StrictConvexSpace.of_pairwise_sphere_norm_ne_two
    (h : (sphere (0 : E) 1).Pairwise fun x y => ‖x + y‖ ≠ 2) : StrictConvexSpace ℝ E :=
  StrictConvexSpace.of_norm_add_ne_two fun _ _ hx hy =>
    h (mem_sphere_zero_iff_norm.2 hx) (mem_sphere_zero_iff_norm.2 hy)

/-- If `‖x + y‖ = ‖x‖ + ‖y‖` implies that `x y : E` are in the same ray, then `E` is a strictly
convex space. See also a more -/
/-
**StrictConvexSpace.of_norm_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexSpace.of_norm_add (h : forall x y : E, ‖x‖ = 1 -> ‖y‖ = 1 -> ‖
x + y‖ = 2 -> SameRay Real x y) : StrictConvexSpace Real E
参数：h : forall x y : E, ‖x‖ = 1 -> ‖y‖ = 1 -> ‖x + y‖ = 2 -> SameRay Real x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `StrictConvexSpace.of_pairwise_sphere_norm_ne_two`：StrictConvexSpace.of_p
airwise_sphere_norm_ne_two (h : (sphere (0 : E) 1).Pairwise fun x y => ‖x + y‖ !
= 2) : StrictConvexSpace Real E
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sameRay_iff_of_norm_eq`：sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : SameRay
 Real x y ↔ x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_sphere_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E]
 {a : E} {r : ℝ}, a ∈ Metric.sphere 0 r ↔ ‖a‖ = r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `‖x + y‖ = ‖x‖ + ‖y‖` implies that `x y : E` are in the same ray, then `E` is
 a strictly
convex space. See also a more
-/
theorem StrictConvexSpace.of_norm_add
    (h : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ‖x + y‖ = 2 → SameRay ℝ x y) : StrictConvexSpace ℝ E := by
  refine StrictConvexSpace.of_pairwise_sphere_norm_ne_two fun x hx y hy => mt fun h₂ => ?_
  rw [mem_sphere_zero_iff_norm] at hx hy
  exact (sameRay_iff_of_norm_eq (hx.trans hy.symm)).1 (h x y hx hy h₂)

variable [StrictConvexSpace ℝ E] {x y z : E} {a b r : ℝ}

/-- If `x ≠ y` belong to the same closed ball, then a convex combination of `x` and `y` with
positive coefficients belongs to the corresponding open ball. -/
/-
**combo_mem_ball_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：combo_mem_ball_of_ne (hx : x in closedBall z r) (hy : y in closedBall z r)
 (hne : x != y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a • x + b • y in b
all z r
参数：hx : x in closedBall z r；hy : y in closedBall z r；hne : x != y；ha : 0 < a；hb 
: 0 < b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_closedBall`：interior_closedBall (x : E) {r : Real} (hr : r != 0
) : interior (closedBall x r) = ball x r
· 使用定理 `strictConvex_closedBall`：strictConvex_closedBall [StrictConvexSpace 𝕜 E]
 (x : E) (r : Real) : StrictConvex 𝕜 (closedBall x r)

--- 原说明 ---
If `x ≠ y` belong to the same closed ball, then a convex combination of `x` and 
`y` with
positive coefficients belongs to the corresponding open ball.
-/
theorem combo_mem_ball_of_ne (hx : x ∈ closedBall z r) (hy : y ∈ closedBall z r) (hne : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a • x + b • y ∈ ball z r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, mem_singleton_iff] at hx hy
    exact (hne (hx.trans hy.symm)).elim
  · simp only [← interior_closedBall _ hr] at hx hy ⊢
    exact strictConvex_closedBall ℝ z r hx hy hne ha hb hab

/-- If `x ≠ y` belong to the same closed ball, then the open segment with endpoints `x` and `y` is
included in the corresponding open ball. -/
/-
**openSegment_subset_ball_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：openSegment_subset_ball_of_ne (hx : x in closedBall z r) (hy : y in closed
Ball z r) (hne : x != y) : openSegment Real x y subseteq ball z r
参数：hx : x in closedBall z r；hy : y in closedBall z r；hne : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `openSegment_subset_iff`：openSegment_subset_iff : openSegment 𝕜 x y subse
teq s ↔ forall a b : 𝕜, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s
· 使用定理 `combo_mem_ball_of_ne`：combo_mem_ball_of_ne (hx : x in closedBall z r) (h
y : y in closedBall z r) (hne : x != y) (ha : 0 < a) (hb : 0 < b) (hab : a + b =
 1) : a • …

--- 原说明 ---
If `x ≠ y` belong to the same closed ball, then the open segment with endpoints 
`x` and `y` is
included in the corresponding open ball.
-/
theorem openSegment_subset_ball_of_ne (hx : x ∈ closedBall z r) (hy : y ∈ closedBall z r)
    (hne : x ≠ y) : openSegment ℝ x y ⊆ ball z r :=
  (openSegment_subset_iff _).2 fun _ _ => combo_mem_ball_of_ne hx hy hne

/-- If `x` and `y` are two distinct vectors of norm at most `r`, then a convex combination of `x`
and `y` with positive coefficients has norm strictly less than `r`. -/
/-
**norm_combo_lt_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_combo_lt_of_ne (hx : ‖x‖ <= r) (hy : ‖y‖ <= r) (hne : x != y) (ha : 0
 < a) (hb : 0 < b) (hab : a + b = 1) : ‖a • x + b • y‖ < r
参数：hx : ‖x‖ <= r；hy : ‖y‖ <= r；hne : x != y；ha : 0 < a；hb : 0 < b；hab : a + b = 
1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `combo_mem_ball_of_ne`：combo_mem_ball_of_ne (hx : x in closedBall z r) (h
y : y in closedBall z r) (hne : x != y) (ha : 0 < a) (hb : 0 < b) (hab : a + b =
 1) : a • …

--- 原说明 ---
If `x` and `y` are two distinct vectors of norm at most `r`, then a convex combi
nation of `x`
and `y` with positive coefficients has norm strictly less than `r`.
-/
theorem norm_combo_lt_of_ne (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hne : x ≠ y) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) : ‖a • x + b • y‖ < r := by
  simp only [← mem_ball_zero_iff, ← mem_closedBall_zero_iff] at hx hy ⊢
  exact combo_mem_ball_of_ne hx hy hne ha hb hab

/-- In a strictly convex space, if `x` and `y` are not in the same ray, then `‖x + y‖ < ‖x‖ + ‖y‖`.
-/
/-
**norm_add_lt_of_not_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_add_lt_of_not_sameRay (h : ¬SameRay Real x y) : ‖x + y‖ < ‖x‖ + ‖y‖
参数：h : ¬SameRay Real x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `combo_mem_ball_of_ne`：combo_mem_ball_of_ne (hx : x in closedBall z r) (h
y : y in closedBall z r) (hne : x != y) (ha : 0 < a) (hb : 0 < b) (hab : a + b =
 1) : a • …
· 使用定理 `inv_norm_smul_mem_unitClosedBall`：inv_norm_smul_mem_unitClosedBall (x : 
E) : ‖x‖⁻¹ • x in closedBall (0 : E) 1
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r

--- 原说明 ---
In a strictly convex space, if `x` and `y` are not in the same ray, then `‖x + y
‖ < ‖x‖ + ‖y‖`.
-/
theorem norm_add_lt_of_not_sameRay (h : ¬SameRay ℝ x y) : ‖x + y‖ < ‖x‖ + ‖y‖ := by
  simp only [sameRay_iff_inv_norm_smul_eq, not_or, ← Ne.eq_def] at h
  rcases h with ⟨hx, hy, hne⟩
  rw [← norm_pos_iff] at hx hy
  have hxy : 0 < ‖x‖ + ‖y‖ := add_pos hx hy
  have :=
    combo_mem_ball_of_ne (inv_norm_smul_mem_unitClosedBall x)
      (inv_norm_smul_mem_unitClosedBall y) hne (div_pos hx hxy) (div_pos hy hxy)
      (by rw [← add_div, div_self hxy.ne'])
  rwa [mem_ball_zero_iff, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, smul_inv_smul₀ hx.ne',
    smul_inv_smul₀ hy.ne', ← smul_add, norm_smul, Real.norm_of_nonneg (inv_pos.2 hxy).le, ←
    div_eq_inv_mul, div_lt_one hxy] at this
/-
**lt_norm_sub_of_not_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_norm_sub_of_not_sameRay (h : ¬SameRay Real x y) : ‖x‖ - ‖y‖ < ‖x - y‖
参数：h : ¬SameRay Real x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
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
· 使用定理 `norm_add_lt_of_not_sameRay`：norm_add_lt_of_not_sameRay (h : ¬SameRay Rea
l x y) : ‖x + y‖ < ‖x‖ + ‖y‖
· 使用定理 `SameRay.add_left`：add_left (hx : SameRay R x z) (hy : SameRay R y z) : S
ameRay R (x + y) z
· 使用定理 `SameRay.rfl`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialO
rder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoi
d…
-/
theorem lt_norm_sub_of_not_sameRay (h : ¬SameRay ℝ x y) : ‖x‖ - ‖y‖ < ‖x - y‖ := by
  nth_rw 1 [← sub_add_cancel x y] at h ⊢
  exact sub_lt_iff_lt_add.2 (norm_add_lt_of_not_sameRay fun H' => h <| H'.add_left SameRay.rfl)
/-
**abs_lt_norm_sub_of_not_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_lt_norm_sub_of_not_sameRay (h : ¬SameRay Real x y) : |‖x‖ - ‖y‖| < ‖x 
- y‖
参数：h : ¬SameRay Real x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_sub_lt_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| < c ↔ a - b < c ∧ b - a 
< c
· 使用定理 `lt_norm_sub_of_not_sameRay`：lt_norm_sub_of_not_sameRay (h : ¬SameRay Rea
l x y) : ‖x‖ - ‖y‖ < ‖x - y‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SameRay.symm`：symm (h : SameRay R x y) : SameRay R y x
-/
theorem abs_lt_norm_sub_of_not_sameRay (h : ¬SameRay ℝ x y) : |‖x‖ - ‖y‖| < ‖x - y‖ := by
  refine abs_sub_lt_iff.2 ⟨lt_norm_sub_of_not_sameRay h, ?_⟩
  rw [norm_sub_rev]
  exact lt_norm_sub_of_not_sameRay (mt SameRay.symm h)

/-- In a strictly convex space, two vectors `x`, `y` are in the same ray if and only if the triangle
inequality for `x` and `y` becomes an equality. -/
/-
**sameRay_iff_norm_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_iff_norm_add : SameRay Real x y ↔ ‖x + y‖ = ‖x‖ + ‖y‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.norm_add`：norm_add (h : SameRay Real x y) : ‖x + y‖ = ‖x‖ + ‖y‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `norm_add_lt_of_not_sameRay`：norm_add_lt_of_not_sameRay (h : ¬SameRay Rea
l x y) : ‖x + y‖ < ‖x‖ + ‖y‖

--- 原说明 ---
In a strictly convex space, two vectors `x`, `y` are in the same ray if and only
 if the triangle
inequality for `x` and `y` becomes an equality.
-/
theorem sameRay_iff_norm_add : SameRay ℝ x y ↔ ‖x + y‖ = ‖x‖ + ‖y‖ :=
  ⟨SameRay.norm_add, fun h => Classical.not_not.1 fun h' => (norm_add_lt_of_not_sameRay h').ne h⟩

/-- If `x` and `y` are two vectors in a strictly convex space have the same norm and the norm of
their sum is equal to the sum of their norms, then they are equal. -/
/-
**eq_of_norm_eq_of_norm_add_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_norm_eq_of_norm_add_eq (h₁ : ‖x‖ = ‖y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) :
 x = y
参数：h₁ : ‖x‖ = ‖y‖；h₂ : ‖x + y‖ = ‖x‖ + ‖y‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.eq_of_norm_eq`：SameRay.eq_of_norm_eq (h : SameRay Real x y) (hn 
: ‖x‖ = ‖y‖) : x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sameRay_iff_norm_add`：sameRay_iff_norm_add : SameRay Real x y ↔ ‖x + y‖ 
= ‖x‖ + ‖y‖

--- 原说明 ---
If `x` and `y` are two vectors in a strictly convex space have the same norm and
 the norm of
their sum is equal to the sum of their norms, then they are equal.
-/
theorem eq_of_norm_eq_of_norm_add_eq (h₁ : ‖x‖ = ‖y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) : x = y :=
  (sameRay_iff_norm_add.mpr h₂).eq_of_norm_eq h₁

/-- In a strictly convex space, two vectors `x`, `y` are not in the same ray if and only if the
triangle inequality for `x` and `y` is strict. -/
/-
**not_sameRay_iff_norm_add_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_sameRay_iff_norm_add_lt : ¬SameRay Real x y ↔ ‖x + y‖ < ‖x‖ + ‖y‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `sameRay_iff_norm_add`：sameRay_iff_norm_add : SameRay Real x y ↔ ‖x + y‖ 
= ‖x‖ + ‖y‖
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖

--- 原说明 ---
In a strictly convex space, two vectors `x`, `y` are not in the same ray if and 
only if the
triangle inequality for `x` and `y` is strict.
-/
theorem not_sameRay_iff_norm_add_lt : ¬SameRay ℝ x y ↔ ‖x + y‖ < ‖x‖ + ‖y‖ :=
  sameRay_iff_norm_add.not.trans (norm_add_le _ _).lt_iff_ne.symm
/-
**sameRay_iff_norm_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_iff_norm_sub : SameRay Real x y ↔ ‖x - y‖ = |‖x‖ - ‖y‖|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.norm_sub`：norm_sub (h : SameRay Real x y) : ‖x - y‖ = |‖x‖ - ‖y‖
|
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `abs_lt_norm_sub_of_not_sameRay`：abs_lt_norm_sub_of_not_sameRay (h : ¬Sam
eRay Real x y) : |‖x‖ - ‖y‖| < ‖x - y‖
-/
theorem sameRay_iff_norm_sub : SameRay ℝ x y ↔ ‖x - y‖ = |‖x‖ - ‖y‖| :=
  ⟨SameRay.norm_sub, fun h =>
    Classical.not_not.1 fun h' => (abs_lt_norm_sub_of_not_sameRay h').ne' h⟩
/-
**not_sameRay_iff_abs_lt_norm_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_sameRay_iff_abs_lt_norm_sub : ¬SameRay Real x y ↔ |‖x‖ - ‖y‖| < ‖x - y
‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `sameRay_iff_norm_sub`：sameRay_iff_norm_sub : SameRay Real x y ↔ ‖x - y‖ 
= |‖x‖ - ‖y‖|
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `abs_norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E]
 (a b : E), |‖a‖ - ‖b‖| ≤ ‖a - b‖
-/
theorem not_sameRay_iff_abs_lt_norm_sub : ¬SameRay ℝ x y ↔ |‖x‖ - ‖y‖| < ‖x - y‖ :=
  sameRay_iff_norm_sub.not.trans <| ne_comm.trans (abs_norm_sub_norm_le _ _).lt_iff_ne.symm
/-
**norm_midpoint_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_midpoint_lt_iff (h : ‖x‖ = ‖y‖) : ‖(1 / 2 : Real) • (x + y)‖ < ‖x‖ ↔ 
x != y
参数：h : ‖x‖ = ‖y‖。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_nonneg`：one_div_nonneg : 0 <= 1 / a ↔ 0 <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `zero_lt_two'`：zero_lt_two' : (0 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `not_sameRay_iff_of_norm_eq`：not_sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) :
 ¬SameRay Real x y ↔ x != y
· 使用定理 `not_sameRay_iff_norm_add_lt`：not_sameRay_iff_norm_add_lt : ¬SameRay Real
 x y ↔ ‖x + y‖ < ‖x‖ + ‖y‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_midpoint_lt_iff (h : ‖x‖ = ‖y‖) : ‖(1 / 2 : ℝ) • (x + y)‖ < ‖x‖ ↔ x ≠ y := by
  rw [norm_smul, Real.norm_of_nonneg (one_div_nonneg.2 zero_le_two), ← inv_eq_one_div, ←
    div_eq_inv_mul, div_lt_iff₀ (zero_lt_two' ℝ), mul_two, ← not_sameRay_iff_of_norm_eq h,
    not_sameRay_iff_norm_add_lt, h]
/-
**Real.instStrictConvexSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.instStrictConvexSpace : StrictConvexSpace Real Real where strictConve
x_closedBall _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `strictConvex_iff_convex`：strictConvex_iff_convex : StrictConvex 𝕜 s ↔ Co
nvex 𝕜 s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
-/
instance Real.instStrictConvexSpace : StrictConvexSpace ℝ ℝ where
  strictConvex_closedBall _ _ := strictConvex_iff_convex.mpr (convex_closedBall _ _)
