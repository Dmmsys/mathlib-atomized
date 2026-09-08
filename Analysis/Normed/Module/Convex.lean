/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Metric properties of convex sets in normed spaces

We prove the following facts:

* `convexOn_norm`, `convexOn_dist` : norm and distance to a fixed point is convex on any convex
  set;
* `convexOn_univ_norm`, `convexOn_univ_dist` : norm and distance to a fixed point is convex on
  the whole space;
* `convexHull_ediam`, `convexHull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `isBounded_convexHull` : convex hull of a set is bounded if and only if the original set
  is bounded.
-/

public section

-- TODO assert_not_exists Cardinal

variable {E : Type*}

open Metric Set

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set E}

/-- The norm on a real normed space is convex on any convex set. See also `Seminorm.convexOn`
and `convexOn_univ_norm`. -/
/-
**convexOn_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_norm (hs : Convex Real s) : ConvexOn Real s norm
参数：hs : Convex Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r

--- 原说明 ---
The norm on a real normed space is convex on any convex set. See also `Seminorm.
convexOn`
and `convexOn_univ_norm`.
-/
theorem convexOn_norm (hs : Convex ℝ s) : ConvexOn ℝ s norm :=
  ⟨hs, fun x _ y _ a b ha hb _ =>
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]⟩

/-- The norm on a real normed space is convex on the whole space. See also `Seminorm.convexOn`
and `convexOn_norm`. -/
/-
**convexOn_univ_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_univ_norm : ConvexOn Real univ (norm : E -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_norm`：convexOn_norm (hs : Convex Real s) : ConvexOn Real s norm
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)

--- 原说明 ---
The norm on a real normed space is convex on the whole space. See also `Seminorm
.convexOn`
and `convexOn_norm`.
-/
theorem convexOn_univ_norm : ConvexOn ℝ univ (norm : E → ℝ) :=
  convexOn_norm convex_univ
/-
**convexOn_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_dist (z : E) (hs : Convex Real s) : ConvexOn Real s fun z' => dis
t z' z
参数：z : E；hs : Convex Real s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `ConvexOn.comp_affineMap`：ConvexOn.comp_affineMap {f : F -> β} (g : E ->ᵃ
[𝕜] F) {s : Set F} (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g)
· 使用定理 `convexOn_norm`：convexOn_norm (hs : Convex Real s) : ConvexOn Real s norm
· 使用定理 `Convex.translate`：Convex.translate (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 
((fun x => z + x) '' s)
-/
theorem convexOn_dist (z : E) (hs : Convex ℝ s) : ConvexOn ℝ s fun z' => dist z' z := by
  simpa [dist_eq_norm, preimage_preimage] using!
    (convexOn_norm (hs.translate (-z))).comp_affineMap (AffineMap.id ℝ E - AffineMap.const ℝ E z)
/-
**convexOn_univ_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_univ_dist (z : E) : ConvexOn Real univ fun z' => dist z' z
参数：z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_dist`：convexOn_dist (z : E) (hs : Convex Real s) : ConvexOn Rea
l s fun z' => dist z' z
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem convexOn_univ_dist (z : E) : ConvexOn ℝ univ fun z' => dist z' z :=
  convexOn_dist z convex_univ
/-
**convex_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
参数：a : E；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `ConvexOn.convex_lt`：ConvexOn.convex_lt (hf : ConvexOn 𝕜 s f) (r : β) : C
onvex 𝕜 ({ x in s | f x < r })
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `convexOn_univ_dist`：convexOn_univ_dist (z : E) : ConvexOn Real univ fun 
z' => dist z' z
-/
theorem convex_ball (a : E) (r : ℝ) : Convex ℝ (ball a r) := by
  simpa only [ball, sep_univ] using (convexOn_univ_dist a).convex_lt r
/-
**convex_eball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_eball (a : E) (r : ENNReal) : Convex Real (eball a r)
参数：a : E；r : ENNReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_top`：Metric.eball_top (x : α) : eball x ⊤ = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.eball_coe`：Metric.eball_coe {x : α} {ε : Real>=0} : eball x ε = b
all x ε
-/
theorem convex_eball (a : E) (r : ENNReal) : Convex ℝ (eball a r) := by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [eball_coe, convex_ball]
/-
**convex_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_closedBall (a : E) (r : Real) : Convex Real (closedBall a r)
参数：a : E；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `ConvexOn.convex_le`：ConvexOn.convex_le (hf : ConvexOn 𝕜 s f) (r : β) : C
onvex 𝕜 ({ x in s | f x <= r })
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `convexOn_univ_dist`：convexOn_univ_dist (z : E) : ConvexOn Real univ fun 
z' => dist z' z
-/
theorem convex_closedBall (a : E) (r : ℝ) : Convex ℝ (closedBall a r) := by
  simpa only [closedBall, sep_univ] using (convexOn_univ_dist a).convex_le r

/-- The segment from `x` to `y` is contained in the closed ball centered at `x` with radius
`dist x y`. -/
/-
**segment_subset_closedBall_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_subset_closedBall_left (x y : E) : segment Real x y subseteq close
dBall x (dist x y)
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
· 使用定理 `Metric.mem_closedBall_self`：mem_closedBall_self (h : 0 <= ε) : x in clos
edBall x ε
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
The segment from `x` to `y` is contained in the closed ball centered at `x` with
 radius
`dist x y`.
-/
theorem segment_subset_closedBall_left (x y : E) : segment ℝ x y ⊆ closedBall x (dist x y) :=
  (convex_closedBall x _).segment_subset (mem_closedBall_self dist_nonneg)
    (mem_closedBall.mpr (dist_comm y x ▸ le_refl _))

/-- The segment from `x` to `y` is contained in the closed ball centered at `y` with radius
`dist x y`. -/
/-
**segment_subset_closedBall_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_subset_closedBall_right (x y : E) : segment Real x y subseteq clos
edBall y (dist x y)
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_symm`：segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x]
· 使用定理 `segment_subset_closedBall_left`：segment_subset_closedBall_left (x y : E)
 : segment Real x y subseteq closedBall x (dist x y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
The segment from `x` to `y` is contained in the closed ball centered at `y` with
 radius
`dist x y`.
-/
theorem segment_subset_closedBall_right (x y : E) :
    segment ℝ x y ⊆ closedBall y (dist x y) := by
  rw [segment_symm]
  exact dist_comm x y ▸ segment_subset_closedBall_left y x
/-
**convex_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_closedEBall (a : E) (r : ENNReal) : Convex Real (closedEBall a r)
参数：a : E；r : ENNReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.closedEBall_top`：closedEBall_top (x : α) : closedEBall x ∞ = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.closedEBall_coe`：Metric.closedEBall_coe {x : α} {ε : Real>=0} : c
losedEBall x ε = closedBall x ε
-/
theorem convex_closedEBall (a : E) (r : ENNReal) : Convex ℝ (closedEBall a r) := by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [closedEBall_coe, convex_closedBall]

open scoped Pointwise in
/-
**convexHull_sphere_eq_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_sphere_eq_closedBall {F : Type*} [NormedAddCommGroup F] [Normed
Space Real F] [Nontrivial F] (x : F) {r : Real} (hr : 0 <= r) : convexHull Real 
(sphere x r) = closedBall x r
参数：x : F；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_convexHull_iff`：mem_convexHull_iff : x in convexHull 𝕜 s ↔ forall t,
 s subseteq t -> Convex 𝕜 t -> x in t
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NormedSpace.sphere_nonempty`：NormedSpace.sphere_nonempty {x : E} {r : Re
al} : (sphere x r).Nonempty ↔ 0 <= r
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `midpoint_self_neg`：midpoint_self_neg (x : V) : midpoint R x (-x) = 0
· 使用定理 `Convex.midpoint_mem`：Convex.midpoint_mem [Ring 𝕜] [LinearOrder 𝕜] [IsStr
ictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [Invertible (2 : 𝕜)] {s : Set E}
 {x y : E…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 62 条，此处仅展示前 30 条）
-/
theorem convexHull_sphere_eq_closedBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial F] (x : F) {r : ℝ} (hr : 0 ≤ r) :
    convexHull ℝ (sphere x r) = closedBall x r := by
  suffices convexHull ℝ (sphere (0 : F) r) = closedBall 0 r by
    rw [← add_zero x, ← vadd_eq_add, ← vadd_sphere, convexHull_vadd,
      this, vadd_closedBall_zero, vadd_eq_add, add_zero]
  refine subset_antisymm (convexHull_min sphere_subset_closedBall (convex_closedBall 0 r))
    (fun x h ↦ mem_convexHull_iff.mpr fun U hU_sub hU ↦ ?_)
  have zero_mem : (0 : F) ∈ U := by
    have _ : Invertible (2 : ℝ) := by use 2⁻¹ <;> grind
    obtain ⟨z, hz⟩ := NormedSpace.sphere_nonempty (E := F).mpr hr
    rw [← midpoint_self_neg (R := ℝ) (x := z)]
    exact Convex.midpoint_mem hU (hU_sub hz) <| hU_sub (by simp_all)
  by_cases hr₀ : r = 0
  · simp_all
  by_cases x_zero : x = 0
  · rwa [x_zero]
  set z := (r * ‖x‖⁻¹) • x with hz_def
  have hr₁ : r⁻¹ * ‖x‖ ≤ 1 := by
    simp only [mem_closedBall, dist_zero_right] at h
    grw [h, inv_mul_le_one]
  have hz : z ∈ U := by
    apply hU_sub
    simp_all [norm_smul]
  have := StarConvex.smul_mem (hU.starConvex zero_mem) hz (by positivity) hr₁
  rwa [hz_def, ← smul_assoc, smul_eq_mul, ← mul_assoc, mul_comm, mul_comm r⁻¹, mul_assoc _ r⁻¹,
    inv_mul_cancel₀ hr₀, mul_one, inv_mul_cancel₀ (by simp_all), one_smul] at this

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
/-
**convexHull_exists_dist_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_exists_dist_ge {s : Set E} {x : E} (hx : x in convexHull Real s
) (y : E) : exists x' in s, dist x y <= dist x' y
参数：hx : x in convexHull Real s；y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.exists_ge_of_mem_convexHull`：ConvexOn.exists_ge_of_mem_convexHu
ll {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t subseteq s) (hx : x in convexHull 
𝕜 t) : exists y in t, f x …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `convexOn_dist`：convexOn_dist (z : E) (hs : Convex Real s) : ConvexOn Rea
l s fun z' => dist z' z
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s

--- 原说明 ---
Given a point `x` in the convex hull of `s` and a point `y`, there exists a poin
t
of `s` at distance at least `dist x y` from `y`.
-/
theorem convexHull_exists_dist_ge {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (y : E) :
    ∃ x' ∈ s, dist x y ≤ dist x' y :=
  (convexOn_dist y (convex_convexHull ℝ _)).exists_ge_of_mem_convexHull (subset_convexHull ..) hx
/-
**Convex.thickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.thickening (hs : Convex Real s) (δ : Real) : Convex Real (thickenin
g δ s)
参数：hs : Convex Real s；δ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_ball_zero`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (δ : ℝ
) (s : Set E), s + Metric.ball 0 δ = Metric.thickening δ s
· 使用定理 `Convex.add`：Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
 Convex 𝕜 (s + t)
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
-/
theorem Convex.thickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (thickening δ s) := by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)
/-
**Convex.cthickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.cthickening (hs : Convex Real s) (δ : Real) : Convex Real (cthicken
ing δ s)
参数：hs : Convex Real s；δ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.cthickening_eq_iInter_thickening`：cthickening_eq_iInter_thickenin
g {δ : Real} (δ_nn : 0 <= δ) (E : Set α) : cthickening δ E = ⋂ (ε : Real) (_ : δ
 < ε), thickening ε E
· 使用定理 `convex_iInter₂`：convex_iInter₂ {ι : Sort*} {κ : ι -> Sort*} {s : (i : ι)
 -> κ i -> Set E} (h : forall i j, Convex 𝕜 (s i j)) : Convex 𝕜 (⋂ (i) (j), s i 
j)
· 使用定理 `Convex.thickening`：Convex.thickening (hs : Convex Real s) (δ : Real) : C
onvex Real (thickening δ s)
· 使用定理 `Metric.cthickening_of_nonpos`：cthickening_of_nonpos {δ : Real} (hδ : δ <
= 0) (E : Set α) : cthickening δ E = closure E
· 使用定理 `Convex.closure`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [ins
t_4 …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem Convex.cthickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (cthickening δ s) := by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_iInter_thickening hδ]
    exact convex_iInter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
/-
**convexHull_exists_dist_ge2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_exists_dist_ge2 {s t : Set E} {x y : E} (hx : x in convexHull R
eal s) (hy : y in convexHull Real t) : exists x' in s, exists y' in t, dist x y 
<= dist x' y'
参数：hx : x in convexHull Real s；hy : y in convexHull Real t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexHull_exists_dist_ge`：convexHull_exists_dist_ge {s : Set E} {x : E}
 (hx : x in convexHull Real s) (y : E) : exists x' in s, dist x y <= dist x' y
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
Given a point `x` in the convex hull of `s` and a point `y` in the convex hull o
f `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`.
-/
theorem convexHull_exists_dist_ge2 {s t : Set E} {x y : E} (hx : x ∈ convexHull ℝ s)
    (hy : y ∈ convexHull ℝ t) : ∃ x' ∈ s, ∃ y' ∈ t, dist x y ≤ dist x' y' := by
  rcases convexHull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
  rcases convexHull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
  use x', hx', y', hy'
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s`. -/
@[simp]
/-
**convexHull_ediam** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_ediam (s : Set E) : ediam (convexHull Real s) = ediam s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `convexHull_exists_dist_ge2`：convexHull_exists_dist_ge2 {s t : Set E} {x 
y : E} (hx : x in convexHull Real s) (hy : y in convexHull Real t) : exists x' i
n s, exists y' i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s

--- 原说明 ---
Emetric diameter of the convex hull of a set `s` equals the emetric diameter of 
`s`.
-/
theorem convexHull_ediam (s : Set E) : ediam (convexHull ℝ s) = ediam s := by
  refine (ediam_le fun x hx y hy => ?_).antisymm (ediam_mono <| subset_convexHull ℝ s)
  rcases convexHull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
  rw [edist_dist]
  apply le_trans (ENNReal.ofReal_le_ofReal H)
  rw [← edist_dist]
  exact edist_le_ediam_of_mem hx' hy'

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s`. -/
@[simp]
/-
**convexHull_diam** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_diam (s : Set E) : diam (convexHull Real s) = diam s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_ediam`：convexHull_ediam (s : Set E) : ediam (convexHull Real 
s) = ediam s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Diameter of the convex hull of a set `s` equals the emetric diameter of `s`.
-/
theorem convexHull_diam (s : Set E) : diam (convexHull ℝ s) = diam s := by
  simp only [diam, convexHull_ediam]

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp]
/-
**isBounded_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBounded_convexHull {s : Set E} : Bornology.IsBounded (convexHull Real s)
 ↔ Bornology.IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `convexHull_ediam`：convexHull_ediam (s : Set E) : ediam (convexHull Real 
s) = ediam s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Convex hull of `s` is bounded if and only if `s` is bounded.
-/
theorem isBounded_convexHull {s : Set E} :
    Bornology.IsBounded (convexHull ℝ s) ↔ Bornology.IsBounded s := by
  simp only [isBounded_iff_ediam_ne_top, convexHull_ediam]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormedSpace.instPathConnectedSpace : PathConnectedSpace E :=
  IsTopologicalAddGroup.pathConnectedSpace

/-- The set of vectors in the same ray as `x` is connected. -/
/-
**isConnected_setOfPred_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_setOfPred_sameRay (x : E) : IsConnected { y | SameRay Real x y
 }
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `isConnected_univ`：isConnected_univ [ConnectedSpace α] : IsConnected (uni
v : Set α)
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_nonneg_left_iff_sameRay`：exists_nonneg_left_iff_sameRay (hx : x !
= 0) : (exists r : R, 0 <= r ∧ r • x = y) ↔ SameRay R x y
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `isConnected_Ici`：isConnected_Ici : IsConnected (Ici a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ContinuousOn.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s

--- 原说明 ---
The set of vectors in the same ray as `x` is connected.
-/
theorem isConnected_setOfPred_sameRay (x : E) : IsConnected { y | SameRay ℝ x y } := by
  by_cases hx : x = 0; · simpa [hx] using isConnected_univ (α := E)
  simp_rw [← exists_nonneg_left_iff_sameRay hx]
  exact isConnected_Ici.image _ (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sameRay := isConnected_setOfPred_sameRay

/-- The set of nonzero vectors in the same ray as the nonzero vector `x` is connected. -/
/-
**isConnected_setOfPred_sameRay_and_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_setOfPred_sameRay_and_ne_zero {x : E} (hx : x != 0) : IsConnec
ted { y | SameRay Real x y ∧ y != 0 }
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_pos_left_iff_sameRay_and_ne_zero`：exists_pos_left_iff_sameRay_and
_ne_zero (hx : x != 0) : (exists r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y ∧ y !
= 0
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `isConnected_Ioi`：isConnected_Ioi [NoMaxOrder α] : IsConnected (Ioi a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `ContinuousOn.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s

--- 原说明 ---
The set of nonzero vectors in the same ray as the nonzero vector `x` is connecte
d.
-/
theorem isConnected_setOfPred_sameRay_and_ne_zero {x : E} (hx : x ≠ 0) :
    IsConnected { y | SameRay ℝ x y ∧ y ≠ 0 } := by
  simp_rw [← exists_pos_left_iff_sameRay_and_ne_zero hx]
  exact isConnected_Ioi.image _ (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sameRay_and_ne_zero := isConnected_setOfPred_sameRay_and_ne_zero
/-
**norm_sub_le_of_mem_segment** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_sub_le_of_mem_segment {x y z : E} (hy : y in segment Real x z) : ‖y -
 x‖ <= ‖z - x‖
参数：hy : y in segment Real x z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `segment_eq_image'`：segment_eq_image' (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜
 => x + θ • (y - x)) '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
lemma norm_sub_le_of_mem_segment {x y z : E} (hy : y ∈ segment ℝ x z) :
    ‖y - x‖ ≤ ‖z - x‖ := by
  rw [segment_eq_image'] at hy
  simp only [mem_image, mem_Icc] at hy
  obtain ⟨u, ⟨hu_nonneg, hu_le_one⟩, rfl⟩ := hy
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg hu_nonneg]
  conv_rhs => rw [← one_mul (‖z - x‖)]
  gcongr

namespace Filter

open scoped Convex Topology
variable {α : Type*} {f : Filter α} {x : E} {y z : α → E} {r : α → E → Prop}

/-
**Filter.Eventually.segment_of_prod_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Event
ually`。
形式化陈述：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] [inst_1 : NormedSpace ℝ
 E] {α : Type u_2} {f : Filter α} {x : E}   {y z : α → E} {r : α → E → Prop},   
Filter.Tendsto y f (nhds x) →     Filter.Tendsto z f (nhds x) →       (∀ᶠ (p : α
 × E) in f ×ˢ nhds x, r p.1 p.2) → ∀ᶠ (χ : α) in f, ∀ v ∈ segment ℝ (y χ) (z χ),
 r χ v
参数：nhds x；nhds x；∀ᶠ (p : α × E) in f ×ˢ nhds x, r p.1 p.2；χ : α；y χ；z χ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.eventually_prod_nhds_iff`：eventually_prod_nhds_iff {f : Filter ι}
 {x₀ : α} {p : ι × α -> Prop} : (forallᶠ x in f ×ˢ 𝓝 x₀, p x) ↔ exists pa : ι ->
 Prop, (forallᶠ i in …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `convex_iff_segment_subset`：convex_iff_segment_subset : Convex 𝕜 s ↔ fora
ll ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
-/
theorem Eventually.segment_of_prod_nhds (hy : Tendsto y f (𝓝 x)) (hz : Tendsto z f (𝓝 x))
    (hr : ∀ᶠ p in f ×ˢ 𝓝 x, r p.1 p.2) : ∀ᶠ χ in f, ∀ v ∈ [y χ -[ℝ] z χ], r χ v := by
  obtain ⟨p, hp, δ, hδ, hr⟩ := eventually_prod_nhds_iff.mp hr
  rw [Metric.tendsto_nhds] at hy hz
  filter_upwards [hp, hy δ hδ, hz δ hδ] with χ hp hy hz
  exact fun v hv => hr hp <| convex_iff_segment_subset.mp (convex_ball x δ) hy hz hv
/-
**Filter.Eventually.segment_of_prod_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `Filter
.Eventually`。
形式化陈述：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] [inst_1 : NormedSpace ℝ
 E] {s : Set E} {α : Type u_2} {f : Filter α}   {x : E} {y z : α → E} {r : α → E
 → Prop},   Filter.Tendsto y f (nhds x) →     Filter.Tendsto z f (nhds x) →     
  (∀ᶠ (p : α × E) in f ×ˢ nhdsWithin x s, r p.1 p.2) →         (∀ᶠ (χ : α) in f,
 segment ℝ (y χ) (z χ) ⊆ s) → ∀ᶠ (χ : α) in f, ∀ v ∈ segment ℝ (y χ) (z χ), r χ 
v
参数：nhds x；nhds x；∀ᶠ (p : α × E) in f ×ˢ nhdsWithin x s, r p.1 p.2；∀ᶠ (χ : α) in 
f, segment ℝ (y χ) (z χ) ⊆ s；χ : α；y χ；z χ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.segment_of_prod_nhds`：∀ {E : Type u_1} [inst : Seminor
medAddCommGroup E] [inst_1 : NormedSpace ℝ E] {α : Type u_2} {f : Filter α} {x :
 E}   {y z : α → E} {r : α →…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
-/
theorem Eventually.segment_of_prod_nhdsWithin (hy : Tendsto y f (𝓝 x)) (hz : Tendsto z f (𝓝 x))
    (hr : ∀ᶠ p in f ×ˢ 𝓝[s] x, r p.1 p.2) (seg : ∀ᶠ χ in f, [y χ -[ℝ] z χ] ⊆ s) :
    ∀ᶠ χ in f, ∀ v ∈ [y χ -[ℝ] z χ], r χ v := by
  refine seg.mp <| .mono ?_ (fun _ => forall₂_imp)
  apply Eventually.segment_of_prod_nhds hy hz
  simpa [nhdsWithin, prod_eq_inf, ← inf_assoc, eventually_inf_principal] using hr

end Filter

end SeminormedAddCommGroup

