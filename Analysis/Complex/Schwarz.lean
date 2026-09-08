/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Schwarz lemma

In this file we prove several versions of the Schwarz lemma.

* `Complex.norm_deriv_le_div_of_mapsTo_ball`. Let `f : ℂ → E` be a complex analytic function
  on an open disk with center `c` and a positive radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then the norm of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`.

* `Complex.dist_le_div_mul_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c` and radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`.

* `Complex.norm_deriv_le_one_of_mapsTo_ball`. If `f : ℂ → E` is complex analytic
  on an open disk with center `c` and a positive radius `R₁`,
  and it sends this disk to a closed ball with center `f c` and radius the same radius,
  then the norm of the derivative of `f` at the center of this disk is at most `1`.

* `Complex.dist_le_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c`.
  If `f` sends this ball to a closed ball with center `f c` and the same radius,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ dist z c`.

* `Complex.norm_le_norm_of_mapsTo_ball`:
  Let `f : E → F` be a complex analytic on an open ball with center at the origin.
  If `f` sends this ball to the closed ball with center `0` of the same radius and `f 0 = 0`,
  then for any point `z` of this disk we have `‖f z‖ ≤ ‖z‖`.

## Implementation notes

Traditionally, the Schwarz lemma is formulated for maps `f : ℂ → ℂ`.
We generalize all versions of the lemma to the case of maps to any normed space.
For the versions that don't use `deriv` or `dslope`,
we state it for maps between any two normed spaces.

## TODO

* Prove that any diffeomorphism of the unit disk to itself is a Möbius map.

## Tags

Schwarz lemma
-/

open Metric Set Function Filter TopologicalSpace

open scoped Topology ComplexConjugate

namespace Complex

/-- An auxiliary lemma for `Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`. -/
/-
**Complex.schwarz_aux** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：schwarz_aux {f : Complex -> Complex} {c z : Complex} {R₁ R₂ : Real} {n : N
at} (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball c R₁)
 (closedBall (f c) R₂)) (hn : (f · - f c) =o[𝓝 c] (fun w => (w - c) ^ n)) (hz : 
z in ball c R₁) : ‖f z - f c‖ <= R₂ * (‖z - c‖ / R₁) ^ (n + 1)
参数：hd : DifferentiableOn Complex f (ball c R₁)；h_maps : MapsTo f (ball c R₁) (cl
osedBall (f c) R₂)；hn : (f · - f c) =o[𝓝 c] (fun w => (w - c) ^ n)；hz : z in bal
l c R₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma for `Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`
.
-/
theorem schwarz_aux {f : ℂ → ℂ} {c z : ℂ} {R₁ R₂ : ℝ} {n : ℕ}
    (hd : DifferentiableOn ℂ f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (hn : (f · - f c) =o[𝓝 c] (fun w ↦ (w - c) ^ n)) (hz : z ∈ ball c R₁) :
    ‖f z - f c‖ ≤ R₂ * (‖z - c‖ / R₁) ^ (n + 1) := by
  -- By slightly reducing `R₁`, we can assume that `f` is differentiable on `closedBall c R₁`
  -- and it maps this ball to the closed ball in the codomain.
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  wlog hd' : DifferentiableOn ℂ f (closedBall c R₁) ∧
    MapsTo f (closedBall c R₁) (closedBall (f c) R₂) generalizing R₁
  · suffices ∀ᶠ r in 𝓝[<] R₁, ‖f z - f c‖ ≤ R₂ * (‖z - c‖ / r) ^ (n + 1) by
      refine ge_of_tendsto ?_ this
      refine ContinuousAt.continuousWithinAt ?_
      fun_prop (disch := positivity)
    rw [mem_ball_iff_norm] at hz
    filter_upwards [Ioo_mem_nhdsLT hz] with r ⟨hzr, hrR₁⟩
    apply this
    · exact hd.mono <| by gcongr
    · exact h_maps.mono_left <| by gcongr
    · rwa [mem_ball_iff_norm]
    · exact (norm_nonneg _).trans_lt hzr
    · exact ⟨hd.mono <| closedBall_subset_ball hrR₁, h_maps.mono_left <|
        closedBall_subset_ball hrR₁⟩
  -- Cleanup, discard the case `z = c`.
  clear hd h_maps
  rcases hd' with ⟨hd, h_maps⟩
  rcases eq_or_ne z c with rfl | hne
  · simp
  -- Consider the function given by `g w := ((w - c) ^ (n + 1))⁻¹ * (f w - f c)`.
  -- It is differentiable away from `c` and satisfies `g w = o((w - c)⁻¹)`,
  -- thus it can be extended to a function g'` differentiable on the whole closed ball
  -- with center c` and radius `R₁`.
  set g : ℂ → ℂ := fun w ↦ ((w - c) ^ (n + 1))⁻¹ * (f w - f c)
  set g' := update g c (limUnder (𝓝[≠] c) g)
  have hdg' : DifferentiableOn ℂ g' (closedBall c R₁) := by
    refine .mono ?_ (subset_insert_sdiff_singleton c _)
    apply differentiableOn_update_limUnder_insert_of_isLittleO
    · exact sdiff_mem_nhdsWithin_compl (closedBall_mem_nhds _ hR₁) _
    · refine .mul ?_ (hd.mono sdiff_subset |>.sub_const _)
      fun_prop (disch := simp +contextual [sub_eq_zero])
    · refine Asymptotics.isBigO_refl (fun w ↦ ((w - c) ^ (n + 1))⁻¹) _ |>.mul_isLittleO hn
        |>.mono (nhdsWithin_le_nhds (s := {c}ᶜ)) |>.congr' ?_ ?_
      · simp [g]
      · refine eventually_mem_nhdsWithin.mono fun w hw ↦ ?_
        rw [mem_compl_singleton_iff, ← sub_ne_zero] at hw
        simp [pow_succ, field]
  -- Finally, we apply the maximum modulus principle to this function.
  -- On the sphere `dist w c = R₁`, its norm is bounded by `R₂ / R₁ ^ (n + 1)`,
  -- thus it's bounded by the same constant on the whole closed ball,
  -- in particular, at `w = z`.
  suffices ‖g' z‖ ≤ R₂ / R₁ ^ (n + 1) by
    have hz' : ‖z - c‖ ≠ 0 := by simpa [sub_eq_zero] using hne
    simpa [g', hne, g, div_pow, mul_comm, field] using this
  refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hdg'.diffContOnCl_ball subset_rfl)
    ?_ ?_
  · grw [frontier_ball_subset_sphere]
    intro w hw
    have hwc := ne_of_mem_sphere hw hR₁.ne'
    have hfw : ‖f w - f c‖ ≤ R₂ := by
      simpa [dist_eq_norm] using h_maps (sphere_subset_closedBall hw)
    rw [mem_sphere_iff_norm] at hw
    simpa [g', hwc, g, hw, field]
  · exact subset_closure hz

public section

section NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {R R₁ R₂ : ℝ} {f : E → F} {c z : E}

set_option backward.isDefEq.respectTransparency.types false in
open AffineMap in
/-- Let `f : E → F` be a complex analytic map
sending an open ball of radius `R₁` to a closed ball of radius `R₂`.
If `f w - f c = o(‖w - c‖ ^ n)`, then for any `z` in the ball in the domain,
we have `dist (f z) (f c) ≤ R₂ * (dist z c / R₁) ^ (n + 1)`.

For `n = 0`, this theorem gives a usual Schwarz lemma,
see `dist_le_div_mul_dist_of_mapsTo_ball` below.
-/
/-
**Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO** 是 Mathlib 中的一个定理，位于命
名空间 `Complex`。
形式化陈述：dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO {f : E -> F} {c z : E} {R₁
 R₂ : Real} {n : Nat} (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : Ma
psTo f (ball c R₁) (closedBall (f c) R₂)) (hn : (f · - f c) =o[𝓝 c] (fun w => ‖w
 - c‖ ^ n)) (hz : z in ball c R₁) : dist (f z) (f c) <= R₂ * (dist z c / R₁) ^ (
n + 1)
参数：hd : DifferentiableOn Complex f (ball c R₁)；h_maps : MapsTo f (ball c R₁) (cl
osedBall (f c) R₂)；hn : (f · - f c) =o[𝓝 c] (fun w => ‖w - c‖ ^ n)；hz : z in bal
l c R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `exists_dual_vector`：exists_dual_vector (x : E) (h : ‖x‖ != 0) : exists g
 : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `norm_sub_eq_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a b : 
E}, ‖a - b‖ = 0 ↔ a = b
· 使用定理 `dist_lineMap_left`：dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap
 p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
Let `f : E → F` be a complex analytic map
sending an open ball of radius `R₁` to a closed ball of radius `R₂`.
If `f w - f c = o(‖w - c‖ ^ n)`, then for any `z` in the ball in the domain,
we have `dist (f z) (f c) ≤ R₂ * (dist z c / R₁) ^ (n + 1)`.

For `n = 0`, this theorem gives a usual Schwarz lemma,
see `dist_le_div_mul_dist_of_mapsTo_ball` below.
-/
theorem dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO {f : E → F} {c z : E} {R₁ R₂ : ℝ} {n : ℕ}
    (hd : DifferentiableOn ℂ f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (hn : (f · - f c) =o[𝓝 c] (fun w ↦ ‖w - c‖ ^ n)) (hz : z ∈ ball c R₁) :
    dist (f z) (f c) ≤ R₂ * (dist z c / R₁) ^ (n + 1) := by
  -- Note that `0 < R₁`, `0 ≤ R₂`, then discard the trivial case `f z = f c`.
  have hR₁ : 0 < R₁ := nonempty_ball.mp ⟨_, hz⟩
  have hR₂ : 0 ≤ R₂ := nonempty_closedBall.mp ⟨_, h_maps hz⟩
  rcases eq_or_ne (f z) (f c) with heq | hfne
  · trans 0 <;> [simp [heq]; positivity]
  have hne : z ≠ c := ne_of_apply_ne _ hfne
  -- Let `g : F → ℂ` be a continuous linear function such that `‖g‖ = 1`
  -- and `‖g (f z - f c)‖ = ‖f z - f c‖`.
  rcases exists_dual_vector ℂ _ (norm_sub_eq_zero_iff.not.mpr hfne) with ⟨g, hg, hgf⟩
  -- Consider `h : ℂ → ℂ` given by `h w = g (f (c + w * (z - c)))`.
  set h : ℂ → ℂ := g ∘ f ∘ lineMap c z
  -- This map is differentiable on the ball with center at the origin and radius `R₁ / dist z c`
  -- and it sends this ball to the closed ball with center `h 0 = f c` and radius R₂`.
  have hmaps_line : MapsTo (lineMap c z) (ball (0 : ℂ) (R₁ / dist z c)) (ball c R₁) := by
    intro w hw
    simpa [lt_div_iff₀, hne, dist_comm c] using hw
  have hmaps : MapsTo h (ball 0 (R₁ / dist z c)) (closedBall (h 0) R₂) := by
    refine MapsTo.comp ?_ (h_maps.comp hmaps_line)
    simpa [hg, h] using g.lipschitz.mapsTo_closedBall (f c) R₂
  have hdiff : DifferentiableOn ℂ h (ball 0 (R₁ / dist z c)) :=
    g.differentiable.comp_differentiableOn <| hd.comp (lineMap c z).differentiableOn hmaps_line
  -- This map also satisfies `h(w) - h(0) = o(w ^ n)`, thus we can apply the auxiliary lemma above.
  have hn : (h · - h 0) =o[𝓝 0] (fun w ↦ (w - 0) ^ n) := by
    simp only [h, ← map_sub, Function.comp_apply, sub_zero]
    refine (g.isBigO_comp _ _).trans_isLittleO ?_
    rw [← lineMap_apply_zero (k := ℂ) c z] at hn
    refine hn.comp_tendsto ?_ |>.trans_isBigO ?_
    · exact Continuous.tendsto (by fun_prop) 0
    · simpa [Function.comp_def, ← dist_eq_norm_sub, mul_pow, mul_comm]
        using (Asymptotics.isBigO_refl (· ^ n) (𝓝 (0 : ℂ))).norm_left.const_mul_left _
  have hmem : 1 ∈ ball (0 : ℂ) (R₁ / dist z c) := by
    simpa [lt_div_iff₀, hne]
  rw [map_sub] at hgf
  simpa [hgf, h, dist_eq_norm_sub] using schwarz_aux hdiff hmaps hn hmem

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and radius `R₁`.
If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
then for any `z` in the former ball we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`.
-/
/-
**Complex.dist_le_div_mul_dist_of_mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：dist_le_div_mul_dist_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball
 c R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z in ball c 
R₁) : dist (f z) (f c) <= R₂ / R₁ * dist z c
参数：hd : DifferentiableOn Complex f (ball c R₁)；h_maps : MapsTo f (ball c R₁) (cl
osedBall (f c) R₂)；hz : z in ball c R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`：dist_le_mul_div
_pow_of_mapsTo_ball_of_isLittleO {f : E -> F} {c z : E} {R₁ R₂ : Real} {n : Nat}
 (hd : DifferentiableOn Complex f (ball c R₁)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.Tendsto.sub_const`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] {c : G} {f : α → G}   {l : Filter α
}, Filter.Tend…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and radius `R₁`.
If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
then for any `z` in the former ball we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist
 z c`.
-/
theorem dist_le_div_mul_dist_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z ∈ ball c R₁) :
    dist (f z) (f c) ≤ R₂ / R₁ * dist z c := by
  refine dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (n := 0) hd h_maps ?_ hz |>.trans_eq ?_
  · simpa using hd.continuousOn.continuousAt
      (ball_mem_nhds _ <| nonempty_ball.mp ⟨_, hz⟩) |>.sub_const (f c)
  · simp [field]

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and positive radius `R₁`.
If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
then the norm of the Fréchet derivative of `f` at `c` is at most `R₂ / R₁`.
-/
/-
**Complex.norm_fderiv_le_div_of_mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_fderiv_le_div_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c
 R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) : ‖fde
riv Complex f c‖ <= R₂ / R₁
参数：hd : DifferentiableOn Complex f (ball c R₁)；h_maps : MapsTo f (ball c R₁) (cl
osedBall (f c) R₂)；h₀ : 0 < R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `Set.MapsTo.nonempty`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Se
t β} {f : α → β}, Set.MapsTo f s t → s.Nonempty → t.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `norm_fderiv_le_of_lip'`：norm_fderiv_le_of_lip' {f : E -> F} {x₀ : E} {C 
: Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) 
: ‖fderiv 𝕜 …
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), dist a b = ‖a - b‖
· 使用定理 `Complex.dist_le_div_mul_dist_of_mapsTo_ball`：dist_le_div_mul_dist_of_map
sTo_ball (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball 
c R₁) (closedBall (f c) R₂)) (hz …

--- 原说明 ---
The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and positive radius `R₁`.
If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
then the norm of the Fréchet derivative of `f` at `c` is at most `R₂ / R₁`.
-/
theorem norm_fderiv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) :
    ‖fderiv ℂ f c‖ ≤ R₂ / R₁ := by
  have : 0 ≤ R₂ := nonempty_closedBall.mp <| h_maps.nonempty <| nonempty_ball.mpr h₀
  refine norm_fderiv_le_of_lip' _ (by positivity) ?_
  filter_upwards [ball_mem_nhds _ h₀] with z hz
  simpa [dist_eq_norm_sub] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c`.
If `f` sends this ball to a closed ball with center `f c` and the same radius,
then for any `z` in the former ball we have `dist (f z) (f c) ≤ dist z c`.
-/
/-
**Complex.dist_le_dist_of_mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：dist_le_dist_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c R)) (
h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hz : z in ball c R) : dist (
f z) (f c) <= dist z c
参数：hd : DifferentiableOn Complex f (ball c R)；h_maps : MapsTo f (ball c R) (clos
edBall (f c) R)；hz : z in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.dist_le_div_mul_dist_of_mapsTo_ball`：dist_le_div_mul_dist_of_map
sTo_ball (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball 
c R₁) (closedBall (f c) R₂)) (hz …

--- 原说明 ---
The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c`.
If `f` sends this ball to a closed ball with center `f c` and the same radius,
then for any `z` in the former ball we have `dist (f z) (f c) ≤ dist z c`.
-/
theorem dist_le_dist_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hz : z ∈ ball c R) :
    dist (f z) (f c) ≤ dist z c := by
  simpa [(nonempty_ball.1 ⟨z, hz⟩).ne'] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

@[deprecated (since := "2026-01-03")]
alias dist_le_dist_of_mapsTo_ball_self := dist_le_dist_of_mapsTo_ball

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and a positive radius.
If `f` sends this ball to a closed ball with center `f c` and the same radius,
then the norm of the Fréchet derivative of `f` at `c` is at most one.
-/
/-
**Complex.norm_fderiv_le_one_of_mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_fderiv_le_one_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c
 R)) (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hR : 0 < R) : ‖fderiv 
Complex f c‖ <= 1
参数：hd : DifferentiableOn Complex f (ball c R)；h_maps : MapsTo f (ball c R) (clos
edBall (f c) R)；hR : 0 < R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Complex.norm_fderiv_le_div_of_mapsTo_ball`：norm_fderiv_le_div_of_mapsTo_
ball (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball c R₁
) (closedBall (f c) R₂)) (h₀ : …

--- 原说明 ---
The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and a positive radius.
If `f` sends this ball to a closed ball with center `f c` and the same radius,
then the norm of the Fréchet derivative of `f` at `c` is at most one.
-/
theorem norm_fderiv_le_one_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hR : 0 < R) :
    ‖fderiv ℂ f c‖ ≤ 1 := by
  simpa [hR.ne'] using norm_fderiv_le_div_of_mapsTo_ball hd h_maps hR

/-- The **Schwarz Lemma**.
Let `f : E → F` be a complex analytic on an open ball with center at the origin.
If `f` sends this ball to the closed ball with center `0` of the same radius and `f 0 = 0`,
then for any point `z` of this disk we have `‖f z‖ ≤ ‖z‖`. -/
/-
**Complex.norm_le_norm_of_mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_le_norm_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball 0 R)) (
h_maps : MapsTo f (ball 0 R) (closedBall 0 R)) (h₀ : f 0 = 0) (hz : ‖z‖ < R) : ‖
f z‖ <= ‖z‖
参数：hd : DifferentiableOn Complex f (ball 0 R)；h_maps : MapsTo f (ball 0 R) (clos
edBall 0 R)；h₀ : f 0 = 0；hz : ‖z‖ < R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Complex.dist_le_dist_of_mapsTo_ball`：dist_le_dist_of_mapsTo_ball (hd : D
ifferentiableOn Complex f (ball c R)) (h_maps : MapsTo f (ball c R) (closedBall 
(f c) R)) (hz : z in ball…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r

--- 原说明 ---
The **Schwarz Lemma**.
Let `f : E → F` be a complex analytic on an open ball with center at the origin.
If `f` sends this ball to the closed ball with center `0` of the same radius and
 `f 0 = 0`,
then for any point `z` of this disk we have `‖f z‖ ≤ ‖z‖`.
-/
theorem norm_le_norm_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball 0 R))
    (h_maps : MapsTo f (ball 0 R) (closedBall 0 R)) (h₀ : f 0 = 0) (hz : ‖z‖ < R) :
    ‖f z‖ ≤ ‖z‖ := by
  simpa [h₀] using dist_le_dist_of_mapsTo_ball hd (by rwa [h₀]) (mem_ball_zero_iff.mpr hz)

@[deprecated (since := "2026-01-03")]
alias norm_le_norm_of_mapsTo_ball_self := norm_le_norm_of_mapsTo_ball

end NormedSpace

section DimOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {R R₁ R₂ : ℝ} {f : ℂ → E}
  {c z z₀ : ℂ}

/-- The **Schwarz Lemma**: if `f : ℂ → E` is complex analytic
on an open disk with center `c` and a positive radius `R₁`,
and it sends this disk to a closed ball with center `f c` and radius `R₂`,
then the norm of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`. -/
/-
**Complex.norm_deriv_le_div_of_mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_deriv_le_div_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c 
R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) : ‖deri
v f c‖ <= R₂ / R₁
参数：hd : DifferentiableOn Complex f (ball c R₁)；h_maps : MapsTo f (ball c R₁) (cl
osedBall (f c) R₂)；h₀ : 0 < R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_deriv_eq_norm_fderiv`：norm_deriv_eq_norm_fderiv : ‖deriv f x‖ = ‖fd
eriv 𝕜 f x‖
· 使用定理 `Complex.norm_fderiv_le_div_of_mapsTo_ball`：norm_fderiv_le_div_of_mapsTo_
ball (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball c R₁
) (closedBall (f c) R₂)) (h₀ : …

--- 原说明 ---
The **Schwarz Lemma**: if `f : ℂ → E` is complex analytic
on an open disk with center `c` and a positive radius `R₁`,
and it sends this disk to a closed ball with center `f c` and radius `R₂`,
then the norm of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`.
-/
theorem norm_deriv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) :
    ‖deriv f c‖ ≤ R₂ / R₁ := by
  rw [norm_deriv_eq_norm_fderiv]
  exact norm_fderiv_le_div_of_mapsTo_ball hd h_maps h₀

/-- The **Schwarz Lemma**: if `f : ℂ → E` is complex analytic
on an open disk with center `c` and a positive radius `R₁`,
and it sends this disk to a closed ball with center `f c` and radius the same radius,
then the norm of the derivative of `f` at the center of this disk is at most `1`.
-/
/-
**Complex.norm_deriv_le_one_of_mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_deriv_le_one_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c 
R)) (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (h₀ : 0 < R) : ‖deriv f 
c‖ <= 1
参数：hd : DifferentiableOn Complex f (ball c R)；h_maps : MapsTo f (ball c R) (clos
edBall (f c) R)；h₀ : 0 < R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Complex.norm_deriv_le_div_of_mapsTo_ball`：norm_deriv_le_div_of_mapsTo_ba
ll (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) 
(closedBall (f c) R₂)) (h₀ : 0…
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
The **Schwarz Lemma**: if `f : ℂ → E` is complex analytic
on an open disk with center `c` and a positive radius `R₁`,
and it sends this disk to a closed ball with center `f c` and radius the same ra
dius,
then the norm of the derivative of `f` at the center of this disk is at most `1`
.
-/
theorem norm_deriv_le_one_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (h₀ : 0 < R) : ‖deriv f c‖ ≤ 1 :=
  (norm_deriv_le_div_of_mapsTo_ball hd h_maps h₀).trans_eq (div_self h₀.ne')

/-- Two cases of the **Schwarz Lemma** (derivative and distance), merged together.

If `f : ℂ → E` is a complex analytic function on an open ball `ball c R₁`
hat sends it to a closed ball `closedBall (f c) R₂`, then the norm of `dslope f c z`,
which is defined as `(z - c)⁻¹ • (f z - f c)` for `z ≠ c` and as `deriv f c` for `z = c`,
is not greater than the ratio `R₂ / R₁`.
-/
/-
**Complex.norm_dslope_le_div_of_mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_dslope_le_div_of_mapsTo_ball (hd : DifferentiableOn Complex f (ball c
 R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z in ball c R₁
) : ‖dslope f c z‖ <= R₂ / R₁
参数：hd : DifferentiableOn Complex f (ball c R₁)；h_maps : MapsTo f (ball c R₁) (cl
osedBall (f c) R₂)；hz : z in ball c R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dslope_same`：dslope_same (f : 𝕜 -> E) (a : 𝕜) : dslope f a a = deriv f a
· 使用定理 `Complex.norm_deriv_le_div_of_mapsTo_ball`：norm_deriv_le_div_of_mapsTo_ba
ll (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) 
(closedBall (f c) R₂)) (h₀ : 0…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `dslope_of_ne`：dslope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a b = sl
ope f a b
· 使用定理 `slope_def_module`：slope_def_module (f : k -> E) (a b : k) : slope f a b 
= (b - a)⁻¹ • (f b - f a)
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), dist a b = ‖a - b‖
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Complex.dist_le_div_mul_dist_of_mapsTo_ball`：dist_le_div_mul_dist_of_map
sTo_ball (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball 
c R₁) (closedBall (f c) R₂)) (hz …

--- 原说明 ---
Two cases of the **Schwarz Lemma** (derivative and distance), merged together.

If `f : ℂ → E` is a complex analytic function on an open ball `ball c R₁`
hat sends it to a closed ball `closedBall (f c) R₂`, then the norm of `dslope f 
c z`,
which is defined as `(z - c)⁻¹ • (f z - f c)` for `z ≠ c` and as `deriv f c` for
 `z = c`,
is not greater than the ratio `R₂ / R₁`.
-/
theorem norm_dslope_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z ∈ ball c R₁) :
    ‖dslope f c z‖ ≤ R₂ / R₁ := by
  rcases eq_or_ne z c with rfl | hne
  · simpa using norm_deriv_le_div_of_mapsTo_ball hd h_maps (by simpa using hz)
  · rw [dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv, ← dist_eq_norm_sub,
      ← dist_eq_norm_sub, ← div_eq_inv_mul, div_le_iff₀]
    · exact dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz
    · simpa

/-- Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_mapsTo_ball`,
if `‖dslope f c z₀‖ = R₂ / R₁` holds at a point in the ball
then the map `f` is affine with slope `dslope f c z₀`.

Note that this lemma requires the codomain to be a strictly convex space.
Indeed, for `E = ℂ × ℂ` there is a counterexample:
the map `f := fun z ↦ (z, z ^ 2)` sends `ball 0 1` to `closedBall 0 1`,
`‖dslope f 0 0‖ = ‖deriv f 0‖ = ‖(1, 0)‖ = 1`, but the map is not an affine map.
-/
/-
**Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div** 是 Mathlib 中的一个定理，位于命名空间 
`Complex`。
形式化陈述：affine_of_mapsTo_ball_of_norm_dslope_eq_div [StrictConvexSpace Real E] (hd
 : DifferentiableOn Complex f (ball c R₁)) (h_maps : Set.MapsTo f (ball c R₁) (c
losedBall (f c) R₂)) (h_z₀ : z₀ in ball c R₁) (h_eq : ‖dslope f c z₀‖ = R₂ / R₁)
 : Set.EqOn f (fun z => f c + (z - c) • dslope f c z₀) (ball c R₁)
参数：hd : DifferentiableOn Complex f (ball c R₁)；h_maps : Set.MapsTo f (ball c R₁)
 (closedBall (f c) R₂)；h_z₀ : z₀ in ball c R₁；h_eq : ‖dslope f c z₀‖ = R₂ / R₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.dslope_comp`：ContinuousLinearMap.dslope_comp {F : Ty
pe*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E ->L[𝕜] F) (g : 𝕜 -> E) (a b
 : 𝕜) (H : a = b -> D…
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Complex.norm_dslope_le_div_of_mapsTo_ball`：norm_dslope_le_div_of_mapsTo_
ball (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : MapsTo f (ball c R₁
) (closedBall (f c) R₂)) (hz : …
· 使用定理 `Differentiable.comp_differentiableOn`：Differentiable.comp_differentiable
On {g : F -> G} (hg : Differentiable 𝕜 g) (hf : DifferentiableOn 𝕜 f s) : Differ
entiableOn 𝕜 (g ∘ f) s
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UniformSpace.Completion.dist_eq`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] (x y : α), dist ↑x ↑y = dist x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isMaxOn_iff`：isMaxOn_iff : IsMaxOn f s a ↔ forall x in s, f x <= f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
· 使用定理 `Complex.differentiableOn_dslope`：differentiableOn_dslope {f : Complex ->
 E} {s : Set Complex} {c : Complex} (hc : s in 𝓝 c) : DifferentiableOn Complex (
dslope f c) s ↔ Diffe…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`：norm_eqOn_of_isPreconnec
ted_of_isMaxOn {f : E -> F} {U : Set E} {c : E} (hc : IsPreconnected U) (ho : Is
Open U) (hd : DifferentiableOn Compl…
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_m
apsTo_ball`,
if `‖dslope f c z₀‖ = R₂ / R₁` holds at a point in the ball
then the map `f` is affine with slope `dslope f c z₀`.

Note that this lemma requires the codomain to be a strictly convex space.
Indeed, for `E = ℂ × ℂ` there is a counterexample:
the map `f := fun z ↦ (z, z ^ 2)` sends `ball 0 1` to `closedBall 0 1`,
`‖dslope f 0 0‖ = ‖deriv f 0‖ = ‖(1, 0)‖ = 1`, but the map is not an affine map.
-/
theorem affine_of_mapsTo_ball_of_norm_dslope_eq_div [StrictConvexSpace ℝ E]
    (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : Set.MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (h_z₀ : z₀ ∈ ball c R₁) (h_eq : ‖dslope f c z₀‖ = R₂ / R₁) :
    Set.EqOn f (fun z => f c + (z - c) • dslope f c z₀) (ball c R₁) := by
  set e : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  set g := dslope (e ∘ f) c
  rintro z hz
  have h_R₁ : 0 < R₁ := nonempty_ball.mp ⟨_, h_z₀⟩
  have hg' : g = e ∘ dslope f c := by
    ext w
    simp only [g]
    rw [e.dslope_comp, Function.comp_apply]
    rintro rfl
    exact hd.differentiableAt <| ball_mem_nhds _ h_R₁
  have g_le_div : ∀ z ∈ ball c R₁, ‖g z‖ ≤ R₂ / R₁ := fun z hz =>
    norm_dslope_le_div_of_mapsTo_ball (e.differentiable.comp_differentiableOn hd)
      (fun w hw ↦ by simpa [e] using h_maps hw) hz
  have g_max : IsMaxOn (norm ∘ g) (ball c R₁) z₀ :=
    isMaxOn_iff.mpr fun z hz => by simpa [h_eq, hg', e] using g_le_div z hz
  have g_diff : DifferentiableOn ℂ g (ball c R₁) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self h_R₁))).mpr
      (e.differentiable.comp_differentiableOn hd)
  have heq : ‖dslope f c z‖ = ‖dslope f c z₀‖ := by
    simpa [hg', e] using norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball c R₁).isPreconnected
      isOpen_ball g_diff h_z₀ g_max hz
  have heq_add : ‖dslope f c z + dslope f c z₀‖ = ‖dslope f c z₀ + dslope f c z₀‖ := by
    simpa [hg', e, ← UniformSpace.Completion.coe_add]
      using norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball c R₁).isPreconnected
        isOpen_ball (g_diff.add_const (g z₀)) h_z₀ g_max.norm_add_self hz
  have : dslope f c z = dslope f c z₀ := eq_of_norm_eq_of_norm_add_eq heq <| by
    simp only [heq, SameRay.rfl.norm_add, heq_add]
  simp [← this]

@[deprecated (since := "2026-01-03")]
alias affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div :=
  affine_of_mapsTo_ball_of_norm_dslope_eq_div

/-- Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_mapsTo_ball`,
if there exists a point `z₀` in the ball such that `‖dslope f c z₀‖ = R₂ / R₁`,
then the map `f` is affine with the absolute value of the slope equal to `R₂ / R₁`.

This is an existence version of `affine_of_mapsTo_ball_of_norm_dslope_eq_div` above.

TODO: once the deprecated alias `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div` is gone,
rename this theorem to `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div`.
-/
/-
**Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'** 是 Mathlib 中的一个定理
，位于命名空间 `Complex`。
形式化陈述：affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' [StrictConvexSpace Rea
l E] (hd : DifferentiableOn Complex f (ball c R₁)) (h_maps : Set.MapsTo f (ball 
c R₁) (closedBall (f c) R₂)) (h_z₀ : exists z₀ in ball c R₁, ‖dslope f c z₀‖ = R
₂ / R₁) : exists C : E, ‖C‖ = R₂ / R₁ ∧ Set.EqOn f (fun z => f c + (z - c) • C) 
(ball c R₁)
参数：hd : DifferentiableOn Complex f (ball c R₁)；h_maps : Set.MapsTo f (ball c R₁)
 (closedBall (f c) R₂)；h_z₀ : exists z₀ in ball c R₁, ‖dslope f c z₀‖ = R₂ / R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`：affine_of_mapsTo_ba
ll_of_norm_dslope_eq_div [StrictConvexSpace Real E] (hd : DifferentiableOn Compl
ex f (ball c R₁)) (h_maps : Set.MapsTo f …

--- 原说明 ---
Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_m
apsTo_ball`,
if there exists a point `z₀` in the ball such that `‖dslope f c z₀‖ = R₂ / R₁`,
then the map `f` is affine with the absolute value of the slope equal to `R₂ / R
₁`.

This is an existence version of `affine_of_mapsTo_ball_of_norm_dslope_eq_div` ab
ove.

TODO: once the deprecated alias `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_
div` is gone,
rename this theorem to `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div`.
-/
theorem affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'
    [StrictConvexSpace ℝ E] (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : Set.MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (h_z₀ : ∃ z₀ ∈ ball c R₁, ‖dslope f c z₀‖ = R₂ / R₁) :
    ∃ C : E, ‖C‖ = R₂ / R₁ ∧ Set.EqOn f (fun z => f c + (z - c) • C) (ball c R₁) :=
  let ⟨z₀, h_z₀, h_eq⟩ := h_z₀
  ⟨dslope f c z₀, h_eq, affine_of_mapsTo_ball_of_norm_dslope_eq_div hd h_maps h_z₀ h_eq⟩

end DimOne

end -- public section

end Complex

