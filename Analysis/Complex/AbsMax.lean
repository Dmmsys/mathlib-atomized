/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Extr
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Order.ExtrClosure

/-!
# Maximum modulus principle

In this file we prove several versions of the maximum modulus principle. There are several
statements that can be called "the maximum modulus principle" for maps between normed complex
spaces. They differ by assumptions on the domain (any space, a nontrivial space, a finite
dimensional space), assumptions on the codomain (any space, a strictly convex space), and by
conclusion (either equality of norms or of the values of the function).

## Main results

### Theorems for any codomain

Consider a function `f : E → F` that is complex differentiable on a set `s`, is continuous on its
closure, and `‖f x‖` has a maximum on `s` at `c`. We prove the following theorems.

- `Complex.norm_eqOn_closedBall_of_isMaxOn`: if `s = Metric.ball c r`, then `‖f x‖ = ‖f c‖` for
  any `x` from the corresponding closed ball;

- `Complex.norm_eq_norm_of_isMaxOn_of_ball_subset`: if `Metric.ball c (dist w c) ⊆ s`, then
  `‖f w‖ = ‖f c‖`;

- `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`: if `U` is an open (pre)connected set, `f` is
  complex differentiable on `U`, and `‖f x‖` has a maximum on `U` at `c ∈ U`, then `‖f x‖ = ‖f c‖`
  for all `x ∈ U`;

- `Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn`: if `s` is open and (pre)connected
  and `c ∈ s`, then `‖f x‖ = ‖f c‖` for all `x ∈ closure s`;

- `Complex.norm_eventually_eq_of_isLocalMax`: if `f` is complex differentiable in a neighborhood
  of `c` and `‖f x‖` has a local maximum at `c`, then `‖f x‖` is locally a constant in a
  neighborhood of `c`.

### Theorems for a strictly convex codomain

If the codomain `F` is a strictly convex space, then in the lemmas from the previous section we can
prove `f w = f c` instead of `‖f w‖ = ‖f c‖`, see
`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`,
`Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm`,
`Complex.eq_of_isMaxOn_of_ball_subset`, `Complex.eqOn_closedBall_of_isMaxOn_norm`, and
`Complex.eventually_eq_of_isLocalMax_norm`.

### Values on the frontier

Finally, we prove some corollaries that relate the (norm of the) values of a function on a set to
its values on the frontier of the set. All these lemmas assume that `E` is a nontrivial space.  In
this section `f g : E → F` are functions that are complex differentiable on a bounded set `s` and
are continuous on its closure. We prove the following theorems.

- `Complex.exists_mem_frontier_isMaxOn_norm`: If `E` is a finite-dimensional space and `s` is a
  nonempty bounded set, then there exists a point `z ∈ frontier s` such that `(‖f ·‖)` takes it
  maximum value on `closure s` at `z`.

- `Complex.norm_le_of_forall_mem_frontier_norm_le`: if `‖f z‖ ≤ C` for all `z ∈ frontier s`, then
  `‖f z‖ ≤ C` for all `z ∈ s`; note that this theorem does not require `E` to be a
  finite-dimensional space.

- `Complex.eqOn_closure_of_eqOn_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `closure s`;

- `Complex.eqOn_of_eqOn_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `s`.

## Tags

maximum modulus principle, complex analysis
-/

public section


open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory AffineMap Bornology

open scoped Topology Filter NNReal Real

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/-!
### Auxiliary lemmas

We split the proof into a series of lemmas. First we prove the principle for a function `f : ℂ → F`
with an additional assumption that `F` is a complete space, then drop unneeded assumptions one by
one.

The lemmas with names `*_auxₙ` are considered to be private and should not be used outside of this
file.
-/

/-
**Complex.norm_max_aux** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Auxiliary lemmas

We split the proof into a series of lemmas. First we prove the principle for a f
unction `f : ℂ → F`
with an additional assumption that `F` is a complete space, then drop unneeded a
ssumptions one by
one.

The lemmas with names `*_auxₙ` are considered to be private and should not be us
ed outside of this
file.
-/
theorem norm_max_aux₁ [CompleteSpace F] {f : ℂ → F} {z w : ℂ}
    (hd : DiffContOnCl ℂ f (ball z (dist w z)))
    (hz : IsMaxOn (norm ∘ f) (closedBall z (dist w z)) z) : ‖f w‖ = ‖f z‖ := by
  -- Consider a circle of radius `r = dist w z`.
  set r : ℝ := dist w z
  have hw : w ∈ closedBall z r := mem_closedBall.2 le_rfl
  -- Assume the converse. Since `‖f w‖ ≤ ‖f z‖`, we have `‖f w‖ < ‖f z‖`.
  refine (isMaxOn_iff.1 hz _ hw).antisymm (not_lt.1 ?_)
  rintro hw_lt : ‖f w‖ < ‖f z‖
  have hr : 0 < r := dist_pos.2 (ne_of_apply_ne (norm ∘ f) hw_lt.ne)
  -- Due to Cauchy integral formula, it suffices to prove the following inequality.
  suffices ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * ‖f z‖ by
    refine this.ne ?_
    have A : (∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ) = (2 * π * I : ℂ) • f z :=
      hd.circleIntegral_sub_inv_smul (mem_ball_self hr)
    simp [A, norm_smul, Real.pi_pos.le]
  suffices ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * r * (‖f z‖ / r) by
    rwa [mul_assoc, mul_div_cancel₀ _ hr.ne'] at this
  /- This inequality is true because `‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r` for all `ζ` on the circle and
    this inequality is strict at `ζ = w`. -/
  have hsub : sphere z r ⊆ closedBall z r := sphere_subset_closedBall
  refine circleIntegral.norm_integral_lt_of_norm_le_const_of_lt hr ?_ ?_ ⟨w, rfl, ?_⟩
  · show ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹ • f ζ) (sphere z r)
    refine ((continuousOn_id.sub continuousOn_const).inv₀ ?_).smul (hd.continuousOn_ball.mono hsub)
    exact fun ζ hζ => sub_ne_zero.2 (ne_of_mem_sphere hζ hr.ne')
  · show ∀ ζ ∈ sphere z r, ‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r
    rintro ζ hζ
    rw [le_div_iff₀ hr, norm_smul, norm_inv, mem_sphere_iff_norm.1 hζ, mul_comm,
      mul_inv_cancel_left₀ hr.ne']
    exact hz (hsub hζ)
  show ‖(w - z)⁻¹ • f w‖ < ‖f z‖ / r
  rw [norm_smul, norm_inv, ← div_eq_inv_mul, ← dist_eq_norm]
  exact (div_lt_div_iff_of_pos_right hr).2 hw_lt

/-!
Now we drop the assumption `CompleteSpace F` by embedding `F` into its completion.
-/

/-
**Complex.norm_max_aux** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Now we drop the assumption `CompleteSpace F` by embedding `F` into its completio
n.
-/
theorem norm_max_aux₂ {f : ℂ → F} {z w : ℂ} (hd : DiffContOnCl ℂ f (ball z (dist w z)))
    (hz : IsMaxOn (norm ∘ f) (closedBall z (dist w z)) z) : ‖f w‖ = ‖f z‖ := by
  set e : F →L[ℂ] F̂ := UniformSpace.Completion.toComplL
  have he : ∀ x, ‖e x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
  replace hz : IsMaxOn (norm ∘ e ∘ f) (closedBall z (dist w z)) z := by
    simpa only [IsMaxOn, Function.comp_def, he] using hz
  simpa only [he, Function.comp_def]
    using norm_max_aux₁ (e.differentiable.comp_diffContOnCl hd) hz

/-!
Then we replace the assumption `IsMaxOn (norm ∘ f) (Metric.closedBall z r) z` with a seemingly
weaker assumption `IsMaxOn (norm ∘ f) (Metric.ball z r) z`.
-/

/-
**Complex.norm_max_aux** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Then we replace the assumption `IsMaxOn (norm ∘ f) (Metric.closedBall z r) z` wi
th a seemingly
weaker assumption `IsMaxOn (norm ∘ f) (Metric.ball z r) z`.
-/
theorem norm_max_aux₃ {f : ℂ → F} {z w : ℂ} {r : ℝ} (hr : dist w z = r)
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) : ‖f w‖ = ‖f z‖ := by
  subst r
  rcases eq_or_ne w z with (rfl | hne); · rfl
  rw [← dist_ne_zero] at hne
  exact norm_max_aux₂ hd (closure_ball z hne ▸ hz.closure hd.continuousOn.norm)

/-!
### Maximum modulus principle for any codomain

If we do not assume that the codomain is a strictly convex space, then we can only claim that the
**norm** `‖f x‖` is locally constant.
-/

/-!
Finally, we generalize the theorem from a disk in `ℂ` to a closed ball in any normed space.
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- **Maximum modulus principle** on a closed ball: if `f : E → F` is continuous on a closed ball,
is complex differentiable on the corresponding open ball, and the norm `‖f w‖` takes its maximum
value on the open ball at its center, then the norm `‖f w‖` is constant on the closed ball. -/
/-
**Complex.norm_eqOn_closedBall_of_isMaxOn** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_eqOn_closedBall_of_isMaxOn {f : E -> F} {z : E} {r : Real} (hd : Diff
ContOnCl Complex f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) : EqOn (no
rm ∘ f) (const E ‖f z‖) (closedBall z r)
参数：hd : DiffContOnCl Complex f (ball z r)；hz : IsMaxOn (norm ∘ f) (ball z r) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `Differentiable.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `Differentiable.smul_const`：Differentiable.smul_const (hc : Differentiabl
e 𝕜 c) (f : F) : Differentiable 𝕜 fun y => c y • f
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `LipschitzWith.mapsTo_ball`：mapsTo_ball (hf : LipschitzWith K f) (hK : K 
!= 0) (x : α) (r : Real) : MapsTo f (Metric.ball x r) (Metric.ball (f x) (K * r)
)
· 使用定理 `lipschitzWith_lineMap`：lipschitzWith_lineMap (p₁ p₂ : P) : LipschitzWith
 (nndist p₁ p₂) (lineMap p₁ p₂ : 𝕜 -> P)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nndist_eq_zero`：nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Metric.ball_subset_ball`：ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ sub
seteq ball x ε₂
· 使用定理 `Complex.norm_max_aux₃`：norm_max_aux₃ {f : Complex -> F} {z w : Complex} 
{r : Real} (hr : dist w z = r) (hd : DiffContOnCl Complex f (ball z r)) (hz : Is
MaxOn (norm…
· 使用定理 `DiffContOnCl.comp`：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f 
s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `IsMaxOn.comp_mapsTo`：IsMaxOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ
} (hf : IsMaxOn f s a) (hg : MapsTo g t s) (ha : g b = a) : IsMaxOn (f ∘ g) t b
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁

--- 原说明 ---
**Maximum modulus principle** on a closed ball: if `f : E → F` is continuous on 
a closed ball,
is complex differentiable on the corresponding open ball, and the norm `‖f w‖` t
akes its maximum
value on the open ball at its center, then the norm `‖f w‖` is constant on the c
losed ball.
-/
theorem norm_eqOn_closedBall_of_isMaxOn {f : E → F} {z : E} {r : ℝ}
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn (norm ∘ f) (const E ‖f z‖) (closedBall z r) := by
  intro w hw
  rw [mem_closedBall, dist_comm] at hw
  rcases eq_or_ne z w with (rfl | hne); · rfl
  set e := (lineMap z w : ℂ → E)
  have hde : Differentiable ℂ e := (differentiable_id.smul_const (w - z)).add_const z
  suffices ‖(f ∘ e) (1 : ℂ)‖ = ‖(f ∘ e) (0 : ℂ)‖ by simpa [e]
  have hr : dist (1 : ℂ) 0 = 1 := by simp
  have hball : MapsTo e (ball 0 1) (ball z r) := by
    refine ((lipschitzWith_lineMap z w).mapsTo_ball (mt nndist_eq_zero.1 hne) 0 1).mono
      Subset.rfl ?_
    simpa only [lineMap_apply_zero, mul_one, coe_nndist] using ball_subset_ball hw
  exact norm_max_aux₃ hr (hd.comp hde.diffContOnCl hball)
      (hz.comp_mapsTo hball (lineMap_apply_zero z w))

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a set `s`, the norm
of `f` takes it maximum on `s` at `z`, and `w` is a point such that the closed ball with center `z`
and radius `dist w z` is included in `s`, then `‖f w‖ = ‖f z‖`. -/
/-
**Complex.norm_eq_norm_of_isMaxOn_of_ball_subset** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
形式化陈述：norm_eq_norm_of_isMaxOn_of_ball_subset {f : E -> F} {s : Set E} {z w : E} 
(hd : DiffContOnCl Complex f s) (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (di
st w z) subseteq s) : ‖f w‖ = ‖f z‖
参数：hd : DiffContOnCl Complex f s；hz : IsMaxOn (norm ∘ f) s z；hsub : ball z (dist
 w z) subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.norm_eqOn_closedBall_of_isMaxOn`：norm_eqOn_closedBall_of_isMaxOn
 {f : E -> F} {z : E} {r : Real} (hd : DiffContOnCl Complex f (ball z r)) (hz : 
IsMaxOn (norm ∘ f) (ball z r)…
· 使用定理 `DiffContOnCl.mono`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst 
: NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedA
ddCommG…
· 使用定理 `IsMaxOn.on_subset`：IsMaxOn.on_subset (hf : IsMaxOn f t a) (h : s subsete
q t) : IsMaxOn f s a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
**Maximum modulus principle**: if `f : E → F` is complex differentiable on a set
 `s`, the norm
of `f` takes it maximum on `s` at `z`, and `w` is a point such that the closed b
all with center `z`
and radius `dist w z` is included in `s`, then `‖f w‖ = ‖f z‖`.
-/
theorem norm_eq_norm_of_isMaxOn_of_ball_subset {f : E → F} {s : Set E} {z w : E}
    (hd : DiffContOnCl ℂ f s) (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) :
    ‖f w‖ = ‖f z‖ :=
  norm_eqOn_closedBall_of_isMaxOn (hd.mono hsub) (hz.on_subset hsub) (mem_closedBall.2 le_rfl)

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `‖f z‖` is locally constant in a neighborhood
of `c`. -/
/-
**Complex.norm_eventually_eq_of_isLocalMax** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_eventually_eq_of_isLocalMax {f : E -> F} {c : E} (hd : forallᶠ z in 𝓝
 c, DifferentiableAt Complex f z) (hc : IsLocalMax (norm ∘ f) c) : forallᶠ y in 
𝓝 c, ‖f y‖ = ‖f c‖
参数：hd : forallᶠ z in 𝓝 c, DifferentiableAt Complex f z；hc : IsLocalMax (norm ∘ f
) c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.norm_eqOn_closedBall_of_isMaxOn`：norm_eqOn_closedBall_of_isMaxOn
 {f : E -> F} {z : E} {r : Real} (hd : DiffContOnCl Complex f (ball z r)) (hz : 
IsMaxOn (norm ∘ f) (ball z r)…
· 使用定理 `DifferentiableOn.diffContOnCl`：DifferentiableOn.diffContOnCl (h : Differ
entiableOn 𝕜 f (closure s)) : DiffContOnCl 𝕜 f s
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Metric.closure_ball_subset_closedBall`：closure_ball_subset_closedBall : 
closure (ball x ε) subseteq closedBall x ε
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε

--- 原说明 ---
**Maximum modulus principle**: if `f : E → F` is complex differentiable in a nei
ghborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `‖f z‖` is locally constan
t in a neighborhood
of `c`.
-/
theorem norm_eventually_eq_of_isLocalMax {f : E → F} {c : E}
    (hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ := by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, norm_eqOn_closedBall_of_isMaxOn (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx =>
      (hr <| ball_subset_closedBall hx).2⟩
/-
**Complex.isOpen_setOfPred_mem_nhds_and_isMaxOn_norm** 是 Mathlib 中的一个定理，位于命名空间 `
Complex`。
形式化陈述：isOpen_setOfPred_mem_nhds_and_isMaxOn_norm {f : E -> F} {s : Set E} (hd : 
DifferentiableOn Complex f s) : IsOpen {z | s in 𝓝 z ∧ IsMaxOn (norm ∘ f) s z}
参数：hd : DifferentiableOn Complex f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `eventually_eventually_nhds`：eventually_eventually_nhds {p : X -> Prop} :
 (forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝 x, p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `DifferentiableOn.eventually_differentiableAt`：DifferentiableOn.eventuall
y_differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : forallᶠ y in 𝓝
 x, DifferentiableAt 𝕜 f y
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Complex.norm_eventually_eq_of_isLocalMax`：norm_eventually_eq_of_isLocalM
ax {f : E -> F} {c : E} (hd : forallᶠ z in 𝓝 c, DifferentiableAt Complex f z) (h
c : IsLocalMax (norm ∘ f) c) :…
· 使用定理 `IsMaxOn.isLocalMax`：IsMaxOn.isLocalMax (hf : IsMaxOn f s a) (hs : s in 𝓝
 a) : IsLocalMax f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem isOpen_setOfPred_mem_nhds_and_isMaxOn_norm {f : E → F} {s : Set E}
    (hd : DifferentiableOn ℂ f s) : IsOpen {z | s ∈ 𝓝 z ∧ IsMaxOn (norm ∘ f) s z} := by
  refine isOpen_iff_mem_nhds.2 fun z hz => (eventually_eventually_nhds.2 hz.1).and ?_
  replace hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w := hd.eventually_differentiableAt hz.1
  exact (norm_eventually_eq_of_isLocalMax hd <| hz.2.isLocalMax hz.1).mono fun x hx y hy =>
    le_trans (hz.2 hy).out hx.ge

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_mem_nhds_and_isMaxOn_norm := isOpen_setOfPred_mem_nhds_and_isMaxOn_norm

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space. Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `‖f x‖ = ‖f c‖` for all `x ∈ U`. -/
/-
**Complex.norm_eqOn_of_isPreconnected_of_isMaxOn** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
形式化陈述：norm_eqOn_of_isPreconnected_of_isMaxOn {f : E -> F} {U : Set E} {c : E} (h
c : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn Complex f U) (hcU :
 c in U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) U
参数：hc : IsPreconnected U；ho : IsOpen U；hd : DifferentiableOn Complex f U；hcU : c
 in U；hm : IsMaxOn (norm ∘ f) U c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用定理 `Complex.isOpen_setOfPred_mem_nhds_and_isMaxOn_norm`：isOpen_setOfPred_mem
_nhds_and_isMaxOn_norm {f : E -> F} {s : Set E} (hd : DifferentiableOn Complex f
 s) : IsOpen {z | s in 𝓝 z ∧ IsMaxOn (no…
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `IsPreconnected.subset_left_of_subset_union`：IsPreconnected.subset_left_o
f_subset_union (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hsuv : s su
bseteq u union v) (hsu : (s inte…

--- 原说明 ---
**Maximum modulus principle** on a connected set. Let `U` be a (pre)connected op
en set in a
complex normed space. Let `f : E → F` be a function that is complex differentiab
le on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `‖f x‖ = ‖f c‖` for
 all `x ∈ U`.
-/
theorem norm_eqOn_of_isPreconnected_of_isMaxOn {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) U := by
  set V := U ∩ {z | IsMaxOn (norm ∘ f) U z}
  have hV : ∀ x ∈ V, ‖f x‖ = ‖f c‖ := fun x hx => le_antisymm (hm hx.1) (hx.2 hcU)
  suffices U ⊆ V from fun x hx => hV x (this hx)
  have hVo : IsOpen V := by
    simpa only [ho.mem_nhds_iff, ofPred_and, ofPred_mem_eq]
      using isOpen_setOfPred_mem_nhds_and_isMaxOn_norm hd
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, hm⟩
  set W := U ∩ {z | ‖f z‖ ≠ ‖f c‖}
  have hWo : IsOpen W := hd.continuousOn.norm.isOpen_inter_preimage ho isOpen_ne
  have hdVW : Disjoint V W := disjoint_left.mpr fun x hxV hxW => hxW.2 (hV x hxV)
  have hUVW : U ⊆ V ∪ W := fun x hx =>
    (eq_or_ne ‖f x‖ ‖f c‖).imp (fun h => ⟨hx, fun y hy => (hm hy).out.trans_eq h.symm⟩)
      (And.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`‖f x‖ = ‖f c‖` for all `x ∈ closure U`. -/
/-
**Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn** 是 Mathlib 中的一个定理，位于命名
空间 `Complex`。
形式化陈述：norm_eqOn_closure_of_isPreconnected_of_isMaxOn {f : E -> F} {U : Set E} {c
 : E} (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl Complex f U) (h
cU : c in U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) (cl
osure U)
参数：hc : IsPreconnected U；ho : IsOpen U；hd : DiffContOnCl Complex f U；hcU : c in 
U；hm : IsMaxOn (norm ∘ f) U c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.of_subset_closure`：Set.EqOn.of_subset_closure [T2Space Y] {s t 
: Set X} {f g : X -> Y} (h : EqOn f g s) (hf : ContinuousOn f t) (hg : Continuou
sOn g t) (hst : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`：norm_eqOn_of_isPreconnec
ted_of_isMaxOn {f : E -> F} {U : Set E} {c : E} (hc : IsPreconnected U) (ho : Is
Open U) (hd : DifferentiableOn Compl…
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
**Maximum modulus principle** on a connected set. Let `U` be a (pre)connected op
en set in a
complex normed space.  Let `f : E → F` be a function that is complex differentia
ble on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` a
t `c ∈ U`. Then
`‖f x‖ = ‖f c‖` for all `x ∈ closure U`.
-/
theorem norm_eqOn_closure_of_isPreconnected_of_isMaxOn {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) (closure U) :=
  (norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn.norm continuousOn_const subset_closure Subset.rfl

section StrictConvex

/-!
### The case of a strictly convex codomain

If the codomain `F` is a strictly convex space, then we can claim equalities like `f w = f z`
instead of `‖f w‖ = ‖f z‖`.

Instead of repeating the proof starting with lemmas about integrals, we apply a corresponding lemma
above twice: for `f` and for `(f · + f c)`.  Then we have `‖f w‖ = ‖f z‖` and
`‖f w + f z‖ = ‖f z + f z‖`, thus `‖f w + f z‖ = ‖f w‖ + ‖f z‖`. This is only possible if
`f w = f z`, see `eq_of_norm_eq_of_norm_add_eq`.
-/

variable [StrictConvexSpace ℝ F]

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `f x = f c` for all `x ∈ U`.

TODO: change assumption from `IsMaxOn` to `IsLocalMax`. -/
/-
**Complex.eqOn_of_isPreconnected_of_isMaxOn_norm** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
形式化陈述：eqOn_of_isPreconnected_of_isMaxOn_norm {f : E -> F} {U : Set E} {c : E} (h
c : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn Complex f U) (hcU :
 c in U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) U
参数：hc : IsPreconnected U；ho : IsOpen U；hd : DifferentiableOn Complex f U；hcU : c
 in U；hm : IsMaxOn (norm ∘ f) U c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`：norm_eqOn_of_isPreconnec
ted_of_isMaxOn {f : E -> F} {U : Set E} {c : E} (hc : IsPreconnected U) (ho : Is
Open U) (hd : DifferentiableOn Compl…
· 使用定理 `DifferentiableOn.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `IsMaxOn.norm_add_self`：IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c
) : IsMaxOn (fun x => ‖f x + f c‖) s c
· 使用定理 `eq_of_norm_eq_of_norm_add_eq`：eq_of_norm_eq_of_norm_add_eq (h₁ : ‖x‖ = ‖
y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SameRay.norm_add`：norm_add (h : SameRay Real x y) : ‖x + y‖ = ‖x‖ + ‖y‖
· 使用定理 `SameRay.rfl`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialO
rder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoi
d…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Maximum modulus principle** on a connected set. Let `U` be a (pre)connected op
en set in a
complex normed space.  Let `f : E → F` be a function that is complex differentia
ble on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `f x = f c` for all
 `x ∈ U`.

TODO: change assumption from `IsMaxOn` to `IsLocalMax`.
-/
theorem eqOn_of_isPreconnected_of_isMaxOn_norm {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) U := fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd hcU hm hx
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hc ho (hd.add_const _) hcU hm.norm_add_self hx
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`f x = f c` for all `x ∈ closure U`. -/
/-
**Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm** 是 Mathlib 中的一个定理，位于命名
空间 `Complex`。
形式化陈述：eqOn_closure_of_isPreconnected_of_isMaxOn_norm {f : E -> F} {U : Set E} {c
 : E} (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl Complex f U) (h
cU : c in U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) (closure U)
参数：hc : IsPreconnected U；ho : IsOpen U；hd : DiffContOnCl Complex f U；hcU : c in 
U；hm : IsMaxOn (norm ∘ f) U c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.of_subset_closure`：Set.EqOn.of_subset_closure [T2Space Y] {s t 
: Set X} {f g : X -> Y} (h : EqOn f g s) (hf : ContinuousOn f t) (hg : Continuou
sOn g t) (hst : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`：eqOn_of_isPreconnected_o
f_isMaxOn_norm {f : E -> F} {U : Set E} {c : E} (hc : IsPreconnected U) (ho : Is
Open U) (hd : DifferentiableOn Compl…
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
**Maximum modulus principle** on a connected set. Let `U` be a (pre)connected op
en set in a
complex normed space.  Let `f : E → F` be a function that is complex differentia
ble on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` a
t `c ∈ U`. Then
`f x = f c` for all `x ∈ closure U`.
-/
theorem eqOn_closure_of_isPreconnected_of_isMaxOn_norm {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) (closure U) :=
  (eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn continuousOn_const subset_closure Subset.rfl

/-- **Maximum modulus principle**. Let `f : E → F` be a function between complex normed spaces.
Suppose that the codomain `F` is a strictly convex space, `f` is complex differentiable on a set
`s`, `f` is continuous on the closure of `s`, the norm of `f` takes it maximum on `s` at `z`, and
`w` is a point such that the closed ball with center `z` and radius `dist w z` is included in `s`,
then `f w = f z`. -/
/-
**Complex.eq_of_isMaxOn_of_ball_subset** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：eq_of_isMaxOn_of_ball_subset {f : E -> F} {s : Set E} {z w : E} (hd : Diff
ContOnCl Complex f s) (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) su
bseteq s) : f w = f z
参数：hd : DiffContOnCl Complex f s；hz : IsMaxOn (norm ∘ f) s z；hsub : ball z (dist
 w z) subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.norm_eq_norm_of_isMaxOn_of_ball_subset`：norm_eq_norm_of_isMaxOn_
of_ball_subset {f : E -> F} {s : Set E} {z w : E} (hd : DiffContOnCl Complex f s
) (hz : IsMaxOn (norm ∘ f) s z) (hsu…
· 使用定理 `DiffContOnCl.add_const`：add_const (hf : DiffContOnCl 𝕜 f s) (c : F) : Di
ffContOnCl 𝕜 (fun x => f x + c) s
· 使用定理 `IsMaxOn.norm_add_self`：IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c
) : IsMaxOn (fun x => ‖f x + f c‖) s c
· 使用定理 `eq_of_norm_eq_of_norm_add_eq`：eq_of_norm_eq_of_norm_add_eq (h₁ : ‖x‖ = ‖
y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SameRay.norm_add`：norm_add (h : SameRay Real x y) : ‖x + y‖ = ‖x‖ + ‖y‖
· 使用定理 `SameRay.rfl`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialO
rder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoi
d…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Maximum modulus principle**. Let `f : E → F` be a function between complex nor
med spaces.
Suppose that the codomain `F` is a strictly convex space, `f` is complex differe
ntiable on a set
`s`, `f` is continuous on the closure of `s`, the norm of `f` takes it maximum o
n `s` at `z`, and
`w` is a point such that the closed ball with center `z` and radius `dist w z` i
s included in `s`,
then `f w = f z`.
-/
theorem eq_of_isMaxOn_of_ball_subset {f : E → F} {s : Set E} {z w : E} (hd : DiffContOnCl ℂ f s)
    (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) : f w = f z :=
  have H₁ : ‖f w‖ = ‖f z‖ := norm_eq_norm_of_isMaxOn_of_ball_subset hd hz hsub
  have H₂ : ‖f w + f z‖ = ‖f z + f z‖ :=
    norm_eq_norm_of_isMaxOn_of_ball_subset (hd.add_const _) hz.norm_add_self hsub
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, SameRay.rfl.norm_add, H₁]

/-- **Maximum modulus principle** on a closed ball. Suppose that a function `f : E → F` from a
normed complex space to a strictly convex normed complex space has the following properties:

- it is continuous on a closed ball `Metric.closedBall z r`,
- it is complex differentiable on the corresponding open ball;
- the norm `‖f w‖` takes its maximum value on the open ball at its center.

Then `f` is a constant on the closed ball. -/
/-
**Complex.eqOn_closedBall_of_isMaxOn_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：eqOn_closedBall_of_isMaxOn_norm {f : E -> F} {z : E} {r : Real} (hd : Diff
ContOnCl Complex f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) : EqOn f (
const E (f z)) (closedBall z r)
参数：hd : DiffContOnCl Complex f (ball z r)；hz : IsMaxOn (norm ∘ f) (ball z r) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.eq_of_isMaxOn_of_ball_subset`：eq_of_isMaxOn_of_ball_subset {f : 
E -> F} {s : Set E} {z w : E} (hd : DiffContOnCl Complex f s) (hz : IsMaxOn (nor
m ∘ f) s z) (hsub : ball z…
· 使用定理 `Metric.ball_subset_ball`：ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ sub
seteq ball x ε₂

--- 原说明 ---
**Maximum modulus principle** on a closed ball. Suppose that a function `f : E →
 F` from a
normed complex space to a strictly convex normed complex space has the following
 properties:

- it is continuous on a closed ball `Metric.closedBall z r`,
- it is complex differentiable on the corresponding open ball;
- the norm `‖f w‖` takes its maximum value on the open ball at its center.

Then `f` is a constant on the closed ball.
-/
theorem eqOn_closedBall_of_isMaxOn_norm {f : E → F} {z : E} {r : ℝ}
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn f (const E (f z)) (closedBall z r) := fun _x hx =>
  eq_of_isMaxOn_of_ball_subset hd hz <| ball_subset_ball hx

/-- If `f` is differentiable on the open unit ball `{z : ℂ | ‖z‖ < 1}`, and `‖f‖` attains a maximum
in this open ball, then `f` is constant. -/
/-
**Complex.eq_const_of_exists_max** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：eq_const_of_exists_max {f : E -> F} {b : Real} (h_an : DifferentiableOn Co
mplex f (ball 0 b)) {v : E} (hv : v in ball 0 b) (hv_max : IsMaxOn (norm ∘ f) (b
all 0 b) v) : Set.EqOn f (Function.const E (f v)) (ball 0 b)
参数：h_an : DifferentiableOn Complex f (ball 0 b)；hv : v in ball 0 b；hv_max : IsMa
xOn (norm ∘ f) (ball 0 b) v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`：eqOn_of_isPreconnected_o
f_isMaxOn_norm {f : E -> F} {U : Set E} {c : E} (hc : IsPreconnected U) (ho : Is
Open U) (hd : DifferentiableOn Compl…
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)

--- 原说明 ---
If `f` is differentiable on the open unit ball `{z : ℂ | ‖z‖ < 1}`, and `‖f‖` at
tains a maximum
in this open ball, then `f` is constant.
-/
lemma eq_const_of_exists_max {f : E → F} {b : ℝ} (h_an : DifferentiableOn ℂ f (ball 0 b))
    {v : E} (hv : v ∈ ball 0 b) (hv_max : IsMaxOn (norm ∘ f) (ball 0 b) v) :
    Set.EqOn f (Function.const E (f v)) (ball 0 b) :=
  Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball 0 b).isPreconnected
    isOpen_ball h_an hv hv_max

/-- If `f` is a function differentiable on the open unit ball, and there exists an `r < 1` such that
any value of `‖f‖` on the open ball is bounded above by some value on the closed ball of radius `r`,
then `f` is constant. -/
/-
**Complex.eq_const_of_exists_le** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：eq_const_of_exists_le [ProperSpace E] {f : E -> F} {r b : Real} (h_an : Di
fferentiableOn Complex f (ball 0 b)) (hr_nn : 0 <= r) (hr_lt : r < b) (hr : fora
ll z, z in (ball 0 b) -> exists w, w in closedBall 0 r ∧ ‖f z‖ <= ‖f w‖) : Set.E
qOn f (Function.const E (f 0)) (ball 0 b)
参数：h_an : DifferentiableOn Complex f (ball 0 b)；hr_nn : 0 <= r；hr_lt : r < b；hr 
: forall z, z in (ball 0 b) -> exists w, w in closedBall 0 r ∧ ‖f z‖ <= ‖f w‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Metric.closedBall_subset_ball`：closedBall_subset_ball (h : ε₁ < ε₂) : cl
osedBall x ε₁ subseteq ball x ε₂
· 使用引理 `Complex.eq_const_of_exists_max`：eq_const_of_exists_max {f : E -> F} {b :
 Real} (h_an : DifferentiableOn Complex f (ball 0 b)) {v : E} (hv : v in ball 0 
b) (hv_max : IsMaxOn…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
If `f` is a function differentiable on the open unit ball, and there exists an `
r < 1` such that
any value of `‖f‖` on the open ball is bounded above by some value on the closed
 ball of radius `r`,
then `f` is constant.
-/
lemma eq_const_of_exists_le [ProperSpace E] {f : E → F} {r b : ℝ}
    (h_an : DifferentiableOn ℂ f (ball 0 b)) (hr_nn : 0 ≤ r) (hr_lt : r < b)
    (hr : ∀ z, z ∈ (ball 0 b) → ∃ w, w ∈ closedBall 0 r ∧ ‖f z‖ ≤ ‖f w‖) :
    Set.EqOn f (Function.const E (f 0)) (ball 0 b) := by
  obtain ⟨x, hx_mem, hx_max⟩ := isCompact_closedBall (0 : E) r |>.exists_isMaxOn
    (nonempty_closedBall.mpr hr_nn)
    (h_an.continuousOn.mono <| closedBall_subset_ball hr_lt).norm
  suffices Set.EqOn f (Function.const E (f x)) (ball 0 b) by
    rwa [this (mem_ball_self (hr_nn.trans_lt hr_lt))]
  apply eq_const_of_exists_max h_an (closedBall_subset_ball hr_lt hx_mem) (fun z hz ↦ ?_)
  obtain ⟨w, hw, hw'⟩ := hr z hz
  exact hw'.trans (hx_max hw)

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `f` is locally constant in a neighborhood
of `c`. -/
/-
**Complex.eventually_eq_of_isLocalMax_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：eventually_eq_of_isLocalMax_norm {f : E -> F} {c : E} (hd : forallᶠ z in 𝓝
 c, DifferentiableAt Complex f z) (hc : IsLocalMax (norm ∘ f) c) : forallᶠ y in 
𝓝 c, f y = f c
参数：hd : forallᶠ z in 𝓝 c, DifferentiableAt Complex f z；hc : IsLocalMax (norm ∘ f
) c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.eqOn_closedBall_of_isMaxOn_norm`：eqOn_closedBall_of_isMaxOn_norm
 {f : E -> F} {z : E} {r : Real} (hd : DiffContOnCl Complex f (ball z r)) (hz : 
IsMaxOn (norm ∘ f) (ball z r)…
· 使用定理 `DifferentiableOn.diffContOnCl`：DifferentiableOn.diffContOnCl (h : Differ
entiableOn 𝕜 f (closure s)) : DiffContOnCl 𝕜 f s
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Metric.closure_ball_subset_closedBall`：closure_ball_subset_closedBall : 
closure (ball x ε) subseteq closedBall x ε
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε

--- 原说明 ---
**Maximum modulus principle**: if `f : E → F` is complex differentiable in a nei
ghborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `f` is locally constant in
 a neighborhood
of `c`.
-/
theorem eventually_eq_of_isLocalMax_norm {f : E → F} {c : E}
    (hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, f y = f c := by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, eqOn_closedBall_of_isMaxOn_norm (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx =>
      (hr <| ball_subset_closedBall hx).2⟩
/-
**Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm** 是 Mathlib 中的一个定理，位于命名空间 
`Complex`。
形式化陈述：eventually_eq_or_eq_zero_of_isLocalMin_norm {f : E -> Complex} {c : E} (hf
 : forallᶠ z in 𝓝 c, DifferentiableAt Complex f z) (hc : IsLocalMin (norm ∘ f) c
) : (forallᶠ z in 𝓝 c, f z = f c) ∨ f c = 0
参数：hf : forallᶠ z in 𝓝 c, DifferentiableAt Complex f z；hc : IsLocalMin (norm ∘ f
) c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `ContinuousAt.eventually_ne`：ContinuousAt.eventually_ne [TopologicalSpace
 Y] [T1Space Y] {g : X -> Y} {x : X} {y : Y} (hg1 : ContinuousAt g x) (hg2 : g x
 != y) : forallᶠ…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `IsLocalMin.inv`：IsLocalMin.inv {f : α -> β} {a : α} (h1 : IsLocalMin f a
) (h2 : forallᶠ z in 𝓝 a, 0 < f z) : IsLocalMax f⁻¹ a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `IsLocalMax.congr`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α
] [inst_1 : Preorder β] {f g : α → β} {a : α},   IsLocalMax f a → f =ᶠ[nhds a] g
 → IsL…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 39 条，此处仅展示前 30 条）
-/
theorem eventually_eq_or_eq_zero_of_isLocalMin_norm {f : E → ℂ} {c : E}
    (hf : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMin (norm ∘ f) c) :
    (∀ᶠ z in 𝓝 c, f z = f c) ∨ f c = 0 := by
  refine or_iff_not_imp_right.mpr fun h => ?_
  have h1 : ∀ᶠ z in 𝓝 c, f z ≠ 0 := hf.self_of_nhds.continuousAt.eventually_ne h
  have h2 : IsLocalMax (norm ∘ f)⁻¹ c := hc.inv (h1.mono fun z => norm_pos_iff.mpr)
  have h3 : IsLocalMax (norm ∘ f⁻¹) c := by refine h2.congr (Eventually.of_forall ?_); simp
  have h4 : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f⁻¹ z := by filter_upwards [hf, h1] with z h using h.inv
  filter_upwards [eventually_eq_of_isLocalMax_norm h4 h3] with z using inv_inj.mp

end StrictConvex

/-!
### Maximum on a set vs maximum on its frontier

In this section we prove corollaries of the maximum modulus principle that relate the values of a
function on a set to its values on the frontier of this set.
-/


variable [Nontrivial E]

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a nonempty bounded
set `U` and is continuous on its closure, then there exists a point `z ∈ frontier U` such that
`(‖f ·‖)` takes it maximum value on `closure U` at `z`. -/
/-
**Complex.exists_mem_frontier_isMaxOn_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exists_mem_frontier_isMaxOn_norm [FiniteDimensional Complex E] {f : E -> F
} {U : Set E} (hb : IsBounded U) (hne : U.Nonempty) (hd : DiffContOnCl Complex f
 U) : exists z in frontier U, IsMaxOn (norm ∘ f) (closure U) z
参数：hb : IsBounded U；hne : U.Nonempty；hd : DiffContOnCl Complex f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.isCompact_closure`：∀ {α : Type u} {s : Set α} [inst 
: PseudoMetricSpace α] [ProperSpace α], Bornology.IsBounded s → IsCompact (closu
re s)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `FiniteDimensional.complexToReal`：∀ (E : Type u_1) [inst : AddCommGroup E
] [inst_1 : _root_.Module ℂ E] [FiniteDimensional ℂ E], FiniteDimensional ℝ E
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Nonempty.closure`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Nonempty → (closure s).Nonempty
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `closure_eq_interior_union_frontier`：closure_eq_interior_union_frontier (
s : Set X) : closure s = interior s union frontier s
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `IsCompact.ne_univ`：IsCompact.ne_univ [NoncompactSpace X] (hs : IsCompact
 s) : s != univ
· 使用定理 `RealNormedSpace.noncompactSpace`：∀ (E : Type u_3) [inst : NormedAddCommG
roup E] [Nontrivial E] [NormedSpace ℝ E], NoncompactSpace E
· 使用定理 `interior_subset_closure`：interior_subset_closure : interior s subseteq c
losure s
· 使用定理 `exists_mem_frontier_infDist_compl_eq_dist`：exists_mem_frontier_infDist_c
ompl_eq_dist {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDime
nsional Real E] {x : E} {s : Se…
· 使用定理 `frontier_interior_subset`：frontier_interior_subset : frontier (interior 
s) subseteq frontier s
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_eq_norm_of_isMaxOn_of_ball_subset`：norm_eq_norm_of_isMaxOn_
of_ball_subset {f : E -> F} {s : Set E} {z w : E} (hd : DiffContOnCl Complex f s
) (hz : IsMaxOn (norm ∘ f) s z) (hsu…
· 使用定理 `IsMaxOn.on_subset`：IsMaxOn.on_subset (hf : IsMaxOn f t a) (h : s subsete
q t) : IsMaxOn f s a
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.ball_infDist_compl_subset`：ball_infDist_compl_subset : ball x (in
fDist x sᶜ) subseteq s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
**Maximum modulus principle**: if `f : E → F` is complex differentiable on a non
empty bounded
set `U` and is continuous on its closure, then there exists a point `z ∈ frontie
r U` such that
`(‖f ·‖)` takes it maximum value on `closure U` at `z`.
-/
theorem exists_mem_frontier_isMaxOn_norm [FiniteDimensional ℂ E] {f : E → F} {U : Set E}
    (hb : IsBounded U) (hne : U.Nonempty) (hd : DiffContOnCl ℂ f U) :
    ∃ z ∈ frontier U, IsMaxOn (norm ∘ f) (closure U) z := by
  have hc : IsCompact (closure U) := hb.isCompact_closure
  obtain ⟨w, hwU, hle⟩ : ∃ w ∈ closure U, IsMaxOn (norm ∘ f) (closure U) w :=
    hc.exists_isMaxOn hne.closure hd.continuousOn.norm
  rw [closure_eq_interior_union_frontier, mem_union] at hwU
  rcases hwU with hwU | hwU; rotate_left; · exact ⟨w, hwU, hle⟩
  have : interior U ≠ univ := ne_top_of_le_ne_top hc.ne_univ interior_subset_closure
  rcases exists_mem_frontier_infDist_compl_eq_dist hwU this with ⟨z, hzU, hzw⟩
  refine ⟨z, frontier_interior_subset hzU, fun x hx => (hle hx).out.trans_eq ?_⟩
  refine (norm_eq_norm_of_isMaxOn_of_ball_subset hd (hle.on_subset subset_closure) ?_).symm
  rw [dist_comm, ← hzw]
  exact ball_infDist_compl_subset.trans interior_subset

set_option backward.isDefEq.respectTransparency.types false in
/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a bounded set `U` and
`‖f z‖ ≤ C` for any `z ∈ frontier U`, then the same is true for any `z ∈ closure U`. -/
/-
**Complex.norm_le_of_forall_mem_frontier_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
形式化陈述：norm_le_of_forall_mem_frontier_norm_le {f : E -> F} {U : Set E} (hU : IsBo
unded U) (hd : DiffContOnCl Complex f U) {C : Real} (hC : forall z in frontier U
, ‖f z‖ <= C) {z : E} (hz : z in closure U) : ‖f z‖ <= C
参数：hU : IsBounded U；hd : DiffContOnCl Complex f U；hC : forall z in frontier U, ‖
f z‖ <= C；hz : z in closure U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `closure_eq_self_union_frontier`：closure_eq_self_union_frontier (s : Set 
X) : closure s = s union frontier s
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Differentiable.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `Differentiable.smul_const`：Differentiable.smul_const (hc : Differentiabl
e 𝕜 c) (f : F) : Differentiable 𝕜 fun y => c y • f
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `antilipschitzWith_lineMap`：antilipschitzWith_lineMap {p₁ p₂ : Q} (h : p₁
 != p₂) : AntilipschitzWith (nndist p₁ p₂)⁻¹ (lineMap p₁ p₂ : 𝕜 -> Q)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `DiffContOnCl.comp`：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f 
s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `Complex.exists_mem_frontier_isMaxOn_norm`：exists_mem_frontier_isMaxOn_no
rm [FiniteDimensional Complex E] {f : E -> F} {U : Set E} (hb : IsBounded U) (hn
e : U.Nonempty) (hd : DiffCont…
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `AntilipschitzWith.isBounded_preimage`：isBounded_preimage (hf : Antilipsc
hitzWith K f) {s : Set β} (hs : IsBounded s) : IsBounded (f ⁻¹' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Continuous.frontier_preimage_subset`：Continuous.frontier_preimage_subset
 (hf : Continuous f) (t : Set Y) : frontier (f ⁻¹' t) subseteq f ⁻¹' frontier t
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
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
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
**Maximum modulus principle**: if `f : E → F` is complex differentiable on a bou
nded set `U` and
`‖f z‖ ≤ C` for any `z ∈ frontier U`, then the same is true for any `z ∈ closure
 U`.
-/
theorem norm_le_of_forall_mem_frontier_norm_le {f : E → F} {U : Set E} (hU : IsBounded U)
    (hd : DiffContOnCl ℂ f U) {C : ℝ} (hC : ∀ z ∈ frontier U, ‖f z‖ ≤ C) {z : E}
    (hz : z ∈ closure U) : ‖f z‖ ≤ C := by
  rw [closure_eq_self_union_frontier, union_comm, mem_union] at hz
  rcases hz with hz | hz; · exact hC z hz
  /- In case of a finite-dimensional domain, one can just apply
    `Complex.exists_mem_frontier_isMaxOn_norm`. To make it work in any Banach space, we restrict
    the function to a line first. -/
  rcases exists_ne z with ⟨w, hne⟩
  set e := (lineMap z w : ℂ → E)
  have hde : Differentiable ℂ e := (differentiable_id.smul_const (w - z)).add_const z
  have hL : AntilipschitzWith (nndist z w)⁻¹ e := antilipschitzWith_lineMap hne.symm
  replace hd : DiffContOnCl ℂ (f ∘ e) (e ⁻¹' U) :=
    hd.comp hde.diffContOnCl (mapsTo_preimage _ _)
  have h₀ : (0 : ℂ) ∈ e ⁻¹' U := by simpa only [e, mem_preimage, lineMap_apply_zero]
  rcases exists_mem_frontier_isMaxOn_norm (hL.isBounded_preimage hU) ⟨0, h₀⟩ hd with ⟨ζ, hζU, hζ⟩
  calc
    ‖f z‖ = ‖f (e 0)‖ := by simp only [e, lineMap_apply_zero]
    _ ≤ ‖f (e ζ)‖ := hζ (subset_closure h₀)
    _ ≤ C := hC _ (hde.continuous.frontier_preimage_subset _ hζU)

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `closure U`. -/
/-
**Complex.eqOn_closure_of_eqOn_frontier** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：eqOn_closure_of_eqOn_frontier {f g : E -> F} {U : Set E} (hU : IsBounded U
) (hf : DiffContOnCl Complex f U) (hg : DiffContOnCl Complex g U) (hfg : EqOn f 
g (frontier U)) : EqOn f g (closure U)
参数：hU : IsBounded U；hf : DiffContOnCl Complex f U；hg : DiffContOnCl Complex g U；
hfg : EqOn f g (frontier U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.norm_le_of_forall_mem_frontier_norm_le`：norm_le_of_forall_mem_fr
ontier_norm_le {f : E -> F} {U : Set E} (hU : IsBounded U) (hd : DiffContOnCl Co
mplex f U) {C : Real} (hC : forall z…
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If two complex differentiable functions `f g : E → F` are equal on the boundary 
of a bounded set
`U`, then they are equal on `closure U`.
-/
theorem eqOn_closure_of_eqOn_frontier {f g : E → F} {U : Set E} (hU : IsBounded U)
    (hf : DiffContOnCl ℂ f U) (hg : DiffContOnCl ℂ g U) (hfg : EqOn f g (frontier U)) :
    EqOn f g (closure U) := by
  suffices H : ∀ z ∈ closure U, ‖(f - g) z‖ ≤ 0 by simpa [sub_eq_zero] using! H
  refine fun z hz => norm_le_of_forall_mem_frontier_norm_le hU (hf.sub hg) (fun w hw => ?_) hz
  simp [hfg hw]

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `U`. -/
/-
**Complex.eqOn_of_eqOn_frontier** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：eqOn_of_eqOn_frontier {f g : E -> F} {U : Set E} (hU : IsBounded U) (hf : 
DiffContOnCl Complex f U) (hg : DiffContOnCl Complex g U) (hfg : EqOn f g (front
ier U)) : EqOn f g U
参数：hU : IsBounded U；hf : DiffContOnCl Complex f U；hg : DiffContOnCl Complex g U；
hfg : EqOn f g (frontier U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Complex.eqOn_closure_of_eqOn_frontier`：eqOn_closure_of_eqOn_frontier {f 
g : E -> F} {U : Set E} (hU : IsBounded U) (hf : DiffContOnCl Complex f U) (hg :
 DiffContOnCl Complex g U) …

--- 原说明 ---
If two complex differentiable functions `f g : E → F` are equal on the boundary 
of a bounded set
`U`, then they are equal on `U`.
-/
theorem eqOn_of_eqOn_frontier {f g : E → F} {U : Set E} (hU : IsBounded U) (hf : DiffContOnCl ℂ f U)
    (hg : DiffContOnCl ℂ g U) (hfg : EqOn f g (frontier U)) : EqOn f g U :=
  (eqOn_closure_of_eqOn_frontier hU hf hg hfg).mono subset_closure

end Complex

