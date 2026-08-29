/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Grönwall's inequality

The main technical result of this file is the Grönwall-like inequality
`norm_le_gronwallBound_of_norm_deriv_right_le`. It states that if `f : ℝ → E` satisfies `‖f a‖ ≤ δ`
and `∀ x ∈ [a, b), ‖f' x‖ ≤ K * ‖f x‖ + ε`, then for all `x ∈ [a, b]` we have `‖f x‖ ≤ δ * exp (K *
x) + (ε / K) * (exp (K * x) - 1)`.

Then we use this inequality to prove some estimates on the possible rate of growth of the distance
between two approximate or exact solutions of an ordinary differential equation.

The proofs are based on [Hubbard and West, *Differential Equations: A Dynamical Systems Approach*,
Sec. 4.5][HubbardWest-ode], where `norm_le_gronwallBound_of_norm_deriv_right_le` is called
“Fundamental Inequality”.

## TODO

- Once we have FTC, prove an inequality for a function satisfying `‖f' x‖ ≤ K x * ‖f x‖ + ε`,
  or more generally `liminf_{y→x+0} (f y - f x)/(y - x) ≤ K x * f x + ε` with any sign
  of `K x` and `f x`.
-/

@[expose] public section

open Metric Set Asymptotics Filter Real
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-! ### Technical lemmas about `gronwallBound` -/


/--
Definition of `gronwallBound` / `gronwallBound` 的定义

English:
definition gronwallBound
  signature: (δ K ε x : Real)
  body: if K = 0 then δ + ε * x else δ * exp (K * x) + ε / K * (exp (K * x) - 1)

中文:
定义 gronwallBound
  签名: (δ K ε x : 实数)
  定义体: if K = 0 then δ + ε * x else δ * exp (K * x) + ε / K * (exp (K * x) - 1)
-/
noncomputable def gronwallBound (δ K ε x : Real) : Real :=
  if K = 0 then δ + ε * x else δ * exp (K * x) + ε / K * (exp (K * x) - 1)

/--
theorem `gronwallBound_K0` / 定理 `gronwallBound_K0`

English:
theorem gronwallBound_K0
  given: (δ ε : Real)
  statement: gronwallBound δ 0 ε = fun x => δ + ε * x
  proof: funext fun _ => if_pos rfl

中文:
定理 gronwallBound_K0
  条件: (δ ε : 实数)
  结论: gronwallBound δ 0 ε = fun x => δ + ε * x
  证明: funext fun _ => if_pos rfl

Depends on / 依赖: if_pos
-/
theorem gronwallBound_K0 (δ ε : Real) : gronwallBound δ 0 ε = fun x => δ + ε * x :=
  funext fun _ => if_pos rfl

/--
theorem `gronwallBound_of_K_ne_0` / 定理 `gronwallBound_of_K_ne_0`

English:
theorem gronwallBound_of_K_ne_0
  given: {δ K ε : Real} (hK : K != 0)
  proof: funext fun _ => if_neg hK

中文:
定理 gronwallBound_of_K_ne_0
  条件: {δ K ε : 实数} (hK : K != 0)
  证明: funext fun _ => if_neg hK

Depends on / 依赖: if_neg
-/
theorem gronwallBound_of_K_ne_0 {δ K ε : Real} (hK : K != 0) :
    gronwallBound δ K ε = fun x => δ * exp (K * x) + ε / K * (exp (K * x) - 1) :=
  funext fun _ => if_neg hK

/--
theorem `hasDerivAt_gronwallBound` / 定理 `hasDerivAt_gronwallBound`

English:
theorem hasDerivAt_gronwallBound
  given: (δ K ε x : Real)
  proof: by
  by_cases hK : K = 0
  · subst K
    simp only [gronwallBound_K0, zero_mul, zero_add]
    convert! ((hasDerivAt_id x).const_mul ε).const_add δ
    rw [mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK]
    convert!
      (((hasDerivAt_id x).const_mul K).exp.const_mul δ).add
        ((((hasDeriv

中文:
定理 hasDerivAt_gronwallBound
  条件: (δ K ε x : 实数)
  证明: by
  by_cases hK : K = 0
  · subst K
    simp only [gronwallBound_K0, zero_mul, zero_add]
    convert! ((hasDerivAt_id x).const_mul ε).const_add δ
    rw [mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK]
    convert!
      (((hasDerivAt_id x).const_mul K).exp.const_mul δ).add
        ((((hasDeriv

Depends on / 依赖: const_add, const_mul, convert, exp.const_mul, exp.sub_const, gronwallBound_K0, gronwallBound_of_K_ne_0, hasDerivAt_id, mul_one, sub_const, zero_add, zero_mul
-/
theorem hasDerivAt_gronwallBound (δ K ε x : Real) :
    HasDerivAt (gronwallBound δ K ε) (K * gronwallBound δ K ε x + ε) x := by
  by_cases hK : K = 0
  · subst K
    simp only [gronwallBound_K0, zero_mul, zero_add]
    convert! ((hasDerivAt_id x).const_mul ε).const_add δ
    rw [mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK]
    convert!
      (((hasDerivAt_id x).const_mul K).exp.const_mul δ).add
        ((((hasDerivAt_id x).const_mul K).exp.sub_const 1).const_mul (ε / K)) using 1
    simp only [id]
    field

/--
theorem `hasDerivAt_gronwallBound_shift` / 定理 `hasDerivAt_gronwallBound_shift`

English:
theorem hasDerivAt_gronwallBound_shift
  given: (δ K ε x a : Real)
  proof: by
  convert! (hasDerivAt_gronwallBound δ K ε _).comp x ((hasDerivAt_id x).sub_const a) using 1
  rw [id]; rw [mul_one]

中文:
定理 hasDerivAt_gronwallBound_shift
  条件: (δ K ε x a : 实数)
  证明: by
  convert! (hasDerivAt_gronwallBound δ K ε _).comp x ((hasDerivAt_id x).sub_const a) using 1
  rw [id]; rw [mul_one]

Depends on / 依赖: convert, hasDerivAt_gronwallBound, hasDerivAt_id, mul_one, sub_const
-/
theorem hasDerivAt_gronwallBound_shift (δ K ε x a : Real) :
    HasDerivAt (fun y => gronwallBound δ K ε (y - a)) (K * gronwallBound δ K ε (x - a) + ε) x := by
  convert! (hasDerivAt_gronwallBound δ K ε _).comp x ((hasDerivAt_id x).sub_const a) using 1
  rw [id]; rw [mul_one]

/--
theorem `gronwallBound_x0` / 定理 `gronwallBound_x0`

English:
theorem gronwallBound_x0
  given: (δ K ε : Real)
  statement: gronwallBound δ K ε 0 = δ
  proof: by
  by_cases hK : K = 0
  · simp only [gronwallBound, if_pos hK, mul_zero, add_zero]
  · simp only [gronwallBound, if_neg hK, mul_zero, exp_zero, sub_self, mul_one,
      add_zero]

中文:
定理 gronwallBound_x0
  条件: (δ K ε : 实数)
  结论: gronwallBound δ K ε 0 = δ
  证明: by
  by_cases hK : K = 0
  · simp only [gronwallBound, if_pos hK, mul_zero, add_zero]
  · simp only [gronwallBound, if_neg hK, mul_zero, exp_zero, sub_self, mul_one,
      add_zero]

Depends on / 依赖: add_zero, exp_zero, gronwallBound, if_neg, if_pos, mul_one, mul_zero, sub_self
-/
theorem gronwallBound_x0 (δ K ε : Real) : gronwallBound δ K ε 0 = δ := by
  by_cases hK : K = 0
  · simp only [gronwallBound, if_pos hK, mul_zero, add_zero]
  · simp only [gronwallBound, if_neg hK, mul_zero, exp_zero, sub_self, mul_one,
      add_zero]

/--
theorem `gronwallBound_ε0` / 定理 `gronwallBound_ε0`

English:
theorem gronwallBound_ε0
  given: (δ K x : Real)
  statement: gronwallBound δ K 0 x = δ * exp (K * x)
  proof: by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK, zero_mul, exp_zero, add_zero, mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK, zero_div, zero_mul, add_zero]

中文:
定理 gronwallBound_ε0
  条件: (δ K x : 实数)
  结论: gronwallBound δ K 0 x = δ * exp (K * x)
  证明: by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK, zero_mul, exp_zero, add_zero, mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK, zero_div, zero_mul, add_zero]

Depends on / 依赖: add_zero, exp_zero, gronwallBound_K0, gronwallBound_of_K_ne_0, mul_one, zero_div, zero_mul
-/
theorem gronwallBound_ε0 (δ K x : Real) : gronwallBound δ K 0 x = δ * exp (K * x) := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK, zero_mul, exp_zero, add_zero, mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK, zero_div, zero_mul, add_zero]

/--
theorem `gronwallBound_ε0_δ0` / 定理 `gronwallBound_ε0_δ0`

English:
theorem gronwallBound_ε0_δ0
  given: (K x : Real)
  statement: gronwallBound 0 K 0 x = 0
  proof: by
  simp only [gronwallBound_ε0, zero_mul]

中文:
定理 gronwallBound_ε0_δ0
  条件: (K x : 实数)
  结论: gronwallBound 0 K 0 x = 0
  证明: by
  simp only [gronwallBound_ε0, zero_mul]

Depends on / 依赖: zero_mul
-/
theorem gronwallBound_ε0_δ0 (K x : Real) : gronwallBound 0 K 0 x = 0 := by
  simp only [gronwallBound_ε0, zero_mul]

/--
theorem `gronwallBound_continuous_ε` / 定理 `gronwallBound_continuous_ε`

English:
theorem gronwallBound_continuous_ε
  given: (δ K x : Real)
  statement: Continuous fun ε => gronwallBound δ K ε x
  proof: by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK]
    fun_prop
  · simp only [gronwallBound_of_K_ne_0 hK]
    fun_prop

中文:
定理 gronwallBound_continuous_ε
  条件: (δ K x : 实数)
  结论: Continuous fun ε => gronwallBound δ K ε x
  证明: by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK]
    fun_prop
  · simp only [gronwallBound_of_K_ne_0 hK]
    fun_prop

Depends on / 依赖: fun_prop, gronwallBound_K0, gronwallBound_of_K_ne_0
-/
theorem gronwallBound_continuous_ε (δ K x : Real) : Continuous fun ε => gronwallBound δ K ε x := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK]
    fun_prop
  · simp only [gronwallBound_of_K_ne_0 hK]
    fun_prop

/--
lemma `gronwallBound_mono` / 引理 `gronwallBound_mono`

English:
lemma gronwallBound_mono
  given: {δ K ε : Real} (hδ : 0 <= δ) (hε : 0 <= ε) (hK : 0 <= K)
  proof: by
  intro x₁ x₂ hx
  unfold gronwallBound
  split_ifs with hK₀
  · gcongr
  · have hK_pos : 0 < K := by positivity
    gcongr

中文:
引理 gronwallBound_mono
  条件: {δ K ε : 实数} (hδ : 0 <= δ) (hε : 0 <= ε) (hK : 0 <= K)
  证明: by
  intro x₁ x₂ hx
  unfold gronwallBound
  split_ifs with hK₀
  · gcongr
  · have hK_pos : 0 < K := by positivity
    gcongr

Depends on / 依赖: gronwallBound, hK_pos, split_ifs
-/
lemma gronwallBound_mono {δ K ε : Real} (hδ : 0 <= δ) (hε : 0 <= ε) (hK : 0 <= K) :
    Monotone (gronwallBound δ K ε) := by
  intro x₁ x₂ hx
  unfold gronwallBound
  split_ifs with hK₀
  · gcongr
  · have hK_pos : 0 < K := by positivity
    gcongr

/-! ### Inequality and corollaries -/

/--
theorem `le_gronwallBound_of_liminf_deriv_right_le` / 定理 `le_gronwallBound_of_liminf_deriv_right_le`

English:
theorem le_gronwallBound_of_liminf_deriv_right_le
  statement: {f f' : Real -> Real} {δ K ε : Real} {a b : Real}
  proof: by
  have H : forall x in Icc a b, forall ε' in Ioi ε, f x <= gronwallBound δ K ε' (x - a) := by
    intro x hx ε' (hε' : ε < ε')
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hf'
    · rwa [sub_self, gronwallBound_x0]
    · exact fun x => hasDerivAt_gronwallBound_shift δ K ε' x a
  

中文:
定理 le_gronwallBound_of_liminf_deriv_right_le
  结论: {f f' : 实数 -> 实数} {δ K ε : 实数} {a b : 实数}
  证明: by
  have H : forall x in Icc a b, forall ε' in Ioi ε, f x <= gronwallBound δ K ε' (x - a) := by
    intro x hx ε' (hε' : ε < ε')
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hf'
    · rwa [sub_self, gronwallBound_x0]
    · exact fun x => hasDerivAt_gronwallBound_shift δ K ε' x a
  

Depends on / 依赖: closure_Ioi, closure_le, continuousWithinAt_const, continuousWithinAt_const.closure_le, convert, gronwallBound, gronwallBound_x0, hasDerivAt_gronwallBound_shift, image_le_of_liminf_slope_right_lt_deriv_boundary, self_mem_Ici, sub_self
-/
theorem le_gronwallBound_of_liminf_deriv_right_le {f f' : Real -> Real} {δ K ε : Real} {a b : Real}
    (hf : ContinuousOn f (Icc a b))
    (hf' : forall x in Ico a b, forall r, f' x < r -> existsᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r)
    (ha : f a <= δ) (bound : forall x in Ico a b, f' x <= K * f x + ε) :
    forall x in Icc a b, f x <= gronwallBound δ K ε (x - a) := by
  have H : forall x in Icc a b, forall ε' in Ioi ε, f x <= gronwallBound δ K ε' (x - a) := by
    intro x hx ε' (hε' : ε < ε')
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hf'
    · rwa [sub_self, gronwallBound_x0]
    · exact fun x => hasDerivAt_gronwallBound_shift δ K ε' x a
    · grind
    · exact hx
  intro x hx
  change f x <= (fun ε' => gronwallBound δ K ε' (x - a)) ε
  convert! continuousWithinAt_const.closure_le _ _ (H x hx)
  · simp only [closure_Ioi, self_mem_Ici]
  exact (gronwallBound_continuous_ε δ K (x - a)).continuousWithinAt

/--
theorem `norm_le_gronwallBound_of_norm_deriv_right_le` / 定理 `norm_le_gronwallBound_of_norm_deriv_right_le`

English:
theorem norm_le_gronwallBound_of_norm_deriv_right_le
  statement: {f f' : Real -> E} {δ K ε : Real} {a b : Real}
  proof: le_gronwallBound_of_liminf_deriv_right_le (continuous_norm.comp_continuousOn hf)
    (fun x hx _r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha bound

中文:
定理 norm_le_gronwallBound_of_norm_deriv_right_le
  结论: {f f' : 实数 -> E} {δ K ε : 实数} {a b : 实数}
  证明: le_gronwallBound_of_liminf_deriv_right_le (continuous_norm.comp_continuousOn hf)
    (fun x hx _r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha bound

Depends on / 依赖: comp_continuousOn, continuous_norm, continuous_norm.comp_continuousOn, le_gronwallBound_of_liminf_deriv_right_le, liminf_right_slope_norm_le
-/
theorem norm_le_gronwallBound_of_norm_deriv_right_le {f f' : Real -> E} {δ K ε : Real} {a b : Real}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : ‖f a‖ <= δ) (bound : forall x in Ico a b, ‖f' x‖ <= K * ‖f x‖ + ε) :
    forall x in Icc a b, ‖f x‖ <= gronwallBound δ K ε (x - a) :=
  le_gronwallBound_of_liminf_deriv_right_le (continuous_norm.comp_continuousOn hf)
    (fun x hx _r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha bound

/--
theorem `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` / 定理 `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`

English:
theorem eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
  statement: {f f' : Real -> E} {K a b : Real}
  proof: by
  intro x hx
  apply norm_le_zero_iff.mp
  calc ‖f x‖
    _ <= gronwallBound 0 K 0 (x - a) :=
      norm_le_gronwallBound_of_norm_deriv_right_le hf hf' (by simp [ha]) (by simpa using bound) _ hx
    _ = 0 := by rw [gronwallBound_ε0_δ0]

中文:
定理 eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
  结论: {f f' : 实数 -> E} {K a b : 实数}
  证明: by
  intro x hx
  apply norm_le_zero_iff.mp
  calc ‖f x‖
    _ <= gronwallBound 0 K 0 (x - a) :=
      norm_le_gronwallBound_of_norm_deriv_right_le hf hf' (by simp [ha]) (by simpa using bound) _ hx
    _ = 0 := by rw [gronwallBound_ε0_δ0]

Depends on / 依赖: gronwallBound, norm_le_gronwallBound_of_norm_deriv_right_le, norm_le_zero_iff, norm_le_zero_iff.mp
-/
theorem eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right {f f' : Real -> E} {K a b : Real}
    (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : f a = 0) (bound : forall x in Ico a b, ‖f' x‖ <= K * ‖f x‖) :
    forall x in Set.Icc a b, f x = 0 := by
  intro x hx
  apply norm_le_zero_iff.mp
  calc ‖f x‖
    _ <= gronwallBound 0 K 0 (x - a) :=
      norm_le_gronwallBound_of_norm_deriv_right_le hf hf' (by simp [ha]) (by simpa using bound) _ hx
    _ = 0 := by rw [gronwallBound_ε0_δ0]

variable {v : Real -> E -> E} {s : Real -> Set E} {K : Real>=0} {f g f' g' : Real -> E} {a b t₀ : Real} {εf εg δ : Real}

/--
theorem `dist_le_of_approx_trajectories_ODE_of_mem` / 定理 `dist_le_of_approx_trajectories_ODE_of_mem`

English:
theorem dist_le_of_approx_trajectories_ODE_of_mem
  proof: by
  simp only [dist_eq_norm] at ha ⊢
  have h_deriv : forall t in Ico a b, HasDerivWithinAt (fun t => f t - g t) (f' t - g' t) (Ici t) t :=
    fun t ht => (hf' t ht).sub (hg' t ht)
  apply norm_le_gronwallBound_of_norm_deriv_right_le (hf.fun_sub hg) h_deriv ha
  intro t ht
  have := dist_triangle4

中文:
定理 dist_le_of_approx_trajectories_ODE_of_mem
  证明: by
  simp only [dist_eq_norm] at ha ⊢
  have h_deriv : forall t in Ico a b, HasDerivWithinAt (fun t => f t - g t) (f' t - g' t) (Ici t) t :=
    fun t ht => (hf' t ht).sub (hg' t ht)
  apply norm_le_gronwallBound_of_norm_deriv_right_le (hf.fun_sub hg) h_deriv ha
  intro t ht
  have := dist_triangle4

Depends on / 依赖: HasDerivWithinAt, IsSplitEpi, IsSplitEpi.of_iso, dist_eq_norm, dist_le_mul, dist_triangle4_right, fun_sub, h_deriv, hf.fun_sub, norm_le_gronwallBound_of_norm_deriv_right_le, of_iso
-/
theorem dist_le_of_approx_trajectories_ODE_of_mem
    (hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : forall t in Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : forall t in Ico a b, dist (f' t) (v t (f t)) <= εf)
    (hfs : forall t in Ico a b, f t in s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : forall t in Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : forall t in Ico a b, dist (g' t) (v t (g t)) <= εg)
    (hgs : forall t in Ico a b, g t in s t)
    (ha : dist (f a) (g a) <= δ) :
    forall t in Icc a b, dist (f t) (g t) <= gronwallBound δ K (εf + εg) (t - a) := by
  simp only [dist_eq_norm] at ha ⊢
  have h_deriv : forall t in Ico a b, HasDerivWithinAt (fun t => f t - g t) (f' t - g' t) (Ici t) t :=
    fun t ht => (hf' t ht).sub (hg' t ht)
  apply norm_le_gronwallBound_of_norm_deriv_right_le (hf.fun_sub hg) h_deriv ha
  intro t ht
  have := dist_triangle4_right (f' t) (g' t) (v t (f t)) (v t (g t))
  have := (hv t ht).dist_le_mul _ (hfs t ht) _ (hgs t ht)
  grind [dist_eq_norm]

/--
theorem `dist_le_of_approx_trajectories_ODE` / 定理 `dist_le_of_approx_trajectories_ODE`

English:
theorem dist_le_of_approx_trajectories_ODE
  proof: have hfs : forall t in Ico a b, f t in @univ E := fun _ _ => trivial
  dist_le_of_approx_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf'
    f_bound hfs hg hg' g_bound (fun _ _ => trivial) ha

中文:
定理 dist_le_of_approx_trajectories_ODE
  证明: have hfs : forall t in Ico a b, f t in @univ E := fun _ _ => trivial
  dist_le_of_approx_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf'
    f_bound hfs hg hg' g_bound (fun _ _ => trivial) ha

Depends on / 依赖: dist_le_of_approx_trajectories_ODE_of_mem, f_bound, g_bound, lipschitzOnWith
-/
theorem dist_le_of_approx_trajectories_ODE
    (hv : forall t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : forall t in Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : forall t in Ico a b, dist (f' t) (v t (f t)) <= εf)
    (hg : ContinuousOn g (Icc a b))
    (hg' : forall t in Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : forall t in Ico a b, dist (g' t) (v t (g t)) <= εg)
    (ha : dist (f a) (g a) <= δ) :
    forall t in Icc a b, dist (f t) (g t) <= gronwallBound δ K (εf + εg) (t - a) :=
  have hfs : forall t in Ico a b, f t in @univ E := fun _ _ => trivial
  dist_le_of_approx_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf'
    f_bound hfs hg hg' g_bound (fun _ _ => trivial) ha

/--
theorem `dist_le_of_trajectories_ODE_of_mem` / 定理 `dist_le_of_trajectories_ODE_of_mem`

English:
theorem dist_le_of_trajectories_ODE_of_mem
  proof: by
  have f_bound : forall t in Ico a b, dist (v t (f t)) (v t (f t)) <= 0 := by intros; rw [dist_self]
  have g_bound : forall t in Ico a b, dist (v t (g t)) (v t (g t)) <= 0 := by intros; rw [dist_self]
  intro t ht
  have :=
    dist_le_of_approx_trajectories_ODE_of_mem hv hf hf' f_bound hfs hg h

中文:
定理 dist_le_of_trajectories_ODE_of_mem
  证明: by
  have f_bound : forall t in Ico a b, dist (v t (f t)) (v t (f t)) <= 0 := by intros; rw [dist_self]
  have g_bound : forall t in Ico a b, dist (v t (g t)) (v t (g t)) <= 0 := by intros; rw [dist_self]
  intro t ht
  have :=
    dist_le_of_approx_trajectories_ODE_of_mem hv hf hf' f_bound hfs hg h

Depends on / 依赖: IsSplitEpi, IsSplitEpi.epi, dist_le_of_approx_trajectories_ODE_of_mem, dist_self, f_bound, g_bound, intros, zero_add
-/
theorem dist_le_of_trajectories_ODE_of_mem
    (hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : forall t in Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hfs : forall t in Ico a b, f t in s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : forall t in Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : forall t in Ico a b, g t in s t) (ha : dist (f a) (g a) <= δ) :
    forall t in Icc a b, dist (f t) (g t) <= δ * exp (K * (t - a)) := by
  have f_bound : forall t in Ico a b, dist (v t (f t)) (v t (f t)) <= 0 := by intros; rw [dist_self]
  have g_bound : forall t in Ico a b, dist (v t (g t)) (v t (g t)) <= 0 := by intros; rw [dist_self]
  intro t ht
  have :=
    dist_le_of_approx_trajectories_ODE_of_mem hv hf hf' f_bound hfs hg hg' g_bound hgs ha t ht
  rwa [zero_add, gronwallBound_ε0] at this

/--
theorem `dist_le_of_trajectories_ODE` / 定理 `dist_le_of_trajectories_ODE`

English:
theorem dist_le_of_trajectories_ODE
  proof: have hfs : forall t in Ico a b, f t in @univ E := fun _ _ => trivial
  dist_le_of_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg
    hg' (fun _ _ => trivial) ha

中文:
定理 dist_le_of_trajectories_ODE
  证明: have hfs : forall t in Ico a b, f t in @univ E := fun _ _ => trivial
  dist_le_of_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg
    hg' (fun _ _ => trivial) ha

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, dist_le_of_trajectories_ODE_of_mem, exists_splitEpi, hf.exists_splitEpi.some.comp, hg.exists_splitEpi.some, lipschitzOnWith
-/
theorem dist_le_of_trajectories_ODE
    (hv : forall t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : forall t in Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : forall t in Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : dist (f a) (g a) <= δ) :
    forall t in Icc a b, dist (f t) (g t) <= δ * exp (K * (t - a)) :=
  have hfs : forall t in Ico a b, f t in @univ E := fun _ _ => trivial
  dist_le_of_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg
    hg' (fun _ _ => trivial) ha
