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
its values on the frontier of the set. All these lemmas assume that `E` is a nontrivial space. In
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

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Complex E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace Complex F]

local postfix:100 "̂" => UniformSpace.Completion

namespace Complex


/--
theorem `norm_max_aux₁` / 定理 `norm_max_aux₁`

English:
theorem norm_max_aux₁
  statement: [CompleteSpace F] {f : Complex -> F} {z w : Complex}
  proof: by
  -- Consider a circle of radius `r = dist w z`.
  set r : Real := dist w z
  have hw : w in closedBall z r := mem_closedBall.2 le_rfl
  -- Assume the converse. Since `‖f w‖ ≤ ‖f z‖`, we have `‖f w‖ < ‖f z‖`.
  refine (isMaxOn_iff.1 hz _ hw).antisymm (not_lt.1 ?_)
  rintro hw_lt : ‖f w‖ < ‖f z‖
 

中文:
定理 norm_max_aux₁
  结论: [完备空间 F] {f : 复形 -> F} {z w : 复形}
  证明: by
  -- Consider a circle of radius `r = dist w z`.
  set r : Real := dist w z
  have hw : w in closedBall z r := mem_closedBall.2 le_rfl
  -- Assume the converse. Since `‖f w‖ ≤ ‖f z‖`, we have `‖f w‖ < ‖f z‖`.
  refine (isMaxOn_iff.1 hz _ hw).antisymm (not_lt.1 ?_)
  rintro hw_lt : ‖f w‖ < ‖f z‖
 
-/
theorem norm_max_aux₁ [CompleteSpace F] {f : Complex -> F} {z w : Complex}
    (hd : DiffContOnCl Complex f (ball z (dist w z)))
    (hz : IsMaxOn (norm ∘ f) (closedBall z (dist w z)) z) : ‖f w‖ = ‖f z‖ := by
  -- Consider a circle of radius `r = dist w z`.
  set r : Real := dist w z
  have hw : w in closedBall z r := mem_closedBall.2 le_rfl
  -- Assume the converse. Since `‖f w‖ ≤ ‖f z‖`, we have `‖f w‖ < ‖f z‖`.
  refine (isMaxOn_iff.1 hz _ hw).antisymm (not_lt.1 ?_)
  rintro hw_lt : ‖f w‖ < ‖f z‖
  have hr : 0 < r := dist_pos.2 (ne_of_apply_ne (norm ∘ f) hw_lt.ne)
  -- Due to Cauchy integral formula, it suffices to prove the following inequality.
  suffices ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * ‖f z‖ by
    refine this.ne ?_
    have A : (∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ) = (2 * π * I : Complex) • f z :=
      hd.circleIntegral_sub_inv_smul (mem_ball_self hr)
    simp [A, norm_smul, Real.pi_pos.le]
  suffices ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * r * (‖f z‖ / r) by
    rwa [mul_assoc, mul_div_cancel₀ _ hr.ne'] at this
  /- This inequality is true because `‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r` for all `ζ` on the circle and
    this inequality is strict at `ζ = w`. -/
  have hsub : sphere z r subseteq closedBall z r := sphere_subset_closedBall
  refine circleIntegral.norm_integral_lt_of_norm_le_const_of_lt hr ?_ ?_ ⟨w, rfl, ?_⟩
  · show ContinuousOn (fun ζ : Complex => (ζ - z)⁻¹ • f ζ) (sphere z r)
    refine ((continuousOn_id.sub continuousOn_const).inv₀ ?_).smul (hd.continuousOn_ball.mono hsub)
    exact fun ζ hζ => sub_ne_zero.2 (ne_of_mem_sphere hζ hr.ne')
  · show forall ζ in sphere z r, ‖(ζ - z)⁻¹ • f ζ‖ <= ‖f z‖ / r
    rintro ζ hζ
    rw [le_div_iff₀ hr]; rw [norm_smul]; rw [norm_inv]; rw [mem_sphere_iff_norm.1 hζ]; rw [mul_comm]; rw [mul_inv_cancel_left₀ hr.ne']
    exact hz (hsub hζ)
  show ‖(w - z)⁻¹ • f w‖ < ‖f z‖ / r
  rw [norm_smul]; rw [norm_inv]; rw [← div_eq_inv_mul]; rw [← dist_eq_norm]
  exact (div_lt_div_iff_of_pos_right hr).2 hw_lt


/--
theorem `norm_max_aux₂` / 定理 `norm_max_aux₂`

English:
theorem norm_max_aux₂
  statement: {f : Complex -> F} {z w : Complex} (hd : DiffContOnCl Complex f (ball z (dist w z)))
  proof: by
  set e : F ->L[Complex] F̂ := UniformSpace.Completion.toComplL
  have he : forall x, ‖e x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
  replace hz : IsMaxOn (norm ∘ e ∘ f) (closedBall z (dist w z)) z := by
    simpa only [IsMaxOn, Function.comp_def, he] using hz
  simpa only [he, Function.comp_de

中文:
定理 norm_max_aux₂
  结论: {f : 复形 -> F} {z w : 复形} (hd : DiffContOnCl 复形 f (ball z (dist w z)))
  证明: by
  set e : F ->L[Complex] F̂ := UniformSpace.Completion.toComplL
  have he : forall x, ‖e x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
  replace hz : IsMaxOn (norm ∘ e ∘ f) (closedBall z (dist w z)) z := by
    simpa only [IsMaxOn, Function.comp_def, he] using hz
  simpa only [he, Function.comp_de

Depends on / 依赖: Completion, Function, Function.comp_def, IsMaxOn, UniformSpace, UniformSpace.Completion.norm_coe, UniformSpace.Completion.toComplL, closedBall, comp_def, comp_diffContOnCl, differentiable, e.differentiable.comp_diffContOnCl, norm_coe, replace, toComplL
-/
theorem norm_max_aux₂ {f : Complex -> F} {z w : Complex} (hd : DiffContOnCl Complex f (ball z (dist w z)))
    (hz : IsMaxOn (norm ∘ f) (closedBall z (dist w z)) z) : ‖f w‖ = ‖f z‖ := by
  set e : F ->L[Complex] F̂ := UniformSpace.Completion.toComplL
  have he : forall x, ‖e x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
  replace hz : IsMaxOn (norm ∘ e ∘ f) (closedBall z (dist w z)) z := by
    simpa only [IsMaxOn, Function.comp_def, he] using hz
  simpa only [he, Function.comp_def]
    using norm_max_aux₁ (e.differentiable.comp_diffContOnCl hd) hz


/--
theorem `norm_max_aux₃` / 定理 `norm_max_aux₃`

English:
theorem norm_max_aux₃
  statement: {f : Complex -> F} {z w : Complex} {r : Real} (hr : dist w z = r)
  proof: by
  subst r
  rcases eq_or_ne w z with (rfl | hne); · rfl
  rw [← dist_ne_zero] at hne
  exact norm_max_aux₂ hd (closure_ball z hne ▸ hz.closure hd.continuousOn.norm)

中文:
定理 norm_max_aux₃
  结论: {f : 复形 -> F} {z w : 复形} {r : 实数} (hr : dist w z = r)
  证明: by
  subst r
  rcases eq_or_ne w z with (rfl | hne); · rfl
  rw [← dist_ne_zero] at hne
  exact norm_max_aux₂ hd (closure_ball z hne ▸ hz.closure hd.continuousOn.norm)

Depends on / 依赖: closure, closure_ball, continuousOn, dist_ne_zero, eq_or_ne, hd.continuousOn.norm, hz.closure
-/
theorem norm_max_aux₃ {f : Complex -> F} {z w : Complex} {r : Real} (hr : dist w z = r)
    (hd : DiffContOnCl Complex f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) : ‖f w‖ = ‖f z‖ := by
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
/--
theorem `norm_eqOn_closedBall_of_isMaxOn` / 定理 `norm_eqOn_closedBall_of_isMaxOn`

English:
theorem norm_eqOn_closedBall_of_isMaxOn
  statement: {f : E -> F} {z : E} {r : Real}
  proof: by
  intro w hw
  rw [mem_closedBall]; rw [dist_comm] at hw
  rcases eq_or_ne z w with (rfl | hne); · rfl
  set e := (lineMap z w : Complex -> E)
  have hde : Differentiable Complex e := (differentiable_id.smul_const (w - z)).add_const z
  suffices ‖(f ∘ e) (1 : Complex)‖ = ‖(f ∘ e) (0 : Complex)‖ b

中文:
定理 norm_eqOn_closedBall_of_isMaxOn
  结论: {f : E -> F} {z : E} {r : 实数}
  证明: by
  intro w hw
  rw [mem_closedBall]; rw [dist_comm] at hw
  rcases eq_or_ne z w with (rfl | hne); · rfl
  set e := (lineMap z w : Complex -> E)
  have hde : Differentiable Complex e := (differentiable_id.smul_const (w - z)).add_const z
  suffices ‖(f ∘ e) (1 : Complex)‖ = ‖(f ∘ e) (0 : Complex)‖ b

Depends on / 依赖: Differentiable, MapsTo, Subset, Subset.rfl, add_const, differentiable_id, differentiable_id.smul_const, dist_comm, eq_or_ne, lineMap, lipschitzWith_lineMap, mapsTo_ball, mem_closedBall, nndist_eq_zero, smul_const
-/
theorem norm_eqOn_closedBall_of_isMaxOn {f : E -> F} {z : E} {r : Real}
    (hd : DiffContOnCl Complex f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn (norm ∘ f) (const E ‖f z‖) (closedBall z r) := by
  intro w hw
  rw [mem_closedBall]; rw [dist_comm] at hw
  rcases eq_or_ne z w with (rfl | hne); · rfl
  set e := (lineMap z w : Complex -> E)
  have hde : Differentiable Complex e := (differentiable_id.smul_const (w - z)).add_const z
  suffices ‖(f ∘ e) (1 : Complex)‖ = ‖(f ∘ e) (0 : Complex)‖ by simpa [e]
  have hr : dist (1 : Complex) 0 = 1 := by simp
  have hball : MapsTo e (ball 0 1) (ball z r) := by
    refine ((lipschitzWith_lineMap z w).mapsTo_ball (mt nndist_eq_zero.1 hne) 0 1).mono
      Subset.rfl ?_
    simpa only [lineMap_apply_zero, mul_one, coe_nndist] using ball_subset_ball hw
  exact norm_max_aux₃ hr (hd.comp hde.diffContOnCl hball)
      (hz.comp_mapsTo hball (lineMap_apply_zero z w))

/--
theorem `norm_eq_norm_of_isMaxOn_of_ball_subset` / 定理 `norm_eq_norm_of_isMaxOn_of_ball_subset`

English:
theorem norm_eq_norm_of_isMaxOn_of_ball_subset
  statement: {f : E -> F} {s : Set E} {z w : E}
  proof: norm_eqOn_closedBall_of_isMaxOn (hd.mono hsub) (hz.on_subset hsub) (mem_closedBall.2 le_rfl)

中文:
定理 norm_eq_norm_of_isMaxOn_of_ball_subset
  结论: {f : E -> F} {s : 集合 E} {z w : E}
  证明: norm_eqOn_closedBall_of_isMaxOn (hd.mono hsub) (hz.on_subset hsub) (mem_closedBall.2 le_rfl)

Depends on / 依赖: hd.mono, hz.on_subset, le_rfl, mem_closedBall, norm_eqOn_closedBall_of_isMaxOn, on_subset
-/
theorem norm_eq_norm_of_isMaxOn_of_ball_subset {f : E -> F} {s : Set E} {z w : E}
    (hd : DiffContOnCl Complex f s) (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) subseteq s) :
    ‖f w‖ = ‖f z‖ :=
  norm_eqOn_closedBall_of_isMaxOn (hd.mono hsub) (hz.on_subset hsub) (mem_closedBall.2 le_rfl)

/--
theorem `norm_eventually_eq_of_isLocalMax` / 定理 `norm_eventually_eq_of_isLocalMax`

English:
theorem norm_eventually_eq_of_isLocalMax
  statement: {f : E -> F} {c : E}
  proof: by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, norm_eqOn_closedBall_of_isMaxOn (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx

中文:
定理 norm_eventually_eq_of_isLocalMax
  结论: {f : E -> F} {c : E}
  证明: by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, norm_eqOn_closedBall_of_isMaxOn (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx

Depends on / 依赖: DifferentiableOn, DifferentiableOn.diffContOnCl, ball_subset_closedBall, closure_ball_subset_closedBall, diffContOnCl, differentiableWithinAt, eventually_iff, hd.and, nhds_basis_closedBall, nhds_basis_closedBall.eventually_iff, norm_eqOn_closedBall_of_isMaxOn
-/
theorem norm_eventually_eq_of_isLocalMax {f : E -> F} {c : E}
    (hd : forallᶠ z in 𝓝 c, DifferentiableAt Complex f z) (hc : IsLocalMax (norm ∘ f) c) :
    forallᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ := by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, norm_eqOn_closedBall_of_isMaxOn (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx =>
      (hr <| ball_subset_closedBall hx).2⟩

/--
theorem `isOpen_setOfPred_mem_nhds_and_isMaxOn_norm` / 定理 `isOpen_setOfPred_mem_nhds_and_isMaxOn_norm`

English:
theorem isOpen_setOfPred_mem_nhds_and_isMaxOn_norm
  statement: {f : E -> F} {s : Set E}
  proof: by
  refine isOpen_iff_mem_nhds.2 fun z hz => (eventually_eventually_nhds.2 hz.1).and ?_
  replace hd : forallᶠ w in 𝓝 z, DifferentiableAt Complex f w := hd.eventually_differentiableAt hz.1
  exact (norm_eventually_eq_of_isLocalMax hd <| hz.2.isLocalMax hz.1).mono fun x hx y hy =>
    le_trans (hz.2

中文:
定理 isOpen_setOfPred_mem_nhds_and_isMaxOn_norm
  结论: {f : E -> F} {s : 集合 E}
  证明: by
  refine isOpen_iff_mem_nhds.2 fun z hz => (eventually_eventually_nhds.2 hz.1).and ?_
  replace hd : forallᶠ w in 𝓝 z, DifferentiableAt Complex f w := hd.eventually_differentiableAt hz.1
  exact (norm_eventually_eq_of_isLocalMax hd <| hz.2.isLocalMax hz.1).mono fun x hx y hy =>
    le_trans (hz.2

Depends on / 依赖: DifferentiableAt, eventually_differentiableAt, eventually_eventually_nhds, hd.eventually_differentiableAt, hx.ge, isLocalMax, isOpen_iff_mem_nhds, le_trans, norm_eventually_eq_of_isLocalMax, replace
-/
theorem isOpen_setOfPred_mem_nhds_and_isMaxOn_norm {f : E -> F} {s : Set E}
    (hd : DifferentiableOn Complex f s) : IsOpen {z | s in 𝓝 z ∧ IsMaxOn (norm ∘ f) s z} := by
  refine isOpen_iff_mem_nhds.2 fun z hz => (eventually_eventually_nhds.2 hz.1).and ?_
  replace hd : forallᶠ w in 𝓝 z, DifferentiableAt Complex f w := hd.eventually_differentiableAt hz.1
  exact (norm_eventually_eq_of_isLocalMax hd <| hz.2.isLocalMax hz.1).mono fun x hx y hy =>
    le_trans (hz.2 hy).out hx.ge

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_mem_nhds_and_isMaxOn_norm := isOpen_setOfPred_mem_nhds_and_isMaxOn_norm

/--
theorem `norm_eqOn_of_isPreconnected_of_isMaxOn` / 定理 `norm_eqOn_of_isPreconnected_of_isMaxOn`

English:
theorem norm_eqOn_of_isPreconnected_of_isMaxOn
  statement: {f : E -> F} {U : Set E} {c : E}
  proof: by
  set V := U inter {z | IsMaxOn (norm ∘ f) U z}
  have hV : forall x in V, ‖f x‖ = ‖f c‖ := fun x hx => le_antisymm (hm hx.1) (hx.2 hcU)
  suffices U subseteq V from fun x hx => hV x (this hx)
  have hVo : IsOpen V := by
    simpa only [ho.mem_nhds_iff, ofPred_and, ofPred_mem_eq]
      using isOp

中文:
定理 norm_eqOn_of_isPreconnected_of_isMaxOn
  结论: {f : E -> F} {U : 集合 E} {c : E}
  证明: by
  set V := U inter {z | IsMaxOn (norm ∘ f) U z}
  have hV : forall x in V, ‖f x‖ = ‖f c‖ := fun x hx => le_antisymm (hm hx.1) (hx.2 hcU)
  suffices U subseteq V from fun x hx => hV x (this hx)
  have hVo : IsOpen V := by
    simpa only [ho.mem_nhds_iff, ofPred_and, ofPred_mem_eq]
      using isOp

Depends on / 依赖: IsMaxOn, IsOpen, Nonempty, continuousOn, hd.continuousOn.norm.isOpen_inter_preimage, ho.mem_nhds_iff, isOpen_inter_preimage, isOpen_ne, isOpen_setOfPred_mem_nhds_and_isMaxOn_norm, le_antisymm, mem_nhds_iff, ofPred_and, ofPred_mem_eq, subseteq
-/
theorem norm_eqOn_of_isPreconnected_of_isMaxOn {f : E -> F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn Complex f U) (hcU : c in U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) U := by
  set V := U inter {z | IsMaxOn (norm ∘ f) U z}
  have hV : forall x in V, ‖f x‖ = ‖f c‖ := fun x hx => le_antisymm (hm hx.1) (hx.2 hcU)
  suffices U subseteq V from fun x hx => hV x (this hx)
  have hVo : IsOpen V := by
    simpa only [ho.mem_nhds_iff, ofPred_and, ofPred_mem_eq]
      using isOpen_setOfPred_mem_nhds_and_isMaxOn_norm hd
  have hVne : (U inter V).Nonempty := ⟨c, hcU, hcU, hm⟩
  set W := U inter {z | ‖f z‖ != ‖f c‖}
  have hWo : IsOpen W := hd.continuousOn.norm.isOpen_inter_preimage ho isOpen_ne
  have hdVW : Disjoint V W := disjoint_left.mpr fun x hxV hxW => hxW.2 (hV x hxV)
  have hUVW : U subseteq V union W := fun x hx =>
    (eq_or_ne ‖f x‖ ‖f c‖).imp (fun h => ⟨hx, fun y hy => (hm hy).out.trans_eq h.symm⟩)
      (And.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne

/--
theorem `norm_eqOn_closure_of_isPreconnected_of_isMaxOn` / 定理 `norm_eqOn_closure_of_isPreconnected_of_isMaxOn`

English:
theorem norm_eqOn_closure_of_isPreconnected_of_isMaxOn
  statement: {f : E -> F} {U : Set E} {c : E}
  proof: (norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn.norm continuousOn_const subset_closure Subset.rfl

中文:
定理 norm_eqOn_closure_of_isPreconnected_of_isMaxOn
  结论: {f : E -> F} {U : 集合 E} {c : E}
  证明: (norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn.norm continuousOn_const subset_closure Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, continuousOn, continuousOn_const, differentiableOn, hd.continuousOn.norm, hd.differentiableOn, norm_eqOn_of_isPreconnected_of_isMaxOn, of_subset_closure, subset_closure
-/
theorem norm_eqOn_closure_of_isPreconnected_of_isMaxOn {f : E -> F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl Complex f U) (hcU : c in U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) (closure U) :=
  (norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn.norm continuousOn_const subset_closure Subset.rfl

section StrictConvex

/-!
### The case of a strictly convex codomain

If the codomain `F` is a strictly convex space, then we can claim equalities like `f w = f z`
instead of `‖f w‖ = ‖f z‖`.

Instead of repeating the proof starting with lemmas about integrals, we apply a corresponding lemma
above twice: for `f` and for `(f · + f c)`. Then we have `‖f w‖ = ‖f z‖` and
`‖f w + f z‖ = ‖f z + f z‖`, thus `‖f w + f z‖ = ‖f w‖ + ‖f z‖`. This is only possible if
`f w = f z`, see `eq_of_norm_eq_of_norm_add_eq`.
-/

variable [StrictConvexSpace Real F]

/--
theorem `eqOn_of_isPreconnected_of_isMaxOn_norm` / 定理 `eqOn_of_isPreconnected_of_isMaxOn_norm`

English:
theorem eqOn_of_isPreconnected_of_isMaxOn_norm
  statement: {f : E -> F} {U : Set E} {c : E}
  proof: fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd hcU hm hx
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hc ho (hd.add_const _) hcU hm.norm_add_self hx
eq_of_norm_eq_of_norm_add_eq H₁ by simp only [H₂, SameRay.rfl.norm_add

中文:
定理 eqOn_of_isPreconnected_of_isMaxOn_norm
  结论: {f : E -> F} {U : 集合 E} {c : E}
  证明: fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd hcU hm hx
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hc ho (hd.add_const _) hcU hm.norm_add_self hx
eq_of_norm_eq_of_norm_add_eq H₁ by simp only [H₂, SameRay.rfl.norm_add
-/
theorem eqOn_of_isPreconnected_of_isMaxOn_norm {f : E -> F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn Complex f U) (hcU : c in U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) U := fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd hcU hm hx
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hc ho (hd.add_const _) hcU hm.norm_add_self hx
eq_of_norm_eq_of_norm_add_eq H₁ by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]

/--
theorem `eqOn_closure_of_isPreconnected_of_isMaxOn_norm` / 定理 `eqOn_closure_of_isPreconnected_of_isMaxOn_norm`

English:
theorem eqOn_closure_of_isPreconnected_of_isMaxOn_norm
  statement: {f : E -> F} {U : Set E} {c : E}
  proof: (eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn continuousOn_const subset_closure Subset.rfl

中文:
定理 eqOn_closure_of_isPreconnected_of_isMaxOn_norm
  结论: {f : E -> F} {U : 集合 E} {c : E}
  证明: (eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn continuousOn_const subset_closure Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, continuousOn, continuousOn_const, differentiableOn, eqOn_of_isPreconnected_of_isMaxOn_norm, hd.continuousOn, hd.differentiableOn, of_subset_closure, subset_closure
-/
theorem eqOn_closure_of_isPreconnected_of_isMaxOn_norm {f : E -> F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl Complex f U) (hcU : c in U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) (closure U) :=
  (eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn continuousOn_const subset_closure Subset.rfl

/--
theorem `eq_of_isMaxOn_of_ball_subset` / 定理 `eq_of_isMaxOn_of_ball_subset`

English:
theorem eq_of_isMaxOn_of_ball_subset
  statement: {f : E -> F} {s : Set E} {z w : E} (hd : DiffContOnCl Complex f s)
  proof: have H₁ : ‖f w‖ = ‖f z‖ := norm_eq_norm_of_isMaxOn_of_ball_subset hd hz hsub
  have H₂ : ‖f w + f z‖ = ‖f z + f z‖ :=
    norm_eq_norm_of_isMaxOn_of_ball_subset (hd.add_const _) hz.norm_add_self hsub
eq_of_norm_eq_of_norm_add_eq H₁ by simp only [H₂, SameRay.rfl.norm_add, H₁]

中文:
定理 eq_of_isMaxOn_of_ball_subset
  结论: {f : E -> F} {s : 集合 E} {z w : E} (hd : DiffContOnCl 复形 f s)
  证明: have H₁ : ‖f w‖ = ‖f z‖ := norm_eq_norm_of_isMaxOn_of_ball_subset hd hz hsub
  have H₂ : ‖f w + f z‖ = ‖f z + f z‖ :=
    norm_eq_norm_of_isMaxOn_of_ball_subset (hd.add_const _) hz.norm_add_self hsub
eq_of_norm_eq_of_norm_add_eq H₁ by simp only [H₂, SameRay.rfl.norm_add, H₁]

Depends on / 依赖: SameRay, SameRay.rfl.norm_add, add_const, eq_of_norm_eq_of_norm_add_eq, hd.add_const, hz.norm_add_self, norm_add, norm_add_self, norm_eq_norm_of_isMaxOn_of_ball_subset
-/
theorem eq_of_isMaxOn_of_ball_subset {f : E -> F} {s : Set E} {z w : E} (hd : DiffContOnCl Complex f s)
    (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) subseteq s) : f w = f z :=
  have H₁ : ‖f w‖ = ‖f z‖ := norm_eq_norm_of_isMaxOn_of_ball_subset hd hz hsub
  have H₂ : ‖f w + f z‖ = ‖f z + f z‖ :=
    norm_eq_norm_of_isMaxOn_of_ball_subset (hd.add_const _) hz.norm_add_self hsub
eq_of_norm_eq_of_norm_add_eq H₁ by simp only [H₂, SameRay.rfl.norm_add, H₁]

/--
theorem `eqOn_closedBall_of_isMaxOn_norm` / 定理 `eqOn_closedBall_of_isMaxOn_norm`

English:
theorem eqOn_closedBall_of_isMaxOn_norm
  statement: {f : E -> F} {z : E} {r : Real}
  proof: fun _x hx =>
eq_of_isMaxOn_of_ball_subset hd hz ball_subset_ball hx

中文:
定理 eqOn_closedBall_of_isMaxOn_norm
  结论: {f : E -> F} {z : E} {r : 实数}
  证明: fun _x hx =>
eq_of_isMaxOn_of_ball_subset hd hz ball_subset_ball hx
-/
theorem eqOn_closedBall_of_isMaxOn_norm {f : E -> F} {z : E} {r : Real}
    (hd : DiffContOnCl Complex f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn f (const E (f z)) (closedBall z r) := fun _x hx =>
eq_of_isMaxOn_of_ball_subset hd hz ball_subset_ball hx

/--
lemma `eq_const_of_exists_max` / 引理 `eq_const_of_exists_max`

English:
lemma eq_const_of_exists_max
  statement: {f : E -> F} {b : Real} (h_an : DifferentiableOn Complex f (ball 0 b))
  proof: Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball 0 b).isPreconnected
    isOpen_ball h_an hv hv_max

中文:
引理 eq_const_of_存在_max
  结论: {f : E -> F} {b : 实数} (h_an : DifferentiableOn 复形 f (ball 0 b))
  证明: Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball 0 b).isPreconnected
    isOpen_ball h_an hv hv_max

Depends on / 依赖: Complex.eqOn_of_isPreconnected_of_isMaxOn_norm, convex_ball, eqOn_of_isPreconnected_of_isMaxOn_norm, h_an, hv_max, isOpen_ball, isPreconnected
-/
lemma eq_const_of_exists_max {f : E -> F} {b : Real} (h_an : DifferentiableOn Complex f (ball 0 b))
    {v : E} (hv : v in ball 0 b) (hv_max : IsMaxOn (norm ∘ f) (ball 0 b) v) :
    Set.EqOn f (Function.const E (f v)) (ball 0 b) :=
  Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball 0 b).isPreconnected
    isOpen_ball h_an hv hv_max

/--
lemma `eq_const_of_exists_le` / 引理 `eq_const_of_exists_le`

English:
lemma eq_const_of_exists_le
  statement: [ProperSpace E] {f : E -> F} {r b : Real}
  proof: by
.exists_isMaxOn obtain ⟨x, hx_mem, hx_max⟩ := isCompact_closedBall (0 : E) r
    (nonempty_closedBall.mpr hr_nn)
    (h_an.continuousOn.mono <| closedBall_subset_ball hr_lt).norm
  suffices Set.EqOn f (Function.const E (f x)) (ball 0 b) by
    rwa [this (mem_ball_self (hr_nn.trans_lt hr_lt))]
  a

中文:
引理 eq_const_of_存在_le
  结论: [真空间 E] {f : E -> F} {r b : 实数}
  证明: by
.exists_isMaxOn obtain ⟨x, hx_mem, hx_max⟩ := isCompact_closedBall (0 : E) r
    (nonempty_closedBall.mpr hr_nn)
    (h_an.continuousOn.mono <| closedBall_subset_ball hr_lt).norm
  suffices Set.EqOn f (Function.const E (f x)) (ball 0 b) by
    rwa [this (mem_ball_self (hr_nn.trans_lt hr_lt))]
  a

Depends on / 依赖: Function, Function.const, Set.EqOn, closedBall_subset_ball, continuousOn, eq_const_of_exists_max, exists_isMaxOn, h_an, h_an.continuousOn.mono, hr_lt, hr_nn, hr_nn.trans_lt, hx_max, hx_mem, isCompact_closedBall, mem_ball_self, nonempty_closedBall, nonempty_closedBall.mpr, trans_lt
-/
lemma eq_const_of_exists_le [ProperSpace E] {f : E -> F} {r b : Real}
    (h_an : DifferentiableOn Complex f (ball 0 b)) (hr_nn : 0 <= r) (hr_lt : r < b)
    (hr : forall z, z in (ball 0 b) -> exists w, w in closedBall 0 r ∧ ‖f z‖ <= ‖f w‖) :
    Set.EqOn f (Function.const E (f 0)) (ball 0 b) := by
.exists_isMaxOn obtain ⟨x, hx_mem, hx_max⟩ := isCompact_closedBall (0 : E) r
    (nonempty_closedBall.mpr hr_nn)
    (h_an.continuousOn.mono <| closedBall_subset_ball hr_lt).norm
  suffices Set.EqOn f (Function.const E (f x)) (ball 0 b) by
    rwa [this (mem_ball_self (hr_nn.trans_lt hr_lt))]
  apply eq_const_of_exists_max h_an (closedBall_subset_ball hr_lt hx_mem) (fun z hz => ?_)
  obtain ⟨w, hw, hw'⟩ := hr z hz
  exact hw'.trans (hx_max hw)

/--
theorem `eventually_eq_of_isLocalMax_norm` / 定理 `eventually_eq_of_isLocalMax_norm`

English:
theorem eventually_eq_of_isLocalMax_norm
  statement: {f : E -> F} {c : E}
  proof: by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, eqOn_closedBall_of_isMaxOn_norm (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx

中文:
定理 eventually_eq_of_isLocalMax_norm
  结论: {f : E -> F} {c : E}
  证明: by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, eqOn_closedBall_of_isMaxOn_norm (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx

Depends on / 依赖: DifferentiableOn, DifferentiableOn.diffContOnCl, ball_subset_closedBall, closure_ball_subset_closedBall, diffContOnCl, differentiableWithinAt, eqOn_closedBall_of_isMaxOn_norm, eventually_iff, hd.and, nhds_basis_closedBall, nhds_basis_closedBall.eventually_iff
-/
theorem eventually_eq_of_isLocalMax_norm {f : E -> F} {c : E}
    (hd : forallᶠ z in 𝓝 c, DifferentiableAt Complex f z) (hc : IsLocalMax (norm ∘ f) c) :
    forallᶠ y in 𝓝 c, f y = f c := by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, eqOn_closedBall_of_isMaxOn_norm (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx =>
      (hr <| ball_subset_closedBall hx).2⟩

/--
theorem `eventually_eq_or_eq_zero_of_isLocalMin_norm` / 定理 `eventually_eq_or_eq_zero_of_isLocalMin_norm`

English:
theorem eventually_eq_or_eq_zero_of_isLocalMin_norm
  statement: {f : E -> Complex} {c : E}
  proof: by
  refine or_iff_not_imp_right.mpr fun h => ?_
  have h1 : forallᶠ z in 𝓝 c, f z != 0 := hf.self_of_nhds.continuousAt.eventually_ne h
  have h2 : IsLocalMax (norm ∘ f)⁻¹ c := hc.inv (h1.mono fun z => norm_pos_iff.mpr)
  have h3 : IsLocalMax (norm ∘ f⁻¹) c := by refine h2.congr (Eventually.of_foral

中文:
定理 eventually_eq_or_eq_zero_of_isLocalMin_norm
  结论: {f : E -> 复形} {c : E}
  证明: by
  refine or_iff_not_imp_right.mpr fun h => ?_
  have h1 : forallᶠ z in 𝓝 c, f z != 0 := hf.self_of_nhds.continuousAt.eventually_ne h
  have h2 : IsLocalMax (norm ∘ f)⁻¹ c := hc.inv (h1.mono fun z => norm_pos_iff.mpr)
  have h3 : IsLocalMax (norm ∘ f⁻¹) c := by refine h2.congr (Eventually.of_foral

Depends on / 依赖: DifferentiableAt, Eventually, Eventually.of_forall, IsLocalMax, continuousAt, eventually_eq_of_isLocalMax_norm, eventually_ne, filter_upwards, h.inv, h1.mono, h2.congr, hc.inv, hf.self_of_nhds.continuousAt.eventually_ne, inv_inj, inv_inj.mp, norm_pos_iff, norm_pos_iff.mpr, of_forall, or_iff_not_imp_right, or_iff_not_imp_right.mpr
-/
theorem eventually_eq_or_eq_zero_of_isLocalMin_norm {f : E -> Complex} {c : E}
    (hf : forallᶠ z in 𝓝 c, DifferentiableAt Complex f z) (hc : IsLocalMin (norm ∘ f) c) :
    (forallᶠ z in 𝓝 c, f z = f c) ∨ f c = 0 := by
  refine or_iff_not_imp_right.mpr fun h => ?_
  have h1 : forallᶠ z in 𝓝 c, f z != 0 := hf.self_of_nhds.continuousAt.eventually_ne h
  have h2 : IsLocalMax (norm ∘ f)⁻¹ c := hc.inv (h1.mono fun z => norm_pos_iff.mpr)
  have h3 : IsLocalMax (norm ∘ f⁻¹) c := by refine h2.congr (Eventually.of_forall ?_); simp
  have h4 : forallᶠ z in 𝓝 c, DifferentiableAt Complex f⁻¹ z := by filter_upwards [hf, h1] with z h using h.inv
  filter_upwards [eventually_eq_of_isLocalMax_norm h4 h3] with z using inv_inj.mp

end StrictConvex

/-!
### Maximum on a set vs maximum on its frontier

In this section we prove corollaries of the maximum modulus principle that relate the values of a
function on a set to its values on the frontier of this set.
-/


variable [Nontrivial E]

/--
theorem `exists_mem_frontier_isMaxOn_norm` / 定理 `exists_mem_frontier_isMaxOn_norm`

English:
theorem exists_mem_frontier_isMaxOn_norm
  statement: [FiniteDimensional Complex E] {f : E -> F} {U : Set E}
  proof: by
  have hc : IsCompact (closure U) := hb.isCompact_closure
  obtain ⟨w, hwU, hle⟩ : exists w in closure U, IsMaxOn (norm ∘ f) (closure U) w :=
    hc.exists_isMaxOn hne.closure hd.continuousOn.norm
  rw [closure_eq_interior_union_frontier]; rw [mem_union] at hwU
  rcases hwU with hwU | hwU; rotate

中文:
定理 存在_mem_frontier_isMaxOn_norm
  结论: [有限维 复形 E] {f : E -> F} {U : 集合 E}
  证明: by
  have hc : IsCompact (closure U) := hb.isCompact_closure
  obtain ⟨w, hwU, hle⟩ : exists w in closure U, IsMaxOn (norm ∘ f) (closure U) w :=
    hc.exists_isMaxOn hne.closure hd.continuousOn.norm
  rw [closure_eq_interior_union_frontier]; rw [mem_union] at hwU
  rcases hwU with hwU | hwU; rotate

Depends on / 依赖: IsCompact, IsMaxOn, closure, closure_eq_interior_union_frontier, continuousOn, exists_isMaxOn, exists_mem_frontier_infDist_compl_eq_dist, frontier_in, hb.isCompact_closure, hc.exists_isMaxOn, hc.ne_univ, hd.continuousOn.norm, hne.closure, interior, interior_subset_closure, isCompact_closure, mem_union, ne_top_of_le_ne_top, ne_univ, rotate_left
-/
theorem exists_mem_frontier_isMaxOn_norm [FiniteDimensional Complex E] {f : E -> F} {U : Set E}
    (hb : IsBounded U) (hne : U.Nonempty) (hd : DiffContOnCl Complex f U) :
    exists z in frontier U, IsMaxOn (norm ∘ f) (closure U) z := by
  have hc : IsCompact (closure U) := hb.isCompact_closure
  obtain ⟨w, hwU, hle⟩ : exists w in closure U, IsMaxOn (norm ∘ f) (closure U) w :=
    hc.exists_isMaxOn hne.closure hd.continuousOn.norm
  rw [closure_eq_interior_union_frontier]; rw [mem_union] at hwU
  rcases hwU with hwU | hwU; rotate_left; · exact ⟨w, hwU, hle⟩
  have : interior U != univ := ne_top_of_le_ne_top hc.ne_univ interior_subset_closure
  rcases exists_mem_frontier_infDist_compl_eq_dist hwU this with ⟨z, hzU, hzw⟩
  refine ⟨z, frontier_interior_subset hzU, fun x hx => (hle hx).out.trans_eq ?_⟩
  refine (norm_eq_norm_of_isMaxOn_of_ball_subset hd (hle.on_subset subset_closure) ?_).symm
  rw [dist_comm]; rw [← hzw]
  exact ball_infDist_compl_subset.trans interior_subset

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `norm_le_of_forall_mem_frontier_norm_le` / 定理 `norm_le_of_forall_mem_frontier_norm_le`

English:
theorem norm_le_of_forall_mem_frontier_norm_le
  statement: {f : E -> F} {U : Set E} (hU : IsBounded U)
  proof: by
  rw [closure_eq_self_union_frontier]; rw [union_comm]; rw [mem_union] at hz
  rcases hz with hz | hz; · exact hC z hz
  /- In case of a finite-dimensional domain, one can just apply
    `Complex.exists_mem_frontier_isMaxOn_norm`. To make it work in any Banach space, we restrict
    the function 

中文:
定理 norm_le_of_对任意_mem_frontier_norm_le
  结论: {f : E -> F} {U : 集合 E} (hU : IsBounded U)
  证明: by
  rw [closure_eq_self_union_frontier]; rw [union_comm]; rw [mem_union] at hz
  rcases hz with hz | hz; · exact hC z hz
  /- In case of a finite-dimensional domain, one can just apply
    `Complex.exists_mem_frontier_isMaxOn_norm`. To make it work in any Banach space, we restrict
    the function 

Depends on / 依赖: closure_eq_self_union_frontier, mem_union, union_comm
-/
theorem norm_le_of_forall_mem_frontier_norm_le {f : E -> F} {U : Set E} (hU : IsBounded U)
    (hd : DiffContOnCl Complex f U) {C : Real} (hC : forall z in frontier U, ‖f z‖ <= C) {z : E}
    (hz : z in closure U) : ‖f z‖ <= C := by
  rw [closure_eq_self_union_frontier]; rw [union_comm]; rw [mem_union] at hz
  rcases hz with hz | hz; · exact hC z hz
  /- In case of a finite-dimensional domain, one can just apply
    `Complex.exists_mem_frontier_isMaxOn_norm`. To make it work in any Banach space, we restrict
    the function to a line first. -/
  rcases exists_ne z with ⟨w, hne⟩
  set e := (lineMap z w : Complex -> E)
  have hde : Differentiable Complex e := (differentiable_id.smul_const (w - z)).add_const z
  have hL : AntilipschitzWith (nndist z w)⁻¹ e := antilipschitzWith_lineMap hne.symm
  replace hd : DiffContOnCl Complex (f ∘ e) (e ⁻¹' U) :=
    hd.comp hde.diffContOnCl (mapsTo_preimage _ _)
  have h₀ : (0 : Complex) in e ⁻¹' U := by simpa only [e, mem_preimage, lineMap_apply_zero]
  rcases exists_mem_frontier_isMaxOn_norm (hL.isBounded_preimage hU) ⟨0, h₀⟩ hd with ⟨ζ, hζU, hζ⟩
  calc
    ‖f z‖ = ‖f (e 0)‖ := by simp only [e, lineMap_apply_zero]
    _ <= ‖f (e ζ)‖ := hζ (subset_closure h₀)
    _ <= C := hC _ (hde.continuous.frontier_preimage_subset _ hζU)

/--
theorem `eqOn_closure_of_eqOn_frontier` / 定理 `eqOn_closure_of_eqOn_frontier`

English:
theorem eqOn_closure_of_eqOn_frontier
  statement: {f g : E -> F} {U : Set E} (hU : IsBounded U)
  proof: by
  suffices H : forall z in closure U, ‖(f - g) z‖ <= 0 by simpa [sub_eq_zero] using! H
  refine fun z hz => norm_le_of_forall_mem_frontier_norm_le hU (hf.sub hg) (fun w hw => ?_) hz
  simp [hfg hw]

中文:
定理 eqOn_closure_of_eqOn_frontier
  结论: {f g : E -> F} {U : 集合 E} (hU : IsBounded U)
  证明: by
  suffices H : forall z in closure U, ‖(f - g) z‖ <= 0 by simpa [sub_eq_zero] using! H
  refine fun z hz => norm_le_of_forall_mem_frontier_norm_le hU (hf.sub hg) (fun w hw => ?_) hz
  simp [hfg hw]

Depends on / 依赖: closure, hf.sub, norm_le_of_forall_mem_frontier_norm_le, sub_eq_zero
-/
theorem eqOn_closure_of_eqOn_frontier {f g : E -> F} {U : Set E} (hU : IsBounded U)
    (hf : DiffContOnCl Complex f U) (hg : DiffContOnCl Complex g U) (hfg : EqOn f g (frontier U)) :
    EqOn f g (closure U) := by
  suffices H : forall z in closure U, ‖(f - g) z‖ <= 0 by simpa [sub_eq_zero] using! H
  refine fun z hz => norm_le_of_forall_mem_frontier_norm_le hU (hf.sub hg) (fun w hw => ?_) hz
  simp [hfg hw]

/--
theorem `eqOn_of_eqOn_frontier` / 定理 `eqOn_of_eqOn_frontier`

English:
theorem eqOn_of_eqOn_frontier
  statement: {f g : E -> F} {U : Set E} (hU : IsBounded U) (hf : DiffContOnCl Complex f U)
  proof: (eqOn_closure_of_eqOn_frontier hU hf hg hfg).mono subset_closure

中文:
定理 eqOn_of_eqOn_frontier
  结论: {f g : E -> F} {U : 集合 E} (hU : IsBounded U) (hf : DiffContOnCl 复形 f U)
  证明: (eqOn_closure_of_eqOn_frontier hU hf hg hfg).mono subset_closure

Depends on / 依赖: eqOn_closure_of_eqOn_frontier, subset_closure
-/
theorem eqOn_of_eqOn_frontier {f g : E -> F} {U : Set E} (hU : IsBounded U) (hf : DiffContOnCl Complex f U)
    (hg : DiffContOnCl Complex g U) (hfg : EqOn f g (frontier U)) : EqOn f g U :=
  (eqOn_closure_of_eqOn_frontier hU hf hg hfg).mono subset_closure

end Complex
