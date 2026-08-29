/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Liouville's theorem

In this file we prove Liouville's theorem: if `f : E → F` is complex differentiable on the whole
space and its range is bounded, then the function is a constant. Various versions of this theorem
are formalized in `Differentiable.apply_eq_apply_of_bounded`,
`Differentiable.exists_const_forall_eq_of_bounded`, and
`Differentiable.exists_eq_const_of_bounded`.

The proof is based on the Cauchy integral formula for the derivative of an analytic function, see
`Complex.deriv_eq_smul_circleIntegral`.
-/

public section

open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory Bornology

open scoped Topology Filter NNReal Real

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Complex E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace Complex F]

local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/--
theorem `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` / 定理 `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`

English:
theorem norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
  statement: [CompleteSpace F] {c : Complex} {R C : Real}
  proof: by
  have hp (z) (hz : z in sphere c R) : ‖(z - c)⁻¹ ^ (n + 1) • f z‖ <= C / (R ^ n * R) := by
    simpa [norm_smul, norm_pow, norm_inv, ← div_eq_inv_mul, mem_sphere_iff_norm.1 hz] using!
      (div_le_div_iff_of_pos_right (mul_pos (pow_pos hR n) hR)).2 (hC z hz)
  have hq : iteratedDeriv n f c = n.

中文:
定理 norm_iteratedDeriv_le_of_对任意_mem_sphere_norm_le
  结论: [完备空间 F] {c : 复形} {R C : 实数}
  证明: by
  have hp (z) (hz : z in sphere c R) : ‖(z - c)⁻¹ ^ (n + 1) • f z‖ <= C / (R ^ n * R) := by
    simpa [norm_smul, norm_pow, norm_inv, ← div_eq_inv_mul, mem_sphere_iff_norm.1 hz] using!
      (div_le_div_iff_of_pos_right (mul_pos (pow_pos hR n) hR)).2 (hC z hz)
  have hq : iteratedDeriv n f c = n.

Depends on / 依赖: Nat.factorial_ne_zero, div_eq_inv_mul, div_le_div_iff_of_pos_right, factorial, factorial_ne_zero, inv_div, iteratedDeriv, mem_sphere_iff_norm, mul_pos, n.factorial, norm_inv, norm_pow, norm_smul, pow_pos, sphere
-/
theorem norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le [CompleteSpace F] {c : Complex} {R C : Real}
    {f : Complex -> F} (n : Nat) (hR : 0 < R) (hf : DiffContOnCl Complex f (ball c R))
    (hC : forall z in sphere c R, ‖f z‖ <= C) :
    ‖iteratedDeriv n f c‖ <= n.factorial * C / R ^ n := by
  have hp (z) (hz : z in sphere c R) : ‖(z - c)⁻¹ ^ (n + 1) • f z‖ <= C / (R ^ n * R) := by
    simpa [norm_smul, norm_pow, norm_inv, ← div_eq_inv_mul, mem_sphere_iff_norm.1 hz] using!
      (div_le_div_iff_of_pos_right (mul_pos (pow_pos hR n) hR)).2 (hC z hz)
  have hq : iteratedDeriv n f c = n.factorial • (2 * π * I)⁻¹ •
    ∮ z in C(c, R), (z - c)⁻¹ ^ (n + 1) • f z := by
    have : (2 * π * I / n.factorial) != 0 := by simp [Nat.factorial_ne_zero]
    rw [← inv_smul_smul₀ this (iteratedDeriv n f c)]; rw [inv_div]; rw [div_eq_inv_mul]; rw [mul_comm]; rw [← nsmul_eq_mul]; rw [smul_assoc]
    simp [← DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul hR n hf]
  calc
    ‖iteratedDeriv n f c‖ = ‖n.factorial • (2 * π * I)⁻¹ •
      ∮ z in C(c, R), (z - c)⁻¹ ^ (n + 1) • f z‖ := by rw [hq]
    _ <= n.factorial * (R * (C / (R ^ (n + 1)))) := by
      rw [RCLike.norm_nsmul (K := Complex)]; rw [nsmul_eq_mul]; rw [mul_le_mul_iff_right₀ (by positivity)]
      exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hp
    _ = n.factorial * C / R ^ n := by
      grind

/--
theorem `norm_deriv_le_aux` / 定理 `norm_deriv_le_aux`

English:
theorem norm_deriv_le_aux
  statement: [CompleteSpace F] {c : Complex} {R C : Real} {f : Complex -> F} (hR : 0 < R)
  proof: by
  simpa using norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR hf hC

中文:
定理 norm_deriv_le_aux
  结论: [完备空间 F] {c : 复形} {R C : 实数} {f : 复形 -> F} (hR : 0 < R)
  证明: by
  simpa using norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR hf hC
-/
private theorem norm_deriv_le_aux [CompleteSpace F] {c : Complex} {R C : Real} {f : Complex -> F} (hR : 0 < R)
    (hf : DiffContOnCl Complex f (ball c R)) (hC : forall z in sphere c R, ‖f z‖ <= C) :
    ‖deriv f c‖ <= C / R := by
  simpa using norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR hf hC

/--
theorem `norm_deriv_le_of_forall_mem_sphere_norm_le` / 定理 `norm_deriv_le_of_forall_mem_sphere_norm_le`

English:
theorem norm_deriv_le_of_forall_mem_sphere_norm_le
  statement: {c : Complex} {R C : Real} {f : Complex -> F} (hR : 0 < R)
  proof: by
  set e : F ->L[Complex] F̂ := UniformSpace.Completion.toComplL
  have : HasDerivAt (e ∘ f) (e (deriv f c)) c :=
    e.hasFDerivAt.comp_hasDerivAt c
      (hd.differentiableAt isOpen_ball <| mem_ball_self hR).hasDerivAt
  calc
    ‖deriv f c‖ = ‖deriv (e ∘ f) c‖ := by
      rw [this.deriv]
      

中文:
定理 norm_deriv_le_of_对任意_mem_sphere_norm_le
  结论: {c : 复形} {R C : 实数} {f : 复形 -> F} (hR : 0 < R)
  证明: by
  set e : F ->L[Complex] F̂ := UniformSpace.Completion.toComplL
  have : HasDerivAt (e ∘ f) (e (deriv f c)) c :=
    e.hasFDerivAt.comp_hasDerivAt c
      (hd.differentiableAt isOpen_ball <| mem_ball_self hR).hasDerivAt
  calc
    ‖deriv f c‖ = ‖deriv (e ∘ f) c‖ := by
      rw [this.deriv]
      

Depends on / 依赖: Completion, HasDerivAt, UniformSpace, UniformSpace.Completion.norm_coe, UniformSpace.Completion.toComplL, comp_diffContOnCl, comp_hasDerivAt, differentiable, differentiableAt, e.differentiable.comp_diffContOnCl, e.hasFDerivAt.comp_hasDerivAt, hasDerivAt, hasFDerivAt, hd.differentiableAt, isOpen_ball, mem_ball_self, norm_coe, norm_deriv_le_aux, this.deriv, toComplL
-/
theorem norm_deriv_le_of_forall_mem_sphere_norm_le {c : Complex} {R C : Real} {f : Complex -> F} (hR : 0 < R)
    (hd : DiffContOnCl Complex f (ball c R)) (hC : forall z in sphere c R, ‖f z‖ <= C) :
    ‖deriv f c‖ <= C / R := by
  set e : F ->L[Complex] F̂ := UniformSpace.Completion.toComplL
  have : HasDerivAt (e ∘ f) (e (deriv f c)) c :=
    e.hasFDerivAt.comp_hasDerivAt c
      (hd.differentiableAt isOpen_ball <| mem_ball_self hR).hasDerivAt
  calc
    ‖deriv f c‖ = ‖deriv (e ∘ f) c‖ := by
      rw [this.deriv]
      exact (UniformSpace.Completion.norm_coe _).symm
    _ <= C / R :=
      norm_deriv_le_aux hR (e.differentiable.comp_diffContOnCl hd) fun z hz =>
        (UniformSpace.Completion.norm_coe _).trans_le (hC z hz)

/--
theorem `liouville_theorem_aux` / 定理 `liouville_theorem_aux`

English:
theorem liouville_theorem_aux
  statement: {f : Complex -> F} (hf : Differentiable Complex f) (hb : IsBounded (range f))
  proof: by
  suffices forall c, deriv f c = 0 from is_const_of_deriv_eq_zero hf this z w
  clear z w; intro c
  obtain ⟨C, C₀, hC⟩ : exists C > (0 : Real), forall z, ‖f z‖ <= C := by
    rcases isBounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩
    exact
      ⟨max C 1, lt_max_iff.2 (Or.inr zero_lt_one), fun z 

中文:
定理 liouville_theorem_aux
  结论: {f : 复形 -> F} (hf : 可微 复形 f) (hb : IsBounded (range f))
  证明: by
  suffices forall c, deriv f c = 0 from is_const_of_deriv_eq_zero hf this z w
  clear z w; intro c
  obtain ⟨C, C₀, hC⟩ : exists C > (0 : Real), forall z, ‖f z‖ <= C := by
    rcases isBounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩
    exact
      ⟨max C 1, lt_max_iff.2 (Or.inr zero_lt_one), fun z 

Depends on / 依赖: Or.inr, div_pos, isBounded_iff_forall_norm_le, is_const_of_deriv_eq_zero, le_max_left, le_of_forall_gt_imp_ge_of_dense, lt_max_iff, mem_range_self, norm_deriv_le_of_forall_mem_sphere_norm_le, norm_le_zero_iff, zero_lt_one
-/
theorem liouville_theorem_aux {f : Complex -> F} (hf : Differentiable Complex f) (hb : IsBounded (range f))
    (z w : Complex) : f z = f w := by
  suffices forall c, deriv f c = 0 from is_const_of_deriv_eq_zero hf this z w
  clear z w; intro c
  obtain ⟨C, C₀, hC⟩ : exists C > (0 : Real), forall z, ‖f z‖ <= C := by
    rcases isBounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩
    exact
      ⟨max C 1, lt_max_iff.2 (Or.inr zero_lt_one), fun z =>
        (hC (f z) (mem_range_self _)).trans (le_max_left _ _)⟩
  refine norm_le_zero_iff.1 (le_of_forall_gt_imp_ge_of_dense fun ε ε₀ => ?_)
  calc
    ‖deriv f c‖ <= C / (C / ε) :=
      norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.diffContOnCl fun z _ => hC z
    _ = ε := div_div_cancel₀ C₀.lt.ne'

end Complex

namespace Differentiable

open Complex

/--
theorem `apply_eq_apply_of_bounded` / 定理 `apply_eq_apply_of_bounded`

English:
theorem apply_eq_apply_of_bounded
  statement: {f : E -> F} (hf : Differentiable Complex f) (hb : IsBounded (range f))
  proof: by
  set g : Complex -> F := f ∘ fun t : Complex => t • (w - z) + z
  suffices g 0 = g 1 by simpa [g]
  apply liouville_theorem_aux
  exacts [hf.comp ((differentiable_id.smul_const (w - z)).add_const z),
    hb.subset (range_comp_subset_range _ _)]

中文:
定理 apply_eq_apply_of_bounded
  结论: {f : E -> F} (hf : 可微 复形 f) (hb : IsBounded (range f))
  证明: by
  set g : Complex -> F := f ∘ fun t : Complex => t • (w - z) + z
  suffices g 0 = g 1 by simpa [g]
  apply liouville_theorem_aux
  exacts [hf.comp ((differentiable_id.smul_const (w - z)).add_const z),
    hb.subset (range_comp_subset_range _ _)]

Depends on / 依赖: FunLike, FunLike.module, add_const, differentiable_id, differentiable_id.smul_const, exacts, fast_instance, hb.subset, hf.comp, liouville_theorem_aux, module, range_comp_subset_range, smul_const, subset
-/
theorem apply_eq_apply_of_bounded {f : E -> F} (hf : Differentiable Complex f) (hb : IsBounded (range f))
    (z w : E) : f z = f w := by
  set g : Complex -> F := f ∘ fun t : Complex => t • (w - z) + z
  suffices g 0 = g 1 by simpa [g]
  apply liouville_theorem_aux
  exacts [hf.comp ((differentiable_id.smul_const (w - z)).add_const z),
    hb.subset (range_comp_subset_range _ _)]

/--
theorem `exists_const_forall_eq_of_bounded` / 定理 `exists_const_forall_eq_of_bounded`

English:
theorem exists_const_forall_eq_of_bounded
  statement: {f : E -> F} (hf : Differentiable Complex f)
  proof: ⟨f 0, fun _ => hf.apply_eq_apply_of_bounded hb _ _⟩

中文:
定理 存在_const_对任意_eq_of_bounded
  结论: {f : E -> F} (hf : 可微 复形 f)
  证明: ⟨f 0, fun _ => hf.apply_eq_apply_of_bounded hb _ _⟩

Depends on / 依赖: apply_eq_apply_of_bounded, hf.apply_eq_apply_of_bounded
-/
theorem exists_const_forall_eq_of_bounded {f : E -> F} (hf : Differentiable Complex f)
    (hb : IsBounded (range f)) : exists c, forall z, f z = c :=
  ⟨f 0, fun _ => hf.apply_eq_apply_of_bounded hb _ _⟩

/--
theorem `exists_eq_const_of_bounded` / 定理 `exists_eq_const_of_bounded`

English:
theorem exists_eq_const_of_bounded
  statement: {f : E -> F} (hf : Differentiable Complex f)
  proof: (hf.exists_const_forall_eq_of_bounded hb).imp fun _ => funext

中文:
定理 存在_eq_const_of_bounded
  结论: {f : E -> F} (hf : 可微 复形 f)
  证明: (hf.exists_const_forall_eq_of_bounded hb).imp fun _ => funext

Depends on / 依赖: exists_const_forall_eq_of_bounded, hf.exists_const_forall_eq_of_bounded
-/
theorem exists_eq_const_of_bounded {f : E -> F} (hf : Differentiable Complex f)
    (hb : IsBounded (range f)) : exists c, f = const E c :=
  (hf.exists_const_forall_eq_of_bounded hb).imp fun _ => funext

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `eq_const_of_tendsto_cocompact` / 定理 `eq_const_of_tendsto_cocompact`

English:
theorem eq_const_of_tendsto_cocompact
  statement: [Nontrivial E] {f : E -> F} (hf : Differentiable Complex f) {c : F}
  proof: by
  have h_bdd : Bornology.IsBounded (Set.range f) := by
    obtain ⟨s, hs, hs_bdd⟩ := Metric.exists_isBounded_image_of_tendsto hb
    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
.subset .isBounded.union hs_bdd apply ht.image hf.continuous
simpa [Set.image_union, Set.image_univ] using! Set.image_mon

中文:
定理 eq_const_of_tendsto_cocompact
  结论: [非平凡 E] {f : E -> F} (hf : 可微 复形 f) {c : F}
  证明: by
  have h_bdd : Bornology.IsBounded (Set.range f) := by
    obtain ⟨s, hs, hs_bdd⟩ := Metric.exists_isBounded_image_of_tendsto hb
    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
.subset .isBounded.union hs_bdd apply ht.image hf.continuous
simpa [Set.image_union, Set.image_univ] using! Set.image_mon

Depends on / 依赖: Bornology, Bornology.IsBounded, IsBounded, Metric, Metric.exists_isBounded_image_of_tendsto, Set.image_mono, Set.image_union, Set.image_univ, Set.range, Set.univ, continuous, convert, exists_eq_const_of_bounded, exists_isBounded_image_of_tendsto, h_bdd, hf.continuous, hf.exists_eq_const_of_bounded, hs_bdd, ht.image, image_mono
-/
theorem eq_const_of_tendsto_cocompact [Nontrivial E] {f : E -> F} (hf : Differentiable Complex f) {c : F}
    (hb : Tendsto f (cocompact E) (𝓝 c)) : f = Function.const E c := by
  have h_bdd : Bornology.IsBounded (Set.range f) := by
    obtain ⟨s, hs, hs_bdd⟩ := Metric.exists_isBounded_image_of_tendsto hb
    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
.subset .isBounded.union hs_bdd apply ht.image hf.continuous
simpa [Set.image_union, Set.image_univ] using! Set.image_mono calc
      Set.univ = t union tᶜ := t.union_compl_self.symm
      _ subseteq t union s := by gcongr
  obtain ⟨c', hc'⟩ := hf.exists_eq_const_of_bounded h_bdd
  convert hc'
  exact tendsto_nhds_unique hb (by simpa [hc'] using! tendsto_const_nhds)

/--
theorem `apply_eq_of_tendsto_cocompact` / 定理 `apply_eq_of_tendsto_cocompact`

English:
theorem apply_eq_of_tendsto_cocompact
  statement: [Nontrivial E] {f : E -> F} (hf : Differentiable Complex f) {c : F}
  proof: congr($(hf.eq_const_of_tendsto_cocompact hb) x)

中文:
定理 apply_eq_of_tendsto_cocompact
  结论: [非平凡 E] {f : E -> F} (hf : 可微 复形 f) {c : F}
  证明: congr($(hf.eq_const_of_tendsto_cocompact hb) x)

Depends on / 依赖: eq_const_of_tendsto_cocompact, hf.eq_const_of_tendsto_cocompact
-/
theorem apply_eq_of_tendsto_cocompact [Nontrivial E] {f : E -> F} (hf : Differentiable Complex f) {c : F}
    (x : E) (hb : Tendsto f (cocompact E) (𝓝 c)) : f x = c :=
  congr($(hf.eq_const_of_tendsto_cocompact hb) x)

end Differentiable
