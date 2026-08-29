/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Tactic.Module

/-!
# Inner product space derived from a norm

This file defines an `InnerProductSpace` instance from a norm that respects the
parallelogram identity. The parallelogram identity is a way to express the inner product of `x` and
`y` in terms of the norms of `x`, `y`, `x + y`, `x - y`.

## Main results

- `InnerProductSpace.ofNorm`: a normed space whose norm respects the parallelogram identity,
  can be seen as an inner product space.

## Implementation notes

We define `inner_`

$$\langle x, y \rangle := \frac{1}{4} (‖x + y‖^2 - ‖x - y‖^2 + i ‖ix + y‖ ^ 2 - i ‖ix - y‖^2)$$

and use the parallelogram identity

$$‖x + y‖^2 + ‖x - y‖^2 = 2 (‖x‖^2 + ‖y‖^2)$$

to prove it is an inner product, i.e., that it is conjugate-symmetric (`inner_.conj_symm`) and
linear in the first argument. `add_left` is proved by judicious application of the parallelogram
identity followed by tedious arithmetic. `smul_left` is proved step by step, first noting that
$\langle λ x, y \rangle = λ \langle x, y \rangle$ for $λ ∈ ℕ$, $λ = -1$, hence $λ ∈ ℤ$ and $λ ∈ ℚ$
by arithmetic. Then by continuity and the fact that ℚ is dense in ℝ, the same is true for ℝ.
The case of ℂ then follows by applying the result for ℝ and more arithmetic.

## TODO

Move upstream to `Analysis.InnerProductSpace.Basic`.

## References

- [Jordan, P. and von Neumann, J., *On inner products in linear, metric spaces*][Jordan1935]
- https://math.stackexchange.com/questions/21792/norms-induced-by-inner-products-and-the-parallelogram-law
- https://math.dartmouth.edu/archive/m113w10/public_html/jordan-vneumann-thm.pdf

## Tags

inner product space, Hilbert space, norm
-/

@[expose] public section


open RCLike

open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]

/--
Definition of `InnerProductSpaceable` / `InnerProductSpaceable` 的定义

English:
class InnerProductSpaceable
  parameters: : Prop where
  axioms and operations (1):
    - parallelogram_identity : forall x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)

中文:
类 InnerProductSpaceable
  参数: : 命题 where
  公理与运算 (1 个):
    - parallelogram_identity : 对任意 x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)
-/
class InnerProductSpaceable : Prop where
  parallelogram_identity :
    forall x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)

variable (𝕜) {E}

/--
theorem `InnerProductSpace.toInnerProductSpaceable` / 定理 `InnerProductSpace.toInnerProductSpaceable`

English:
theorem InnerProductSpace.toInnerProductSpaceable
  given: [InnerProductSpace 𝕜 E]
  proof: ⟨parallelogram_law_with_norm_mul 𝕜⟩

中文:
定理 内积空间.toInnerProductSpaceable
  条件: [内积空间 𝕜 E]
  证明: ⟨parallelogram_law_with_norm_mul 𝕜⟩

Depends on / 依赖: parallelogram_law_with_norm_mul
-/
theorem InnerProductSpace.toInnerProductSpaceable [InnerProductSpace 𝕜 E] :
    InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm_mul 𝕜⟩

-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.toInnerProductSpaceable_ofReal
    [InnerProductSpace Real E] : InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm_mul Real⟩

variable [NormedSpace 𝕜 E]

local notation "𝓚" => algebraMap Real 𝕜

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def inner_ (x y : E)
  body: 4⁻¹ * (𝓚 ‖x + y‖ * 𝓚 ‖x + y‖ - 𝓚 ‖x - y‖ * 𝓚 ‖x - y‖ +
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x + y‖ * 𝓚 ‖(I : 𝕜) • x + y‖ -
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x - y‖ * 𝓚 ‖(I : 𝕜) • x - y‖)

中文:
定义 noncomputable
  签名: def inner_ (x y : E)
  定义体: 4⁻¹ * (𝓚 ‖x + y‖ * 𝓚 ‖x + y‖ - 𝓚 ‖x - y‖ * 𝓚 ‖x - y‖ +
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x + y‖ * 𝓚 ‖(I : 𝕜) • x + y‖ -
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x - y‖ * 𝓚 ‖(I : 𝕜) • x - y‖)
-/
private noncomputable def inner_ (x y : E) : 𝕜 :=
  4⁻¹ * (𝓚 ‖x + y‖ * 𝓚 ‖x + y‖ - 𝓚 ‖x - y‖ * 𝓚 ‖x - y‖ +
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x + y‖ * 𝓚 ‖(I : 𝕜) • x + y‖ -
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x - y‖ * 𝓚 ‖(I : 𝕜) • x - y‖)

namespace InnerProductSpaceable

variable {𝕜} (E)

set_option backward.privateInPublic true in
-- This has a prime added to avoid clashing with public `innerProp`
/--
Definition of `innerProp'` / `innerProp'` 的定义

English:
definition innerProp'
  signature: (r : 𝕜)
  body: forall x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y

中文:
定义 innerProp'
  签名: (r : 𝕜)
  定义体: forall x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y
-/
private def innerProp' (r : 𝕜) : Prop :=
  forall x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y

variable {E}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `_root_.Continuous.inner_` / 定理 `_root_.Continuous.inner_`

English:
theorem _root_.Continuous.inner_
  given: {f g : Real -> E} (hf : Continuous f) (hg : Continuous g)
  proof: by
  unfold _root_.inner_
  fun_prop

中文:
定理 _root_.连续.inner_
  条件: {f g : 实数 -> E} (hf : 连续 f) (hg : 连续 g)
  证明: by
  unfold _root_.inner_
  fun_prop

Depends on / 依赖: _root_, _root_.inner_, fun_prop, inner_
-/
theorem _root_.Continuous.inner_ {f g : Real -> E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => inner_ 𝕜 (f x) (g x) := by
  unfold _root_.inner_
  fun_prop

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `inner_.norm_sq` / 定理 `inner_.norm_sq`

English:
theorem inner_.norm_sq
  given: (x : E)
  statement: ‖x‖ ^ 2 = re (inner_ 𝕜 x x)
  proof: by
  simp only [inner_, normSq_apply, ofNat_re, ofNat_im, map_sub, map_add,
    ofReal_re, ofReal_im, mul_re, inv_re, mul_im, I_re, inv_im]
  have h₁ : ‖x - x‖ = 0 := by simp
  have h₂ : ‖x + x‖ = 2 • ‖x‖ := by convert norm_nsmul 𝕜 2 x; module
  rw [h₁]; rw [h₂]
  ring

中文:
定理 inner_.norm_sq
  条件: (x : E)
  结论: ‖x‖ ^ 2 = re (inner_ 𝕜 x x)
  证明: by
  simp only [inner_, normSq_apply, ofNat_re, ofNat_im, map_sub, map_add,
    ofReal_re, ofReal_im, mul_re, inv_re, mul_im, I_re, inv_im]
  have h₁ : ‖x - x‖ = 0 := by simp
  have h₂ : ‖x + x‖ = 2 • ‖x‖ := by convert norm_nsmul 𝕜 2 x; module
  rw [h₁]; rw [h₂]
  ring

Depends on / 依赖: I_re, convert, inner_, inv_im, inv_re, map_add, map_sub, module, mul_im, mul_re, normSq_apply, norm_nsmul, ofNat_im, ofNat_re, ofReal_im, ofReal_re
-/
theorem inner_.norm_sq (x : E) : ‖x‖ ^ 2 = re (inner_ 𝕜 x x) := by
  simp only [inner_, normSq_apply, ofNat_re, ofNat_im, map_sub, map_add,
    ofReal_re, ofReal_im, mul_re, inv_re, mul_im, I_re, inv_im]
  have h₁ : ‖x - x‖ = 0 := by simp
  have h₂ : ‖x + x‖ = 2 • ‖x‖ := by convert norm_nsmul 𝕜 2 x; module
  rw [h₁]; rw [h₂]
  ring

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `inner_.conj_symm` / 定理 `inner_.conj_symm`

English:
theorem inner_.conj_symm
  given: (x y : E)
  statement: conj (inner_ 𝕜 y x) = inner_ 𝕜 x y
  proof: by
  simp only [inner_, map_sub, map_add, map_mul, map_inv₀, map_ofNat, conj_ofReal, conj_I]
  rw [add_comm y x]; rw [norm_sub_rev]
  by_cases hI : (I : 𝕜) = 0
  · simp only [hI, neg_zero, zero_mul]
  have hI' := I_mul_I_of_nonzero hI
  have I_smul (v : E) : ‖(I : 𝕜) • v‖ = ‖v‖ := by rw [norm_smul, norm_I_of_ne_zero hI, one_mul]
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖ := by
    convert I_smul ((I : 𝕜) • x + y)
    linear_combination (norm := module) -hI' • x
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖ := by
    convert (I_smul ((I : 𝕜) • y + x)).symm
    linear_combination (norm := module) -hI' • y
  rw [h₁]; rw [h₂]
  ring

中文:
定理 inner_.conj_symm
  条件: (x y : E)
  结论: conj (inner_ 𝕜 y x) = inner_ 𝕜 x y
  证明: by
  simp only [inner_, map_sub, map_add, map_mul, map_inv₀, map_ofNat, conj_ofReal, conj_I]
  rw [add_comm y x]; rw [norm_sub_rev]
  by_cases hI : (I : 𝕜) = 0
  · simp only [hI, neg_zero, zero_mul]
  have hI' := I_mul_I_of_nonzero hI
  have I_smul (v : E) : ‖(I : 𝕜) • v‖ = ‖v‖ := by rw [norm_smul, norm_I_of_ne_zero hI, one_mul]
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖ := by
    convert I_smul ((I : 𝕜) • x + y)
    linear_combination (norm := module) -hI' • x
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖ := by
    convert (I_smul ((I : 𝕜) • y + x)).symm
    linear_combination (norm := module) -hI' • y
  rw [h₁]; rw [h₂]
  ring

Depends on / 依赖: I_mul_I_of_nonzero, I_smul, add_comm, conj_I, conj_ofReal, convert, inner_, linear_combination, map_add, map_mul, map_ofNat, map_sub, module, neg_zero, norm_I_of_ne_zero, norm_smul, norm_sub_rev, one_mul, zero_mul
-/
theorem inner_.conj_symm (x y : E) : conj (inner_ 𝕜 y x) = inner_ 𝕜 x y := by
  simp only [inner_, map_sub, map_add, map_mul, map_inv₀, map_ofNat, conj_ofReal, conj_I]
  rw [add_comm y x]; rw [norm_sub_rev]
  by_cases hI : (I : 𝕜) = 0
  · simp only [hI, neg_zero, zero_mul]
  have hI' := I_mul_I_of_nonzero hI
  have I_smul (v : E) : ‖(I : 𝕜) • v‖ = ‖v‖ := by rw [norm_smul, norm_I_of_ne_zero hI, one_mul]
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖ := by
    convert I_smul ((I : 𝕜) • x + y)
    linear_combination (norm := module) -hI' • x
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖ := by
    convert (I_smul ((I : 𝕜) • y + x)).symm
    linear_combination (norm := module) -hI' • y
  rw [h₁]; rw [h₂]
  ring

variable [InnerProductSpaceable E]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: (x y z : E)
  statement: inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z
  proof: by
  unfold inner_
  have h1 := parallelogram_identity (x + y + z) (x - z)
  have h2 := parallelogram_identity (x + y - z) (x + z)
  have h3 := parallelogram_identity (y + z) z
  have h4 := parallelogram_identity (y - z) z
  have h5 := parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z)
  have h6 := parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z)
  have h7 := parallelogram_identity ((I : 𝕜) • y + z) z
  have h8 := parallelogram_identity ((I : 𝕜) • y - z) z
  apply_fun 𝓚 at h1 h2 h3 h4 h5 h6 h7 h8
  simp only [map_add, map_mul, map_ofNat, smul_add] at *
  abel_nf at * -- TODO this should be `module_nf` (then the `smul_add` above can go)
  linear_combination (- h1 + h2 + h3 - h4 + I * (- h5 + h6 + h7 - h8)) / 8

中文:
定理 add_left
  条件: (x y z : E)
  结论: inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z
  证明: by
  unfold inner_
  have h1 := parallelogram_identity (x + y + z) (x - z)
  have h2 := parallelogram_identity (x + y - z) (x + z)
  have h3 := parallelogram_identity (y + z) z
  have h4 := parallelogram_identity (y - z) z
  have h5 := parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z)
  have h6 := parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z)
  have h7 := parallelogram_identity ((I : 𝕜) • y + z) z
  have h8 := parallelogram_identity ((I : 𝕜) • y - z) z
  apply_fun 𝓚 at h1 h2 h3 h4 h5 h6 h7 h8
  simp only [map_add, map_mul, map_ofNat, smul_add] at *
  abel_nf at * -- TODO this should be `module_nf` (then the `smul_add` above can go)
  linear_combination (- h1 + h2 + h3 - h4 + I * (- h5 + h6 + h7 - h8)) / 8

Depends on / 依赖: apply_fun, inner_, parallelogram_identity
-/
theorem add_left (x y z : E) : inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z := by
  unfold inner_
  have h1 := parallelogram_identity (x + y + z) (x - z)
  have h2 := parallelogram_identity (x + y - z) (x + z)
  have h3 := parallelogram_identity (y + z) z
  have h4 := parallelogram_identity (y - z) z
  have h5 := parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z)
  have h6 := parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z)
  have h7 := parallelogram_identity ((I : 𝕜) • y + z) z
  have h8 := parallelogram_identity ((I : 𝕜) • y - z) z
  apply_fun 𝓚 at h1 h2 h3 h4 h5 h6 h7 h8
  simp only [map_add, map_mul, map_ofNat, smul_add] at *
  abel_nf at * -- TODO this should be `module_nf` (then the `smul_add` above can go)
  linear_combination (- h1 + h2 + h3 - h4 + I * (- h5 + h6 + h7 - h8)) / 8

/--
theorem `rat_prop` / 定理 `rat_prop`

English:
theorem rat_prop
  given: (r : Rat)
  statement: innerProp' E (r : 𝕜)
  proof: by
  intro x y
let hom : 𝕜 ->ₗ[Rat] 𝕜 := AddMonoidHom.toRatLinearMap
AddMonoidHom.mk' (fun r => inner_ 𝕜 (r • x) y) fun a b => by
      simpa [add_smul] using add_left (a • x) (b • x) y
  simpa [hom, Rat.smul_def] using map_smul hom r 1

中文:
定理 rat_prop
  条件: (r : 有理数)
  结论: innerProp' E (r : 𝕜)
  证明: by
  intro x y
let hom : 𝕜 ->ₗ[Rat] 𝕜 := AddMonoidHom.toRatLinearMap
AddMonoidHom.mk' (fun r => inner_ 𝕜 (r • x) y) fun a b => by
      simpa [add_smul] using add_left (a • x) (b • x) y
  simpa [hom, Rat.smul_def] using map_smul hom r 1
-/
private theorem rat_prop (r : Rat) : innerProp' E (r : 𝕜) := by
  intro x y
let hom : 𝕜 ->ₗ[Rat] 𝕜 := AddMonoidHom.toRatLinearMap
AddMonoidHom.mk' (fun r => inner_ 𝕜 (r • x) y) fun a b => by
      simpa [add_smul] using add_left (a • x) (b • x) y
  simpa [hom, Rat.smul_def] using map_smul hom r 1

/--
theorem `real_prop` / 定理 `real_prop`

English:
theorem real_prop
  given: (r : Real)
  statement: innerProp' E (r : 𝕜)
  proof: by
  intro x y
  revert r
  rw [← funext_iff]
  refine Rat.isDenseEmbedding_coe_real.dense.equalizer ?_ ?_ (funext fun X => ?_)
  · exact (continuous_ofReal.smul continuous_const).inner_ continuous_const
  · exact (continuous_conj.comp continuous_ofReal).mul continuous_const
  · simp only [Function.comp_apply, RCLike.ofReal_ratCast, rat_prop _ _]

中文:
定理 real_prop
  条件: (r : 实数)
  结论: innerProp' E (r : 𝕜)
  证明: by
  intro x y
  revert r
  rw [← funext_iff]
  refine Rat.isDenseEmbedding_coe_real.dense.equalizer ?_ ?_ (funext fun X => ?_)
  · exact (continuous_ofReal.smul continuous_const).inner_ continuous_const
  · exact (continuous_conj.comp continuous_ofReal).mul continuous_const
  · simp only [Function.comp_apply, RCLike.ofReal_ratCast, rat_prop _ _]
-/
private theorem real_prop (r : Real) : innerProp' E (r : 𝕜) := by
  intro x y
  revert r
  rw [← funext_iff]
  refine Rat.isDenseEmbedding_coe_real.dense.equalizer ?_ ?_ (funext fun X => ?_)
  · exact (continuous_ofReal.smul continuous_const).inner_ continuous_const
  · exact (continuous_conj.comp continuous_ofReal).mul continuous_const
  · simp only [Function.comp_apply, RCLike.ofReal_ratCast, rat_prop _ _]

/--
theorem `I_prop` / 定理 `I_prop`

English:
theorem I_prop
  statement: innerProp' E (I : 𝕜)
  proof: by
  by_cases hI : (I : 𝕜) = 0
  · rw [hI]
    simpa using real_prop (𝕜 := 𝕜) 0
  intro x y
  have hI' := I_mul_I_of_nonzero hI
  rw [conj_I]; rw [inner_]; rw [inner_]; rw [mul_left_comm]; rw [smul_smul]; rw [hI']; rw [neg_one_smul]
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  rw [h₁]; rw [h₂]
  linear_combination (- 𝓚 ‖(I : 𝕜) • x - y‖ ^ 2 + 𝓚 ‖(I : 𝕜) • x + y‖ ^ 2) * hI' / 4

中文:
定理 I_prop
  结论: innerProp' E (I : 𝕜)
  证明: by
  by_cases hI : (I : 𝕜) = 0
  · rw [hI]
    simpa using real_prop (𝕜 := 𝕜) 0
  intro x y
  have hI' := I_mul_I_of_nonzero hI
  rw [conj_I]; rw [inner_]; rw [inner_]; rw [mul_left_comm]; rw [smul_smul]; rw [hI']; rw [neg_one_smul]
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  rw [h₁]; rw [h₂]
  linear_combination (- 𝓚 ‖(I : 𝕜) • x - y‖ ^ 2 + 𝓚 ‖(I : 𝕜) • x + y‖ ^ 2) * hI' / 4
-/
private theorem I_prop : innerProp' E (I : 𝕜) := by
  by_cases hI : (I : 𝕜) = 0
  · rw [hI]
    simpa using real_prop (𝕜 := 𝕜) 0
  intro x y
  have hI' := I_mul_I_of_nonzero hI
  rw [conj_I]; rw [inner_]; rw [inner_]; rw [mul_left_comm]; rw [smul_smul]; rw [hI']; rw [neg_one_smul]
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  rw [h₁]; rw [h₂]
  linear_combination (- 𝓚 ‖(I : 𝕜) • x - y‖ ^ 2 + 𝓚 ‖(I : 𝕜) • x + y‖ ^ 2) * hI' / 4

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `innerProp` / 定理 `innerProp`

English:
theorem innerProp
  given: (r : 𝕜)
  statement: innerProp' E r
  proof: by
  intro x y
  rw [← re_add_im r]; rw [add_smul]; rw [add_left]; rw [real_prop _ x]; rw [← smul_smul]; rw [real_prop _ _ y]; rw [I_prop]; rw [map_add]; rw [map_mul]; rw [conj_ofReal]; rw [conj_ofReal]; rw [conj_I]
  ring

中文:
定理 innerProp
  条件: (r : 𝕜)
  结论: innerProp' E r
  证明: by
  intro x y
  rw [← re_add_im r]; rw [add_smul]; rw [add_left]; rw [real_prop _ x]; rw [← smul_smul]; rw [real_prop _ _ y]; rw [I_prop]; rw [map_add]; rw [map_mul]; rw [conj_ofReal]; rw [conj_ofReal]; rw [conj_I]
  ring

Depends on / 依赖: I_prop, add_left, add_smul, conj_I, conj_ofReal, map_add, map_mul, re_add_im, real_prop, smul_smul
-/
theorem innerProp (r : 𝕜) : innerProp' E r := by
  intro x y
  rw [← re_add_im r]; rw [add_smul]; rw [add_left]; rw [real_prop _ x]; rw [← smul_smul]; rw [real_prop _ _ y]; rw [I_prop]; rw [map_add]; rw [map_mul]; rw [conj_ofReal]; rw [conj_ofReal]; rw [conj_I]
  ring

end InnerProductSpaceable

open InnerProductSpaceable

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. -/
@[instance_reducible]
/--
Definition of `InnerProductSpace.ofNorm` / `InnerProductSpace.ofNorm` 的定义

English:
definition InnerProductSpace.ofNorm
  body: haveI : InnerProductSpaceable E := ⟨h⟩
  { inner := inner_ 𝕜
    norm_sq_eq_re_inner := inner_.norm_sq
    conj_inner_symm := inner_.conj_symm
    add_left := InnerProductSpaceable.add_left
    smul_left := fun _ _ _ => innerProp _ _ _ }

中文:
定义 内积空间.ofNorm
  定义体: haveI : InnerProductSpaceable E := ⟨h⟩
  { inner := inner_ 𝕜
    norm_sq_eq_re_inner := inner_.norm_sq
    conj_inner_symm := inner_.conj_symm
    add_left := InnerProductSpaceable.add_left
    smul_left := fun _ _ _ => innerProp _ _ _ }

Depends on / 依赖: InnerProductSpaceable, InnerProductSpaceable.add_left, add_left, conj_inner_symm, conj_symm, innerProp, inner_, inner_.conj_symm, inner_.norm_sq, norm_sq, norm_sq_eq_re_inner, smul_left
-/
noncomputable def InnerProductSpace.ofNorm
    (h : forall x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    InnerProductSpace 𝕜 E :=
  haveI : InnerProductSpaceable E := ⟨h⟩
  { inner := inner_ 𝕜
    norm_sq_eq_re_inner := inner_.norm_sq
    conj_inner_symm := inner_.conj_symm
    add_left := InnerProductSpaceable.add_left
    smul_left := fun _ _ _ => innerProp _ _ _ }

variable (E)
variable [InnerProductSpaceable E]

/--
theorem `nonempty_innerProductSpace` / 定理 `nonempty_innerProductSpace`

English:
theorem nonempty_innerProductSpace
  statement: Nonempty (InnerProductSpace 𝕜 E)
  proof: ⟨{ inner := inner_ 𝕜
      norm_sq_eq_re_inner := inner_.norm_sq
      conj_inner_symm := inner_.conj_symm
      add_left := add_left
      smul_left := fun _ _ _ => innerProp _ _ _ }⟩

中文:
定理 nonempty_innerProductSpace
  结论: 非空 (内积空间 𝕜 E)
  证明: ⟨{ inner := inner_ 𝕜
      norm_sq_eq_re_inner := inner_.norm_sq
      conj_inner_symm := inner_.conj_symm
      add_left := add_left
      smul_left := fun _ _ _ => innerProp _ _ _ }⟩

Depends on / 依赖: add_left, conj_inner_symm, conj_symm, innerProp, inner_, inner_.conj_symm, inner_.norm_sq, norm_sq, norm_sq_eq_re_inner, smul_left
-/
theorem nonempty_innerProductSpace : Nonempty (InnerProductSpace 𝕜 E) :=
  ⟨{ inner := inner_ 𝕜
      norm_sq_eq_re_inner := inner_.norm_sq
      conj_inner_symm := inner_.conj_symm
      add_left := add_left
      smul_left := fun _ _ _ => innerProp _ _ _ }⟩

variable {𝕜 E}
variable [NormedSpace Real E]

-- TODO: Replace `InnerProductSpace.toUniformConvexSpace`
-- See note [lower instance priority]
instance (priority := 100) InnerProductSpaceable.to_uniformConvexSpace : UniformConvexSpace E := by
  cases nonempty_innerProductSpace Real E; infer_instance
