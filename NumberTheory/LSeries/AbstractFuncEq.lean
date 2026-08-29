/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.MellinTransform

/-!
# Abstract functional equations for Mellin transforms

This file formalises a general version of an argument used to prove functional equations for
zeta and L-functions.

### FE-pairs

We define a *weak FE-pair* to be a pair of functions `f, g` on the reals which are locally
integrable on `(0, ∞)`, have the form "constant" + "rapidly decaying term" at `∞`, and satisfy a
functional equation of the form

`f (1 / x) = ε * x ^ k * g x`

for some constants `k ∈ ℝ` and `ε ∈ ℂ`. (Modular forms give rise to natural examples
with `k` being the weight and `ε` the global root number; hence the notation.) We could arrange
`ε = 1` by scaling `g`; but this is inconvenient in applications so we set things up more generally.

A *strong FE-pair* is a weak FE-pair where the constant terms of `f` and `g` at `∞` are both 0.

The main property of these pairs is the following: if `f`, `g` are a weak FE-pair, with constant
terms `f₀` and `g₀` at `∞`, then the Mellin transforms `Λ` and `Λ'` of `f - f₀` and `g - g₀`
respectively both have meromorphic continuation and satisfy a functional equation of the form

`Λ (k - s) = ε * Λ' s`.

The poles (and their residues) are explicitly given in terms of `f₀` and `g₀`; in particular, if
`(f, g)` are a strong FE-pair, then the Mellin transforms of `f` and `g` are entire functions.

### Main definitions and results

See the sections *Main theorems on weak FE-pairs* and
*Main theorems on strong FE-pairs* below.

* Weak FE pairs:
  - `WeakFEPair.Λ₀`: and `WeakFEPair.Λ`: functions of `s : ℂ`
  - `WeakFEPair.differentiable_Λ₀`: `Λ₀` is entire
  - `WeakFEPair.differentiableAt_Λ`: `Λ` is differentiable away from `s = 0` and `s = k`
  - `WeakFEPair.hasMellin`: for `k < re s`, `Λ s` equals the Mellin transform of `f - f₀`
  - `WeakFEPair.functional_equation₀`: the functional equation for `Λ₀`
  - `WeakFEPair.functional_equation`: the functional equation for `Λ`
  - `WeakFEPair.Λ_residue_k`: computation of the residue at `k`
  - `WeakFEPair.Λ_residue_zero`: computation of the residue at `0`.

* Strong FE pairs:
  - `IsStrongFEPair.differentiable_Λ`: `Λ` is entire
  - `IsStrongFEPair.hasMellin`: `Λ` is everywhere equal to the Mellin transform of `f`
-/

@[expose] public section


/- TODO: Consider extending the results to allow functional equations of the form
`f (N / x) = (const) • x ^ k • g x` for a real parameter `0 < N`. This could be done either by
generalising the existing proofs in situ, or by a separate wrapper `FEPairWithLevel` which just
applies a scaling factor to `f` and `g` to reduce to the `N = 1` case.
-/

noncomputable section

open Real Complex Filter Topology Asymptotics Set MeasureTheory

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace Complex E]

/-!
## Definitions and symmetry
-/

/--
Definition of `WeakFEPair` / `WeakFEPair` 的定义

English:
structure WeakFEPair
  parameters: where
  axioms and operations (11):
    - (f(g) : Real -> E)
    - (k : Real)
    - (ε : Complex)
    - (f₀(g₀) : E)
    - (hf_int : LocallyIntegrableOn f (Ioi 0))
    - (hg_int : LocallyIntegrableOn g (Ioi 0))
    - (hk : 0 < k)
    - (hε : ε != 0)
    - (h_feq : forall x in Ioi 0, f (1 / x) = (ε * ↑(x ^ k)) • g x)
    - (hf_top((r : Real)) : (f · - f₀) =O[atTop] (· ^ r))
    - (hg_top((r : Real)) : (g · - g₀) =O[atTop] (· ^ r))

中文:
结构 WeakFEPair
  参数: where
  公理与运算 (11 个):
    - (f(g) : 实数 -> E)
    - (k : 实数)
    - (ε : Complex)
    - (f₀(g₀) : E)
    - (hf_int : Locally整数egrableOn f (Ioi 0))
    - (hg_int : Locally整数egrableOn g (Ioi 0))
    - (hk : 0 < k)
    - (hε : ε != 0)
    - (h_feq : 对任意 x in Ioi 0, f (1 / x) = (ε * ↑(x ^ k)) • g x)
    - (hf_top((r : 实数)) : (f · - f₀) =O[atTop] (· ^ r))
    - (hg_top((r : 实数)) : (g · - g₀) =O[atTop] (· ^ r))
-/
structure WeakFEPair where
  /-- The functions whose Mellin transform we study -/
  (f g : Real -> E)
  /-- Weight (exponent in the functional equation) -/
  (k : Real)
  /-- Root number -/
  (ε : Complex)
  /-- Constant terms at `∞` -/
  (f₀ g₀ : E)
  (hf_int : LocallyIntegrableOn f (Ioi 0))
  (hg_int : LocallyIntegrableOn g (Ioi 0))
  (hk : 0 < k)
  (hε : ε != 0)
  (h_feq : forall x in Ioi 0, f (1 / x) = (ε * ↑(x ^ k)) • g x)
  (hf_top (r : Real) : (f · - f₀) =O[atTop] (· ^ r))
  (hg_top (r : Real) : (g · - g₀) =O[atTop] (· ^ r))

variable {E}

/--
Definition of `IsStrongFEPair` / `IsStrongFEPair` 的定义

English:
structure IsStrongFEPair
  parameters: (P : WeakFEPair E)
  axioms and operations (2):
    - hf₀ : P.f₀ = 0
    - hg₀ : P.g₀ = 0

中文:
结构 IsStrongFEPair
  参数: (P : WeakFEPair E)
  公理与运算 (2 个):
    - hf₀ : P.f₀ = 0
    - hg₀ : P.g₀ = 0
-/
structure IsStrongFEPair (P : WeakFEPair E) : Prop where
  hf₀ : P.f₀ = 0
  hg₀ : P.g₀ = 0

section symmetry

/--
lemma `WeakFEPair.h_feq'` / 引理 `WeakFEPair.h_feq'`

English:
lemma WeakFEPair.h_feq'
  given: (P : WeakFEPair E) (x : Real) (hx : 0 < x)
  proof: by
  rw [(div_div_cancel₀ (one_ne_zero' Real) ▸ P.h_feq (1 / x) (one_div_pos.mpr hx) :)]; rw [← mul_smul]
  convert! (one_smul Complex (P.g (1 / x))).symm using 2
  rw [one_div]; rw [inv_rpow hx.le]; rw [ofReal_inv]
  field [P.hε, (rpow_pos_of_pos hx _).ne']

中文:
引理 WeakFEPair.h_feq'
  条件: (P : WeakFEPair E) (x : 实数) (hx : 0 < x)
  证明: by
  rw [(div_div_cancel₀ (one_ne_zero' Real) ▸ P.h_feq (1 / x) (one_div_pos.mpr hx) :)]; rw [← mul_smul]
  convert! (one_smul Complex (P.g (1 / x))).symm using 2
  rw [one_div]; rw [inv_rpow hx.le]; rw [ofReal_inv]
  field [P.hε, (rpow_pos_of_pos hx _).ne']

Depends on / 依赖: P.h_feq, convert, h_feq, hx.le, inv_rpow, mul_smul, ofReal_inv, one_div, one_div_pos, one_div_pos.mpr, one_ne_zero, one_smul, rpow_pos_of_pos
-/
lemma WeakFEPair.h_feq' (P : WeakFEPair E) (x : Real) (hx : 0 < x) :
    P.g (1 / x) = (P.ε⁻¹ * ↑(x ^ P.k)) • P.f x := by
  rw [(div_div_cancel₀ (one_ne_zero' Real) ▸ P.h_feq (1 / x) (one_div_pos.mpr hx) :)]; rw [← mul_smul]
  convert! (one_smul Complex (P.g (1 / x))).symm using 2
  rw [one_div]; rw [inv_rpow hx.le]; rw [ofReal_inv]
  field [P.hε, (rpow_pos_of_pos hx _).ne']

/-- The hypotheses are symmetric in `f` and `g`, with the constant `ε` replaced by `ε⁻¹`. -/
@[simps]
/--
Definition of `WeakFEPair.symm` / `WeakFEPair.symm` 的定义

English:
definition WeakFEPair.symm
  signature: (P : WeakFEPair E)
  body: P.g
  g := P.f
  k := P.k
  ε := P.ε⁻¹
  f₀ := P.g₀
  g₀ := P.f₀
  hf_int := P.hg_int
  hg_int := P.hf_int
  hf_top := P.hg_top
  hg_top := P.hf_top
  hε := inv_ne_zero P.hε
  hk := P.hk
  h_feq := P.h_feq'

中文:
定义 WeakFEPair.symm
  签名: (P : WeakFEPair E)
  定义体: P.g
  g := P.f
  k := P.k
  ε := P.ε⁻¹
  f₀ := P.g₀
  g₀ := P.f₀
  hf_int := P.hg_int
  hg_int := P.hf_int
  hf_top := P.hg_top
  hg_top := P.hf_top
  hε := inv_ne_zero P.hε
  hk := P.hk
  h_feq := P.h_feq'
-/
def WeakFEPair.symm (P : WeakFEPair E) : WeakFEPair E where
  f := P.g
  g := P.f
  k := P.k
  ε := P.ε⁻¹
  f₀ := P.g₀
  g₀ := P.f₀
  hf_int := P.hg_int
  hg_int := P.hf_int
  hf_top := P.hg_top
  hg_top := P.hf_top
  hε := inv_ne_zero P.hε
  hk := P.hk
  h_feq := P.h_feq'

/--
lemma `isStrongFEPair_symm` / 引理 `isStrongFEPair_symm`

English:
lemma isStrongFEPair_symm
  given: {P : WeakFEPair E}
  proof: ⟨h.hg₀, h.hf₀⟩
  mpr h := ⟨h.hg₀, h.hf₀⟩

中文:
引理 isStrongFEPair_symm
  条件: {P : WeakFEPair E}
  证明: ⟨h.hg₀, h.hf₀⟩
  mpr h := ⟨h.hg₀, h.hf₀⟩
-/
@[simp] lemma isStrongFEPair_symm {P : WeakFEPair E} :
    IsStrongFEPair P.symm ↔ IsStrongFEPair P where
  mp h := ⟨h.hg₀, h.hf₀⟩
  mpr h := ⟨h.hg₀, h.hf₀⟩

/--
lemma `IsStrongFEPair.symm` / 引理 `IsStrongFEPair.symm`

English:
lemma IsStrongFEPair.symm
  given: {P : WeakFEPair E} (hP : IsStrongFEPair P)
  proof: isStrongFEPair_symm.2 hP

中文:
引理 IsStrongFEPair.symm
  条件: {P : WeakFEPair E} (hP : IsStrongFEPair P)
  证明: isStrongFEPair_symm.2 hP

Depends on / 依赖: isStrongFEPair_symm
-/
lemma IsStrongFEPair.symm {P : WeakFEPair E} (hP : IsStrongFEPair P) :
    IsStrongFEPair P.symm := isStrongFEPair_symm.2 hP

end symmetry

namespace WeakFEPair

variable (P : WeakFEPair E)

/-!
## Auxiliary results I: lemmas on asymptotics
-/

/--
lemma `hf_zero` / 引理 `hf_zero`

English:
lemma hf_zero
  given: (r : Real)
  proof: by
  have := (P.hg_top (-(r + P.k))).comp_tendsto tendsto_inv_nhdsGT_zero
  simp_rw [IsBigO, IsBigOWith, eventually_nhdsWithin_iff] at this ⊢
  obtain ⟨C, hC⟩ := this
  use ‖P.ε‖ * C
  filter_upwards [hC] with x hC' (hx : 0 < x)
  have h_nv2 : ↑(x ^ P.k) != (0 : Complex) := ofReal_ne_zero.mpr (rpow_

中文:
引理 hf_zero
  条件: (r : 实数)
  证明: by
  have := (P.hg_top (-(r + P.k))).comp_tendsto tendsto_inv_nhdsGT_zero
  simp_rw [IsBigO, IsBigOWith, eventually_nhdsWithin_iff] at this ⊢
  obtain ⟨C, hC⟩ := this
  use ‖P.ε‖ * C
  filter_upwards [hC] with x hC' (hx : 0 < x)
  have h_nv2 : ↑(x ^ P.k) != (0 : Complex) := ofReal_ne_zero.mpr (rpow_

Depends on / 依赖: Function, Function.comp_apply, IsBigO, IsBigOWith, P.h_feq, P.hg_top, P.symm.h, comp_apply, comp_tendsto, eventually_nhdsWithin_iff, filter_upwards, h_feq, h_nv, h_nv2, hg_top, mul_ne_zero, ofReal_ne_zero, ofReal_ne_zero.mpr, one_div, one_sm
-/
lemma hf_zero (r : Real) :
    (fun x => P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀) =O[𝓝[>] 0] (· ^ r) := by
  have := (P.hg_top (-(r + P.k))).comp_tendsto tendsto_inv_nhdsGT_zero
  simp_rw [IsBigO, IsBigOWith, eventually_nhdsWithin_iff] at this ⊢
  obtain ⟨C, hC⟩ := this
  use ‖P.ε‖ * C
  filter_upwards [hC] with x hC' (hx : 0 < x)
  have h_nv2 : ↑(x ^ P.k) != (0 : Complex) := ofReal_ne_zero.mpr (rpow_pos_of_pos hx _).ne'
  have h_nv : P.ε⁻¹ * ↑(x ^ P.k) != 0 := mul_ne_zero P.symm.hε h_nv2
  specialize hC' hx
  simp_rw [Function.comp_apply, ← one_div, P.h_feq' _ hx] at hC'
  rw [← ((mul_inv_cancel₀ h_nv).symm ▸ one_smul Complex P.g₀ :)]; rw [mul_smul _ _ P.g₀]; rw [← smul_sub]; rw [norm_smul]; rw [← le_div_iff₀' (lt_of_le_of_ne (norm_nonneg _) (norm_ne_zero_iff.mpr h_nv).symm)] at hC'
  convert! hC' using 1
  · congr 3
    rw [rpow_neg hx.le]
    simp [field]
  · simp_rw [norm_mul, norm_real, one_div, inv_rpow hx.le, rpow_neg hx.le, inv_inv, norm_inv,
      norm_of_nonneg (rpow_pos_of_pos hx _).le, rpow_add hx]
    field

/--
lemma `hf_zero'` / 引理 `hf_zero'`

English:
lemma hf_zero'
  statement: (fun x : Real => P.f x - P.f₀) =O[𝓝[>] 0] (· ^ (-P.k))
  proof: by
  simp_rw [← fun x => sub_add_sub_cancel (P.f x) ((P.ε * ↑(x ^ (-P.k))) • P.g₀) P.f₀]
  refine (P.hf_zero _).add (IsBigO.sub ?_ ?_)
  · rw [← isBigO_norm_norm]
    simp_rw [mul_smul, norm_smul, mul_comm _ ‖P.g₀‖, ← mul_assoc, norm_real]
    apply (isBigO_refl _ _).const_mul_left
  · refine IsBigO

中文:
引理 hf_zero'
  结论: (fun x : 实数 => P.f x - P.f₀) =O[𝓝[>] 0] (· ^ (-P.k))
  证明: by
  simp_rw [← fun x => sub_add_sub_cancel (P.f x) ((P.ε * ↑(x ^ (-P.k))) • P.g₀) P.f₀]
  refine (P.hf_zero _).add (IsBigO.sub ?_ ?_)
  · rw [← isBigO_norm_norm]
    simp_rw [mul_smul, norm_smul, mul_comm _ ‖P.g₀‖, ← mul_assoc, norm_real]
    apply (isBigO_refl _ _).const_mul_left
  · refine IsBigO

Depends on / 依赖: IsBigO, IsBigO.of_bound, IsBigO.sub, P.hf_zero, const_mul_left, eventually_le_nhds, eventually_nhdsWithin_iff, eventually_nhdsWithin_iff.mpr, filter_upwards, hf_zero, isBigO_norm_norm, isBigO_refl, le_mul_of_one_le_right, mul_assoc, mul_comm, mul_smul, norm_nonneg, norm_of_nonneg, norm_real, norm_smul
-/
lemma hf_zero' : (fun x : Real => P.f x - P.f₀) =O[𝓝[>] 0] (· ^ (-P.k)) := by
  simp_rw [← fun x => sub_add_sub_cancel (P.f x) ((P.ε * ↑(x ^ (-P.k))) • P.g₀) P.f₀]
  refine (P.hf_zero _).add (IsBigO.sub ?_ ?_)
  · rw [← isBigO_norm_norm]
    simp_rw [mul_smul, norm_smul, mul_comm _ ‖P.g₀‖, ← mul_assoc, norm_real]
    apply (isBigO_refl _ _).const_mul_left
  · refine IsBigO.of_bound ‖P.f₀‖ (eventually_nhdsWithin_iff.mpr ?_)
    filter_upwards [eventually_le_nhds zero_lt_one] with x hx' (hx : 0 < x)
    apply le_mul_of_one_le_right (norm_nonneg _)
    rw [norm_of_nonneg (rpow_pos_of_pos hx _).le]; rw [rpow_neg hx.le]
    exact (one_le_inv₀ (rpow_pos_of_pos hx _)).2 (rpow_le_one hx.le hx' P.hk.le)

/--
theorem `functional_equation_aux` / 定理 `functional_equation_aux`

English:
theorem functional_equation_aux
  given: (s : Complex)
  proof: by
  -- substitute `t ↦ t⁻¹` in `mellin P.g s`
  have step1 := mellin_comp_rpow P.g (-s) (-1)
  simp_rw [abs_neg, abs_one, inv_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one, neg_neg,
    rpow_neg_one, ← one_div] at step1
  -- introduce a power of `t` to match the hypothesis `P.h_feq`
  hav

中文:
定理 functional_equation_aux
  条件: (s : Complex)
  证明: by
  -- substitute `t ↦ t⁻¹` in `mellin P.g s`
  have step1 := mellin_comp_rpow P.g (-s) (-1)
  simp_rw [abs_neg, abs_one, inv_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one, neg_neg,
    rpow_neg_one, ← one_div] at step1
  -- introduce a power of `t` to match the hypothesis `P.h_feq`
  hav
-/
private theorem functional_equation_aux (s : Complex) :
    mellin P.f (P.k - s) = P.ε • mellin P.g s := by
  -- substitute `t ↦ t⁻¹` in `mellin P.g s`
  have step1 := mellin_comp_rpow P.g (-s) (-1)
  simp_rw [abs_neg, abs_one, inv_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one, neg_neg,
    rpow_neg_one, ← one_div] at step1
  -- introduce a power of `t` to match the hypothesis `P.h_feq`
  have step2 := mellin_cpow_smul (fun t => P.g (1 / t)) (P.k - s) (-P.k)
  rw [← sub_eq_add_neg]; rw [sub_right_comm]; rw [sub_self]; rw [zero_sub]; rw [step1] at step2
  -- put in the constant `P.ε`
  have step3 := mellin_const_smul (fun t => (t : Complex) ^ (-P.k : Complex) • P.g (1 / t)) (P.k - s) P.ε
  rw [step2] at step3
  rw [← step3]
  -- now the integrand matches `P.h_feq'` on `Ioi 0`, so we can apply `setIntegral_congr_fun`
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp_rw [P.h_feq' t ht, ← mul_smul]
  -- some simple `cpow` arithmetic to finish
  rw [cpow_neg]; rw [ofReal_cpow (le_of_lt ht)]
  have : (t : Complex) ^ (P.k : Complex) != 0 := by simpa [← ofReal_cpow ht.le] using (rpow_pos_of_pos ht _).ne'
  field_simp [P.hε]

end WeakFEPair

namespace IsStrongFEPair

variable {P : WeakFEPair E} (hP : IsStrongFEPair P)
include hP

/--
lemma `hf_top` / 引理 `hf_top`

English:
lemma hf_top
  given: (r : Real)
  statement: P.f =O[atTop] (· ^ r)
  proof: by
  simpa [hP.hf₀] using P.hf_top r

中文:
引理 hf_top
  条件: (r : 实数)
  结论: P.f =O[atTop] (· ^ r)
  证明: by
  simpa [hP.hf₀] using P.hf_top r

Depends on / 依赖: P.hf_top, hP.hf, hf_top
-/
lemma hf_top (r : Real) : P.f =O[atTop] (· ^ r) := by
  simpa [hP.hf₀] using P.hf_top r

/--
lemma `hf_zero` / 引理 `hf_zero`

English:
lemma hf_zero
  given: (r : Real)
  statement: P.f =O[𝓝[>] 0] (· ^ r)
  proof: by
  simpa using (hP.hg₀ ▸ P.hf_zero r :)

中文:
引理 hf_zero
  条件: (r : 实数)
  结论: P.f =O[𝓝[>] 0] (· ^ r)
  证明: by
  simpa using (hP.hg₀ ▸ P.hf_zero r :)

Depends on / 依赖: P.hf_zero, hP.hg, hf_zero
-/
lemma hf_zero (r : Real) : P.f =O[𝓝[>] 0] (· ^ r) := by
  simpa using (hP.hg₀ ▸ P.hf_zero r :)

/--
theorem `mellinConvergent` / 定理 `mellinConvergent`

English:
theorem mellinConvergent
  given: (s : Complex)
  statement: MellinConvergent P.f s
  proof: let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellinConvergent_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu

中文:
定理 mellinConvergent
  条件: (s : Complex)
  结论: MellinConvergent P.f s
  证明: let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellinConvergent_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu
-/
private theorem mellinConvergent (s : Complex) : MellinConvergent P.f s :=
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellinConvergent_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu

/--
theorem `differentiable_mellin` / 定理 `differentiable_mellin`

English:
theorem differentiable_mellin
  statement: Differentiable Complex (mellin P.f)
  proof: fun s =>
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellin_differentiableAt_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu

中文:
定理 differentiable_mellin
  结论: Differentiable Complex (mellin P.f)
  证明: fun s =>
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellin_differentiableAt_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu
-/
private theorem differentiable_mellin : Differentiable Complex (mellin P.f) := fun s =>
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellin_differentiableAt_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu

end IsStrongFEPair

namespace WeakFEPair

variable (P : WeakFEPair E)

/-!
## Auxiliary results II: building a strong FE-pair from a weak FE-pair
-/

/--
Definition of `f_modif` / `f_modif` 的定义

English:
definition f_modif
  signature: : Real -> E
  body: (Ioi 1).indicator (fun x => P.f x - P.f₀) +
  (Ioo 0 1).indicator (fun x => P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀)

中文:
定义 f_modif
  签名: : 实数 -> E
  定义体: (Ioi 1).indicator (fun x => P.f x - P.f₀) +
  (Ioo 0 1).indicator (fun x => P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀)

Depends on / 依赖: indicator
-/
def f_modif : Real -> E :=
  (Ioi 1).indicator (fun x => P.f x - P.f₀) +
  (Ioo 0 1).indicator (fun x => P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀)

/--
Definition of `g_modif` / `g_modif` 的定义

English:
definition g_modif
  signature: : Real -> E
  body: (Ioi 1).indicator (fun x => P.g x - P.g₀) +
  (Ioo 0 1).indicator (fun x => P.g x - (P.ε⁻¹ * ↑(x ^ (-P.k))) • P.f₀)

中文:
定义 g_modif
  签名: : 实数 -> E
  定义体: (Ioi 1).indicator (fun x => P.g x - P.g₀) +
  (Ioo 0 1).indicator (fun x => P.g x - (P.ε⁻¹ * ↑(x ^ (-P.k))) • P.f₀)

Depends on / 依赖: indicator
-/
def g_modif : Real -> E :=
  (Ioi 1).indicator (fun x => P.g x - P.g₀) +
  (Ioo 0 1).indicator (fun x => P.g x - (P.ε⁻¹ * ↑(x ^ (-P.k))) • P.f₀)

/--
lemma `hf_modif_int` / 引理 `hf_modif_int`

English:
lemma hf_modif_int
  proof: by
  have : LocallyIntegrableOn (fun x : Real => (P.ε * ↑(x ^ (-P.k))) • P.g₀) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt (fun x (hx : 0 < x) => ?_)
    have : x != 0 ∨ 0 <= -P.k := Or.inl hx.ne'
    fun_prop
  refine

中文:
引理 hf_modif_int
  证明: by
  have : LocallyIntegrableOn (fun x : Real => (P.ε * ↑(x ^ (-P.k))) • P.g₀) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt (fun x (hx : 0 < x) => ?_)
    have : x != 0 ∨ 0 <= -P.k := Or.inl hx.ne'
    fun_prop
  refine

Depends on / 依赖: ContinuousOn, ContinuousOn.locallyIntegrableOn, LocallyIntegrableOn, LocallyIntegrableOn.add, Or.inl, P.hf_int.sub, continuousOn_of_forall_continuousAt, fun_prop, hf_int, hx.ne, indicator, locallyIntegrableOn, locallyIntegrableOn_const, measurableSet_Ioi
-/
lemma hf_modif_int :
    LocallyIntegrableOn P.f_modif (Ioi 0) := by
  have : LocallyIntegrableOn (fun x : Real => (P.ε * ↑(x ^ (-P.k))) • P.g₀) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt (fun x (hx : 0 < x) => ?_)
    have : x != 0 ∨ 0 <= -P.k := Or.inl hx.ne'
    fun_prop
  refine LocallyIntegrableOn.add (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨s, hs, hs'⟩ := P.hf_int.sub (locallyIntegrableOn_const _) x hx
    exact ⟨s, hs, hs'.indicator measurableSet_Ioi⟩
  · obtain ⟨s, hs, hs'⟩ := P.hf_int.sub this x hx
    exact ⟨s, hs, hs'.indicator measurableSet_Ioo⟩

/--
lemma `hf_modif_FE` / 引理 `hf_modif_FE`

English:
lemma hf_modif_FE
  given: (x : Real) (hx : 0 < x)
  proof: by
  rcases lt_trichotomy 1 x with hx' | rfl | hx'
  · have : 1 / x < 1 := by rwa [one_div_lt hx one_pos, div_one]
    rw [f_modif]; rw [Pi.add_apply]; rw [indicator_of_notMem (notMem_Ioi.mpr this.le)]; rw [zero_add]; rw [indicator_of_mem (mem_Ioo.mpr ⟨div_pos one_pos hx]; rw [this⟩)]; rw [g_modif];

中文:
引理 hf_modif_FE
  条件: (x : 实数) (hx : 0 < x)
  证明: by
  rcases lt_trichotomy 1 x with hx' | rfl | hx'
  · have : 1 / x < 1 := by rwa [one_div_lt hx one_pos, div_one]
    rw [f_modif]; rw [Pi.add_apply]; rw [indicator_of_notMem (notMem_Ioi.mpr this.le)]; rw [zero_add]; rw [indicator_of_mem (mem_Ioo.mpr ⟨div_pos one_pos hx]; rw [this⟩)]; rw [g_modif];

Depends on / 依赖: P.h_feq, Pi.add_apply, add_apply, add_zero, div_one, div_pos, f_modif, g_modif, h_feq, indicator_of_mem, indicator_of_notMem, lt_trichotomy, mem_Ioi, mem_Ioi.mpr, mem_Ioo, mem_Ioo.mpr, notMem_Ioi, notMem_Ioi.mpr, notMem_Ioo_of_ge, one_
-/
lemma hf_modif_FE (x : Real) (hx : 0 < x) :
    P.f_modif (1 / x) = (P.ε * ↑(x ^ P.k)) • P.g_modif x := by
  rcases lt_trichotomy 1 x with hx' | rfl | hx'
  · have : 1 / x < 1 := by rwa [one_div_lt hx one_pos, div_one]
    rw [f_modif]; rw [Pi.add_apply]; rw [indicator_of_notMem (notMem_Ioi.mpr this.le)]; rw [zero_add]; rw [indicator_of_mem (mem_Ioo.mpr ⟨div_pos one_pos hx]; rw [this⟩)]; rw [g_modif]; rw [Pi.add_apply]; rw [indicator_of_mem (mem_Ioi.mpr hx')]; rw [indicator_of_notMem
      (notMem_Ioo_of_ge hx'.le)]; rw [add_zero]; rw [P.h_feq _ hx]; rw [smul_sub]
    simp_rw [rpow_neg (one_div_pos.mpr hx).le, one_div, inv_rpow hx.le, inv_inv]
  · simp [f_modif, g_modif]
  · have : 1 < 1 / x := by rwa [lt_one_div one_pos hx, div_one]
    rw [f_modif]; rw [Pi.add_apply]; rw [indicator_of_mem (mem_Ioi.mpr this)]; rw [indicator_of_notMem (notMem_Ioo_of_ge this.le)]; rw [g_modif]; rw [Pi.add_apply]; rw [indicator_of_notMem (notMem_Ioi.mpr hx'.le)]; rw [indicator_of_mem (mem_Ioo.mpr ⟨hx]; rw [hx'⟩)]; rw [P.h_feq _ hx]
    simp_rw [rpow_neg hx.le]
    match_scalars <;> field [(rpow_pos_of_pos hx P.k).ne', P.hε]

/--
lemma `hf_modif_top` / 引理 `hf_modif_top`

English:
lemma hf_modif_top
  given: (r : Real)
  proof: by
  refine (P.hf_top r).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [f_modif, mem_Ioi.mpr hx, notMem_Ioo_of_ge hx.le]

中文:
引理 hf_modif_top
  条件: (r : 实数)
  证明: by
  refine (P.hf_top r).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [f_modif, mem_Ioi.mpr hx, notMem_Ioo_of_ge hx.le]

Depends on / 依赖: P.hf_top, eventually_gt_atTop, f_modif, filter_upwards, hf_top, hx.le, mem_Ioi, mem_Ioi.mpr, notMem_Ioo_of_ge
-/
lemma hf_modif_top (r : Real) :
    (fun x => P.f_modif x - 0) =O[atTop] fun x => x ^ r := by
  refine (P.hf_top r).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [f_modif, mem_Ioi.mpr hx, notMem_Ioo_of_ge hx.le]

/--
Definition of `toStrongFEPair` / `toStrongFEPair` 的定义

English:
definition toStrongFEPair
  signature: : WeakFEPair E where
  body: P.f_modif
  g := P.symm.f_modif
  k := P.k
  ε := P.ε
  f₀ := 0
  g₀ := 0
  hf_int := P.hf_modif_int
  hg_int := P.symm.hf_modif_int
  h_feq := P.hf_modif_FE
  hε := P.hε
  hk := P.hk
  hf_top := P.hf_modif_top
  hg_top := P.symm.hf_modif_top

中文:
定义 toStrongFEPair
  签名: : WeakFEPair E where
  定义体: P.f_modif
  g := P.symm.f_modif
  k := P.k
  ε := P.ε
  f₀ := 0
  g₀ := 0
  hf_int := P.hf_modif_int
  hg_int := P.symm.hf_modif_int
  h_feq := P.hf_modif_FE
  hε := P.hε
  hk := P.hk
  hf_top := P.hf_modif_top
  hg_top := P.symm.hf_modif_top

Depends on / 依赖: P.f_modif, f_modif
-/
def toStrongFEPair : WeakFEPair E where
  f := P.f_modif
  g := P.symm.f_modif
  k := P.k
  ε := P.ε
  f₀ := 0
  g₀ := 0
  hf_int := P.hf_modif_int
  hg_int := P.symm.hf_modif_int
  h_feq := P.hf_modif_FE
  hε := P.hε
  hk := P.hk
  hf_top := P.hf_modif_top
  hg_top := P.symm.hf_modif_top

/--
lemma `isStrongFEPair_toStrongFEPair` / 引理 `isStrongFEPair_toStrongFEPair`

English:
lemma isStrongFEPair_toStrongFEPair
  statement: IsStrongFEPair P.toStrongFEPair where
  proof: rfl
  hg₀ := rfl

中文:
引理 isStrongFEPair_toStrongFEPair
  结论: IsStrongFEPair P.toStrongFEPair where
  证明: rfl
  hg₀ := rfl
-/
lemma isStrongFEPair_toStrongFEPair : IsStrongFEPair P.toStrongFEPair where
  hf₀ := rfl
  hg₀ := rfl

/--
lemma `f_modif_aux1` / 引理 `f_modif_aux1`

English:
lemma f_modif_aux1
  statement: EqOn (fun x => P.f_modif x - P.f x + P.f₀)
  proof: by
  intro x (hx : 0 < x)
  simp_rw [f_modif, Pi.add_apply]
  rcases lt_trichotomy x 1 with hx' | rfl | hx'
  · simp_rw [indicator_of_notMem (notMem_Ioi.mpr hx'.le), indicator_of_mem (mem_Ioo.mpr ⟨hx, hx'⟩),
      indicator_of_notMem (mem_singleton_iff.not.mpr hx'.ne)]
    abel
  · simp [add_comm, s

中文:
引理 f_modif_aux1
  结论: EqOn (fun x => P.f_modif x - P.f x + P.f₀)
  证明: by
  intro x (hx : 0 < x)
  simp_rw [f_modif, Pi.add_apply]
  rcases lt_trichotomy x 1 with hx' | rfl | hx'
  · simp_rw [indicator_of_notMem (notMem_Ioi.mpr hx'.le), indicator_of_mem (mem_Ioo.mpr ⟨hx, hx'⟩),
      indicator_of_notMem (mem_singleton_iff.not.mpr hx'.ne)]
    abel
  · simp [add_comm, s

Depends on / 依赖: Pi.add_apply, add_apply, add_comm, f_modif, indicator_of_mem, indicator_of_notMem, lt_trichotomy, mem_Ioi, mem_Ioi.mpr, mem_Ioo, mem_Ioo.mpr, mem_singleton_iff, mem_singleton_iff.not.mpr, notMem_Ioi, notMem_Ioi.mpr, notMem_Ioo_of_ge, simp_rw, sub_eq_add_neg
-/
lemma f_modif_aux1 : EqOn (fun x => P.f_modif x - P.f x + P.f₀)
    ((Ioo 0 1).indicator (fun x : Real => P.f₀ - (P.ε * ↑(x ^ (-P.k))) • P.g₀)
    + ({1} : Set Real).indicator (fun _ => P.f₀ - P.f 1)) (Ioi 0) := by
  intro x (hx : 0 < x)
  simp_rw [f_modif, Pi.add_apply]
  rcases lt_trichotomy x 1 with hx' | rfl | hx'
  · simp_rw [indicator_of_notMem (notMem_Ioi.mpr hx'.le), indicator_of_mem (mem_Ioo.mpr ⟨hx, hx'⟩),
      indicator_of_notMem (mem_singleton_iff.not.mpr hx'.ne)]
    abel
  · simp [add_comm, sub_eq_add_neg]
  · simp_rw [indicator_of_mem (mem_Ioi.mpr hx'), indicator_of_notMem (notMem_Ioo_of_ge hx'.le),
      indicator_of_notMem (mem_singleton_iff.not.mpr hx'.ne')]
    abel

/--
lemma `f_modif_aux2` / 引理 `f_modif_aux2`

English:
lemma f_modif_aux2
  given: [CompleteSpace E] {s : Complex} (hs : P.k < re s)
  proof: by
  have h_re1 : -1 < re (s - 1) := by simpa using P.hk.trans hs
  have h_re2 : -1 < re (s - P.k - 1) := by simpa using hs
  calc
  _ = ∫ (x : Real) in Ioi 0, (x : Complex) ^ (s - 1) •
      ((Ioo 0 1).indicator (fun t : Real => P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x
      + ({1} : Set Real).indica

中文:
引理 f_modif_aux2
  条件: [CompleteSpace E] {s : Complex} (hs : P.k < re s)
  证明: by
  have h_re1 : -1 < re (s - 1) := by simpa using P.hk.trans hs
  have h_re2 : -1 < re (s - P.k - 1) := by simpa using hs
  calc
  _ = ∫ (x : Real) in Ioi 0, (x : Complex) ^ (s - 1) •
      ((Ioo 0 1).indicator (fun t : Real => P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x
      + ({1} : Set Real).indica

Depends on / 依赖: P.hk.trans, f_modif_aux1, h_re1, h_re2, indicator, measurableSet_Ioi, setIntegral_congr_fun
-/
lemma f_modif_aux2 [CompleteSpace E] {s : Complex} (hs : P.k < re s) :
    mellin (fun x => P.f_modif x - P.f x + P.f₀) s = (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g₀ := by
  have h_re1 : -1 < re (s - 1) := by simpa using P.hk.trans hs
  have h_re2 : -1 < re (s - P.k - 1) := by simpa using hs
  calc
  _ = ∫ (x : Real) in Ioi 0, (x : Complex) ^ (s - 1) •
      ((Ioo 0 1).indicator (fun t : Real => P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x
      + ({1} : Set Real).indicator (fun _ => P.f₀ - P.f 1) x) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => by simp [f_modif_aux1 P hx])
  _ = ∫ (x : Real) in Ioi 0, (x : Complex) ^ (s - 1) • ((Ioo 0 1).indicator
      (fun t : Real => P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x) := by
    refine setIntegral_congr_ae measurableSet_Ioi (eventually_of_mem (U := {1}ᶜ)
        (compl_mem_ae_iff.mpr (subsingleton_singleton.measure_zero _)) (fun x hx _ => ?_))
    rw [indicator_of_notMem hx]; rw [add_zero]
  _ = ∫ (x : Real) in Ioc 0 1, (x : Complex) ^ (s - 1) • (P.f₀ - (P.ε * ↑(x ^ (-P.k))) • P.g₀) := by
    simp_rw [← indicator_smul, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, integral_Ioc_eq_integral_Ioo]
  _ = ∫ x : Real in Ioc 0 1, ((x : Complex) ^ (s - 1) • P.f₀ - P.ε • (x : Complex) ^ (s - P.k - 1) • P.g₀) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x ⟨hx, _⟩ => ?_)
    rw [ofReal_cpow hx.le]; rw [ofReal_neg]; rw [smul_sub]; rw [← mul_smul]; rw [mul_comm]; rw [mul_assoc]; rw [mul_smul]; rw [mul_comm]; rw [← cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]; rw [← sub_eq_add_neg]; rw [sub_right_comm]
  _ = (∫ (x : Real) in Ioc 0 1, (x : Complex) ^ (s - 1)) • P.f₀
        - P.ε • (∫ (x : Real) in Ioc 0 1, (x : Complex) ^ (s - P.k - 1)) • P.g₀ := by
    rw [integral_sub]; rw [integral_smul]; rw [integral_smul_const]; rw [integral_smul_const]
    · apply Integrable.smul_const
      rw [← IntegrableOn]; rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_cpow' h_re1
    · refine (Integrable.smul_const ?_ _).smul _
      rw [← IntegrableOn]; rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_cpow' h_re2
  _ = _ := by
      simp_rw [← intervalIntegral.integral_of_le zero_le_one]
      match_scalars
      · simp [integral_cpow (.inl h_re1), zero_cpow (show s != 0 by grind [P.hk, zero_re])]
      · simp [integral_cpow (.inl h_re2), zero_cpow (show s - P.k != 0 by grind [P.hk, ofReal_re])]
        grind
/-!
## Main theorems on weak FE-pairs
-/

/--
Definition of `Λ₀` / `Λ₀` 的定义

English:
definition Λ₀
  signature: : Complex -> E
  body: mellin P.f_modif

中文:
定义 Λ₀
  签名: : Complex -> E
  定义体: mellin P.f_modif

Depends on / 依赖: P.f_modif, f_modif, mellin
-/
def Λ₀ : Complex -> E := mellin P.f_modif

/--
Definition of `Λ` / `Λ` 的定义

English:
definition Λ
  signature: (s : Complex)
  body: P.Λ₀ s - (1 / s) • P.f₀ - (P.ε / (P.k - s)) • P.g₀

中文:
定义 Λ
  签名: (s : Complex)
  定义体: P.Λ₀ s - (1 / s) • P.f₀ - (P.ε / (P.k - s)) • P.g₀
-/
def Λ (s : Complex) : E := P.Λ₀ s - (1 / s) • P.f₀ - (P.ε / (P.k - s)) • P.g₀

/--
lemma `Λ₀_eq` / 引理 `Λ₀_eq`

English:
lemma Λ₀_eq
  given: (s : Complex)
  statement: P.Λ₀ s = P.Λ s + (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g₀
  proof: by
  unfold Λ Λ₀
  abel

中文:
引理 Λ₀_eq
  条件: (s : Complex)
  结论: P.Λ₀ s = P.Λ s + (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g₀
  证明: by
  unfold Λ Λ₀
  abel
-/
lemma Λ₀_eq (s : Complex) : P.Λ₀ s = P.Λ s + (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g₀ := by
  unfold Λ Λ₀
  abel

/--
lemma `symm_Λ₀_eq` / 引理 `symm_Λ₀_eq`

English:
lemma symm_Λ₀_eq
  given: (s : Complex)
  proof: by
  simp [P.symm.Λ₀_eq]

中文:
引理 symm_Λ₀_eq
  条件: (s : Complex)
  证明: by
  simp [P.symm.Λ₀_eq]

Depends on / 依赖: P.symm
-/
lemma symm_Λ₀_eq (s : Complex) :
    P.symm.Λ₀ s = P.symm.Λ s + (1 / s) • P.g₀ + (P.ε⁻¹ / (P.k - s)) • P.f₀ := by
  simp [P.symm.Λ₀_eq]

/--
theorem `differentiable_Λ₀` / 定理 `differentiable_Λ₀`

English:
theorem differentiable_Λ₀
  statement: Differentiable Complex P.Λ₀
  proof: P.isStrongFEPair_toStrongFEPair.differentiable_mellin

中文:
定理 differentiable_Λ₀
  结论: Differentiable Complex P.Λ₀
  证明: P.isStrongFEPair_toStrongFEPair.differentiable_mellin

Depends on / 依赖: P.isStrongFEPair_toStrongFEPair.differentiable_mellin, differentiable_mellin, isStrongFEPair_toStrongFEPair
-/
theorem differentiable_Λ₀ : Differentiable Complex P.Λ₀ :=
  P.isStrongFEPair_toStrongFEPair.differentiable_mellin

/--
theorem `differentiableAt_Λ` / 定理 `differentiableAt_Λ`

English:
theorem differentiableAt_Λ
  given: {s : Complex} (hs : s != 0 ∨ P.f₀ = 0) (hs' : s != P.k ∨ P.g₀ = 0)
  proof: by
  refine ((P.differentiable_Λ₀ s).sub ?_).sub ?_
  · rcases hs with hs | hs
    · fun_prop
    · simp [hs]
  · rcases hs' with hs' | hs'
    · fun_prop (disch := grind)
    · simp [hs']

中文:
定理 differentiableAt_Λ
  条件: {s : Complex} (hs : s != 0 ∨ P.f₀ = 0) (hs' : s != P.k ∨ P.g₀ = 0)
  证明: by
  refine ((P.differentiable_Λ₀ s).sub ?_).sub ?_
  · rcases hs with hs | hs
    · fun_prop
    · simp [hs]
  · rcases hs' with hs' | hs'
    · fun_prop (disch := grind)
    · simp [hs']

Depends on / 依赖: P.differentiable_, fun_prop
-/
theorem differentiableAt_Λ {s : Complex} (hs : s != 0 ∨ P.f₀ = 0) (hs' : s != P.k ∨ P.g₀ = 0) :
    DifferentiableAt Complex P.Λ s := by
  refine ((P.differentiable_Λ₀ s).sub ?_).sub ?_
  · rcases hs with hs | hs
    · fun_prop
    · simp [hs]
  · rcases hs' with hs' | hs'
    · fun_prop (disch := grind)
    · simp [hs']

/--
theorem `hasMellin` / 定理 `hasMellin`

English:
theorem hasMellin
  statement: [CompleteSpace E]
  proof: by
  have hc1 : MellinConvergent (P.f · - P.f₀) s :=
    let ⟨_, ht⟩ := exists_gt s.re
    mellinConvergent_of_isBigO_rpow (P.hf_int.sub (locallyIntegrableOn_const _)) (P.hf_top _) ht
      P.hf_zero' hs
  refine ⟨hc1, ?_⟩
  have hc2 : MellinConvergent P.f_modif s :=
    P.isStrongFEPair_toStrongFEP

中文:
定理 hasMellin
  结论: [CompleteSpace E]
  证明: by
  have hc1 : MellinConvergent (P.f · - P.f₀) s :=
    let ⟨_, ht⟩ := exists_gt s.re
    mellinConvergent_of_isBigO_rpow (P.hf_int.sub (locallyIntegrableOn_const _)) (P.hf_top _) ht
      P.hf_zero' hs
  refine ⟨hc1, ?_⟩
  have hc2 : MellinConvergent P.f_modif s :=
    P.isStrongFEPair_toStrongFEP

Depends on / 依赖: MellinConvergent, P.f_modif, P.f_modif_aux2, P.hf_int.sub, P.hf_top, P.hf_zero, P.isStrongFEPair_toStrongFEPair.mellinConvergent, exists_gt, f_modif, f_modif_aux2, hasMellin_sub, hf_int, hf_top, hf_zero, isStrongFEPair_toStrongFEPair, locallyIntegrableOn_const, mellin, mellinConvergent, mellinConvergent_of_isBigO_rpow, s.re
-/
theorem hasMellin [CompleteSpace E]
    {s : Complex} (hs : P.k < s.re) : HasMellin (P.f · - P.f₀) s (P.Λ s) := by
  have hc1 : MellinConvergent (P.f · - P.f₀) s :=
    let ⟨_, ht⟩ := exists_gt s.re
    mellinConvergent_of_isBigO_rpow (P.hf_int.sub (locallyIntegrableOn_const _)) (P.hf_top _) ht
      P.hf_zero' hs
  refine ⟨hc1, ?_⟩
  have hc2 : MellinConvergent P.f_modif s :=
    P.isStrongFEPair_toStrongFEPair.mellinConvergent s
  have hc3 : mellin (fun x => f_modif P x - f P x + P.f₀) s =
    (1 / s) • P.f₀ + (P.ε / (↑P.k - s)) • P.g₀ := P.f_modif_aux2 hs
  have := (hasMellin_sub hc2 hc1).2
  simp only [Λ, Λ₀] at *
  grind

/--
theorem `functional_equation₀` / 定理 `functional_equation₀`

English:
theorem functional_equation₀
  given: (s : Complex)
  statement: P.Λ₀ (P.k - s) = P.ε • P.symm.Λ₀ s
  proof: P.toStrongFEPair.functional_equation_aux s

中文:
定理 functional_equation₀
  条件: (s : Complex)
  结论: P.Λ₀ (P.k - s) = P.ε • P.symm.Λ₀ s
  证明: P.toStrongFEPair.functional_equation_aux s

Depends on / 依赖: P.toStrongFEPair.functional_equation_aux, functional_equation_aux, toStrongFEPair
-/
theorem functional_equation₀ (s : Complex) : P.Λ₀ (P.k - s) = P.ε • P.symm.Λ₀ s :=
  P.toStrongFEPair.functional_equation_aux s

/--
theorem `functional_equation` / 定理 `functional_equation`

English:
theorem functional_equation
  given: (s : Complex)
  proof: by
  linear_combination (norm := module) P.functional_equation₀ s - P.Λ₀_eq (P.k - s)
    + congr(P.ε • $(P.symm_Λ₀_eq s)) + congr(($(mul_inv_cancel₀ P.hε) / (P.k - s)) • P.f₀)

中文:
定理 functional_equation
  条件: (s : Complex)
  证明: by
  linear_combination (norm := module) P.functional_equation₀ s - P.Λ₀_eq (P.k - s)
    + congr(P.ε • $(P.symm_Λ₀_eq s)) + congr(($(mul_inv_cancel₀ P.hε) / (P.k - s)) • P.f₀)

Depends on / 依赖: P.functional_equation, P.symm_, linear_combination, module
-/
theorem functional_equation (s : Complex) :
    P.Λ (P.k - s) = P.ε • P.symm.Λ s := by
  linear_combination (norm := module) P.functional_equation₀ s - P.Λ₀_eq (P.k - s)
    + congr(P.ε • $(P.symm_Λ₀_eq s)) + congr(($(mul_inv_cancel₀ P.hε) / (P.k - s)) • P.f₀)

/--
theorem `Λ_residue_k` / 定理 `Λ_residue_k`

English:
theorem Λ_residue_k
  proof: by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (P.ε • P.g₀) = 𝓝 (0 - 0 - -P.ε • P.g₀))]
  refine ((Tendsto.sub ?_ ?_).mono_left nhdsWithin_le_nhds).sub ?_
  · rw [(by simp : 𝓝 0 = 𝓝 ((P.k - P.k : Complex) • P.Λ₀ P.k))]
    apply ((continuous_sub_right _).smul P.differentiable_Λ₀.continuous).tendsto
  · rw 

中文:
定理 Λ_residue_k
  证明: by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (P.ε • P.g₀) = 𝓝 (0 - 0 - -P.ε • P.g₀))]
  refine ((Tendsto.sub ?_ ?_).mono_left nhdsWithin_le_nhds).sub ?_
  · rw [(by simp : 𝓝 0 = 𝓝 ((P.k - P.k : Complex) • P.Λ₀ P.k))]
    apply ((continuous_sub_right _).smul P.differentiable_Λ₀.continuous).tendsto
  · rw 

Depends on / 依赖: ContinuousAt, ContinuousAt.smul, P.differentiable_, P.hk.ne, Tendsto, Tendsto.sub, continuous, continuousAt, continuousAt.smul, continuousAt_const, continuous_sub_right, fun_prop, mono_left, nhdsWithin_le_nhds, ofReal_ne_zero, ofReal_ne_zero.mpr, simp_rw, smul_sub, tendsto
-/
theorem Λ_residue_k :
    Tendsto (fun s : Complex => (s - P.k) • P.Λ s) (𝓝[!=] P.k) (𝓝 (P.ε • P.g₀)) := by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (P.ε • P.g₀) = 𝓝 (0 - 0 - -P.ε • P.g₀))]
  refine ((Tendsto.sub ?_ ?_).mono_left nhdsWithin_le_nhds).sub ?_
  · rw [(by simp : 𝓝 0 = 𝓝 ((P.k - P.k : Complex) • P.Λ₀ P.k))]
    apply ((continuous_sub_right _).smul P.differentiable_Λ₀.continuous).tendsto
  · rw [(by simp : 𝓝 0 = 𝓝 ((P.k - P.k : Complex) • (1 / P.k : Complex) • P.f₀))]
    refine (continuous_sub_right _).continuousAt.smul (ContinuousAt.smul ?_ continuousAt_const)
    have := ofReal_ne_zero.mpr P.hk.ne'
    fun_prop
  · refine (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s != P.k)
    match_scalars
    grind

/--
theorem `Λ_residue_zero` / 定理 `Λ_residue_zero`

English:
theorem Λ_residue_zero
  statement: Tendsto (fun s => s • P.Λ s) (𝓝[!=] 0) (𝓝 (-P.f₀))
  proof: by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (-P.f₀) = 𝓝 (((0 : Complex) • P.Λ₀ 0) - P.f₀ - 0))]
  refine ((Tendsto.mono_left ?_ nhdsWithin_le_nhds).sub ?_).sub ?_
  · exact (continuous_id.smul P.differentiable_Λ₀.continuous).tendsto _
  · refine (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).congr' ?

中文:
定理 Λ_residue_zero
  结论: Tendsto (fun s => s • P.Λ s) (𝓝[!=] 0) (𝓝 (-P.f₀))
  证明: by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (-P.f₀) = 𝓝 (((0 : Complex) • P.Λ₀ 0) - P.f₀ - 0))]
  refine ((Tendsto.mono_left ?_ nhdsWithin_le_nhds).sub ?_).sub ?_
  · exact (continuous_id.smul P.differentiable_Λ₀.continuous).tendsto _
  · refine (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).congr' ?

Depends on / 依赖: P.differentiable_, Tendsto, Tendsto.mono_left, continu, continuous, continuousAt_id, continuousAt_id.smul, continuous_id, continuous_id.smul, filter_upwards, match_scalars, mono_left, nhdsWithin_le_nhds, self_mem_nhdsWithin, simp_rw, smul_sub, tendsto, tendsto_const_nhds, tendsto_const_nhds.mono_left, zero_smul
-/
theorem Λ_residue_zero : Tendsto (fun s => s • P.Λ s) (𝓝[!=] 0) (𝓝 (-P.f₀)) := by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (-P.f₀) = 𝓝 (((0 : Complex) • P.Λ₀ 0) - P.f₀ - 0))]
  refine ((Tendsto.mono_left ?_ nhdsWithin_le_nhds).sub ?_).sub ?_
  · exact (continuous_id.smul P.differentiable_Λ₀.continuous).tendsto _
  · refine (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s != 0)
    match_scalars
    grind
  · rw [show 𝓝 0 = 𝓝 ((0 : Complex) • (P.ε / (P.k - 0 : Complex)) • P.g₀) by rw [zero_smul]]
    exact (continuousAt_id.smul ((continuousAt_const.div ((continuous_sub_left _).continuousAt)
      (by simpa using P.hk.ne')).smul continuousAt_const)).mono_left nhdsWithin_le_nhds

end WeakFEPair

namespace IsStrongFEPair
/-!
## Main theorems on strong FE-pairs
-/

open WeakFEPair

variable {P : WeakFEPair E} (hP : IsStrongFEPair P)
include hP

/--
lemma `Λ_eq` / 引理 `Λ_eq`

English:
lemma Λ_eq
  statement: P.Λ = mellin P.f
  proof: by
  ext s
  simp only [mellin, Λ, Λ₀, f_modif, hP.hf₀, sub_zero, hP.hg₀, smul_zero]
refine integral_congr_ae (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (Subsingleton.measure_zero (s := {1}) (by simp) _)]
    with t (ht₁ : t != 1) (ht₀ : 0 < t)
  by_cases ht :

中文:
引理 Λ_eq
  结论: P.Λ = mellin P.f
  证明: by
  ext s
  simp only [mellin, Λ, Λ₀, f_modif, hP.hf₀, sub_zero, hP.hg₀, smul_zero]
refine integral_congr_ae (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (Subsingleton.measure_zero (s := {1}) (by simp) _)]
    with t (ht₁ : t != 1) (ht₀ : 0 < t)
  by_cases ht :

Depends on / 依赖: Pi.add_apply, Subsingleton, Subsingleton.measure_zero, add_apply, add_comm, add_zero, ae_restrict_iff, compl_mem_ae_iff, compl_mem_ae_iff.mpr, f_modif, filter_upwards, hP.hf, hP.hg, indicator_of_mem, indicator_of_notMem, integral_congr_ae, measurableSet_Ioi, measure_zero, mellin, smul_zero
-/
lemma Λ_eq : P.Λ = mellin P.f := by
  ext s
  simp only [mellin, Λ, Λ₀, f_modif, hP.hf₀, sub_zero, hP.hg₀, smul_zero]
refine integral_congr_ae (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (Subsingleton.measure_zero (s := {1}) (by simp) _)]
    with t (ht₁ : t != 1) (ht₀ : 0 < t)
  by_cases ht : t < 1 <;> [rw [add_comm] ; skip] <;>
  rw [Pi.add_apply]; rw [indicator_of_mem (by grind)]; rw [indicator_of_notMem (by grind)]; rw [add_zero]

/--
lemma `symm_Λ_eq` / 引理 `symm_Λ_eq`

English:
lemma symm_Λ_eq
  statement: P.symm.Λ = mellin P.g
  proof: hP.symm.Λ_eq

中文:
引理 symm_Λ_eq
  结论: P.symm.Λ = mellin P.g
  证明: hP.symm.Λ_eq

Depends on / 依赖: hP.symm
-/
lemma symm_Λ_eq : P.symm.Λ = mellin P.g := hP.symm.Λ_eq

/--
theorem `hasMellin` / 定理 `hasMellin`

English:
theorem hasMellin
  given: (s : Complex)
  statement: HasMellin P.f s (P.Λ s)
  proof: ⟨hP.mellinConvergent s, congr_fun hP.Λ_eq.symm s⟩

中文:
定理 hasMellin
  条件: (s : Complex)
  结论: HasMellin P.f s (P.Λ s)
  证明: ⟨hP.mellinConvergent s, congr_fun hP.Λ_eq.symm s⟩

Depends on / 依赖: _eq.symm, congr_fun, hP.mellinConvergent, mellinConvergent
-/
theorem hasMellin (s : Complex) : HasMellin P.f s (P.Λ s) :=
  ⟨hP.mellinConvergent s, congr_fun hP.Λ_eq.symm s⟩

/--
theorem `differentiable_Λ` / 定理 `differentiable_Λ`

English:
theorem differentiable_Λ
  statement: Differentiable Complex P.Λ
  proof: hP.Λ_eq ▸ hP.differentiable_mellin

中文:
定理 differentiable_Λ
  结论: Differentiable Complex P.Λ
  证明: hP.Λ_eq ▸ hP.differentiable_mellin

Depends on / 依赖: differentiable_mellin, hP.differentiable_mellin
-/
theorem differentiable_Λ : Differentiable Complex P.Λ :=
  hP.Λ_eq ▸ hP.differentiable_mellin

end IsStrongFEPair
