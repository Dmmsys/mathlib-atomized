/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.MeanValue

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Slope
/-!
# Logarithmic Derivatives

We define the logarithmic derivative of a function `f` as `deriv f / f`. We then prove some basic
facts about this, including how it changes under multiplication and composition.

-/

@[expose] public section

noncomputable section

open Filter Function Set

open scoped Topology

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

/--
Definition of `logDeriv` / `logDeriv` 的定义

English:
definition logDeriv
  signature: (f : 𝕜 -> 𝕜')
  body: deriv f / f

中文:
定义 logDeriv
  签名: (f : 𝕜 -> 𝕜')
  定义体: deriv f / f
-/
def logDeriv (f : 𝕜 -> 𝕜') :=
  deriv f / f

/--
theorem `logDeriv_apply` / 定理 `logDeriv_apply`

English:
theorem logDeriv_apply
  given: (f : 𝕜 -> 𝕜') (x : 𝕜)
  statement: logDeriv f x = deriv f x / f x
  proof: rfl

中文:
定理 logDeriv_apply
  条件: (f : 𝕜 -> 𝕜') (x : 𝕜)
  结论: logDeriv f x = deriv f x / f x
  证明: rfl
-/
theorem logDeriv_apply (f : 𝕜 -> 𝕜') (x : 𝕜) : logDeriv f x = deriv f x / f x := rfl

/--
lemma `logDeriv_eq_zero_of_not_differentiableAt` / 引理 `logDeriv_eq_zero_of_not_differentiableAt`

English:
lemma logDeriv_eq_zero_of_not_differentiableAt
  given: (f : 𝕜 -> 𝕜') (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x)
  proof: by
  simp only [logDeriv_apply, deriv_zero_of_not_differentiableAt h, zero_div]

中文:
引理 logDeriv_eq_zero_of_not_differentiableAt
  条件: (f : 𝕜 -> 𝕜') (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x)
  证明: by
  simp only [logDeriv_apply, deriv_zero_of_not_differentiableAt h, zero_div]

Depends on / 依赖: deriv_zero_of_not_differentiableAt, logDeriv_apply, zero_div
-/
lemma logDeriv_eq_zero_of_not_differentiableAt (f : 𝕜 -> 𝕜') (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x) :
    logDeriv f x = 0 := by
  simp only [logDeriv_apply, deriv_zero_of_not_differentiableAt h, zero_div]

/--
lemma `logDeriv_congr_nhds` / 引理 `logDeriv_congr_nhds`

English:
lemma logDeriv_congr_nhds
  given: {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝 x] g)
  proof: h.deriv.div h

中文:
引理 logDeriv_congr_nhds
  条件: {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝 x] g)
  证明: h.deriv.div h

Depends on / 依赖: h.deriv.div
-/
lemma logDeriv_congr_nhds {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝 x] g) :
    logDeriv f =ᶠ[𝓝 x] logDeriv g := h.deriv.div h

/--
lemma `logDeriv_congr_nhdsNE` / 引理 `logDeriv_congr_nhdsNE`

English:
lemma logDeriv_congr_nhdsNE
  given: {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝[!=] x] g)
  proof: h.nhdsNE_deriv.div h

中文:
引理 logDeriv_congr_nhdsNE
  条件: {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝[!=] x] g)
  证明: h.nhdsNE_deriv.div h

Depends on / 依赖: h.nhdsNE_deriv.div, nhdsNE_deriv
-/
lemma logDeriv_congr_nhdsNE {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝[!=] x] g) :
    logDeriv f =ᶠ[𝓝[!=] x] logDeriv g := h.nhdsNE_deriv.div h

/--
theorem `logDeriv_congr_codiscreteWithin` / 定理 `logDeriv_congr_codiscreteWithin`

English:
theorem logDeriv_congr_codiscreteWithin
  statement: {f g : 𝕜 -> 𝕜'} {U : Set 𝕜} (hU : IsOpen U)
  proof: by
  refine mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun x hx => ?_
  refine mem_of_superset (logDeriv_congr_nhdsNE ?_) Set.subset_union_left
  filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx,
    nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz hzU
  exact hz.resolve_right (no

中文:
定理 logDeriv_congr_codiscreteWithin
  结论: {f g : 𝕜 -> 𝕜'} {U : 集合 𝕜} (hU : 是开集 U)
  证明: by
  refine mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun x hx => ?_
  refine mem_of_superset (logDeriv_congr_nhdsNE ?_) Set.subset_union_left
  filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx,
    nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz hzU
  exact hz.resolve_right (no

Depends on / 依赖: Set.subset_union_left, filter_upwards, hU.mem_nhds, hz.resolve_right, logDeriv_congr_nhdsNE, mem_codiscreteWithin_iff_forall_mem_nhdsNE, mem_nhds, mem_of_superset, nhdsWithin_le_nhds, not_not_intro, resolve_right, subset_union_left
-/
theorem logDeriv_congr_codiscreteWithin {f g : 𝕜 -> 𝕜'} {U : Set 𝕜} (hU : IsOpen U)
    (h : f =ᶠ[codiscreteWithin U] g) :
    logDeriv f =ᶠ[codiscreteWithin U] logDeriv g := by
  refine mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun x hx => ?_
  refine mem_of_superset (logDeriv_congr_nhdsNE ?_) Set.subset_union_left
  filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx,
    nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz hzU
  exact hz.resolve_right (not_not_intro hzU)

/--
theorem `logDeriv_congr_codiscrete` / 定理 `logDeriv_congr_codiscrete`

English:
theorem logDeriv_congr_codiscrete
  given: {f g : 𝕜 -> 𝕜'} (h : f =ᶠ[codiscrete 𝕜] g)
  proof: logDeriv_congr_codiscreteWithin isOpen_univ h

@[simp]

中文:
定理 logDeriv_congr_codiscrete
  条件: {f g : 𝕜 -> 𝕜'} (h : f =ᶠ[codiscrete 𝕜] g)
  证明: logDeriv_congr_codiscreteWithin isOpen_univ h

@[simp]

Depends on / 依赖: isOpen_univ, logDeriv_congr_codiscreteWithin
-/
theorem logDeriv_congr_codiscrete {f g : 𝕜 -> 𝕜'} (h : f =ᶠ[codiscrete 𝕜] g) :
    logDeriv f =ᶠ[codiscrete 𝕜] logDeriv g :=
  logDeriv_congr_codiscreteWithin isOpen_univ h

@[simp]
/--
theorem `logDeriv_id` / 定理 `logDeriv_id`

English:
theorem logDeriv_id
  given: (x : 𝕜)
  statement: logDeriv id x = 1 / x
  proof: by
  simp [logDeriv_apply]

中文:
定理 logDeriv_id
  条件: (x : 𝕜)
  结论: logDeriv id x = 1 / x
  证明: by
  simp [logDeriv_apply]

Depends on / 依赖: logDeriv_apply
-/
theorem logDeriv_id (x : 𝕜) : logDeriv id x = 1 / x := by
  simp [logDeriv_apply]

/--
theorem `logDeriv_id'` / 定理 `logDeriv_id'`

English:
theorem logDeriv_id'
  given: (x : 𝕜)
  statement: logDeriv (·) x = 1 / x
  proof: logDeriv_id x

@[simp]

中文:
定理 logDeriv_id'
  条件: (x : 𝕜)
  结论: logDeriv (·) x = 1 / x
  证明: logDeriv_id x

@[simp]
-/
@[simp] theorem logDeriv_id' (x : 𝕜) : logDeriv (·) x = 1 / x := logDeriv_id x

@[simp]
/--
theorem `logDeriv_const` / 定理 `logDeriv_const`

English:
theorem logDeriv_const
  given: (a : 𝕜')
  statement: logDeriv (fun _ : 𝕜 => a) = 0
  proof: by
  ext
  simp [logDeriv_apply]

中文:
定理 logDeriv_const
  条件: (a : 𝕜')
  结论: logDeriv (fun _ : 𝕜 => a) = 0
  证明: by
  ext
  simp [logDeriv_apply]

Depends on / 依赖: logDeriv_apply
-/
theorem logDeriv_const (a : 𝕜') : logDeriv (fun _ : 𝕜 => a) = 0 := by
  ext
  simp [logDeriv_apply]

/--
theorem `logDeriv_mul` / 定理 `logDeriv_mul`

English:
theorem logDeriv_mul
  statement: {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg : g x != 0)
  proof: by
  simp [field, logDeriv_apply, *]

中文:
定理 logDeriv_mul
  结论: {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg : g x != 0)
  证明: by
  simp [field, logDeriv_apply, *]

Depends on / 依赖: logDeriv_apply
-/
theorem logDeriv_mul {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg : g x != 0)
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) :
      logDeriv (fun z => f z * g z) x = logDeriv f x + logDeriv g x := by
  simp [field, logDeriv_apply, *]

/--
theorem `logDeriv_div` / 定理 `logDeriv_div`

English:
theorem logDeriv_div
  statement: {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg : g x != 0)
  proof: by
  simp [field, logDeriv_apply, *]

中文:
定理 logDeriv_div
  结论: {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg : g x != 0)
  证明: by
  simp [field, logDeriv_apply, *]

Depends on / 依赖: logDeriv_apply
-/
theorem logDeriv_div {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg : g x != 0)
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) :
    logDeriv (fun z => f z / g z) x = logDeriv f x - logDeriv g x := by
  simp [field, logDeriv_apply, *]

/--
theorem `logDeriv_mul_const` / 定理 `logDeriv_mul_const`

English:
theorem logDeriv_mul_const
  given: {f : 𝕜 -> 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a != 0)
  proof: by
  simp only [logDeriv_apply, deriv_mul_const_field, mul_div_mul_right _ _ ha]

中文:
定理 logDeriv_mul_const
  条件: {f : 𝕜 -> 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a != 0)
  证明: by
  simp only [logDeriv_apply, deriv_mul_const_field, mul_div_mul_right _ _ ha]

Depends on / 依赖: deriv_mul_const_field, logDeriv_apply, mul_div_mul_right
-/
theorem logDeriv_mul_const {f : 𝕜 -> 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a != 0) :
    logDeriv (fun z => f z * a) x = logDeriv f x := by
  simp only [logDeriv_apply, deriv_mul_const_field, mul_div_mul_right _ _ ha]

/--
theorem `logDeriv_const_mul` / 定理 `logDeriv_const_mul`

English:
theorem logDeriv_const_mul
  given: {f : 𝕜 -> 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a != 0)
  proof: by
  simp only [logDeriv_apply, deriv_const_mul_field, mul_div_mul_left _ _ ha]

中文:
定理 logDeriv_const_mul
  条件: {f : 𝕜 -> 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a != 0)
  证明: by
  simp only [logDeriv_apply, deriv_const_mul_field, mul_div_mul_left _ _ ha]

Depends on / 依赖: deriv_const_mul_field, logDeriv_apply, mul_div_mul_left
-/
theorem logDeriv_const_mul {f : 𝕜 -> 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a != 0) :
    logDeriv (fun z => a * f z) x = logDeriv f x := by
  simp only [logDeriv_apply, deriv_const_mul_field, mul_div_mul_left _ _ ha]

/--
theorem `logDeriv_prod` / 定理 `logDeriv_prod`

English:
theorem logDeriv_prod
  statement: {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'} {x : 𝕜} (hf : forall i in s, f i x != 0)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.forall_mem_cons] at hf hd
    simp_rw [Finset.prod_cons, Finset.sum_cons]
    rw [logDeriv_mul]; rw [ih hf.2 hd.2]
    · exact hf.1
    · simpa [Finset.prod_eq_zero_iff] using hf.2
    · exact hd

中文:
定理 logDeriv_prod
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 𝕜 -> 𝕜'} {x : 𝕜} (hf : 对任意 i in s, f i x != 0)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.forall_mem_cons] at hf hd
    simp_rw [Finset.prod_cons, Finset.sum_cons]
    rw [logDeriv_mul]; rw [ih hf.2 hd.2]
    · exact hf.1
    · simpa [Finset.prod_eq_zero_iff] using hf.2
    · exact hd

Depends on / 依赖: Finset, Finset.cons_induction, Finset.forall_mem_cons, Finset.prod_cons, Finset.prod_eq_zero_iff, Finset.sum_cons, cons_induction, forall_mem_cons, fun_finsetProd, logDeriv_mul, prod_cons, prod_eq_zero_iff, simp_rw, sum_cons
-/
theorem logDeriv_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'} {x : 𝕜} (hf : forall i in s, f i x != 0)
    (hd : forall i in s, DifferentiableAt 𝕜 (f i) x) :
    logDeriv (∏ i in s, f i ·) x = ∑ i in s, logDeriv (f i) x := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.forall_mem_cons] at hf hd
    simp_rw [Finset.prod_cons, Finset.sum_cons]
    rw [logDeriv_mul]; rw [ih hf.2 hd.2]
    · exact hf.1
    · simpa [Finset.prod_eq_zero_iff] using hf.2
    · exact hd.1
    · exact .fun_finsetProd hd.2

/--
lemma `logDeriv_fun_zpow` / 引理 `logDeriv_fun_zpow`

English:
lemma logDeriv_fun_zpow
  given: {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : Int)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn; · simp
  rcases eq_or_ne (f x) 0 with hf | hf
  · simp [logDeriv_apply, zero_zpow, *]
  · rw [logDeriv_apply, ← comp_def (· ^ n), deriv_comp _ (differentiableAt_zpow.2 <| .inl hf) hdf,
      deriv_zpow, logDeriv_apply]
    simp [field, zpow_sub_one₀ hf]

中文:
引理 logDeriv_fun_zpow
  条件: {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : 整数)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn; · simp
  rcases eq_or_ne (f x) 0 with hf | hf
  · simp [logDeriv_apply, zero_zpow, *]
  · rw [logDeriv_apply, ← comp_def (· ^ n), deriv_comp _ (differentiableAt_zpow.2 <| .inl hf) hdf,
      deriv_zpow, logDeriv_apply]
    simp [field, zpow_sub_one₀ hf]

Depends on / 依赖: comp_def, deriv_comp, deriv_zpow, differentiableAt_zpow, eq_or_ne, logDeriv_apply, zero_zpow
-/
lemma logDeriv_fun_zpow {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : Int) :
    logDeriv (f · ^ n) x = n * logDeriv f x := by
  rcases eq_or_ne n 0 with rfl | hn; · simp
  rcases eq_or_ne (f x) 0 with hf | hf
  · simp [logDeriv_apply, zero_zpow, *]
  · rw [logDeriv_apply, ← comp_def (· ^ n), deriv_comp _ (differentiableAt_zpow.2 <| .inl hf) hdf,
      deriv_zpow, logDeriv_apply]
    simp [field, zpow_sub_one₀ hf]

/--
lemma `logDeriv_fun_pow` / 引理 `logDeriv_fun_pow`

English:
lemma logDeriv_fun_pow
  given: {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : Nat)
  proof: mod_cast logDeriv_fun_zpow hdf n

@[simp]

中文:
引理 logDeriv_fun_pow
  条件: {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : 自然数)
  证明: mod_cast logDeriv_fun_zpow hdf n

@[simp]

Depends on / 依赖: logDeriv_fun_zpow, mod_cast
-/
lemma logDeriv_fun_pow {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : Nat) :
    logDeriv (f · ^ n) x = n * logDeriv f x :=
  mod_cast logDeriv_fun_zpow hdf n

@[simp]
/--
lemma `logDeriv_zpow` / 引理 `logDeriv_zpow`

English:
lemma logDeriv_zpow
  given: (x : 𝕜) (n : Int)
  statement: logDeriv (· ^ n) x = n / x
  proof: by
  rw [logDeriv_fun_zpow (by fun_prop)]; rw [logDeriv_id']; rw [mul_one_div]

@[simp]

中文:
引理 logDeriv_zpow
  条件: (x : 𝕜) (n : 整数)
  结论: logDeriv (· ^ n) x = n / x
  证明: by
  rw [logDeriv_fun_zpow (by fun_prop)]; rw [logDeriv_id']; rw [mul_one_div]

@[simp]

Depends on / 依赖: fun_prop, logDeriv_fun_zpow, logDeriv_id, mul_one_div
-/
lemma logDeriv_zpow (x : 𝕜) (n : Int) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_fun_zpow (by fun_prop)]; rw [logDeriv_id']; rw [mul_one_div]

@[simp]
/--
lemma `logDeriv_pow` / 引理 `logDeriv_pow`

English:
lemma logDeriv_pow
  given: (x : 𝕜) (n : Nat)
  statement: logDeriv (· ^ n) x = n / x
  proof: mod_cast logDeriv_zpow x n

中文:
引理 logDeriv_pow
  条件: (x : 𝕜) (n : 自然数)
  结论: logDeriv (· ^ n) x = n / x
  证明: mod_cast logDeriv_zpow x n

Depends on / 依赖: logDeriv_zpow, mod_cast
-/
lemma logDeriv_pow (x : 𝕜) (n : Nat) : logDeriv (· ^ n) x = n / x :=
  mod_cast logDeriv_zpow x n

/--
lemma `logDeriv_inv` / 引理 `logDeriv_inv`

English:
lemma logDeriv_inv
  given: (x : 𝕜)
  statement: logDeriv (·⁻¹) x = -1 / x
  proof: by
  simpa using logDeriv_zpow x (-1)

中文:
引理 logDeriv_inv
  条件: (x : 𝕜)
  结论: logDeriv (·⁻¹) x = -1 / x
  证明: by
  simpa using logDeriv_zpow x (-1)
-/
@[simp] lemma logDeriv_inv (x : 𝕜) : logDeriv (·⁻¹) x = -1 / x := by
  simpa using logDeriv_zpow x (-1)

/--
theorem `logDeriv_comp` / 定理 `logDeriv_comp`

English:
theorem logDeriv_comp
  statement: {f : 𝕜' -> 𝕜'} {g : 𝕜 -> 𝕜'} {x : 𝕜} (hf : DifferentiableAt 𝕜' f (g x))
  proof: by
  simp only [logDeriv, Pi.div_apply, deriv_comp _ hf hg, comp_apply]
  ring

中文:
定理 logDeriv_comp
  结论: {f : 𝕜' -> 𝕜'} {g : 𝕜 -> 𝕜'} {x : 𝕜} (hf : DifferentiableAt 𝕜' f (g x))
  证明: by
  simp only [logDeriv, Pi.div_apply, deriv_comp _ hf hg, comp_apply]
  ring

Depends on / 依赖: Pi.div_apply, comp_apply, deriv_comp, div_apply, logDeriv
-/
theorem logDeriv_comp {f : 𝕜' -> 𝕜'} {g : 𝕜 -> 𝕜'} {x : 𝕜} (hf : DifferentiableAt 𝕜' f (g x))
    (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x = logDeriv f (g x) * deriv g x := by
  simp only [logDeriv, Pi.div_apply, deriv_comp _ hf hg, comp_apply]
  ring

/--
lemma `logDeriv_eqOn_iff` / 引理 `logDeriv_eqOn_iff`

English:
lemma logDeriv_eqOn_iff
  statement: [IsRCLikeNormedField 𝕜] {f g : 𝕜 -> 𝕜'} {s : Set 𝕜}
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · simpa using ⟨1, one_ne_zero⟩
  · constructor
    · refine fun h => ⟨f t * (g t)⁻¹, by grind, fun y hy => ?_⟩
      have hderiv : s.EqOn (deriv (f * g⁻¹)) (deriv f * g⁻¹ - f * deriv g / g ^ 2) := by
        intro z hz
        rw [deriv_mul (hf

中文:
引理 logDeriv_eqOn_iff
  结论: [是RCLikeNormedField 𝕜] {f g : 𝕜 -> 𝕜'} {s : 集合 𝕜}
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · simpa using ⟨1, one_ne_zero⟩
  · constructor
    · refine fun h => ⟨f t * (g t)⁻¹, by grind, fun y hy => ?_⟩
      have hderiv : s.EqOn (deriv (f * g⁻¹)) (deriv f * g⁻¹ - f * deriv g / g ^ 2) := by
        intro z hz
        rw [deriv_mul (hf

Depends on / 依赖: Pi.inv_apply, deriv_comp, deriv_inv, deriv_mul, differentiableAt, differentiableAt_inv, eq_empty_or_nonempty, hderiv, hf.differentiableAt, hg.dif, hg.differentiableAt, hs2.mem_nhds, inv_apply, mem_nhds, neg_mul, one_ne_zero, s.EqOn, s.eq_empty_or_nonempty
-/
lemma logDeriv_eqOn_iff [IsRCLikeNormedField 𝕜] {f g : 𝕜 -> 𝕜'} {s : Set 𝕜}
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hs2 : IsOpen s) (hsc : IsPreconnected s) (hgn : forall x in s, g x != 0) (hfn : forall x in s, f x != 0) :
    EqOn (logDeriv f) (logDeriv g) s ↔ exists z : 𝕜', z != 0 ∧ EqOn f (z • g) s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · simpa using ⟨1, one_ne_zero⟩
  · constructor
    · refine fun h => ⟨f t * (g t)⁻¹, by grind, fun y hy => ?_⟩
      have hderiv : s.EqOn (deriv (f * g⁻¹)) (deriv f * g⁻¹ - f * deriv g / g ^ 2) := by
        intro z hz
        rw [deriv_mul (hf.differentiableAt (hs2.mem_nhds hz)) ((hg.differentiableAt
          (hs2.mem_nhds hz)).inv (hgn z hz))]
        simp only [Pi.inv_apply, show g⁻¹ = (fun x => x⁻¹) ∘ g by rfl, deriv_inv, neg_mul,
          deriv_comp z (differentiableAt_inv (hgn z hz)) (hg.differentiableAt (hs2.mem_nhds hz)),
          mul_neg, Pi.sub_apply, Pi.mul_apply, comp_apply, Pi.div_apply, Pi.pow_apply]
        ring
      have hfg : EqOn (deriv (f * g⁻¹)) 0 s := hderiv.trans fun z hz => by
        simp only [Pi.sub_apply, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.pow_apply,
          Pi.zero_apply]
        grind [logDeriv_apply, Pi.div_apply]
      let := IsRCLikeNormedField.rclike 𝕜
      obtain ⟨a, ha⟩ := hs2.exists_is_const_of_deriv_eq_zero hsc (hf.mul (hg.inv hgn)) hfg
      grind [Pi.mul_apply, Pi.inv_apply, Pi.smul_apply, smul_eq_mul]
    · rintro ⟨z, hz0, hz⟩ x hx
      simp [logDeriv_apply, hz.deriv hs2 hx, hz hx, deriv_const_smul _
        (hg.differentiableAt (hs2.mem_nhds hx)), mul_div_mul_left (deriv g x) (g x) hz0]


/--
theorem `AnalyticAt.tendsto_mul_logDeriv_simple_zero` / 定理 `AnalyticAt.tendsto_mul_logDeriv_simple_zero`

English:
theorem AnalyticAt.tendsto_mul_logDeriv_simple_zero
  statement: [CompleteSpace 𝕜]
  proof: by
  have h_slope := hasDerivAt_iff_tendsto_slope.mp hf.differentiableAt.hasDerivAt
  rw [← div_self hf']
.div h_slope hf' convert hf.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simp [logDeriv, slope, hfx]
  field

中文:
定理 AnalyticAt.tendsto_mul_logDeriv_simple_zero
  结论: [完备空间 𝕜]
  证明: by
  have h_slope := hasDerivAt_iff_tendsto_slope.mp hf.differentiableAt.hasDerivAt
  rw [← div_self hf']
.div h_slope hf' convert hf.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simp [logDeriv, slope, hfx]
  field

Depends on / 依赖: continuousAt, convert, differentiableAt, div_self, h_slope, hasDerivAt, hasDerivAt_iff_tendsto_slope, hasDerivAt_iff_tendsto_slope.mp, hf.deriv.continuousAt.tendsto.mono_left, hf.differentiableAt.hasDerivAt, logDeriv, mono_left, nhdsWithin_le_nhds, tendsto
-/
theorem AnalyticAt.tendsto_mul_logDeriv_simple_zero [CompleteSpace 𝕜]
    {f : 𝕜 -> 𝕜} {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hfx : f x = 0) (hf' : deriv f x != 0) :
    Filter.Tendsto (fun w => (w - x) * logDeriv f w)
      (𝓝[!=] x) (𝓝 1) := by
  have h_slope := hasDerivAt_iff_tendsto_slope.mp hf.differentiableAt.hasDerivAt
  rw [← div_self hf']
.div h_slope hf' convert hf.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simp [logDeriv, slope, hfx]
  field
