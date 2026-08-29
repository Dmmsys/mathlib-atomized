/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus using Claude Code
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# Meromorphic API for the Logarithmic Derivative
-/

@[expose] public section

open Filter Function Set Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f g : 𝕜 -> 𝕜'} {x : 𝕜} {U : Set 𝕜}

/-!
## Arithmetic on Codiscrete Sets

The pointwise lemma `logDeriv_mul` requires differentiability and nonvanishing of the factors at the
point in question. For meromorphic functions whose order is nowhere `⊤`, both conditions hold away
from a codiscrete set, turning the pointwise arithmetic into arithmetic of codiscrete equivalence
classes.
-/

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a product of two meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun MeromorphicOn.logDeriv_fun_mul_eventuallyEq]
/--
theorem `MeromorphicOn.logDeriv_mul_eventuallyEq` / 定理 `MeromorphicOn.logDeriv_mul_eventuallyEq`

English:
theorem MeromorphicOn.logDeriv_mul_eventuallyEq
  statement: (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
  proof: by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, hg.analyticAt_mem_codiscreteWithin,
    hf.eventually_codiscreteWithin_apply_ne_zero h'f,
    hg.eventually_codiscreteWithin_apply_ne_zero h'g]
    with y h₁y h₂y h₃y h₄y
  rw [Pi.add_apply]; rw [Pi.mul_def]
  exact logDeriv_mul y h₃y h₄y h₁y.differentiableAt h₂y.differentiableAt

中文:
定理 MeromorphicOn.logDeriv_mul_eventuallyEq
  结论: (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
  证明: by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, hg.analyticAt_mem_codiscreteWithin,
    hf.eventually_codiscreteWithin_apply_ne_zero h'f,
    hg.eventually_codiscreteWithin_apply_ne_zero h'g]
    with y h₁y h₂y h₃y h₄y
  rw [Pi.add_apply]; rw [Pi.mul_def]
  exact logDeriv_mul y h₃y h₄y h₁y.differentiableAt h₂y.differentiableAt

Depends on / 依赖: Pi.add_apply, Pi.mul_def, add_apply, analyticAt_mem_codiscreteWithin, differentiableAt, eventually_codiscreteWithin_apply_ne_zero, filter_upwards, hf.analyticAt_mem_codiscreteWithin, hf.eventually_codiscreteWithin_apply_ne_zero, hg.analyticAt_mem_codiscreteWithin, hg.eventually_codiscreteWithin_apply_ne_zero, logDeriv_mul, mul_def, y.differentiableAt
-/
theorem MeromorphicOn.logDeriv_mul_eventuallyEq (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (h'f : forall x in U, meromorphicOrderAt f x != ⊤) (h'g : forall x in U, meromorphicOrderAt g x != ⊤) :
    logDeriv (f * g) =ᶠ[codiscreteWithin U] logDeriv f + logDeriv g := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, hg.analyticAt_mem_codiscreteWithin,
    hf.eventually_codiscreteWithin_apply_ne_zero h'f,
    hg.eventually_codiscreteWithin_apply_ne_zero h'g]
    with y h₁y h₂y h₃y h₄y
  rw [Pi.add_apply]; rw [Pi.mul_def]
  exact logDeriv_mul y h₃y h₄y h₁y.differentiableAt h₂y.differentiableAt

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a product of two meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun Meromorphic.logDeriv_fun_mul_eventuallyEq]
/--
theorem `Meromorphic.logDeriv_mul_eventuallyEq` / 定理 `Meromorphic.logDeriv_mul_eventuallyEq`

English:
theorem Meromorphic.logDeriv_mul_eventuallyEq
  statement: (hf : Meromorphic f) (hg : Meromorphic g)
  proof: (meromorphicOn_univ.2 hf).logDeriv_mul_eventuallyEq (meromorphicOn_univ.2 hg)
    (fun x _ => h'f x) (fun x _ => h'g x)

中文:
定理 亚纯.logDeriv_mul_eventuallyEq
  结论: (hf : 亚纯 f) (hg : 亚纯 g)
  证明: (meromorphicOn_univ.2 hf).logDeriv_mul_eventuallyEq (meromorphicOn_univ.2 hg)
    (fun x _ => h'f x) (fun x _ => h'g x)

Depends on / 依赖: logDeriv_mul_eventuallyEq, meromorphicOn_univ
-/
theorem Meromorphic.logDeriv_mul_eventuallyEq (hf : Meromorphic f) (hg : Meromorphic g)
    (h'f : forall x, meromorphicOrderAt f x != ⊤) (h'g : forall x, meromorphicOrderAt g x != ⊤) :
    logDeriv (f * g) =ᶠ[codiscrete 𝕜] logDeriv f + logDeriv g :=
  (meromorphicOn_univ.2 hf).logDeriv_mul_eventuallyEq (meromorphicOn_univ.2 hg)
    (fun x _ => h'f x) (fun x _ => h'g x)

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun MeromorphicOn.logDeriv_fun_prod_eventuallyEq]
/--
theorem `MeromorphicOn.logDeriv_prod_eventuallyEq` / 定理 `MeromorphicOn.logDeriv_prod_eventuallyEq`

English:
theorem MeromorphicOn.logDeriv_prod_eventuallyEq
  statement: {ι : Type*} {s : Finset ι} {F : ι -> 𝕜 -> 𝕜'}
  proof: by
  have hA : forallᶠ y in codiscreteWithin U, forall i in s, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset s).2 fun i hi => (h i hi).analyticAt_mem_codiscreteWithin
  have hN : forallᶠ y in codiscreteWithin U, forall i in s, F i y != 0 :=
    (eventually_all_finset s).2 fun i hi => (h i hi).eventually_codiscreteWithin_apply_ne_zero
      (h' i hi)
  filter_upwards [hA, hN] with y h₁y h₂y
  rw [Finset.sum_apply]; rw [Finset.prod_fn]
  exact logDeriv_prod h₂y fun i hi => (h₁y i hi).differentiableAt

中文:
定理 MeromorphicOn.logDeriv_prod_eventuallyEq
  结论: {ι : 类型} {s : 有限集 ι} {F : ι -> 𝕜 -> 𝕜'}
  证明: by
  have hA : forallᶠ y in codiscreteWithin U, forall i in s, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset s).2 fun i hi => (h i hi).analyticAt_mem_codiscreteWithin
  have hN : forallᶠ y in codiscreteWithin U, forall i in s, F i y != 0 :=
    (eventually_all_finset s).2 fun i hi => (h i hi).eventually_codiscreteWithin_apply_ne_zero
      (h' i hi)
  filter_upwards [hA, hN] with y h₁y h₂y
  rw [Finset.sum_apply]; rw [Finset.prod_fn]
  exact logDeriv_prod h₂y fun i hi => (h₁y i hi).differentiableAt

Depends on / 依赖: AnalyticAt, Finset, Finset.prod_fn, Finset.sum_apply, analyticAt_mem_codiscreteWithin, codiscreteWithin, differentiableAt, eventually_all_finset, eventually_codiscreteWithin_apply_ne_zero, filter_upwards, logDeriv_prod, prod_fn, sum_apply
-/
theorem MeromorphicOn.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι -> 𝕜 -> 𝕜'}
    (h : forall i in s, MeromorphicOn (F i) U)
    (h' : forall i in s, forall x in U, meromorphicOrderAt (F i) x != ⊤) :
    logDeriv (∏ i in s, F i) =ᶠ[codiscreteWithin U] ∑ i in s, logDeriv (F i) := by
  have hA : forallᶠ y in codiscreteWithin U, forall i in s, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset s).2 fun i hi => (h i hi).analyticAt_mem_codiscreteWithin
  have hN : forallᶠ y in codiscreteWithin U, forall i in s, F i y != 0 :=
    (eventually_all_finset s).2 fun i hi => (h i hi).eventually_codiscreteWithin_apply_ne_zero
      (h' i hi)
  filter_upwards [hA, hN] with y h₁y h₂y
  rw [Finset.sum_apply]; rw [Finset.prod_fn]
  exact logDeriv_prod h₂y fun i hi => (h₁y i hi).differentiableAt

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun Meromorphic.logDeriv_fun_prod_eventuallyEq]
/--
theorem `Meromorphic.logDeriv_prod_eventuallyEq` / 定理 `Meromorphic.logDeriv_prod_eventuallyEq`

English:
theorem Meromorphic.logDeriv_prod_eventuallyEq
  statement: {ι : Type*} {s : Finset ι} {F : ι -> 𝕜 -> 𝕜'}
  proof: by
  apply MeromorphicOn.logDeriv_prod_eventuallyEq (fun i hi => meromorphicOn_univ.mpr (h i hi))
  aesop

中文:
定理 亚纯.logDeriv_prod_eventuallyEq
  结论: {ι : 类型} {s : 有限集 ι} {F : ι -> 𝕜 -> 𝕜'}
  证明: by
  apply MeromorphicOn.logDeriv_prod_eventuallyEq (fun i hi => meromorphicOn_univ.mpr (h i hi))
  aesop

Depends on / 依赖: MeromorphicOn, MeromorphicOn.logDeriv_prod_eventuallyEq, logDeriv_prod_eventuallyEq, meromorphicOn_univ, meromorphicOn_univ.mpr
-/
theorem Meromorphic.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι -> 𝕜 -> 𝕜'}
    (h : forall i in s, Meromorphic (F i)) (h' : forall i in s, forall x, meromorphicOrderAt (F i) x != ⊤) :
    logDeriv (∏ i in s, F i) =ᶠ[codiscrete 𝕜] ∑ i in s, logDeriv (F i) := by
  apply MeromorphicOn.logDeriv_prod_eventuallyEq (fun i hi => meromorphicOn_univ.mpr (h i hi))
  aesop

/--
theorem `MeromorphicOn.logDeriv_finprod_eventuallyEq` / 定理 `MeromorphicOn.logDeriv_finprod_eventuallyEq`

English:
theorem MeromorphicOn.logDeriv_finprod_eventuallyEq
  statement: {ι : Type*} {F : ι -> 𝕜 -> 𝕜'}
  proof: by
  have hsub : support (fun i => logDeriv (F i)) subseteq hF.toFinset := by
    simp +contextual [Set.subset_def, not_imp_not, Pi.one_def]
  rw [finprod_eq_prod_of_mulSupport_subset F (s := hF.toFinset) (by simp)]; rw [finsum_eq_sum_of_support_subset _ hsub]
  exact logDeriv_prod_eventuallyEq (fun i _ => h i) (fun i _ => h' i)

中文:
定理 MeromorphicOn.logDeriv_finprod_eventuallyEq
  结论: {ι : 类型} {F : ι -> 𝕜 -> 𝕜'}
  证明: by
  have hsub : support (fun i => logDeriv (F i)) subseteq hF.toFinset := by
    simp +contextual [Set.subset_def, not_imp_not, Pi.one_def]
  rw [finprod_eq_prod_of_mulSupport_subset F (s := hF.toFinset) (by simp)]; rw [finsum_eq_sum_of_support_subset _ hsub]
  exact logDeriv_prod_eventuallyEq (fun i _ => h i) (fun i _ => h' i)

Depends on / 依赖: Pi.one_def, Set.subset_def, contextual, finprod_eq_prod_of_mulSupport_subset, finsum_eq_sum_of_support_subset, hF.toFinset, logDeriv, logDeriv_prod_eventuallyEq, not_imp_not, one_def, subset_def, subseteq, support, toFinset
-/
theorem MeromorphicOn.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -> 𝕜'}
    (hF : (mulSupport F).Finite) (h : forall i, MeromorphicOn (F i) U)
    (h' : forall i, forall x in U, meromorphicOrderAt (F i) x != ⊤) :
    logDeriv (∏ᶠ i, F i) =ᶠ[codiscreteWithin U] ∑ᶠ i, logDeriv (F i) := by
  have hsub : support (fun i => logDeriv (F i)) subseteq hF.toFinset := by
    simp +contextual [Set.subset_def, not_imp_not, Pi.one_def]
  rw [finprod_eq_prod_of_mulSupport_subset F (s := hF.toFinset) (by simp)]; rw [finsum_eq_sum_of_support_subset _ hsub]
  exact logDeriv_prod_eventuallyEq (fun i _ => h i) (fun i _ => h' i)

/--
theorem `Meromorphic.logDeriv_finprod_eventuallyEq` / 定理 `Meromorphic.logDeriv_finprod_eventuallyEq`

English:
theorem Meromorphic.logDeriv_finprod_eventuallyEq
  statement: {ι : Type*} {F : ι -> 𝕜 -> 𝕜'}
  proof: by
  apply MeromorphicOn.logDeriv_finprod_eventuallyEq hF (fun i => meromorphicOn_univ.mpr (h i))
  aesop

中文:
定理 亚纯.logDeriv_finprod_eventuallyEq
  结论: {ι : 类型} {F : ι -> 𝕜 -> 𝕜'}
  证明: by
  apply MeromorphicOn.logDeriv_finprod_eventuallyEq hF (fun i => meromorphicOn_univ.mpr (h i))
  aesop

Depends on / 依赖: MeromorphicOn, MeromorphicOn.logDeriv_finprod_eventuallyEq, logDeriv_finprod_eventuallyEq, meromorphicOn_univ, meromorphicOn_univ.mpr
-/
theorem Meromorphic.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -> 𝕜'}
    (hF : (mulSupport F).Finite) (h : forall i, Meromorphic (F i))
    (h' : forall i x, meromorphicOrderAt (F i) x != ⊤) :
    logDeriv (∏ᶠ i, F i) =ᶠ[codiscrete 𝕜] ∑ᶠ i, logDeriv (F i) := by
  apply MeromorphicOn.logDeriv_finprod_eventuallyEq hF (fun i => meromorphicOn_univ.mpr (h i))
  aesop

/--
Away from a codiscrete subset of `U`, the logarithmic derivative of the `n`-th power of a
meromorphic function is `n` times the logarithmic derivative.
-/
@[to_fun MeromorphicOn.logDeriv_fun_zpow_eventuallyEq]
/--
theorem `MeromorphicOn.logDeriv_zpow_eventuallyEq` / 定理 `MeromorphicOn.logDeriv_zpow_eventuallyEq`

English:
theorem MeromorphicOn.logDeriv_zpow_eventuallyEq
  given: (hf : MeromorphicOn f U) (n : Int)
  proof: by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with y hy
  rw [Pi.smul_apply]; rw [zsmul_eq_mul]; rw [show f ^ n = (f · ^ n) from rfl]
  exact logDeriv_fun_zpow hy.differentiableAt n

中文:
定理 MeromorphicOn.logDeriv_zpow_eventuallyEq
  条件: (hf : MeromorphicOn f U) (n : 整数)
  证明: by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with y hy
  rw [Pi.smul_apply]; rw [zsmul_eq_mul]; rw [show f ^ n = (f · ^ n) from rfl]
  exact logDeriv_fun_zpow hy.differentiableAt n

Depends on / 依赖: Pi.smul_apply, analyticAt_mem_codiscreteWithin, differentiableAt, filter_upwards, hf.analyticAt_mem_codiscreteWithin, hy.differentiableAt, logDeriv_fun_zpow, smul_apply, zsmul_eq_mul
-/
theorem MeromorphicOn.logDeriv_zpow_eventuallyEq (hf : MeromorphicOn f U) (n : Int) :
    logDeriv (f ^ n) =ᶠ[codiscreteWithin U] n • logDeriv f := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with y hy
  rw [Pi.smul_apply]; rw [zsmul_eq_mul]; rw [show f ^ n = (f · ^ n) from rfl]
  exact logDeriv_fun_zpow hy.differentiableAt n

/--
Away from a codiscrete subset of `𝕜`, the logarithmic derivative of the `n`-th power of a
meromorphic function is `n` times the logarithmic derivative.
-/
@[to_fun Meromorphic.logDeriv_fun_zpow_eventuallyEq]
/--
theorem `Meromorphic.logDeriv_zpow_eventuallyEq` / 定理 `Meromorphic.logDeriv_zpow_eventuallyEq`

English:
theorem Meromorphic.logDeriv_zpow_eventuallyEq
  given: (hf : Meromorphic f) (n : Int)
  proof: by
  apply MeromorphicOn.logDeriv_zpow_eventuallyEq (meromorphicOn_univ.mpr hf)

中文:
定理 亚纯.logDeriv_zpow_eventuallyEq
  条件: (hf : 亚纯 f) (n : 整数)
  证明: by
  apply MeromorphicOn.logDeriv_zpow_eventuallyEq (meromorphicOn_univ.mpr hf)

Depends on / 依赖: MeromorphicOn, MeromorphicOn.logDeriv_zpow_eventuallyEq, logDeriv_zpow_eventuallyEq, meromorphicOn_univ, meromorphicOn_univ.mpr
-/
theorem Meromorphic.logDeriv_zpow_eventuallyEq (hf : Meromorphic f) (n : Int) :
    logDeriv (f ^ n) =ᶠ[codiscrete 𝕜] n • logDeriv f := by
  apply MeromorphicOn.logDeriv_zpow_eventuallyEq (meromorphicOn_univ.mpr hf)


/--
theorem `MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq` / 定理 `MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq`

English:
theorem MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq
  statement: {ι : Type*} {F : ι -> 𝕜 -> 𝕜'} {d : ι -> Int}
  proof: by
  have hA : forallᶠ y in codiscreteWithin U, forall i in hd.toFinset, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset hd.toFinset).2 fun i _ => (h i).analyticAt_mem_codiscreteWithin
  have hN : forallᶠ y in codiscreteWithin U, forall i in hd.toFinset, F i y != 0 :=
    (eventually_all_finset hd.toFinset).2 fun i _ => (h i).eventually_codiscreteWithin_apply_ne_zero
      (h' i)
  filter_upwards [hA, hN] with y h₁y h₂y
  have h₀ : ∏ᶠ i, F i ^ d i = ∏ i in hd.toFinset, F i ^ d i :=
finprod_eq_prod_of_mulSupport_subset _ by simp +contextual [Set.subset_def, not_imp_not]
  have hsub : support (fun i => d i • logDeriv (F i) y) subseteq hd.toFinset := by
    simp +contextual [-support_mul, -mul_eq_zero, Set.subset_def, not_imp_not]
  calc logDeriv (∏ᶠ i, F i ^ d i) y
      = logDeriv (fun z => ∏ i in hd.toFinset, (F i ^ d i) z) y := by rw [h₀, Finset.prod_fn]
    _ = ∑ i in hd.toFinset, logDeriv (F i ^ d i) y :=
        logDeriv_prod (fun i hi => zpow_ne_zero _ (h₂y i hi))
          (fun i hi => ((h₁y i hi).zpow (h₂y i hi)).differentiableAt)
    _ = ∑ i in hd.toFinset, d i • logDeriv (F i) y := by
        congr! with i hi
        rw [zsmul_eq_mul]; rw [Pi.pow_def]
        exact logDeriv_fun_zpow (h₁y i hi).differentiableAt (d i)
    _ = ∑ᶠ i, d i • logDeriv (F i) y := (finsum_eq_sum_of_support_subset _ hsub).symm

中文:
定理 MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq
  结论: {ι : 类型} {F : ι -> 𝕜 -> 𝕜'} {d : ι -> 整数}
  证明: by
  have hA : forallᶠ y in codiscreteWithin U, forall i in hd.toFinset, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset hd.toFinset).2 fun i _ => (h i).analyticAt_mem_codiscreteWithin
  have hN : forallᶠ y in codiscreteWithin U, forall i in hd.toFinset, F i y != 0 :=
    (eventually_all_finset hd.toFinset).2 fun i _ => (h i).eventually_codiscreteWithin_apply_ne_zero
      (h' i)
  filter_upwards [hA, hN] with y h₁y h₂y
  have h₀ : ∏ᶠ i, F i ^ d i = ∏ i in hd.toFinset, F i ^ d i :=
finprod_eq_prod_of_mulSupport_subset _ by simp +contextual [Set.subset_def, not_imp_not]
  have hsub : support (fun i => d i • logDeriv (F i) y) subseteq hd.toFinset := by
    simp +contextual [-support_mul, -mul_eq_zero, Set.subset_def, not_imp_not]
  calc logDeriv (∏ᶠ i, F i ^ d i) y
      = logDeriv (fun z => ∏ i in hd.toFinset, (F i ^ d i) z) y := by rw [h₀, Finset.prod_fn]
    _ = ∑ i in hd.toFinset, logDeriv (F i ^ d i) y :=
        logDeriv_prod (fun i hi => zpow_ne_zero _ (h₂y i hi))
          (fun i hi => ((h₁y i hi).zpow (h₂y i hi)).differentiableAt)
    _ = ∑ i in hd.toFinset, d i • logDeriv (F i) y := by
        congr! with i hi
        rw [zsmul_eq_mul]; rw [Pi.pow_def]
        exact logDeriv_fun_zpow (h₁y i hi).differentiableAt (d i)
    _ = ∑ᶠ i, d i • logDeriv (F i) y := (finsum_eq_sum_of_support_subset _ hsub).symm

Depends on / 依赖: AnalyticAt, analyticAt_mem_codiscreteWithin, codiscreteWithin, eventually_all_finset, eventually_codiscreteWithin_apply_ne_zero, filter_upwards, finprod_eq_prod_of_mulSupport_su, hd.toFinset, toFinset
-/
theorem MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -> 𝕜'} {d : ι -> Int}
    (hd : (support d).Finite) (h : forall i, MeromorphicOn (F i) U)
    (h' : forall i, forall x in U, meromorphicOrderAt (F i) x != ⊤) :
    logDeriv (∏ᶠ i, F i ^ d i)
      =ᶠ[codiscreteWithin U] fun z => ∑ᶠ i, d i • logDeriv (F i) z := by
  have hA : forallᶠ y in codiscreteWithin U, forall i in hd.toFinset, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset hd.toFinset).2 fun i _ => (h i).analyticAt_mem_codiscreteWithin
  have hN : forallᶠ y in codiscreteWithin U, forall i in hd.toFinset, F i y != 0 :=
    (eventually_all_finset hd.toFinset).2 fun i _ => (h i).eventually_codiscreteWithin_apply_ne_zero
      (h' i)
  filter_upwards [hA, hN] with y h₁y h₂y
  have h₀ : ∏ᶠ i, F i ^ d i = ∏ i in hd.toFinset, F i ^ d i :=
finprod_eq_prod_of_mulSupport_subset _ by simp +contextual [Set.subset_def, not_imp_not]
  have hsub : support (fun i => d i • logDeriv (F i) y) subseteq hd.toFinset := by
    simp +contextual [-support_mul, -mul_eq_zero, Set.subset_def, not_imp_not]
  calc logDeriv (∏ᶠ i, F i ^ d i) y
      = logDeriv (fun z => ∏ i in hd.toFinset, (F i ^ d i) z) y := by rw [h₀, Finset.prod_fn]
    _ = ∑ i in hd.toFinset, logDeriv (F i ^ d i) y :=
        logDeriv_prod (fun i hi => zpow_ne_zero _ (h₂y i hi))
          (fun i hi => ((h₁y i hi).zpow (h₂y i hi)).differentiableAt)
    _ = ∑ i in hd.toFinset, d i • logDeriv (F i) y := by
        congr! with i hi
        rw [zsmul_eq_mul]; rw [Pi.pow_def]
        exact logDeriv_fun_zpow (h₁y i hi).differentiableAt (d i)
    _ = ∑ᶠ i, d i • logDeriv (F i) y := (finsum_eq_sum_of_support_subset _ hsub).symm

/--
theorem `Meromorphic.logDeriv_finprod_zpow_eventuallyEq` / 定理 `Meromorphic.logDeriv_finprod_zpow_eventuallyEq`

English:
theorem Meromorphic.logDeriv_finprod_zpow_eventuallyEq
  statement: {ι : Type*} {F : ι -> 𝕜 -> 𝕜'} {d : ι -> Int}
  proof: by
  apply MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hd (fun i => meromorphicOn_univ.mpr (h i))
  aesop

中文:
定理 亚纯.logDeriv_finprod_zpow_eventuallyEq
  结论: {ι : 类型} {F : ι -> 𝕜 -> 𝕜'} {d : ι -> 整数}
  证明: by
  apply MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hd (fun i => meromorphicOn_univ.mpr (h i))
  aesop

Depends on / 依赖: MeromorphicOn, MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq, logDeriv_finprod_zpow_eventuallyEq, meromorphicOn_univ, meromorphicOn_univ.mpr
-/
theorem Meromorphic.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -> 𝕜'} {d : ι -> Int}
    (hd : (support d).Finite) (h : forall i, Meromorphic (F i))
    (h' : forall i x, meromorphicOrderAt (F i) x != ⊤) :
    logDeriv (∏ᶠ i, F i ^ d i)
      =ᶠ[codiscrete 𝕜] fun z => ∑ᶠ i, d i • logDeriv (F i) z := by
  apply MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hd (fun i => meromorphicOn_univ.mpr (h i))
  aesop
