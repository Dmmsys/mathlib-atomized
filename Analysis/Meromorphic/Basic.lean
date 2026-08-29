/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Meromorphic functions

Main statements:

* `MeromorphicAt`: definition of meromorphy at a point
* `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`: `f` is meromorphic at `z₀` iff we have
  `f z = (z - z₀) ^ n • g z` on a punctured neighborhood of `z₀`, for some `n : ℤ`
  and `g` analytic at `z₀`.
-/

@[expose] public section

open Filter Metric Set

open scoped Pointwise Topology

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]

/-- Meromorphy of `f` at `x` (more precisely, on a punctured neighbourhood of `x`; the value at
`x` itself is irrelevant). -/
@[fun_prop]
/--
Definition of `MeromorphicAt` / `MeromorphicAt` 的定义

English:
definition MeromorphicAt
  signature: (f : 𝕜 -> E) (x : 𝕜)
  body: exists (n : Nat), AnalyticAt 𝕜 (fun z => (z - x) ^ n • f z) x

@[fun_prop]

中文:
定义 MeromorphicAt
  签名: (f : 𝕜 -> E) (x : 𝕜)
  定义体: exists (n : Nat), AnalyticAt 𝕜 (fun z => (z - x) ^ n • f z) x

@[fun_prop]

Depends on / 依赖: AnalyticAt
-/
def MeromorphicAt (f : 𝕜 -> E) (x : 𝕜) :=
  exists (n : Nat), AnalyticAt 𝕜 (fun z => (z - x) ^ n • f z) x

@[fun_prop]
/--
lemma `AnalyticAt.meromorphicAt` / 引理 `AnalyticAt.meromorphicAt`

English:
lemma AnalyticAt.meromorphicAt
  given: {f : 𝕜 -> E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
  proof: ⟨0, by simpa only [pow_zero, one_smul]⟩

中文:
引理 AnalyticAt.meromorphicAt
  条件: {f : 𝕜 -> E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
  证明: ⟨0, by simpa only [pow_zero, one_smul]⟩

Depends on / 依赖: one_smul, pow_zero
-/
lemma AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    MeromorphicAt f x :=
  ⟨0, by simpa only [pow_zero, one_smul]⟩

/--
theorem `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero` / 定理 `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`

English:
theorem MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero
  statement: {f : 𝕜 -> E} {z₀ : 𝕜}
  proof: by
  obtain ⟨n, h⟩ := hf
  rcases h.eventually_eq_zero_or_eventually_ne_zero with h₁ | h₂
  · left
    filter_upwards [nhdsWithin_le_nhds h₁, self_mem_nhdsWithin] with y h₁y h₂y
    rw [Set.mem_compl_iff]; rw [Set.mem_singleton_iff]; rw [← sub_eq_zero] at h₂y
.mp h₁y exact smul_eq_zero_iff_right (po

中文:
定理 MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero
  结论: {f : 𝕜 -> E} {z₀ : 𝕜}
  证明: by
  obtain ⟨n, h⟩ := hf
  rcases h.eventually_eq_zero_or_eventually_ne_zero with h₁ | h₂
  · left
    filter_upwards [nhdsWithin_le_nhds h₁, self_mem_nhdsWithin] with y h₁y h₂y
    rw [Set.mem_compl_iff]; rw [Set.mem_singleton_iff]; rw [← sub_eq_zero] at h₂y
.mp h₁y exact smul_eq_zero_iff_right (po

Depends on / 依赖: Set.mem_compl_iff, Set.mem_singleton_iff, eventually_eq_zero_or_eventually_ne_zero, filter_upwards, h.eventually_eq_zero_or_eventually_ne_zero, mem_compl_iff, mem_singleton_iff, nhdsWithin_le_nhds, pow_ne_zero, self_mem_nhdsWithin, smul_eq_zero_iff_right, smul_ne_zero_iff, sub_eq_zero
-/
theorem MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero {f : 𝕜 -> E} {z₀ : 𝕜}
    (hf : MeromorphicAt f z₀) :
    (forallᶠ z in 𝓝[!=] z₀, f z = 0) ∨ (forallᶠ z in 𝓝[!=] z₀, f z != 0) := by
  obtain ⟨n, h⟩ := hf
  rcases h.eventually_eq_zero_or_eventually_ne_zero with h₁ | h₂
  · left
    filter_upwards [nhdsWithin_le_nhds h₁, self_mem_nhdsWithin] with y h₁y h₂y
    rw [Set.mem_compl_iff]; rw [Set.mem_singleton_iff]; rw [← sub_eq_zero] at h₂y
.mp h₁y exact smul_eq_zero_iff_right (pow_ne_zero n h₂y)
  · right
    filter_upwards [h₂, self_mem_nhdsWithin] with y h₁y h₂y
    exact (smul_ne_zero_iff.1 h₁y).2

namespace MeromorphicAt

variable {ι : Type*} {s : Finset ι} {F : ι -> 𝕜 -> 𝕜'} {G : ι -> 𝕜 -> E}

@[fun_prop]
/--
lemma `id` / 引理 `id`

English:
lemma id
  given: (x : 𝕜)
  statement: MeromorphicAt id x
  proof: analyticAt_id.meromorphicAt

@[fun_prop, simp]

中文:
引理 id
  条件: (x : 𝕜)
  结论: MeromorphicAt id x
  证明: analyticAt_id.meromorphicAt

@[fun_prop, simp]

Depends on / 依赖: analyticAt_id, analyticAt_id.meromorphicAt, meromorphicAt
-/
lemma id (x : 𝕜) : MeromorphicAt id x := analyticAt_id.meromorphicAt

@[fun_prop, simp]
/--
lemma `const` / 引理 `const`

English:
lemma const
  given: (e : E) (x : 𝕜)
  statement: MeromorphicAt (fun _ => e) x
  proof: analyticAt_const.meromorphicAt

中文:
引理 const
  条件: (e : E) (x : 𝕜)
  结论: MeromorphicAt (fun _ => e) x
  证明: analyticAt_const.meromorphicAt

Depends on / 依赖: analyticAt_const, analyticAt_const.meromorphicAt, meromorphicAt
-/
lemma const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) x :=
  analyticAt_const.meromorphicAt

variable {x : 𝕜}

@[to_fun (attr := fun_prop)]
/--
lemma `add` / 引理 `add`

English:
lemma add
  given: {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  proof: by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨max m n, ?_⟩
  have : (fun z => (z - x) ^ max m n • (f + g) z) = fun z => (z - x) ^ (max m n - m) •
      ((z - x) ^ m • f z) + (z - x) ^ (max m n - n) • ((z - x) ^ n • g z) := by
    simp_rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (N

中文:
引理 add
  条件: {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  证明: by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨max m n, ?_⟩
  have : (fun z => (z - x) ^ max m n • (f + g) z) = fun z => (z - x) ^ (max m n - m) •
      ((z - x) ^ m • f z) + (z - x) ^ (max m n - n) • ((z - x) ^ n • g z) := by
    simp_rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (N

Depends on / 依赖: Nat.le_max_left, Nat.le_max_right, Nat.sub_add_cancel, Pi.add_apply, add_apply, analyticAt_const, analyticAt_id, analyticAt_id.sub, le_max_left, le_max_right, mul_smul, pow_add, simp_rw, smul_add, sub_add_cancel
-/
lemma add {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨max m n, ?_⟩
  have : (fun z => (z - x) ^ max m n • (f + g) z) = fun z => (z - x) ^ (max m n - m) •
      ((z - x) ^ m • f z) + (z - x) ^ (max m n - n) • ((z - x) ^ n • g z) := by
    simp_rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (Nat.le_max_left _ _),
      Nat.sub_add_cancel (Nat.le_max_right _ _), Pi.add_apply, smul_add]
  rw [this]
  exact (((analyticAt_id.sub analyticAt_const).pow _).smul hf).add
    (((analyticAt_id.sub analyticAt_const).pow _).smul hg)

@[to_fun (attr := fun_prop)]
/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  statement: [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E]
  proof: by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨m + n, ?_⟩
  convert hf.smul hg with z
  rw [Pi.smul_apply']; rw [Pi.smul_apply']; rw [smul_smul_smul_comm]; rw [smul_eq_mul]; rw [pow_add]

@[to_fun (attr := fun_prop)]

中文:
引理 smul
  结论: [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E]
  证明: by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨m + n, ?_⟩
  convert hf.smul hg with z
  rw [Pi.smul_apply']; rw [Pi.smul_apply']; rw [smul_smul_smul_comm]; rw [smul_eq_mul]; rw [pow_add]

@[to_fun (attr := fun_prop)]

Depends on / 依赖: Pi.smul_apply, convert, hf.smul, pow_add, smul_apply, smul_eq_mul, smul_smul_smul_comm
-/
lemma smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E]
    {f : 𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f • g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨m + n, ?_⟩
  convert hf.smul hg with z
  rw [Pi.smul_apply']; rw [Pi.smul_apply']; rw [smul_smul_smul_comm]; rw [smul_eq_mul]; rw [pow_add]

@[to_fun (attr := fun_prop)]
/--
lemma `const_smul` / 引理 `const_smul`

English:
lemma const_smul
  given: [SMulCommClass 𝕜 R E] {x : 𝕜} {f : 𝕜 -> E} (hf : MeromorphicAt f x) (c : R)
  proof: by
  rcases hf with ⟨m, hf⟩
  exact ⟨m, by simpa [smul_comm _ c _] using hf.fun_const_smul⟩

@[to_fun (attr := fun_prop)]

中文:
引理 const_smul
  条件: [SMulCommClass 𝕜 R E] {x : 𝕜} {f : 𝕜 -> E} (hf : MeromorphicAt f x) (c : R)
  证明: by
  rcases hf with ⟨m, hf⟩
  exact ⟨m, by simpa [smul_comm _ c _] using hf.fun_const_smul⟩

@[to_fun (attr := fun_prop)]

Depends on / 依赖: fun_const_smul, hf.fun_const_smul, smul_comm
-/
lemma const_smul [SMulCommClass 𝕜 R E] {x : 𝕜} {f : 𝕜 -> E} (hf : MeromorphicAt f x) (c : R) :
    MeromorphicAt (c • f) x := by
  rcases hf with ⟨m, hf⟩
  exact ⟨m, by simpa [smul_comm _ c _] using hf.fun_const_smul⟩

@[to_fun (attr := fun_prop)]
/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  given: {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  proof: by
  simpa using hf.smul hg

中文:
引理 mul
  条件: {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  证明: by
  simpa using hf.smul hg

Depends on / 依赖: hf.smul
-/
lemma mul {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f * g) x := by
  simpa using hf.smul hg

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop] -- TODO: to_fun generates an unreadable statement, see #32866
/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  given: (hf : forall σ in s, MeromorphicAt (F σ) x)
  proof: by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.prod_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).mul
      (hs (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

中文:
定理 prod
  条件: (hf : 对任意 σ in s, MeromorphicAt (F σ) x)
  证明: by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.prod_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).mul
      (hs (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_empty, Finset.prod_insert, MeromorphicAt, MeromorphicAt.const, classical, insert, mem_insert_of_mem, mem_insert_self, prod_empty, prod_insert
-/
theorem prod (hf : forall σ in s, MeromorphicAt (F σ) x) :
    MeromorphicAt (∏ i in s, F i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.prod_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).mul
      (hs (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop]
/--
theorem `fun_prod` / 定理 `fun_prod`

English:
theorem fun_prod
  given: (h : forall σ in s, MeromorphicAt (F σ) x)
  proof: by
  convert! prod h (s := s)
  simp

中文:
定理 fun_prod
  条件: (h : 对任意 σ in s, MeromorphicAt (F σ) x)
  证明: by
  convert! prod h (s := s)
  simp

Depends on / 依赖: convert
-/
theorem fun_prod (h : forall σ in s, MeromorphicAt (F σ) x) :
    MeromorphicAt (fun z => ∏ n in s, F n z) x := by
  convert! prod h (s := s)
  simp

/-- Finprods of meromorphic functions are meromorphic. -/
@[fun_prop]
/--
theorem `finprod` / 定理 `finprod`

English:
theorem finprod
  given: {x : 𝕜} (hf : forall i, MeromorphicAt (F i) x)
  proof: by
  by_cases h₂f : Function.HasFiniteMulSupport F
  · simpa [finprod_eq_prod F h₂f] using prod (by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₂f ▸ const (1 : 𝕜') x

中文:
定理 finprod
  条件: {x : 𝕜} (hf : 对任意 i, MeromorphicAt (F i) x)
  证明: by
  by_cases h₂f : Function.HasFiniteMulSupport F
  · simpa [finprod_eq_prod F h₂f] using prod (by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₂f ▸ const (1 : 𝕜') x

Depends on / 依赖: Function, Function.HasFiniteMulSupport, HasFiniteMulSupport, finprod_eq_prod, finprod_of_not_hasFiniteMulSupport
-/
theorem finprod {x : 𝕜} (hf : forall i, MeromorphicAt (F i) x) :
    MeromorphicAt (∏ᶠ i, F i) x := by
  by_cases h₂f : Function.HasFiniteMulSupport F
  · simpa [finprod_eq_prod F h₂f] using prod (by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₂f ▸ const (1 : 𝕜') x

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop] -- TODO: to_fun generates an unreadable statement, see #32866
/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  given: (h : forall σ in s, MeromorphicAt (G σ) x)
  proof: by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticAt_const.meromorphicAt
  | insert σ s hσ hind =>
    rw [Finset.sum_insert hσ]
    apply (h σ (Finset.mem_insert_self σ s)).add
      (hind (fun τ hτ => h τ (Finset.mem_insert_of_

中文:
定理 sum
  条件: (h : 对任意 σ in s, MeromorphicAt (G σ) x)
  证明: by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticAt_const.meromorphicAt
  | insert σ s hσ hind =>
    rw [Finset.sum_insert hσ]
    apply (h σ (Finset.mem_insert_self σ s)).add
      (hind (fun τ hτ => h τ (Finset.mem_insert_of_

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.sum_empty, Finset.sum_insert, analyticAt_const, analyticAt_const.meromorphicAt, classical, insert, mem_insert_of_mem, mem_insert_self, meromorphicAt, sum_empty, sum_insert
-/
theorem sum (h : forall σ in s, MeromorphicAt (G σ) x) :
    MeromorphicAt (∑ n in s, G n) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticAt_const.meromorphicAt
  | insert σ s hσ hind =>
    rw [Finset.sum_insert hσ]
    apply (h σ (Finset.mem_insert_self σ s)).add
      (hind (fun τ hτ => h τ (Finset.mem_insert_of_mem hτ)))

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
/--
theorem `fun_sum` / 定理 `fun_sum`

English:
theorem fun_sum
  given: (h : forall σ in s, MeromorphicAt (G σ) x)
  proof: by
  convert! sum h (s := s)
  simp

中文:
定理 fun_sum
  条件: (h : 对任意 σ in s, MeromorphicAt (G σ) x)
  证明: by
  convert! sum h (s := s)
  simp

Depends on / 依赖: convert
-/
theorem fun_sum (h : forall σ in s, MeromorphicAt (G σ) x) :
    MeromorphicAt (fun z => ∑ n in s, G n z) x := by
  convert! sum h (s := s)
  simp

/-- Finsums of meromorphic functions are meromorphic. -/
@[fun_prop]
/--
theorem `finsum` / 定理 `finsum`

English:
theorem finsum
  given: (hF : forall i, MeromorphicAt (F i) x)
  proof: by
  by_cases h₂f : Function.HasFiniteSupport F
  · simpa [finsum_eq_sum F h₂f] using sum (by aesop)
  · exact finsum_of_not_hasFiniteSupport h₂f ▸ const (0 : 𝕜') x

@[to_fun (attr := fun_prop)]

中文:
定理 finsum
  条件: (hF : 对任意 i, MeromorphicAt (F i) x)
  证明: by
  by_cases h₂f : Function.HasFiniteSupport F
  · simpa [finsum_eq_sum F h₂f] using sum (by aesop)
  · exact finsum_of_not_hasFiniteSupport h₂f ▸ const (0 : 𝕜') x

@[to_fun (attr := fun_prop)]

Depends on / 依赖: Function, Function.HasFiniteSupport, HasFiniteSupport, finsum_eq_sum, finsum_of_not_hasFiniteSupport
-/
theorem finsum (hF : forall i, MeromorphicAt (F i) x) :
    MeromorphicAt (∑ᶠ i, F i) x := by
  by_cases h₂f : Function.HasFiniteSupport F
  · simpa [finsum_eq_sum F h₂f] using sum (by aesop)
  · exact finsum_of_not_hasFiniteSupport h₂f ▸ const (0 : 𝕜') x

@[to_fun (attr := fun_prop)]
/--
lemma `neg` / 引理 `neg`

English:
lemma neg
  given: {f : 𝕜 -> E} (hf : MeromorphicAt f x)
  statement: MeromorphicAt (-f) x
  proof: by
  convert (MeromorphicAt.const (-1 : 𝕜) x).smul hf
  ext1 z
  simp only [Pi.neg_apply, Pi.smul_apply', neg_smul, one_smul]

@[simp]

中文:
引理 neg
  条件: {f : 𝕜 -> E} (hf : MeromorphicAt f x)
  结论: MeromorphicAt (-f) x
  证明: by
  convert (MeromorphicAt.const (-1 : 𝕜) x).smul hf
  ext1 z
  simp only [Pi.neg_apply, Pi.smul_apply', neg_smul, one_smul]

@[simp]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.const, Pi.neg_apply, Pi.smul_apply, convert, neg_apply, neg_smul, one_smul, smul_apply
-/
lemma neg {f : 𝕜 -> E} (hf : MeromorphicAt f x) : MeromorphicAt (-f) x := by
  convert (MeromorphicAt.const (-1 : 𝕜) x).smul hf
  ext1 z
  simp only [Pi.neg_apply, Pi.smul_apply', neg_smul, one_smul]

@[simp]
/--
lemma `neg_iff` / 引理 `neg_iff`

English:
lemma neg_iff
  given: {f : 𝕜 -> E}
  proof: ⟨fun h => by simpa only [neg_neg] using h.neg, MeromorphicAt.neg⟩

@[to_fun (attr := fun_prop)]

中文:
引理 neg_iff
  条件: {f : 𝕜 -> E}
  证明: ⟨fun h => by simpa only [neg_neg] using h.neg, MeromorphicAt.neg⟩

@[to_fun (attr := fun_prop)]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.neg, h.neg, neg_neg
-/
lemma neg_iff {f : 𝕜 -> E} :
    MeromorphicAt (-f) x ↔ MeromorphicAt f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, MeromorphicAt.neg⟩

@[to_fun (attr := fun_prop)]
/--
lemma `sub` / 引理 `sub`

English:
lemma sub
  given: {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  proof: by
  convert hf.add hg.neg
  ext1 z
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

中文:
引理 sub
  条件: {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  证明: by
  convert hf.add hg.neg
  ext1 z
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

Depends on / 依赖: Pi.add_apply, Pi.neg_apply, Pi.sub_apply, add_apply, convert, hf.add, hg.neg, neg_apply, simp_rw, sub_apply, sub_eq_add_neg
-/
lemma sub {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x := by
  convert hf.add hg.neg
  ext1 z
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

/--
lemma `meromorphicAt_add_iff_meromorphicAt₁` / 引理 `meromorphicAt_add_iff_meromorphicAt₁`

English:
lemma meromorphicAt_add_iff_meromorphicAt₁
  given: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  proof: by
  exact ⟨fun h => by simpa using h.sub hf, fun _ => by fun_prop⟩

中文:
引理 meromorphicAt_add_iff_meromorphicAt₁
  条件: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  证明: by
  exact ⟨fun h => by simpa using h.sub hf, fun _ => by fun_prop⟩

Depends on / 依赖: algebraMapCoe, fun_prop, h.sub
-/
lemma meromorphicAt_add_iff_meromorphicAt₁ {f g : 𝕜 -> E} (hf : MeromorphicAt f x) :
    MeromorphicAt (f + g) x ↔ MeromorphicAt g x := by
  exact ⟨fun h => by simpa using h.sub hf, fun _ => by fun_prop⟩

/--
lemma `meromorphicAt_fun_add_iff_meromorphicAt₁` / 引理 `meromorphicAt_fun_add_iff_meromorphicAt₁`

English:
lemma meromorphicAt_fun_add_iff_meromorphicAt₁
  given: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  proof: meromorphicAt_add_iff_meromorphicAt₁ hf

中文:
引理 meromorphicAt_fun_add_iff_meromorphicAt₁
  条件: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  证明: meromorphicAt_add_iff_meromorphicAt₁ hf
-/
lemma meromorphicAt_fun_add_iff_meromorphicAt₁ {f g : 𝕜 -> E} (hf : MeromorphicAt f x) :
    MeromorphicAt (fun z => f z + g z) x ↔ MeromorphicAt g x :=
  meromorphicAt_add_iff_meromorphicAt₁ hf

/--
lemma `meromorphicAt_add_iff_meromorphicAt₂` / 引理 `meromorphicAt_add_iff_meromorphicAt₂`

English:
lemma meromorphicAt_add_iff_meromorphicAt₂
  given: {f g : 𝕜 -> E} (hg : MeromorphicAt g x)
  proof: by
  rw [add_comm]
  exact meromorphicAt_add_iff_meromorphicAt₁ hg

中文:
引理 meromorphicAt_add_iff_meromorphicAt₂
  条件: {f g : 𝕜 -> E} (hg : MeromorphicAt g x)
  证明: by
  rw [add_comm]
  exact meromorphicAt_add_iff_meromorphicAt₁ hg

Depends on / 依赖: add_comm
-/
lemma meromorphicAt_add_iff_meromorphicAt₂ {f g : 𝕜 -> E} (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x ↔ MeromorphicAt f x := by
  rw [add_comm]
  exact meromorphicAt_add_iff_meromorphicAt₁ hg

/--
lemma `meromorphicAt_fun_add_iff_meromorphicAt₂` / 引理 `meromorphicAt_fun_add_iff_meromorphicAt₂`

English:
lemma meromorphicAt_fun_add_iff_meromorphicAt₂
  given: {f g : 𝕜 -> E} (hg : MeromorphicAt g x)
  proof: meromorphicAt_add_iff_meromorphicAt₂ hg

中文:
引理 meromorphicAt_fun_add_iff_meromorphicAt₂
  条件: {f g : 𝕜 -> E} (hg : MeromorphicAt g x)
  证明: meromorphicAt_add_iff_meromorphicAt₂ hg
-/
lemma meromorphicAt_fun_add_iff_meromorphicAt₂ {f g : 𝕜 -> E} (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z => f z + g z) x ↔ MeromorphicAt f x :=
  meromorphicAt_add_iff_meromorphicAt₂ hg

/--
lemma `meromorphicAt_sub_iff_meromorphicAt₁` / 引理 `meromorphicAt_sub_iff_meromorphicAt₁`

English:
lemma meromorphicAt_sub_iff_meromorphicAt₁
  given: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  proof: by
  exact ⟨fun h => by simpa using h.sub hf, fun _ => by fun_prop⟩

中文:
引理 meromorphicAt_sub_iff_meromorphicAt₁
  条件: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  证明: by
  exact ⟨fun h => by simpa using h.sub hf, fun _ => by fun_prop⟩

Depends on / 依赖: fun_prop, h.sub
-/
lemma meromorphicAt_sub_iff_meromorphicAt₁ {f g : 𝕜 -> E} (hf : MeromorphicAt f x) :
    MeromorphicAt (f - g) x ↔ MeromorphicAt g x := by
  exact ⟨fun h => by simpa using h.sub hf, fun _ => by fun_prop⟩

/--
lemma `meromorphicAt_fun_sub_iff_meromorphicAt₁` / 引理 `meromorphicAt_fun_sub_iff_meromorphicAt₁`

English:
lemma meromorphicAt_fun_sub_iff_meromorphicAt₁
  given: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  proof: meromorphicAt_sub_iff_meromorphicAt₁ hf

中文:
引理 meromorphicAt_fun_sub_iff_meromorphicAt₁
  条件: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  证明: meromorphicAt_sub_iff_meromorphicAt₁ hf
-/
lemma meromorphicAt_fun_sub_iff_meromorphicAt₁ {f g : 𝕜 -> E} (hf : MeromorphicAt f x) :
    MeromorphicAt (fun z => f z - g z) x ↔ MeromorphicAt g x :=
  meromorphicAt_sub_iff_meromorphicAt₁ hf

/--
lemma `meromorphicAt_sub_iff_meromorphicAt₂` / 引理 `meromorphicAt_sub_iff_meromorphicAt₂`

English:
lemma meromorphicAt_sub_iff_meromorphicAt₂
  given: {f g : 𝕜 -> E} (hg : MeromorphicAt g x)
  proof: by
  exact ⟨fun h => by simpa using h.add hg, fun _ => by fun_prop⟩

中文:
引理 meromorphicAt_sub_iff_meromorphicAt₂
  条件: {f g : 𝕜 -> E} (hg : MeromorphicAt g x)
  证明: by
  exact ⟨fun h => by simpa using h.add hg, fun _ => by fun_prop⟩

Depends on / 依赖: fun_prop, h.add
-/
lemma meromorphicAt_sub_iff_meromorphicAt₂ {f g : 𝕜 -> E} (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x ↔ MeromorphicAt f x := by
  exact ⟨fun h => by simpa using h.add hg, fun _ => by fun_prop⟩

/--
lemma `meromorphicAt_fun_sub_iff_meromorphicAt₂` / 引理 `meromorphicAt_fun_sub_iff_meromorphicAt₂`

English:
lemma meromorphicAt_fun_sub_iff_meromorphicAt₂
  given: {f g : 𝕜 -> E} (hg : MeromorphicAt g x)
  proof: meromorphicAt_sub_iff_meromorphicAt₂ hg

中文:
引理 meromorphicAt_fun_sub_iff_meromorphicAt₂
  条件: {f g : 𝕜 -> E} (hg : MeromorphicAt g x)
  证明: meromorphicAt_sub_iff_meromorphicAt₂ hg
-/
lemma meromorphicAt_fun_sub_iff_meromorphicAt₂ {f g : 𝕜 -> E} (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z => f z - g z) x ↔ MeromorphicAt f x :=
  meromorphicAt_sub_iff_meromorphicAt₂ hg

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[!=] x] g)
  proof: by
  rcases hf with ⟨m, hf⟩
  refine ⟨m + 1, ?_⟩
  have : AnalyticAt 𝕜 (fun z => z - x) x := by fun_prop
  refine (this.fun_smul hf).congr ?_
  rw [eventuallyEq_nhdsWithin_iff] at hfg
  filter_upwards [hfg] with z hz
  rcases eq_or_ne z x with rfl | hn
  · simp
  · rw [hz (Set.mem_compl_singleton_if

中文:
引理 congr
  条件: {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[!=] x] g)
  证明: by
  rcases hf with ⟨m, hf⟩
  refine ⟨m + 1, ?_⟩
  have : AnalyticAt 𝕜 (fun z => z - x) x := by fun_prop
  refine (this.fun_smul hf).congr ?_
  rw [eventuallyEq_nhdsWithin_iff] at hfg
  filter_upwards [hfg] with z hz
  rcases eq_or_ne z x with rfl | hn
  · simp
  · rw [hz (Set.mem_compl_singleton_if

Depends on / 依赖: AnalyticAt, Set.mem_compl_singleton_iff.mp, eq_or_ne, eventuallyEq_nhdsWithin_iff, filter_upwards, fun_prop, fun_smul, mem_compl_singleton_iff, mul_smul, pow_succ, this.fun_smul
-/
lemma congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[!=] x] g) :
    MeromorphicAt g x := by
  rcases hf with ⟨m, hf⟩
  refine ⟨m + 1, ?_⟩
  have : AnalyticAt 𝕜 (fun z => z - x) x := by fun_prop
  refine (this.fun_smul hf).congr ?_
  rw [eventuallyEq_nhdsWithin_iff] at hfg
  filter_upwards [hfg] with z hz
  rcases eq_or_ne z x with rfl | hn
  · simp
  · rw [hz (Set.mem_compl_singleton_iff.mp hn), pow_succ', mul_smul]

/--
lemma `meromorphicAt_congr` / 引理 `meromorphicAt_congr`

English:
lemma meromorphicAt_congr
  given: {f g : 𝕜 -> E} (h : f =ᶠ[𝓝[!=] x] g)
  proof: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

@[simp]

中文:
引理 meromorphicAt_congr
  条件: {f g : 𝕜 -> E} (h : f =ᶠ[𝓝[!=] x] g)
  证明: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

@[simp]

Depends on / 依赖: h.symm, hf.congr, hg.congr
-/
lemma meromorphicAt_congr {f g : 𝕜 -> E} (h : f =ᶠ[𝓝[!=] x] g) :
    MeromorphicAt f x ↔ MeromorphicAt g x :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

@[simp]
/--
lemma `update_iff` / 引理 `update_iff`

English:
lemma update_iff
  given: [DecidableEq 𝕜] {f : 𝕜 -> E} {z w : 𝕜} {e : E}
  proof: meromorphicAt_congr (Function.update_eventuallyEq_nhdsNE f w z e)

@[fun_prop]

中文:
引理 update_iff
  条件: [DecidableEq 𝕜] {f : 𝕜 -> E} {z w : 𝕜} {e : E}
  证明: meromorphicAt_congr (Function.update_eventuallyEq_nhdsNE f w z e)

@[fun_prop]

Depends on / 依赖: Function, Function.update_eventuallyEq_nhdsNE, meromorphicAt_congr, update_eventuallyEq_nhdsNE
-/
lemma update_iff [DecidableEq 𝕜] {f : 𝕜 -> E} {z w : 𝕜} {e : E} :
    MeromorphicAt (Function.update f w e) z ↔ MeromorphicAt f z :=
  meromorphicAt_congr (Function.update_eventuallyEq_nhdsNE f w z e)

@[fun_prop]
/--
lemma `update` / 引理 `update`

English:
lemma update
  given: [DecidableEq 𝕜] {f : 𝕜 -> E} {z} (hf : MeromorphicAt f z) (w e)
  proof: update_iff.mpr hf

@[to_fun (attr := fun_prop)]

中文:
引理 update
  条件: [DecidableEq 𝕜] {f : 𝕜 -> E} {z} (hf : MeromorphicAt f z) (w e)
  证明: update_iff.mpr hf

@[to_fun (attr := fun_prop)]

Depends on / 依赖: update_iff, update_iff.mpr
-/
lemma update [DecidableEq 𝕜] {f : 𝕜 -> E} {z} (hf : MeromorphicAt f z) (w e) :
    MeromorphicAt (Function.update f w e) z :=
  update_iff.mpr hf

@[to_fun (attr := fun_prop)]
/--
lemma `inv` / 引理 `inv`

English:
lemma inv
  given: {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
  statement: MeromorphicAt f⁻¹ x
  proof: by
  rcases hf with ⟨m, hf⟩
  by_cases h_eq : (fun z => (z - x) ^ m • f z) =ᶠ[𝓝 x] 0
  · -- silly case: f locally 0 near x
    refine (MeromorphicAt.const 0 x).congr ?_
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [h_eq] with z hfz hz
    rw [Pi.inv_apply]; rw [(smul_eq_zero_iff_right <| 

中文:
引理 inv
  条件: {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
  结论: MeromorphicAt f⁻¹ x
  证明: by
  rcases hf with ⟨m, hf⟩
  by_cases h_eq : (fun z => (z - x) ^ m • f z) =ᶠ[𝓝 x] 0
  · -- silly case: f locally 0 near x
    refine (MeromorphicAt.const 0 x).congr ?_
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [h_eq] with z hfz hz
    rw [Pi.inv_apply]; rw [(smul_eq_zero_iff_right <| 

Depends on / 依赖: AnalyticAt, MeromorphicAt, MeromorphicAt.const, Pi.inv_apply, eventuallyEq_nhdsWithin_iff, exists_eventuallyEq_pow_smul_nonzero_iff, filter_upwards, formula, h_eq, hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr, hg_an, hg_eq, hg_ne, interesting, inv_apply, inv_zero, locally, pow_ne_zero, smul_eq_zero_iff_right, sub_ne_zero
-/
lemma inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : MeromorphicAt f⁻¹ x := by
  rcases hf with ⟨m, hf⟩
  by_cases h_eq : (fun z => (z - x) ^ m • f z) =ᶠ[𝓝 x] 0
  · -- silly case: f locally 0 near x
    refine (MeromorphicAt.const 0 x).congr ?_
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [h_eq] with z hfz hz
    rw [Pi.inv_apply]; rw [(smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)).mp hfz]; rw [inv_zero]
  · -- interesting case: use local formula for `f`
    obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h_eq
    have : AnalyticAt 𝕜 (fun z => (z - x) ^ (m + 1)) x :=
      (analyticAt_id.sub analyticAt_const).pow _
    -- use `m + 1` rather than `m` to damp out any silly issues with the value at `z = x`
    refine ⟨n + 1, (this.fun_smul <| hg_an.inv hg_ne).congr ?_⟩
    filter_upwards [hg_eq, hg_an.continuousAt.eventually_ne hg_ne] with z hfg hg_ne'
    rcases eq_or_ne z x with rfl | hz_ne
    · simp
    · replace hfg := congr_arg (·⁻¹) hfg
      simp only [smul_inv₀] at hfg
      rw [inv_smul_eq_iff₀ (pow_ne_zero m (sub_ne_zero.mpr hz_ne))]; rw [smul_comm]; rw [eq_inv_smul_iff₀ (pow_ne_zero n (sub_ne_zero.mpr hz_ne))] at hfg
      simp [pow_succ', mul_smul, hfg]

@[simp]
/--
lemma `inv_iff` / 引理 `inv_iff`

English:
lemma inv_iff
  given: {f : 𝕜 -> 𝕜'}
  proof: ⟨fun h => by simpa only [inv_inv] using h.inv, MeromorphicAt.inv⟩

@[to_fun (attr := fun_prop)]

中文:
引理 inv_iff
  条件: {f : 𝕜 -> 𝕜'}
  证明: ⟨fun h => by simpa only [inv_inv] using h.inv, MeromorphicAt.inv⟩

@[to_fun (attr := fun_prop)]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.inv, h.inv, inv_inv
-/
lemma inv_iff {f : 𝕜 -> 𝕜'} :
    MeromorphicAt f⁻¹ x ↔ MeromorphicAt f x :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, MeromorphicAt.inv⟩

@[to_fun (attr := fun_prop)]
/--
lemma `div` / 引理 `div`

English:
lemma div
  given: {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  proof: (div_eq_mul_inv f g).symm ▸ (hf.mul hg.inv)

@[to_fun (attr := fun_prop)]

中文:
引理 div
  条件: {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  证明: (div_eq_mul_inv f g).symm ▸ (hf.mul hg.inv)

@[to_fun (attr := fun_prop)]

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
lemma div {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f / g) x :=
  (div_eq_mul_inv f g).symm ▸ (hf.mul hg.inv)

@[to_fun (attr := fun_prop)]
/--
lemma `pow` / 引理 `pow`

English:
lemma pow
  given: {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Nat)
  statement: MeromorphicAt (f ^ n) x
  proof: by
  induction n with
  | zero => simpa only [pow_zero] using! MeromorphicAt.const 1 x
  | succ m hm => simpa only [pow_succ] using! hm.mul hf

@[to_fun (attr := fun_prop)]

中文:
引理 pow
  条件: {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : 自然数)
  结论: MeromorphicAt (f ^ n) x
  证明: by
  induction n with
  | zero => simpa only [pow_zero] using! MeromorphicAt.const 1 x
  | succ m hm => simpa only [pow_succ] using! hm.mul hf

@[to_fun (attr := fun_prop)]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.const, hm.mul, pow_succ, pow_zero
-/
lemma pow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Nat) : MeromorphicAt (f ^ n) x := by
  induction n with
  | zero => simpa only [pow_zero] using! MeromorphicAt.const 1 x
  | succ m hm => simpa only [pow_succ] using! hm.mul hf

@[to_fun (attr := fun_prop)]
/--
lemma `zpow` / 引理 `zpow`

English:
lemma zpow
  given: {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int)
  statement: MeromorphicAt (f ^ n) x
  proof: by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow m
  | negSucc m => simpa only [zpow_negSucc, inv_iff] using hf.pow (m + 1)

中文:
引理 zpow
  条件: {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : 整数)
  结论: MeromorphicAt (f ^ n) x
  证明: by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow m
  | negSucc m => simpa only [zpow_negSucc, inv_iff] using hf.pow (m + 1)

Depends on / 依赖: Int.ofNat_eq_natCast, hf.pow, inv_iff, negSucc, ofNat_eq_natCast, zpow_natCast, zpow_negSucc
-/
lemma zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int) : MeromorphicAt (f ^ n) x := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow m
  | negSucc m => simpa only [zpow_negSucc, inv_iff] using hf.pow (m + 1)

/--
theorem `eventually_continuousAt` / 定理 `eventually_continuousAt`

English:
theorem eventually_continuousAt
  statement: {f : 𝕜 -> E}
  proof: by
  obtain ⟨n, h⟩ := h
  have : forallᶠ y in 𝓝[!=] x, ContinuousAt (fun z => (z - x) ^ n • f z) y :=
    nhdsWithin_le_nhds h.eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h'y
  have : ContinuousAt (fun z

中文:
定理 eventually_continuousAt
  结论: {f : 𝕜 -> E}
  证明: by
  obtain ⟨n, h⟩ := h
  have : forallᶠ y in 𝓝[!=] x, ContinuousAt (fun z => (z - x) ^ n • f z) y :=
    nhdsWithin_le_nhds h.eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h'y
  have : ContinuousAt (fun z

Depends on / 依赖: ContinuousAt, ContinuousAt.inv, Set.mem_compl_iff, Set.mem_singleton_iff, eventually_continuousAt, eventually_ne_nhds, filter_upwards, fun_prop, h.eventually_continuousAt, mem_compl_iff, mem_singleton_iff, nhdsWithin_le_nhds, self_mem_nhdsWithin, smul_smul, sub_eq_zero, this.smul
-/
theorem eventually_continuousAt {f : 𝕜 -> E}
    (h : MeromorphicAt f x) : forallᶠ y in 𝓝[!=] x, ContinuousAt f y := by
  obtain ⟨n, h⟩ := h
  have : forallᶠ y in 𝓝[!=] x, ContinuousAt (fun z => (z - x) ^ n • f z) y :=
    nhdsWithin_le_nhds h.eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h'y
  have : ContinuousAt (fun z => ((z - x) ^ n)⁻¹) y :=
    ContinuousAt.inv₀ (by fun_prop) (by simp [sub_eq_zero, h'y])
  apply (this.smul hy).congr
  filter_upwards [eventually_ne_nhds h'y] with z hz
  simp [smul_smul, hz, sub_eq_zero]

/--
theorem `eventually_analyticAt` / 定理 `eventually_analyticAt`

English:
theorem eventually_analyticAt
  statement: [CompleteSpace E] {f : 𝕜 -> E}
  proof: by
  obtain ⟨n, h⟩ := h
  apply AnalyticAt.eventually_analyticAt at h
  refine (h.filter_mono ?_).mp ?_
  · simp [nhdsWithin]
  · rw [eventually_nhdsWithin_iff]
    apply Filter.Eventually.of_forall
    intro y hy hf
    rw [Set.mem_compl_iff]; rw [Set.mem_singleton_iff] at hy
    have := ((analytic

中文:
定理 eventually_analyticAt
  结论: [CompleteSpace E] {f : 𝕜 -> E}
  证明: by
  obtain ⟨n, h⟩ := h
  apply AnalyticAt.eventually_analyticAt at h
  refine (h.filter_mono ?_).mp ?_
  · simp [nhdsWithin]
  · rw [eventually_nhdsWithin_iff]
    apply Filter.Eventually.of_forall
    intro y hy hf
    rw [Set.mem_compl_iff]; rw [Set.mem_singleton_iff] at hy
    have := ((analytic

Depends on / 依赖: AnalyticAt, AnalyticAt.eventually_analyticAt, Eventually, Filter, Filter.Eventually.of_forall, Set.mem_compl_iff, Set.mem_singleton_iff, analyticAt_const, analyticAt_id, eventually_analyticAt, eventually_ne_nhds, eventually_nhdsWithin_iff, filter_mono, h.filter_mono, mem_compl_iff, mem_singleton_iff, nhdsWithin, of_forall, pow_ne_zero, smul_smul
-/
theorem eventually_analyticAt [CompleteSpace E] {f : 𝕜 -> E}
    (h : MeromorphicAt f x) : forallᶠ y in 𝓝[!=] x, AnalyticAt 𝕜 f y := by
  obtain ⟨n, h⟩ := h
  apply AnalyticAt.eventually_analyticAt at h
  refine (h.filter_mono ?_).mp ?_
  · simp [nhdsWithin]
  · rw [eventually_nhdsWithin_iff]
    apply Filter.Eventually.of_forall
    intro y hy hf
    rw [Set.mem_compl_iff]; rw [Set.mem_singleton_iff] at hy
    have := ((analyticAt_id (𝕜 := 𝕜).sub analyticAt_const).pow n).inv
      (pow_ne_zero _ (sub_ne_zero_of_ne hy))
    apply (this.smul hf).congr ∘ (eventually_ne_nhds hy).mono
    intro z hz
    simp [smul_smul, hz, sub_eq_zero]

/--
lemma `iff_eventuallyEq_zpow_smul_analyticAt` / 引理 `iff_eventuallyEq_zpow_smul_analyticAt`

English:
lemma iff_eventuallyEq_zpow_smul_analyticAt
  given: {f : 𝕜 -> E}
  statement: MeromorphicAt f x ↔
  proof: by
  refine ⟨fun ⟨n, hn⟩ => ⟨-n, _, ⟨hn, eventually_nhdsWithin_iff.mpr ?_⟩⟩, ?_⟩
  · filter_upwards with z hz
    match_scalars
    simp [sub_ne_zero.mpr hz]
  · refine fun ⟨n, g, hg_an, hg_eq⟩ => MeromorphicAt.congr ?_ (EventuallyEq.symm hg_eq)
    exact (((MeromorphicAt.id x).sub (.const _ x)).zpo

中文:
引理 iff_eventuallyEq_zpow_smul_analyticAt
  条件: {f : 𝕜 -> E}
  结论: MeromorphicAt f x ↔
  证明: by
  refine ⟨fun ⟨n, hn⟩ => ⟨-n, _, ⟨hn, eventually_nhdsWithin_iff.mpr ?_⟩⟩, ?_⟩
  · filter_upwards with z hz
    match_scalars
    simp [sub_ne_zero.mpr hz]
  · refine fun ⟨n, g, hg_an, hg_eq⟩ => MeromorphicAt.congr ?_ (EventuallyEq.symm hg_eq)
    exact (((MeromorphicAt.id x).sub (.const _ x)).zpo

Depends on / 依赖: EventuallyEq, EventuallyEq.symm, MeromorphicAt, MeromorphicAt.congr, MeromorphicAt.id, eventually_nhdsWithin_iff, eventually_nhdsWithin_iff.mpr, filter_upwards, hg_an, hg_an.meromorphicAt, hg_eq, match_scalars, meromorphicAt, sub_ne_zero, sub_ne_zero.mpr
-/
lemma iff_eventuallyEq_zpow_smul_analyticAt {f : 𝕜 -> E} : MeromorphicAt f x ↔
    exists (n : Int) (g : 𝕜 -> E), AnalyticAt 𝕜 g x ∧ forallᶠ z in 𝓝[!=] x, f z = (z - x) ^ n • g z := by
  refine ⟨fun ⟨n, hn⟩ => ⟨-n, _, ⟨hn, eventually_nhdsWithin_iff.mpr ?_⟩⟩, ?_⟩
  · filter_upwards with z hz
    match_scalars
    simp [sub_ne_zero.mpr hz]
  · refine fun ⟨n, g, hg_an, hg_eq⟩ => MeromorphicAt.congr ?_ (EventuallyEq.symm hg_eq)
    exact (((MeromorphicAt.id x).sub (.const _ x)).zpow _).smul hg_an.meromorphicAt

/--
Derivatives of meromorphic functions are meromorphic.
-/
@[fun_prop]
/--
theorem `deriv` / 定理 `deriv`

English:
theorem deriv
  given: [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} (h : MeromorphicAt f x)
  proof: by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt] at h
  obtain ⟨n, g, h₁g, h₂g⟩ := h
  have : _root_.deriv (fun z => (z - x) ^ n • g z)
      =ᶠ[𝓝[!=] x] fun z => (n * (z - x) ^ (n - 1)) • g z + (z - x) ^ n • _root_.deriv g z := by
    filter_upwards [eventually_nhdsWithin_of_eventually

中文:
定理 deriv
  条件: [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} (h : MeromorphicAt f x)
  证明: by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt] at h
  obtain ⟨n, g, h₁g, h₂g⟩ := h
  have : _root_.deriv (fun z => (z - x) ^ n • g z)
      =ᶠ[𝓝[!=] x] fun z => (n * (z - x) ^ (n - 1)) • g z + (z - x) ^ n • _root_.deriv g z := by
    filter_upwards [eventually_nhdsWithin_of_eventually
-/
protected theorem deriv [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} (h : MeromorphicAt f x) :
    MeromorphicAt (deriv f) x := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt] at h
  obtain ⟨n, g, h₁g, h₂g⟩ := h
  have : _root_.deriv (fun z => (z - x) ^ n • g z)
      =ᶠ[𝓝[!=] x] fun z => (n * (z - x) ^ (n - 1)) • g z + (z - x) ^ n • _root_.deriv g z := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁g.eventually_analyticAt,
      eventually_nhdsWithin_of_forall fun _ a => a] with z₀ h₁ h₂
    rw [deriv_fun_smul (DifferentiableAt.zpow (by fun_prop) (by simp_all [sub_ne_zero_of_ne h₂]))
      (by fun_prop), add_comm, deriv_comp_sub_const (f := (· ^ n))]
    aesop
  rw [MeromorphicAt.meromorphicAt_congr (Filter.EventuallyEq.nhdsNE_deriv h₂g)]; rw [MeromorphicAt.meromorphicAt_congr this]
  fun_prop

/--
theorem `iterated_deriv` / 定理 `iterated_deriv`

English:
theorem iterated_deriv
  statement: [CompleteSpace E] {n : Nat} {f : 𝕜 -> E} {x : 𝕜}
  proof: by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

中文:
定理 iterated_deriv
  结论: [CompleteSpace E] {n : 自然数} {f : 𝕜 -> E} {x : 𝕜}
  证明: by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv
-/
@[fun_prop] theorem iterated_deriv [CompleteSpace E] {n : Nat} {f : 𝕜 -> E} {x : 𝕜}
    (h : MeromorphicAt f x) :
    MeromorphicAt (_root_.deriv^[n] f) x := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

/--
theorem `logDeriv` / 定理 `logDeriv`

English:
theorem logDeriv
  given: [CompleteSpace 𝕜'] {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
  proof: hf.deriv.div hf

中文:
定理 logDeriv
  条件: [CompleteSpace 𝕜'] {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
  证明: hf.deriv.div hf
-/
@[fun_prop] theorem logDeriv [CompleteSpace 𝕜'] {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) :
    MeromorphicAt (logDeriv f) x := hf.deriv.div hf

end MeromorphicAt

section smul_iff

variable {g : 𝕜 -> 𝕜} {x : 𝕜}

/--
lemma `meromorphicAt_smul_iff_of_ne_zero` / 引理 `meromorphicAt_smul_iff_of_ne_zero`

English:
lemma meromorphicAt_smul_iff_of_ne_zero
  given: {f : 𝕜 -> E} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0)
  proof: by
  refine ⟨fun hfg => ?_, hg.meromorphicAt.smul⟩
.congr ?_ refine (hg.inv hg').meromorphicAt.smul hfg
  filter_upwards [(hg.continuousAt.mono_left nhdsWithin_le_nhds).eventually_ne hg'] with z hz
  simp [inv_smul_smul₀ hz]

中文:
引理 meromorphicAt_smul_iff_of_ne_zero
  条件: {f : 𝕜 -> E} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0)
  证明: by
  refine ⟨fun hfg => ?_, hg.meromorphicAt.smul⟩
.congr ?_ refine (hg.inv hg').meromorphicAt.smul hfg
  filter_upwards [(hg.continuousAt.mono_left nhdsWithin_le_nhds).eventually_ne hg'] with z hz
  simp [inv_smul_smul₀ hz]

Depends on / 依赖: continuousAt, eventually_ne, filter_upwards, hg.continuousAt.mono_left, hg.inv, hg.meromorphicAt.smul, meromorphicAt, meromorphicAt.smul, mono_left, nhdsWithin_le_nhds
-/
lemma meromorphicAt_smul_iff_of_ne_zero {f : 𝕜 -> E} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0) :
    MeromorphicAt (g • f) x ↔ MeromorphicAt f x := by
  refine ⟨fun hfg => ?_, hg.meromorphicAt.smul⟩
.congr ?_ refine (hg.inv hg').meromorphicAt.smul hfg
  filter_upwards [(hg.continuousAt.mono_left nhdsWithin_le_nhds).eventually_ne hg'] with z hz
  simp [inv_smul_smul₀ hz]

/--
lemma `meromorphicAt_mul_iff_of_ne_zero` / 引理 `meromorphicAt_mul_iff_of_ne_zero`

English:
lemma meromorphicAt_mul_iff_of_ne_zero
  given: {f : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0)
  proof: meromorphicAt_smul_iff_of_ne_zero hg hg'

中文:
引理 meromorphicAt_mul_iff_of_ne_zero
  条件: {f : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0)
  证明: meromorphicAt_smul_iff_of_ne_zero hg hg'

Depends on / 依赖: meromorphicAt_smul_iff_of_ne_zero
-/
lemma meromorphicAt_mul_iff_of_ne_zero {f : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0) :
    MeromorphicAt (g * f) x ↔ MeromorphicAt f x :=
  meromorphicAt_smul_iff_of_ne_zero hg hg'

end smul_iff

section composition
/-!
### Composition with an analytic function
-/

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : 𝕜}

/-- The composition of a meromorphic and an analytic function is meromorphic. -/
@[fun_prop]
/--
lemma `MeromorphicAt.comp_analyticAt` / 引理 `MeromorphicAt.comp_analyticAt`

English:
lemma MeromorphicAt.comp_analyticAt
  statement: {f : 𝕜' -> F} {g : 𝕜 -> 𝕜'}
  proof: by
  obtain ⟨r, hr⟩ := hf
  by_cases hg' : analyticOrderAt (g · - g x) x = ⊤
  · -- trivial case: `g` is locally constant near `x`
    refine .congr (.const (f (g x)) x) ?_
    filter_upwards [nhdsWithin_le_nhds <| analyticOrderAt_eq_top.mp hg'] with z hz
    grind
  · -- interesting case: `g z - g 

中文:
引理 MeromorphicAt.comp_analyticAt
  结论: {f : 𝕜' -> F} {g : 𝕜 -> 𝕜'}
  证明: by
  obtain ⟨r, hr⟩ := hf
  by_cases hg' : analyticOrderAt (g · - g x) x = ⊤
  · -- trivial case: `g` is locally constant near `x`
    refine .congr (.const (f (g x)) x) ?_
    filter_upwards [nhdsWithin_le_nhds <| analyticOrderAt_eq_top.mp hg'] with z hz
    grind
  · -- interesting case: `g z - g 

Depends on / 依赖: WithTop, WithTop.ne_top_iff_exists.mp, analyticAt_const, analyticOrderAt, analyticOrderAt_eq_natCast, analyticOrderAt_eq_natCast.mp, analyticOrderAt_eq_top, analyticOrderAt_eq_top.mp, constant, filter_upwards, fun_sub, function, hg.fun_sub, hn.symm, interesting, locally, ne_top_iff_exists, nhdsWithin_le_nhds, vanishing
-/
lemma MeromorphicAt.comp_analyticAt {f : 𝕜' -> F} {g : 𝕜 -> 𝕜'}
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) :
    MeromorphicAt (f ∘ g) x := by
  obtain ⟨r, hr⟩ := hf
  by_cases hg' : analyticOrderAt (g · - g x) x = ⊤
  · -- trivial case: `g` is locally constant near `x`
    refine .congr (.const (f (g x)) x) ?_
    filter_upwards [nhdsWithin_le_nhds <| analyticOrderAt_eq_top.mp hg'] with z hz
    grind
  · -- interesting case: `g z - g x` looks like `(z - x) ^ n` times a non-vanishing function
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hg'
    obtain ⟨h, han, hne, heq⟩ := (hg.fun_sub analyticAt_const).analyticOrderAt_eq_natCast.mp hn.symm
    set j := fun z => (z - g x) ^ r • f z
    have : AnalyticAt 𝕜 (fun i => (h i)⁻¹ ^ r • j (g i)) x :=
      ((han.inv hne).pow r).smul (hr.restrictScalars.comp hg)
    refine ⟨n * r, this.congr ?_⟩
    filter_upwards [heq, han.continuousAt.tendsto.eventually_ne hne] with z hz hzne
    simp only [j, inv_pow, Function.comp_apply, inv_smul_eq_iff₀ (pow_ne_zero r hzne)]
    rw [hz]; rw [smul_comm]; rw [← smul_assoc]; rw [pow_mul]; rw [smul_pow]

/--
lemma `meromorphicAt_comp_iff_of_deriv_ne_zero` / 引理 `meromorphicAt_comp_iff_of_deriv_ne_zero`

English:
lemma meromorphicAt_comp_iff_of_deriv_ne_zero
  statement: [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> E}
  proof: by
  refine ⟨fun hf => ?_, by fun_prop⟩
  let r := hg.hasStrictDerivAt.localInverse _ _ _ hg'
  have hra : AnalyticAt 𝕜 r (g x) := hg.analyticAt_localInverse hg'
  have : r (g x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hf
  refine (hf.comp_analyticAt hra).congr (.filter

中文:
引理 meromorphicAt_comp_iff_of_deriv_ne_zero
  结论: [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> E}
  证明: by
  refine ⟨fun hf => ?_, by fun_prop⟩
  let r := hg.hasStrictDerivAt.localInverse _ _ _ hg'
  have hra : AnalyticAt 𝕜 r (g x) := hg.analyticAt_localInverse hg'
  have : r (g x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hf
  refine (hf.comp_analyticAt hra).congr (.filter

Depends on / 依赖: AnalyticAt, EventuallyEq, EventuallyEq.fun_comp, HasStrictDerivAt, HasStrictDerivAt.eventually_right_inverse, HasStrictFDerivAt, HasStrictFDerivAt.localInverse_apply_image, analyticAt_localInverse, comp_analyticAt, eventually_right_inverse, filter_mono, fun_comp, fun_prop, hasStrictDerivAt, hf.comp_analyticAt, hg.analyticAt_localInverse, hg.hasStrictDerivAt.localInverse, localInverse, localInverse_apply_image, nhdsWithin_le_nhds
-/
lemma meromorphicAt_comp_iff_of_deriv_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> E}
    {g : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x != 0) :
    MeromorphicAt (f ∘ g) x ↔ MeromorphicAt f (g x) := by
  refine ⟨fun hf => ?_, by fun_prop⟩
  let r := hg.hasStrictDerivAt.localInverse _ _ _ hg'
  have hra : AnalyticAt 𝕜 r (g x) := hg.analyticAt_localInverse hg'
  have : r (g x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hf
  refine (hf.comp_analyticAt hra).congr (.filter_mono ?_ nhdsWithin_le_nhds)
  exact EventuallyEq.fun_comp (HasStrictDerivAt.eventually_right_inverse ..) f

/-- `MeromorphicAt` is invariant under translation. -/
@[to_fun meromorphicAt_fun_comp_add_const_iff_meromorphicAt]
/--
theorem `meromorphicAt_comp_add_const_iff_meromorphicAt` / 定理 `meromorphicAt_comp_add_const_iff_meromorphicAt`

English:
theorem meromorphicAt_comp_add_const_iff_meromorphicAt
  given: {c : 𝕜} {f : 𝕜 -> E}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show f = ((f ∘ fun x => x + c) ∘ fun z => z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z => z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z => z + c) (by fun_prop)

中文:
定理 meromorphicAt_comp_add_const_iff_meromorphicAt
  条件: {c : 𝕜} {f : 𝕜 -> E}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show f = ((f ∘ fun x => x + c) ∘ fun z => z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z => z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z => z + c) (by fun_prop)

Depends on / 依赖: comp_analyticAt, fun_prop, h.comp_analyticAt
-/
theorem meromorphicAt_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 -> E} :
    MeromorphicAt (f ∘ (· + c)) x ↔ MeromorphicAt f (x + c) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show f = ((f ∘ fun x => x + c) ∘ fun z => z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z => z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z => z + c) (by fun_prop)

/-- `MeromorphicAt` is invariant under translation. -/
@[to_fun meromorphicAt_fun_comp_sub_const_iff_meromorphicAt]
/--
theorem `meromorphicAt_comp_sub_const_iff_meromorphicAt` / 定理 `meromorphicAt_comp_sub_const_iff_meromorphicAt`

English:
theorem meromorphicAt_comp_sub_const_iff_meromorphicAt
  given: {c : 𝕜} {f : 𝕜 -> E}
  proof: by
  simp_rw [sub_eq_add_neg, meromorphicAt_comp_add_const_iff_meromorphicAt]

中文:
定理 meromorphicAt_comp_sub_const_iff_meromorphicAt
  条件: {c : 𝕜} {f : 𝕜 -> E}
  证明: by
  simp_rw [sub_eq_add_neg, meromorphicAt_comp_add_const_iff_meromorphicAt]

Depends on / 依赖: meromorphicAt_comp_add_const_iff_meromorphicAt, simp_rw, sub_eq_add_neg
-/
theorem meromorphicAt_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 -> E} :
    MeromorphicAt (f ∘ (· - c)) x ↔ MeromorphicAt f (x - c) := by
  simp_rw [sub_eq_add_neg, meromorphicAt_comp_add_const_iff_meromorphicAt]

end composition


/--
Definition of `MeromorphicOn` / `MeromorphicOn` 的定义

English:
definition MeromorphicOn
  signature: (f : 𝕜 -> E) (U : Set 𝕜)
  body: forall x in U, MeromorphicAt f x

中文:
定义 MeromorphicOn
  签名: (f : 𝕜 -> E) (U : Set 𝕜)
  定义体: forall x in U, MeromorphicAt f x

Depends on / 依赖: MeromorphicAt
-/
def MeromorphicOn (f : 𝕜 -> E) (U : Set 𝕜) : Prop := forall x in U, MeromorphicAt f x

/--
lemma `AnalyticOnNhd.meromorphicOn` / 引理 `AnalyticOnNhd.meromorphicOn`

English:
lemma AnalyticOnNhd.meromorphicOn
  given: {f : 𝕜 -> E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
  proof: fun x hx => (hf x hx).meromorphicAt

中文:
引理 AnalyticOnNhd.meromorphicOn
  条件: {f : 𝕜 -> E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
  证明: fun x hx => (hf x hx).meromorphicAt

Depends on / 依赖: meromorphicAt
-/
lemma AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) :
    MeromorphicOn f U :=
  fun x hx => (hf x hx).meromorphicAt

namespace MeromorphicOn

variable {s t : 𝕜 -> 𝕜'} {f g : 𝕜 -> E} {U : Set 𝕜}
  (hs : MeromorphicOn s U) (ht : MeromorphicOn t U)
  (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)

/--
theorem `congr_codiscreteWithin_of_eqOn_compl` / 定理 `congr_codiscreteWithin_of_eqOn_compl`

English:
theorem congr_codiscreteWithin_of_eqOn_compl
  statement: (hf : MeromorphicOn f U)
  proof: by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  filter_upwards [h₁ x hx] with a ha
  simp at ha
  tauto

中文:
定理 congr_codiscreteWithin_of_eqOn_compl
  结论: (hf : MeromorphicOn f U)
  证明: by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  filter_upwards [h₁ x hx] with a ha
  simp at ha
  tauto

Depends on / 依赖: Eventually, EventuallyEq, Filter, Filter.Eventually, disjoint_principal_right, filter_upwards, mem_codiscreteWithin, simp_rw
-/
theorem congr_codiscreteWithin_of_eqOn_compl (hf : MeromorphicOn f U)
    (h₁ : f =ᶠ[codiscreteWithin U] g) (h₂ : Set.EqOn f g Uᶜ) :
    MeromorphicOn g U := by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  filter_upwards [h₁ x hx] with a ha
  simp at ha
  tauto

/--
theorem `congr_codiscreteWithin` / 定理 `congr_codiscreteWithin`

English:
theorem congr_codiscreteWithin
  statement: (hf : MeromorphicOn f U) (h₁ : f =ᶠ[codiscreteWithin U] g)
  proof: by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  have : U in 𝓝[!=] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only 

中文:
定理 congr_codiscreteWithin
  结论: (hf : MeromorphicOn f U) (h₁ : f =ᶠ[codiscreteWithin U] g)
  证明: by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  have : U in 𝓝[!=] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only 

Depends on / 依赖: Eventually, EventuallyEq, Filter, Filter.Eventually, Set.inter_subset_left, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_sdiff, disjoint_principal_right, filter_upwards, inter_subset_left, mem_codiscreteWithin, mem_compl_iff, mem_nhdsWithin, mem_nhdsWithin.mpr, mem_ofPred_eq, mem_sdiff, not_and, simp_rw
-/
theorem congr_codiscreteWithin (hf : MeromorphicOn f U) (h₁ : f =ᶠ[codiscreteWithin U] g)
    (h₂ : IsOpen U) :
    MeromorphicOn g U := by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  have : U in 𝓝[!=] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at h₂a
  tauto

/--
theorem `_root_.meromorphicOn_congr_codiscreteWithin` / 定理 `_root_.meromorphicOn_congr_codiscreteWithin`

English:
theorem _root_.meromorphicOn_congr_codiscreteWithin
  statement: {f g : 𝕜 -> E} (h₁ : f =ᶠ[codiscreteWithin U] g)
  proof: ⟨(·.congr_codiscreteWithin h₁ h₂), (·.congr_codiscreteWithin h₁.symm h₂)⟩

中文:
定理 _root_.meromorphicOn_congr_codiscreteWithin
  结论: {f g : 𝕜 -> E} (h₁ : f =ᶠ[codiscreteWithin U] g)
  证明: ⟨(·.congr_codiscreteWithin h₁ h₂), (·.congr_codiscreteWithin h₁.symm h₂)⟩

Depends on / 依赖: congr_codiscreteWithin
-/
theorem _root_.meromorphicOn_congr_codiscreteWithin {f g : 𝕜 -> E} (h₁ : f =ᶠ[codiscreteWithin U] g)
    (h₂ : IsOpen U) :
    MeromorphicOn f U ↔ MeromorphicOn g U :=
  ⟨(·.congr_codiscreteWithin h₁ h₂), (·.congr_codiscreteWithin h₁.symm h₂)⟩

/--
lemma `id` / 引理 `id`

English:
lemma id
  given: {U : Set 𝕜}
  statement: MeromorphicOn id U
  proof: fun x _ => .id x

中文:
引理 id
  条件: {U : Set 𝕜}
  结论: MeromorphicOn id U
  证明: fun x _ => .id x
-/
lemma id {U : Set 𝕜} : MeromorphicOn id U := fun x _ => .id x

/--
lemma `const` / 引理 `const`

English:
lemma const
  given: (e : E) {U : Set 𝕜}
  statement: MeromorphicOn (fun _ => e) U
  proof: fun x _ => .const e x

中文:
引理 const
  条件: (e : E) {U : Set 𝕜}
  结论: MeromorphicOn (fun _ => e) U
  证明: fun x _ => .const e x
-/
lemma const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ => e) U :=
  fun x _ => .const e x

section arithmetic

include hf in
/--
lemma `mono_set` / 引理 `mono_set`

English:
lemma mono_set
  given: {V : Set 𝕜} (hv : V subseteq U)
  statement: MeromorphicOn f V
  proof: fun x hx => hf x (hv hx)

include hf hg in

中文:
引理 mono_set
  条件: {V : Set 𝕜} (hv : V subseteq U)
  结论: MeromorphicOn f V
  证明: fun x hx => hf x (hv hx)

include hf hg in
-/
lemma mono_set {V : Set 𝕜} (hv : V subseteq U) : MeromorphicOn f V := fun x hx => hf x (hv hx)

include hf hg in
/--
lemma `add` / 引理 `add`

English:
lemma add
  statement: MeromorphicOn (f + g) U
  proof: fun x hx => (hf x hx).add (hg x hx)

include hf hg in

中文:
引理 add
  结论: MeromorphicOn (f + g) U
  证明: fun x hx => (hf x hx).add (hg x hx)

include hf hg in
-/
@[to_fun] lemma add : MeromorphicOn (f + g) U := fun x hx => (hf x hx).add (hg x hx)

include hf hg in
/--
lemma `sub` / 引理 `sub`

English:
lemma sub
  statement: MeromorphicOn (f - g) U
  proof: fun x hx => (hf x hx).sub (hg x hx)

include hf in

中文:
引理 sub
  结论: MeromorphicOn (f - g) U
  证明: fun x hx => (hf x hx).sub (hg x hx)

include hf in
-/
@[to_fun] lemma sub : MeromorphicOn (f - g) U := fun x hx => (hf x hx).sub (hg x hx)

include hf in
/--
lemma `neg` / 引理 `neg`

English:
lemma neg
  statement: MeromorphicOn (-f) U
  proof: fun x hx => (hf x hx).neg

中文:
引理 neg
  结论: MeromorphicOn (-f) U
  证明: fun x hx => (hf x hx).neg
-/
@[to_fun] lemma neg : MeromorphicOn (-f) U := fun x hx => (hf x hx).neg

/--
lemma `neg_iff` / 引理 `neg_iff`

English:
lemma neg_iff
  statement: MeromorphicOn (-f) U ↔ MeromorphicOn f U
  proof: ⟨fun h => by simpa only [neg_neg] using h.neg, neg⟩

@[to_fun]

中文:
引理 neg_iff
  结论: MeromorphicOn (-f) U ↔ MeromorphicOn f U
  证明: ⟨fun h => by simpa only [neg_neg] using h.neg, neg⟩

@[to_fun]
-/
@[simp] lemma neg_iff : MeromorphicOn (-f) U ↔ MeromorphicOn f U :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, neg⟩

@[to_fun]
/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  statement: [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {s : 𝕜 -> R} (hs : MeromorphicOn s U)
  proof: fun x hx => (hs x hx).smul (hf x hx)

include hf in

中文:
引理 smul
  结论: [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {s : 𝕜 -> R} (hs : MeromorphicOn s U)
  证明: fun x hx => (hs x hx).smul (hf x hx)

include hf in

Depends on / 依赖: CharZero, charZero_rclike
-/
lemma smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {s : 𝕜 -> R} (hs : MeromorphicOn s U)
    {f : 𝕜 -> E} (hf : MeromorphicOn f U) :
    MeromorphicOn (s • f) U :=
  fun x hx => (hs x hx).smul (hf x hx)

include hf in
/--
lemma `const_smul` / 引理 `const_smul`

English:
lemma const_smul
  given: [SMulCommClass 𝕜 R E] (c : R)
  statement: MeromorphicOn (c • f) U
  proof: fun x hx => (hf x hx).const_smul c

include hs ht in

中文:
引理 const_smul
  条件: [SMulCommClass 𝕜 R E] (c : R)
  结论: MeromorphicOn (c • f) U
  证明: fun x hx => (hf x hx).const_smul c

include hs ht in
-/
@[to_fun] lemma const_smul [SMulCommClass 𝕜 R E] (c : R) : MeromorphicOn (c • f) U :=
  fun x hx => (hf x hx).const_smul c

include hs ht in
/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  statement: MeromorphicOn (s * t) U
  proof: fun x hx => (hs x hx).mul (ht x hx)

中文:
引理 mul
  结论: MeromorphicOn (s * t) U
  证明: fun x hx => (hs x hx).mul (ht x hx)
-/
@[to_fun] lemma mul : MeromorphicOn (s * t) U := fun x hx => (hs x hx).mul (ht x hx)

/--
lemma `prod` / 引理 `prod`

English:
lemma prod
  statement: {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
  proof: fun z hz => MeromorphicAt.prod (h · · z hz)

中文:
引理 prod
  结论: {U : Set 𝕜} {ι : 类型} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
  证明: fun z hz => MeromorphicAt.prod (h · · z hz)

Depends on / 依赖: MeromorphicAt, MeromorphicAt.prod
-/
lemma prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
    (h : forall σ in s, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ n in s, f n) U :=
  fun z hz => MeromorphicAt.prod (h · · z hz)

/--
lemma `fun_prod` / 引理 `fun_prod`

English:
lemma fun_prod
  statement: {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
  proof: fun z hz => MeromorphicAt.fun_prod (h · · z hz)

中文:
引理 fun_prod
  结论: {U : Set 𝕜} {ι : 类型} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
  证明: fun z hz => MeromorphicAt.fun_prod (h · · z hz)

Depends on / 依赖: MeromorphicAt, MeromorphicAt.fun_prod, fun_prod
-/
lemma fun_prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
    (h : forall σ in s, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z => ∏ n in s, f n z) U :=
  fun z hz => MeromorphicAt.fun_prod (h · · z hz)

/--
lemma `finprod` / 引理 `finprod`

English:
lemma finprod
  given: {U : Set 𝕜} {ι : Type*} {f : ι -> 𝕜 -> 𝕜'} (h : forall σ, MeromorphicOn (f σ) U)
  proof: fun z hz => MeromorphicAt.finprod (h · z hz)

中文:
引理 finprod
  条件: {U : Set 𝕜} {ι : 类型} {f : ι -> 𝕜 -> 𝕜'} (h : 对任意 σ, MeromorphicOn (f σ) U)
  证明: fun z hz => MeromorphicAt.finprod (h · z hz)

Depends on / 依赖: MeromorphicAt, MeromorphicAt.finprod, finprod
-/
lemma finprod {U : Set 𝕜} {ι : Type*} {f : ι -> 𝕜 -> 𝕜'} (h : forall σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ᶠ n, f n) U :=
  fun z hz => MeromorphicAt.finprod (h · z hz)

/--
lemma `sum` / 引理 `sum`

English:
lemma sum
  statement: {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> E}
  proof: fun z hz => MeromorphicAt.sum (h · · z hz)

中文:
引理 sum
  结论: {U : Set 𝕜} {ι : 类型} {s : Finset ι} {f : ι -> 𝕜 -> E}
  证明: fun z hz => MeromorphicAt.sum (h · · z hz)

Depends on / 依赖: MeromorphicAt, MeromorphicAt.sum
-/
lemma sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> E}
    (h : forall σ in s, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ n in s, f n) U :=
  fun z hz => MeromorphicAt.sum (h · · z hz)

/--
lemma `fun_sum` / 引理 `fun_sum`

English:
lemma fun_sum
  statement: {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> E}
  proof: fun z hz => MeromorphicAt.fun_sum (fun σ _ => h σ z hz)

中文:
引理 fun_sum
  结论: {U : Set 𝕜} {ι : 类型} {s : Finset ι} {f : ι -> 𝕜 -> E}
  证明: fun z hz => MeromorphicAt.fun_sum (fun σ _ => h σ z hz)

Depends on / 依赖: MeromorphicAt, MeromorphicAt.fun_sum, fun_sum
-/
lemma fun_sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> E}
    (h : forall σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z => ∑ n in s, f n z) U :=
  fun z hz => MeromorphicAt.fun_sum (fun σ _ => h σ z hz)

/--
lemma `finsum` / 引理 `finsum`

English:
lemma finsum
  given: {U : Set 𝕜} {ι : Type*} {f : ι -> 𝕜 -> 𝕜'} (h : forall σ, MeromorphicOn (f σ) U)
  proof: fun z hz => MeromorphicAt.finsum (h · z hz)

include hs in

中文:
引理 finsum
  条件: {U : Set 𝕜} {ι : 类型} {f : ι -> 𝕜 -> 𝕜'} (h : 对任意 σ, MeromorphicOn (f σ) U)
  证明: fun z hz => MeromorphicAt.finsum (h · z hz)

include hs in

Depends on / 依赖: MeromorphicAt, MeromorphicAt.finsum, finsum
-/
lemma finsum {U : Set 𝕜} {ι : Type*} {f : ι -> 𝕜 -> 𝕜'} (h : forall σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ᶠ n, f n) U :=
  fun z hz => MeromorphicAt.finsum (h · z hz)

include hs in
/--
lemma `inv` / 引理 `inv`

English:
lemma inv
  statement: MeromorphicOn s⁻¹ U
  proof: fun x hx => (hs x hx).inv

中文:
引理 inv
  结论: MeromorphicOn s⁻¹ U
  证明: fun x hx => (hs x hx).inv
-/
@[to_fun] lemma inv : MeromorphicOn s⁻¹ U := fun x hx => (hs x hx).inv

/--
lemma `inv_iff` / 引理 `inv_iff`

English:
lemma inv_iff
  statement: MeromorphicOn s⁻¹ U ↔ MeromorphicOn s U
  proof: ⟨fun h => by simpa only [inv_inv] using h.inv, inv⟩

include hs ht in

中文:
引理 inv_iff
  结论: MeromorphicOn s⁻¹ U ↔ MeromorphicOn s U
  证明: ⟨fun h => by simpa only [inv_inv] using h.inv, inv⟩

include hs ht in
-/
@[simp] lemma inv_iff : MeromorphicOn s⁻¹ U ↔ MeromorphicOn s U :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, inv⟩

include hs ht in
/--
lemma `div` / 引理 `div`

English:
lemma div
  statement: MeromorphicOn (s / t) U
  proof: fun x hx => (hs x hx).div (ht x hx)

include hs in

中文:
引理 div
  结论: MeromorphicOn (s / t) U
  证明: fun x hx => (hs x hx).div (ht x hx)

include hs in
-/
@[to_fun] lemma div : MeromorphicOn (s / t) U := fun x hx => (hs x hx).div (ht x hx)

include hs in
/--
lemma `pow` / 引理 `pow`

English:
lemma pow
  given: (n : Nat)
  statement: MeromorphicOn (s ^ n) U
  proof: fun x hx => (hs x hx).pow _

include hs in

中文:
引理 pow
  条件: (n : 自然数)
  结论: MeromorphicOn (s ^ n) U
  证明: fun x hx => (hs x hx).pow _

include hs in
-/
@[to_fun] lemma pow (n : Nat) : MeromorphicOn (s ^ n) U := fun x hx => (hs x hx).pow _

include hs in
/--
lemma `zpow` / 引理 `zpow`

English:
lemma zpow
  given: (n : Int)
  statement: MeromorphicOn (s ^ n) U
  proof: fun x hx => (hs x hx).zpow _

include hf in

中文:
引理 zpow
  条件: (n : 整数)
  结论: MeromorphicOn (s ^ n) U
  证明: fun x hx => (hs x hx).zpow _

include hf in
-/
@[to_fun] lemma zpow (n : Int) : MeromorphicOn (s ^ n) U := fun x hx => (hs x hx).zpow _

include hf in
/--
theorem `deriv` / 定理 `deriv`

English:
theorem deriv
  given: [CompleteSpace E]
  statement: MeromorphicOn (deriv f) U
  proof: fun z hz => (hf z hz).deriv

include hf in

中文:
定理 deriv
  条件: [CompleteSpace E]
  结论: MeromorphicOn (deriv f) U
  证明: fun z hz => (hf z hz).deriv

include hf in
-/
protected theorem deriv [CompleteSpace E] : MeromorphicOn (deriv f) U := fun z hz => (hf z hz).deriv

include hf in
/--
theorem `iterated_deriv` / 定理 `iterated_deriv`

English:
theorem iterated_deriv
  given: [CompleteSpace E] {n : Nat}
  statement: MeromorphicOn (_root_.deriv^[n] f) U
  proof: fun z hz => (hf z hz).iterated_deriv

中文:
定理 iterated_deriv
  条件: [CompleteSpace E] {n : 自然数}
  结论: MeromorphicOn (_root_.deriv^[n] f) U
  证明: fun z hz => (hf z hz).iterated_deriv

Depends on / 依赖: iterated_deriv
-/
theorem iterated_deriv [CompleteSpace E] {n : Nat} : MeromorphicOn (_root_.deriv^[n] f) U :=
  fun z hz => (hf z hz).iterated_deriv

/--
theorem `logDeriv` / 定理 `logDeriv`

English:
theorem logDeriv
  given: [CompleteSpace 𝕜'] {f : 𝕜 -> 𝕜'} {hf : MeromorphicOn f U}
  proof: hf.deriv.div hf

中文:
定理 logDeriv
  条件: [CompleteSpace 𝕜'] {f : 𝕜 -> 𝕜'} {hf : MeromorphicOn f U}
  证明: hf.deriv.div hf
-/
protected theorem logDeriv [CompleteSpace 𝕜'] {f : 𝕜 -> 𝕜'} {hf : MeromorphicOn f U} :
    MeromorphicOn (logDeriv f) U := hf.deriv.div hf
/-- `MeromorphicOn` is invariant under translation. -/
@[to_fun meromorphicOn_fun_comp_add_const_iff_meromorphicOn]
/--
theorem `meromorphicOn_comp_add_const_iff_meromorphicOn` / 定理 `meromorphicOn_comp_add_const_iff_meromorphicOn`

English:
theorem meromorphicOn_comp_add_const_iff_meromorphicOn
  given: {c : 𝕜} {U : Set 𝕜}
  proof: by
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicAt_comp_add_const_iff_meromorphicAt] using h x h₁x
  · rw [meromorphicAt_comp_add_const_iff_meromorphicAt]
    aesop

中文:
定理 meromorphicOn_comp_add_const_iff_meromorphicOn
  条件: {c : 𝕜} {U : Set 𝕜}
  证明: by
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicAt_comp_add_const_iff_meromorphicAt] using h x h₁x
  · rw [meromorphicAt_comp_add_const_iff_meromorphicAt]
    aesop

Depends on / 依赖: add_singleton, mem_image, meromorphicAt_comp_add_const_iff_meromorphicAt
-/
theorem meromorphicOn_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicOn (f ∘ (· + c)) U ↔ MeromorphicOn f (U + {c}) := by
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicAt_comp_add_const_iff_meromorphicAt] using h x h₁x
  · rw [meromorphicAt_comp_add_const_iff_meromorphicAt]
    aesop

/-- `MeromorphicOn` is invariant under translation. -/
@[to_fun meromorphicOn_fun_comp_sub_const_iff_meromorphicOn]
/--
theorem `meromorphicOn_comp_sub_const_iff_meromorphicOn` / 定理 `meromorphicOn_comp_sub_const_iff_meromorphicOn`

English:
theorem meromorphicOn_comp_sub_const_iff_meromorphicOn
  given: {c : 𝕜} {U : Set 𝕜}
  proof: by
  simp_rw [sub_eq_add_neg, meromorphicOn_comp_add_const_iff_meromorphicOn, neg_singleton]

中文:
定理 meromorphicOn_comp_sub_const_iff_meromorphicOn
  条件: {c : 𝕜} {U : Set 𝕜}
  证明: by
  simp_rw [sub_eq_add_neg, meromorphicOn_comp_add_const_iff_meromorphicOn, neg_singleton]

Depends on / 依赖: meromorphicOn_comp_add_const_iff_meromorphicOn, neg_singleton, simp_rw, sub_eq_add_neg
-/
theorem meromorphicOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicOn (f ∘ (· - c)) U ↔ MeromorphicOn f (U - {c}) := by
  simp_rw [sub_eq_add_neg, meromorphicOn_comp_add_const_iff_meromorphicOn, neg_singleton]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a ball. -/
@[to_fun (attr := simp) meromorphicOn_ball_fun_comp_sub_const_iff_meromorphicOn_ball]
/--
theorem `meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball` / 定理 `meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball`

English:
theorem meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball
  given: {c : 𝕜} {R : Real}
  proof: by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn]; rw [ball_sub_singleton]; rw [sub_self]

中文:
定理 meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball
  条件: {c : 𝕜} {R : 实数}
  证明: by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn]; rw [ball_sub_singleton]; rw [sub_self]

Depends on / 依赖: ball_sub_singleton, meromorphicOn_comp_sub_const_iff_meromorphicOn, sub_self
-/
theorem meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball {c : 𝕜} {R : Real} :
    MeromorphicOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicOn f (ball 0 R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn]; rw [ball_sub_singleton]; rw [sub_self]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a closed ball. -/
@[to_fun (attr := simp) meromorphicOn_closedBall_fun_comp_sub_const_iff_meromorphicOn_closedBall]
/--
theorem `meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall` / 定理 `meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall`

English:
theorem meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall
  given: {c : 𝕜} {R : Real}
  proof: by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn]; rw [closedBall_sub_singleton]; rw [sub_self]

中文:
定理 meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall
  条件: {c : 𝕜} {R : 实数}
  证明: by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn]; rw [closedBall_sub_singleton]; rw [sub_self]

Depends on / 依赖: closedBall_sub_singleton, meromorphicOn_comp_sub_const_iff_meromorphicOn, sub_self
-/
theorem meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall {c : 𝕜} {R : Real} :
    MeromorphicOn (f ∘ (· - c)) (closedBall c R) ↔ MeromorphicOn f (closedBall 0 R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn]; rw [closedBall_sub_singleton]; rw [sub_self]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) meromorphicOn_sphere_fun_comp_sub_const_iff_meromorphicOn_sphere]
/--
theorem `meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere` / 定理 `meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere`

English:
theorem meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere
  given: {c : 𝕜} {R : Real}
  proof: by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn]; rw [sphere_sub_singleton]; rw [sub_self]

中文:
定理 meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere
  条件: {c : 𝕜} {R : 实数}
  证明: by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn]; rw [sphere_sub_singleton]; rw [sub_self]

Depends on / 依赖: meromorphicOn_comp_sub_const_iff_meromorphicOn, sphere_sub_singleton, sub_self
-/
theorem meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere {c : 𝕜} {R : Real} :
    MeromorphicOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicOn f (sphere 0 R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn]; rw [sphere_sub_singleton]; rw [sub_self]

end arithmetic

include hf in
/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: (h_eq : Set.EqOn f g U) (hu : IsOpen U)
  statement: MeromorphicOn g U
  proof: by
  refine fun x hx => (hf x hx).congr (EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds)
  exact eventually_of_mem (hu.mem_nhds hx) h_eq

中文:
引理 congr
  条件: (h_eq : Set.EqOn f g U) (hu : IsOpen U)
  结论: MeromorphicOn g U
  证明: by
  refine fun x hx => (hf x hx).congr (EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds)
  exact eventually_of_mem (hu.mem_nhds hx) h_eq

Depends on / 依赖: EventuallyEq, EventuallyEq.filter_mono, eventually_of_mem, filter_mono, h_eq, hu.mem_nhds, mem_nhds, nhdsWithin_le_nhds
-/
lemma congr (h_eq : Set.EqOn f g U) (hu : IsOpen U) : MeromorphicOn g U := by
  refine fun x hx => (hf x hx).congr (EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds)
  exact eventually_of_mem (hu.mem_nhds hx) h_eq

/--
theorem `eventually_codiscreteWithin_analyticAt` / 定理 `eventually_codiscreteWithin_analyticAt`

English:
theorem eventually_codiscreteWithin_analyticAt
  proof: by
  rw [eventually_iff]; rw [mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  apply Filter.mem_of_superset ((h x hx).eventually_analyticAt)
  intro x hx
  simp [hx]

中文:
定理 eventually_codiscreteWithin_analyticAt
  证明: by
  rw [eventually_iff]; rw [mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  apply Filter.mem_of_superset ((h x hx).eventually_analyticAt)
  intro x hx
  simp [hx]

Depends on / 依赖: Filter, Filter.mem_of_superset, disjoint_principal_right, eventually_analyticAt, eventually_iff, mem_codiscreteWithin, mem_of_superset
-/
theorem eventually_codiscreteWithin_analyticAt
    [CompleteSpace E] (f : 𝕜 -> E) (h : MeromorphicOn f U) :
    forallᶠ (y : 𝕜) in codiscreteWithin U, AnalyticAt 𝕜 f y := by
  rw [eventually_iff]; rw [mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  apply Filter.mem_of_superset ((h x hx).eventually_analyticAt)
  intro x hx
  simp [hx]

/--
theorem `countable_compl_analyticAt_inter` / 定理 `countable_compl_analyticAt_inter`

English:
theorem countable_compl_analyticAt_inter
  statement: [SecondCountableTopology 𝕜] [CompleteSpace E]
  proof: by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_of_codiscreteWithin _)
  simpa using! eventually_codiscreteWithin_analyticAt f h

中文:
定理 countable_compl_analyticAt_inter
  结论: [SecondCountableTopology 𝕜] [CompleteSpace E]
  证明: by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_of_codiscreteWithin _)
  simpa using! eventually_codiscreteWithin_analyticAt f h

Depends on / 依赖: HereditarilyLindelofSpace, HereditarilyLindelofSpace.isLindelof, countable_of_isDiscrete, eventually_codiscreteWithin_analyticAt, isDiscrete_of_codiscreteWithin, isLindelof
-/
theorem countable_compl_analyticAt_inter [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : MeromorphicOn f U) :
    ({z | AnalyticAt 𝕜 f z}ᶜ inter U).Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_of_codiscreteWithin _)
  simpa using! eventually_codiscreteWithin_analyticAt f h

end MeromorphicOn

/-- Meromorphy of a function on all of 𝕜. -/
@[fun_prop]
/--
Definition of `Meromorphic` / `Meromorphic` 的定义

English:
definition Meromorphic
  signature: (f : 𝕜 -> E)
  body: forall x, MeromorphicAt f x

中文:
定义 Meromorphic
  签名: (f : 𝕜 -> E)
  定义体: forall x, MeromorphicAt f x

Depends on / 依赖: MeromorphicAt
-/
def Meromorphic (f : 𝕜 -> E) := forall x, MeromorphicAt f x

/-- A function is meromorphic iff it is meromorphic on Set.univ. -/
@[simp]
/--
lemma `meromorphicOn_univ` / 引理 `meromorphicOn_univ`

English:
lemma meromorphicOn_univ
  given: {f : 𝕜 -> E}
  statement: MeromorphicOn f Set.univ ↔ Meromorphic f
  proof: by tauto

中文:
引理 meromorphicOn_univ
  条件: {f : 𝕜 -> E}
  结论: MeromorphicOn f Set.univ ↔ Meromorphic f
  证明: by tauto
-/
lemma meromorphicOn_univ {f : 𝕜 -> E} : MeromorphicOn f Set.univ ↔ Meromorphic f := by tauto

namespace Meromorphic

variable
  {ι : Type*} {s : Finset ι}
  {f g : 𝕜 -> E} {F : ι -> 𝕜 -> 𝕜'} {G : ι -> 𝕜 -> E}

@[fun_prop]
/--
lemma `meromorphicAt` / 引理 `meromorphicAt`

English:
lemma meromorphicAt
  given: {x : 𝕜} (hf : Meromorphic f)
  statement: MeromorphicAt f x
  proof: hf x

中文:
引理 meromorphicAt
  条件: {x : 𝕜} (hf : Meromorphic f)
  结论: MeromorphicAt f x
  证明: hf x
-/
lemma meromorphicAt {x : 𝕜} (hf : Meromorphic f) : MeromorphicAt f x := hf x

/--
lemma `meromorphicOn` / 引理 `meromorphicOn`

English:
lemma meromorphicOn
  given: {s : Set 𝕜} (hf : Meromorphic f)
  statement: MeromorphicOn f s
  proof: fun x _ => hf x

@[fun_prop]

中文:
引理 meromorphicOn
  条件: {s : Set 𝕜} (hf : Meromorphic f)
  结论: MeromorphicOn f s
  证明: fun x _ => hf x

@[fun_prop]
-/
lemma meromorphicOn {s : Set 𝕜} (hf : Meromorphic f) : MeromorphicOn f s := fun x _ => hf x

@[fun_prop]
/--
lemma `const` / 引理 `const`

English:
lemma const
  given: (x : E)
  statement: Meromorphic fun _ : 𝕜 => x
  proof: fun _ => .const _ _

@[to_fun (attr := fun_prop)]

中文:
引理 const
  条件: (x : E)
  结论: Meromorphic fun _ : 𝕜 => x
  证明: fun _ => .const _ _

@[to_fun (attr := fun_prop)]
-/
lemma const (x : E) : Meromorphic fun _ : 𝕜 => x := fun _ => .const _ _

@[to_fun (attr := fun_prop)]
/--
lemma `neg` / 引理 `neg`

English:
lemma neg
  given: (hf : Meromorphic f)
  statement: Meromorphic (-f)
  proof: fun x => (hf x).neg

@[to_fun (attr := fun_prop)]

中文:
引理 neg
  条件: (hf : Meromorphic f)
  结论: Meromorphic (-f)
  证明: fun x => (hf x).neg

@[to_fun (attr := fun_prop)]
-/
lemma neg (hf : Meromorphic f) : Meromorphic (-f) := fun x => (hf x).neg

@[to_fun (attr := fun_prop)]
/--
lemma `add` / 引理 `add`

English:
lemma add
  given: (hf : Meromorphic f) (hg : Meromorphic g)
  proof: fun x => (hf x).add (hg x)

@[to_fun (attr := fun_prop)]

中文:
引理 add
  条件: (hf : Meromorphic f) (hg : Meromorphic g)
  证明: fun x => (hf x).add (hg x)

@[to_fun (attr := fun_prop)]
-/
lemma add (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f + g) := fun x => (hf x).add (hg x)

@[to_fun (attr := fun_prop)]
/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  given: (h : forall σ in s, Meromorphic (G σ))
  proof: fun x => MeromorphicAt.sum (h · · x)

@[fun_prop]

中文:
定理 sum
  条件: (h : 对任意 σ in s, Meromorphic (G σ))
  证明: fun x => MeromorphicAt.sum (h · · x)

@[fun_prop]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.sum
-/
theorem sum (h : forall σ in s, Meromorphic (G σ)) :
    Meromorphic (∑ n in s, G n) := fun x => MeromorphicAt.sum (h · · x)

@[fun_prop]
/--
theorem `finsum` / 定理 `finsum`

English:
theorem finsum
  given: (h : forall σ, Meromorphic (F σ))
  proof: fun x => MeromorphicAt.finsum (h · x)

@[to_fun (attr := fun_prop)]

中文:
定理 finsum
  条件: (h : 对任意 σ, Meromorphic (F σ))
  证明: fun x => MeromorphicAt.finsum (h · x)

@[to_fun (attr := fun_prop)]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.finsum, finsum
-/
theorem finsum (h : forall σ, Meromorphic (F σ)) :
    Meromorphic (∑ᶠ σ, F σ) := fun x => MeromorphicAt.finsum (h · x)

@[to_fun (attr := fun_prop)]
/--
lemma `sub` / 引理 `sub`

English:
lemma sub
  given: (hf : Meromorphic f) (hg : Meromorphic g)
  proof: fun x => (hf x).sub (hg x)

@[to_fun (attr := fun_prop)]

中文:
引理 sub
  条件: (hf : Meromorphic f) (hg : Meromorphic g)
  证明: fun x => (hf x).sub (hg x)

@[to_fun (attr := fun_prop)]
-/
lemma sub (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f - g) := fun x => (hf x).sub (hg x)

@[to_fun (attr := fun_prop)]
/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  statement: [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 𝕜 -> R} (hf : Meromorphic f)
  proof: fun x => (hf x).smul (hg x)

@[to_fun (attr := fun_prop)]

中文:
引理 smul
  结论: [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 𝕜 -> R} (hf : Meromorphic f)
  证明: fun x => (hf x).smul (hg x)

@[to_fun (attr := fun_prop)]
-/
lemma smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 𝕜 -> R} (hf : Meromorphic f)
    (hg : Meromorphic g) :
    Meromorphic (f • g) := fun x => (hf x).smul (hg x)

@[to_fun (attr := fun_prop)]
/--
lemma `const_smul` / 引理 `const_smul`

English:
lemma const_smul
  given: [SMulCommClass 𝕜 R E] (hf : Meromorphic f) (c : R)
  proof: fun x => (hf x).const_smul c

@[to_fun (attr := fun_prop)]

中文:
引理 const_smul
  条件: [SMulCommClass 𝕜 R E] (hf : Meromorphic f) (c : R)
  证明: fun x => (hf x).const_smul c

@[to_fun (attr := fun_prop)]

Depends on / 依赖: const_smul
-/
lemma const_smul [SMulCommClass 𝕜 R E] (hf : Meromorphic f) (c : R) :
    Meromorphic (c • f) := fun x => (hf x).const_smul c

@[to_fun (attr := fun_prop)]
/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  given: {f g : 𝕜 -> 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g)
  proof: fun x => (hf x).mul (hg x)

@[to_fun (attr := fun_prop)]

中文:
引理 mul
  条件: {f g : 𝕜 -> 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g)
  证明: fun x => (hf x).mul (hg x)

@[to_fun (attr := fun_prop)]
-/
lemma mul {f g : 𝕜 -> 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f * g) := fun x => (hf x).mul (hg x)

@[to_fun (attr := fun_prop)]
/--
lemma `inv` / 引理 `inv`

English:
lemma inv
  given: {f : 𝕜 -> 𝕜'} (hf : Meromorphic f)
  statement: Meromorphic f⁻¹
  proof: fun x => (hf x).inv

@[to_fun (attr := fun_prop)]

中文:
引理 inv
  条件: {f : 𝕜 -> 𝕜'} (hf : Meromorphic f)
  结论: Meromorphic f⁻¹
  证明: fun x => (hf x).inv

@[to_fun (attr := fun_prop)]
-/
lemma inv {f : 𝕜 -> 𝕜'} (hf : Meromorphic f) : Meromorphic f⁻¹ := fun x => (hf x).inv

@[to_fun (attr := fun_prop)]
/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  given: (h : forall σ in s, Meromorphic (F σ))
  proof: fun x => MeromorphicAt.prod (h · · x)

@[fun_prop]

中文:
定理 prod
  条件: (h : 对任意 σ in s, Meromorphic (F σ))
  证明: fun x => MeromorphicAt.prod (h · · x)

@[fun_prop]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.prod
-/
theorem prod (h : forall σ in s, Meromorphic (F σ)) :
    Meromorphic (∏ n in s, F n) := fun x => MeromorphicAt.prod (h · · x)

@[fun_prop]
/--
theorem `finprod` / 定理 `finprod`

English:
theorem finprod
  given: (h : forall σ, Meromorphic (F σ))
  proof: fun x => MeromorphicAt.finprod (h · x)

@[to_fun (attr := fun_prop)]

中文:
定理 finprod
  条件: (h : 对任意 σ, Meromorphic (F σ))
  证明: fun x => MeromorphicAt.finprod (h · x)

@[to_fun (attr := fun_prop)]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.finprod, finprod
-/
theorem finprod (h : forall σ, Meromorphic (F σ)) :
    Meromorphic (∏ᶠ σ, F σ) := fun x => MeromorphicAt.finprod (h · x)

@[to_fun (attr := fun_prop)]
/--
lemma `div` / 引理 `div`

English:
lemma div
  given: {f g : 𝕜 -> 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g)
  proof: fun x => (hf x).div (hg x)

@[to_fun (attr := fun_prop)]

中文:
引理 div
  条件: {f g : 𝕜 -> 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g)
  证明: fun x => (hf x).div (hg x)

@[to_fun (attr := fun_prop)]
-/
lemma div {f g : 𝕜 -> 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f / g) := fun x => (hf x).div (hg x)

@[to_fun (attr := fun_prop)]
/--
lemma `pow` / 引理 `pow`

English:
lemma pow
  given: {f : 𝕜 -> 𝕜'} {n : Nat} (hf : Meromorphic f)
  statement: Meromorphic (f ^ n)
  proof: fun x => (hf x).pow n

@[to_fun (attr := fun_prop)]

中文:
引理 pow
  条件: {f : 𝕜 -> 𝕜'} {n : 自然数} (hf : Meromorphic f)
  结论: Meromorphic (f ^ n)
  证明: fun x => (hf x).pow n

@[to_fun (attr := fun_prop)]
-/
lemma pow {f : 𝕜 -> 𝕜'} {n : Nat} (hf : Meromorphic f) : Meromorphic (f ^ n) := fun x => (hf x).pow n

@[to_fun (attr := fun_prop)]
/--
lemma `zpow` / 引理 `zpow`

English:
lemma zpow
  given: {f : 𝕜 -> 𝕜'} {n : Int} (hf : Meromorphic f)
  statement: Meromorphic (f ^ n)
  proof: fun x => (hf x).zpow n

@[fun_prop]

中文:
引理 zpow
  条件: {f : 𝕜 -> 𝕜'} {n : 整数} (hf : Meromorphic f)
  结论: Meromorphic (f ^ n)
  证明: fun x => (hf x).zpow n

@[fun_prop]
-/
lemma zpow {f : 𝕜 -> 𝕜'} {n : Int} (hf : Meromorphic f) : Meromorphic (f ^ n) := fun x => (hf x).zpow n

@[fun_prop]
/--
lemma `deriv` / 引理 `deriv`

English:
lemma deriv
  given: [CompleteSpace E] (hf : Meromorphic f)
  statement: Meromorphic (deriv f)
  proof: fun x => (hf x).deriv

@[fun_prop]

中文:
引理 deriv
  条件: [CompleteSpace E] (hf : Meromorphic f)
  结论: Meromorphic (deriv f)
  证明: fun x => (hf x).deriv

@[fun_prop]
-/
protected lemma deriv [CompleteSpace E] (hf : Meromorphic f) : Meromorphic (deriv f) :=
  fun x => (hf x).deriv

@[fun_prop]
/--
lemma `iterated_deriv` / 引理 `iterated_deriv`

English:
lemma iterated_deriv
  given: [CompleteSpace E] {n : Nat} (hf : Meromorphic f)
  proof: fun x => (hf x).iterated_deriv

中文:
引理 iterated_deriv
  条件: [CompleteSpace E] {n : 自然数} (hf : Meromorphic f)
  证明: fun x => (hf x).iterated_deriv

Depends on / 依赖: iterated_deriv
-/
lemma iterated_deriv [CompleteSpace E] {n : Nat} (hf : Meromorphic f) :
    Meromorphic (deriv^[n] f) := fun x => (hf x).iterated_deriv

/--
theorem `logDeriv` / 定理 `logDeriv`

English:
theorem logDeriv
  given: [CompleteSpace 𝕜'] {f : 𝕜 -> 𝕜'} (hf : Meromorphic f)
  proof: hf.deriv.div hf

中文:
定理 logDeriv
  条件: [CompleteSpace 𝕜'] {f : 𝕜 -> 𝕜'} (hf : Meromorphic f)
  证明: hf.deriv.div hf
-/
@[fun_prop] protected theorem logDeriv [CompleteSpace 𝕜'] {f : 𝕜 -> 𝕜'} (hf : Meromorphic f) :
    Meromorphic (logDeriv f) := hf.deriv.div hf

/--
theorem `congr_codiscrete` / 定理 `congr_codiscrete`

English:
theorem congr_codiscrete
  given: (hf : Meromorphic f) (h₁ : f =ᶠ[codiscrete 𝕜] g)
  proof: by
  rw [← meromorphicOn_univ] at *
  exact hf.congr_codiscreteWithin (eventuallyEq_of_mem h₁ fun ⦃x⦄ a => a) isOpen_univ

中文:
定理 congr_codiscrete
  条件: (hf : Meromorphic f) (h₁ : f =ᶠ[codiscrete 𝕜] g)
  证明: by
  rw [← meromorphicOn_univ] at *
  exact hf.congr_codiscreteWithin (eventuallyEq_of_mem h₁ fun ⦃x⦄ a => a) isOpen_univ

Depends on / 依赖: congr_codiscreteWithin, eventuallyEq_of_mem, hf.congr_codiscreteWithin, isOpen_univ, meromorphicOn_univ
-/
theorem congr_codiscrete (hf : Meromorphic f) (h₁ : f =ᶠ[codiscrete 𝕜] g) :
    Meromorphic g := by
  rw [← meromorphicOn_univ] at *
  exact hf.congr_codiscreteWithin (eventuallyEq_of_mem h₁ fun ⦃x⦄ a => a) isOpen_univ

/--
theorem `_root_.meromorphic_congr_codiscrete` / 定理 `_root_.meromorphic_congr_codiscrete`

English:
theorem _root_.meromorphic_congr_codiscrete
  given: (h₁ : f =ᶠ[codiscrete 𝕜] g)
  proof: ⟨(·.congr_codiscrete h₁), (·.congr_codiscrete h₁.symm)⟩

中文:
定理 _root_.meromorphic_congr_codiscrete
  条件: (h₁ : f =ᶠ[codiscrete 𝕜] g)
  证明: ⟨(·.congr_codiscrete h₁), (·.congr_codiscrete h₁.symm)⟩

Depends on / 依赖: congr_codiscrete
-/
theorem _root_.meromorphic_congr_codiscrete (h₁ : f =ᶠ[codiscrete 𝕜] g) :
    Meromorphic f ↔ Meromorphic g :=
  ⟨(·.congr_codiscrete h₁), (·.congr_codiscrete h₁.symm)⟩

/--
theorem `countable_compl_analyticAt` / 定理 `countable_compl_analyticAt`

English:
theorem countable_compl_analyticAt
  statement: [SecondCountableTopology 𝕜] [CompleteSpace E]
  proof: by
  simpa using (h.meromorphicOn (s := univ)).countable_compl_analyticAt_inter

中文:
定理 countable_compl_analyticAt
  结论: [SecondCountableTopology 𝕜] [CompleteSpace E]
  证明: by
  simpa using (h.meromorphicOn (s := univ)).countable_compl_analyticAt_inter

Depends on / 依赖: countable_compl_analyticAt_inter, h.meromorphicOn, meromorphicOn
-/
theorem countable_compl_analyticAt [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : Meromorphic f) :
    {z | AnalyticAt 𝕜 f z}ᶜ.Countable := by
  simpa using (h.meromorphicOn (s := univ)).countable_compl_analyticAt_inter

/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  statement: [MeasurableSpace 𝕜] [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
  proof: by
  set s := {z : 𝕜 | AnalyticAt 𝕜 f z}
  have h₁ : sᶜ.Countable := by simpa using h.countable_compl_analyticAt
  have h₁' := h₁.to_subtype
  have h₂ : IsOpen s := isOpen_analyticAt 𝕜 f
  have h₃ : ContinuousOn f s := fun z hz => hz.continuousAt.continuousWithinAt
  exact .of_union_range_cover (.su

中文:
定理 measurable
  结论: [MeasurableSpace 𝕜] [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
  证明: by
  set s := {z : 𝕜 | AnalyticAt 𝕜 f z}
  have h₁ : sᶜ.Countable := by simpa using h.countable_compl_analyticAt
  have h₁' := h₁.to_subtype
  have h₂ : IsOpen s := isOpen_analyticAt 𝕜 f
  have h₃ : ContinuousOn f s := fun z hz => hz.continuousAt.continuousWithinAt
  exact .of_union_range_cover (.su
-/
@[fun_prop] theorem measurable [MeasurableSpace 𝕜] [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
    [MeasurableSpace E] [CompleteSpace E] [BorelSpace E] (h : Meromorphic f) :
    Measurable f := by
  set s := {z : 𝕜 | AnalyticAt 𝕜 f z}
  have h₁ : sᶜ.Countable := by simpa using h.countable_compl_analyticAt
  have h₁' := h₁.to_subtype
  have h₂ : IsOpen s := isOpen_analyticAt 𝕜 f
  have h₃ : ContinuousOn f s := fun z hz => hz.continuousAt.continuousWithinAt
  exact .of_union_range_cover (.subtype_coe h₂.measurableSet) (.subtype_coe h₁.measurableSet)
    (by simp [-mem_compl_iff]) h₃.domRestrict.measurable (measurable_of_countable _)

/--
theorem `meromorphic_comp_add_const_iff_meromorphic` / 定理 `meromorphic_comp_add_const_iff_meromorphic`

English:
theorem meromorphic_comp_add_const_iff_meromorphic
  given: {c : 𝕜}
  proof: by
  rw [Meromorphic]; rw [Meromorphic]; rw [(Equiv.subRight c).surjective.forall]
  simp [meromorphicAt_comp_add_const_iff_meromorphicAt]

中文:
定理 meromorphic_comp_add_const_iff_meromorphic
  条件: {c : 𝕜}
  证明: by
  rw [Meromorphic]; rw [Meromorphic]; rw [(Equiv.subRight c).surjective.forall]
  simp [meromorphicAt_comp_add_const_iff_meromorphicAt]
-/
@[simp] theorem meromorphic_comp_add_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (f ∘ (· + c)) ↔ Meromorphic f := by
  rw [Meromorphic]; rw [Meromorphic]; rw [(Equiv.subRight c).surjective.forall]
  simp [meromorphicAt_comp_add_const_iff_meromorphicAt]

/--
theorem `meromorphic_fun_comp_add_const_iff_meromorphic` / 定理 `meromorphic_fun_comp_add_const_iff_meromorphic`

English:
theorem meromorphic_fun_comp_add_const_iff_meromorphic
  given: {c : 𝕜}
  proof: meromorphic_comp_add_const_iff_meromorphic

中文:
定理 meromorphic_fun_comp_add_const_iff_meromorphic
  条件: {c : 𝕜}
  证明: meromorphic_comp_add_const_iff_meromorphic
-/
@[simp] theorem meromorphic_fun_comp_add_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (fun z => f (z + c)) ↔ Meromorphic f :=
  meromorphic_comp_add_const_iff_meromorphic

/--
theorem `meromorphic_comp_sub_const_iff_meromorphic` / 定理 `meromorphic_comp_sub_const_iff_meromorphic`

English:
theorem meromorphic_comp_sub_const_iff_meromorphic
  given: {c : 𝕜}
  proof: by
  nth_rw 2 [← meromorphic_comp_add_const_iff_meromorphic (c := -c)]
  simp_rw [sub_eq_add_neg]

中文:
定理 meromorphic_comp_sub_const_iff_meromorphic
  条件: {c : 𝕜}
  证明: by
  nth_rw 2 [← meromorphic_comp_add_const_iff_meromorphic (c := -c)]
  simp_rw [sub_eq_add_neg]
-/
@[simp] theorem meromorphic_comp_sub_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (f ∘ (· - c)) ↔ Meromorphic f := by
  nth_rw 2 [← meromorphic_comp_add_const_iff_meromorphic (c := -c)]
  simp_rw [sub_eq_add_neg]

/--
theorem `meromorphic_fun_comp_sub_const_iff_meromorphic` / 定理 `meromorphic_fun_comp_sub_const_iff_meromorphic`

English:
theorem meromorphic_fun_comp_sub_const_iff_meromorphic
  given: {c : 𝕜}
  proof: meromorphic_comp_sub_const_iff_meromorphic

中文:
定理 meromorphic_fun_comp_sub_const_iff_meromorphic
  条件: {c : 𝕜}
  证明: meromorphic_comp_sub_const_iff_meromorphic
-/
@[simp] theorem meromorphic_fun_comp_sub_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (fun z => f (z - c)) ↔ Meromorphic f :=
  meromorphic_comp_sub_const_iff_meromorphic

end Meromorphic
