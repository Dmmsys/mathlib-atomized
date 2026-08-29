/-
Copyright (c) 2026 Huanyu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Discreteness of the zeros of the Riemann zeta function

We show that the zeros of the Riemann zeta function form a discrete subset of `ℂ`,
so that in particular any compact subset of `ℂ` contains only finitely many zeros.

## Main declarations

* `riemannZetaZeros`: The zeros of Riemann zeta function.

## Main results

* `isClosed_riemannZetaZeros`: `riemannZetaZeros` is closed.

* `isDiscrete_riemannZetaZeros`: `riemannZetaZeros` is discrete.

* `IsCompact.inter_riemannZetaZeros_finite`: for any compact set `S : Set ℂ`, the intersection
  `S ∩ riemannZetaZeros` is finite.
-/

@[expose] public section

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `riemannZetaZeros` / `riemannZetaZeros` 的定义

English:
definition riemannZetaZeros
  signature: : Set Complex
  body: riemannZeta ⁻¹' {0}

中文:
定义 riemannZetaZeros
  签名: : 集合 复形
  定义体: riemannZeta ⁻¹' {0}

Depends on / 依赖: riemannZeta
-/
noncomputable def riemannZetaZeros : Set Complex := riemannZeta ⁻¹' {0}

/--
lemma `mem_riemannZetaZeros` / 引理 `mem_riemannZetaZeros`

English:
lemma mem_riemannZetaZeros
  given: {z : Complex}
  proof: .rfl

中文:
引理 mem_riemannZetaZeros
  条件: {z : 复形}
  证明: .rfl
-/
lemma mem_riemannZetaZeros {z : Complex} :
    z in riemannZetaZeros ↔ riemannZeta z = 0 := .rfl

/--
lemma `riemannZetaZeros_codiscreteWithin_compl_one` / 引理 `riemannZetaZeros_codiscreteWithin_compl_one`

English:
lemma riemannZetaZeros_codiscreteWithin_compl_one
  proof: by
  refine analyticOn_riemannZeta.preimage_zero_mem_codiscreteWithin (x := 2) ?_ (by simp) ?_
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact isConnected_compl_singleton_of_one_lt_rank (by simp) 1

中文:
引理 riemannZetaZeros_codiscreteWithin_compl_one
  证明: by
  refine analyticOn_riemannZeta.preimage_zero_mem_codiscreteWithin (x := 2) ?_ (by simp) ?_
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact isConnected_compl_singleton_of_one_lt_rank (by simp) 1
-/
private lemma riemannZetaZeros_codiscreteWithin_compl_one :
    riemannZetaZerosᶜ in Filter.codiscreteWithin {1}ᶜ := by
  refine analyticOn_riemannZeta.preimage_zero_mem_codiscreteWithin (x := 2) ?_ (by simp) ?_
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact isConnected_compl_singleton_of_one_lt_rank (by simp) 1

/--
lemma `compl_riemannZetaZeros_mem_codiscrete` / 引理 `compl_riemannZetaZeros_mem_codiscrete`

English:
lemma compl_riemannZetaZeros_mem_codiscrete
  proof: by
  have := riemannZetaZeros_codiscreteWithin_compl_one
  simp only [mem_codiscreteWithin, Set.mem_compl_iff, Set.mem_singleton_iff, sdiff_compl,
    Set.inf_eq_inter, Filter.disjoint_principal_right, mem_codiscrete, compl_compl] at this ⊢
  intro x
  rcases eq_or_ne x 1 with rfl | hx
  · exact riemannZeta_eventually_ne_zero_nhds_one.filter_mono nhdsWithin_le_nhds
  · exact Filter.mem_of_superset (this x hx)
      (by grind [riemannZeta_one_ne_zero, mem_riemannZetaZeros])

中文:
引理 compl_riemannZetaZeros_mem_codiscrete
  证明: by
  have := riemannZetaZeros_codiscreteWithin_compl_one
  simp only [mem_codiscreteWithin, Set.mem_compl_iff, Set.mem_singleton_iff, sdiff_compl,
    Set.inf_eq_inter, Filter.disjoint_principal_right, mem_codiscrete, compl_compl] at this ⊢
  intro x
  rcases eq_or_ne x 1 with rfl | hx
  · exact riemannZeta_eventually_ne_zero_nhds_one.filter_mono nhdsWithin_le_nhds
  · exact Filter.mem_of_superset (this x hx)
      (by grind [riemannZeta_one_ne_zero, mem_riemannZetaZeros])
-/
private lemma compl_riemannZetaZeros_mem_codiscrete :
    riemannZetaZerosᶜ in Filter.codiscrete Complex := by
  have := riemannZetaZeros_codiscreteWithin_compl_one
  simp only [mem_codiscreteWithin, Set.mem_compl_iff, Set.mem_singleton_iff, sdiff_compl,
    Set.inf_eq_inter, Filter.disjoint_principal_right, mem_codiscrete, compl_compl] at this ⊢
  intro x
  rcases eq_or_ne x 1 with rfl | hx
  · exact riemannZeta_eventually_ne_zero_nhds_one.filter_mono nhdsWithin_le_nhds
  · exact Filter.mem_of_superset (this x hx)
      (by grind [riemannZeta_one_ne_zero, mem_riemannZetaZeros])

/--
lemma `isClosed_riemannZetaZeros` / 引理 `isClosed_riemannZetaZeros`

English:
lemma isClosed_riemannZetaZeros
  statement: IsClosed riemannZetaZeros
  proof: by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).1

中文:
引理 isClosed_riemannZetaZeros
  结论: 是闭集 riemannZetaZeros
  证明: by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).1

Depends on / 依赖: compl_riemannZetaZeros_mem_codiscrete, mem_codiscrete
-/
lemma isClosed_riemannZetaZeros : IsClosed riemannZetaZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).1

/--
lemma `isDiscrete_riemannZetaZeros` / 引理 `isDiscrete_riemannZetaZeros`

English:
lemma isDiscrete_riemannZetaZeros
  statement: IsDiscrete riemannZetaZeros
  proof: by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).2

中文:
引理 isDiscrete_riemannZetaZeros
  结论: 是离散 riemannZetaZeros
  证明: by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).2

Depends on / 依赖: compl_riemannZetaZeros_mem_codiscrete, mem_codiscrete
-/
lemma isDiscrete_riemannZetaZeros : IsDiscrete riemannZetaZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).2

/--
lemma `IsCompact.inter_riemannZetaZeros_finite` / 引理 `IsCompact.inter_riemannZetaZeros_finite`

English:
lemma IsCompact.inter_riemannZetaZeros_finite
  given: {S : Set Complex} (hS : IsCompact S)
  proof: by
  apply (hS.inter_right isClosed_riemannZetaZeros).finite
  exact isDiscrete_riemannZetaZeros.mono Set.inter_subset_right

中文:
引理 是紧集.inter_riemannZetaZeros_finite
  条件: {S : 集合 复形} (hS : 是紧集 S)
  证明: by
  apply (hS.inter_right isClosed_riemannZetaZeros).finite
  exact isDiscrete_riemannZetaZeros.mono Set.inter_subset_right

Depends on / 依赖: Set.inter_subset_right, finite, hS.inter_right, inter_right, inter_subset_right, isClosed_riemannZetaZeros, isDiscrete_riemannZetaZeros, isDiscrete_riemannZetaZeros.mono
-/
lemma IsCompact.inter_riemannZetaZeros_finite {S : Set Complex} (hS : IsCompact S) :
    (S inter riemannZetaZeros).Finite := by
  apply (hS.inter_right isClosed_riemannZetaZeros).finite
  exact isDiscrete_riemannZetaZeros.mono Set.inter_subset_right

open Filter in
/--
lemma `tendsto_riemannZeta_cofinite_cocompact` / 引理 `tendsto_riemannZeta_cofinite_cocompact`

English:
lemma tendsto_riemannZeta_cofinite_cocompact
  proof: isClosed_riemannZetaZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannZetaZeros

中文:
引理 tendsto_riemannZeta_cofinite_cocompact
  证明: isClosed_riemannZetaZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannZetaZeros

Depends on / 依赖: isClosed_riemannZetaZeros, isClosed_riemannZetaZeros.tendsto_coe_cofinite_of_isDiscrete, isDiscrete_riemannZetaZeros, tendsto_coe_cofinite_of_isDiscrete
-/
lemma tendsto_riemannZeta_cofinite_cocompact :
    Tendsto ((↑) : riemannZetaZeros -> Complex) cofinite (cocompact Complex) :=
  isClosed_riemannZetaZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannZetaZeros

end
