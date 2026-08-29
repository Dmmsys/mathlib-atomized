/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Module.Card
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Cardinal.CountableCover
public import Mathlib.Topology.MetricSpace.Perfect

/-!
# Cardinality of open subsets of vector spaces

Any nonempty open subset of a topological vector space over a nontrivially normed field has the same
cardinality as the whole space. This is proved in `cardinal_eq_of_isOpen`.

We deduce that a countable set in a nontrivial vector space over a complete nontrivially normed
field has dense complement, in `Set.Countable.dense_compl`. This follows from the previous
argument and the fact that a complete nontrivially normed field has cardinality at least
continuum, proved in `continuum_le_cardinal_of_nontriviallyNormedField`.
-/

public section
universe u v

open Filter Pointwise Set Function Cardinal
open scoped Cardinal Topology

/--
theorem `continuum_le_cardinal_of_nontriviallyNormedField` / 定理 `continuum_le_cardinal_of_nontriviallyNormedField`

English:
theorem continuum_le_cardinal_of_nontriviallyNormedField
  proof: by
  suffices exists f : (Nat -> Bool) -> 𝕜, range f subseteq univ ∧ Continuous f ∧ Injective f by
    rcases this with ⟨f, -, -, f_inj⟩
    simpa using lift_mk_le_lift_mk_of_injective f_inj
  apply Perfect.exists_nat_bool_injection _ univ_nonempty
  refine ⟨isClosed_univ, preperfect_iff_nhds.2 (fun x _ U hU => ?_)⟩
  rcases NormedField.exists_norm_lt_one 𝕜 with ⟨c, c_pos, hc⟩
  have A : Tendsto (fun n => x + c ^ n) atTop (𝓝 (x + 0)) :=
    tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc)
  rw [add_zero] at A
  have B : forallᶠ n in atTop, x + c ^ n in U := tendsto_def.1 A U hU
  rcases B.exists with ⟨n, hn⟩
  refine ⟨x + c^n, by simpa using hn, ?_⟩
  simp only [add_ne_left]
  apply pow_ne_zero
  simpa using c_pos

中文:
定理 continuum_le_cardinal_of_nontriviallyNormedField
  证明: by
  suffices exists f : (Nat -> Bool) -> 𝕜, range f subseteq univ ∧ Continuous f ∧ Injective f by
    rcases this with ⟨f, -, -, f_inj⟩
    simpa using lift_mk_le_lift_mk_of_injective f_inj
  apply Perfect.exists_nat_bool_injection _ univ_nonempty
  refine ⟨isClosed_univ, preperfect_iff_nhds.2 (fun x _ U hU => ?_)⟩
  rcases NormedField.exists_norm_lt_one 𝕜 with ⟨c, c_pos, hc⟩
  have A : Tendsto (fun n => x + c ^ n) atTop (𝓝 (x + 0)) :=
    tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc)
  rw [add_zero] at A
  have B : forallᶠ n in atTop, x + c ^ n in U := tendsto_def.1 A U hU
  rcases B.exists with ⟨n, hn⟩
  refine ⟨x + c^n, by simpa using hn, ?_⟩
  simp only [add_ne_left]
  apply pow_ne_zero
  simpa using c_pos

Depends on / 依赖: Continuous, Injective, NormedField, NormedField.exists_norm_lt_one, Perfect, Perfect.exists_nat_bool_injection, Tendsto, c_pos, exists_nat_bool_injection, exists_norm_lt_one, f_inj, isClosed_univ, lift_mk_le_lift_mk_of_injective, preperfect_iff_nhds, subseteq, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_pow_atTop_nhds_zero_of_norm_lt_one, univ_nonempty
-/
theorem continuum_le_cardinal_of_nontriviallyNormedField
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] : 𝔠 <= #𝕜 := by
  suffices exists f : (Nat -> Bool) -> 𝕜, range f subseteq univ ∧ Continuous f ∧ Injective f by
    rcases this with ⟨f, -, -, f_inj⟩
    simpa using lift_mk_le_lift_mk_of_injective f_inj
  apply Perfect.exists_nat_bool_injection _ univ_nonempty
  refine ⟨isClosed_univ, preperfect_iff_nhds.2 (fun x _ U hU => ?_)⟩
  rcases NormedField.exists_norm_lt_one 𝕜 with ⟨c, c_pos, hc⟩
  have A : Tendsto (fun n => x + c ^ n) atTop (𝓝 (x + 0)) :=
    tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc)
  rw [add_zero] at A
  have B : forallᶠ n in atTop, x + c ^ n in U := tendsto_def.1 A U hU
  rcases B.exists with ⟨n, hn⟩
  refine ⟨x + c^n, by simpa using hn, ?_⟩
  simp only [add_ne_left]
  apply pow_ne_zero
  simpa using c_pos

/--
theorem `continuum_le_cardinal_of_module` / 定理 `continuum_le_cardinal_of_module`

English:
theorem continuum_le_cardinal_of_module
  proof: by
  have A : lift.{v} (𝔠 : Cardinal.{u}) <= lift.{v} (#𝕜) := by
    simpa using continuum_le_cardinal_of_nontriviallyNormedField 𝕜
  simpa using A.trans (Cardinal.mk_le_of_module 𝕜 E)

中文:
定理 continuum_le_cardinal_of_module
  证明: by
  have A : lift.{v} (𝔠 : Cardinal.{u}) <= lift.{v} (#𝕜) := by
    simpa using continuum_le_cardinal_of_nontriviallyNormedField 𝕜
  simpa using A.trans (Cardinal.mk_le_of_module 𝕜 E)

Depends on / 依赖: A.trans, Cardinal, Cardinal.mk_le_of_module, continuum_le_cardinal_of_nontriviallyNormedField, mk_le_of_module
-/
theorem continuum_le_cardinal_of_module
    (𝕜 : Type u) (E : Type v) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Nontrivial E] : 𝔠 <= #E := by
  have A : lift.{v} (𝔠 : Cardinal.{u}) <= lift.{v} (#𝕜) := by
    simpa using continuum_le_cardinal_of_nontriviallyNormedField 𝕜
  simpa using A.trans (Cardinal.mk_le_of_module 𝕜 E)

/--
lemma `cardinal_eq_of_mem_nhds_zero` / 引理 `cardinal_eq_of_mem_nhds_zero`

English:
lemma cardinal_eq_of_mem_nhds_zero
  proof: by
  /- As `s` is a neighborhood of `0`, the space is covered by the rescaled sets `c^n • s`,
  where `c` is any element of `𝕜` with norm `> 1`. All these sets are in bijection and have
  therefore the same cardinality. The conclusion follows. -/
  obtain ⟨c, hc⟩ : exists x : 𝕜, 1 < ‖x‖ := NormedField.exists_lt_norm 𝕜 1
  have cn_ne : forall n, c ^ n != 0 := by
    intro n
    apply pow_ne_zero
    rintro rfl
    simp only [norm_zero] at hc
    exact lt_irrefl _ (hc.trans zero_lt_one)
  have A : forall (x : E), forallᶠ n in (atTop : Filter Nat), x in c ^ n • s := by
    intro x
    have : Tendsto (fun n => (c ^ n)⁻¹ • x) atTop (𝓝 ((0 : 𝕜) • x)) := by
      have : Tendsto (fun n => (c ^ n)⁻¹) atTop (𝓝 0) := by
        simp_rw [← inv_pow]
        apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hc
      exact Tendsto.smul_const this x
    rw [zero_smul] at this
    filter_upwards [this hs] with n (hn : (c ^ n)⁻¹ • x in s)
    exact (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).2 hn
  have B : forall n, #(c ^ n • s :) = #s := by
    intro n
    have : (c ^ n • s :) ≃ s :=
    { toFun := fun x => ⟨(c ^ n)⁻¹ • x.1, (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).1 x.2⟩
      invFun := fun x => ⟨(c^n) • x.1, smul_mem_smul_set x.2⟩
      left_inv := fun x => by simp [smul_smul, mul_inv_cancel₀ (cn_ne n)]
      right_inv := fun x => by simp [smul_smul, inv_mul_cancel₀ (cn_ne n)] }
    exact Cardinal.mk_congr this
  apply (Cardinal.mk_of_countable_eventually_mem A B).symm

中文:
引理 cardinal_eq_of_mem_nhds_zero
  证明: by
  /- As `s` is a neighborhood of `0`, the space is covered by the rescaled sets `c^n • s`,
  where `c` is any element of `𝕜` with norm `> 1`. All these sets are in bijection and have
  therefore the same cardinality. The conclusion follows. -/
  obtain ⟨c, hc⟩ : exists x : 𝕜, 1 < ‖x‖ := NormedField.exists_lt_norm 𝕜 1
  have cn_ne : forall n, c ^ n != 0 := by
    intro n
    apply pow_ne_zero
    rintro rfl
    simp only [norm_zero] at hc
    exact lt_irrefl _ (hc.trans zero_lt_one)
  have A : forall (x : E), forallᶠ n in (atTop : Filter Nat), x in c ^ n • s := by
    intro x
    have : Tendsto (fun n => (c ^ n)⁻¹ • x) atTop (𝓝 ((0 : 𝕜) • x)) := by
      have : Tendsto (fun n => (c ^ n)⁻¹) atTop (𝓝 0) := by
        simp_rw [← inv_pow]
        apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hc
      exact Tendsto.smul_const this x
    rw [zero_smul] at this
    filter_upwards [this hs] with n (hn : (c ^ n)⁻¹ • x in s)
    exact (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).2 hn
  have B : forall n, #(c ^ n • s :) = #s := by
    intro n
    have : (c ^ n • s :) ≃ s :=
    { toFun := fun x => ⟨(c ^ n)⁻¹ • x.1, (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).1 x.2⟩
      invFun := fun x => ⟨(c^n) • x.1, smul_mem_smul_set x.2⟩
      left_inv := fun x => by simp [smul_smul, mul_inv_cancel₀ (cn_ne n)]
      right_inv := fun x => by simp [smul_smul, inv_mul_cancel₀ (cn_ne n)] }
    exact Cardinal.mk_congr this
  apply (Cardinal.mk_of_countable_eventually_mem A B).symm
-/
lemma cardinal_eq_of_mem_nhds_zero
    {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [Zero E] [MulActionWithZero 𝕜 E]
    [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} (hs : s in 𝓝 (0 : E)) : #s = #E := by
  /- As `s` is a neighborhood of `0`, the space is covered by the rescaled sets `c^n • s`,
  where `c` is any element of `𝕜` with norm `> 1`. All these sets are in bijection and have
  therefore the same cardinality. The conclusion follows. -/
  obtain ⟨c, hc⟩ : exists x : 𝕜, 1 < ‖x‖ := NormedField.exists_lt_norm 𝕜 1
  have cn_ne : forall n, c ^ n != 0 := by
    intro n
    apply pow_ne_zero
    rintro rfl
    simp only [norm_zero] at hc
    exact lt_irrefl _ (hc.trans zero_lt_one)
  have A : forall (x : E), forallᶠ n in (atTop : Filter Nat), x in c ^ n • s := by
    intro x
    have : Tendsto (fun n => (c ^ n)⁻¹ • x) atTop (𝓝 ((0 : 𝕜) • x)) := by
      have : Tendsto (fun n => (c ^ n)⁻¹) atTop (𝓝 0) := by
        simp_rw [← inv_pow]
        apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hc
      exact Tendsto.smul_const this x
    rw [zero_smul] at this
    filter_upwards [this hs] with n (hn : (c ^ n)⁻¹ • x in s)
    exact (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).2 hn
  have B : forall n, #(c ^ n • s :) = #s := by
    intro n
    have : (c ^ n • s :) ≃ s :=
    { toFun := fun x => ⟨(c ^ n)⁻¹ • x.1, (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).1 x.2⟩
      invFun := fun x => ⟨(c^n) • x.1, smul_mem_smul_set x.2⟩
      left_inv := fun x => by simp [smul_smul, mul_inv_cancel₀ (cn_ne n)]
      right_inv := fun x => by simp [smul_smul, inv_mul_cancel₀ (cn_ne n)] }
    exact Cardinal.mk_congr this
  apply (Cardinal.mk_of_countable_eventually_mem A B).symm

/--
theorem `cardinal_eq_of_mem_nhds` / 定理 `cardinal_eq_of_mem_nhds`

English:
theorem cardinal_eq_of_mem_nhds
  proof: by
  let g := Homeomorph.addLeft x
  let t := g ⁻¹' s
  have : t in 𝓝 0 := g.continuous.continuousAt.preimage_mem_nhds (by simpa [g] using hs)
  have A : #t = #E := cardinal_eq_of_mem_nhds_zero 𝕜 this
  have B : #t = #s := Cardinal.mk_subtype_of_equiv (· in s) g.toEquiv
  rwa [B] at A

中文:
定理 cardinal_eq_of_mem_nhds
  证明: by
  let g := Homeomorph.addLeft x
  let t := g ⁻¹' s
  have : t in 𝓝 0 := g.continuous.continuousAt.preimage_mem_nhds (by simpa [g] using hs)
  have A : #t = #E := cardinal_eq_of_mem_nhds_zero 𝕜 this
  have B : #t = #s := Cardinal.mk_subtype_of_equiv (· in s) g.toEquiv
  rwa [B] at A

Depends on / 依赖: Cardinal, Cardinal.mk_subtype_of_equiv, Homeomorph, Homeomorph.addLeft, addLeft, cardinal_eq_of_mem_nhds_zero, continuous, continuousAt, g.continuous.continuousAt.preimage_mem_nhds, g.toEquiv, mk_subtype_of_equiv, preimage_mem_nhds, toEquiv
-/
theorem cardinal_eq_of_mem_nhds
    {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [AddGroup E] [MulActionWithZero 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {s : Set E} {x : E} (hs : s in 𝓝 x) : #s = #E := by
  let g := Homeomorph.addLeft x
  let t := g ⁻¹' s
  have : t in 𝓝 0 := g.continuous.continuousAt.preimage_mem_nhds (by simpa [g] using hs)
  have A : #t = #E := cardinal_eq_of_mem_nhds_zero 𝕜 this
  have B : #t = #s := Cardinal.mk_subtype_of_equiv (· in s) g.toEquiv
  rwa [B] at A

/--
theorem `cardinal_eq_of_isOpen` / 定理 `cardinal_eq_of_isOpen`

English:
theorem cardinal_eq_of_isOpen
  proof: by
  rcases h's with ⟨x, hx⟩
  exact cardinal_eq_of_mem_nhds 𝕜 (hs.mem_nhds hx)

中文:
定理 cardinal_eq_of_isOpen
  证明: by
  rcases h's with ⟨x, hx⟩
  exact cardinal_eq_of_mem_nhds 𝕜 (hs.mem_nhds hx)

Depends on / 依赖: cardinal_eq_of_mem_nhds, hs.mem_nhds, mem_nhds
-/
theorem cardinal_eq_of_isOpen
    {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [AddGroup E] [MulActionWithZero 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {s : Set E}
    (hs : IsOpen s) (h's : s.Nonempty) : #s = #E := by
  rcases h's with ⟨x, hx⟩
  exact cardinal_eq_of_mem_nhds 𝕜 (hs.mem_nhds hx)

/--
theorem `continuum_le_cardinal_of_isOpen` / 定理 `continuum_le_cardinal_of_isOpen`

English:
theorem continuum_le_cardinal_of_isOpen
  proof: by
  simpa [cardinal_eq_of_isOpen 𝕜 hs h's] using continuum_le_cardinal_of_module 𝕜 E

中文:
定理 continuum_le_cardinal_of_isOpen
  证明: by
  simpa [cardinal_eq_of_isOpen 𝕜 hs h's] using continuum_le_cardinal_of_module 𝕜 E

Depends on / 依赖: cardinal_eq_of_isOpen, continuum_le_cardinal_of_module
-/
theorem continuum_le_cardinal_of_isOpen
    {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Nontrivial E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {s : Set E} (hs : IsOpen s) (h's : s.Nonempty) : 𝔠 <= #s := by
  simpa [cardinal_eq_of_isOpen 𝕜 hs h's] using continuum_le_cardinal_of_module 𝕜 E

/--
theorem `Set.Countable.dense_compl` / 定理 `Set.Countable.dense_compl`

English:
theorem Set.Countable.dense_compl
  proof: by
  rw [← interior_eq_empty_iff_dense_compl]
  by_contra H
  apply lt_irrefl (ℵ₀ : Cardinal.{u})
  calc
    (ℵ₀ : Cardinal.{u}) < 𝔠 := aleph0_lt_continuum
    _ <= #(interior s) :=
      continuum_le_cardinal_of_isOpen 𝕜 isOpen_interior (notMem_singleton_empty.1 H)
    _ <= #s := mk_le_mk_of_subset interior_subset
    _ <= ℵ₀ := le_aleph0 hs

中文:
定理 集合.可数.dense_compl
  证明: by
  rw [← interior_eq_empty_iff_dense_compl]
  by_contra H
  apply lt_irrefl (ℵ₀ : Cardinal.{u})
  calc
    (ℵ₀ : Cardinal.{u}) < 𝔠 := aleph0_lt_continuum
    _ <= #(interior s) :=
      continuum_le_cardinal_of_isOpen 𝕜 isOpen_interior (notMem_singleton_empty.1 H)
    _ <= #s := mk_le_mk_of_subset interior_subset
    _ <= ℵ₀ := le_aleph0 hs

Depends on / 依赖: Cardinal, aleph0_lt_continuum, continuum_le_cardinal_of_isOpen, interior, interior_eq_empty_iff_dense_compl, interior_subset, isOpen_interior, le_aleph0, lt_irrefl, mk_le_mk_of_subset, notMem_singleton_empty
-/
theorem Set.Countable.dense_compl
    {E : Type u} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Nontrivial E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {s : Set E} (hs : s.Countable) : Dense sᶜ := by
  rw [← interior_eq_empty_iff_dense_compl]
  by_contra H
  apply lt_irrefl (ℵ₀ : Cardinal.{u})
  calc
    (ℵ₀ : Cardinal.{u}) < 𝔠 := aleph0_lt_continuum
    _ <= #(interior s) :=
      continuum_le_cardinal_of_isOpen 𝕜 isOpen_interior (notMem_singleton_empty.1 H)
    _ <= #s := mk_le_mk_of_subset interior_subset
    _ <= ℵ₀ := le_aleph0 hs
