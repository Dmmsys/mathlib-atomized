/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated pointwise
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.SimpleFunc.nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `SimpleFunc` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `MeasureTheory.SimpleFunc.approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.

## Main results

* `tendsto_approxOn` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.

## Notation

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/

@[expose] public section

open Set Function Filter TopologicalSpace Metric MeasureTheory
open scoped Topology ENNReal

variable {α β : Type*}

noncomputable section

namespace MeasureTheory

local infixr:25 " ->ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Pointwise approximation by simple functions -/


variable [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]

/--
Definition of `nearestPtInd` / `nearestPtInd` 的定义

English:
definition nearestPtInd
  signature: (e : Nat -> α)

中文:
定义 nearestPtInd
  签名: (e : 自然数 -> α)
-/
noncomputable def nearestPtInd (e : Nat -> α) : Nat -> α ->ₛ Nat
  | 0 => const α 0
  | N + 1 =>
    piecewise (⋂ k <= N, { x | edist (e (N + 1)) x < edist (e k) x })
      (MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ =>
          measurableSet_lt measurable_edist_right measurable_edist_right)
      (const α <| N + 1) (nearestPtInd e N)

/--
Definition of `nearestPt` / `nearestPt` 的定义

English:
definition nearestPt
  signature: (e : Nat -> α) (N : Nat)
  body: (nearestPtInd e N).map e

@[simp]

中文:
定义 nearestPt
  签名: (e : 自然数 -> α) (N : 自然数)
  定义体: (nearestPtInd e N).map e

@[simp]

Depends on / 依赖: nearestPtInd
-/
noncomputable def nearestPt (e : Nat -> α) (N : Nat) : α ->ₛ α :=
  (nearestPtInd e N).map e

@[simp]
/--
theorem `nearestPtInd_zero` / 定理 `nearestPtInd_zero`

English:
theorem nearestPtInd_zero
  given: (e : Nat -> α)
  statement: nearestPtInd e 0 = const α 0
  proof: rfl

@[simp]

中文:
定理 nearestPtInd_zero
  条件: (e : 自然数 -> α)
  结论: nearestPtInd e 0 = const α 0
  证明: rfl

@[simp]
-/
theorem nearestPtInd_zero (e : Nat -> α) : nearestPtInd e 0 = const α 0 :=
  rfl

@[simp]
/--
theorem `nearestPt_zero` / 定理 `nearestPt_zero`

English:
theorem nearestPt_zero
  given: (e : Nat -> α)
  statement: nearestPt e 0 = const α (e 0)
  proof: rfl

中文:
定理 nearestPt_zero
  条件: (e : 自然数 -> α)
  结论: nearestPt e 0 = const α (e 0)
  证明: rfl
-/
theorem nearestPt_zero (e : Nat -> α) : nearestPt e 0 = const α (e 0) :=
  rfl

/--
theorem `nearestPtInd_succ` / 定理 `nearestPtInd_succ`

English:
theorem nearestPtInd_succ
  given: (e : Nat -> α) (N : Nat) (x : α)
  proof: by
  simp only [nearestPtInd, coe_piecewise, Set.piecewise]
  congr
  simp

中文:
定理 nearestPtInd_succ
  条件: (e : 自然数 -> α) (N : 自然数) (x : α)
  证明: by
  simp only [nearestPtInd, coe_piecewise, Set.piecewise]
  congr
  simp

Depends on / 依赖: Set.piecewise, coe_piecewise, nearestPtInd, piecewise
-/
theorem nearestPtInd_succ (e : Nat -> α) (N : Nat) (x : α) :
    nearestPtInd e (N + 1) x =
      if forall k <= N, edist (e (N + 1)) x < edist (e k) x then N + 1 else nearestPtInd e N x := by
  simp only [nearestPtInd, coe_piecewise, Set.piecewise]
  congr
  simp

/--
theorem `nearestPtInd_le` / 定理 `nearestPtInd_le`

English:
theorem nearestPtInd_le
  given: (e : Nat -> α) (N : Nat) (x : α)
  statement: nearestPtInd e N x <= N
  proof: by
  induction N with
  | zero => simp
  | succ N ihN =>
    simp only [nearestPtInd_succ]
    split_ifs
    exacts [le_rfl, ihN.trans N.le_succ]

中文:
定理 nearestPtInd_le
  条件: (e : 自然数 -> α) (N : 自然数) (x : α)
  结论: nearestPtInd e N x <= N
  证明: by
  induction N with
  | zero => simp
  | succ N ihN =>
    simp only [nearestPtInd_succ]
    split_ifs
    exacts [le_rfl, ihN.trans N.le_succ]

Depends on / 依赖: N.le_succ, exacts, ihN.trans, le_rfl, le_succ, nearestPtInd_succ, split_ifs
-/
theorem nearestPtInd_le (e : Nat -> α) (N : Nat) (x : α) : nearestPtInd e N x <= N := by
  induction N with
  | zero => simp
  | succ N ihN =>
    simp only [nearestPtInd_succ]
    split_ifs
    exacts [le_rfl, ihN.trans N.le_succ]

/--
theorem `edist_nearestPt_le` / 定理 `edist_nearestPt_le`

English:
theorem edist_nearestPt_le
  given: (e : Nat -> α) (x : α) {k N : Nat} (hk : k <= N)
  proof: by
  induction N generalizing k with
  | zero => simp [nonpos_iff_eq_zero.1 hk]
  | succ N ihN =>
    simp only [nearestPt, nearestPtInd_succ, map_apply]
    split_ifs with h
    · rcases hk.eq_or_lt with (rfl | hk)
      exacts [le_rfl, (h k (Nat.lt_succ_iff.1 hk)).le]
    · push Not at h
      rca

中文:
定理 edist_nearestPt_le
  条件: (e : 自然数 -> α) (x : α) {k N : 自然数} (hk : k <= N)
  证明: by
  induction N generalizing k with
  | zero => simp [nonpos_iff_eq_zero.1 hk]
  | succ N ihN =>
    simp only [nearestPt, nearestPtInd_succ, map_apply]
    split_ifs with h
    · rcases hk.eq_or_lt with (rfl | hk)
      exacts [le_rfl, (h k (Nat.lt_succ_iff.1 hk)).le]
    · push Not at h
      rca

Depends on / 依赖: Nat.lt_succ_iff, eq_or_lt, exacts, generalizing, hk.eq_or_lt, le_rfl, lt_succ_iff, map_apply, nearestPt, nearestPtInd_succ, nonpos_iff_eq_zero, split_ifs
-/
theorem edist_nearestPt_le (e : Nat -> α) (x : α) {k N : Nat} (hk : k <= N) :
    edist (nearestPt e N x) x <= edist (e k) x := by
  induction N generalizing k with
  | zero => simp [nonpos_iff_eq_zero.1 hk]
  | succ N ihN =>
    simp only [nearestPt, nearestPtInd_succ, map_apply]
    split_ifs with h
    · rcases hk.eq_or_lt with (rfl | hk)
      exacts [le_rfl, (h k (Nat.lt_succ_iff.1 hk)).le]
    · push Not at h
      rcases h with ⟨l, hlN, hxl⟩
      rcases hk.eq_or_lt with (rfl | hk)
      exacts [(ihN hlN).trans hxl, ihN (Nat.lt_succ_iff.1 hk)]

/--
theorem `tendsto_nearestPt` / 定理 `tendsto_nearestPt`

English:
theorem tendsto_nearestPt
  given: {e : Nat -> α} {x : α} (hx : x in closure (range e))
  proof: by
  refine (atTop_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => ?_
  rcases EMetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
  rw [edist_comm] at hN
  exact ⟨N, trivial, fun n hn => (edist_nearestPt_le e x hn).trans_lt hN⟩

中文:
定理 tendsto_nearestPt
  条件: {e : 自然数 -> α} {x : α} (hx : x in closure (range e))
  证明: by
  refine (atTop_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => ?_
  rcases EMetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
  rw [edist_comm] at hN
  exact ⟨N, trivial, fun n hn => (edist_nearestPt_le e x hn).trans_lt hN⟩

Depends on / 依赖: EMetric, EMetric.mem_closure_iff, atTop_basis, atTop_basis.tendsto_iff, edist_comm, edist_nearestPt_le, mem_closure_iff, nhds_basis_eball, tendsto_iff, trans_lt
-/
theorem tendsto_nearestPt {e : Nat -> α} {x : α} (hx : x in closure (range e)) :
    Tendsto (fun N => nearestPt e N x) atTop (𝓝 x) := by
  refine (atTop_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => ?_
  rcases EMetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
  rw [edist_comm] at hN
  exact ⟨N, trivial, fun n hn => (edist_nearestPt_le e x hn).trans_lt hN⟩

variable [MeasurableSpace β] {f : β -> α}

/--
Definition of `approxOn` / `approxOn` 的定义

English:
definition approxOn
  signature: (f : β -> α) (hf : Measurable f) (s : Set α) (y₀ : α) (h₀ : y₀ in s)
  body: haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  comp (nearestPt (fun k => Nat.casesOn k y₀ ((↑) ∘ denseSeq s) : Nat -> α) n) f hf

@[simp]

中文:
定义 approxOn
  签名: (f : β -> α) (hf : Measurable f) (s : Set α) (y₀ : α) (h₀ : y₀ in s)
  定义体: haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  comp (nearestPt (fun k => Nat.casesOn k y₀ ((↑) ∘ denseSeq s) : Nat -> α) n) f hf

@[simp]

Depends on / 依赖: Nat.casesOn, Nonempty, casesOn, denseSeq, nearestPt
-/
noncomputable def approxOn (f : β -> α) (hf : Measurable f) (s : Set α) (y₀ : α) (h₀ : y₀ in s)
    [SeparableSpace s] (n : Nat) : β ->ₛ α :=
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  comp (nearestPt (fun k => Nat.casesOn k y₀ ((↑) ∘ denseSeq s) : Nat -> α) n) f hf

@[simp]
/--
theorem `approxOn_zero` / 定理 `approxOn_zero`

English:
theorem approxOn_zero
  statement: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  proof: rfl

中文:
定理 approxOn_zero
  结论: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  证明: rfl
-/
theorem approxOn_zero {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
    [SeparableSpace s] (x : β) : approxOn f hf s y₀ h₀ 0 x = y₀ :=
  rfl

/--
theorem `approxOn_mem` / 定理 `approxOn_mem`

English:
theorem approxOn_mem
  statement: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  proof: by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  suffices forall n, (Nat.casesOn n y₀ ((↑) ∘ denseSeq s) : α) in s by apply this
  rintro (_ | n)
  exacts [h₀, Subtype.mem _]

中文:
定理 approxOn_mem
  结论: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  证明: by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  suffices forall n, (Nat.casesOn n y₀ ((↑) ∘ denseSeq s) : α) in s by apply this
  rintro (_ | n)
  exacts [h₀, Subtype.mem _]

Depends on / 依赖: Nat.casesOn, Nonempty, Subtype, Subtype.mem, casesOn, denseSeq, exacts
-/
theorem approxOn_mem {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
    [SeparableSpace s] (n : Nat) (x : β) : approxOn f hf s y₀ h₀ n x in s := by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  suffices forall n, (Nat.casesOn n y₀ ((↑) ∘ denseSeq s) : α) in s by apply this
  rintro (_ | n)
  exacts [h₀, Subtype.mem _]

/--
lemma `approxOn_range_nonneg` / 引理 `approxOn_range_nonneg`

English:
lemma approxOn_range_nonneg
  statement: [Zero α] [Preorder α] {f : β -> α}
  proof: by
  have : range f union {0} subseteq Set.Ici 0 := by
    simp only [Set.union_singleton, Set.insert_subset_iff, Set.mem_Ici, le_refl, true_and]
    rintro - ⟨x, rfl⟩
    exact hf x
exact fun _ => this approxOn_mem ..

@[simp]

中文:
引理 approxOn_range_nonneg
  结论: [Zero α] [Preorder α] {f : β -> α}
  证明: by
  have : range f union {0} subseteq Set.Ici 0 := by
    simp only [Set.union_singleton, Set.insert_subset_iff, Set.mem_Ici, le_refl, true_and]
    rintro - ⟨x, rfl⟩
    exact hf x
exact fun _ => this approxOn_mem ..

@[simp]

Depends on / 依赖: Set.Ici, Set.insert_subset_iff, Set.mem_Ici, Set.union_singleton, approxOn_mem, insert_subset_iff, le_refl, mem_Ici, subseteq, true_and, union_singleton
-/
lemma approxOn_range_nonneg [Zero α] [Preorder α] {f : β -> α}
    (hf : 0 <= f) {hfm : Measurable f} [SeparableSpace (range f union {0} : Set α)] (n : Nat) :
    0 <= approxOn f hfm (range f union {0}) 0 (by simp) n := by
  have : range f union {0} subseteq Set.Ici 0 := by
    simp only [Set.union_singleton, Set.insert_subset_iff, Set.mem_Ici, le_refl, true_and]
    rintro - ⟨x, rfl⟩
    exact hf x
exact fun _ => this approxOn_mem ..

@[simp]
/--
theorem `approxOn_comp` / 定理 `approxOn_comp`

English:
theorem approxOn_comp
  statement: {γ : Type*} [MeasurableSpace γ] {f : β -> α} (hf : Measurable f) {g : γ -> β}
  proof: rfl

中文:
定理 approxOn_comp
  结论: {γ : 类型} [MeasurableSpace γ] {f : β -> α} (hf : Measurable f) {g : γ -> β}
  证明: rfl
-/
theorem approxOn_comp {γ : Type*} [MeasurableSpace γ] {f : β -> α} (hf : Measurable f) {g : γ -> β}
    (hg : Measurable g) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace s] (n : Nat) :
    approxOn (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approxOn f hf s y₀ h₀ n).comp g hg :=
  rfl

/--
theorem `tendsto_approxOn` / 定理 `tendsto_approxOn`

English:
theorem tendsto_approxOn
  statement: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  proof: by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  rw [← @Subtype.range_coe _ s]; rw [← image_univ]; rw [← (denseRange_denseSeq s).closure_eq] at hx
  simp -iota only [approxOn, coe_comp]
  refine tendsto_nearestPt (closure_minimal ?_ isClosed_closure hx)
  simp -iota only [Nat.range_casesOn, closure_union, ran

中文:
定理 tendsto_approxOn
  结论: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  证明: by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  rw [← @Subtype.range_coe _ s]; rw [← image_univ]; rw [← (denseRange_denseSeq s).closure_eq] at hx
  simp -iota only [approxOn, coe_comp]
  refine tendsto_nearestPt (closure_minimal ?_ isClosed_closure hx)
  simp -iota only [Nat.range_casesOn, closure_union, ran

Depends on / 依赖: Nat.range_casesOn, Nonempty, Subset, Subset.trans, Subtype, Subtype.range_coe, approxOn, closure_eq, closure_minimal, closure_union, coe_comp, continuous_subtype_val, denseRange_denseSeq, image_closure_subset_closure_image, image_univ, isClosed_closure, range_casesOn, range_coe, range_comp, subset_union_right
-/
theorem tendsto_approxOn {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
    [SeparableSpace s] {x : β} (hx : f x in closure s) :
    Tendsto (fun n => approxOn f hf s y₀ h₀ n x) atTop (𝓝 <| f x) := by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  rw [← @Subtype.range_coe _ s]; rw [← image_univ]; rw [← (denseRange_denseSeq s).closure_eq] at hx
  simp -iota only [approxOn, coe_comp]
  refine tendsto_nearestPt (closure_minimal ?_ isClosed_closure hx)
  simp -iota only [Nat.range_casesOn, closure_union, range_comp]
  exact
    Subset.trans (image_closure_subset_closure_image continuous_subtype_val)
      subset_union_right

/--
theorem `edist_approxOn_mono` / 定理 `edist_approxOn_mono`

English:
theorem edist_approxOn_mono
  statement: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  proof: by
  dsimp only [approxOn, coe_comp, Function.comp_def]
  exact edist_nearestPt_le _ _ ((nearestPtInd_le _ _ _).trans h)

中文:
定理 edist_approxOn_mono
  结论: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  证明: by
  dsimp only [approxOn, coe_comp, Function.comp_def]
  exact edist_nearestPt_le _ _ ((nearestPtInd_le _ _ _).trans h)

Depends on / 依赖: Function, Function.comp_def, approxOn, coe_comp, comp_def, edist_nearestPt_le, nearestPtInd_le
-/
theorem edist_approxOn_mono {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
    [SeparableSpace s] (x : β) {m n : Nat} (h : m <= n) :
    edist (approxOn f hf s y₀ h₀ n x) (f x) <= edist (approxOn f hf s y₀ h₀ m x) (f x) := by
  dsimp only [approxOn, coe_comp, Function.comp_def]
  exact edist_nearestPt_le _ _ ((nearestPtInd_le _ _ _).trans h)

/--
theorem `edist_approxOn_le` / 定理 `edist_approxOn_le`

English:
theorem edist_approxOn_le
  statement: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  proof: edist_approxOn_mono hf h₀ x zero_le

中文:
定理 edist_approxOn_le
  结论: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  证明: edist_approxOn_mono hf h₀ x zero_le

Depends on / 依赖: edist_approxOn_mono, zero_le
-/
theorem edist_approxOn_le {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
    [SeparableSpace s] (x : β) (n : Nat) : edist (approxOn f hf s y₀ h₀ n x) (f x) <= edist y₀ (f x) :=
  edist_approxOn_mono hf h₀ x zero_le

/--
theorem `edist_approxOn_y0_le` / 定理 `edist_approxOn_y0_le`

English:
theorem edist_approxOn_y0_le
  statement: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  proof: calc
    edist y₀ (approxOn f hf s y₀ h₀ n x) <=
        edist y₀ (f x) + edist (approxOn f hf s y₀ h₀ n x) (f x) :=
      edist_triangle_right _ _ _
    _ <= edist y₀ (f x) + edist y₀ (f x) := by grw [edist_approxOn_le hf h₀ x n]

中文:
定理 edist_approxOn_y0_le
  结论: {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
  证明: calc
    edist y₀ (approxOn f hf s y₀ h₀ n x) <=
        edist y₀ (f x) + edist (approxOn f hf s y₀ h₀ n x) (f x) :=
      edist_triangle_right _ _ _
    _ <= edist y₀ (f x) + edist y₀ (f x) := by grw [edist_approxOn_le hf h₀ x n]

Depends on / 依赖: approxOn, edist_approxOn_le, edist_triangle_right
-/
theorem edist_approxOn_y0_le {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s)
    [SeparableSpace s] (x : β) (n : Nat) :
    edist y₀ (approxOn f hf s y₀ h₀ n x) <= edist y₀ (f x) + edist y₀ (f x) :=
  calc
    edist y₀ (approxOn f hf s y₀ h₀ n x) <=
        edist y₀ (f x) + edist (approxOn f hf s y₀ h₀ n x) (f x) :=
      edist_triangle_right _ _ _
    _ <= edist y₀ (f x) + edist y₀ (f x) := by grw [edist_approxOn_le hf h₀ x n]

end SimpleFunc

end MeasureTheory

section CompactSupport

variable {X Y α : Type*} [Zero α]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]

/--
lemma `HasCompactSupport.exists_simpleFunc_approx_of_prod` / 引理 `HasCompactSupport.exists_simpleFunc_approx_of_prod`

English:
lemma HasCompactSupport.exists_simpleFunc_approx_of_prod
  statement: [PseudoMetricSpace α]
  proof: by
  have M : forall (K : Set (X × Y)), IsCompact K ->
      exists (g : SimpleFunc (X × Y) α), exists (s : Set (X × Y)), MeasurableSet s ∧ K subseteq s ∧
      forall x in s, dist (f x) (g x) < ε := by
    intro K hK
    apply IsCompact.induction_on
      (p := fun t => exists (g : SimpleFunc (X × 

中文:
引理 HasCompactSupport.exists_simpleFunc_approx_of_prod
  结论: [PseudoMetricSpace α]
  证明: by
  have M : forall (K : Set (X × Y)), IsCompact K ->
      exists (g : SimpleFunc (X × Y) α), exists (s : Set (X × Y)), MeasurableSet s ∧ K subseteq s ∧
      forall x in s, dist (f x) (g x) < ε := by
    intro K hK
    apply IsCompact.induction_on
      (p := fun t => exists (g : SimpleFunc (X × 

Depends on / 依赖: IsCompact, IsCompact.induction_on, MeasurableSet, SimpleFunc, induction_on, s_meas, subseteq
-/
lemma HasCompactSupport.exists_simpleFunc_approx_of_prod [PseudoMetricSpace α]
    {f : X × Y -> α} (hf : Continuous f) (h'f : HasCompactSupport f)
    {ε : Real} (hε : 0 < ε) :
    exists (g : SimpleFunc (X × Y) α), forall x, dist (f x) (g x) < ε := by
  have M : forall (K : Set (X × Y)), IsCompact K ->
      exists (g : SimpleFunc (X × Y) α), exists (s : Set (X × Y)), MeasurableSet s ∧ K subseteq s ∧
      forall x in s, dist (f x) (g x) < ε := by
    intro K hK
    apply IsCompact.induction_on
      (p := fun t => exists (g : SimpleFunc (X × Y) α), exists (s : Set (X × Y)), MeasurableSet s ∧ t subseteq s ∧
        forall x in s, dist (f x) (g x) < ε) hK
    · exact ⟨0, ∅, by simp⟩
    · intro t t' htt' ⟨g, s, s_meas, ts, hg⟩
      exact ⟨g, s, s_meas, htt'.trans ts, hg⟩
    · intro t t' ⟨g, s, s_meas, ts, hg⟩ ⟨g', s', s'_meas, t's', hg'⟩
      refine ⟨g.piecewise s s_meas g', s union s', s_meas.union s'_meas,
        union_subset_union ts t's', fun p hp => ?_⟩
      by_cases H : p in s
      · simpa [H, SimpleFunc.piecewise_apply] using hg p H
      · simp only [SimpleFunc.piecewise_apply, H, ite_false]
        apply hg'
        simpa [H] using (mem_union _ _ _).1 hp
    · rintro ⟨x, y⟩ -
      obtain ⟨u, v, hu, xu, hv, yv, huv⟩ : exists u v, IsOpen u ∧ x in u ∧ IsOpen v ∧ y in v ∧
        u ×ˢ v subseteq {z | dist (f z) (f (x, y)) < ε} :=
mem_nhds_prod_iff'.1 Metric.continuousAt_iff'.1 hf.continuousAt ε hε
refine ⟨u ×ˢ v, nhdsWithin_le_nhds (hu.prod hv).mem_nhds (mk_mem_prod xu yv), ?_⟩
      exact ⟨SimpleFunc.const _ (f (x, y)), u ×ˢ v, hu.measurableSet.prod hv.measurableSet,
        Subset.rfl, fun z hz => huv hz⟩
  obtain ⟨g, s, s_meas, fs, hg⟩ : exists (g : SimpleFunc (X × Y) α) (s : Set (X × Y)),
    MeasurableSet s ∧ tsupport f subseteq s ∧ forall (x : X × Y), x in s -> dist (f x) (g x) < ε := M _ h'f
  refine ⟨g.piecewise s s_meas 0, fun p => ?_⟩
  by_cases H : p in s
  · simpa [H, SimpleFunc.piecewise_apply] using hg p H
  · have : f p = 0 := by
      contrapose! H
      rw [← Function.mem_support] at H
      exact fs (subset_tsupport _ H)
    simp [SimpleFunc.piecewise_apply, H, this, hε]

/--
lemma `HasCompactSupport.measurable_of_prod` / 引理 `HasCompactSupport.measurable_of_prod`

English:
lemma HasCompactSupport.measurable_of_prod
  proof: by
  let : PseudoMetricSpace α := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
  obtain ⟨u, -, u_pos, u_lim⟩ : exists u, StrictAnti u ∧ (forall (n : Nat), 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  have : forall n, exists (g : SimpleFunc (X × Y) α), fo

中文:
引理 HasCompactSupport.measurable_of_prod
  证明: by
  let : PseudoMetricSpace α := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
  obtain ⟨u, -, u_pos, u_lim⟩ : exists u, StrictAnti u ∧ (forall (n : Nat), 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  have : forall n, exists (g : SimpleFunc (X × Y) α), fo

Depends on / 依赖: PseudoMetricSpace, SimpleFunc, StrictAnti, Tendsto, TopologicalSpace, TopologicalSpace.pseudoMetrizableSpacePseudoMetric, exists_seq_strictAnti_tendsto, exists_simpleFunc_approx_of_prod, f.exists_simpleFunc_approx_of_prod, pseudoMetrizableSpacePseudoMetric, tendsto_iff_dist, u_lim, u_pos
-/
lemma HasCompactSupport.measurable_of_prod
    [TopologicalSpace α] [PseudoMetrizableSpace α] [MeasurableSpace α] [BorelSpace α]
    {f : X × Y -> α} (hf : Continuous f) (h'f : HasCompactSupport f) :
    Measurable f := by
  let : PseudoMetricSpace α := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
  obtain ⟨u, -, u_pos, u_lim⟩ : exists u, StrictAnti u ∧ (forall (n : Nat), 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  have : forall n, exists (g : SimpleFunc (X × Y) α), forall x, dist (f x) (g x) < u n :=
    fun n => h'f.exists_simpleFunc_approx_of_prod hf (u_pos n)
  choose g hg using this
  have A : forall x, Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) u_lim
    rw [dist_comm]
    exact (hg n x).le
  apply measurable_of_tendsto_metrizable (fun n => (g n).measurable) (tendsto_pi_nhds.2 A)

end CompactSupport
