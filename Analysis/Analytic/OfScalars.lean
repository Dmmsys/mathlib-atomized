/-
Copyright (c) 2024 Edward Watine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward Watine
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius

/-!
# Scalar series

This file contains API for analytic functions `∑ cᵢ • xⁱ` defined in terms of scalars
`c₀, c₁, c₂, …`.

## Main definitions / results:
* `FormalMultilinearSeries.ofScalars`: the formal power series `∑ cᵢ • xⁱ`.
* `FormalMultilinearSeries.ofScalarsSum`: the sum of such a power series, if it exists, and zero
  otherwise.
* `FormalMultilinearSeries.ofScalars_radius_eq_(zero/inv/top)_of_tendsto`:
  the ratio test for an analytic function defined in terms of a formal power series `∑ cᵢ • xⁱ`.
* `FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto_ENNReal`:
  the ratio test for an analytic function using `ENNReal` division for all values `ℝ≥0∞`.
-/

@[expose] public section

namespace FormalMultilinearSeries

section Field

open ContinuousMultilinearMap

variable {𝕜 : Type*} (E : Type*) [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E]
  [IsTopologicalRing E] {c : Nat -> 𝕜}

/--
Definition of `ofScalars` / `ofScalars` 的定义

English:
definition ofScalars
  signature: (c : Nat -> 𝕜)
  body: fun n => c n • ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E

@[simp]

中文:
定义 ofScalars
  签名: (c : 自然数 -> 𝕜)
  定义体: fun n => c n • ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebraFin, mkPiAlgebraFin
-/
def ofScalars (c : Nat -> 𝕜) : FormalMultilinearSeries 𝕜 E E :=
  fun n => c n • ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E

@[simp]
/--
theorem `ofScalars_eq_zero` / 定理 `ofScalars_eq_zero`

English:
theorem ofScalars_eq_zero
  given: [Nontrivial E] (n : Nat)
  statement: ofScalars E c n = 0 ↔ c n = 0
  proof: by
  rw [ofScalars]; rw [smul_eq_zero]
  refine or_iff_left (ContinuousMultilinearMap.ext_iff.1.mt <| not_forall_of_exists_not ?_)
  use fun _ => 1
  simp

@[simp]

中文:
定理 ofScalars_eq_zero
  条件: [非平凡 E] (n : 自然数)
  结论: ofScalars E c n = 0 ↔ c n = 0
  证明: by
  rw [ofScalars]; rw [smul_eq_zero]
  refine or_iff_left (ContinuousMultilinearMap.ext_iff.1.mt <| not_forall_of_exists_not ?_)
  use fun _ => 1
  simp

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.ext_iff, ext_iff, not_forall_of_exists_not, ofScalars, or_iff_left, smul_eq_zero
-/
theorem ofScalars_eq_zero [Nontrivial E] (n : Nat) : ofScalars E c n = 0 ↔ c n = 0 := by
  rw [ofScalars]; rw [smul_eq_zero]
  refine or_iff_left (ContinuousMultilinearMap.ext_iff.1.mt <| not_forall_of_exists_not ?_)
  use fun _ => 1
  simp

@[simp]
/--
theorem `ofScalars_eq_zero_of_scalar_zero` / 定理 `ofScalars_eq_zero_of_scalar_zero`

English:
theorem ofScalars_eq_zero_of_scalar_zero
  given: {n : Nat} (hc : c n = 0)
  statement: ofScalars E c n = 0
  proof: by
  rw [ofScalars]; rw [hc]; rw [zero_smul 𝕜 (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]

@[simp]

中文:
定理 ofScalars_eq_zero_of_scalar_zero
  条件: {n : 自然数} (hc : c n = 0)
  结论: ofScalars E c n = 0
  证明: by
  rw [ofScalars]; rw [hc]; rw [zero_smul 𝕜 (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebraFin, mkPiAlgebraFin, ofScalars, zero_smul
-/
theorem ofScalars_eq_zero_of_scalar_zero {n : Nat} (hc : c n = 0) : ofScalars E c n = 0 := by
  rw [ofScalars]; rw [hc]; rw [zero_smul 𝕜 (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]

@[simp]
/--
theorem `ofScalars_series_eq_zero` / 定理 `ofScalars_series_eq_zero`

English:
theorem ofScalars_series_eq_zero
  given: [Nontrivial E]
  statement: ofScalars E c = 0 ↔ c = 0
  proof: by
  simp [FormalMultilinearSeries.ext_iff, funext_iff]

中文:
定理 ofScalars_series_eq_zero
  条件: [非平凡 E]
  结论: ofScalars E c = 0 ↔ c = 0
  证明: by
  simp [FormalMultilinearSeries.ext_iff, funext_iff]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ext_iff, ext_iff, funext_iff
-/
theorem ofScalars_series_eq_zero [Nontrivial E] : ofScalars E c = 0 ↔ c = 0 := by
  simp [FormalMultilinearSeries.ext_iff, funext_iff]

variable (𝕜) in
@[simp]
/--
theorem `ofScalars_series_eq_zero_of_scalar_zero` / 定理 `ofScalars_series_eq_zero_of_scalar_zero`

English:
theorem ofScalars_series_eq_zero_of_scalar_zero
  statement: ofScalars E (0 : Nat -> 𝕜) = 0
  proof: by
  simp [FormalMultilinearSeries.ext_iff]

@[simp]

中文:
定理 ofScalars_series_eq_zero_of_scalar_zero
  结论: ofScalars E (0 : 自然数 -> 𝕜) = 0
  证明: by
  simp [FormalMultilinearSeries.ext_iff]

@[simp]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ext_iff, ext_iff
-/
theorem ofScalars_series_eq_zero_of_scalar_zero : ofScalars E (0 : Nat -> 𝕜) = 0 := by
  simp [FormalMultilinearSeries.ext_iff]

@[simp]
/--
theorem `ofScalars_series_of_subsingleton` / 定理 `ofScalars_series_of_subsingleton`

English:
theorem ofScalars_series_of_subsingleton
  given: [Subsingleton E]
  statement: ofScalars E c = 0
  proof: by
  simp_rw [FormalMultilinearSeries.ext_iff, ofScalars, ContinuousMultilinearMap.ext_iff]
  exact fun _ _ => Subsingleton.allEq _ _

中文:
定理 ofScalars_series_of_subsingleton
  条件: [子单例 E]
  结论: ofScalars E c = 0
  证明: by
  simp_rw [FormalMultilinearSeries.ext_iff, ofScalars, ContinuousMultilinearMap.ext_iff]
  exact fun _ _ => Subsingleton.allEq _ _

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.ext_iff, FormalMultilinearSeries, FormalMultilinearSeries.ext_iff, Subsingleton, Subsingleton.allEq, ext_iff, ofScalars, simp_rw
-/
theorem ofScalars_series_of_subsingleton [Subsingleton E] : ofScalars E c = 0 := by
  simp_rw [FormalMultilinearSeries.ext_iff, ofScalars, ContinuousMultilinearMap.ext_iff]
  exact fun _ _ => Subsingleton.allEq _ _

variable (𝕜) in
/--
theorem `ofScalars_series_injective` / 定理 `ofScalars_series_injective`

English:
theorem ofScalars_series_injective
  given: [Nontrivial E]
  statement: Function.Injective (ofScalars E (𝕜 := 𝕜))
  proof: by
  intro _ _ h
  ext n
  simpa [ofScalars] using congrArg (fun p => p n fun _ => (1 : E)) h

中文:
定理 ofScalars_series_injective
  条件: [非平凡 E]
  结论: 函数.单射 (ofScalars E (𝕜 := 𝕜))
  证明: by
  intro _ _ h
  ext n
  simpa [ofScalars] using congrArg (fun p => p n fun _ => (1 : E)) h

Depends on / 依赖: ofScalars
-/
theorem ofScalars_series_injective [Nontrivial E] : Function.Injective (ofScalars E (𝕜 := 𝕜)) := by
  intro _ _ h
  ext n
  simpa [ofScalars] using congrArg (fun p => p n fun _ => (1 : E)) h

variable (c)

@[simp]
/--
theorem `ofScalars_series_eq_iff` / 定理 `ofScalars_series_eq_iff`

English:
theorem ofScalars_series_eq_iff
  given: [Nontrivial E] (c' : Nat -> 𝕜)
  proof: ⟨fun e => ofScalars_series_injective 𝕜 E e, _root_.congrArg _⟩

中文:
定理 ofScalars_series_eq_iff
  条件: [非平凡 E] (c' : 自然数 -> 𝕜)
  证明: ⟨fun e => ofScalars_series_injective 𝕜 E e, _root_.congrArg _⟩

Depends on / 依赖: _root_, _root_.congrArg, ofScalars_series_injective
-/
theorem ofScalars_series_eq_iff [Nontrivial E] (c' : Nat -> 𝕜) :
    ofScalars E c = ofScalars E c' ↔ c = c' :=
  ⟨fun e => ofScalars_series_injective 𝕜 E e, _root_.congrArg _⟩

/--
theorem `ofScalars_apply_zero` / 定理 `ofScalars_apply_zero`

English:
theorem ofScalars_apply_zero
  given: (n : Nat)
  proof: by
  rw [ofScalars]
  cases n <;> simp

@[simp]

中文:
定理 ofScalars_apply_zero
  条件: (n : 自然数)
  证明: by
  rw [ofScalars]
  cases n <;> simp

@[simp]

Depends on / 依赖: ofScalars
-/
theorem ofScalars_apply_zero (n : Nat) :
    ofScalars E c n (fun _ => 0) = Pi.single (M := fun _ => E) 0 (c 0 • 1) n := by
  rw [ofScalars]
  cases n <;> simp

@[simp]
/--
lemma `coeff_ofScalars` / 引理 `coeff_ofScalars`

English:
lemma coeff_ofScalars
  given: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat}
  proof: by
  simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]

中文:
引理 coeff_ofScalars
  条件: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {p : 自然数 -> 𝕜} {n : 自然数}
  证明: by
  simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn, ofScalars, prod_ofFn
-/
lemma coeff_ofScalars {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} :
    (FormalMultilinearSeries.ofScalars 𝕜 p).coeff n = p n := by
  simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]

/--
theorem `ofScalars_add` / 定理 `ofScalars_add`

English:
theorem ofScalars_add
  given: (c' : Nat -> 𝕜)
  statement: ofScalars E (c + c') = ofScalars E c + ofScalars E c'
  proof: by
  ext; simp [ofScalars, add_smul]

中文:
定理 ofScalars_add
  条件: (c' : 自然数 -> 𝕜)
  结论: ofScalars E (c + c') = ofScalars E c + ofScalars E c'
  证明: by
  ext; simp [ofScalars, add_smul]

Depends on / 依赖: add_smul, ofScalars
-/
theorem ofScalars_add (c' : Nat -> 𝕜) : ofScalars E (c + c') = ofScalars E c + ofScalars E c' := by
  ext; simp [ofScalars, add_smul]

/--
lemma `ofScalars_sub` / 引理 `ofScalars_sub`

English:
lemma ofScalars_sub
  given: (c' : Nat -> 𝕜)
  statement: ofScalars E (c - c') = ofScalars E c - ofScalars E c'
  proof: by
  ext; simp [ofScalars, sub_smul]

中文:
引理 ofScalars_sub
  条件: (c' : 自然数 -> 𝕜)
  结论: ofScalars E (c - c') = ofScalars E c - ofScalars E c'
  证明: by
  ext; simp [ofScalars, sub_smul]

Depends on / 依赖: ofScalars, sub_smul
-/
lemma ofScalars_sub (c' : Nat -> 𝕜) : ofScalars E (c - c') = ofScalars E c - ofScalars E c' := by
  ext; simp [ofScalars, sub_smul]

/--
theorem `ofScalars_smul` / 定理 `ofScalars_smul`

English:
theorem ofScalars_smul
  given: (x : 𝕜)
  statement: ofScalars E (x • c) = x • ofScalars E c
  proof: by
  ext; simp [ofScalars, smul_smul]

中文:
定理 ofScalars_smul
  条件: (x : 𝕜)
  结论: ofScalars E (x • c) = x • ofScalars E c
  证明: by
  ext; simp [ofScalars, smul_smul]

Depends on / 依赖: ofScalars, smul_smul
-/
theorem ofScalars_smul (x : 𝕜) : ofScalars E (x • c) = x • ofScalars E c := by
  ext; simp [ofScalars, smul_smul]

/--
theorem `ofScalars_comp_neg_id` / 定理 `ofScalars_comp_neg_id`

English:
theorem ofScalars_comp_neg_id
  proof: by
  ext n
  rcases n.even_or_odd with (h | h) <;>
  simp [ofScalars, show ((-ContinuousLinearMap.id 𝕜 E : _) : E -> E) = Neg.neg by rfl,
    ← List.map_ofFn, h.neg_one_pow]

中文:
定理 ofScalars_comp_neg_id
  证明: by
  ext n
  rcases n.even_or_odd with (h | h) <;>
  simp [ofScalars, show ((-ContinuousLinearMap.id 𝕜 E : _) : E -> E) = Neg.neg by rfl,
    ← List.map_ofFn, h.neg_one_pow]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, List.map_ofFn, Neg.neg, even_or_odd, h.neg_one_pow, map_ofFn, n.even_or_odd, neg_one_pow, ofScalars
-/
theorem ofScalars_comp_neg_id :
    (ofScalars E c).compContinuousLinearMap (-ContinuousLinearMap.id _ _) =
    (ofScalars E (fun k => (-1) ^ k * c k)) := by
  ext n
  rcases n.even_or_odd with (h | h) <;>
  simp [ofScalars, show ((-ContinuousLinearMap.id 𝕜 E : _) : E -> E) = Neg.neg by rfl,
    ← List.map_ofFn, h.neg_one_pow]

/--
theorem `ofScalars_comp_neg` / 定理 `ofScalars_comp_neg`

English:
theorem ofScalars_comp_neg
  given: (f : E ->L[𝕜] E)
  proof: by
  conv => lhs; rw [← ContinuousLinearMap.id_comp f, ← ContinuousLinearMap.neg_comp]
  rw [← FormalMultilinearSeries.compContinuousLinearMap_comp]; rw [ofScalars_comp_neg_id]

中文:
定理 ofScalars_comp_neg
  条件: (f : E ->L[𝕜] E)
  证明: by
  conv => lhs; rw [← ContinuousLinearMap.id_comp f, ← ContinuousLinearMap.neg_comp]
  rw [← FormalMultilinearSeries.compContinuousLinearMap_comp]; rw [ofScalars_comp_neg_id]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id_comp, ContinuousLinearMap.neg_comp, FormalMultilinearSeries, FormalMultilinearSeries.compContinuousLinearMap_comp, compContinuousLinearMap_comp, id_comp, neg_comp, ofScalars_comp_neg_id
-/
theorem ofScalars_comp_neg (f : E ->L[𝕜] E) :
    (ofScalars E c).compContinuousLinearMap (-f) =
    (ofScalars E (fun k => (-1) ^ k * c k)).compContinuousLinearMap f := by
  conv => lhs; rw [← ContinuousLinearMap.id_comp f, ← ContinuousLinearMap.neg_comp]
  rw [← FormalMultilinearSeries.compContinuousLinearMap_comp]; rw [ofScalars_comp_neg_id]

variable (𝕜) in
/--
Definition of `ofScalarsSubmodule` / `ofScalarsSubmodule` 的定义

English:
definition ofScalarsSubmodule
  signature: : Submodule 𝕜 (FormalMultilinearSeries 𝕜 E E) where
  body: {ofScalars E f | f}
  add_mem' := fun ⟨c, hc⟩ ⟨c', hc'⟩ => ⟨c + c', hc' ▸ hc ▸ ofScalars_add E c c'⟩
  zero_mem' := ⟨0, ofScalars_series_eq_zero_of_scalar_zero 𝕜 E⟩
  smul_mem' := fun x _ ⟨c, hc⟩ => ⟨x • c, hc ▸ ofScalars_smul E c x⟩

中文:
定义 ofScalarsSubmodule
  签名: : 子模 𝕜 (FormalMultilinearSeries 𝕜 E E) where
  定义体: {ofScalars E f | f}
  add_mem' := fun ⟨c, hc⟩ ⟨c', hc'⟩ => ⟨c + c', hc' ▸ hc ▸ ofScalars_add E c c'⟩
  zero_mem' := ⟨0, ofScalars_series_eq_zero_of_scalar_zero 𝕜 E⟩
  smul_mem' := fun x _ ⟨c, hc⟩ => ⟨x • c, hc ▸ ofScalars_smul E c x⟩

Depends on / 依赖: ofScalars
-/
def ofScalarsSubmodule : Submodule 𝕜 (FormalMultilinearSeries 𝕜 E E) where
  carrier := {ofScalars E f | f}
  add_mem' := fun ⟨c, hc⟩ ⟨c', hc'⟩ => ⟨c + c', hc' ▸ hc ▸ ofScalars_add E c c'⟩
  zero_mem' := ⟨0, ofScalars_series_eq_zero_of_scalar_zero 𝕜 E⟩
  smul_mem' := fun x _ ⟨c, hc⟩ => ⟨x • c, hc ▸ ofScalars_smul E c x⟩

variable {E}

/--
theorem `ofScalars_apply_eq` / 定理 `ofScalars_apply_eq`

English:
theorem ofScalars_apply_eq
  given: (x : E) (n : Nat)
  proof: by
  simp [ofScalars]

中文:
定理 ofScalars_apply_eq
  条件: (x : E) (n : 自然数)
  证明: by
  simp [ofScalars]

Depends on / 依赖: ofScalars
-/
theorem ofScalars_apply_eq (x : E) (n : Nat) :
    ofScalars E c n (fun _ => x) = c n • x ^ n := by
  simp [ofScalars]

/--
theorem `ofScalars_apply_eq'` / 定理 `ofScalars_apply_eq'`

English:
theorem ofScalars_apply_eq'
  given: (x : E)
  proof: by
  simp [ofScalars]

中文:
定理 ofScalars_apply_eq'
  条件: (x : E)
  证明: by
  simp [ofScalars]

Depends on / 依赖: ofScalars
-/
theorem ofScalars_apply_eq' (x : E) :
    (fun n => ofScalars E c n (fun _ => x)) = fun n => c n • x ^ n := by
  simp [ofScalars]

/--
Definition of `ofScalarsSum` / `ofScalarsSum` 的定义

English:
definition ofScalarsSum
  body: (ofScalars E c).sum

中文:
定义 ofScalarsSum
  定义体: (ofScalars E c).sum

Depends on / 依赖: ofScalars
-/
noncomputable def ofScalarsSum := (ofScalars E c).sum

/--
theorem `ofScalars_sum_eq` / 定理 `ofScalars_sum_eq`

English:
theorem ofScalars_sum_eq
  given: (x : E)
  statement: ofScalarsSum c x =
  proof: tsum_congr fun n => ofScalars_apply_eq c x n

中文:
定理 ofScalars_sum_eq
  条件: (x : E)
  结论: ofScalarsSum c x =
  证明: tsum_congr fun n => ofScalars_apply_eq c x n

Depends on / 依赖: ofScalars_apply_eq, tsum_congr
-/
theorem ofScalars_sum_eq (x : E) : ofScalarsSum c x =
    ∑' n, c n • x ^ n := tsum_congr fun n => ofScalars_apply_eq c x n

/--
theorem `ofScalarsSum_eq_tsum` / 定理 `ofScalarsSum_eq_tsum`

English:
theorem ofScalarsSum_eq_tsum
  statement: ofScalarsSum c =
  proof: funext (ofScalars_sum_eq c)

@[simp]

中文:
定理 ofScalarsSum_eq_tsum
  结论: ofScalarsSum c =
  证明: funext (ofScalars_sum_eq c)

@[simp]

Depends on / 依赖: ofScalars_sum_eq
-/
theorem ofScalarsSum_eq_tsum : ofScalarsSum c =
    fun (x : E) => ∑' n : Nat, c n • x ^ n := funext (ofScalars_sum_eq c)

@[simp]
/--
theorem `ofScalarsSum_zero` / 定理 `ofScalarsSum_zero`

English:
theorem ofScalarsSum_zero
  statement: ofScalarsSum c (0 : E) = c 0 • 1
  proof: by
  simp [ofScalarsSum_eq_tsum, ← ofScalars_apply_eq, ofScalars_apply_zero]

@[simp]

中文:
定理 ofScalarsSum_zero
  结论: ofScalarsSum c (0 : E) = c 0 • 1
  证明: by
  simp [ofScalarsSum_eq_tsum, ← ofScalars_apply_eq, ofScalars_apply_zero]

@[simp]

Depends on / 依赖: ofScalarsSum_eq_tsum, ofScalars_apply_eq, ofScalars_apply_zero
-/
theorem ofScalarsSum_zero : ofScalarsSum c (0 : E) = c 0 • 1 := by
  simp [ofScalarsSum_eq_tsum, ← ofScalars_apply_eq, ofScalars_apply_zero]

@[simp]
/--
theorem `ofScalarsSum_of_subsingleton` / 定理 `ofScalarsSum_of_subsingleton`

English:
theorem ofScalarsSum_of_subsingleton
  given: [Subsingleton E] {x : E}
  statement: ofScalarsSum c x = 0
  proof: by
  simp [Subsingleton.eq_zero (α := E)]

@[simp]

中文:
定理 ofScalarsSum_of_subsingleton
  条件: [子单例 E] {x : E}
  结论: ofScalarsSum c x = 0
  证明: by
  simp [Subsingleton.eq_zero (α := E)]

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero
-/
theorem ofScalarsSum_of_subsingleton [Subsingleton E] {x : E} : ofScalarsSum c x = 0 := by
  simp [Subsingleton.eq_zero (α := E)]

@[simp]
/--
theorem `ofScalarsSum_op` / 定理 `ofScalarsSum_op`

English:
theorem ofScalarsSum_op
  given: [T2Space E] (x : E)
  proof: by
  simp [ofScalars_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]

中文:
定理 ofScalarsSum_op
  条件: [T2空间 E] (x : E)
  证明: by
  simp [ofScalars_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.op_pow, MulOpposite.op_smul, ofScalars_sum_eq, op_pow, op_smul, tsum_op
-/
theorem ofScalarsSum_op [T2Space E] (x : E) :
    ofScalarsSum c (MulOpposite.op x) = MulOpposite.op (ofScalarsSum c x) := by
  simp [ofScalars_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]
/--
theorem `ofScalarsSum_unop` / 定理 `ofScalarsSum_unop`

English:
theorem ofScalarsSum_unop
  given: [T2Space E] (x : Eᵐᵒᵖ)
  proof: by
  simp [ofScalars_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]

中文:
定理 ofScalarsSum_unop
  条件: [T2空间 E] (x : Eᵐᵒᵖ)
  证明: by
  simp [ofScalars_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]

Depends on / 依赖: MulOpposite, MulOpposite.unop_pow, MulOpposite.unop_smul, ofScalars_sum_eq, tsum_unop, unop_pow, unop_smul
-/
theorem ofScalarsSum_unop [T2Space E] (x : Eᵐᵒᵖ) :
    ofScalarsSum c (MulOpposite.unop x) = MulOpposite.unop (ofScalarsSum c x) := by
  simp [ofScalars_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]

end Field

section Seminormed

open Filter ENNReal
open scoped Topology NNReal

variable {𝕜 : Type*} (E : Type*) [NontriviallyNormedField 𝕜] [SeminormedRing E]
    [NormedAlgebra 𝕜 E] (c : Nat -> 𝕜) (n : Nat)

@[simp]
/--
theorem `ofScalars_norm_eq_mul` / 定理 `ofScalars_norm_eq_mul`

English:
theorem ofScalars_norm_eq_mul
  proof: by
  rw [ofScalars]; rw [norm_smul]

中文:
定理 ofScalars_norm_eq_mul
  证明: by
  rw [ofScalars]; rw [norm_smul]

Depends on / 依赖: norm_smul, ofScalars
-/
theorem ofScalars_norm_eq_mul :
    ‖ofScalars E c n‖ = ‖c n‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E‖ := by
  rw [ofScalars]; rw [norm_smul]

/--
theorem `ofScalars_norm_le` / 定理 `ofScalars_norm_le`

English:
theorem ofScalars_norm_le
  given: (hn : n > 0)
  statement: ‖ofScalars E c n‖ <= ‖c n‖
  proof: by
  simp only [ofScalars_norm_eq_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos hn))

中文:
定理 ofScalars_norm_le
  条件: (hn : n > 0)
  结论: ‖ofScalars E c n‖ <= ‖c n‖
  证明: by
  simp only [ofScalars_norm_eq_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos hn))

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos, mul_le_of_le_one_right, norm_mkPiAlgebraFin_le_of_pos, norm_nonneg, ofScalars_norm_eq_mul
-/
theorem ofScalars_norm_le (hn : n > 0) : ‖ofScalars E c n‖ <= ‖c n‖ := by
  simp only [ofScalars_norm_eq_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos hn))

/--
theorem `ofScalars_norm` / 定理 `ofScalars_norm`

English:
theorem ofScalars_norm
  given: [NormOneClass E]
  statement: ‖ofScalars E c n‖ = ‖c n‖
  proof: by
  simp

中文:
定理 ofScalars_norm
  条件: [NormOne类 E]
  结论: ‖ofScalars E c n‖ = ‖c n‖
  证明: by
  simp
-/
theorem ofScalars_norm [NormOneClass E] : ‖ofScalars E c n‖ = ‖c n‖ := by
  simp

end Seminormed

section Normed

open Filter ENNReal
open scoped Topology NNReal

variable {𝕜 : Type*} (E : Type*) [NontriviallyNormedField 𝕜] [NormedRing E]
    [NormedAlgebra 𝕜 E] (c : Nat -> 𝕜) (n : Nat)

/--
theorem `tendsto_succ_norm_div_norm` / 定理 `tendsto_succ_norm_div_norm`

English:
theorem tendsto_succ_norm_div_norm
  statement: {r r' : Real>=0} (hr' : r' != 0)
  proof: by
  simp_rw [norm_mul, norm_norm, mul_div_mul_comm, ← norm_div, pow_succ, mul_div_right_comm,
    div_self (pow_ne_zero _ (NNReal.coe_ne_zero.mpr hr')), one_mul, norm_div, NNReal.norm_eq]
  exact mul_comm r' r ▸ hc.mul tendsto_const_nhds

中文:
定理 tendsto_succ_norm_div_norm
  结论: {r r' : 实数>=0} (hr' : r' != 0)
  证明: by
  simp_rw [norm_mul, norm_norm, mul_div_mul_comm, ← norm_div, pow_succ, mul_div_right_comm,
    div_self (pow_ne_zero _ (NNReal.coe_ne_zero.mpr hr')), one_mul, norm_div, NNReal.norm_eq]
  exact mul_comm r' r ▸ hc.mul tendsto_const_nhds
-/
private theorem tendsto_succ_norm_div_norm {r r' : Real>=0} (hr' : r' != 0)
    (hc : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      Tendsto (fun n => ‖‖c (n + 1)‖ * r' ^ (n + 1)‖ /
        ‖‖c n‖ * r' ^ n‖) atTop (𝓝 ↑(r' * r)) := by
  simp_rw [norm_mul, norm_norm, mul_div_mul_comm, ← norm_div, pow_succ, mul_div_right_comm,
    div_self (pow_ne_zero _ (NNReal.coe_ne_zero.mpr hr')), one_mul, norm_div, NNReal.norm_eq]
  exact mul_comm r' r ▸ hc.mul tendsto_const_nhds

/--
theorem `inv_le_ofScalars_radius_of_tendsto` / 定理 `inv_le_ofScalars_radius_of_tendsto`

English:
theorem inv_le_ofScalars_radius_of_tendsto
  statement: {r : Real>=0} (hr : r != 0)
  proof: by
  refine le_of_forall_nnreal_lt (fun r' hr' => ?_)
  rw [coe_lt_coe]; rw [NNReal.lt_inv_iff_mul_lt hr] at hr'
  by_cases hrz : r' = 0
  · simp [hrz]
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_norm_bounded_eventually (g := fun n => ‖‖c n‖ * r' ^ n‖) ?_ ?_
  · r

中文:
定理 inv_le_ofScalars_radius_of_tendsto
  结论: {r : 实数>=0} (hr : r != 0)
  证明: by
  refine le_of_forall_nnreal_lt (fun r' hr' => ?_)
  rw [coe_lt_coe]; rw [NNReal.lt_inv_iff_mul_lt hr] at hr'
  by_cases hrz : r' = 0
  · simp [hrz]
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_norm_bounded_eventually (g := fun n => ‖‖c n‖ * r' ^ n‖) ?_ ?_
  · r

Depends on / 依赖: Eventually, Eventually.of_forall, FormalMultilinearSeries, FormalMultilinearSeries.le_radius_of_summable_norm, NNReal, NNReal.coe_ne_zero.mpr, NNReal.lt_inv_iff_mul_lt, Summable, Summable.of_norm_bounded_eventually, coe_lt_coe, coe_ne_zero, eventually_ne, hc.eventually_ne, le_of_forall_nnreal_lt, le_radius_of_summable_norm, lt_inv_iff_mul_lt, norm_norm, of_forall, of_norm_bounded_eventually, simp_rw
-/
theorem inv_le_ofScalars_radius_of_tendsto {r : Real>=0} (hr : r != 0)
    (hc : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      ofNNReal r⁻¹ <= (ofScalars E c).radius := by
  refine le_of_forall_nnreal_lt (fun r' hr' => ?_)
  rw [coe_lt_coe]; rw [NNReal.lt_inv_iff_mul_lt hr] at hr'
  by_cases hrz : r' = 0
  · simp [hrz]
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_norm_bounded_eventually (g := fun n => ‖‖c n‖ * r' ^ n‖) ?_ ?_
  · refine summable_of_ratio_test_tendsto_lt_one hr' ?_ ?_
    · refine (hc.eventually_ne (NNReal.coe_ne_zero.mpr hr)).mp (Eventually.of_forall ?_)
      simp_all
    · simp_rw [norm_norm]
      exact tendsto_succ_norm_div_norm c hrz hc
  · filter_upwards [eventually_cofinite_ne 0] with n hn
    simp only [norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
    gcongr
    exact ofScalars_norm_le E c n (Nat.pos_iff_ne_zero.mpr hn)

/--
theorem `ofScalars_radius_eq_inv_of_tendsto` / 定理 `ofScalars_radius_eq_inv_of_tendsto`

English:
theorem ofScalars_radius_eq_inv_of_tendsto
  statement: [NormOneClass E] {r : Real>=0} (hr : r != 0)
  proof: by
  refine le_antisymm ?_ (inv_le_ofScalars_radius_of_tendsto E c hr hc)
  refine le_of_forall_nnreal_lt (fun r' hr' => ?_)
  rw [coe_le_coe]; rw [NNReal.le_inv_iff_mul_le hr]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr'
  contrapose! this
  apply not_summable_of_ratio_test_tendsto

中文:
定理 ofScalars_radius_eq_inv_of_tendsto
  结论: [NormOne类 E] {r : 实数>=0} (hr : r != 0)
  证明: by
  refine le_antisymm ?_ (inv_le_ofScalars_radius_of_tendsto E c hr hc)
  refine le_of_forall_nnreal_lt (fun r' hr' => ?_)
  rw [coe_le_coe]; rw [NNReal.le_inv_iff_mul_le hr]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr'
  contrapose! this
  apply not_summable_of_ratio_test_tendsto

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.summable_norm_mul_pow, NNReal, NNReal.le_inv_iff_mul_le, coe_le_coe, contrapose, inv_le_ofScalars_radius_of_tendsto, le_antisymm, le_inv_iff_mul_le, le_of_forall_nnreal_lt, not_summable_of_ratio_test_tendsto_gt_one, ofScalars_norm, simp_rw, summable_norm_mul_pow, tendsto_succ_norm_div_norm
-/
theorem ofScalars_radius_eq_inv_of_tendsto [NormOneClass E] {r : Real>=0} (hr : r != 0)
    (hc : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = ofNNReal r⁻¹ := by
  refine le_antisymm ?_ (inv_le_ofScalars_radius_of_tendsto E c hr hc)
  refine le_of_forall_nnreal_lt (fun r' hr' => ?_)
  rw [coe_le_coe]; rw [NNReal.le_inv_iff_mul_le hr]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr'
  contrapose! this
  apply not_summable_of_ratio_test_tendsto_gt_one this
  simp_rw [ofScalars_norm]
  exact tendsto_succ_norm_div_norm c (by aesop) hc

/--
theorem `ofScalars_radius_eq_of_tendsto` / 定理 `ofScalars_radius_eq_of_tendsto`

English:
theorem ofScalars_radius_eq_of_tendsto
  statement: [NormOneClass E] {r : NNReal} (hr : r != 0)
  proof: by
  suffices Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r⁻¹) by
    convert! ofScalars_radius_eq_inv_of_tendsto E c (inv_ne_zero hr) this
    simp
  convert hc.inv₀ (NNReal.coe_ne_zero.mpr hr)
  simp

中文:
定理 ofScalars_radius_eq_of_tendsto
  结论: [NormOne类 E] {r : 非负实数} (hr : r != 0)
  证明: by
  suffices Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r⁻¹) by
    convert! ofScalars_radius_eq_inv_of_tendsto E c (inv_ne_zero hr) this
    simp
  convert hc.inv₀ (NNReal.coe_ne_zero.mpr hr)
  simp

Depends on / 依赖: NNReal, NNReal.coe_ne_zero.mpr, Tendsto, coe_ne_zero, convert, hc.inv, inv_ne_zero, n.succ, ofScalars_radius_eq_inv_of_tendsto
-/
theorem ofScalars_radius_eq_of_tendsto [NormOneClass E] {r : NNReal} (hr : r != 0)
    (hc : Tendsto (fun n => ‖c n‖ / ‖c n.succ‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = ofNNReal r := by
  suffices Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r⁻¹) by
    convert! ofScalars_radius_eq_inv_of_tendsto E c (inv_ne_zero hr) this
    simp
  convert hc.inv₀ (NNReal.coe_ne_zero.mpr hr)
  simp

/--
theorem `ofScalars_radius_eq_top_of_tendsto` / 定理 `ofScalars_radius_eq_top_of_tendsto`

English:
theorem ofScalars_radius_eq_top_of_tendsto
  statement: (hc : forallᶠ n in atTop, c n != 0)
  proof: by
  refine radius_eq_top_of_summable_norm _ fun r' => ?_
  by_cases hrz : r' = 0
  · apply Summable.comp_nat_add (k := 1)
    simp [hrz]
  · refine Summable.of_norm_bounded_eventually (g := fun n => ‖‖c n‖ * r' ^ n‖) ?_ ?_
    · apply summable_of_ratio_test_tendsto_lt_one zero_lt_one (hc.mp (Eventu

中文:
定理 ofScalars_radius_eq_top_of_tendsto
  结论: (hc : 对任意ᶠ n in atTop, c n != 0)
  证明: by
  refine radius_eq_top_of_summable_norm _ fun r' => ?_
  by_cases hrz : r' = 0
  · apply Summable.comp_nat_add (k := 1)
    simp [hrz]
  · refine Summable.of_norm_bounded_eventually (g := fun n => ‖‖c n‖ * r' ^ n‖) ?_ ?_
    · apply summable_of_ratio_test_tendsto_lt_one zero_lt_one (hc.mp (Eventu

Depends on / 依赖: Eventually, Eventually.of_forall, NNReal, NNReal.coe_zero, Summable, Summable.comp_nat_add, Summable.of_norm_bounded_eventually, coe_zero, comp_nat_add, eventually_cofinite_ne, filter_upwards, hc.mp, mul_zero, norm_mul, norm_norm, of_forall, of_norm_bounded_eventually, radius_eq_top_of_summable_norm, summable_of_ratio_test_tendsto_lt_one, tendsto_succ_norm_div_norm
-/
theorem ofScalars_radius_eq_top_of_tendsto (hc : forallᶠ n in atTop, c n != 0)
    (hc' : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0)) : (ofScalars E c).radius = ⊤ := by
  refine radius_eq_top_of_summable_norm _ fun r' => ?_
  by_cases hrz : r' = 0
  · apply Summable.comp_nat_add (k := 1)
    simp [hrz]
  · refine Summable.of_norm_bounded_eventually (g := fun n => ‖‖c n‖ * r' ^ n‖) ?_ ?_
    · apply summable_of_ratio_test_tendsto_lt_one zero_lt_one (hc.mp (Eventually.of_forall ?_))
      · simp only [norm_norm]
        exact mul_zero (_ : Real) ▸ tendsto_succ_norm_div_norm _ hrz (NNReal.coe_zero ▸ hc')
      · simp_all
    · filter_upwards [eventually_cofinite_ne 0] with n hn
      simp only [norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
      gcongr
      exact ofScalars_norm_le E c n (Nat.pos_iff_ne_zero.mpr hn)

/--
theorem `ofScalars_radius_eq_zero_of_tendsto` / 定理 `ofScalars_radius_eq_zero_of_tendsto`

English:
theorem ofScalars_radius_eq_zero_of_tendsto
  statement: [NormOneClass E]
  proof: by
  suffices (ofScalars E c).radius <= 0 by simp_all
  refine le_of_forall_nnreal_lt (fun r hr => ?_)
  rw [← coe_zero]; rw [coe_le_coe]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr
  contrapose! this
  refine not_summable_of_ratio_norm_eventually_ge (r := 2) (by simp) ?_ ?_
  · con

中文:
定理 ofScalars_radius_eq_zero_of_tendsto
  结论: [NormOne类 E]
  证明: by
  suffices (ofScalars E c).radius <= 0 by simp_all
  refine le_of_forall_nnreal_lt (fun r hr => ?_)
  rw [← coe_zero]; rw [coe_le_coe]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr
  contrapose! this
  refine not_summable_of_ratio_norm_eventually_ge (r := 2) (by simp) ?_ ?_
  · con

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.summable_norm_mul_pow, Tendsto, Tendsto.congr, coe_le_coe, coe_zero, contrapose, filter_upwards, le_of_forall_nnreal_lt, mul_eq_zero, norm_mul, norm_norm, not_summable_of_ratio_norm_eventually_ge, not_tendsto_atTop_of_tendsto_nhds, ofScalars, ofScalars_norm, radius, summable_norm_mul_pow, tendsto_const_nhds
-/
theorem ofScalars_radius_eq_zero_of_tendsto [NormOneClass E]
    (hc : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop atTop) : (ofScalars E c).radius = 0 := by
  suffices (ofScalars E c).radius <= 0 by simp_all
  refine le_of_forall_nnreal_lt (fun r hr => ?_)
  rw [← coe_zero]; rw [coe_le_coe]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr
  contrapose! this
  refine not_summable_of_ratio_norm_eventually_ge (r := 2) (by simp) ?_ ?_
  · contrapose! hc
    apply not_tendsto_atTop_of_tendsto_nhds (a := 0)
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hc] with n hc'
    rw [ofScalars_norm]; rw [norm_mul]; rw [norm_norm]; rw [mul_eq_zero] at hc'
    cases hc' <;> aesop
  · filter_upwards [hc.eventually_ge_atTop (2 * r⁻¹), eventually_ne_atTop 0] with n hc hn
    simp only [ofScalars_norm, norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
    rw [mul_comm ‖c n‖]; rw [← mul_assoc]; rw [← div_le_div_iff₀]; rw [mul_div_assoc]
    · convert! hc
      rw [pow_succ]; rw [div_mul_cancel_left₀]; rw [NNReal.coe_inv]
      aesop
    · simp_all
    · refine Ne.lt_of_le (fun hr' => Not.elim ?_ hc) (norm_nonneg _)
      rw [← hr']
      simp [this]

/--
theorem `ofScalars_radius_eq_inv_of_tendsto_ENNReal` / 定理 `ofScalars_radius_eq_inv_of_tendsto_ENNReal`

English:
theorem ofScalars_radius_eq_inv_of_tendsto_ENNReal
  statement: [NormOneClass E] {r : Real>=0∞}
  proof: by
  rcases ENNReal.trichotomy r with (hr | hr | hr)
  · simp_rw [hr, inv_zero] at hc' ⊢
    by_cases h : (forallᶠ (n : Nat) in atTop, c n != 0)
    · apply ofScalars_radius_eq_top_of_tendsto E c h ?_
refine Tendsto.congr' ?_ (tendsto_toReal zero_ne_top).comp hc'
      filter_upwards [h]
      simp


中文:
定理 ofScalars_radius_eq_inv_of_tendsto_ENN实数
  结论: [NormOne类 E] {r : 实数>=0∞}
  证明: by
  rcases ENNReal.trichotomy r with (hr | hr | hr)
  · simp_rw [hr, inv_zero] at hc' ⊢
    by_cases h : (forallᶠ (n : Nat) in atTop, c n != 0)
    · apply ofScalars_radius_eq_top_of_tendsto E c h ?_
refine Tendsto.congr' ?_ (tendsto_toReal zero_ne_top).comp hc'
      filter_upwards [h]
      simp


Depends on / 依赖: ENNReal, ENNReal.trichotomy, Tendsto, Tendsto.congr, eventually_atTop, eventually_atTop.mp, eventually_ne, filter_upwards, inv_zero, not_exists, not_forall, not_not, ofScalars, ofScalars_radius_eq_top_of_tendsto, radius_eq_top_of_eventually_eq_zero, simp_rw, tendsto_toReal, trichotomy, zero_ne_top
-/
theorem ofScalars_radius_eq_inv_of_tendsto_ENNReal [NormOneClass E] {r : Real>=0∞}
    (hc' : Tendsto (fun n => ENNReal.ofReal ‖c n.succ‖ / ENNReal.ofReal ‖c n‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = r⁻¹ := by
  rcases ENNReal.trichotomy r with (hr | hr | hr)
  · simp_rw [hr, inv_zero] at hc' ⊢
    by_cases h : (forallᶠ (n : Nat) in atTop, c n != 0)
    · apply ofScalars_radius_eq_top_of_tendsto E c h ?_
refine Tendsto.congr' ?_ (tendsto_toReal zero_ne_top).comp hc'
      filter_upwards [h]
      simp
    · apply (ofScalars E c).radius_eq_top_of_eventually_eq_zero
      simp only [eventually_atTop, not_exists, not_forall, not_not] at h ⊢
      obtain ⟨ti, hti⟩ := eventually_atTop.mp (hc'.eventually_ne zero_ne_top)
      obtain ⟨zi, hzi, z⟩ := h ti
      refine ⟨zi, Nat.le_induction (ofScalars_eq_zero_of_scalar_zero E z) fun n hmn a => ?_⟩
      nontriviality E
      simp only [ofScalars_eq_zero] at a ⊢
      contrapose! hti
      exact ⟨n, hzi.trans hmn, ENNReal.div_eq_top.mpr (by simp [a, hti])⟩
  · simp_rw [hr, inv_top] at hc' ⊢
    apply ofScalars_radius_eq_zero_of_tendsto E c ((tendsto_add_atTop_iff_nat 1).mp ?_)
    refine tendsto_ofReal_nhds_top.mp (Tendsto.congr' ?_ ((tendsto_add_atTop_iff_nat 1).mpr hc'))
    filter_upwards [hc'.eventually_ne top_ne_zero] with n hn
    apply (ofReal_div_of_pos (Ne.lt_of_le (Ne.symm ?_) (norm_nonneg _))).symm
    simp_all
  · have hr' := toReal_ne_zero.mp hr.ne.symm
    have hr'' := toNNReal_ne_zero.mpr hr' -- this result could go in ENNReal
    convert! ofScalars_radius_eq_inv_of_tendsto E c hr'' ?_
    · simp [ENNReal.coe_inv hr'', ENNReal.coe_toNNReal (toReal_ne_zero.mp hr.ne.symm).2]
    · simp_rw [ENNReal.coe_toNNReal_eq_toReal]
refine Tendsto.congr' ?_ (tendsto_toReal hr'.2).comp hc'
      filter_upwards [hc'.eventually_ne hr'.1, hc'.eventually_ne hr'.2]
      simp

end Normed

end FormalMultilinearSeries
