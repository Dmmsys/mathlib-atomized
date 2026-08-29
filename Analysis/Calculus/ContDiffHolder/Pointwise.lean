/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Continuously `k` times differentiable functions with pointwise Hölder continuous derivatives

We say that a function is of class $C^{k+(α)}$ at a point `a`,
where `k` is a natural number and `0 ≤ α ≤ 1`, if

- it is of class $C^k$ at `a` in the sense of `ContDiffAt`;
- its `k`th derivative satisfies $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`.

Note that the Hölder condition used in this definition fixes one of the points at `a`.
In different sources, it is called *pointwise*, *local*, or *weak* Hölder condition,
though the term "local" may also mean a stronger condition
saying that a function is Hölder continuous on a neighborhood of `a`.

The immediate reason for adding this definition to the library
is its use in [Moreira2001], where Moreira proves a version of the Morse-Sard theorem
for functions that satisfy this condition on their critical set.

In this file, we define `ContDiffPointwiseHolderAt` to be the predicate
saying that a function is $C^{k+(α)}$ in the sense described above
and prove basic properties of this predicate.

## Implementation notes

In Moreira's paper, `k` is assumed to be a strictly positive number.
We define the predicate for any `k : ℕ`, then assume `k ≠ 0` whenever it is necessary.
-/

public section

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]
  {k l m : Nat} {α β : I} {f : E -> F} {a : E}

/-- A map `f` is said to be $C^{k+(α)}$ at `a`, where `k` is a natural number and `0 ≤ α ≤ 1`,
if it is $C^k$ at this point and $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`.

When naming lemmas about this predicate, `k` is called "order", and `α` is called "exponent". -/
@[mk_iff]
/--
Definition of `ContDiffPointwiseHolderAt` / `ContDiffPointwiseHolderAt` 的定义

English:
structure ContDiffPointwiseHolderAt
  parameters: (k : Nat) (α : I) (f : E -> F) (a : E)
  axioms and operations (2):
    - contDiffAt : ContDiffAt Real k f a
    - isBigO : (iteratedFDeriv Real k f · - iteratedFDeriv Real k f a) =O[𝓝 a] (‖· - a‖ ^ (α : Real))

中文:
结构 ContDiffPointwiseHolderAt
  参数: (k : 自然数) (α : I) (f : E -> F) (a : E)
  公理与运算 (2 个):
    - contDiffAt : ContDiffAt 实数 k f a
    - isBigO : (iteratedFDeriv 实数 k f · - iteratedFDeriv 实数 k f a) =O[𝓝 a] (‖· - a‖ ^ (α : 实数))
-/
structure ContDiffPointwiseHolderAt (k : Nat) (α : I) (f : E -> F) (a : E) : Prop where
  /-- A $C^{k+(α)}$ map is a $C^k$ map. -/
  contDiffAt : ContDiffAt Real k f a
  /-- A $C^{k+(α)}$ map satisfies $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`. -/
  isBigO : (iteratedFDeriv Real k f · - iteratedFDeriv Real k f a) =O[𝓝 a] (‖· - a‖ ^ (α : Real))

/--
theorem `ContDiffAt.contDiffPointwiseHolderAt` / 定理 `ContDiffAt.contDiffPointwiseHolderAt`

English:
theorem ContDiffAt.contDiffPointwiseHolderAt
  statement: {n : WithTop Nat∞} (h : ContDiffAt Real n f a) (hk : k < n)
  proof: h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv Real k f · - iteratedFDeriv Real k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : Real)) :=
.of_norm_left .comp_tendsto (.id_rpow_of_le_one α.2.2) tendsto_norm_sub_self_nhdsGE a

中文:
定理 ContDiffAt.contDiffPointwiseHolderAt
  结论: {n : WithTop 自然数∞} (h : ContDiffAt 实数 n f a) (hk : k < n)
  证明: h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv Real k f · - iteratedFDeriv Real k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : Real)) :=
.of_norm_left .comp_tendsto (.id_rpow_of_le_one α.2.2) tendsto_norm_sub_self_nhdsGE a

Depends on / 依赖: h.of_le, hk.le, of_le
-/
theorem ContDiffAt.contDiffPointwiseHolderAt {n : WithTop Nat∞} (h : ContDiffAt Real n f a) (hk : k < n)
    (α : I) : ContDiffPointwiseHolderAt k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv Real k f · - iteratedFDeriv Real k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : Real)) :=
.of_norm_left .comp_tendsto (.id_rpow_of_le_one α.2.2) tendsto_norm_sub_self_nhdsGE a

namespace ContDiffPointwiseHolderAt

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: (h : ContDiffPointwiseHolderAt k α f a)
  statement: ContinuousAt f a
  proof: h.contDiffAt.continuousAt

中文:
定理 continuousAt
  条件: (h : ContDiffPointwiseHolderAt k α f a)
  结论: ContinuousAt f a
  证明: h.contDiffAt.continuousAt

Depends on / 依赖: contDiffAt, continuousAt, h.contDiffAt.continuousAt
-/
theorem continuousAt (h : ContDiffPointwiseHolderAt k α f a) : ContinuousAt f a :=
  h.contDiffAt.continuousAt

/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  given: (h : ContDiffPointwiseHolderAt k α f a) (hk : k != 0)
  proof: h.contDiffAt.differentiableAt mod_cast hk

中文:
定理 differentiableAt
  条件: (h : ContDiffPointwiseHolderAt k α f a) (hk : k != 0)
  证明: h.contDiffAt.differentiableAt mod_cast hk

Depends on / 依赖: contDiffAt, differentiableAt, h.contDiffAt.differentiableAt, mod_cast
-/
theorem differentiableAt (h : ContDiffPointwiseHolderAt k α f a) (hk : k != 0) :
    DifferentiableAt Real f a :=
h.contDiffAt.differentiableAt mod_cast hk

/-- A function is $C^{k+(0)}$ at a point if and only if it is $C^k$ at the point. -/
@[simp]
/--
theorem `zero_exponent_iff` / 定理 `zero_exponent_iff`

English:
theorem zero_exponent_iff
  statement: ContDiffPointwiseHolderAt k 0 f a ↔ ContDiffAt Real k f a
  proof: by
  refine ⟨contDiffAt, fun h => ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

中文:
定理 zero_exponent_iff
  结论: ContDiffPointwiseHolderAt k 0 f a ↔ ContDiffAt 实数 k f a
  证明: by
  refine ⟨contDiffAt, fun h => ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

Depends on / 依赖: contDiffAt, continuousAt_iteratedFDeriv, h.continuousAt_iteratedFDeriv, isBoundedUnder_le, le_rfl, norm.isBoundedUnder_le, sub_const
-/
theorem zero_exponent_iff : ContDiffPointwiseHolderAt k 0 f a ↔ ContDiffAt Real k f a := by
  refine ⟨contDiffAt, fun h => ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

/--
theorem `zero_order_iff` / 定理 `zero_order_iff`

English:
theorem zero_order_iff
  proof: by
  simp only [contDiffPointwiseHolderAt_iff, Nat.cast_zero, and_congr_right_iff]
  intro hfc
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub]
  rw [← isBigO_norm_left]
  simp_rw [LinearIsometryEquiv.norm_map, isBigO_norm_left]

中文:
定理 zero_order_iff
  证明: by
  simp only [contDiffPointwiseHolderAt_iff, Nat.cast_zero, and_congr_right_iff]
  intro hfc
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub]
  rw [← isBigO_norm_left]
  simp_rw [LinearIsometryEquiv.norm_map, isBigO_norm_left]

Depends on / 依赖: Function, Function.comp_def, LinearIsometryEquiv, LinearIsometryEquiv.norm_map, Nat.cast_zero, and_congr_right_iff, cast_zero, comp_def, contDiffPointwiseHolderAt_iff, isBigO_norm_left, iteratedFDeriv_zero_eq_comp, map_sub, norm_map, simp_rw
-/
theorem zero_order_iff :
    ContDiffPointwiseHolderAt 0 α f a ↔
      ContDiffAt Real 0 f a ∧ (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (α : Real)) := by
  simp only [contDiffPointwiseHolderAt_iff, Nat.cast_zero, and_congr_right_iff]
  intro hfc
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub]
  rw [← isBigO_norm_left]
  simp_rw [LinearIsometryEquiv.norm_map, isBigO_norm_left]

/--
theorem `of_exponent_le` / 定理 `of_exponent_le`

English:
theorem of_exponent_le
  given: (hf : ContDiffPointwiseHolderAt k α f a) (hle : β <= α)
  proof: hf.contDiffAt
isBigO := hf.isBigO.trans by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le_of_imp hle fun hα => ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a

中文:
定理 of_exponent_le
  条件: (hf : ContDiffPointwiseHolderAt k α f a) (hle : β <= α)
  证明: hf.contDiffAt
isBigO := hf.isBigO.trans by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le_of_imp hle fun hα => ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a

Depends on / 依赖: contDiffAt, hf.contDiffAt
-/
theorem of_exponent_le (hf : ContDiffPointwiseHolderAt k α f a) (hle : β <= α) :
    ContDiffPointwiseHolderAt k β f a where
  contDiffAt := hf.contDiffAt
isBigO := hf.isBigO.trans by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le_of_imp hle fun hα => ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a

/--
theorem `of_order_lt` / 定理 `of_order_lt`

English:
theorem of_order_lt
  given: (hf : ContDiffPointwiseHolderAt k α f a) (hlt : l < k)
  proof: hf.contDiffAt.contDiffPointwiseHolderAt (mod_cast hlt) _

中文:
定理 of_order_lt
  条件: (hf : ContDiffPointwiseHolderAt k α f a) (hlt : l < k)
  证明: hf.contDiffAt.contDiffPointwiseHolderAt (mod_cast hlt) _

Depends on / 依赖: contDiffAt, contDiffPointwiseHolderAt, hf.contDiffAt.contDiffPointwiseHolderAt, mod_cast
-/
theorem of_order_lt (hf : ContDiffPointwiseHolderAt k α f a) (hlt : l < k) :
    ContDiffPointwiseHolderAt l β f a :=
  hf.contDiffAt.contDiffPointwiseHolderAt (mod_cast hlt) _

/--
theorem `of_toLex_le` / 定理 `of_toLex_le`

English:
theorem of_toLex_le
  given: (hf : ContDiffPointwiseHolderAt k α f a) (hle : toLex (l, β) <= toLex (k, α))
  proof: (Prod.Lex.le_iff.mp hle).elim hf.of_order_lt by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

中文:
定理 of_toLex_le
  条件: (hf : ContDiffPointwiseHolderAt k α f a) (hle : toLex (l, β) <= toLex (k, α))
  证明: (Prod.Lex.le_iff.mp hle).elim hf.of_order_lt by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

Depends on / 依赖: Prod.Lex.le_iff.mp, hf.of_exponent_le, hf.of_order_lt, le_iff, of_exponent_le, of_order_lt
-/
theorem of_toLex_le (hf : ContDiffPointwiseHolderAt k α f a) (hle : toLex (l, β) <= toLex (k, α)) :
    ContDiffPointwiseHolderAt l β f a :=
(Prod.Lex.le_iff.mp hle).elim hf.of_order_lt by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

/--
theorem `of_order_le` / 定理 `of_order_le`

English:
theorem of_order_le
  given: (hf : ContDiffPointwiseHolderAt k α f a) (hl : l <= k)
  proof: hf.of_toLex_le Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

中文:
定理 of_order_le
  条件: (hf : ContDiffPointwiseHolderAt k α f a) (hl : l <= k)
  证明: hf.of_toLex_le Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

Depends on / 依赖: Prod.Lex.toLex_mono, hf.of_toLex_le, le_rfl, of_toLex_le, toLex_mono
-/
theorem of_order_le (hf : ContDiffPointwiseHolderAt k α f a) (hl : l <= k) :
    ContDiffPointwiseHolderAt l α f a :=
hf.of_toLex_le Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

/--
theorem `of_contDiffOn_holderOnWith` / 定理 `of_contDiffOn_holderOnWith`

English:
theorem of_contDiffOn_holderOnWith
  statement: {s : Set E} {C : Real>=0} (hf : ContDiffOn Real k f s) (hs : s in 𝓝 a)
  proof: hf.contDiffAt hs
isBigO := .of_bound C mem_of_superset hs fun x hx => by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using! hd.dist_le hx (mem_of_mem_nhds hs)

中文:
定理 of_contDiffOn_holderOnWith
  结论: {s : Set E} {C : 实数>=0} (hf : ContDiffOn 实数 k f s) (hs : s in 𝓝 a)
  证明: hf.contDiffAt hs
isBigO := .of_bound C mem_of_superset hs fun x hx => by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using! hd.dist_le hx (mem_of_mem_nhds hs)

Depends on / 依赖: contDiffAt, hf.contDiffAt
-/
theorem of_contDiffOn_holderOnWith {s : Set E} {C : Real>=0} (hf : ContDiffOn Real k f s) (hs : s in 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv Real k f) s) :
    ContDiffPointwiseHolderAt k α f a where
  contDiffAt := hf.contDiffAt hs
isBigO := .of_bound C mem_of_superset hs fun x hx => by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using! hd.dist_le hx (mem_of_mem_nhds hs)

/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  given: {a : E × F}
  statement: ContDiffPointwiseHolderAt k α Prod.fst a
  proof: contDiffAt_fst.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

中文:
定理 fst
  条件: {a : E × F}
  结论: ContDiffPointwiseHolderAt k α Prod.fst a
  证明: contDiffAt_fst.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

Depends on / 依赖: WithTop, WithTop.coe_lt_top, coe_lt_top, contDiffAt_fst, contDiffAt_fst.contDiffPointwiseHolderAt, contDiffPointwiseHolderAt
-/
theorem fst {a : E × F} : ContDiffPointwiseHolderAt k α Prod.fst a :=
  contDiffAt_fst.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  given: {a : E × F}
  statement: ContDiffPointwiseHolderAt k α Prod.snd a
  proof: contDiffAt_snd.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

中文:
定理 snd
  条件: {a : E × F}
  结论: ContDiffPointwiseHolderAt k α Prod.snd a
  证明: contDiffAt_snd.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

Depends on / 依赖: WithTop, WithTop.coe_lt_top, coe_lt_top, contDiffAt_snd, contDiffAt_snd.contDiffPointwiseHolderAt, contDiffPointwiseHolderAt
-/
theorem snd {a : E × F} : ContDiffPointwiseHolderAt k α Prod.snd a :=
  contDiffAt_snd.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

/--
theorem `prodMk` / 定理 `prodMk`

English:
theorem prodMk
  statement: {g : E -> G} (hf : ContDiffPointwiseHolderAt k α f a)
  proof: hf.contDiffAt.prodMk hg.contDiffAt
  isBigO := calc
    _ =ᶠ[𝓝 a] (fun x => (iteratedFDeriv Real k f x - iteratedFDeriv Real k f a).prod
                (iteratedFDeriv Real k g x - iteratedFDeriv Real k g a)) := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hg.contDiffAt.even

中文:
定理 prodMk
  结论: {g : E -> G} (hf : ContDiffPointwiseHolderAt k α f a)
  证明: hf.contDiffAt.prodMk hg.contDiffAt
  isBigO := calc
    _ =ᶠ[𝓝 a] (fun x => (iteratedFDeriv Real k f x - iteratedFDeriv Real k f a).prod
                (iteratedFDeriv Real k g x - iteratedFDeriv Real k g a)) := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hg.contDiffAt.even

Depends on / 依赖: contDiffAt, hf.contDiffAt.prodMk, hg.contDiffAt, prodMk
-/
theorem prodMk {g : E -> G} (hf : ContDiffPointwiseHolderAt k α f a)
    (hg : ContDiffPointwiseHolderAt k α g a) :
    ContDiffPointwiseHolderAt k α (fun x => (f x, g x)) a where
  contDiffAt := hf.contDiffAt.prodMk hg.contDiffAt
  isBigO := calc
    _ =ᶠ[𝓝 a] (fun x => (iteratedFDeriv Real k f x - iteratedFDeriv Real k f a).prod
                (iteratedFDeriv Real k g x - iteratedFDeriv Real k g a)) := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hg.contDiffAt.eventually (by simp)] with x hfx hgx
      apply DFunLike.ext
      rw [iteratedFDeriv_prodMk _ _ le_rfl]; rw [iteratedFDeriv_prodMk _ _ le_rfl] <;>
        simp [hfx, hgx, hf.contDiffAt, hg.contDiffAt]
    _ =O[𝓝 a] fun x => ‖x - a‖ ^ (α : Real) := by
      refine .of_norm_left ?_
      simp only [ContinuousMultilinearMap.opNorm_prod, ← Prod.norm_mk]
      exact (hf.isBigO.prod_left hg.isBigO).norm_left

variable (a) in
/--
theorem `comp_of_differentiableAt` / 定理 `comp_of_differentiableAt`

English:
theorem comp_of_differentiableAt
  statement: {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a))
  proof: hg.contDiffAt.comp a hf.contDiffAt
  isBigO := calc
    (iteratedFDeriv Real k (g ∘ f) · - iteratedFDeriv Real k (g ∘ f) a)
      =ᶠ[𝓝 a] fun x => (ftaylorSeries Real g (f x)).taylorComp (ftaylorSeries Real f x) k -
        (ftaylorSeries Real g (f a)).taylorComp (ftaylorSeries Real f a) k := by
   

中文:
定理 comp_of_differentiableAt
  结论: {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a))
  证明: hg.contDiffAt.comp a hf.contDiffAt
  isBigO := calc
    (iteratedFDeriv Real k (g ∘ f) · - iteratedFDeriv Real k (g ∘ f) a)
      =ᶠ[𝓝 a] fun x => (ftaylorSeries Real g (f x)).taylorComp (ftaylorSeries Real f x) k -
        (ftaylorSeries Real g (f a)).taylorComp (ftaylorSeries Real f a) k := by
   

Depends on / 依赖: contDiffAt, hf.contDiffAt, hg.contDiffAt.comp
-/
theorem comp_of_differentiableAt {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a))
    (hf : ContDiffPointwiseHolderAt k α f a)
    (hd : DifferentiableAt Real g (f a) ∨ DifferentiableAt Real f a) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a where
  contDiffAt := hg.contDiffAt.comp a hf.contDiffAt
  isBigO := calc
    (iteratedFDeriv Real k (g ∘ f) · - iteratedFDeriv Real k (g ∘ f) a)
      =ᶠ[𝓝 a] fun x => (ftaylorSeries Real g (f x)).taylorComp (ftaylorSeries Real f x) k -
        (ftaylorSeries Real g (f a)).taylorComp (ftaylorSeries Real f a) k := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hf.continuousAt.eventually (hg.contDiffAt.eventually (by simp))] with x hfx hgx
      rw [iteratedFDeriv_comp hgx hfx le_rfl]; rw [iteratedFDeriv_comp hg.contDiffAt hf.contDiffAt le_rfl]
    _ =O[𝓝 a] fun x => ‖x - a‖ ^ (α : Real) := by
      apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO <;> intro i hi
      · exact ((hg.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).comp hf.continuousAt)
.norm.isBoundedUnder_le
      · by_cases hfd : DifferentiableAt Real f a
        · refine ((hg.of_order_le hi).isBigO.comp_tendsto hf.continuousAt).trans ?_
refine .rpow α.2.1 (.of_forall fun _ => norm_nonneg _) .norm_norm ?_
          exact hfd.isBigO_sub
        · obtain rfl : k = 0 := by
            contrapose! hfd
            exact hf.differentiableAt hfd
          obtain rfl : i = 0 := by rwa [nonpos_iff_eq_zero] at hi
          refine .of_norm_left ?_
          simp only [ftaylorSeries, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
            LinearIsometryEquiv.norm_map, isBigO_norm_left]
          refine ((hd.resolve_right hfd).isBigO_sub.comp_tendsto hf.continuousAt).trans ?_
          exact (zero_order_iff.mp hf).2
      · exact (hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).norm.isBoundedUnder_le
      · exact isBoundedUnder_const
      · exact (hf.of_order_le hi).isBigO

variable (a) in
/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a))
  proof: hg.comp_of_differentiableAt a hf (.inl <| hg.differentiableAt hk)

中文:
定理 comp
  结论: {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a))
  证明: hg.comp_of_differentiableAt a hf (.inl <| hg.differentiableAt hk)

Depends on / 依赖: comp_of_differentiableAt, differentiableAt, hg.comp_of_differentiableAt, hg.differentiableAt
-/
theorem comp {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a))
    (hf : ContDiffPointwiseHolderAt k α f a) (hk : k != 0) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a :=
  hg.comp_of_differentiableAt a hf (.inl <| hg.differentiableAt hk)

variable (a) in
/--
theorem `comp₂_of_differentiableAt` / 定理 `comp₂_of_differentiableAt`

English:
theorem comp₂_of_differentiableAt
  statement: {H : Type*} [NormedAddCommGroup H] [NormedSpace Real H]
  proof: hg.comp_of_differentiableAt a (hf₁.prodMk hf₂) hdiff.imp_right fun h =>
    h.left.prodMk h.right

中文:
定理 comp₂_of_differentiableAt
  结论: {H : 类型} [NormedAddCommGroup H] [NormedSpace 实数 H]
  证明: hg.comp_of_differentiableAt a (hf₁.prodMk hf₂) hdiff.imp_right fun h =>
    h.left.prodMk h.right

Depends on / 依赖: comp_of_differentiableAt, h.left.prodMk, h.right, hdiff.imp_right, hg.comp_of_differentiableAt, imp_right, prodMk
-/
theorem comp₂_of_differentiableAt {H : Type*} [NormedAddCommGroup H] [NormedSpace Real H]
    {g : F × G -> H} {f₁ : E -> F} {f₂ : E -> G} (hg : ContDiffPointwiseHolderAt k α g (f₁ a, f₂ a))
    (hf₁ : ContDiffPointwiseHolderAt k α f₁ a) (hf₂ : ContDiffPointwiseHolderAt k α f₂ a)
    (hdiff : DifferentiableAt Real g (f₁ a, f₂ a) ∨
      DifferentiableAt Real f₁ a ∧ DifferentiableAt Real f₂ a) :
    ContDiffPointwiseHolderAt k α (fun x => g (f₁ x, f₂ x)) a :=
hg.comp_of_differentiableAt a (hf₁.prodMk hf₂) hdiff.imp_right fun h =>
    h.left.prodMk h.right

/--
theorem `_root_.ContinuousLinearMap.contDiffPointwiseHolderAt` / 定理 `_root_.ContinuousLinearMap.contDiffPointwiseHolderAt`

English:
theorem _root_.ContinuousLinearMap.contDiffPointwiseHolderAt
  given: (f : E ->L[Real] F)
  proof: f.contDiff.contDiffAt.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _

中文:
定理 _root_.ContinuousLinearMap.contDiffPointwiseHolderAt
  条件: (f : E ->L[实数] F)
  证明: f.contDiff.contDiffAt.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _

Depends on / 依赖: WithTop, WithTop.coe_lt_top, coe_lt_top, contDiff, contDiffAt, contDiffPointwiseHolderAt, f.contDiff.contDiffAt.contDiffPointwiseHolderAt
-/
theorem _root_.ContinuousLinearMap.contDiffPointwiseHolderAt (f : E ->L[Real] F) :
    ContDiffPointwiseHolderAt k α f a :=
  f.contDiff.contDiffAt.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _

/--
theorem `_root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt` / 定理 `_root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt`

English:
theorem _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt
  given: (f : E ≃L[Real] F)
  proof: f.toContinuousLinearMap.contDiffPointwiseHolderAt

中文:
定理 _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt
  条件: (f : E ≃L[实数] F)
  证明: f.toContinuousLinearMap.contDiffPointwiseHolderAt

Depends on / 依赖: contDiffPointwiseHolderAt, f.toContinuousLinearMap.contDiffPointwiseHolderAt, toContinuousLinearMap
-/
theorem _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt (f : E ≃L[Real] F) :
    ContDiffPointwiseHolderAt k α f a :=
  f.toContinuousLinearMap.contDiffPointwiseHolderAt

/--
theorem `continuousLinearMap_comp` / 定理 `continuousLinearMap_comp`

English:
theorem continuousLinearMap_comp
  given: (hf : ContDiffPointwiseHolderAt k α f a) (g : F ->L[Real] G)
  proof: g.contDiffPointwiseHolderAt.comp_of_differentiableAt a hf .inl g.differentiableAt

@[simp]

中文:
定理 continuousLinearMap_comp
  条件: (hf : ContDiffPointwiseHolderAt k α f a) (g : F ->L[实数] G)
  证明: g.contDiffPointwiseHolderAt.comp_of_differentiableAt a hf .inl g.differentiableAt

@[simp]

Depends on / 依赖: comp_of_differentiableAt, contDiffPointwiseHolderAt, differentiableAt, g.contDiffPointwiseHolderAt.comp_of_differentiableAt, g.differentiableAt
-/
theorem continuousLinearMap_comp (hf : ContDiffPointwiseHolderAt k α f a) (g : F ->L[Real] G) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a :=
g.contDiffPointwiseHolderAt.comp_of_differentiableAt a hf .inl g.differentiableAt

@[simp]
/--
theorem `_root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp` / 定理 `_root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp`

English:
theorem _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp
  given: (g : F ≃L[Real] G)
  proof: ⟨fun h => by simpa [Function.comp_def] using h.continuousLinearMap_comp (g.symm : G ->L[Real] F),
    fun h => h.continuousLinearMap_comp (g : F ->L[Real] G)⟩

@[simp]

中文:
定理 _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp
  条件: (g : F ≃L[实数] G)
  证明: ⟨fun h => by simpa [Function.comp_def] using h.continuousLinearMap_comp (g.symm : G ->L[Real] F),
    fun h => h.continuousLinearMap_comp (g : F ->L[Real] G)⟩

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_def, continuousLinearMap_comp, g.symm, h.continuousLinearMap_comp
-/
theorem _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp (g : F ≃L[Real] G) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a ↔ ContDiffPointwiseHolderAt k α f a :=
  ⟨fun h => by simpa [Function.comp_def] using h.continuousLinearMap_comp (g.symm : G ->L[Real] F),
    fun h => h.continuousLinearMap_comp (g : F ->L[Real] G)⟩

@[simp]
/--
theorem `_root_.LinearIsometryEquiv.contDiffPointwiseHolderAt_left_comp` / 定理 `_root_.LinearIsometryEquiv.contDiffPointwiseHolderAt_left_comp`

English:
theorem _root_.LinearIsometryEquiv.contDiffPointwiseHolderAt_left_comp
  given: (g : F ≃ₗᵢ[Real] G)
  proof: g.toContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp

中文:
定理 _root_.LinearIsometryEquiv.contDiffPointwiseHolderAt_left_comp
  条件: (g : F ≃ₗᵢ[实数] G)
  证明: g.toContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp

Depends on / 依赖: contDiffPointwiseHolderAt_left_comp, g.toContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp, toContinuousLinearEquiv
-/
theorem _root_.LinearIsometryEquiv.contDiffPointwiseHolderAt_left_comp (g : F ≃ₗᵢ[Real] G) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a ↔ ContDiffPointwiseHolderAt k α f a :=
  g.toContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: ContDiffPointwiseHolderAt k α id a
  proof: .contDiffPointwiseHolderAt ContinuousLinearMap.id Real E

中文:
定理 id
  结论: ContDiffPointwiseHolderAt k α id a
  证明: .contDiffPointwiseHolderAt ContinuousLinearMap.id Real E
-/
protected theorem id : ContDiffPointwiseHolderAt k α id a :=
.contDiffPointwiseHolderAt ContinuousLinearMap.id Real E

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: {b : F}
  statement: ContDiffPointwiseHolderAt k α (Function.const E b) a
  proof: contDiffAt_const.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

中文:
定理 const
  条件: {b : F}
  结论: ContDiffPointwiseHolderAt k α (Function.const E b) a
  证明: contDiffAt_const.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α
-/
protected theorem const {b : F} : ContDiffPointwiseHolderAt k α (Function.const E b) a :=
  contDiffAt_const.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

/--
theorem `fderiv` / 定理 `fderiv`

English:
theorem fderiv
  given: (hf : ContDiffPointwiseHolderAt k α f a) (hl : l < k)
  proof: hf.contDiffAt.fderiv_right (mod_cast hl)
isBigO := .of_norm_left by
    simpa [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, ← dist_eq_norm_sub]
.norm_left .isBigO using hf.of_order_le (Nat.add_one_le_iff.mpr hl)

中文:
定理 fderiv
  条件: (hf : ContDiffPointwiseHolderAt k α f a) (hl : l < k)
  证明: hf.contDiffAt.fderiv_right (mod_cast hl)
isBigO := .of_norm_left by
    simpa [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, ← dist_eq_norm_sub]
.norm_left .isBigO using hf.of_order_le (Nat.add_one_le_iff.mpr hl)
-/
protected theorem fderiv (hf : ContDiffPointwiseHolderAt k α f a) (hl : l < k) :
    ContDiffPointwiseHolderAt l α (fderiv Real f) a where
  contDiffAt := hf.contDiffAt.fderiv_right (mod_cast hl)
isBigO := .of_norm_left by
    simpa [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, ← dist_eq_norm_sub]
.norm_left .isBigO using hf.of_order_le (Nat.add_one_le_iff.mpr hl)

/--
theorem `iteratedFDeriv` / 定理 `iteratedFDeriv`

English:
theorem iteratedFDeriv
  given: (hf : ContDiffPointwiseHolderAt k α f a) (hl : l + m <= k)
  proof: by
  induction m generalizing l with
  | zero =>
    simpa +unfoldPartialApp [iteratedFDeriv_zero_eq_comp] using hf.of_order_le hl
  | succ m ihm =>
    rw [← add_assoc]; rw [add_right_comm] at hl
    simpa +unfoldPartialApp [iteratedFDeriv_succ_eq_comp_left] using (ihm hl).fderiv l.lt_add_one

中文:
定理 iteratedFDeriv
  条件: (hf : ContDiffPointwiseHolderAt k α f a) (hl : l + m <= k)
  证明: by
  induction m generalizing l with
  | zero =>
    simpa +unfoldPartialApp [iteratedFDeriv_zero_eq_comp] using hf.of_order_le hl
  | succ m ihm =>
    rw [← add_assoc]; rw [add_right_comm] at hl
    simpa +unfoldPartialApp [iteratedFDeriv_succ_eq_comp_left] using (ihm hl).fderiv l.lt_add_one
-/
protected theorem iteratedFDeriv (hf : ContDiffPointwiseHolderAt k α f a) (hl : l + m <= k) :
    ContDiffPointwiseHolderAt l α (iteratedFDeriv Real m f) a := by
  induction m generalizing l with
  | zero =>
    simpa +unfoldPartialApp [iteratedFDeriv_zero_eq_comp] using hf.of_order_le hl
  | succ m ihm =>
    rw [← add_assoc]; rw [add_right_comm] at hl
    simpa +unfoldPartialApp [iteratedFDeriv_succ_eq_comp_left] using (ihm hl).fderiv l.lt_add_one

/--
theorem `congr_of_eventuallyEq` / 定理 `congr_of_eventuallyEq`

English:
theorem congr_of_eventuallyEq
  statement: {g : E -> F} (hf : ContDiffPointwiseHolderAt k α f a)
  proof: hf.contDiffAt.congr_of_eventuallyEq hfg.symm
  isBigO := by
    refine EventuallyEq.trans_isBigO (.sub ?_ ?_) hf.isBigO
    · exact hfg.symm.iteratedFDeriv Real _
    · rw [hfg.symm.iteratedFDeriv Real _ |>.self_of_nhds]

中文:
定理 congr_of_eventuallyEq
  结论: {g : E -> F} (hf : ContDiffPointwiseHolderAt k α f a)
  证明: hf.contDiffAt.congr_of_eventuallyEq hfg.symm
  isBigO := by
    refine EventuallyEq.trans_isBigO (.sub ?_ ?_) hf.isBigO
    · exact hfg.symm.iteratedFDeriv Real _
    · rw [hfg.symm.iteratedFDeriv Real _ |>.self_of_nhds]

Depends on / 依赖: congr_of_eventuallyEq, contDiffAt, hf.contDiffAt.congr_of_eventuallyEq, hfg.symm
-/
theorem congr_of_eventuallyEq {g : E -> F} (hf : ContDiffPointwiseHolderAt k α f a)
    (hfg : f =ᶠ[𝓝 a] g) :
    ContDiffPointwiseHolderAt k α g a where
  contDiffAt := hf.contDiffAt.congr_of_eventuallyEq hfg.symm
  isBigO := by
    refine EventuallyEq.trans_isBigO (.sub ?_ ?_) hf.isBigO
    · exact hfg.symm.iteratedFDeriv Real _
    · rw [hfg.symm.iteratedFDeriv Real _ |>.self_of_nhds]

/--
theorem `clm_apply` / 定理 `clm_apply`

English:
theorem clm_apply
  statement: {f : E -> F ->L[Real] G} {g : E -> F} (hf : ContDiffPointwiseHolderAt k α f a)
  proof: (contDiffAt_fst.clm_apply contDiffAt_snd).contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _
.comp₂_of_differentiableAt a hf hg .inl (by fun_prop)

中文:
定理 clm_apply
  结论: {f : E -> F ->L[实数] G} {g : E -> F} (hf : ContDiffPointwiseHolderAt k α f a)
  证明: (contDiffAt_fst.clm_apply contDiffAt_snd).contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _
.comp₂_of_differentiableAt a hf hg .inl (by fun_prop)

Depends on / 依赖: WithTop, WithTop.coe_lt_top, clm_apply, coe_lt_top, contDiffAt_fst, contDiffAt_fst.clm_apply, contDiffAt_snd, contDiffPointwiseHolderAt, fun_prop
-/
theorem clm_apply {f : E -> F ->L[Real] G} {g : E -> F} (hf : ContDiffPointwiseHolderAt k α f a)
    (hg : ContDiffPointwiseHolderAt k α g a) :
    ContDiffPointwiseHolderAt k α (fun x => f x (g x)) a :=
  (contDiffAt_fst.clm_apply contDiffAt_snd).contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _
.comp₂_of_differentiableAt a hf hg .inl (by fun_prop)

end ContDiffPointwiseHolderAt
