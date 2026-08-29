/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.NNReal

/-!
# Hölder continuous functions

In this file we define Hölder continuity on a set and on the whole space. We also prove some basic
properties of Hölder continuous functions.

## Main definitions

* `HolderOnWith`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and
  exponent `r : ℝ≥0` on a set `s`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y ∈ s`;
* `HolderWith`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and exponent
  `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`.

## Implementation notes

We use the type `ℝ≥0` (a.k.a. `NNReal`) for `C` because this type has coercion both to `ℝ` and
`ℝ≥0∞`, so it can be easily used both in inequalities about `dist` and `edist`. We also use `ℝ≥0`
for `r` to ensure that `d ^ r` is monotone in `d`. It might be a good idea to use
`ℝ>0` for `r` but we don't have this type in `mathlib` (yet).

## Tags

Hölder continuity, Lipschitz continuity

-/

@[expose] public section


variable {X Y Z : Type*}

open Filter Set Metric
open scoped NNReal ENNReal Topology

section EMetric

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/--
Definition of `HolderWith` / `HolderWith` 的定义

English:
definition HolderWith
  signature: (C r : Real>=0) (f : X -> Y)
  body: forall x y, edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r : Real)

中文:
定义 HolderWith
  签名: (C r : 实数>=0) (f : X -> Y)
  定义体: forall x y, edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r : Real)
-/
def HolderWith (C r : Real>=0) (f : X -> Y) : Prop :=
  forall x y, edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r : Real)

/--
Definition of `HolderOnWith` / `HolderOnWith` 的定义

English:
definition HolderOnWith
  signature: (C r : Real>=0) (f : X -> Y) (s : Set X)
  body: forall x in s, forall y in s, edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r : Real)

@[simp]

中文:
定义 HolderOnWith
  签名: (C r : 实数>=0) (f : X -> Y) (s : 集合 X)
  定义体: forall x in s, forall y in s, edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r : Real)

@[simp]
-/
def HolderOnWith (C r : Real>=0) (f : X -> Y) (s : Set X) : Prop :=
  forall x in s, forall y in s, edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r : Real)

@[simp]
/--
theorem `holderOnWith_empty` / 定理 `holderOnWith_empty`

English:
theorem holderOnWith_empty
  given: (C r : Real>=0) (f : X -> Y)
  statement: HolderOnWith C r f ∅
  proof: fun _ hx => hx.elim

@[simp]

中文:
定理 holderOnWith_empty
  条件: (C r : 实数>=0) (f : X -> Y)
  结论: HolderOnWith C r f ∅
  证明: fun _ hx => hx.elim

@[simp]

Depends on / 依赖: hx.elim
-/
theorem holderOnWith_empty (C r : Real>=0) (f : X -> Y) : HolderOnWith C r f ∅ := fun _ hx => hx.elim

@[simp]
/--
theorem `holderOnWith_singleton` / 定理 `holderOnWith_singleton`

English:
theorem holderOnWith_singleton
  given: (C r : Real>=0) (f : X -> Y) (x : X)
  statement: HolderOnWith C r f {x}
  proof: by
  simp [HolderOnWith]

中文:
定理 holderOnWith_singleton
  条件: (C r : 实数>=0) (f : X -> Y) (x : X)
  结论: HolderOnWith C r f {x}
  证明: by
  simp [HolderOnWith]

Depends on / 依赖: HolderOnWith
-/
theorem holderOnWith_singleton (C r : Real>=0) (f : X -> Y) (x : X) : HolderOnWith C r f {x} := by
  simp [HolderOnWith]

/--
theorem `Set.Subsingleton.holderOnWith` / 定理 `Set.Subsingleton.holderOnWith`

English:
theorem Set.Subsingleton.holderOnWith
  given: {s : Set X} (hs : s.Subsingleton) (C r : Real>=0) (f : X -> Y)
  proof: hs.induction_on (holderOnWith_empty C r f) (holderOnWith_singleton C r f)

中文:
定理 集合.子单例.holderOnWith
  条件: {s : 集合 X} (hs : s.子单例) (C r : 实数>=0) (f : X -> Y)
  证明: hs.induction_on (holderOnWith_empty C r f) (holderOnWith_singleton C r f)

Depends on / 依赖: holderOnWith_empty, holderOnWith_singleton, hs.induction_on, induction_on
-/
theorem Set.Subsingleton.holderOnWith {s : Set X} (hs : s.Subsingleton) (C r : Real>=0) (f : X -> Y) :
    HolderOnWith C r f s :=
  hs.induction_on (holderOnWith_empty C r f) (holderOnWith_singleton C r f)

/--
theorem `holderOnWith_univ` / 定理 `holderOnWith_univ`

English:
theorem holderOnWith_univ
  given: {C r : Real>=0} {f : X -> Y}
  statement: HolderOnWith C r f univ ↔ HolderWith C r f
  proof: by
  simp only [HolderOnWith, HolderWith, mem_univ, true_imp_iff]

@[simp]

中文:
定理 holderOnWith_univ
  条件: {C r : 实数>=0} {f : X -> Y}
  结论: HolderOnWith C r f univ ↔ HolderWith C r f
  证明: by
  simp only [HolderOnWith, HolderWith, mem_univ, true_imp_iff]

@[simp]

Depends on / 依赖: HolderOnWith, HolderWith, mem_univ, true_imp_iff
-/
theorem holderOnWith_univ {C r : Real>=0} {f : X -> Y} : HolderOnWith C r f univ ↔ HolderWith C r f := by
  simp only [HolderOnWith, HolderWith, mem_univ, true_imp_iff]

@[simp]
/--
theorem `holderOnWith_one` / 定理 `holderOnWith_one`

English:
theorem holderOnWith_one
  given: {C : Real>=0} {f : X -> Y} {s : Set X}
  proof: by
  simp only [HolderOnWith, LipschitzOnWith, NNReal.coe_one, ENNReal.rpow_one]

alias ⟨_, LipschitzOnWith.holderOnWith⟩ := holderOnWith_one

@[simp]

中文:
定理 holderOnWith_one
  条件: {C : 实数>=0} {f : X -> Y} {s : 集合 X}
  证明: by
  simp only [HolderOnWith, LipschitzOnWith, NNReal.coe_one, ENNReal.rpow_one]

alias ⟨_, LipschitzOnWith.holderOnWith⟩ := holderOnWith_one

@[simp]

Depends on / 依赖: ENNReal, ENNReal.rpow_one, HolderOnWith, LipschitzOnWith, NNReal, NNReal.coe_one, coe_one, rpow_one
-/
theorem holderOnWith_one {C : Real>=0} {f : X -> Y} {s : Set X} :
    HolderOnWith C 1 f s ↔ LipschitzOnWith C f s := by
  simp only [HolderOnWith, LipschitzOnWith, NNReal.coe_one, ENNReal.rpow_one]

alias ⟨_, LipschitzOnWith.holderOnWith⟩ := holderOnWith_one

@[simp]
/--
theorem `holderWith_one` / 定理 `holderWith_one`

English:
theorem holderWith_one
  given: {C : Real>=0} {f : X -> Y}
  statement: HolderWith C 1 f ↔ LipschitzWith C f
  proof: holderOnWith_univ.symm.trans holderOnWith_one.trans lipschitzOnWith_univ

alias ⟨_, LipschitzWith.holderWith⟩ := holderWith_one

中文:
定理 holderWith_one
  条件: {C : 实数>=0} {f : X -> Y}
  结论: HolderWith C 1 f ↔ LipschitzWith C f
  证明: holderOnWith_univ.symm.trans holderOnWith_one.trans lipschitzOnWith_univ

alias ⟨_, LipschitzWith.holderWith⟩ := holderWith_one

Depends on / 依赖: holderOnWith_one, holderOnWith_one.trans, holderOnWith_univ, holderOnWith_univ.symm.trans, lipschitzOnWith_univ
-/
theorem holderWith_one {C : Real>=0} {f : X -> Y} : HolderWith C 1 f ↔ LipschitzWith C f :=
holderOnWith_univ.symm.trans holderOnWith_one.trans lipschitzOnWith_univ

alias ⟨_, LipschitzWith.holderWith⟩ := holderWith_one

/--
theorem `holderWith_id` / 定理 `holderWith_id`

English:
theorem holderWith_id
  statement: HolderWith 1 1 (id : X -> X)
  proof: LipschitzWith.id.holderWith

中文:
定理 holderWith_id
  结论: HolderWith 1 1 (id : X -> X)
  证明: LipschitzWith.id.holderWith

Depends on / 依赖: LipschitzWith, LipschitzWith.id.holderWith, holderWith
-/
theorem holderWith_id : HolderWith 1 1 (id : X -> X) :=
  LipschitzWith.id.holderWith

/--
theorem `HolderWith.holderOnWith` / 定理 `HolderWith.holderOnWith`

English:
theorem HolderWith.holderOnWith
  statement: {C r : Real>=0} {f : X -> Y} (h : HolderWith C r f)
  proof: fun x _ y _ => h x y

中文:
定理 HolderWith.holderOnWith
  结论: {C r : 实数>=0} {f : X -> Y} (h : HolderWith C r f)
  证明: fun x _ y _ => h x y
-/
protected theorem HolderWith.holderOnWith {C r : Real>=0} {f : X -> Y} (h : HolderWith C r f)
    (s : Set X) : HolderOnWith C r f s := fun x _ y _ => h x y

namespace HolderOnWith

variable {C r : Real>=0} {f : X -> Y} {s t : Set X}

/--
theorem `edist_le` / 定理 `edist_le`

English:
theorem edist_le
  given: (h : HolderOnWith C r f s) {x y : X} (hx : x in s) (hy : y in s)
  proof: h x hx y hy

中文:
定理 edist_le
  条件: (h : HolderOnWith C r f s) {x y : X} (hx : x in s) (hy : y in s)
  证明: h x hx y hy
-/
theorem edist_le (h : HolderOnWith C r f s) {x y : X} (hx : x in s) (hy : y in s) :
    edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r : Real) :=
  h x hx y hy

/--
theorem `edist_le_of_le` / 定理 `edist_le_of_le`

English:
theorem edist_le_of_le
  statement: (h : HolderOnWith C r f s) {x y : X} (hx : x in s) (hy : y in s) {d : Real>=0∞}
  proof: (h.edist_le hx hy).trans by gcongr

中文:
定理 edist_le_of_le
  结论: (h : HolderOnWith C r f s) {x y : X} (hx : x in s) (hy : y in s) {d : 实数>=0∞}
  证明: (h.edist_le hx hy).trans by gcongr

Depends on / 依赖: edist_le, h.edist_le
-/
theorem edist_le_of_le (h : HolderOnWith C r f s) {x y : X} (hx : x in s) (hy : y in s) {d : Real>=0∞}
    (hd : edist x y <= d) : edist (f x) (f y) <= (C : Real>=0∞) * d ^ (r : Real) :=
(h.edist_le hx hy).trans by gcongr

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {Cg rg : Real>=0} {g : Y -> Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf : Real>=0}
  proof: by
  intro x hx y hy
  rw [ENNReal.coe_mul]; rw [mul_comm rg]; rw [NNReal.coe_mul]; rw [ENNReal.rpow_mul]; rw [mul_assoc]; rw [ENNReal.coe_rpow_of_nonneg _ rg.coe_nonneg]; rw [← ENNReal.mul_rpow_of_nonneg _ _ rg.coe_nonneg]
  exact hg.edist_le_of_le (hst hx) (hst hy) (hf.edist_le hx hy)

中文:
定理 comp
  结论: {Cg rg : 实数>=0} {g : Y -> Z} {t : 集合 Y} (hg : HolderOnWith Cg rg g t) {Cf rf : 实数>=0}
  证明: by
  intro x hx y hy
  rw [ENNReal.coe_mul]; rw [mul_comm rg]; rw [NNReal.coe_mul]; rw [ENNReal.rpow_mul]; rw [mul_assoc]; rw [ENNReal.coe_rpow_of_nonneg _ rg.coe_nonneg]; rw [← ENNReal.mul_rpow_of_nonneg _ _ rg.coe_nonneg]
  exact hg.edist_le_of_le (hst hx) (hst hy) (hf.edist_le hx hy)

Depends on / 依赖: ENNReal, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_mul, NNReal, NNReal.coe_mul, coe_mul, coe_nonneg, coe_rpow_of_nonneg, edist_le, edist_le_of_le, hf.edist_le, hg.edist_le_of_le, mul_assoc, mul_comm, mul_rpow_of_nonneg, rg.coe_nonneg, rpow_mul
-/
theorem comp {Cg rg : Real>=0} {g : Y -> Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf : Real>=0}
    {f : X -> Y} (hf : HolderOnWith Cf rf f s) (hst : MapsTo f s t) :
    HolderOnWith (Cg * Cf ^ (rg : Real)) (rg * rf) (g ∘ f) s := by
  intro x hx y hy
  rw [ENNReal.coe_mul]; rw [mul_comm rg]; rw [NNReal.coe_mul]; rw [ENNReal.rpow_mul]; rw [mul_assoc]; rw [ENNReal.coe_rpow_of_nonneg _ rg.coe_nonneg]; rw [← ENNReal.mul_rpow_of_nonneg _ _ rg.coe_nonneg]
  exact hg.edist_le_of_le (hst hx) (hst hy) (hf.edist_le hx hy)

/--
theorem `comp_holderWith` / 定理 `comp_holderWith`

English:
theorem comp_holderWith
  statement: {Cg rg : Real>=0} {g : Y -> Z} {t : Set Y} (hg : HolderOnWith Cg rg g t)
  proof: holderOnWith_univ.mp hg.comp (hf.holderOnWith univ) fun x _ => ht x

中文:
定理 comp_holderWith
  结论: {Cg rg : 实数>=0} {g : Y -> Z} {t : 集合 Y} (hg : HolderOnWith Cg rg g t)
  证明: holderOnWith_univ.mp hg.comp (hf.holderOnWith univ) fun x _ => ht x

Depends on / 依赖: hf.holderOnWith, hg.comp, holderOnWith, holderOnWith_univ, holderOnWith_univ.mp
-/
theorem comp_holderWith {Cg rg : Real>=0} {g : Y -> Z} {t : Set Y} (hg : HolderOnWith Cg rg g t)
    {Cf rf : Real>=0} {f : X -> Y} (hf : HolderWith Cf rf f) (ht : forall x, f x in t) :
    HolderWith (Cg * Cf ^ (rg : Real)) (rg * rf) (g ∘ f) :=
holderOnWith_univ.mp hg.comp (hf.holderOnWith univ) fun x _ => ht x

/--
theorem `uniformContinuousOn` / 定理 `uniformContinuousOn`

English:
theorem uniformContinuousOn
  given: (hf : HolderOnWith C r f s) (h0 : 0 < r)
  proof: by
  refine EMetric.uniformContinuousOn_iff.2 fun ε εpos => ?_
  have : Tendsto (fun d : Real>=0∞ => (C : Real>=0∞) * d ^ (r : Real)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top h0
  rcases ENNReal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)) with ⟨δ, δ0, H⟩
  exact ⟨δ, δ0, fun hx y hy h => (hf.edist_le hx hy).trans_lt (H h)⟩

中文:
定理 uniformContinuousOn
  条件: (hf : HolderOnWith C r f s) (h0 : 0 < r)
  证明: by
  refine EMetric.uniformContinuousOn_iff.2 fun ε εpos => ?_
  have : Tendsto (fun d : Real>=0∞ => (C : Real>=0∞) * d ^ (r : Real)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top h0
  rcases ENNReal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)) with ⟨δ, δ0, H⟩
  exact ⟨δ, δ0, fun hx y hy h => (hf.edist_le hx hy).trans_lt (H h)⟩
-/
protected theorem uniformContinuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) :
    UniformContinuousOn f s := by
  refine EMetric.uniformContinuousOn_iff.2 fun ε εpos => ?_
  have : Tendsto (fun d : Real>=0∞ => (C : Real>=0∞) * d ^ (r : Real)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top h0
  rcases ENNReal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)) with ⟨δ, δ0, H⟩
  exact ⟨δ, δ0, fun hx y hy h => (hf.edist_le hx hy).trans_lt (H h)⟩

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (hf : HolderOnWith C r f s) (h0 : 0 < r)
  statement: ContinuousOn f s
  proof: (hf.uniformContinuousOn h0).continuousOn

中文:
定理 continuousOn
  条件: (hf : HolderOnWith C r f s) (h0 : 0 < r)
  结论: ContinuousOn f s
  证明: (hf.uniformContinuousOn h0).continuousOn
-/
protected theorem continuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) : ContinuousOn f s :=
  (hf.uniformContinuousOn h0).continuousOn

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hf : HolderOnWith C r f s) (ht : t subseteq s)
  statement: HolderOnWith C r f t
  proof: fun _ hx _ hy => hf.edist_le (ht hx) (ht hy)

中文:
定理 mono
  条件: (hf : HolderOnWith C r f s) (ht : t subseteq s)
  结论: HolderOnWith C r f t
  证明: fun _ hx _ hy => hf.edist_le (ht hx) (ht hy)
-/
protected theorem mono (hf : HolderOnWith C r f s) (ht : t subseteq s) : HolderOnWith C r f t :=
  fun _ hx _ hy => hf.edist_le (ht hx) (ht hy)

/--
theorem `ediam_image_le_of_le` / 定理 `ediam_image_le_of_le`

English:
theorem ediam_image_le_of_le
  given: (hf : HolderOnWith C r f s) {d : Real>=0∞} (hd : ediam s <= d)
  proof: ediam_image_le_iff.2 fun _ hx _ hy =>
hf.edist_le_of_le hx hy (edist_le_ediam_of_mem hx hy).trans hd

中文:
定理 ediam_image_le_of_le
  条件: (hf : HolderOnWith C r f s) {d : 实数>=0∞} (hd : ediam s <= d)
  证明: ediam_image_le_iff.2 fun _ hx _ hy =>
hf.edist_le_of_le hx hy (edist_le_ediam_of_mem hx hy).trans hd

Depends on / 依赖: ediam_image_le_iff, edist_le_ediam_of_mem, edist_le_of_le, hf.edist_le_of_le
-/
theorem ediam_image_le_of_le (hf : HolderOnWith C r f s) {d : Real>=0∞} (hd : ediam s <= d) :
    ediam (f '' s) <= (C : Real>=0∞) * d ^ (r : Real) :=
  ediam_image_le_iff.2 fun _ hx _ hy =>
hf.edist_le_of_le hx hy (edist_le_ediam_of_mem hx hy).trans hd

/--
theorem `ediam_image_le` / 定理 `ediam_image_le`

English:
theorem ediam_image_le
  given: (hf : HolderOnWith C r f s)
  proof: hf.ediam_image_le_of_le le_rfl

中文:
定理 ediam_image_le
  条件: (hf : HolderOnWith C r f s)
  证明: hf.ediam_image_le_of_le le_rfl

Depends on / 依赖: ediam_image_le_of_le, hf.ediam_image_le_of_le, le_rfl
-/
theorem ediam_image_le (hf : HolderOnWith C r f s) :
    ediam (f '' s) <= (C : Real>=0∞) * ediam s ^ (r : Real) :=
  hf.ediam_image_le_of_le le_rfl

/--
theorem `ediam_image_le_of_subset` / 定理 `ediam_image_le_of_subset`

English:
theorem ediam_image_le_of_subset
  given: (hf : HolderOnWith C r f s) (ht : t subseteq s)
  proof: (hf.mono ht).ediam_image_le

中文:
定理 ediam_image_le_of_subset
  条件: (hf : HolderOnWith C r f s) (ht : t subseteq s)
  证明: (hf.mono ht).ediam_image_le

Depends on / 依赖: ediam_image_le, hf.mono
-/
theorem ediam_image_le_of_subset (hf : HolderOnWith C r f s) (ht : t subseteq s) :
    ediam (f '' t) <= (C : Real>=0∞) * ediam t ^ (r : Real) :=
  (hf.mono ht).ediam_image_le

/--
theorem `ediam_image_le_of_subset_of_le` / 定理 `ediam_image_le_of_subset_of_le`

English:
theorem ediam_image_le_of_subset_of_le
  statement: (hf : HolderOnWith C r f s) (ht : t subseteq s) {d : Real>=0∞}
  proof: (hf.mono ht).ediam_image_le_of_le hd

中文:
定理 ediam_image_le_of_subset_of_le
  结论: (hf : HolderOnWith C r f s) (ht : t subseteq s) {d : 实数>=0∞}
  证明: (hf.mono ht).ediam_image_le_of_le hd

Depends on / 依赖: ediam_image_le_of_le, hf.mono
-/
theorem ediam_image_le_of_subset_of_le (hf : HolderOnWith C r f s) (ht : t subseteq s) {d : Real>=0∞}
    (hd : ediam t <= d) : ediam (f '' t) <= (C : Real>=0∞) * d ^ (r : Real) :=
  (hf.mono ht).ediam_image_le_of_le hd

/--
theorem `ediam_image_inter_le_of_le` / 定理 `ediam_image_inter_le_of_le`

English:
theorem ediam_image_inter_le_of_le
  statement: (hf : HolderOnWith C r f s) {d : Real>=0∞}
  proof: hf.ediam_image_le_of_subset_of_le inter_subset_right
    (ediam_mono inter_subset_left).trans hd

中文:
定理 ediam_image_inter_le_of_le
  结论: (hf : HolderOnWith C r f s) {d : 实数>=0∞}
  证明: hf.ediam_image_le_of_subset_of_le inter_subset_right
    (ediam_mono inter_subset_left).trans hd

Depends on / 依赖: ediam_image_le_of_subset_of_le, ediam_mono, hf.ediam_image_le_of_subset_of_le, inter_subset_left, inter_subset_right
-/
theorem ediam_image_inter_le_of_le (hf : HolderOnWith C r f s) {d : Real>=0∞}
    (hd : ediam t <= d) : ediam (f '' (t inter s)) <= (C : Real>=0∞) * d ^ (r : Real) :=
hf.ediam_image_le_of_subset_of_le inter_subset_right
    (ediam_mono inter_subset_left).trans hd

/--
theorem `ediam_image_inter_le` / 定理 `ediam_image_inter_le`

English:
theorem ediam_image_inter_le
  given: (hf : HolderOnWith C r f s) (t : Set X)
  proof: hf.ediam_image_inter_le_of_le le_rfl

中文:
定理 ediam_image_inter_le
  条件: (hf : HolderOnWith C r f s) (t : 集合 X)
  证明: hf.ediam_image_inter_le_of_le le_rfl

Depends on / 依赖: ediam_image_inter_le_of_le, hf.ediam_image_inter_le_of_le, le_rfl
-/
theorem ediam_image_inter_le (hf : HolderOnWith C r f s) (t : Set X) :
    ediam (f '' (t inter s)) <= (C : Real>=0∞) * ediam t ^ (r : Real) :=
  hf.ediam_image_inter_le_of_le le_rfl

/--
lemma `interpolate` / 引理 `interpolate`

English:
lemma interpolate
  statement: {C₁ C₂ s t₁ t₂ : Real>=0} {A : Set X}
  proof: by
  intro x hx y hy
  calc edist (f x) (f y)
      = (edist (f x) (f y)) ^ (t₁ : Real) * (edist (f x) (f y)) ^ (t₂ : Real) := by
        simp [← ENNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]
    _ <= (C₁ * (edist x y) ^ (r : Real)) ^ (t₁ : Real) * (C₂ * (edist x y) ^ (s : Real)) ^ (t₂ : Real) := by
        nth_grw 1 [hf₁ x hx y hy, hf₂ x hx y hy]
    _ = ↑(C₁ ^ (t₁ : Real) * C₂ ^ (t₂ : Real)) * (edist x y) ^ (↑(r * t₁ + s * t₂) : Real) := by
        push_cast
        simp (discharger := positivity) only [ENNReal.mul_rpow_of_nonneg,
          ENNReal.rpow_add_of_nonneg, ENNReal.rpow_mul, ENNReal.coe_rpow_of_nonneg]
        ring

中文:
引理 interpolate
  结论: {C₁ C₂ s t₁ t₂ : 实数>=0} {A : 集合 X}
  证明: by
  intro x hx y hy
  calc edist (f x) (f y)
      = (edist (f x) (f y)) ^ (t₁ : Real) * (edist (f x) (f y)) ^ (t₂ : Real) := by
        simp [← ENNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]
    _ <= (C₁ * (edist x y) ^ (r : Real)) ^ (t₁ : Real) * (C₂ * (edist x y) ^ (s : Real)) ^ (t₂ : Real) := by
        nth_grw 1 [hf₁ x hx y hy, hf₂ x hx y hy]
    _ = ↑(C₁ ^ (t₁ : Real) * C₂ ^ (t₂ : Real)) * (edist x y) ^ (↑(r * t₁ + s * t₂) : Real) := by
        push_cast
        simp (discharger := positivity) only [ENNReal.mul_rpow_of_nonneg,
          ENNReal.rpow_add_of_nonneg, ENNReal.rpow_mul, ENNReal.coe_rpow_of_nonneg]
        ring

Depends on / 依赖: ENNReal, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_add_of_nonneg, NNReal, NNReal.coe_add, coe_add, discharger, mul_rpow_of_nonneg, nth_grw, rpow_add_of_nonneg
-/
lemma interpolate {C₁ C₂ s t₁ t₂ : Real>=0} {A : Set X}
    (hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (ht : t₁ + t₂ = 1) :
    HolderOnWith (C₁ ^ (t₁ : Real) * C₂ ^ (t₂ : Real)) (r * t₁ + s * t₂) f A := by
  intro x hx y hy
  calc edist (f x) (f y)
      = (edist (f x) (f y)) ^ (t₁ : Real) * (edist (f x) (f y)) ^ (t₂ : Real) := by
        simp [← ENNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]
    _ <= (C₁ * (edist x y) ^ (r : Real)) ^ (t₁ : Real) * (C₂ * (edist x y) ^ (s : Real)) ^ (t₂ : Real) := by
        nth_grw 1 [hf₁ x hx y hy, hf₂ x hx y hy]
    _ = ↑(C₁ ^ (t₁ : Real) * C₂ ^ (t₂ : Real)) * (edist x y) ^ (↑(r * t₁ + s * t₂) : Real) := by
        push_cast
        simp (discharger := positivity) only [ENNReal.mul_rpow_of_nonneg,
          ENNReal.rpow_add_of_nonneg, ENNReal.rpow_mul, ENNReal.coe_rpow_of_nonneg]
        ring

/--
lemma `holderOnWith_zero_of_bounded` / 引理 `holderOnWith_zero_of_bounded`

English:
lemma holderOnWith_zero_of_bounded
  statement: {C D : Real>=0} {A : Set X}
  proof: by
  intro x hx y hy
  simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
  grw [hf x hx y hy, hA x hx y hy, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by simp)]

中文:
引理 holderOnWith_zero_of_bounded
  结论: {C D : 实数>=0} {A : 集合 X}
  证明: by
  intro x hx y hy
  simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
  grw [hf x hx y hy, hA x hx y hy, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by simp)]

Depends on / 依赖: ENNReal, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg, ENNReal.rpow_zero, NNReal, NNReal.coe_zero, coe_mul, coe_rpow_of_nonneg, coe_zero, mul_one, rpow_zero
-/
lemma holderOnWith_zero_of_bounded {C D : Real>=0} {A : Set X}
    (hA : forall x in A, forall y in A, edist x y <= D) (hf : HolderOnWith C r f A) :
    HolderOnWith (C * D ^ (r : Real)) 0 f A := by
  intro x hx y hy
  simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
  grw [hf x hx y hy, hA x hx y hy, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by simp)]

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  statement: {C D s : Real>=0} {A : Set X}
  proof: by
  obtain rfl | ht := eq_zero_or_pos s
  · simpa using hf.holderOnWith_zero_of_bounded hA
  have hr : 0 < r := ht.trans_le hsr
  rw [← NNReal.coe_le_coe] at hsr
  rw [← NNReal.coe_pos] at hr
  set θ₁ : Real>=0 := .mk (s / r) (by positivity)
  set θ₂ : Real>=0 := .mk (1 - s / r) (by simpa using div_le_one_of_le₀ hsr (by positivity))
  have hθ : θ₁ + θ₂ = 1 := by ext; simp [θ₁, θ₂]
  have hθt : r * θ₁ + 0 * θ₂ = s := by ext; simp [θ₁, mul_div_cancel₀ _ hr.ne']
  have hθC : C * D ^ (r - s : Real) = C ^ (θ₁ : Real) * (C * D ^ (r : Real)) ^ (θ₂ : Real) := by
    simp (discharger := positivity) only [NNReal.mul_rpow, ← mul_assoc,
      ← NNReal.rpow_add_of_nonneg, ← NNReal.rpow_mul, ← NNReal.coe_add, hθ, NNReal.coe_one,
      NNReal.rpow_one]
    congr
    simp [mul_sub, θ₂, mul_div_cancel₀ _ hr.ne']
  rw [hθC]; rw [← hθt]
  exact hf.interpolate (hf.holderOnWith_zero_of_bounded hA) hθ

中文:
引理 of_le
  结论: {C D s : 实数>=0} {A : 集合 X}
  证明: by
  obtain rfl | ht := eq_zero_or_pos s
  · simpa using hf.holderOnWith_zero_of_bounded hA
  have hr : 0 < r := ht.trans_le hsr
  rw [← NNReal.coe_le_coe] at hsr
  rw [← NNReal.coe_pos] at hr
  set θ₁ : Real>=0 := .mk (s / r) (by positivity)
  set θ₂ : Real>=0 := .mk (1 - s / r) (by simpa using div_le_one_of_le₀ hsr (by positivity))
  have hθ : θ₁ + θ₂ = 1 := by ext; simp [θ₁, θ₂]
  have hθt : r * θ₁ + 0 * θ₂ = s := by ext; simp [θ₁, mul_div_cancel₀ _ hr.ne']
  have hθC : C * D ^ (r - s : Real) = C ^ (θ₁ : Real) * (C * D ^ (r : Real)) ^ (θ₂ : Real) := by
    simp (discharger := positivity) only [NNReal.mul_rpow, ← mul_assoc,
      ← NNReal.rpow_add_of_nonneg, ← NNReal.rpow_mul, ← NNReal.coe_add, hθ, NNReal.coe_one,
      NNReal.rpow_one]
    congr
    simp [mul_sub, θ₂, mul_div_cancel₀ _ hr.ne']
  rw [hθC]; rw [← hθt]
  exact hf.interpolate (hf.holderOnWith_zero_of_bounded hA) hθ

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.coe_pos, coe_le_coe, coe_pos, eq_zero_or_pos, hf.holderOnWith_zero_of_bounded, holderOnWith_zero_of_bounded, hr.ne, ht.trans_le, trans_le
-/
lemma of_le {C D s : Real>=0} {A : Set X}
    (hA : forall x in A, forall y in A, edist x y <= D) (hf : HolderOnWith C r f A) (hsr : s <= r) :
    HolderOnWith (C * D ^ (r - s : Real)) s f A := by
  obtain rfl | ht := eq_zero_or_pos s
  · simpa using hf.holderOnWith_zero_of_bounded hA
  have hr : 0 < r := ht.trans_le hsr
  rw [← NNReal.coe_le_coe] at hsr
  rw [← NNReal.coe_pos] at hr
  set θ₁ : Real>=0 := .mk (s / r) (by positivity)
  set θ₂ : Real>=0 := .mk (1 - s / r) (by simpa using div_le_one_of_le₀ hsr (by positivity))
  have hθ : θ₁ + θ₂ = 1 := by ext; simp [θ₁, θ₂]
  have hθt : r * θ₁ + 0 * θ₂ = s := by ext; simp [θ₁, mul_div_cancel₀ _ hr.ne']
  have hθC : C * D ^ (r - s : Real) = C ^ (θ₁ : Real) * (C * D ^ (r : Real)) ^ (θ₂ : Real) := by
    simp (discharger := positivity) only [NNReal.mul_rpow, ← mul_assoc,
      ← NNReal.rpow_add_of_nonneg, ← NNReal.rpow_mul, ← NNReal.coe_add, hθ, NNReal.coe_one,
      NNReal.rpow_one]
    congr
    simp [mul_sub, θ₂, mul_div_cancel₀ _ hr.ne']
  rw [hθC]; rw [← hθt]
  exact hf.interpolate (hf.holderOnWith_zero_of_bounded hA) hθ

/--
lemma `mono_const` / 引理 `mono_const`

English:
lemma mono_const
  statement: {C₁ C₂ : Real>=0} {A : Set X} (hf : HolderOnWith C₁ r f A)
  proof: by
  intro x hx y hy
  grw [← hC]
  exact hf x hx y hy

中文:
引理 mono_const
  结论: {C₁ C₂ : 实数>=0} {A : 集合 X} (hf : HolderOnWith C₁ r f A)
  证明: by
  intro x hx y hy
  grw [← hC]
  exact hf x hx y hy
-/
lemma mono_const {C₁ C₂ : Real>=0} {A : Set X} (hf : HolderOnWith C₁ r f A)
    (hC : C₁ <= C₂) : HolderOnWith C₂ r f A := by
  intro x hx y hy
  grw [← hC]
  exact hf x hx y hy

/--
lemma `interpolate_const` / 引理 `interpolate_const`

English:
lemma interpolate_const
  statement: {C s t₁ t₂ : Real>=0} {A : Set X}
  proof: by
  convert! hf₁.interpolate hf₂ ht
  simp [← NNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]

中文:
引理 interpolate_const
  结论: {C s t₁ t₂ : 实数>=0} {A : 集合 X}
  证明: by
  convert! hf₁.interpolate hf₂ ht
  simp [← NNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]

Depends on / 依赖: NNReal, NNReal.coe_add, NNReal.rpow_add_of_nonneg, coe_add, convert, interpolate, rpow_add_of_nonneg
-/
lemma interpolate_const {C s t₁ t₂ : Real>=0} {A : Set X}
    (hf₁ : HolderOnWith C r f A) (hf₂ : HolderOnWith C s f A) (ht : t₁ + t₂ = 1) :
    HolderOnWith C (r * t₁ + s * t₂) f A := by
  convert! hf₁.interpolate hf₂ ht
  simp [← NNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]

variable (f) in
/--
lemma `_root_.convex_setOfPred_holderOnWith` / 引理 `_root_.convex_setOfPred_holderOnWith`

English:
lemma _root_.convex_setOfPred_holderOnWith
  given: (C : Real>=0) (A : Set X)
  proof: by
  intro r hr s hs _ _ _ _ ht
  rw [smul_eq_mul]; rw [smul_eq_mul]; rw [← mul_comm r]; rw [← mul_comm s]
  exact hr.interpolate_const hs ht

@[deprecated (since := "2026-07-09")]
alias _root_.convex_setOf_holderOnWith := _root_.convex_setOfPred_holderOnWith

中文:
引理 _root_.convex_setOfPred_holderOnWith
  条件: (C : 实数>=0) (A : 集合 X)
  证明: by
  intro r hr s hs _ _ _ _ ht
  rw [smul_eq_mul]; rw [smul_eq_mul]; rw [← mul_comm r]; rw [← mul_comm s]
  exact hr.interpolate_const hs ht

@[deprecated (since := "2026-07-09")]
alias _root_.convex_setOf_holderOnWith := _root_.convex_setOfPred_holderOnWith

Depends on / 依赖: hr.interpolate_const, interpolate_const, mul_comm, smul_eq_mul
-/
lemma _root_.convex_setOfPred_holderOnWith (C : Real>=0) (A : Set X) :
    Convex Real>=0 {r | HolderOnWith C r f A} := by
  intro r hr s hs _ _ _ _ ht
  rw [smul_eq_mul]; rw [smul_eq_mul]; rw [← mul_comm r]; rw [← mul_comm s]
  exact hr.interpolate_const hs ht

@[deprecated (since := "2026-07-09")]
alias _root_.convex_setOf_holderOnWith := _root_.convex_setOfPred_holderOnWith

/--
lemma `of_le_of_le` / 引理 `of_le_of_le`

English:
lemma of_le_of_le
  statement: {C₁ C₂ s t : Real>=0} {A : Set X}
  proof: by
  replace hf₁ := hf₁.mono_const (le_max_left C₁ C₂)
  replace hf₂ := hf₂.mono_const (le_max_right C₁ C₂)
.segment_subset hf₁ hf₂ exact convex_setOfPred_holderOnWith f (max C₁ C₂) A
    (NNReal.Icc_subset_segment ⟨hrt, hts⟩)

中文:
引理 of_le_of_le
  结论: {C₁ C₂ s t : 实数>=0} {A : 集合 X}
  证明: by
  replace hf₁ := hf₁.mono_const (le_max_left C₁ C₂)
  replace hf₂ := hf₂.mono_const (le_max_right C₁ C₂)
.segment_subset hf₁ hf₂ exact convex_setOfPred_holderOnWith f (max C₁ C₂) A
    (NNReal.Icc_subset_segment ⟨hrt, hts⟩)

Depends on / 依赖: Icc_subset_segment, NNReal, NNReal.Icc_subset_segment, convex_setOfPred_holderOnWith, le_max_left, le_max_right, mono_const, replace, segment_subset
-/
lemma of_le_of_le {C₁ C₂ s t : Real>=0} {A : Set X}
    (hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (hrt : r <= t)
    (hts : t <= s) : HolderOnWith (max C₁ C₂) t f A := by
  replace hf₁ := hf₁.mono_const (le_max_left C₁ C₂)
  replace hf₂ := hf₂.mono_const (le_max_right C₁ C₂)
.segment_subset hf₁ hf₂ exact convex_setOfPred_holderOnWith f (max C₁ C₂) A
    (NNReal.Icc_subset_segment ⟨hrt, hts⟩)

end HolderOnWith

namespace HolderWith

variable {C r : Real>=0} {f : X -> Y}

/--
theorem `restrict_iff` / 定理 `restrict_iff`

English:
theorem restrict_iff
  given: {s : Set X}
  statement: HolderWith C r (s.domRestrict f) ↔ HolderOnWith C r f s
  proof: by
  simp [HolderWith, HolderOnWith]

protected alias ⟨_, _root_.HolderOnWith.holderWith⟩ := restrict_iff

中文:
定理 restrict_iff
  条件: {s : 集合 X}
  结论: HolderWith C r (s.domRestrict f) ↔ HolderOnWith C r f s
  证明: by
  simp [HolderWith, HolderOnWith]

protected alias ⟨_, _root_.HolderOnWith.holderWith⟩ := restrict_iff

Depends on / 依赖: HolderOnWith, HolderWith
-/
theorem restrict_iff {s : Set X} : HolderWith C r (s.domRestrict f) ↔ HolderOnWith C r f s := by
  simp [HolderWith, HolderOnWith]

protected alias ⟨_, _root_.HolderOnWith.holderWith⟩ := restrict_iff

/--
theorem `edist_le` / 定理 `edist_le`

English:
theorem edist_le
  given: (h : HolderWith C r f) (x y : X)
  proof: h x y

中文:
定理 edist_le
  条件: (h : HolderWith C r f) (x y : X)
  证明: h x y
-/
theorem edist_le (h : HolderWith C r f) (x y : X) :
    edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r : Real) :=
  h x y

/--
theorem `edist_le_of_le` / 定理 `edist_le_of_le`

English:
theorem edist_le_of_le
  given: (h : HolderWith C r f) {x y : X} {d : Real>=0∞} (hd : edist x y <= d)
  proof: (h.holderOnWith univ).edist_le_of_le trivial trivial hd

中文:
定理 edist_le_of_le
  条件: (h : HolderWith C r f) {x y : X} {d : 实数>=0∞} (hd : edist x y <= d)
  证明: (h.holderOnWith univ).edist_le_of_le trivial trivial hd

Depends on / 依赖: edist_le_of_le, h.holderOnWith, holderOnWith
-/
theorem edist_le_of_le (h : HolderWith C r f) {x y : X} {d : Real>=0∞} (hd : edist x y <= d) :
    edist (f x) (f y) <= (C : Real>=0∞) * d ^ (r : Real) :=
  (h.holderOnWith univ).edist_le_of_le trivial trivial hd

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {Cg rg : Real>=0} {g : Y -> Z} (hg : HolderWith Cg rg g) {Cf rf : Real>=0} {f : X -> Y}
  proof: (hg.holderOnWith univ).comp_holderWith hf fun _ => trivial

中文:
定理 comp
  结论: {Cg rg : 实数>=0} {g : Y -> Z} (hg : HolderWith Cg rg g) {Cf rf : 实数>=0} {f : X -> Y}
  证明: (hg.holderOnWith univ).comp_holderWith hf fun _ => trivial

Depends on / 依赖: comp_holderWith, hg.holderOnWith, holderOnWith
-/
theorem comp {Cg rg : Real>=0} {g : Y -> Z} (hg : HolderWith Cg rg g) {Cf rf : Real>=0} {f : X -> Y}
    (hf : HolderWith Cf rf f) : HolderWith (Cg * Cf ^ (rg : Real)) (rg * rf) (g ∘ f) :=
  (hg.holderOnWith univ).comp_holderWith hf fun _ => trivial

/--
theorem `comp_holderOnWith` / 定理 `comp_holderOnWith`

English:
theorem comp_holderOnWith
  statement: {Cg rg : Real>=0} {g : Y -> Z} (hg : HolderWith Cg rg g) {Cf rf : Real>=0}
  proof: (hg.holderOnWith univ).comp hf fun _ _ => trivial

中文:
定理 comp_holderOnWith
  结论: {Cg rg : 实数>=0} {g : Y -> Z} (hg : HolderWith Cg rg g) {Cf rf : 实数>=0}
  证明: (hg.holderOnWith univ).comp hf fun _ _ => trivial

Depends on / 依赖: hg.holderOnWith, holderOnWith
-/
theorem comp_holderOnWith {Cg rg : Real>=0} {g : Y -> Z} (hg : HolderWith Cg rg g) {Cf rf : Real>=0}
    {f : X -> Y} {s : Set X} (hf : HolderOnWith Cf rf f s) :
    HolderOnWith (Cg * Cf ^ (rg : Real)) (rg * rf) (g ∘ f) s :=
  (hg.holderOnWith univ).comp hf fun _ _ => trivial

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: (hf : HolderWith C r f) (h0 : 0 < r)
  statement: UniformContinuous f
  proof: uniformContinuousOn_univ.mp (hf.holderOnWith univ).uniformContinuousOn h0

中文:
定理 uniformContinuous
  条件: (hf : HolderWith C r f) (h0 : 0 < r)
  结论: 一致连续 f
  证明: uniformContinuousOn_univ.mp (hf.holderOnWith univ).uniformContinuousOn h0
-/
protected theorem uniformContinuous (hf : HolderWith C r f) (h0 : 0 < r) : UniformContinuous f :=
uniformContinuousOn_univ.mp (hf.holderOnWith univ).uniformContinuousOn h0

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (hf : HolderWith C r f) (h0 : 0 < r)
  statement: Continuous f
  proof: (hf.uniformContinuous h0).continuous

中文:
定理 continuous
  条件: (hf : HolderWith C r f) (h0 : 0 < r)
  结论: 连续 f
  证明: (hf.uniformContinuous h0).continuous
-/
protected theorem continuous (hf : HolderWith C r f) (h0 : 0 < r) : Continuous f :=
  (hf.uniformContinuous h0).continuous

/--
theorem `ediam_image_le` / 定理 `ediam_image_le`

English:
theorem ediam_image_le
  given: (hf : HolderWith C r f) (s : Set X)
  proof: ediam_image_le_iff.2 fun _ hx _ hy => hf.edist_le_of_le edist_le_ediam_of_mem hx hy

中文:
定理 ediam_image_le
  条件: (hf : HolderWith C r f) (s : 集合 X)
  证明: ediam_image_le_iff.2 fun _ hx _ hy => hf.edist_le_of_le edist_le_ediam_of_mem hx hy

Depends on / 依赖: ediam_image_le_iff, edist_le_ediam_of_mem, edist_le_of_le, hf.edist_le_of_le
-/
theorem ediam_image_le (hf : HolderWith C r f) (s : Set X) :
    ediam (f '' s) <= (C : Real>=0∞) * ediam s ^ (r : Real) :=
ediam_image_le_iff.2 fun _ hx _ hy => hf.edist_le_of_le edist_le_ediam_of_mem hx hy

/--
lemma `const` / 引理 `const`

English:
lemma const
  given: {y : Y}
  proof: fun x₁ x₂ => by
  simp only [Function.const_apply, edist_self, zero_le]

中文:
引理 const
  条件: {y : Y}
  证明: fun x₁ x₂ => by
  simp only [Function.const_apply, edist_self, zero_le]

Depends on / 依赖: Function, Function.const_apply, const_apply, edist_self, zero_le
-/
lemma const {y : Y} :
    HolderWith C r (Function.const X y) := fun x₁ x₂ => by
  simp only [Function.const_apply, edist_self, zero_le]

/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  given: [Zero Y]
  statement: HolderWith C r (0 : X -> Y)
  proof: .const

中文:
引理 zero
  条件: [零 Y]
  结论: HolderWith C r (0 : X -> Y)
  证明: .const
-/
lemma zero [Zero Y] : HolderWith C r (0 : X -> Y) := .const

/--
lemma `of_isEmpty` / 引理 `of_isEmpty`

English:
lemma of_isEmpty
  given: [IsEmpty X]
  statement: HolderWith C r f
  proof: isEmptyElim

中文:
引理 of_isEmpty
  条件: [是空 X]
  结论: HolderWith C r f
  证明: isEmptyElim

Depends on / 依赖: isEmptyElim
-/
lemma of_isEmpty [IsEmpty X] : HolderWith C r f := isEmptyElim

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: {C' : Real>=0} (hf : HolderWith C r f) (h : C <= C')
  proof: fun x₁ x₂ => (hf x₁ x₂).trans (by gcongr)

中文:
引理 mono
  条件: {C' : 实数>=0} (hf : HolderWith C r f) (h : C <= C')
  证明: fun x₁ x₂ => (hf x₁ x₂).trans (by gcongr)
-/
lemma mono {C' : Real>=0} (hf : HolderWith C r f) (h : C <= C') :
    HolderWith C' r f :=
  fun x₁ x₂ => (hf x₁ x₂).trans (by gcongr)

/--
lemma `interpolate` / 引理 `interpolate`

English:
lemma interpolate
  statement: {C₁ C₂ s t₁ t₂ : Real>=0}
  proof: holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate (holderOnWith_univ.2 hf₂) ht)

中文:
引理 interpolate
  结论: {C₁ C₂ s t₁ t₂ : 实数>=0}
  证明: holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate (holderOnWith_univ.2 hf₂) ht)

Depends on / 依赖: holderOnWith_univ, interpolate
-/
lemma interpolate {C₁ C₂ s t₁ t₂ : Real>=0}
    (hf₁ : HolderWith C₁ r f) (hf₂ : HolderWith C₂ s f) (ht : t₁ + t₂ = 1) :
    HolderWith (C₁ ^ (t₁ : Real) * C₂ ^ (t₂ : Real)) (r * t₁ + s * t₂) f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate (holderOnWith_univ.2 hf₂) ht)

/--
lemma `holderWith_zero_of_bounded` / 引理 `holderWith_zero_of_bounded`

English:
lemma holderWith_zero_of_bounded
  statement: {C D : Real>=0}
  proof: holderOnWith_univ.1 ((holderOnWith_univ.2 hf).holderOnWith_zero_of_bounded (fun x _ y _ => h x y))

中文:
引理 holderWith_zero_of_bounded
  结论: {C D : 实数>=0}
  证明: holderOnWith_univ.1 ((holderOnWith_univ.2 hf).holderOnWith_zero_of_bounded (fun x _ y _ => h x y))

Depends on / 依赖: holderOnWith_univ, holderOnWith_zero_of_bounded
-/
lemma holderWith_zero_of_bounded {C D : Real>=0}
    (h : forall x y : X, edist x y <= D) (hf : HolderWith C r f) :
    HolderWith (C * D ^ (r : Real)) 0 f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf).holderOnWith_zero_of_bounded (fun x _ y _ => h x y))

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: {C D s : Real>=0} (h : forall x y : X, edist x y <= D) (hf : HolderWith C r f) (hsr : s <= r)
  proof: holderOnWith_univ.1 ((holderOnWith_univ.2 hf).of_le (fun x _ y _ => h x y) hsr)

中文:
引理 of_le
  条件: {C D s : 实数>=0} (h : 对任意 x y : X, edist x y <= D) (hf : HolderWith C r f) (hsr : s <= r)
  证明: holderOnWith_univ.1 ((holderOnWith_univ.2 hf).of_le (fun x _ y _ => h x y) hsr)

Depends on / 依赖: holderOnWith_univ, of_le
-/
lemma of_le {C D s : Real>=0} (h : forall x y : X, edist x y <= D) (hf : HolderWith C r f) (hsr : s <= r) :
    HolderWith (C * D ^ (r - s : Real)) s f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf).of_le (fun x _ y _ => h x y) hsr)

/--
lemma `interpolate_const` / 引理 `interpolate_const`

English:
lemma interpolate_const
  statement: {C s t₁ t₂ : Real>=0}
  proof: holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate_const (holderOnWith_univ.2 hf₂) ht)

中文:
引理 interpolate_const
  结论: {C s t₁ t₂ : 实数>=0}
  证明: holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate_const (holderOnWith_univ.2 hf₂) ht)

Depends on / 依赖: holderOnWith_univ, interpolate_const
-/
lemma interpolate_const {C s t₁ t₂ : Real>=0}
    (hf₁ : HolderWith C r f) (hf₂ : HolderWith C s f) (ht : t₁ + t₂ = 1) :
    HolderWith C (r * t₁ + s * t₂) f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate_const (holderOnWith_univ.2 hf₂) ht)

variable (f) in
/--
lemma `_root_.convex_setOfPred_holderWith` / 引理 `_root_.convex_setOfPred_holderWith`

English:
lemma _root_.convex_setOfPred_holderWith
  given: (C : Real>=0)
  proof: by
  simp_rw [← holderOnWith_univ]
  exact convex_setOfPred_holderOnWith f C _

@[deprecated (since := "2026-07-09")]
alias _root_.convex_setOf_holderWith := _root_.convex_setOfPred_holderWith

中文:
引理 _root_.convex_setOfPred_holderWith
  条件: (C : 实数>=0)
  证明: by
  simp_rw [← holderOnWith_univ]
  exact convex_setOfPred_holderOnWith f C _

@[deprecated (since := "2026-07-09")]
alias _root_.convex_setOf_holderWith := _root_.convex_setOfPred_holderWith

Depends on / 依赖: convex_setOfPred_holderOnWith, holderOnWith_univ, simp_rw
-/
lemma _root_.convex_setOfPred_holderWith (C : Real>=0) :
    Convex Real>=0 {r | HolderWith C r f} := by
  simp_rw [← holderOnWith_univ]
  exact convex_setOfPred_holderOnWith f C _

@[deprecated (since := "2026-07-09")]
alias _root_.convex_setOf_holderWith := _root_.convex_setOfPred_holderWith

/--
lemma `of_le_of_le` / 引理 `of_le_of_le`

English:
lemma of_le_of_le
  statement: {C₁ C₂ s t : Real>=0}
  proof: holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).of_le_of_le (holderOnWith_univ.2 hf₂) hrt hts)

中文:
引理 of_le_of_le
  结论: {C₁ C₂ s t : 实数>=0}
  证明: holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).of_le_of_le (holderOnWith_univ.2 hf₂) hrt hts)

Depends on / 依赖: holderOnWith_univ, of_le_of_le
-/
lemma of_le_of_le {C₁ C₂ s t : Real>=0}
    (hf₁ : HolderWith C₁ r f) (hf₂ : HolderWith C₂ s f) (hrt : r <= t)
    (hts : t <= s) : HolderWith (max C₁ C₂) t f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).of_le_of_le (holderOnWith_univ.2 hf₂) hrt hts)

end HolderWith

end EMetric

section PseudoMetric

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] {C r : Real>=0} {f : X -> Y} {s : Set X} {x y : X}

namespace HolderOnWith

/--
theorem `nndist_le_of_le` / 定理 `nndist_le_of_le`

English:
theorem nndist_le_of_le
  statement: (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
  proof: by
  rw [← ENNReal.coe_le_coe]; rw [← edist_nndist]; rw [ENNReal.coe_mul]; rw [ENNReal.coe_rpow_of_nonneg _ r.coe_nonneg]
  apply hf.edist_le_of_le hx hy
  rwa [edist_nndist, ENNReal.coe_le_coe]

中文:
定理 nndist_le_of_le
  结论: (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
  证明: by
  rw [← ENNReal.coe_le_coe]; rw [← edist_nndist]; rw [ENNReal.coe_mul]; rw [ENNReal.coe_rpow_of_nonneg _ r.coe_nonneg]
  apply hf.edist_le_of_le hx hy
  rwa [edist_nndist, ENNReal.coe_le_coe]

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg, coe_le_coe, coe_mul, coe_nonneg, coe_rpow_of_nonneg, edist_le_of_le, edist_nndist, hf.edist_le_of_le, r.coe_nonneg
-/
theorem nndist_le_of_le (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
    {d : Real>=0} (hd : nndist x y <= d) : nndist (f x) (f y) <= C * d ^ (r : Real) := by
  rw [← ENNReal.coe_le_coe]; rw [← edist_nndist]; rw [ENNReal.coe_mul]; rw [ENNReal.coe_rpow_of_nonneg _ r.coe_nonneg]
  apply hf.edist_le_of_le hx hy
  rwa [edist_nndist, ENNReal.coe_le_coe]

/--
theorem `nndist_le` / 定理 `nndist_le`

English:
theorem nndist_le
  given: (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
  proof: hf.nndist_le_of_le hx hy le_rfl

中文:
定理 nndist_le
  条件: (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
  证明: hf.nndist_le_of_le hx hy le_rfl

Depends on / 依赖: hf.nndist_le_of_le, le_rfl, nndist_le_of_le
-/
theorem nndist_le (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s) :
    nndist (f x) (f y) <= C * nndist x y ^ (r : Real) :=
  hf.nndist_le_of_le hx hy le_rfl

/--
theorem `dist_le_of_le` / 定理 `dist_le_of_le`

English:
theorem dist_le_of_le
  statement: (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
  proof: by
  lift d to Real>=0 using dist_nonneg.trans hd
  rw [dist_nndist] at hd ⊢
  norm_cast at hd ⊢
  exact hf.nndist_le_of_le hx hy hd

中文:
定理 dist_le_of_le
  结论: (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
  证明: by
  lift d to Real>=0 using dist_nonneg.trans hd
  rw [dist_nndist] at hd ⊢
  norm_cast at hd ⊢
  exact hf.nndist_le_of_le hx hy hd

Depends on / 依赖: dist_nndist, dist_nonneg, dist_nonneg.trans, hf.nndist_le_of_le, nndist_le_of_le
-/
theorem dist_le_of_le (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
    {d : Real} (hd : dist x y <= d) : dist (f x) (f y) <= C * d ^ (r : Real) := by
  lift d to Real>=0 using dist_nonneg.trans hd
  rw [dist_nndist] at hd ⊢
  norm_cast at hd ⊢
  exact hf.nndist_le_of_le hx hy hd

/--
theorem `dist_le` / 定理 `dist_le`

English:
theorem dist_le
  given: (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
  proof: hf.dist_le_of_le hx hy le_rfl

中文:
定理 dist_le
  条件: (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s)
  证明: hf.dist_le_of_le hx hy le_rfl

Depends on / 依赖: dist_le_of_le, hf.dist_le_of_le, le_rfl
-/
theorem dist_le (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s) :
    dist (f x) (f y) <= C * dist x y ^ (r : Real) :=
  hf.dist_le_of_le hx hy le_rfl

end HolderOnWith

namespace HolderWith

/--
theorem `nndist_le_of_le` / 定理 `nndist_le_of_le`

English:
theorem nndist_le_of_le
  given: (hf : HolderWith C r f) {x y : X} {d : Real>=0} (hd : nndist x y <= d)
  proof: (hf.holderOnWith univ).nndist_le_of_le (mem_univ x) (mem_univ y) hd

中文:
定理 nndist_le_of_le
  条件: (hf : HolderWith C r f) {x y : X} {d : 实数>=0} (hd : nndist x y <= d)
  证明: (hf.holderOnWith univ).nndist_le_of_le (mem_univ x) (mem_univ y) hd

Depends on / 依赖: hf.holderOnWith, holderOnWith, mem_univ, nndist_le_of_le
-/
theorem nndist_le_of_le (hf : HolderWith C r f) {x y : X} {d : Real>=0} (hd : nndist x y <= d) :
    nndist (f x) (f y) <= C * d ^ (r : Real) :=
  (hf.holderOnWith univ).nndist_le_of_le (mem_univ x) (mem_univ y) hd

/--
theorem `nndist_le` / 定理 `nndist_le`

English:
theorem nndist_le
  given: (hf : HolderWith C r f) (x y : X)
  proof: hf.nndist_le_of_le le_rfl

中文:
定理 nndist_le
  条件: (hf : HolderWith C r f) (x y : X)
  证明: hf.nndist_le_of_le le_rfl

Depends on / 依赖: hf.nndist_le_of_le, le_rfl, nndist_le_of_le
-/
theorem nndist_le (hf : HolderWith C r f) (x y : X) :
    nndist (f x) (f y) <= C * nndist x y ^ (r : Real) :=
  hf.nndist_le_of_le le_rfl

/--
theorem `dist_le_of_le` / 定理 `dist_le_of_le`

English:
theorem dist_le_of_le
  given: (hf : HolderWith C r f) {x y : X} {d : Real} (hd : dist x y <= d)
  proof: (hf.holderOnWith univ).dist_le_of_le (mem_univ x) (mem_univ y) hd

中文:
定理 dist_le_of_le
  条件: (hf : HolderWith C r f) {x y : X} {d : 实数} (hd : dist x y <= d)
  证明: (hf.holderOnWith univ).dist_le_of_le (mem_univ x) (mem_univ y) hd

Depends on / 依赖: dist_le_of_le, hf.holderOnWith, holderOnWith, mem_univ
-/
theorem dist_le_of_le (hf : HolderWith C r f) {x y : X} {d : Real} (hd : dist x y <= d) :
    dist (f x) (f y) <= C * d ^ (r : Real) :=
  (hf.holderOnWith univ).dist_le_of_le (mem_univ x) (mem_univ y) hd

/--
theorem `dist_le` / 定理 `dist_le`

English:
theorem dist_le
  given: (hf : HolderWith C r f) (x y : X)
  statement: dist (f x) (f y) <= C * dist x y ^ (r : Real)
  proof: hf.dist_le_of_le le_rfl

中文:
定理 dist_le
  条件: (hf : HolderWith C r f) (x y : X)
  结论: dist (f x) (f y) <= C * dist x y ^ (r : 实数)
  证明: hf.dist_le_of_le le_rfl

Depends on / 依赖: dist_le_of_le, hf.dist_le_of_le, le_rfl
-/
theorem dist_le (hf : HolderWith C r f) (x y : X) : dist (f x) (f y) <= C * dist x y ^ (r : Real) :=
  hf.dist_le_of_le le_rfl

end HolderWith

end PseudoMetric

section Metric

variable [PseudoMetricSpace X] [MetricSpace Y] {r : Real>=0} {f : X -> Y}

@[simp]
/--
lemma `holderWith_zero_iff` / 引理 `holderWith_zero_iff`

English:
lemma holderWith_zero_iff
  statement: HolderWith 0 r f ↔ forall x₁ x₂, f x₁ = f x₂
  proof: by
  refine ⟨fun h x₁ x₂ => ?_, fun h x₁ x₂ => h x₁ x₂ ▸ ?_⟩
  · specialize h x₁ x₂
    simp [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] at h
    assumption
  · simp only [edist_self, ENNReal.coe_zero, zero_mul, le_refl]

中文:
引理 holderWith_zero_iff
  结论: HolderWith 0 r f ↔ 对任意 x₁ x₂, f x₁ = f x₂
  证明: by
  refine ⟨fun h x₁ x₂ => ?_, fun h x₁ x₂ => h x₁ x₂ ▸ ?_⟩
  · specialize h x₁ x₂
    simp [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] at h
    assumption
  · simp only [edist_self, ENNReal.coe_zero, zero_mul, le_refl]

Depends on / 依赖: ENNReal, ENNReal.coe_zero, coe_zero, edist_eq_zero, edist_self, le_refl, nonpos_iff_eq_zero, specialize, zero_mul
-/
lemma holderWith_zero_iff : HolderWith 0 r f ↔ forall x₁ x₂, f x₁ = f x₂ := by
  refine ⟨fun h x₁ x₂ => ?_, fun h x₁ x₂ => h x₁ x₂ ▸ ?_⟩
  · specialize h x₁ x₂
    simp [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] at h
    assumption
  · simp only [edist_self, ENNReal.coe_zero, zero_mul, le_refl]

end Metric

section SeminormedAddCommGroup

variable [PseudoMetricSpace X] [SeminormedAddCommGroup Y] {C C' r : Real>=0} {f g : X -> Y}

namespace HolderWith

/--
lemma `add` / 引理 `add`

English:
lemma add
  given: (hf : HolderWith C r f) (hg : HolderWith C' r g)
  proof: by
  intro x₁ x₂
  simp only [Pi.add_apply, ENNReal.coe_add]
  grw [edist_add_add_le, hf x₁ x₂, hg x₁ x₂]
  rw [add_mul]

中文:
引理 add
  条件: (hf : HolderWith C r f) (hg : HolderWith C' r g)
  证明: by
  intro x₁ x₂
  simp only [Pi.add_apply, ENNReal.coe_add]
  grw [edist_add_add_le, hf x₁ x₂, hg x₁ x₂]
  rw [add_mul]

Depends on / 依赖: ENNReal, ENNReal.coe_add, Pi.add_apply, add_apply, add_mul, coe_add, edist_add_add_le
-/
lemma add (hf : HolderWith C r f) (hg : HolderWith C' r g) :
    HolderWith (C + C') r (f + g) := by
  intro x₁ x₂
  simp only [Pi.add_apply, ENNReal.coe_add]
  grw [edist_add_add_le, hf x₁ x₂, hg x₁ x₂]
  rw [add_mul]

/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  statement: {α} [SeminormedAddCommGroup α] [SMulZeroClass α Y] [IsBoundedSMul α Y] (a : α)
  proof: fun x₁ x₂ => by
.trans ?_ refine edist_smul_le _ _ _
  rw [ENNReal.coe_mul]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [mul_comm (C : Real>=0∞)]; rw [mul_assoc]
  gcongr
  exact hf x₁ x₂

中文:
引理 smul
  结论: {α} [SeminormedAddComm群 α] [SMulZero类 α Y] [是BoundedSMul α Y] (a : α)
  证明: fun x₁ x₂ => by
.trans ?_ refine edist_smul_le _ _ _
  rw [ENNReal.coe_mul]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [mul_comm (C : Real>=0∞)]; rw [mul_assoc]
  gcongr
  exact hf x₁ x₂

Depends on / 依赖: ENNReal, ENNReal.coe_mul, ENNReal.smul_def, coe_mul, edist_smul_le, mul_assoc, mul_comm, smul_def, smul_eq_mul
-/
lemma smul {α} [SeminormedAddCommGroup α] [SMulZeroClass α Y] [IsBoundedSMul α Y] (a : α)
    (hf : HolderWith C r f) : HolderWith (C * ‖a‖₊) r (a • f) := fun x₁ x₂ => by
.trans ?_ refine edist_smul_le _ _ _
  rw [ENNReal.coe_mul]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [mul_comm (C : Real>=0∞)]; rw [mul_assoc]
  gcongr
  exact hf x₁ x₂

/--
lemma `smul_iff` / 引理 `smul_iff`

English:
lemma smul_iff
  statement: {α} [SeminormedRing α] [Module α Y] [NormSMulClass α Y] (a : α)
  proof: by
  simp_rw [HolderWith, ENNReal.coe_mul, Pi.smul_apply, edist_smul₀, ENNReal.smul_def, smul_eq_mul,
    mul_comm (C : Real>=0∞), mul_assoc,
    ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr ha) ENNReal.coe_ne_top, mul_comm]

中文:
引理 smul_iff
  结论: {α} [Seminormed环 α] [模 α Y] [NormSMul类 α Y] (a : α)
  证明: by
  simp_rw [HolderWith, ENNReal.coe_mul, Pi.smul_apply, edist_smul₀, ENNReal.smul_def, smul_eq_mul,
    mul_comm (C : Real>=0∞), mul_assoc,
    ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr ha) ENNReal.coe_ne_top, mul_comm]

Depends on / 依赖: ENNReal, ENNReal.coe_mul, ENNReal.coe_ne_top, ENNReal.coe_ne_zero.mpr, ENNReal.mul_le_mul_iff_right, ENNReal.smul_def, HolderWith, Pi.smul_apply, coe_mul, coe_ne_top, coe_ne_zero, mul_assoc, mul_comm, mul_le_mul_iff_right, simp_rw, smul_apply, smul_def, smul_eq_mul
-/
lemma smul_iff {α} [SeminormedRing α] [Module α Y] [NormSMulClass α Y] (a : α)
    (ha : ‖a‖₊ != 0) :
    HolderWith (C * ‖a‖₊) r (a • f) ↔ HolderWith C r f := by
  simp_rw [HolderWith, ENNReal.coe_mul, Pi.smul_apply, edist_smul₀, ENNReal.smul_def, smul_eq_mul,
    mul_comm (C : Real>=0∞), mul_assoc,
    ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr ha) ENNReal.coe_ne_top, mul_comm]

end HolderWith

end SeminormedAddCommGroup
