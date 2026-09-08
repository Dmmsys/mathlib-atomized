/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Hausdorff dimension

The Hausdorff dimension of a set `X` in an (extended) metric space is the unique number
`dimH s : ℝ≥0∞` such that for any `d : ℝ≥0` we have

- `μH[d] s = 0` if `dimH s < d`, and
- `μH[d] s = ∞` if `d < dimH s`.

In this file we define `dimH s` to be the Hausdorff dimension of `s`, then prove some basic
properties of Hausdorff dimension.

## Main definitions

* `MeasureTheory.dimH`: the Hausdorff dimension of a set. For the Hausdorff dimension of the whole
  space we use `MeasureTheory.dimH (Set.univ : Set X)`.

## Main results

### Basic properties of Hausdorff dimension

* `hausdorffMeasure_of_lt_dimH`, `dimH_le_of_hausdorffMeasure_ne_top`,
  `le_dimH_of_hausdorffMeasure_eq_top`, `hausdorffMeasure_of_dimH_lt`, `measure_zero_of_dimH_lt`,
  `le_dimH_of_hausdorffMeasure_ne_zero`, `dimH_of_hausdorffMeasure_ne_zero_ne_top`: various forms
  of the characteristic property of the Hausdorff dimension;
* `dimH_union`: the Hausdorff dimension of the union of two sets is the maximum of their Hausdorff
  dimensions.
* `dimH_iUnion`, `dimH_bUnion`, `dimH_sUnion`: the Hausdorff dimension of a countable union of sets
  is the supremum of their Hausdorff dimensions;
* `dimH_empty`, `dimH_singleton`, `Set.Subsingleton.dimH_zero`, `Set.Countable.dimH_zero` : `dimH s
  = 0` whenever `s` is countable;

### (Pre)images under (anti)lipschitz and Hölder continuous maps

* `HolderWith.dimH_image_le` etc: if `f : X → Y` is Hölder continuous with exponent `r > 0`, then
  for any `s`, `dimH (f '' s) ≤ dimH s / r`. We prove versions of this statement for `HolderWith`,
  `HolderOnWith`, and locally Hölder maps, as well as for `Set.image` and `Set.range`.
* `LipschitzWith.dimH_image_le` etc: Lipschitz continuous maps do not increase the Hausdorff
  dimension of sets.
* for a map that is known to be both Lipschitz and antilipschitz (e.g., for an `Isometry` or
  a `ContinuousLinearEquiv`) we also prove `dimH (f '' s) = dimH s`.

### Hausdorff measure in `ℝⁿ`

* `Real.dimH_of_nonempty_interior`: if `s` is a set in a finite-dimensional real vector space `E`
  with nonempty interior, then the Hausdorff dimension of `s` is equal to the dimension of `E`.
* `dense_compl_of_dimH_lt_finrank`: if `s` is a set in a finite-dimensional real vector space `E`
  with Hausdorff dimension strictly less than the dimension of `E`, the `s` has a dense complement.
* `ContDiff.dense_compl_range_of_finrank_lt_finrank`: the complement to the range of a `C¹`
  smooth map is dense provided that the dimension of the domain is strictly less than the dimension
  of the codomain.

## Notation

We use the following notation localized in `MeasureTheory`. It is defined in
`MeasureTheory.Measure.Hausdorff`.

- `μH[d]` : `MeasureTheory.Measure.hausdorffMeasure d`

## Implementation notes

* The definition of `dimH` explicitly uses `borel X` as a measurable space structure. This way we
  can formulate lemmas about Hausdorff dimension without assuming that the environment has a
  `[MeasurableSpace X]` instance that is equal but possibly not defeq to `borel X`.

  Lemma `dimH_def` unfolds this definition using whatever `[MeasurableSpace X]` instance we have in
  the environment (as long as it is equal to `borel X`).

* The definition `dimH` is irreducible; use API lemmas or `dimH_def` instead.

## Tags

Hausdorff measure, Hausdorff dimension, dimension
-/

@[expose] public section


open scoped MeasureTheory ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace Module Filter

variable {ι X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

/-- Hausdorff dimension of a set in an (e)metric space. -/
/-
**dimH** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{X : Type u_2} → [EMetricSpace X] → Set X → ENNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Hausdorff dimension of a set in an (e)metric space.
-/
@[irreducible] noncomputable def dimH (s : Set X) : ℝ≥0∞ := by
  borelize X; exact ⨆ (d : ℝ≥0) (_ : @hausdorffMeasure X _ _ ⟨rfl⟩ d s = ∞), d

/-!
### Basic properties
-/


section Measurable

variable [MeasurableSpace X] [BorelSpace X]

/-- Unfold the definition of `dimH` using `[MeasurableSpace X] [BorelSpace X]` from the
environment. -/
/-
**dimH_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_def (s : Set X) : dimH s = ⨆ (d : Real>=0) (_ : μH[d] s = ∞), (d : Re
al>=0∞)
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dimH.eq_1`：∀ {X : Type u_2} [inst : EMetricSpace X] (s : Set X),   dimH 
s = ⨆ d, ⨆ (_ : (MeasureTheory.Measure.hausdorffMeasure ↑d) s = ⊤), ↑d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Unfold the definition of `dimH` using `[MeasurableSpace X] [BorelSpace X]` from 
the
environment.
-/
theorem dimH_def (s : Set X) : dimH s = ⨆ (d : ℝ≥0) (_ : μH[d] s = ∞), (d : ℝ≥0∞) := by
  borelize X; rw [dimH]
/-
**hausdorffMeasure_of_lt_dimH** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hausdorffMeasure_of_lt_dimH {s : Set X} {d : Real>=0} (h : ↑d < dimH s) : 
μH[d] s = ∞
参数：h : ↑d < dimH s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dimH_def`：dimH_def (s : Set X) : dimH s = ⨆ (d : Real>=0) (_ : μH[d] s =
 ∞), (d : Real>=0∞)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_mono`：hausdorffMeasure_mono {d₁ d
₂ : Real} (h : d₁ <= d₂) (s : Set X) : μH[d₂] s <= μH[d₁] s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
-/
theorem hausdorffMeasure_of_lt_dimH {s : Set X} {d : ℝ≥0} (h : ↑d < dimH s) : μH[d] s = ∞ := by
  simp only [dimH_def, lt_iSup_iff] at h
  rcases h with ⟨d', hsd', hdd'⟩
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hdd'
  exact top_unique (hsd' ▸ hausdorffMeasure_mono hdd'.le _)
/-
**dimH_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_le {s : Set X} {d : Real>=0∞} (H : forall d' : Real>=0, μH[d'] s = ∞ 
-> ↑d' <= d) : dimH s <= d
参数：H : forall d' : Real>=0, μH[d'] s = ∞ -> ↑d' <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `dimH_def`：dimH_def (s : Set X) : dimH s = ⨆ (d : Real>=0) (_ : μH[d] s =
 ∞), (d : Real>=0∞)
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
-/
theorem dimH_le {s : Set X} {d : ℝ≥0∞} (H : ∀ d' : ℝ≥0, μH[d'] s = ∞ → ↑d' ≤ d) : dimH s ≤ d :=
  (dimH_def s).trans_le <| iSup₂_le H
/-
**dimH_le_of_hausdorffMeasure_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_le_of_hausdorffMeasure_ne_top {s : Set X} {d : Real>=0} (h : μH[d] s 
!= ∞) : dimH s <= d
参数：h : μH[d] s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `hausdorffMeasure_of_lt_dimH`：hausdorffMeasure_of_lt_dimH {s : Set X} {d 
: Real>=0} (h : ↑d < dimH s) : μH[d] s = ∞
-/
theorem dimH_le_of_hausdorffMeasure_ne_top {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ ∞) : dimH s ≤ d :=
  le_of_not_gt <| mt hausdorffMeasure_of_lt_dimH h
/-
**le_dimH_of_hausdorffMeasure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_dimH_of_hausdorffMeasure_eq_top {s : Set X} {d : Real>=0} (h : μH[d] s 
= ∞) : ↑d <= dimH s
参数：h : μH[d] s = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dimH_def`：dimH_def (s : Set X) : dimH s = ⨆ (d : Real>=0) (_ : μH[d] s =
 ∞), (d : Real>=0∞)
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
theorem le_dimH_of_hausdorffMeasure_eq_top {s : Set X} {d : ℝ≥0} (h : μH[d] s = ∞) :
    ↑d ≤ dimH s := by
  rw [dimH_def]; exact le_iSup₂ (α := ℝ≥0∞) d h
/-
**hausdorffMeasure_of_dimH_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hausdorffMeasure_of_dimH_lt {s : Set X} {d : Real>=0} (h : dimH s < d) : μ
H[d] s = 0
参数：h : dimH s < d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dimH_def`：dimH_def (s : Set X) : dimH s = ⨆ (d : Real>=0) (_ : μH[d] s =
 ∞), (d : Real>=0∞)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_zero_or_top`：hausdorffMeasure_zer
o_or_top {d₁ d₂ : Real} (h : d₁ < d₂) (s : Set X) : μH[d₂] s = 0 ∨ μH[d₁] s = ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
theorem hausdorffMeasure_of_dimH_lt {s : Set X} {d : ℝ≥0} (h : dimH s < d) : μH[d] s = 0 := by
  rw [dimH_def] at h
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hsd', hd'd⟩
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hd'd
  exact (hausdorffMeasure_zero_or_top hd'd s).resolve_right fun h₂ => hsd'.not_ge <|
    le_iSup₂ (α := ℝ≥0∞) d' h₂
/-
**measure_zero_of_dimH_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measure_zero_of_dimH_lt {μ : Measure X} {d : Real>=0} (h : μ ≪ μH[d]) {s :
 Set X} (hd : dimH s < d) : μ s = 0
参数：h : μ ≪ μH[d]；hd : dimH s < d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hausdorffMeasure_of_dimH_lt`：hausdorffMeasure_of_dimH_lt {s : Set X} {d 
: Real>=0} (h : dimH s < d) : μH[d] s = 0
-/
theorem measure_zero_of_dimH_lt {μ : Measure X} {d : ℝ≥0} (h : μ ≪ μH[d]) {s : Set X}
    (hd : dimH s < d) : μ s = 0 :=
  h <| hausdorffMeasure_of_dimH_lt hd
/-
**le_dimH_of_hausdorffMeasure_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_dimH_of_hausdorffMeasure_ne_zero {s : Set X} {d : Real>=0} (h : μH[d] s
 != 0) : ↑d <= dimH s
参数：h : μH[d] s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `hausdorffMeasure_of_dimH_lt`：hausdorffMeasure_of_dimH_lt {s : Set X} {d 
: Real>=0} (h : dimH s < d) : μH[d] s = 0
-/
theorem le_dimH_of_hausdorffMeasure_ne_zero {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ 0) : ↑d ≤ dimH s :=
  le_of_not_gt <| mt hausdorffMeasure_of_dimH_lt h
/-
**dimH_of_hausdorffMeasure_ne_zero_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_of_hausdorffMeasure_ne_zero_ne_top {d : Real>=0} {s : Set X} (h : μH[
d] s != 0) (h' : μH[d] s != ∞) : dimH s = d
参数：h : μH[d] s != 0；h' : μH[d] s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `dimH_le_of_hausdorffMeasure_ne_top`：dimH_le_of_hausdorffMeasure_ne_top {
s : Set X} {d : Real>=0} (h : μH[d] s != ∞) : dimH s <= d
· 使用定理 `le_dimH_of_hausdorffMeasure_ne_zero`：le_dimH_of_hausdorffMeasure_ne_zero
 {s : Set X} {d : Real>=0} (h : μH[d] s != 0) : ↑d <= dimH s
-/
theorem dimH_of_hausdorffMeasure_ne_zero_ne_top {d : ℝ≥0} {s : Set X} (h : μH[d] s ≠ 0)
    (h' : μH[d] s ≠ ∞) : dimH s = d :=
  le_antisymm (dimH_le_of_hausdorffMeasure_ne_top h') (le_dimH_of_hausdorffMeasure_ne_zero h)

/-- The Hausdorff dimension of a set `s` is the infimum of all `d : ℝ≥0` such that the
`d`-dimensional Hausdorff measure of `s` is zero. This infimum is taken in `ℝ≥0∞`.
This gives an equivalent definition of the Hausdorff dimension. -/
/-
**dimH_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_eq_iInf (s : Set X) : dimH s = ⨅ (d : Real>=0) (_ : μH[d] s = 0), (d 
: Real>=0∞)
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dimH_def`：dimH_def (s : Set X) : dimH s = ⨆ (d : Real>=0) (_ : μH[d] s =
 ∞), (d : Real>=0∞)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_mono`：hausdorffMeasure_mono {d₁ d
₂ : Real} (h : d₁ <= d₂) (s : Set X) : μH[d₂] s <= μH[d₁] s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `hausdorffMeasure_of_dimH_lt`：hausdorffMeasure_of_dimH_lt {s : Set X} {d 
: Real>=0} (h : dimH s < d) : μH[d] s = 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…

--- 原说明 ---
The Hausdorff dimension of a set `s` is the infimum of all `d : ℝ≥0` such that t
he
`d`-dimensional Hausdorff measure of `s` is zero. This infimum is taken in `ℝ≥0∞
`.
This gives an equivalent definition of the Hausdorff dimension.
-/
theorem dimH_eq_iInf (s : Set X) : dimH s = ⨅ (d : ℝ≥0) (_ : μH[d] s = 0), (d : ℝ≥0∞) := by
  apply le_antisymm
  · rw [dimH_def]
    simp only [le_iInf_iff, iSup_le_iff, ENNReal.coe_le_coe]
    intro i hi j hj
    by_contra! hij
    simpa [hi, hj] using hausdorffMeasure_mono hij.le s
  · by_contra! h
    rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hdim_lt, hlt⟩
    have h0 : μH[d'] s = 0 := hausdorffMeasure_of_dimH_lt hdim_lt
    exact hlt.not_ge (iInf₂_le d' h0)

end Measurable

@[gcongr, mono]
/-
**dimH_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dimH_le`：dimH_le {s : Set X} {d : Real>=0∞} (H : forall d' : Real>=0, μH
[d'] s = ∞ -> ↑d' <= d) : dimH s <= d
· 使用定理 `le_dimH_of_hausdorffMeasure_eq_top`：le_dimH_of_hausdorffMeasure_eq_top {
s : Set X} {d : Real>=0} (h : μH[d] s = ∞) : ↑d <= dimH s
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem dimH_mono {s t : Set X} (h : s ⊆ t) : dimH s ≤ dimH t := by
  borelize X
  exact dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top <| top_unique <| hd ▸ measure_mono h
/-
**dimH_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_subsingleton {s : Set X} (h : s.Subsingleton) : dimH s = 0
参数：h : s.Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `dimH_le_of_hausdorffMeasure_ne_top`：dimH_le_of_hausdorffMeasure_ne_top {
s : Set X} {d : Real>=0} (h : μH[d] s != ∞) : dimH s <= d
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_le_one_of_subsingleton`：hausdorff
Measure_le_one_of_subsingleton {s : Set X} (hs : s.Subsingleton) {d : Real} (hd 
: 0 <= d) : μH[d] s <= 1
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
-/
theorem dimH_subsingleton {s : Set X} (h : s.Subsingleton) : dimH s = 0 := by
  borelize X
  rw [← nonpos_iff_eq_zero]
  apply dimH_le_of_hausdorffMeasure_ne_top
  exact ((hausdorffMeasure_le_one_of_subsingleton h le_rfl).trans_lt ENNReal.one_lt_top).ne

alias Set.Subsingleton.dimH_zero := dimH_subsingleton

@[simp]
/-
**dimH_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_empty : dimH (∅ : Set X) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.dimH_zero`：∀ {X : Type u_2} [inst : EMetricSpace X] {s 
: Set X}, s.Subsingleton → dimH s = 0
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
-/
theorem dimH_empty : dimH (∅ : Set X) = 0 :=
  subsingleton_empty.dimH_zero

@[simp]
/-
**dimH_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_singleton (x : X) : dimH ({x} : Set X) = 0
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.dimH_zero`：∀ {X : Type u_2} [inst : EMetricSpace X] {s 
: Set X}, s.Subsingleton → dimH s = 0
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem dimH_singleton (x : X) : dimH ({x} : Set X) = 0 :=
  subsingleton_singleton.dimH_zero

@[simp]
/-
**dimH_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_iUnion {ι : Sort*} [Countable ι] (s : ι -> Set X) : dimH (⋃ i, s i) =
 ⨆ i, dimH (s i)
参数：s : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `dimH_le`：dimH_le {s : Set X} {d : Real>=0∞} (H : forall d' : Real>=0, μH
[d'] s = ∞ -> ↑d' <= d) : dimH s <= d
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `hausdorffMeasure_of_dimH_lt`：hausdorffMeasure_of_dimH_lt {s : Set X} {d 
: Real>=0} (h : dimH s < d) : μH[d] s = 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_iUnion_null`：∀ {α : Type u_1} {F : Type u_3} [inst
 : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F}   {ι
 : Sort u_4} [Countable…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `dimH_mono`：dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
theorem dimH_iUnion {ι : Sort*} [Countable ι] (s : ι → Set X) :
    dimH (⋃ i, s i) = ⨆ i, dimH (s i) := by
  borelize X
  refine le_antisymm (dimH_le fun d hd => ?_) (iSup_le fun i => dimH_mono <| subset_iUnion _ _)
  contrapose! hd
  have : ∀ i, μH[d] (s i) = 0 := fun i =>
    hausdorffMeasure_of_dimH_lt ((le_iSup (fun i => dimH (s i)) i).trans_lt hd)
  rw [measure_iUnion_null this]
  exact ENNReal.zero_ne_top

@[simp]
/-
**dimH_bUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι -> Set X) : dimH (⋃ i in
 s, t i) = ⨆ i in s, dimH (t i)
参数：hs : s.Countable；t : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `dimH_iUnion`：dimH_iUnion {ι : Sort*} [Countable ι] (s : ι -> Set X) : di
mH (⋃ i, s i) = ⨆ i, dimH (s i)
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
-/
theorem dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι → Set X) :
    dimH (⋃ i ∈ s, t i) = ⨆ i ∈ s, dimH (t i) := by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion, dimH_iUnion, ← iSup_subtype'']

@[simp]
/-
**dimH_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_sUnion {S : Set (Set X)} (hS : S.Countable) : dimH (⋃₀ S) = ⨆ s in S,
 dimH s
参数：Set X；hS : S.Countable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `dimH_bUnion`：dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι -> Set X)
 : dimH (⋃ i in s, t i) = ⨆ i in s, dimH (t i)
-/
theorem dimH_sUnion {S : Set (Set X)} (hS : S.Countable) : dimH (⋃₀ S) = ⨆ s ∈ S, dimH s := by
  rw [sUnion_eq_biUnion, dimH_bUnion hS]

@[simp]
/-
**dimH_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_union (s t : Set X) : dimH (s union t) = max (dimH s) (dimH t)
参数：s t : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `dimH_iUnion`：dimH_iUnion {ι : Sort*} [Countable ι] (s : ι -> Set X) : di
mH (⋃ i, s i) = ⨆ i, dimH (s i)
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
· 使用定理 `cond.eq_1`：∀ {α : Sort u} (x y : α), (bif true then x else y) = x
· 使用定理 `cond.eq_2`：∀ {α : Sort u} (x y : α), (bif false then x else y) = y
-/
theorem dimH_union (s t : Set X) : dimH (s ∪ t) = max (dimH s) (dimH t) := by
  rw [union_eq_iUnion, dimH_iUnion, iSup_bool_eq, cond, cond]
/-
**dimH_countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_countable {s : Set X} (hs : s.Countable) : dimH s = 0
参数：hs : s.Countable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dimH_bUnion`：dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι -> Set X)
 : dimH (⋃ i in s, t i) = ⨆ i in s, dimH (t i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `dimH_singleton`：dimH_singleton (x : X) : dimH ({x} : Set X) = 0
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
-/
theorem dimH_countable {s : Set X} (hs : s.Countable) : dimH s = 0 :=
  biUnion_of_singleton s ▸ by simp only [dimH_bUnion hs, dimH_singleton, ENNReal.iSup_zero]

alias Set.Countable.dimH_zero := dimH_countable
/-
**dimH_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_finite {s : Set X} (hs : s.Finite) : dimH s = 0
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.dimH_zero`：∀ {X : Type u_2} [inst : EMetricSpace X] {s : S
et X}, s.Countable → dimH s = 0
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
-/
theorem dimH_finite {s : Set X} (hs : s.Finite) : dimH s = 0 :=
  hs.countable.dimH_zero

alias Set.Finite.dimH_zero := dimH_finite

@[simp]
/-
**dimH_coe_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_coe_finset (s : Finset X) : dimH (s : Set X) = 0
参数：s : Finset X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.dimH_zero`：∀ {X : Type u_2} [inst : EMetricSpace X] {s : Set 
X}, s.Finite → dimH s = 0
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem dimH_coe_finset (s : Finset X) : dimH (s : Set X) = 0 :=
  s.finite_toSet.dimH_zero

alias Finset.dimH_zero := dimH_coe_finset

/-!
### Hausdorff dimension as the supremum of local Hausdorff dimensions
-/


section

variable [SecondCountableTopology X]

/-- If `r` is less than the Hausdorff dimension of a set `s` in an (extended) metric space with
second countable topology, then there exists a point `x ∈ s` such that every neighborhood
`t` of `x` within `s` has Hausdorff dimension greater than `r`. -/
/-
**exists_mem_nhdsWithin_lt_dimH_of_lt_dimH** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_nhdsWithin_lt_dimH_of_lt_dimH {s : Set X} {r : Real>=0∞} (h : r
 < dimH s) : exists x in s, forall t in 𝓝[s] x, r < dimH t
参数：h : r < dimH s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalSpace.countable_cover_nhdsWithin`：countable_cover_nhdsWithin 
[SecondCountableTopology α] {f : α -> Set α} {s : Set α} (hf : forall x in s, f 
x in 𝓝[s] x) : exists t subseteq …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `dimH_mono`：dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t
· 使用定理 `dimH_bUnion`：dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι -> Set X)
 : dimH (⋃ i in s, t i) = ⨆ i in s, dimH (t i)
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `r` is less than the Hausdorff dimension of a set `s` in an (extended) metric
 space with
second countable topology, then there exists a point `x ∈ s` such that every nei
ghborhood
`t` of `x` within `s` has Hausdorff dimension greater than `r`.
-/
theorem exists_mem_nhdsWithin_lt_dimH_of_lt_dimH {s : Set X} {r : ℝ≥0∞} (h : r < dimH s) :
    ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, r < dimH t := by
  contrapose! h; choose! t htx htr using h
  rcases countable_cover_nhdsWithin htx with ⟨S, hSs, hSc, hSU⟩
  calc
    dimH s ≤ dimH (⋃ x ∈ S, t x) := dimH_mono hSU
    _ = ⨆ x ∈ S, dimH (t x) := dimH_bUnion hSc _
    _ ≤ r := iSup₂_le fun x hx => htr x <| hSs hx

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over `x ∈ s` of the limit superiors of `dimH t` along
`(𝓝[s] x).smallSets`. -/
/-
**bsupr_limsup_dimH** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bsupr_limsup_dimH (s : Set X) : ⨆ x in s, limsup dimH (𝓝[s] x).smallSets =
 dimH s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Filter.limsup_le_of_le`：limsup_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_smallSets`：eventually_smallSets {p : Set α -> Prop} : 
(forallᶠ s in l.smallSets, p s) ↔ exists s in l, forall t, t subseteq s -> p t
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `dimH_mono`：dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t
· 使用定理 `le_of_forall_lt_imp_le_of_dense`：∀ {α : Type u_2} [inst : LinearOrder α]
 [DenselyOrdered α] {a₁ a₂ : α}, (∀ a < a₂, a ≤ a₁) → a₂ ≤ a₁
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `exists_mem_nhdsWithin_lt_dimH_of_lt_dimH`：exists_mem_nhdsWithin_lt_dimH_
of_lt_dimH {s : Set X} {r : Real>=0∞} (h : r < dimH s) : exists x in s, forall t
 in 𝓝[s] x, r < dimH t
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_eq`：limsup_eq : limsup u f = sInf { a | forallᶠ n in f, u 
n <= a }
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
In an (extended) metric space with second countable topology, the Hausdorff dime
nsion
of a set `s` is the supremum over `x ∈ s` of the limit superiors of `dimH t` alo
ng
`(𝓝[s] x).smallSets`.
-/
theorem bsupr_limsup_dimH (s : Set X) : ⨆ x ∈ s, limsup dimH (𝓝[s] x).smallSets = dimH s := by
  refine le_antisymm (iSup₂_le fun x _ => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hr with ⟨x, hxs, hxr⟩
    refine le_iSup₂_of_le x hxs ?_; rw [limsup_eq]; refine le_sInf fun b hb => ?_
    rcases eventually_smallSets.1 hb with ⟨t, htx, ht⟩
    exact (hxr t htx).le.trans (ht t Subset.rfl)

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over all `x` of the limit superiors of `dimH t` along
`(𝓝[s] x).smallSets`. -/
/-
**iSup_limsup_dimH** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_limsup_dimH (s : Set X) : ⨆ x, limsup dimH (𝓝[s] x).smallSets = dimH 
s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Filter.limsup_le_of_le`：limsup_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_smallSets`：eventually_smallSets {p : Set α -> Prop} : 
(forallᶠ s in l.smallSets, p s) ↔ exists s in l, forall t, t subseteq s -> p t
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `dimH_mono`：dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bsupr_limsup_dimH`：bsupr_limsup_dimH (s : Set X) : ⨆ x in s, limsup dimH
 (𝓝[s] x).smallSets = dimH s
· 使用定理 `iSup₂_le_iSup`：iSup₂_le_iSup (κ : ι -> Sort*) (f : ι -> α) : ⨆ (i) (_ : 
κ i), f i <= ⨆ i, f i

--- 原说明 ---
In an (extended) metric space with second countable topology, the Hausdorff dime
nsion
of a set `s` is the supremum over all `x` of the limit superiors of `dimH t` alo
ng
`(𝓝[s] x).smallSets`.
-/
theorem iSup_limsup_dimH (s : Set X) : ⨆ x, limsup dimH (𝓝[s] x).smallSets = dimH s := by
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · rw [← bsupr_limsup_dimH]; exact iSup₂_le_iSup _ _

end

/-!
### Hausdorff dimension and Hölder continuity
-/


variable {C K r : ℝ≥0} {f : X → Y} {s : Set X}

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then `dimH (f '' s) ≤ dimH s / r`. -/
/-
**HolderOnWith.dimH_image_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HolderOnWith.dimH_image_le (h : HolderOnWith C r f s) (hr : 0 < r) : dimH 
(f '' s) <= dimH s / r
参数：h : HolderOnWith C r f s；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dimH_le`：dimH_le {s : Set X} {d : Real>=0∞} (H : forall d' : Real>=0, μH
[d'] s = ∞ -> ↑d' <= d) : dimH s <= d
· 使用定理 `HolderOnWith.hausdorffMeasure_image_le`：hausdorffMeasure_image_le (h : H
olderOnWith C r f s) (hr : 0 < r) {d : Real} (hd : 0 <= d) : μH[d] (f '' s) <= (
C : Real>=0∞) ^ d * μH[r * d…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `le_dimH_of_hausdorffMeasure_eq_top`：le_dimH_of_hausdorffMeasure_eq_top {
s : Set X} {d : Real>=0} (h : μH[d] s = ∞) : ↑d <= dimH s

--- 原说明 ---
If `f` is a Hölder continuous map with exponent `r > 0`, then `dimH (f '' s) ≤ d
imH s / r`.
-/
theorem HolderOnWith.dimH_image_le (h : HolderOnWith C r f s) (hr : 0 < r) :
    dimH (f '' s) ≤ dimH s / r := by
  borelize X Y
  refine dimH_le fun d hd => ?_
  have := h.hausdorffMeasure_image_le hr d.coe_nonneg
  rw [hd, ← ENNReal.coe_rpow_of_nonneg _ d.coe_nonneg, top_le_iff] at this
  have Hrd : μH[(r * d : ℝ≥0)] s = ⊤ := by
    contrapose this
    finiteness
  rw [ENNReal.le_div_iff_mul_le, mul_comm, ← ENNReal.coe_mul]
  exacts [le_dimH_of_hausdorffMeasure_eq_top Hrd, Or.inl (mt ENNReal.coe_eq_zero.1 hr.ne'),
    Or.inl ENNReal.coe_ne_top]

namespace HolderWith

/-- If `f : X → Y` is Hölder continuous with a positive exponent `r`, then the Hausdorff dimension
of the image of a set `s` is at most `dimH s / r`. -/
/-
**HolderWith.dimH_image_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：dimH_image_le (h : HolderWith C r f) (hr : 0 < r) (s : Set X) : dimH (f ''
 s) <= dimH s / r
参数：h : HolderWith C r f；hr : 0 < r；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.dimH_image_le`：HolderOnWith.dimH_image_le (h : HolderOnWith
 C r f s) (hr : 0 < r) : dimH (f '' s) <= dimH s / r
· 使用定理 `HolderWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoE
MetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, Hol
derWith C r f…

--- 原说明 ---
If `f : X → Y` is Hölder continuous with a positive exponent `r`, then the Hausd
orff dimension
of the image of a set `s` is at most `dimH s / r`.
-/
theorem dimH_image_le (h : HolderWith C r f) (hr : 0 < r) (s : Set X) :
    dimH (f '' s) ≤ dimH s / r :=
  (h.holderOnWith s).dimH_image_le hr

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then the Hausdorff dimension of its
range is at most the Hausdorff dimension of its domain divided by `r`. -/
/-
**HolderWith.dimH_range_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：dimH_range_le (h : HolderWith C r f) (hr : 0 < r) : dimH (range f) <= dimH
 (univ : Set X) / r
参数：h : HolderWith C r f；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderWith.dimH_image_le`：dimH_image_le (h : HolderWith C r f) (hr : 0 <
 r) (s : Set X) : dimH (f '' s) <= dimH s / r
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
If `f` is a Hölder continuous map with exponent `r > 0`, then the Hausdorff dime
nsion of its
range is at most the Hausdorff dimension of its domain divided by `r`.
-/
theorem dimH_range_le (h : HolderWith C r f) (hr : 0 < r) :
    dimH (range f) ≤ dimH (univ : Set X) / r :=
  @image_univ _ _ f ▸ h.dimH_image_le hr univ

end HolderWith

/-- If `s` is a set in a space `X` with second countable topology and `f : X → Y` is Hölder
continuous in a neighborhood within `s` of every point `x ∈ s` with the same positive exponent `r`
but possibly different coefficients, then the Hausdorff dimension of the image `f '' s` is at most
the Hausdorff dimension of `s` divided by `r`. -/
/-
**dimH_image_le_of_locally_holder_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_image_le_of_locally_holder_on [SecondCountableTopology X] {r : Real>=
0} {f : X -> Y} (hr : 0 < r) {s : Set X} (hf : forall x in s, exists C : Real>=0
, exists t in 𝓝[s] x, HolderOnWith C r f t) : dimH (f '' s) <= dimH s / r
参数：hr : 0 < r；hf : forall x in s, exists C : Real>=0, exists t in 𝓝[s] x, Holder
OnWith C r f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.countable_cover_nhdsWithin`：countable_cover_nhdsWithin 
[SecondCountableTopology α] {f : α -> Set α} {s : Set α} (hf : forall x in s, f 
x in 𝓝[s] x) : exists t subseteq …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion₂`：inter_iUnion₂ (s : Set α) (t : forall i, κ i -> Set α
) : (s inter ⋃ (i) (j), t i j) = ⋃ (i) (j), s inter t i j
· 使用定理 `Set.image_iUnion₂`：image_iUnion₂ (f : α -> β) (s : forall i, κ i -> Set 
α) : (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j
· 使用定理 `dimH_bUnion`：dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι -> Set X)
 : dimH (⋃ i in s, t i) = ⨆ i in s, dimH (t i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ENNReal.iSup_div`：iSup_div (f : ι -> Real>=0∞) (a : Real>=0∞) : iSup f /
 a = ⨆ i, f i / a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用定理 `HolderOnWith.dimH_image_le`：HolderOnWith.dimH_image_le (h : HolderOnWith
 C r f s) (hr : 0 < r) : dimH (f '' s) <= dimH s / r
· 使用定理 `HolderOnWith.mono`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetric
Space X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal} {f : X → Y}   {s t : Set
 X}, Ho…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `s` is a set in a space `X` with second countable topology and `f : X → Y` is
 Hölder
continuous in a neighborhood within `s` of every point `x ∈ s` with the same pos
itive exponent `r`
but possibly different coefficients, then the Hausdorff dimension of the image `
f '' s` is at most
the Hausdorff dimension of `s` divided by `r`.
-/
theorem dimH_image_le_of_locally_holder_on [SecondCountableTopology X] {r : ℝ≥0} {f : X → Y}
    (hr : 0 < r) {s : Set X} (hf : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, HolderOnWith C r f t) :
    dimH (f '' s) ≤ dimH s / r := by
  choose! C t htn hC using hf
  rcases countable_cover_nhdsWithin htn with ⟨u, hus, huc, huU⟩
  replace huU := inter_eq_self_of_subset_left huU; rw [inter_iUnion₂] at huU
  rw [← huU, image_iUnion₂, dimH_bUnion huc, dimH_bUnion huc]; simp only [ENNReal.iSup_div]
  exact iSup₂_mono fun x hx => ((hC x (hus hx)).mono inter_subset_right).dimH_image_le hr

/-- If `f : X → Y` is Hölder continuous in a neighborhood of every point `x : X` with the same
positive exponent `r` but possibly different coefficients, then the Hausdorff dimension of the range
of `f` is at most the Hausdorff dimension of `X` divided by `r`. -/
/-
**dimH_range_le_of_locally_holder_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_range_le_of_locally_holder_on [SecondCountableTopology X] {r : Real>=
0} {f : X -> Y} (hr : 0 < r) (hf : forall x : X, exists C : Real>=0, exists s in
 𝓝 x, HolderOnWith C r f s) : dimH (range f) <= dimH (univ : Set X) / r
参数：hr : 0 < r；hf : forall x : X, exists C : Real>=0, exists s in 𝓝 x, HolderOnWi
th C r f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `dimH_image_le_of_locally_holder_on`：dimH_image_le_of_locally_holder_on [
SecondCountableTopology X] {r : Real>=0} {f : X -> Y} (hr : 0 < r) {s : Set X} (
hf : forall x in s, exis…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
If `f : X → Y` is Hölder continuous in a neighborhood of every point `x : X` wit
h the same
positive exponent `r` but possibly different coefficients, then the Hausdorff di
mension of the range
of `f` is at most the Hausdorff dimension of `X` divided by `r`.
-/
theorem dimH_range_le_of_locally_holder_on [SecondCountableTopology X] {r : ℝ≥0} {f : X → Y}
    (hr : 0 < r) (hf : ∀ x : X, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, HolderOnWith C r f s) :
    dimH (range f) ≤ dimH (univ : Set X) / r := by
  rw [← image_univ]
  refine dimH_image_le_of_locally_holder_on hr fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

/-!
### Hausdorff dimension and Lipschitz continuity
-/


/-- If `f : X → Y` is Lipschitz continuous on `s`, then `dimH (f '' s) ≤ dimH s`. -/
/-
**LipschitzOnWith.dimH_image_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.dimH_image_le (h : LipschitzOnWith K f s) : dimH (f '' s) 
<= dimH s
参数：h : LipschitzOnWith K f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `HolderOnWith.dimH_image_le`：HolderOnWith.dimH_image_le (h : HolderOnWith
 C r f s) (hr : 0 < r) : dimH (f '' s) <= dimH s / r
· 使用定理 `LipschitzOnWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : Ps
eudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C : NNReal} {f : X → Y}   {
s : Set X}, Lipsch…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
If `f : X → Y` is Lipschitz continuous on `s`, then `dimH (f '' s) ≤ dimH s`.
-/
theorem LipschitzOnWith.dimH_image_le (h : LipschitzOnWith K f s) : dimH (f '' s) ≤ dimH s := by
  simpa using h.holderOnWith.dimH_image_le zero_lt_one

namespace LipschitzWith

/-- If `f` is a Lipschitz continuous map, then `dimH (f '' s) ≤ dimH s`. -/
/-
**LipschitzWith.dimH_image_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：dimH_image_le (h : LipschitzWith K f) (s : Set X) : dimH (f '' s) <= dimH 
s
参数：h : LipschitzWith K f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.dimH_image_le`：LipschitzOnWith.dimH_image_le (h : Lipsch
itzOnWith K f s) : dimH (f '' s) <= dimH s
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…

--- 原说明 ---
If `f` is a Lipschitz continuous map, then `dimH (f '' s) ≤ dimH s`.
-/
theorem dimH_image_le (h : LipschitzWith K f) (s : Set X) : dimH (f '' s) ≤ dimH s :=
  h.lipschitzOnWith.dimH_image_le

/-- If `f` is a Lipschitz continuous map, then the Hausdorff dimension of its range is at most the
Hausdorff dimension of its domain. -/
/-
**LipschitzWith.dimH_range_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：dimH_range_le (h : LipschitzWith K f) : dimH (range f) <= dimH (univ : Set
 X)
参数：h : LipschitzWith K f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.dimH_image_le`：dimH_image_le (h : LipschitzWith K f) (s : 
Set X) : dimH (f '' s) <= dimH s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
If `f` is a Lipschitz continuous map, then the Hausdorff dimension of its range 
is at most the
Hausdorff dimension of its domain.
-/
theorem dimH_range_le (h : LipschitzWith K f) : dimH (range f) ≤ dimH (univ : Set X) :=
  @image_univ _ _ f ▸ h.dimH_image_le univ

end LipschitzWith

/-- If `s` is a set in an extended metric space `X` with second countable topology and `f : X → Y`
is Lipschitz in a neighborhood within `s` of every point `x ∈ s`, then the Hausdorff dimension of
the image `f '' s` is at most the Hausdorff dimension of `s`. -/
/-
**dimH_image_le_of_locally_lipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_image_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X ->
 Y} {s : Set X} (hf : forall x in s, exists C : Real>=0, exists t in 𝓝[s] x, Lip
schitzOnWith C f t) : dimH (f '' s) <= dimH s
参数：hf : forall x in s, exists C : Real>=0, exists t in 𝓝[s] x, LipschitzOnWith C
 f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `dimH_image_le_of_locally_holder_on`：dimH_image_le_of_locally_holder_on [
SecondCountableTopology X] {r : Real>=0} {f : X -> Y} (hr : 0 < r) {s : Set X} (
hf : forall x in s, exis…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
If `s` is a set in an extended metric space `X` with second countable topology a
nd `f : X → Y`
is Lipschitz in a neighborhood within `s` of every point `x ∈ s`, then the Hausd
orff dimension of
the image `f '' s` is at most the Hausdorff dimension of `s`.
-/
theorem dimH_image_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X → Y} {s : Set X}
    (hf : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, LipschitzOnWith C f t) : dimH (f '' s) ≤ dimH s := by
  have : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, HolderOnWith C 1 f t := by
    simpa only [holderOnWith_one] using hf
  simpa only [ENNReal.coe_one, div_one] using dimH_image_le_of_locally_holder_on zero_lt_one this

/-- If `f : X → Y` is Lipschitz in a neighborhood of each point `x : X`, then the Hausdorff
dimension of `range f` is at most the Hausdorff dimension of `X`. -/
/-
**dimH_range_le_of_locally_lipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_range_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X ->
 Y} (hf : forall x : X, exists C : Real>=0, exists s in 𝓝 x, LipschitzOnWith C f
 s) : dimH (range f) <= dimH (univ : Set X)
参数：hf : forall x : X, exists C : Real>=0, exists s in 𝓝 x, LipschitzOnWith C f s
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `dimH_image_le_of_locally_lipschitzOn`：dimH_image_le_of_locally_lipschitz
On [SecondCountableTopology X] {f : X -> Y} {s : Set X} (hf : forall x in s, exi
sts C : Real>=0, exists t …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
If `f : X → Y` is Lipschitz in a neighborhood of each point `x : X`, then the Ha
usdorff
dimension of `range f` is at most the Hausdorff dimension of `X`.
-/
theorem dimH_range_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X → Y}
    (hf : ∀ x : X, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith C f s) :
    dimH (range f) ≤ dimH (univ : Set X) := by
  rw [← image_univ]
  refine dimH_image_le_of_locally_lipschitzOn fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

namespace AntilipschitzWith

/-
**AntilipschitzWith.dimH_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWit
h`。
形式化陈述：dimH_preimage_le (hf : AntilipschitzWith K f) (s : Set Y) : dimH (f ⁻¹' s)
 <= dimH s
参数：hf : AntilipschitzWith K f；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dimH_le`：dimH_le {s : Set X} {d : Real>=0∞} (H : forall d' : Real>=0, μH
[d'] s = ∞ -> ↑d' <= d) : dimH s <= d
· 使用定理 `le_dimH_of_hausdorffMeasure_eq_top`：le_dimH_of_hausdorffMeasure_eq_top {
s : Set X} {d : Real>=0} (h : μH[d] s = ∞) : ↑d <= dimH s
· 使用定理 `AntilipschitzWith.hausdorffMeasure_preimage_le`：hausdorffMeasure_preimag
e_le (hf : AntilipschitzWith K f) (hd : 0 <= d) (s : Set Y) : μH[d] (f ⁻¹' s) <=
 (K : Real>=0∞) ^ d * μH[d] s
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
-/
theorem dimH_preimage_le (hf : AntilipschitzWith K f) (s : Set Y) : dimH (f ⁻¹' s) ≤ dimH s := by
  borelize X Y
  refine dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top ?_
  have := hf.hausdorffMeasure_preimage_le d.coe_nonneg s
  rw [hd, top_le_iff] at this
  contrapose! this
  exact ENNReal.mul_ne_top (by simp) this
/-
**AntilipschitzWith.le_dimH_image** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：le_dimH_image (hf : AntilipschitzWith K f) (s : Set X) : dimH s <= dimH (f
 '' s)
参数：hf : AntilipschitzWith K f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dimH_mono`：dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `AntilipschitzWith.dimH_preimage_le`：dimH_preimage_le (hf : Antilipschitz
With K f) (s : Set Y) : dimH (f ⁻¹' s) <= dimH s
-/
theorem le_dimH_image (hf : AntilipschitzWith K f) (s : Set X) : dimH s ≤ dimH (f '' s) :=
  calc
    dimH s ≤ dimH (f ⁻¹' f '' s) := dimH_mono (subset_preimage_image _ _)
    _ ≤ dimH (f '' s) := hf.dimH_preimage_le _

end AntilipschitzWith

/-!
### Isometries preserve Hausdorff dimension
-/


/-
**Isometry.dimH_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.dimH_image (hf : Isometry f) (s : Set X) : dimH (f '' s) = dimH s
参数：hf : Isometry f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LipschitzWith.dimH_image_le`：dimH_image_le (h : LipschitzWith K f) (s : 
Set X) : dimH (f '' s) <= dimH s
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `AntilipschitzWith.le_dimH_image`：le_dimH_image (hf : AntilipschitzWith K
 f) (s : Set X) : dimH s <= dimH (f '' s)
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f

--- 原说明 ---
### Isometries preserve Hausdorff dimension
-/
theorem Isometry.dimH_image (hf : Isometry f) (s : Set X) : dimH (f '' s) = dimH s :=
  le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)

namespace IsometryEquiv

@[simp]
/-
**IsometryEquiv.dimH_image** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：dimH_image (e : X ≃ᵢ Y) (s : Set X) : dimH (e '' s) = dimH s
参数：e : X ≃ᵢ Y；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.dimH_image`：Isometry.dimH_image (hf : Isometry f) (s : Set X) :
 dimH (f '' s) = dimH s
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
-/
theorem dimH_image (e : X ≃ᵢ Y) (s : Set X) : dimH (e '' s) = dimH s :=
  e.isometry.dimH_image s

@[simp]
/-
**IsometryEquiv.dimH_preimage** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：dimH_preimage (e : X ≃ᵢ Y) (s : Set Y) : dimH (e ⁻¹' s) = dimH s
参数：e : X ≃ᵢ Y；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.image_symm`：image_symm (h : α ≃ᵢ β) : image h.symm = preim
age h
· 使用定理 `IsometryEquiv.dimH_image`：dimH_image (e : X ≃ᵢ Y) (s : Set X) : dimH (e 
'' s) = dimH s
-/
theorem dimH_preimage (e : X ≃ᵢ Y) (s : Set Y) : dimH (e ⁻¹' s) = dimH s := by
  rw [← e.image_symm, e.symm.dimH_image]
/-
**IsometryEquiv.dimH_univ** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：dimH_univ (e : X ≃ᵢ Y) : dimH (univ : Set X) = dimH (univ : Set Y)
参数：e : X ≃ᵢ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.dimH_preimage`：dimH_preimage (e : X ≃ᵢ Y) (s : Set Y) : di
mH (e ⁻¹' s) = dimH s
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem dimH_univ (e : X ≃ᵢ Y) : dimH (univ : Set X) = dimH (univ : Set Y) := by
  rw [← e.dimH_preimage univ, preimage_univ]

end IsometryEquiv

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp]
/-
**ContinuousLinearEquiv.dimH_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：dimH_image (e : E ≃L[𝕜] F) (s : Set E) : dimH (e '' s) = dimH s
参数：e : E ≃L[𝕜] F；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LipschitzWith.dimH_image_le`：dimH_image_le (h : LipschitzWith K f) (s : 
Set X) : dimH (f '' s) <= dimH s
· 使用定理 `ContinuousLinearEquiv.lipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Nontrivia
llyNormedField 𝕜₂] [i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.symm_image_image`：symm_image_image (e : M₁ ≃SL[σ₁₂
] M₂) (s : Set M₁) : e.symm '' e '' s = s
-/
theorem dimH_image (e : E ≃L[𝕜] F) (s : Set E) : dimH (e '' s) = dimH s :=
  le_antisymm (e.lipschitz.dimH_image_le s) <| by
    simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)

@[simp]
/-
**ContinuousLinearEquiv.dimH_preimage** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：dimH_preimage (e : E ≃L[𝕜] F) (s : Set F) : dimH (e ⁻¹' s) = dimH s
参数：e : E ≃L[𝕜] F；s : Set F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.image_symm_eq_preimage`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `ContinuousLinearEquiv.dimH_image`：dimH_image (e : E ≃L[𝕜] F) (s : Set E)
 : dimH (e '' s) = dimH s
-/
theorem dimH_preimage (e : E ≃L[𝕜] F) (s : Set F) : dimH (e ⁻¹' s) = dimH s := by
  rw [← e.image_symm_eq_preimage, e.symm.dimH_image]
/-
**ContinuousLinearEquiv.dimH_univ** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：dimH_univ (e : E ≃L[𝕜] F) : dimH (univ : Set E) = dimH (univ : Set F)
参数：e : E ≃L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.dimH_preimage`：dimH_preimage (e : E ≃L[𝕜] F) (s : 
Set F) : dimH (e ⁻¹' s) = dimH s
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem dimH_univ (e : E ≃L[𝕜] F) : dimH (univ : Set E) = dimH (univ : Set F) := by
  rw [← e.dimH_preimage, preimage_univ]

end ContinuousLinearEquiv

/-!
### Hausdorff dimension in a real vector space
-/


namespace Real

variable {E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-
**Real.dimH_ball_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_ball_pi (x : ι -> Real) {r : Real} (hr : 0 < r) : dimH (Metric.ball x
 r) = Fintype.card ι
参数：x : ι -> Real；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dimH_subsingleton`：dimH_subsingleton {s : Set X} (h : s.Subsingleton) : 
dimH s = 0
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_natCast`：coe_natCast (n : Nat) : ((n : Real>=0) : Real>=0∞) 
= n
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.hausdorffMeasure_pi_real`：hausdorffMeasure_pi_real {ι : Ty
pe*} [Fintype ι] : (μH[Fintype.card ι] : Measure (ι -> Real)) = volume
· 使用定理 `Real.volume_pi_ball`：∀ {ι : Type u_1} [inst : Fintype ι] (a : ι → ℝ) {r 
: ℝ},   0 < r → MeasureTheory.volume (Metric.ball a r) = ENNReal.ofReal ((2 * r)
 ^ Fintyp…
· 使用定理 `dimH_of_hausdorffMeasure_ne_zero_ne_top`：dimH_of_hausdorffMeasure_ne_zer
o_ne_top {d : Real>=0} {s : Set X} (h : μH[d] s != 0) (h' : μH[d] s != ∞) : dimH
 s = d
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `zero_lt_two'`：zero_lt_two' : (0 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
-/
theorem dimH_ball_pi (x : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    dimH (Metric.ball x r) = Fintype.card ι := by
  cases isEmpty_or_nonempty ι
  · rwa [dimH_subsingleton, eq_comm, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
    exact fun x _ y _ => Subsingleton.elim x y
  · rw [← ENNReal.coe_natCast]
    have : μH[Fintype.card ι] (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
      rw [hausdorffMeasure_pi_real, Real.volume_pi_ball _ hr]
    refine dimH_of_hausdorffMeasure_ne_zero_ne_top ?_ ?_ <;> rw [NNReal.coe_natCast, this]
    · simp [pow_pos (mul_pos (zero_lt_two' ℝ) hr)]
    · exact ENNReal.ofReal_ne_top
/-
**Real.dimH_ball_pi_fin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_ball_pi_fin {n : Nat} (x : Fin n -> Real) {r : Real} (hr : 0 < r) : d
imH (Metric.ball x r) = n
参数：x : Fin n -> Real；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.dimH_ball_pi`：dimH_ball_pi (x : ι -> Real) {r : Real} (hr : 0 < r) 
: dimH (Metric.ball x r) = Fintype.card ι
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem dimH_ball_pi_fin {n : ℕ} (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    dimH (Metric.ball x r) = n := by rw [dimH_ball_pi x hr, Fintype.card_fin]
/-
**Real.dimH_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_univ_pi (ι : Type*) [Fintype ι] : dimH (univ : Set (ι -> Real)) = Fin
type.card ι
参数：ι : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.iUnion_ball_nat_succ`：iUnion_ball_nat_succ (x : α) : ⋃ n : Nat, b
all x (n + 1) = univ
· 使用定理 `dimH_iUnion`：dimH_iUnion {ι : Sort*} [Countable ι] (s : ι -> Set X) : di
mH (⋃ i, s i) = ⨆ i, dimH (s i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.dimH_ball_pi`：dimH_ball_pi (x : ι -> Real) {r : Real} (hr : 0 < r) 
: dimH (Metric.ball x r) = Fintype.card ι
· 使用定理 `Nat.cast_add_one_pos`：cast_add_one_pos (n : Nat) : 0 < (n : α) + 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dimH_univ_pi (ι : Type*) [Fintype ι] : dimH (univ : Set (ι → ℝ)) = Fintype.card ι := by
  simp only [← Metric.iUnion_ball_nat_succ (0 : ι → ℝ), dimH_iUnion,
    dimH_ball_pi _ (Nat.cast_add_one_pos _), iSup_const]
/-
**Real.dimH_univ_pi_fin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_univ_pi_fin (n : Nat) : dimH (univ : Set (Fin n -> Real)) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.dimH_univ_pi`：dimH_univ_pi (ι : Type*) [Fintype ι] : dimH (univ : S
et (ι -> Real)) = Fintype.card ι
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem dimH_univ_pi_fin (n : ℕ) : dimH (univ : Set (Fin n → ℝ)) = n := by
  rw [dimH_univ_pi, Fintype.card_fin]
/-
**Real.dimH_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_of_mem_nhds {x : E} {s : Set E} (h : s in 𝓝 x) : dimH s = finrank Rea
l E
参数：h : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_fin_fun`：Module.finrank_fin_fun {n : Nat} : finrank R (Fi
n n -> R) = n
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.dimH_image`：dimH_image (e : E ≃L[𝕜] F) (s : Set E)
 : dimH (e '' s) = dimH s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `dimH_mono`：dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Real.dimH_univ_pi_fin`：dimH_univ_pi_fin (n : Nat) : dimH (univ : Set (Fi
n n -> Real)) = n
· 使用定理 `ContinuousLinearEquiv.map_nhds_eq`：map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x :
 M₁) : map e (𝓝 x) = 𝓝 (e x)
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.dimH_ball_pi_fin`：dimH_ball_pi_fin {n : Nat} (x : Fin n -> Real) {r
 : Real} (hr : 0 < r) : dimH (Metric.ball x r) = n
-/
theorem dimH_of_mem_nhds {x : E} {s : Set E} (h : s ∈ 𝓝 x) : dimH s = finrank ℝ E := by
  have e : E ≃L[ℝ] Fin (finrank ℝ E) → ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  rw [← e.dimH_image]
  refine le_antisymm ?_ ?_
  · exact (dimH_mono (subset_univ _)).trans_eq (dimH_univ_pi_fin _)
  · have : e '' s ∈ 𝓝 (e x) := by rw [← e.map_nhds_eq]; exact image_mem_map h
    rcases Metric.nhds_basis_ball.mem_iff.1 this with ⟨r, hr0, hr⟩
    simpa only [dimH_ball_pi_fin (e x) hr0] using dimH_mono hr
/-
**Real.dimH_of_nonempty_interior** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_of_nonempty_interior {s : Set E} (h : (interior s).Nonempty) : dimH s
 = finrank Real E
参数：h : (interior s).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.dimH_of_mem_nhds`：dimH_of_mem_nhds {x : E} {s : Set E} (h : s in 𝓝 
x) : dimH s = finrank Real E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
-/
theorem dimH_of_nonempty_interior {s : Set E} (h : (interior s).Nonempty) : dimH s = finrank ℝ E :=
  let ⟨_, hx⟩ := h
  dimH_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)

/-- The Hausdorff dimension of a nonempty convex set equals the dimension of its affine span. -/
/-
**Real.Convex.dimH_eq_finrank_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 `Real.Convex`
。
形式化陈述：∀ {E : Type u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[FiniteDimensional ℝ E] {s : Set E},   Convex ℝ s → s.Nonempty → dimH s = ↑(Modu
le.finrank ℝ ↥(vectorSpan ℝ s))
参数：Module.finrank ℝ ↥(vectorSpan ℝ s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Isometry.dimH_image`：Isometry.dimH_image (hf : Isometry f) (s : Set X) :
 dimH (f '' s) = dimH s
· 使用定理 `isometry_subtype_coe`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {s : 
Set α}, Isometry Subtype.val
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…
· 使用定理 `Real.dimH_of_nonempty_interior`：dimH_of_nonempty_interior {s : Set E} (h
 : (interior s).Nonempty) : dimH s = finrank Real E
· 使用定理 `Homeomorph.image_interior`：image_interior (h : X ≃ₜ Y) (s : Set X) : h '
' interior s = interior (h '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intrinsicInterior_nonempty`：intrinsicInterior_nonempty (hs : Convex Real
 s) : (intrinsicInterior Real s).Nonempty ↔ s.Nonempty
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s

--- 原说明 ---
The Hausdorff dimension of a nonempty convex set equals the dimension of its aff
ine span.
-/
theorem Convex.dimH_eq_finrank_vectorSpan {s : Set E} (hcvx : Convex ℝ s) (hne : s.Nonempty) :
    dimH s = finrank ℝ (vectorSpan ℝ s) := by
  have := hne.to_subtype
  let φ := AffineIsometryEquiv.constVSub ℝ
    (⟨hne.some, subset_affineSpan ℝ s hne.some_mem⟩ : affineSpan ℝ s)
  have hs_eq : s = (↑) '' ((↑) ⁻¹' s : Set (affineSpan ℝ s)) :=
    (image_preimage_eq_of_subset <| (subset_affineSpan ℝ s).trans Subtype.range_coe.superset).symm
  rw [hs_eq, isometry_subtype_coe.dimH_image, ← φ.isometry.dimH_image,
      Real.dimH_of_nonempty_interior, direction_affineSpan ℝ s, ← hs_eq]
  simp_rw [← AffineIsometryEquiv.coe_toHomeomorph, ← φ.toHomeomorph.image_interior, image_nonempty]
  simpa [intrinsicInterior] using (intrinsicInterior_nonempty hcvx).mpr hne

variable (E)
/-
**Real.dimH_univ_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_univ_eq_finrank : dimH (univ : Set E) = finrank Real E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.dimH_of_mem_nhds`：dimH_of_mem_nhds {x : E} {s : Set E} (h : s in 𝓝 
x) : dimH s = finrank Real E
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem dimH_univ_eq_finrank : dimH (univ : Set E) = finrank ℝ E :=
  dimH_of_mem_nhds (@univ_mem _ (𝓝 0))
/-
**Real.dimH_univ** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_univ : dimH (univ : Set Real) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.dimH_univ_eq_finrank`：dimH_univ_eq_finrank : dimH (univ : Set E) = 
finrank Real E
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem dimH_univ : dimH (univ : Set ℝ) = 1 := by
  rw [dimH_univ_eq_finrank ℝ, Module.finrank_self, Nat.cast_one]

variable {E}

/-- The Hausdorff dimension of any set in a finite-dimensional real normed space is finite. -/
/-
**Real.dimH_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_lt_top (s : Set E) : dimH s < ⊤
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dimH_mono`：dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Real.dimH_univ_eq_finrank`：dimH_univ_eq_finrank : dimH (univ : Set E) = 
finrank Real E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
The Hausdorff dimension of any set in a finite-dimensional real normed space is 
finite.
-/
theorem dimH_lt_top (s : Set E) : dimH s < ⊤ := by calc
  dimH s ≤ dimH (univ : Set E) := dimH_mono (subset_univ s)
  _ = finrank ℝ E := dimH_univ_eq_finrank E
  _ < ⊤ := by simp
/-
**Real.dimH_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_ne_top (s : Set E) : dimH s != ⊤
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Real.dimH_lt_top`：dimH_lt_top (s : Set E) : dimH s < ⊤
-/
theorem dimH_ne_top (s : Set E) : dimH s ≠ ⊤ := (dimH_lt_top s).ne
/-
**Real.hausdorffMeasure_of_finrank_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hausdorffMeasure_of_finrank_lt [MeasurableSpace E] [BorelSpace E] {d : Rea
l} (hd : finrank Real E < d) : (μH[d] : Measure E) = 0
参数：hd : finrank Real E < d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `hausdorffMeasure_of_dimH_lt`：hausdorffMeasure_of_dimH_lt {s : Set X} {d 
: Real>=0} (h : dimH s < d) : μH[d] s = 0
· 使用定理 `Real.dimH_univ_eq_finrank`：dimH_univ_eq_finrank : dimH (univ : Set E) = 
finrank Real E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
-/
lemma hausdorffMeasure_of_finrank_lt [MeasurableSpace E] [BorelSpace E] {d : ℝ}
    (hd : finrank ℝ E < d) : (μH[d] : Measure E) = 0 := by
  lift d to ℝ≥0 using (Nat.cast_nonneg _).trans hd.le
  rw [← measure_univ_eq_zero]
  apply hausdorffMeasure_of_dimH_lt
  rw [dimH_univ_eq_finrank]
  exact mod_cast hd

/-- The Hausdorff dimension of a non-degenerate segment in a real normed space is 1. -/
/-
**Real.dimH_segment** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dimH_segment {x y : E} (h : x != y) : dimH (segment Real x y) = 1
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Convex.dimH_eq_finrank_vectorSpan`：∀ {E : Type u_4} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E},  
 Convex ℝ s → s.Nonempty → d…
· 使用定理 `convex_segment`：convex_segment [IsOrderedRing 𝕜] (x y : E) : Convex 𝕜 [x
 -[𝕜] y]
· 使用定理 `left_mem_segment`：left_mem_segment (x y : E) : x in [x -[𝕜] y]
· 使用定理 `vectorSpan_segment`：vectorSpan_segment {p₁ p₂ : E} : vectorSpan R (segme
nt R p₁ p₂) = R ∙ (p₂ -ᵥ p₁)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff dimension of a non-degenerate segment in a real normed space is 1.
-/
theorem dimH_segment {x y : E} (h : x ≠ y) :
    dimH (segment ℝ x y) = 1 := by
  rw [Convex.dimH_eq_finrank_vectorSpan (convex_segment x y) ⟨x, left_mem_segment ℝ x y⟩,
      vectorSpan_segment]
  simp [finrank_span_singleton (sub_ne_zero.mpr h.symm)]

end Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-
**dense_compl_of_dimH_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_compl_of_dimH_lt_finrank {s : Set E} (hs : dimH s < finrank Real E) 
: Dense sᶜ
参数：hs : dimH s < finrank Real E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.dimH_of_mem_nhds`：dimH_of_mem_nhds {x : E} {s : Set E} (h : s in 𝓝 
x) : dimH s = finrank Real E
· 使用定理 `dimH_mono`：dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
-/
theorem dense_compl_of_dimH_lt_finrank {s : Set E} (hs : dimH s < finrank ℝ E) : Dense sᶜ := by
  refine fun x => mem_closure_iff_nhds.2 fun t ht => nonempty_iff_ne_empty.2 fun he => hs.not_ge ?_
  rw [← sdiff_eq, sdiff_eq_empty] at he
  rw [← Real.dimH_of_mem_nhds ht]
  exact dimH_mono he

/-!
### Hausdorff dimension and `C¹`-smooth maps

`C¹`-smooth maps are locally Lipschitz continuous, hence they do not increase the Hausdorff
dimension of sets.
-/


/-- Let `f` be a function defined on a finite-dimensional real normed space. If `f` is `C¹`-smooth
on a convex set `s`, then the Hausdorff dimension of `f '' s` is less than or equal to the Hausdorff
dimension of `s`.

TODO: do we actually need `Convex ℝ s`? -/
/-
**ContDiffOn.dimH_image_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.dimH_image_le {f : E -> F} {s t : Set E} (hf : ContDiffOn Real 
1 f s) (hc : Convex Real s) (ht : t subseteq s) : dimH (f '' t) <= dimH t
参数：hf : ContDiffOn Real 1 f s；hc : Convex Real s；ht : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dimH_image_le_of_locally_lipschitzOn`：dimH_image_le_of_locally_lipschitz
On [SecondCountableTopology X] {f : X -> Y} {s : Set X} (hf : forall x in s, exi
sts C : Real>=0, exists t …
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ContDiffWithinAt.exists_lipschitzOnWith`：ContDiffWithinAt.exists_lipschi
tzOnWith (hf : ContDiffWithinAt Real 1 f s x) (hs : Convex Real s) : exists K : 
Real>=0, exists t in 𝓝[s] x, …
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x

--- 原说明 ---
Let `f` be a function defined on a finite-dimensional real normed space. If `f` 
is `C¹`-smooth
on a convex set `s`, then the Hausdorff dimension of `f '' s` is less than or eq
ual to the Hausdorff
dimension of `s`.

TODO: do we actually need `Convex ℝ s`?
-/
theorem ContDiffOn.dimH_image_le {f : E → F} {s t : Set E} (hf : ContDiffOn ℝ 1 f s)
    (hc : Convex ℝ s) (ht : t ⊆ s) : dimH (f '' t) ≤ dimH t :=
  dimH_image_le_of_locally_lipschitzOn fun x hx =>
    let ⟨C, u, hu, hf⟩ := (hf x (ht hx)).exists_lipschitzOnWith hc
    ⟨C, u, nhdsWithin_mono _ ht hu, hf⟩

/-- The Hausdorff dimension of the range of a `C¹`-smooth function defined on a finite-dimensional
real normed space is at most the dimension of its domain as a vector space over `ℝ`. -/
/-
**ContDiff.dimH_range_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.dimH_range_le {f : E -> F} (h : ContDiff Real 1 f) : dimH (range 
f) <= finrank Real E
参数：h : ContDiff Real 1 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `ContDiffOn.dimH_image_le`：ContDiffOn.dimH_image_le {f : E -> F} {s t : S
et E} (hf : ContDiffOn Real 1 f s) (hc : Convex Real s) (ht : t subseteq s) : di
mH (f '' t) <=…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Real.dimH_univ_eq_finrank`：dimH_univ_eq_finrank : dimH (univ : Set E) = 
finrank Real E

--- 原说明 ---
The Hausdorff dimension of the range of a `C¹`-smooth function defined on a fini
te-dimensional
real normed space is at most the dimension of its domain as a vector space over 
`ℝ`.
-/
theorem ContDiff.dimH_range_le {f : E → F} (h : ContDiff ℝ 1 f) : dimH (range f) ≤ finrank ℝ E :=
  calc
    dimH (range f) = dimH (f '' univ) := by rw [image_univ]
    _ ≤ dimH (univ : Set E) := h.contDiffOn.dimH_image_le convex_univ Subset.rfl
    _ = finrank ℝ E := Real.dimH_univ_eq_finrank E

/-- A particular case of Sard's Theorem. Let `f : E → F` be a map between finite-dimensional real
vector spaces. Suppose that `f` is `C¹` smooth on a convex set `s` of Hausdorff dimension strictly
less than the dimension of `F`. Then the complement of the image `f '' s` is dense in `F`. -/
/-
**ContDiffOn.dense_compl_image_of_dimH_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.dense_compl_image_of_dimH_lt_finrank [FiniteDimensional Real F]
 {f : E -> F} {s t : Set E} (h : ContDiffOn Real 1 f s) (hc : Convex Real s) (ht
 : t subseteq s) (htF : dimH t < finrank Real F) : Dense (f '' t)ᶜ
参数：h : ContDiffOn Real 1 f s；hc : Convex Real s；ht : t subseteq s；htF : dimH t <
 finrank Real F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dense_compl_of_dimH_lt_finrank`：dense_compl_of_dimH_lt_finrank {s : Set 
E} (hs : dimH s < finrank Real E) : Dense sᶜ
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ContDiffOn.dimH_image_le`：ContDiffOn.dimH_image_le {f : E -> F} {s t : S
et E} (hf : ContDiffOn Real 1 f s) (hc : Convex Real s) (ht : t subseteq s) : di
mH (f '' t) <=…

--- 原说明 ---
A particular case of Sard's Theorem. Let `f : E → F` be a map between finite-dim
ensional real
vector spaces. Suppose that `f` is `C¹` smooth on a convex set `s` of Hausdorff 
dimension strictly
less than the dimension of `F`. Then the complement of the image `f '' s` is den
se in `F`.
-/
theorem ContDiffOn.dense_compl_image_of_dimH_lt_finrank [FiniteDimensional ℝ F] {f : E → F}
    {s t : Set E} (h : ContDiffOn ℝ 1 f s) (hc : Convex ℝ s) (ht : t ⊆ s)
    (htF : dimH t < finrank ℝ F) : Dense (f '' t)ᶜ :=
  dense_compl_of_dimH_lt_finrank <| (h.dimH_image_le hc ht).trans_lt htF

/-- A particular case of Sard's Theorem. If `f` is a `C¹` smooth map from a real vector space to a
real vector space `F` of strictly larger dimension, then the complement of the range of `f` is dense
in `F`. -/
/-
**ContDiff.dense_compl_range_of_finrank_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.dense_compl_range_of_finrank_lt_finrank [FiniteDimensional Real F
] {f : E -> F} (h : ContDiff Real 1 f) (hEF : finrank Real E < finrank Real F) :
 Dense (range f)ᶜ
参数：h : ContDiff Real 1 f；hEF : finrank Real E < finrank Real F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dense_compl_of_dimH_lt_finrank`：dense_compl_of_dimH_lt_finrank {s : Set 
E} (hs : dimH s < finrank Real E) : Dense sᶜ
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ContDiff.dimH_range_le`：ContDiff.dimH_range_le {f : E -> F} (h : ContDif
f Real 1 f) : dimH (range f) <= finrank Real E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal

--- 原说明 ---
A particular case of Sard's Theorem. If `f` is a `C¹` smooth map from a real vec
tor space to a
real vector space `F` of strictly larger dimension, then the complement of the r
ange of `f` is dense
in `F`.
-/
theorem ContDiff.dense_compl_range_of_finrank_lt_finrank [FiniteDimensional ℝ F] {f : E → F}
    (h : ContDiff ℝ 1 f) (hEF : finrank ℝ E < finrank ℝ F) : Dense (range f)ᶜ :=
  dense_compl_of_dimH_lt_finrank <| h.dimH_range_le.trans_lt <| Nat.cast_lt.2 hEF

/--
The Hausdorff dimension of the orthogonal projection of a set `s` onto a subspace `K`
is less than or equal to the Hausdorff dimension of `s`.
-/
/-
**dimH_orthogonalProjectionOnto_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dimH_orthogonalProjectionOnto_le {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGr
oup E] [InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (
s : Set E) : dimH (K.orthogonalProjectionOnto '' s) <= dimH s
参数：K : Submodule 𝕜 E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.dimH_image_le`：dimH_image_le (h : LipschitzWith K f) (s : 
Set X) : dimH (f '' s) <= dimH s
· 使用定理 `Submodule.lipschitzWith_orthogonalProjectionOnto`：lipschitzWith_orthogon
alProjectionOnto : LipschitzWith 1 (orthogonalProjectionOnto K)

--- 原说明 ---
The Hausdorff dimension of the orthogonal projection of a set `s` onto a subspac
e `K`
is less than or equal to the Hausdorff dimension of `s`.
-/
theorem dimH_orthogonalProjectionOnto_le {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (s : Set E) :
    dimH (K.orthogonalProjectionOnto '' s) ≤ dimH s :=
  K.lipschitzWith_orthogonalProjectionOnto.dimH_image_le s

@[deprecated (since := "2026-05-05")] alias dimH_orthogonalProjection_le :=
  dimH_orthogonalProjectionOnto_le
