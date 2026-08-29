/-
Copyright (c) 2024 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder norm

This file defines the Hölder (semi-)norm for Hölder functions alongside some basic properties.
The `r`-Hölder norm of a function `f : X → Y` between two metric spaces is the least non-negative
real number `C` for which `f` is `r`-Hölder continuous with constant `C`, i.e. it is the least `C`
for which `WithHolder C r f` is true.

## Main definitions

* `eHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f`.
* `nnHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0` of a function `f`.
* `MemHolder r f`: Predicate for a function `f` being `r`-Hölder continuous.

## Main results

* `eHolderNorm_eq_zero`: the Hölder norm of a function is zero if and only if it is constant.
* `MemHolder.holderWith`: The Hölder norm of a Hölder function `f` is a Hölder constant of `f`.

## Tags

Hölder norm, Hoelder norm, Holder norm

-/

@[expose] public section

variable {X Y : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {r : Real>=0} {f : X -> Y}

/-- The `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f` is the least non-negative real
number `C` for which `f` is `r`-Hölder continuous with constant `C`. This is `∞` if no such
non-negative real exists. -/
noncomputable
/--
Definition of `eHolderNorm` / `eHolderNorm` 的定义

English:
definition eHolderNorm
  signature: (r : Real>=0) (f : X -> Y)
  body: ⨅ (C) (_ : HolderWith C r f), C

中文:
定义 eHolderNorm
  签名: (r : 实数>=0) (f : X -> Y)
  定义体: ⨅ (C) (_ : HolderWith C r f), C

Depends on / 依赖: HolderWith
-/
def eHolderNorm (r : Real>=0) (f : X -> Y) : Real>=0∞ := ⨅ (C) (_ : HolderWith C r f), C

/-- The `r`-Hölder (semi)norm in `ℝ≥0`. -/
noncomputable
/--
Definition of `nnHolderNorm` / `nnHolderNorm` 的定义

English:
definition nnHolderNorm
  signature: (r : Real>=0) (f : X -> Y)
  body: (eHolderNorm r f).toNNReal

中文:
定义 nnHolderNorm
  签名: (r : 实数>=0) (f : X -> Y)
  定义体: (eHolderNorm r f).toNNReal

Depends on / 依赖: eHolderNorm, toNNReal
-/
def nnHolderNorm (r : Real>=0) (f : X -> Y) : Real>=0 := (eHolderNorm r f).toNNReal

/--
Definition of `MemHolder` / `MemHolder` 的定义

English:
definition MemHolder
  signature: (r : Real>=0) (f : X -> Y)
  body: exists C, HolderWith C r f

中文:
定义 MemHolder
  签名: (r : 实数>=0) (f : X -> Y)
  定义体: exists C, HolderWith C r f

Depends on / 依赖: HolderWith
-/
def MemHolder (r : Real>=0) (f : X -> Y) : Prop := exists C, HolderWith C r f

/--
lemma `HolderWith.memHolder` / 引理 `HolderWith.memHolder`

English:
lemma HolderWith.memHolder
  given: {C : Real>=0} (hf : HolderWith C r f)
  statement: MemHolder r f
  proof: ⟨C, hf⟩

中文:
引理 HolderWith.memHolder
  条件: {C : 实数>=0} (hf : HolderWith C r f)
  结论: MemHolder r f
  证明: ⟨C, hf⟩
-/
lemma HolderWith.memHolder {C : Real>=0} (hf : HolderWith C r f) : MemHolder r f := ⟨C, hf⟩

/--
lemma `eHolderNorm_lt_top` / 引理 `eHolderNorm_lt_top`

English:
lemma eHolderNorm_lt_top
  statement: eHolderNorm r f < ∞ ↔ MemHolder r f
  proof: by
  refine ⟨fun h => ?_,
    fun hf => let ⟨C, hC⟩ := hf; iInf_lt_top.2 ⟨C, iInf_lt_top.2 ⟨hC, coe_lt_top⟩⟩⟩
  simp_rw [eHolderNorm, iInf_lt_top] at h
  let ⟨C, hC, _⟩ := h
  exact ⟨C, hC⟩

中文:
引理 eHolderNorm_lt_top
  结论: eHolderNorm r f < ∞ ↔ MemHolder r f
  证明: by
  refine ⟨fun h => ?_,
    fun hf => let ⟨C, hC⟩ := hf; iInf_lt_top.2 ⟨C, iInf_lt_top.2 ⟨hC, coe_lt_top⟩⟩⟩
  simp_rw [eHolderNorm, iInf_lt_top] at h
  let ⟨C, hC, _⟩ := h
  exact ⟨C, hC⟩
-/
@[simp] lemma eHolderNorm_lt_top : eHolderNorm r f < ∞ ↔ MemHolder r f := by
  refine ⟨fun h => ?_,
    fun hf => let ⟨C, hC⟩ := hf; iInf_lt_top.2 ⟨C, iInf_lt_top.2 ⟨hC, coe_lt_top⟩⟩⟩
  simp_rw [eHolderNorm, iInf_lt_top] at h
  let ⟨C, hC, _⟩ := h
  exact ⟨C, hC⟩

/--
lemma `eHolderNorm_ne_top` / 引理 `eHolderNorm_ne_top`

English:
lemma eHolderNorm_ne_top
  statement: eHolderNorm r f != ∞ ↔ MemHolder r f
  proof: by
  rw [← eHolderNorm_lt_top]; rw [lt_top_iff_ne_top]

中文:
引理 eHolderNorm_ne_top
  结论: eHolderNorm r f != ∞ ↔ MemHolder r f
  证明: by
  rw [← eHolderNorm_lt_top]; rw [lt_top_iff_ne_top]

Depends on / 依赖: eHolderNorm_lt_top, lt_top_iff_ne_top
-/
lemma eHolderNorm_ne_top : eHolderNorm r f != ∞ ↔ MemHolder r f := by
  rw [← eHolderNorm_lt_top]; rw [lt_top_iff_ne_top]

/--
lemma `eHolderNorm_eq_top` / 引理 `eHolderNorm_eq_top`

English:
lemma eHolderNorm_eq_top
  statement: eHolderNorm r f = ∞ ↔ ¬ MemHolder r f
  proof: by
  rw [← eHolderNorm_ne_top]; rw [not_not]

protected alias ⟨_, MemHolder.eHolderNorm_lt_top⟩ := eHolderNorm_lt_top
protected alias ⟨_, MemHolder.eHolderNorm_ne_top⟩ := eHolderNorm_ne_top

中文:
引理 eHolderNorm_eq_top
  结论: eHolderNorm r f = ∞ ↔ ¬ MemHolder r f
  证明: by
  rw [← eHolderNorm_ne_top]; rw [not_not]

protected alias ⟨_, MemHolder.eHolderNorm_lt_top⟩ := eHolderNorm_lt_top
protected alias ⟨_, MemHolder.eHolderNorm_ne_top⟩ := eHolderNorm_ne_top
-/
@[simp] lemma eHolderNorm_eq_top : eHolderNorm r f = ∞ ↔ ¬ MemHolder r f := by
  rw [← eHolderNorm_ne_top]; rw [not_not]

protected alias ⟨_, MemHolder.eHolderNorm_lt_top⟩ := eHolderNorm_lt_top
protected alias ⟨_, MemHolder.eHolderNorm_ne_top⟩ := eHolderNorm_ne_top

/--
lemma `coe_nnHolderNorm_le_eHolderNorm` / 引理 `coe_nnHolderNorm_le_eHolderNorm`

English:
lemma coe_nnHolderNorm_le_eHolderNorm
  given: {r : Real>=0} {f : X -> Y}
  proof: coe_toNNReal_le_self

中文:
引理 coe_nnHolderNorm_le_eHolderNorm
  条件: {r : 实数>=0} {f : X -> Y}
  证明: coe_toNNReal_le_self

Depends on / 依赖: coe_toNNReal_le_self
-/
lemma coe_nnHolderNorm_le_eHolderNorm {r : Real>=0} {f : X -> Y} :
    (nnHolderNorm r f : Real>=0∞) <= eHolderNorm r f :=
  coe_toNNReal_le_self

variable (X) in
@[simp]
/--
lemma `eHolderNorm_const` / 引理 `eHolderNorm_const`

English:
lemma eHolderNorm_const
  given: (r : Real>=0) (c : Y)
  statement: eHolderNorm r (Function.const X c) = 0
  proof: by
  rw [eHolderNorm]; rw [← ENNReal.bot_eq_zero]; rw [iInf₂_eq_bot]
  exact fun C' hC' => ⟨0, .const, hC'⟩

中文:
引理 eHolderNorm_const
  条件: (r : 实数>=0) (c : Y)
  结论: eHolderNorm r (Function.const X c) = 0
  证明: by
  rw [eHolderNorm]; rw [← ENNReal.bot_eq_zero]; rw [iInf₂_eq_bot]
  exact fun C' hC' => ⟨0, .const, hC'⟩

Depends on / 依赖: ENNReal, ENNReal.bot_eq_zero, bot_eq_zero, eHolderNorm
-/
lemma eHolderNorm_const (r : Real>=0) (c : Y) : eHolderNorm r (Function.const X c) = 0 := by
  rw [eHolderNorm]; rw [← ENNReal.bot_eq_zero]; rw [iInf₂_eq_bot]
  exact fun C' hC' => ⟨0, .const, hC'⟩

variable (X) in
@[simp]
/--
lemma `eHolderNorm_zero` / 引理 `eHolderNorm_zero`

English:
lemma eHolderNorm_zero
  given: [Zero Y] (r : Real>=0)
  statement: eHolderNorm r (0 : X -> Y) = 0
  proof: eHolderNorm_const X r 0

中文:
引理 eHolderNorm_zero
  条件: [Zero Y] (r : 实数>=0)
  结论: eHolderNorm r (0 : X -> Y) = 0
  证明: eHolderNorm_const X r 0

Depends on / 依赖: eHolderNorm_const
-/
lemma eHolderNorm_zero [Zero Y] (r : Real>=0) : eHolderNorm r (0 : X -> Y) = 0 :=
  eHolderNorm_const X r 0

variable (X) in
@[simp]
/--
lemma `nnHolderNorm_const` / 引理 `nnHolderNorm_const`

English:
lemma nnHolderNorm_const
  given: (r : Real>=0) (c : Y)
  statement: nnHolderNorm r (Function.const X c) = 0
  proof: by
  rw [← nonpos_iff_eq_zero]; rw [← ENNReal.coe_le_coe]; rw [ENNReal.coe_zero]; rw [← eHolderNorm_const X r c]
  exact coe_nnHolderNorm_le_eHolderNorm

中文:
引理 nnHolderNorm_const
  条件: (r : 实数>=0) (c : Y)
  结论: nnHolderNorm r (Function.const X c) = 0
  证明: by
  rw [← nonpos_iff_eq_zero]; rw [← ENNReal.coe_le_coe]; rw [ENNReal.coe_zero]; rw [← eHolderNorm_const X r c]
  exact coe_nnHolderNorm_le_eHolderNorm

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_zero, coe_le_coe, coe_nnHolderNorm_le_eHolderNorm, coe_zero, eHolderNorm_const, nonpos_iff_eq_zero
-/
lemma nnHolderNorm_const (r : Real>=0) (c : Y) : nnHolderNorm r (Function.const X c) = 0 := by
  rw [← nonpos_iff_eq_zero]; rw [← ENNReal.coe_le_coe]; rw [ENNReal.coe_zero]; rw [← eHolderNorm_const X r c]
  exact coe_nnHolderNorm_le_eHolderNorm

variable (X) in
@[simp]
/--
lemma `nnHolderNorm_zero` / 引理 `nnHolderNorm_zero`

English:
lemma nnHolderNorm_zero
  given: [Zero Y] (r : Real>=0)
  statement: nnHolderNorm r (0 : X -> Y) = 0
  proof: nnHolderNorm_const X r 0

中文:
引理 nnHolderNorm_zero
  条件: [Zero Y] (r : 实数>=0)
  结论: nnHolderNorm r (0 : X -> Y) = 0
  证明: nnHolderNorm_const X r 0

Depends on / 依赖: nnHolderNorm_const
-/
lemma nnHolderNorm_zero [Zero Y] (r : Real>=0) : nnHolderNorm r (0 : X -> Y) = 0 :=
  nnHolderNorm_const X r 0

attribute [simp] eHolderNorm_const eHolderNorm_zero

/--
lemma `eHolderNorm_of_isEmpty` / 引理 `eHolderNorm_of_isEmpty`

English:
lemma eHolderNorm_of_isEmpty
  given: [hX : IsEmpty X]
  proof: by
  rw [eHolderNorm]; rw [← ENNReal.bot_eq_zero]; rw [iInf₂_eq_bot]
  exact fun ε hε => ⟨0, .of_isEmpty, hε⟩

中文:
引理 eHolderNorm_of_isEmpty
  条件: [hX : IsEmpty X]
  证明: by
  rw [eHolderNorm]; rw [← ENNReal.bot_eq_zero]; rw [iInf₂_eq_bot]
  exact fun ε hε => ⟨0, .of_isEmpty, hε⟩

Depends on / 依赖: ENNReal, ENNReal.bot_eq_zero, bot_eq_zero, eHolderNorm, of_isEmpty
-/
lemma eHolderNorm_of_isEmpty [hX : IsEmpty X] :
    eHolderNorm r f = 0 := by
  rw [eHolderNorm]; rw [← ENNReal.bot_eq_zero]; rw [iInf₂_eq_bot]
  exact fun ε hε => ⟨0, .of_isEmpty, hε⟩

/--
lemma `HolderWith.eHolderNorm_le` / 引理 `HolderWith.eHolderNorm_le`

English:
lemma HolderWith.eHolderNorm_le
  given: {C : Real>=0} (hf : HolderWith C r f)
  proof: iInf₂_le C hf

中文:
引理 HolderWith.eHolderNorm_le
  条件: {C : 实数>=0} (hf : HolderWith C r f)
  证明: iInf₂_le C hf
-/
lemma HolderWith.eHolderNorm_le {C : Real>=0} (hf : HolderWith C r f) :
    eHolderNorm r f <= C :=
  iInf₂_le C hf

/-- See also `memHolder_const` for the version with the spelling `fun _ ↦ c`. -/
@[simp]
/--
lemma `memHolder_const` / 引理 `memHolder_const`

English:
lemma memHolder_const
  given: {c : Y}
  statement: MemHolder r (Function.const X c)
  proof: (HolderWith.const (C := 0)).memHolder

中文:
引理 memHolder_const
  条件: {c : Y}
  结论: MemHolder r (Function.const X c)
  证明: (HolderWith.const (C := 0)).memHolder

Depends on / 依赖: HolderWith, HolderWith.const, memHolder
-/
lemma memHolder_const {c : Y} : MemHolder r (Function.const X c) :=
  (HolderWith.const (C := 0)).memHolder

/-- Version of `memHolder_const` with the spelling `fun _ ↦ c` for the constant function. -/
@[simp]
/--
lemma `memHolder_const'` / 引理 `memHolder_const'`

English:
lemma memHolder_const'
  given: {c : Y}
  statement: MemHolder r (fun _ => c : X -> Y)
  proof: memHolder_const

@[simp]

中文:
引理 memHolder_const'
  条件: {c : Y}
  结论: MemHolder r (fun _ => c : X -> Y)
  证明: memHolder_const

@[simp]

Depends on / 依赖: memHolder_const
-/
lemma memHolder_const' {c : Y} : MemHolder r (fun _ => c : X -> Y) :=
  memHolder_const

@[simp]
/--
lemma `memHolder_zero` / 引理 `memHolder_zero`

English:
lemma memHolder_zero
  given: [Zero Y]
  statement: MemHolder r (0 : X -> Y)
  proof: memHolder_const

中文:
引理 memHolder_zero
  条件: [Zero Y]
  结论: MemHolder r (0 : X -> Y)
  证明: memHolder_const

Depends on / 依赖: memHolder_const
-/
lemma memHolder_zero [Zero Y] : MemHolder r (0 : X -> Y) :=
  memHolder_const

section Monotonicity

open Bornology

/--
lemma `MemHolder.of_le` / 引理 `MemHolder.of_le`

English:
lemma MemHolder.of_le
  statement: {X : Type*} [PseudoMetricSpace X] [hX : BoundedSpace X]
  proof: by
  obtain ⟨C, hf⟩ := hf
  obtain ⟨C', hC'⟩ := Metric.boundedSpace_iff_edist.1 hX
  exact ⟨C * C' ^ (r - s : Real),
holderOnWith_univ.1 (holderOnWith_univ.2 hf).of_le (fun x _ y _ => hC' x y) hs⟩

中文:
引理 MemHolder.of_le
  结论: {X : 类型} [PseudoMetricSpace X] [hX : BoundedSpace X]
  证明: by
  obtain ⟨C, hf⟩ := hf
  obtain ⟨C', hC'⟩ := Metric.boundedSpace_iff_edist.1 hX
  exact ⟨C * C' ^ (r - s : Real),
holderOnWith_univ.1 (holderOnWith_univ.2 hf).of_le (fun x _ y _ => hC' x y) hs⟩

Depends on / 依赖: Metric, Metric.boundedSpace_iff_edist, boundedSpace_iff_edist, holderOnWith_univ, of_le
-/
lemma MemHolder.of_le {X : Type*} [PseudoMetricSpace X] [hX : BoundedSpace X]
    {f : X -> Y} {s : Real>=0} (hf : MemHolder r f) (hs : s <= r) :
    MemHolder s f := by
  obtain ⟨C, hf⟩ := hf
  obtain ⟨C', hC'⟩ := Metric.boundedSpace_iff_edist.1 hX
  exact ⟨C * C' ^ (r - s : Real),
holderOnWith_univ.1 (holderOnWith_univ.2 hf).of_le (fun x _ y _ => hC' x y) hs⟩

/--
lemma `MemHolder.of_le'` / 引理 `MemHolder.of_le'`

English:
lemma MemHolder.of_le'
  statement: {s : Real>=0} (hf : MemHolder r f) (hs : s <= r)
  proof: by
  obtain ⟨C, hX⟩ := hX
  let := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y => ne_top_of_le_ne_top ENNReal.coe_ne_top (hX x y)
  have := Metric.boundedSpace_iff_edist.2 ⟨C, hX⟩
  exact hf.of_le hs

中文:
引理 MemHolder.of_le'
  结论: {s : 实数>=0} (hf : MemHolder r f) (hs : s <= r)
  证明: by
  obtain ⟨C, hX⟩ := hX
  let := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y => ne_top_of_le_ne_top ENNReal.coe_ne_top (hX x y)
  have := Metric.boundedSpace_iff_edist.2 ⟨C, hX⟩
  exact hf.of_le hs

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, Metric, Metric.boundedSpace_iff_edist, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpace, boundedSpace_iff_edist, coe_ne_top, hf.of_le, ne_top_of_le_ne_top, of_le, toPseudoMetricSpace
-/
lemma MemHolder.of_le' {s : Real>=0} (hf : MemHolder r f) (hs : s <= r)
    (hX : exists C : Real>=0, forall x y : X, edist x y <= C) :
    MemHolder s f := by
  obtain ⟨C, hX⟩ := hX
  let := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y => ne_top_of_le_ne_top ENNReal.coe_ne_top (hX x y)
  have := Metric.boundedSpace_iff_edist.2 ⟨C, hX⟩
  exact hf.of_le hs

/--
lemma `HolderOnWith.exists_holderOnWith_of_le` / 引理 `HolderOnWith.exists_holderOnWith_of_le`

English:
lemma HolderOnWith.exists_holderOnWith_of_le
  statement: {X : Type*} [PseudoMetricSpace X]
  proof: by
  simp_rw [← HolderWith.restrict_iff] at *
  have : BoundedSpace A := boundedSpace_val_set_iff.2 hA
  exact MemHolder.of_le hf hs

中文:
引理 HolderOnWith.exists_holderOnWith_of_le
  结论: {X : 类型} [PseudoMetricSpace X]
  证明: by
  simp_rw [← HolderWith.restrict_iff] at *
  have : BoundedSpace A := boundedSpace_val_set_iff.2 hA
  exact MemHolder.of_le hf hs

Depends on / 依赖: BoundedSpace, HolderWith, HolderWith.restrict_iff, MemHolder, MemHolder.of_le, boundedSpace_val_set_iff, of_le, restrict_iff, simp_rw
-/
lemma HolderOnWith.exists_holderOnWith_of_le {X : Type*} [PseudoMetricSpace X]
    {f : X -> Y} {s : Real>=0} {A : Set X} (hf : exists C, HolderOnWith C r f A) (hs : s <= r)
    (hA : IsBounded A) : exists C, HolderOnWith C s f A := by
  simp_rw [← HolderWith.restrict_iff] at *
  have : BoundedSpace A := boundedSpace_val_set_iff.2 hA
  exact MemHolder.of_le hf hs

/--
lemma `HolderOnWith.exists_holderOnWith_of_le'` / 引理 `HolderOnWith.exists_holderOnWith_of_le'`

English:
lemma HolderOnWith.exists_holderOnWith_of_le'
  statement: {D s : Real>=0} {A : Set X}
  proof: by
  simp_rw [← HolderWith.restrict_iff] at *
  let := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y : A => ne_top_of_le_ne_top ENNReal.coe_ne_top (hA x.2 y.2)
  have : BoundedSpace A := Metric.boundedSpace_iff_edist.2 ⟨D, fun x y => hA x.2 y.2⟩
  exact MemHolder.of_le hf hs

中文:
引理 HolderOnWith.exists_holderOnWith_of_le'
  结论: {D s : 实数>=0} {A : Set X}
  证明: by
  simp_rw [← HolderWith.restrict_iff] at *
  let := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y : A => ne_top_of_le_ne_top ENNReal.coe_ne_top (hA x.2 y.2)
  have : BoundedSpace A := Metric.boundedSpace_iff_edist.2 ⟨D, fun x y => hA x.2 y.2⟩
  exact MemHolder.of_le hf hs

Depends on / 依赖: BoundedSpace, ENNReal, ENNReal.coe_ne_top, HolderWith, HolderWith.restrict_iff, MemHolder, MemHolder.of_le, Metric, Metric.boundedSpace_iff_edist, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpace, boundedSpace_iff_edist, coe_ne_top, ne_top_of_le_ne_top, of_le, restrict_iff, simp_rw, toPseudoMetricSpace
-/
lemma HolderOnWith.exists_holderOnWith_of_le' {D s : Real>=0} {A : Set X}
    (hf : exists C, HolderOnWith C r f A) (hs : s <= r)
    (hA : forall ⦃x⦄, x in A -> forall ⦃y⦄, y in A -> edist x y <= D) :
    exists C, HolderOnWith C s f A := by
  simp_rw [← HolderWith.restrict_iff] at *
  let := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y : A => ne_top_of_le_ne_top ENNReal.coe_ne_top (hA x.2 y.2)
  have : BoundedSpace A := Metric.boundedSpace_iff_edist.2 ⟨D, fun x y => hA x.2 y.2⟩
  exact MemHolder.of_le hf hs

/--
lemma `HolderOnWith.exists_holderOnWith_of_le_of_le` / 引理 `HolderOnWith.exists_holderOnWith_of_le_of_le`

English:
lemma HolderOnWith.exists_holderOnWith_of_le_of_le
  statement: {s t : Real>=0} {A : Set X}
  proof: by
  obtain ⟨C₁, hf₁⟩ := hf₁
  obtain ⟨C₂, hf₂⟩ := hf₂
  exact ⟨max C₁ C₂, hf₁.of_le_of_le hf₂ hrs hst⟩

中文:
引理 HolderOnWith.exists_holderOnWith_of_le_of_le
  结论: {s t : 实数>=0} {A : Set X}
  证明: by
  obtain ⟨C₁, hf₁⟩ := hf₁
  obtain ⟨C₂, hf₂⟩ := hf₂
  exact ⟨max C₁ C₂, hf₁.of_le_of_le hf₂ hrs hst⟩

Depends on / 依赖: of_le_of_le
-/
lemma HolderOnWith.exists_holderOnWith_of_le_of_le {s t : Real>=0} {A : Set X}
    (hf₁ : exists C, HolderOnWith C r f A) (hf₂ : exists C, HolderOnWith C t f A)
    (hrs : r <= s) (hst : s <= t) : exists C, HolderOnWith C s f A := by
  obtain ⟨C₁, hf₁⟩ := hf₁
  obtain ⟨C₂, hf₂⟩ := hf₂
  exact ⟨max C₁ C₂, hf₁.of_le_of_le hf₂ hrs hst⟩

/--
lemma `MemHolder.memHolder_of_le_of_le` / 引理 `MemHolder.memHolder_of_le_of_le`

English:
lemma MemHolder.memHolder_of_le_of_le
  statement: {s t : Real>=0} (hf₁ : MemHolder r f) (hf₂ : MemHolder t f)
  proof: by
  simp_rw [MemHolder, ← holderOnWith_univ] at *
  exact HolderOnWith.exists_holderOnWith_of_le_of_le hf₁ hf₂ hrs hst

中文:
引理 MemHolder.memHolder_of_le_of_le
  结论: {s t : 实数>=0} (hf₁ : MemHolder r f) (hf₂ : MemHolder t f)
  证明: by
  simp_rw [MemHolder, ← holderOnWith_univ] at *
  exact HolderOnWith.exists_holderOnWith_of_le_of_le hf₁ hf₂ hrs hst

Depends on / 依赖: HolderOnWith, HolderOnWith.exists_holderOnWith_of_le_of_le, MemHolder, exists_holderOnWith_of_le_of_le, holderOnWith_univ, simp_rw
-/
lemma MemHolder.memHolder_of_le_of_le {s t : Real>=0} (hf₁ : MemHolder r f) (hf₂ : MemHolder t f)
    (hrs : r <= s) (hst : s <= t) : MemHolder s f := by
  simp_rw [MemHolder, ← holderOnWith_univ] at *
  exact HolderOnWith.exists_holderOnWith_of_le_of_le hf₁ hf₂ hrs hst

end Monotonicity

end PseudoEMetricSpace

section MetricSpace

variable [MetricSpace X] [EMetricSpace Y]

/--
lemma `eHolderNorm_eq_zero` / 引理 `eHolderNorm_eq_zero`

English:
lemma eHolderNorm_eq_zero
  given: {r : Real>=0} {f : X -> Y}
  proof: by
  constructor
  · intro h x₁ x₂
    by_cases hx : x₁ = x₂
    · rw [hx]
    · rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot] at h
      rw [← edist_eq_zero]; rw [← nonpos_iff_eq_zero]
      refine le_of_forall_gt fun b hb => ?_
      obtain ⟨C, hC, hC'⟩ := h (b / edist x₁ x₂ ^ (r : Real))


中文:
引理 eHolderNorm_eq_zero
  条件: {r : 实数>=0} {f : X -> Y}
  证明: by
  constructor
  · intro h x₁ x₂
    by_cases hx : x₁ = x₂
    · rw [hx]
    · rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot] at h
      rw [← edist_eq_zero]; rw [← nonpos_iff_eq_zero]
      refine le_of_forall_gt fun b hb => ?_
      obtain ⟨C, hC, hC'⟩ := h (b / edist x₁ x₂ ^ (r : Real))


Depends on / 依赖: ENNReal, ENNReal.bot_eq_zero, ENNReal.div_pos, ENNReal.mul_lt_of_lt_div, ENNReal.rpow_lt_top_of_nonneg, bot_eq_zero, div_pos, eHolderNorm, eHolderNorm_o, edist_eq_zero, edist_lt_top, hb.ne.symm, isEmpty_or_nonempty, le_of_forall_gt, lt_of_le_of_lt, mul_lt_of_lt_div, nonpos_iff_eq_zero, rpow_lt_top_of_nonneg, zero_le_coe
-/
lemma eHolderNorm_eq_zero {r : Real>=0} {f : X -> Y} :
    eHolderNorm r f = 0 ↔ forall x₁ x₂, f x₁ = f x₂ := by
  constructor
  · intro h x₁ x₂
    by_cases hx : x₁ = x₂
    · rw [hx]
    · rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot] at h
      rw [← edist_eq_zero]; rw [← nonpos_iff_eq_zero]
      refine le_of_forall_gt fun b hb => ?_
      obtain ⟨C, hC, hC'⟩ := h (b / edist x₁ x₂ ^ (r : Real))
        (ENNReal.div_pos hb.ne.symm (ENNReal.rpow_lt_top_of_nonneg zero_le_coe
          (edist_lt_top x₁ x₂).ne).ne)
exact lt_of_le_of_lt (hC x₁ x₂) ENNReal.mul_lt_of_lt_div hC'
  · intro h
    rcases isEmpty_or_nonempty X with hX | hX
    · exact eHolderNorm_of_isEmpty
    · rw [← eHolderNorm_const X r (f hX.some)]
      congr
      simp [funext_iff, h _ hX.some]

/--
lemma `MemHolder.holderWith` / 引理 `MemHolder.holderWith`

English:
lemma MemHolder.holderWith
  given: {r : Real>=0} {f : X -> Y} (hf : MemHolder r f)
  proof: by
  intro x₁ x₂
  by_cases hx : x₁ = x₂
  · simp only [hx, edist_self, zero_le]
  rw [nnHolderNorm]; rw [eHolderNorm]; rw [coe_toNNReal]
  on_goal 2 => exact hf.eHolderNorm_lt_top.ne
  have h₁ : edist x₁ x₂ ^ (r : Real) != 0 :=
    (Ne.symm <| ne_of_lt <| ENNReal.rpow_pos (edist_pos.2 hx) (edist_lt

中文:
引理 MemHolder.holderWith
  条件: {r : 实数>=0} {f : X -> Y} (hf : MemHolder r f)
  证明: by
  intro x₁ x₂
  by_cases hx : x₁ = x₂
  · simp only [hx, edist_self, zero_le]
  rw [nnHolderNorm]; rw [eHolderNorm]; rw [coe_toNNReal]
  on_goal 2 => exact hf.eHolderNorm_lt_top.ne
  have h₁ : edist x₁ x₂ ^ (r : Real) != 0 :=
    (Ne.symm <| ne_of_lt <| ENNReal.rpow_pos (edist_pos.2 hx) (edist_lt

Depends on / 依赖: ENNReal, ENNReal.div_le_iff, ENNReal.rpow_pos, Ne.symm, coe_toNNReal, div_le_iff, eHolderNorm, eHolderNorm_lt_top, edist_lt_top, edist_pos, edist_self, hf.eHolderNorm_lt_top.ne, ne_of_lt, nnHolderNorm, on_goal, rpow_pos, zero_le
-/
lemma MemHolder.holderWith {r : Real>=0} {f : X -> Y} (hf : MemHolder r f) :
    HolderWith (nnHolderNorm r f) r f := by
  intro x₁ x₂
  by_cases hx : x₁ = x₂
  · simp only [hx, edist_self, zero_le]
  rw [nnHolderNorm]; rw [eHolderNorm]; rw [coe_toNNReal]
  on_goal 2 => exact hf.eHolderNorm_lt_top.ne
  have h₁ : edist x₁ x₂ ^ (r : Real) != 0 :=
    (Ne.symm <| ne_of_lt <| ENNReal.rpow_pos (edist_pos.2 hx) (edist_lt_top x₁ x₂).ne)
  have h₂ : edist x₁ x₂ ^ (r : Real) != ∞ := by
    simp [(edist_lt_top x₁ x₂).ne]
  rw [← ENNReal.div_le_iff h₁ h₂]
  refine le_iInf₂ fun C hC => ?_
  rw [ENNReal.div_le_iff h₁ h₂]
  exact hC x₁ x₂

/--
lemma `memHolder_iff_holderWith` / 引理 `memHolder_iff_holderWith`

English:
lemma memHolder_iff_holderWith
  given: {r : Real>=0} {f : X -> Y}
  proof: ⟨MemHolder.holderWith, HolderWith.memHolder⟩

中文:
引理 memHolder_iff_holderWith
  条件: {r : 实数>=0} {f : X -> Y}
  证明: ⟨MemHolder.holderWith, HolderWith.memHolder⟩

Depends on / 依赖: HolderWith, HolderWith.memHolder, MemHolder, MemHolder.holderWith, holderWith, memHolder
-/
lemma memHolder_iff_holderWith {r : Real>=0} {f : X -> Y} :
    MemHolder r f ↔ HolderWith (nnHolderNorm r f) r f :=
  ⟨MemHolder.holderWith, HolderWith.memHolder⟩

/--
lemma `MemHolder.coe_nnHolderNorm_eq_eHolderNorm` / 引理 `MemHolder.coe_nnHolderNorm_eq_eHolderNorm`

English:
lemma MemHolder.coe_nnHolderNorm_eq_eHolderNorm
  proof: by
  rw [nnHolderNorm]; rw [coe_toNNReal]
exact ne_of_lt lt_of_le_of_lt hf.holderWith.eHolderNorm_le coe_lt_top

中文:
引理 MemHolder.coe_nnHolderNorm_eq_eHolderNorm
  证明: by
  rw [nnHolderNorm]; rw [coe_toNNReal]
exact ne_of_lt lt_of_le_of_lt hf.holderWith.eHolderNorm_le coe_lt_top

Depends on / 依赖: coe_lt_top, coe_toNNReal, eHolderNorm_le, hf.holderWith.eHolderNorm_le, holderWith, lt_of_le_of_lt, ne_of_lt, nnHolderNorm
-/
lemma MemHolder.coe_nnHolderNorm_eq_eHolderNorm
    {r : Real>=0} {f : X -> Y} (hf : MemHolder r f) :
    (nnHolderNorm r f : Real>=0∞) = eHolderNorm r f := by
  rw [nnHolderNorm]; rw [coe_toNNReal]
exact ne_of_lt lt_of_le_of_lt hf.holderWith.eHolderNorm_le coe_lt_top

/--
lemma `HolderWith.nnholderNorm_le` / 引理 `HolderWith.nnholderNorm_le`

English:
lemma HolderWith.nnholderNorm_le
  given: {C r : Real>=0} {f : X -> Y} (hf : HolderWith C r f)
  proof: by
  rw [← ENNReal.coe_le_coe]; rw [hf.memHolder.coe_nnHolderNorm_eq_eHolderNorm]
  exact hf.eHolderNorm_le

中文:
引理 HolderWith.nnholderNorm_le
  条件: {C r : 实数>=0} {f : X -> Y} (hf : HolderWith C r f)
  证明: by
  rw [← ENNReal.coe_le_coe]; rw [hf.memHolder.coe_nnHolderNorm_eq_eHolderNorm]
  exact hf.eHolderNorm_le

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, coe_le_coe, coe_nnHolderNorm_eq_eHolderNorm, eHolderNorm_le, hf.eHolderNorm_le, hf.memHolder.coe_nnHolderNorm_eq_eHolderNorm, memHolder
-/
lemma HolderWith.nnholderNorm_le {C r : Real>=0} {f : X -> Y} (hf : HolderWith C r f) :
    nnHolderNorm r f <= C := by
  rw [← ENNReal.coe_le_coe]; rw [hf.memHolder.coe_nnHolderNorm_eq_eHolderNorm]
  exact hf.eHolderNorm_le

/--
lemma `MemHolder.comp` / 引理 `MemHolder.comp`

English:
lemma MemHolder.comp
  statement: {r s : Real>=0} {Z : Type*} [MetricSpace Z] {f : Z -> X} {g : X -> Y}
  proof: (hg.holderWith.comp hf.holderWith).memHolder

中文:
引理 MemHolder.comp
  结论: {r s : 实数>=0} {Z : 类型} [MetricSpace Z] {f : Z -> X} {g : X -> Y}
  证明: (hg.holderWith.comp hf.holderWith).memHolder

Depends on / 依赖: hf.holderWith, hg.holderWith.comp, holderWith, memHolder
-/
lemma MemHolder.comp {r s : Real>=0} {Z : Type*} [MetricSpace Z] {f : Z -> X} {g : X -> Y}
    (hf : MemHolder r f) (hg : MemHolder s g) : MemHolder (s * r) (g ∘ f) :=
  (hg.holderWith.comp hf.holderWith).memHolder

/--
lemma `MemHolder.nnHolderNorm_eq_zero` / 引理 `MemHolder.nnHolderNorm_eq_zero`

English:
lemma MemHolder.nnHolderNorm_eq_zero
  given: {r : Real>=0} {f : X -> Y} (hf : MemHolder r f)
  proof: by
  rw [← ENNReal.coe_eq_zero]; rw [hf.coe_nnHolderNorm_eq_eHolderNorm]; rw [eHolderNorm_eq_zero]

中文:
引理 MemHolder.nnHolderNorm_eq_zero
  条件: {r : 实数>=0} {f : X -> Y} (hf : MemHolder r f)
  证明: by
  rw [← ENNReal.coe_eq_zero]; rw [hf.coe_nnHolderNorm_eq_eHolderNorm]; rw [eHolderNorm_eq_zero]

Depends on / 依赖: ENNReal, ENNReal.coe_eq_zero, coe_eq_zero, coe_nnHolderNorm_eq_eHolderNorm, eHolderNorm_eq_zero, hf.coe_nnHolderNorm_eq_eHolderNorm
-/
lemma MemHolder.nnHolderNorm_eq_zero {r : Real>=0} {f : X -> Y} (hf : MemHolder r f) :
    nnHolderNorm r f = 0 ↔ forall x₁ x₂, f x₁ = f x₂ := by
  rw [← ENNReal.coe_eq_zero]; rw [hf.coe_nnHolderNorm_eq_eHolderNorm]; rw [eHolderNorm_eq_zero]

end MetricSpace

section SeminormedAddCommGroup

variable [MetricSpace X] [NormedAddCommGroup Y]
variable {r : Real>=0} {f g : X -> Y}

/--
lemma `MemHolder.add` / 引理 `MemHolder.add`

English:
lemma MemHolder.add
  given: (hf : MemHolder r f) (hg : MemHolder r g)
  statement: MemHolder r (f + g)
  proof: (hf.holderWith.add hg.holderWith).memHolder

中文:
引理 MemHolder.add
  条件: (hf : MemHolder r f) (hg : MemHolder r g)
  结论: MemHolder r (f + g)
  证明: (hf.holderWith.add hg.holderWith).memHolder

Depends on / 依赖: hf.holderWith.add, hg.holderWith, holderWith, memHolder
-/
lemma MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder r (f + g) :=
  (hf.holderWith.add hg.holderWith).memHolder

/--
lemma `MemHolder.smul` / 引理 `MemHolder.smul`

English:
lemma MemHolder.smul
  statement: {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBoundedSMul 𝕜 Y]
  proof: (hf.holderWith.smul c).memHolder

中文:
引理 MemHolder.smul
  结论: {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBoundedSMul 𝕜 Y]
  证明: (hf.holderWith.smul c).memHolder

Depends on / 依赖: hf.holderWith.smul, holderWith, memHolder
-/
lemma MemHolder.smul {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBoundedSMul 𝕜 Y]
    {c : 𝕜} (hf : MemHolder r f) : MemHolder r (c • f) :=
  (hf.holderWith.smul c).memHolder

/--
lemma `MemHolder.smul_iff` / 引理 `MemHolder.smul_iff`

English:
lemma MemHolder.smul_iff
  statement: {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [NormSMulClass 𝕜 Y]
  proof: by
  refine ⟨fun ⟨h, hh⟩ => ⟨h * ‖c‖₊⁻¹, ?_⟩, .smul⟩
  rw [← HolderWith.smul_iff _ hc]; rw [inv_mul_cancel_right₀ hc]
  exact hh

中文:
引理 MemHolder.smul_iff
  结论: {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [NormSMulClass 𝕜 Y]
  证明: by
  refine ⟨fun ⟨h, hh⟩ => ⟨h * ‖c‖₊⁻¹, ?_⟩, .smul⟩
  rw [← HolderWith.smul_iff _ hc]; rw [inv_mul_cancel_right₀ hc]
  exact hh

Depends on / 依赖: HolderWith, HolderWith.smul_iff, smul_iff
-/
lemma MemHolder.smul_iff {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [NormSMulClass 𝕜 Y]
    {c : 𝕜} (hc : ‖c‖₊ != 0) : MemHolder r (c • f) ↔ MemHolder r f := by
  refine ⟨fun ⟨h, hh⟩ => ⟨h * ‖c‖₊⁻¹, ?_⟩, .smul⟩
  rw [← HolderWith.smul_iff _ hc]; rw [inv_mul_cancel_right₀ hc]
  exact hh

/--
lemma `MemHolder.nsmul` / 引理 `MemHolder.nsmul`

English:
lemma MemHolder.nsmul
  given: [NormedSpace Real Y] (n : Nat) (hf : MemHolder r f)
  proof: by
  simp [← Nat.cast_smul_eq_nsmul (R := Real), hf.smul]

中文:
引理 MemHolder.nsmul
  条件: [NormedSpace 实数 Y] (n : 自然数) (hf : MemHolder r f)
  证明: by
  simp [← Nat.cast_smul_eq_nsmul (R := Real), hf.smul]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, hf.smul
-/
lemma MemHolder.nsmul [NormedSpace Real Y] (n : Nat) (hf : MemHolder r f) :
    MemHolder r (n • f) := by
  simp [← Nat.cast_smul_eq_nsmul (R := Real), hf.smul]

/--
lemma `MemHolder.nnHolderNorm_add_le` / 引理 `MemHolder.nnHolderNorm_add_le`

English:
lemma MemHolder.nnHolderNorm_add_le
  given: (hf : MemHolder r f) (hg : MemHolder r g)
  proof: (hf.add hg).holderWith.nnholderNorm_le.trans (hf.holderWith.add hg.holderWith).nnholderNorm_le

中文:
引理 MemHolder.nnHolderNorm_add_le
  条件: (hf : MemHolder r f) (hg : MemHolder r g)
  证明: (hf.add hg).holderWith.nnholderNorm_le.trans (hf.holderWith.add hg.holderWith).nnholderNorm_le

Depends on / 依赖: hf.add, hf.holderWith.add, hg.holderWith, holderWith, holderWith.nnholderNorm_le.trans, nnholderNorm_le
-/
lemma MemHolder.nnHolderNorm_add_le (hf : MemHolder r f) (hg : MemHolder r g) :
    nnHolderNorm r (f + g) <= nnHolderNorm r f + nnHolderNorm r g :=
  (hf.add hg).holderWith.nnholderNorm_le.trans (hf.holderWith.add hg.holderWith).nnholderNorm_le

/--
lemma `eHolderNorm_add_le` / 引理 `eHolderNorm_add_le`

English:
lemma eHolderNorm_add_le
  proof: by
  by_cases hfg : MemHolder r f ∧ MemHolder r g
  · obtain ⟨hf, hg⟩ := hfg
    rw [← hf.coe_nnHolderNorm_eq_eHolderNorm]; rw [← hg.coe_nnHolderNorm_eq_eHolderNorm]; rw [← (hf.add hg).coe_nnHolderNorm_eq_eHolderNorm]; rw [← coe_add]; rw [ENNReal.coe_le_coe]
    exact hf.nnHolderNorm_add_le hg
  · r

中文:
引理 eHolderNorm_add_le
  证明: by
  by_cases hfg : MemHolder r f ∧ MemHolder r g
  · obtain ⟨hf, hg⟩ := hfg
    rw [← hf.coe_nnHolderNorm_eq_eHolderNorm]; rw [← hg.coe_nnHolderNorm_eq_eHolderNorm]; rw [← (hf.add hg).coe_nnHolderNorm_eq_eHolderNorm]; rw [← coe_add]; rw [ENNReal.coe_le_coe]
    exact hf.nnHolderNorm_add_le hg
  · r

Depends on / 依赖: Classical, Classical.not_and_iff_not_or_not, ENNReal, ENNReal.coe_le_coe, MemHolder, all_goals, coe_add, coe_le_coe, coe_nnHolderNorm_eq_eHolderNorm, eHolderNorm_eq_top, hf.add, hf.coe_nnHolderNorm_eq_eHolderNorm, hf.nnHolderNorm_add_le, hg.coe_nnHolderNorm_eq_eHolderNorm, nnHolderNorm_add_le, not_and_iff_not_or_not
-/
lemma eHolderNorm_add_le :
    eHolderNorm r (f + g) <= eHolderNorm r f + eHolderNorm r g := by
  by_cases hfg : MemHolder r f ∧ MemHolder r g
  · obtain ⟨hf, hg⟩ := hfg
    rw [← hf.coe_nnHolderNorm_eq_eHolderNorm]; rw [← hg.coe_nnHolderNorm_eq_eHolderNorm]; rw [← (hf.add hg).coe_nnHolderNorm_eq_eHolderNorm]; rw [← coe_add]; rw [ENNReal.coe_le_coe]
    exact hf.nnHolderNorm_add_le hg
  · rw [Classical.not_and_iff_not_or_not, ← eHolderNorm_eq_top, ← eHolderNorm_eq_top] at hfg
    obtain (h | h) := hfg
    all_goals simp [h]

/--
lemma `eHolderNorm_smul` / 引理 `eHolderNorm_smul`

English:
lemma eHolderNorm_smul
  given: {α} [NormedRing α] [Module α Y] [NormSMulClass α Y] (c : α)
  proof: by
  by_cases hc : ‖c‖₊ = 0
  · rw [nnnorm_eq_zero] at hc
    simp [hc]
  by_cases hf : MemHolder r f
· refine le_antisymm ((hf.holderWith.smul c).eHolderNorm_le.trans ?_) mul_le_of_le_div' ?_
    · rw [coe_mul, hf.coe_nnHolderNorm_eq_eHolderNorm, mul_comm]
    · rw [← (hf.holderWith.smul c).memHold

中文:
引理 eHolderNorm_smul
  条件: {α} [NormedRing α] [Module α Y] [NormSMulClass α Y] (c : α)
  证明: by
  by_cases hc : ‖c‖₊ = 0
  · rw [nnnorm_eq_zero] at hc
    simp [hc]
  by_cases hf : MemHolder r f
· refine le_antisymm ((hf.holderWith.smul c).eHolderNorm_le.trans ?_) mul_le_of_le_div' ?_
    · rw [coe_mul, hf.coe_nnHolderNorm_eq_eHolderNorm, mul_comm]
    · rw [← (hf.holderWith.smul c).memHold

Depends on / 依赖: ENNReal, ENNReal.le_div_iff_mul_le, ENNReal.mul_div_right_comm, HolderWith, HolderWith.eHolderNorm_le, MemHolder, Or.inl, coe_div, coe_mul, coe_ne_zero, coe_nnHolderNorm_eq_eHolderNorm, eHolderNorm_le, eHolderNorm_le.trans, hf.coe_nnHolderNorm_eq_eHolderNorm, hf.holderWith.smul, holderWith, le_antisymm, le_div_iff_mul_le, memHolder, memHolder.coe_nnHolderNorm_eq_eHolderNorm
-/
lemma eHolderNorm_smul {α} [NormedRing α] [Module α Y] [NormSMulClass α Y] (c : α) :
    eHolderNorm r (c • f) = ‖c‖₊ * eHolderNorm r f := by
  by_cases hc : ‖c‖₊ = 0
  · rw [nnnorm_eq_zero] at hc
    simp [hc]
  by_cases hf : MemHolder r f
· refine le_antisymm ((hf.holderWith.smul c).eHolderNorm_le.trans ?_) mul_le_of_le_div' ?_
    · rw [coe_mul, hf.coe_nnHolderNorm_eq_eHolderNorm, mul_comm]
    · rw [← (hf.holderWith.smul c).memHolder.coe_nnHolderNorm_eq_eHolderNorm, ← coe_div hc]
      refine HolderWith.eHolderNorm_le fun x₁ x₂ => ?_
      rw [coe_div hc]; rw [← ENNReal.mul_div_right_comm]; rw [ENNReal.le_div_iff_mul_le (Or.inl <| coe_ne_zero.2 hc) Or.inl coe_ne_top]; rw [mul_comm]; rw [← smul_eq_mul]; rw [← ENNReal.smul_def]; rw [← edist_smul₀]; rw [← Pi.smul_apply]; rw [← Pi.smul_apply]
      exact hf.smul.holderWith x₁ x₂
  · rw [← eHolderNorm_eq_top] at hf
    rw [hf]; rw [mul_top <| coe_ne_zero.2 hc]; rw [eHolderNorm_eq_top]; rw [MemHolder.smul_iff hc]
    rw [nnnorm_eq_zero] at hc
    intro h
    exact h.eHolderNorm_lt_top.ne hf

/--
lemma `MemHolder.nnHolderNorm_smul` / 引理 `MemHolder.nnHolderNorm_smul`

English:
lemma MemHolder.nnHolderNorm_smul
  statement: {α} [NormedRing α] [Module α Y] [NormSMulClass α Y]
  proof: by
  rw [← ENNReal.coe_inj]; rw [coe_mul]; rw [hf.coe_nnHolderNorm_eq_eHolderNorm]; rw [hf.smul.coe_nnHolderNorm_eq_eHolderNorm]; rw [eHolderNorm_smul]

中文:
引理 MemHolder.nnHolderNorm_smul
  结论: {α} [NormedRing α] [Module α Y] [NormSMulClass α Y]
  证明: by
  rw [← ENNReal.coe_inj]; rw [coe_mul]; rw [hf.coe_nnHolderNorm_eq_eHolderNorm]; rw [hf.smul.coe_nnHolderNorm_eq_eHolderNorm]; rw [eHolderNorm_smul]

Depends on / 依赖: ENNReal, ENNReal.coe_inj, coe_inj, coe_mul, coe_nnHolderNorm_eq_eHolderNorm, eHolderNorm_smul, hf.coe_nnHolderNorm_eq_eHolderNorm, hf.smul.coe_nnHolderNorm_eq_eHolderNorm
-/
lemma MemHolder.nnHolderNorm_smul {α} [NormedRing α] [Module α Y] [NormSMulClass α Y]
    (hf : MemHolder r f) (c : α) :
    nnHolderNorm r (c • f) = ‖c‖₊ * nnHolderNorm r f := by
  rw [← ENNReal.coe_inj]; rw [coe_mul]; rw [hf.coe_nnHolderNorm_eq_eHolderNorm]; rw [hf.smul.coe_nnHolderNorm_eq_eHolderNorm]; rw [eHolderNorm_smul]

/--
lemma `eHolderNorm_nsmul` / 引理 `eHolderNorm_nsmul`

English:
lemma eHolderNorm_nsmul
  given: [NormedSpace Real Y] (n : Nat)
  proof: by
  simp [← Nat.cast_smul_eq_nsmul (R := Real), eHolderNorm_smul]

中文:
引理 eHolderNorm_nsmul
  条件: [NormedSpace 实数 Y] (n : 自然数)
  证明: by
  simp [← Nat.cast_smul_eq_nsmul (R := Real), eHolderNorm_smul]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, eHolderNorm_smul
-/
lemma eHolderNorm_nsmul [NormedSpace Real Y] (n : Nat) :
    eHolderNorm r (n • f) = n • eHolderNorm r f := by
  simp [← Nat.cast_smul_eq_nsmul (R := Real), eHolderNorm_smul]

/--
lemma `MemHolder.nnHolderNorm_nsmul` / 引理 `MemHolder.nnHolderNorm_nsmul`

English:
lemma MemHolder.nnHolderNorm_nsmul
  given: [NormedSpace Real Y] (n : Nat) (hf : MemHolder r f)
  proof: by
  simp [← Nat.cast_smul_eq_nsmul (R := Real), hf.nnHolderNorm_smul]

中文:
引理 MemHolder.nnHolderNorm_nsmul
  条件: [NormedSpace 实数 Y] (n : 自然数) (hf : MemHolder r f)
  证明: by
  simp [← Nat.cast_smul_eq_nsmul (R := Real), hf.nnHolderNorm_smul]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, hf.nnHolderNorm_smul, nnHolderNorm_smul
-/
lemma MemHolder.nnHolderNorm_nsmul [NormedSpace Real Y] (n : Nat) (hf : MemHolder r f) :
    nnHolderNorm r (n • f) = n • nnHolderNorm r f := by
  simp [← Nat.cast_smul_eq_nsmul (R := Real), hf.nnHolderNorm_smul]

end SeminormedAddCommGroup
