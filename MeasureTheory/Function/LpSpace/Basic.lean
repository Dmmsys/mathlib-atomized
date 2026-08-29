/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Lp space

This file provides the space `Lp E p μ` as the subtype of elements of `α →ₘ[μ] E`
(see `MeasureTheory.AEEqFun`) such that `eLpNorm f p μ` is finite.
For `1 ≤ p`, `eLpNorm` defines a norm and `Lp` is a complete metric space
(the latter is proved at `Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`).

## Main definitions

* `Lp E p μ` : elements of `α →ₘ[μ] E` such that `eLpNorm f p μ` is finite.
  Defined as an `AddSubgroup` of `α →ₘ[μ] E`.

Lipschitz functions vanishing at zero act by composition on `Lp`. We define this action, and prove
that it is continuous. In particular,
* `ContinuousLinearMap.compLp` defines the action on `Lp` of a continuous linear map.
* `Lp.posPart` is the positive part of an `Lp` function.
* `Lp.negPart` is the negative part of an `Lp` function.

## Notation

* `α →₁[μ] E` : the type `Lp E 1 μ`.
* `α →₂[μ] E` : the type `Lp E 2 μ`.

## Implementation

Since `Lp` is defined as an `AddSubgroup`, dot notation does not work. Use `Lp.Measurable f` to
say that the coercion of `f` to a genuine function is measurable, instead of the non-working
`f.Measurable`.

To prove that two `Lp` elements are equal, it suffices to show that their coercions to functions
coincide almost everywhere (this is registered as an `ext` rule). This can often be done using
`filter_upwards`. For instance, a proof from first principles that `f + (g + h) = (f + g) + h`
could read (in the `Lp` namespace)
```
example (f g h : Lp E p μ) : (f + g) + h = f + (g + h) := by
  ext1
  filter_upwards [coeFn_add (f + g) h, coeFn_add f g, coeFn_add f (g + h), coeFn_add g h]
    with _ ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, add_assoc]
```
The lemma `coeFn_add` states that the coercion of `f + g` coincides almost everywhere with the sum
of the coercions of `f` and `g`. All such lemmas use `coeFn` in their name, to distinguish the
function coercion from the coercion to almost everywhere defined functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

variable {α 𝕜 𝕜' E F : Type*} {m : MeasurableSpace α} {p : Real>=0∞} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace MeasureTheory

/-!
### Lp space

The space of equivalence classes of measurable functions for which `eLpNorm f p μ < ∞`.
-/

@[simp]
/--
theorem `eLpNorm_aeeqFun` / 定理 `eLpNorm_aeeqFun`

English:
theorem eLpNorm_aeeqFun
  statement: {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  proof: eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)

中文:
定理 eLpNorm_aeeqFun
  结论: {α E : 类型} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  证明: eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_mk, coeFn_mk, eLpNorm_congr_ae
-/
theorem eLpNorm_aeeqFun {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {p : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (AEEqFun.mk f hf) p μ = eLpNorm f p μ :=
  eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)

/--
theorem `MemLp.eLpNorm_mk_lt_top` / 定理 `MemLp.eLpNorm_mk_lt_top`

English:
theorem MemLp.eLpNorm_mk_lt_top
  statement: {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  proof: by simp [hfp.2]

中文:
定理 MemLp.eLpNorm_mk_lt_top
  结论: {α E : 类型} [MeasurableSpace α] {μ : Measure α}
  证明: by simp [hfp.2]
-/
theorem MemLp.eLpNorm_mk_lt_top {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : Real>=0∞} {f : α -> E} (hfp : MemLp f p μ) :
    eLpNorm (AEEqFun.mk f hfp.1) p μ < ∞ := by simp [hfp.2]

/--
Definition of `Lp` / `Lp` 的定义

English:
definition Lp
  signature: {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : Real>=0∞)
  body: { f | eLpNorm f p μ < ∞ }
  zero_mem' := by simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]
  add_mem' {f g} hf hg := by
    simp [eLpNorm_congr_ae (AEEqFun.coeFn_add f g),
      eLpNorm_add_lt_top ⟨f.aestronglyMeasurable, hf⟩ ⟨g.aestronglyMeasurable, hg⟩]
  neg_mem' {f} hf := by rwa [Set.m

中文:
定义 Lp
  签名: {α} (E : 类型) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : 实数>=0∞)
  定义体: { f | eLpNorm f p μ < ∞ }
  zero_mem' := by simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]
  add_mem' {f g} hf hg := by
    simp [eLpNorm_congr_ae (AEEqFun.coeFn_add f g),
      eLpNorm_add_lt_top ⟨f.aestronglyMeasurable, hf⟩ ⟨g.aestronglyMeasurable, hg⟩]
  neg_mem' {f} hf := by rwa [Set.m

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_add, AEEqFun.coeFn_neg, AEEqFun.coeFn_zero, AddSubgroup, Set.mem_ofPred_eq, add_mem, aestronglyMeasurable, carrier, coeFn_add, coeFn_neg, coeFn_zero, eLpNorm, eLpNorm_add_lt_top, eLpNorm_congr_ae, eLpNorm_neg, eLpNorm_zero, f.aestronglyMeasurable, g.aestronglyMeasurable, mem_ofPred_eq
-/
def Lp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : Real>=0∞)
    (μ : Measure α := by volume_tac) : AddSubgroup (α ->ₘ[μ] E) where
  carrier := { f | eLpNorm f p μ < ∞ }
  zero_mem' := by simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]
  add_mem' {f g} hf hg := by
    simp [eLpNorm_congr_ae (AEEqFun.coeFn_add f g),
      eLpNorm_add_lt_top ⟨f.aestronglyMeasurable, hf⟩ ⟨g.aestronglyMeasurable, hg⟩]
  neg_mem' {f} hf := by rwa [Set.mem_ofPred_eq, eLpNorm_congr_ae (AEEqFun.coeFn_neg f), eLpNorm_neg]

/-- `α →₁[μ] E` is the type of `L¹` or integrable functions from `α` to `E`. -/
scoped notation:25 α' " ->₁[" μ "] " E => MeasureTheory.Lp (α := α') E 1 μ
/-- `α →₂[μ] E` is the type of `L²` or square-integrable functions from `α` to `E`. -/
scoped notation:25 α' " ->₂[" μ "] " E => MeasureTheory.Lp (α := α') E 2 μ

namespace MemLp

/--
Definition of `toLp` / `toLp` 的定义

English:
definition toLp
  signature: (f : α -> E) (h_mem_ℒp : MemLp f p μ)
  body: ⟨AEEqFun.mk f h_mem_ℒp.1, h_mem_ℒp.eLpNorm_mk_lt_top⟩

中文:
定义 toLp
  签名: (f : α -> E) (h_mem_ℒp : MemLp f p μ)
  定义体: ⟨AEEqFun.mk f h_mem_ℒp.1, h_mem_ℒp.eLpNorm_mk_lt_top⟩

Depends on / 依赖: AEEqFun, AEEqFun.mk, eLpNorm_mk_lt_top, p.eLpNorm_mk_lt_top
-/
def toLp (f : α -> E) (h_mem_ℒp : MemLp f p μ) : Lp E p μ :=
  ⟨AEEqFun.mk f h_mem_ℒp.1, h_mem_ℒp.eLpNorm_mk_lt_top⟩

/--
theorem `toLp_val` / 定理 `toLp_val`

English:
theorem toLp_val
  given: {f : α -> E} (h : MemLp f p μ)
  statement: (toLp f h).1 = AEEqFun.mk f h.1
  proof: rfl

中文:
定理 toLp_val
  条件: {f : α -> E} (h : MemLp f p μ)
  结论: (toLp f h).1 = AEEqFun.mk f h.1
  证明: rfl
-/
theorem toLp_val {f : α -> E} (h : MemLp f p μ) : (toLp f h).1 = AEEqFun.mk f h.1 := rfl

/--
theorem `coeFn_toLp` / 定理 `coeFn_toLp`

English:
theorem coeFn_toLp
  given: {f : α -> E} (hf : MemLp f p μ)
  statement: hf.toLp f =ᵐ[μ] f
  proof: AEEqFun.coeFn_mk _ _

中文:
定理 coeFn_toLp
  条件: {f : α -> E} (hf : MemLp f p μ)
  结论: hf.toLp f =ᵐ[μ] f
  证明: AEEqFun.coeFn_mk _ _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_mk, coeFn_mk
-/
theorem coeFn_toLp {f : α -> E} (hf : MemLp f p μ) : hf.toLp f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toLp_congr` / 定理 `toLp_congr`

English:
theorem toLp_congr
  given: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g)
  proof: by simp [toLp, hfg]

中文:
定理 toLp_congr
  条件: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g)
  证明: by simp [toLp, hfg]
-/
theorem toLp_congr {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) :
    hf.toLp f = hg.toLp g := by simp [toLp, hfg]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `toLp_eq_toLp_iff` / 定理 `toLp_eq_toLp_iff`

English:
theorem toLp_eq_toLp_iff
  given: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  proof: by simp [toLp]

@[simp]

中文:
定理 toLp_eq_toLp_iff
  条件: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  证明: by simp [toLp]

@[simp]
-/
theorem toLp_eq_toLp_iff {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    hf.toLp f = hg.toLp g ↔ f =ᵐ[μ] g := by simp [toLp]

@[simp]
/--
theorem `toLp_zero` / 定理 `toLp_zero`

English:
theorem toLp_zero
  given: (h : MemLp (0 : α -> E) p μ)
  statement: h.toLp 0 = 0
  proof: rfl

中文:
定理 toLp_zero
  条件: (h : MemLp (0 : α -> E) p μ)
  结论: h.toLp 0 = 0
  证明: rfl
-/
theorem toLp_zero (h : MemLp (0 : α -> E) p μ) : h.toLp 0 = 0 :=
  rfl

/--
theorem `toLp_add` / 定理 `toLp_add`

English:
theorem toLp_add
  given: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  proof: rfl

中文:
定理 toLp_add
  条件: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  证明: rfl
-/
theorem toLp_add {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    (hf.add hg).toLp (f + g) = hf.toLp f + hg.toLp g :=
  rfl

/--
theorem `toLp_neg` / 定理 `toLp_neg`

English:
theorem toLp_neg
  given: {f : α -> E} (hf : MemLp f p μ)
  statement: hf.neg.toLp (-f) = -hf.toLp f
  proof: rfl

中文:
定理 toLp_neg
  条件: {f : α -> E} (hf : MemLp f p μ)
  结论: hf.neg.toLp (-f) = -hf.toLp f
  证明: rfl
-/
theorem toLp_neg {f : α -> E} (hf : MemLp f p μ) : hf.neg.toLp (-f) = -hf.toLp f :=
  rfl

/--
theorem `toLp_sub` / 定理 `toLp_sub`

English:
theorem toLp_sub
  given: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  proof: rfl

中文:
定理 toLp_sub
  条件: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  证明: rfl
-/
theorem toLp_sub {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    (hf.sub hg).toLp (f - g) = hf.toLp f - hg.toLp g :=
  rfl

end MemLp

namespace Lp

/--
Instance `instCoeFun` / 实例 `instCoeFun`

English:
instance instCoeFun
  signature: : CoeFun (Lp E p μ) (fun _ => α -> E)
  body: ⟨fun f => ((f : α ->ₘ[μ] E) : α -> E)⟩

@[ext high]

中文:
实例 instCoeFun
  签名: : CoeFun (Lp E p μ) (fun _ => α -> E)
  定义体: ⟨fun f => ((f : α ->ₘ[μ] E) : α -> E)⟩

@[ext high]
-/
instance instCoeFun : CoeFun (Lp E p μ) (fun _ => α -> E) :=
  ⟨fun f => ((f : α ->ₘ[μ] E) : α -> E)⟩

@[ext high]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : Lp E p μ} (h : f =ᵐ[μ] g)
  statement: f = g
  proof: by
  ext
  exact h

中文:
定理 ext
  条件: {f g : Lp E p μ} (h : f =ᵐ[μ] g)
  结论: f = g
  证明: by
  ext
  exact h
-/
theorem ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g := by
  ext
  exact h

/--
theorem `mem_Lp_iff_eLpNorm_lt_top` / 定理 `mem_Lp_iff_eLpNorm_lt_top`

English:
theorem mem_Lp_iff_eLpNorm_lt_top
  given: {f : α ->ₘ[μ] E}
  statement: f in Lp E p μ ↔ eLpNorm f p μ < ∞
  proof: Iff.rfl

中文:
定理 mem_Lp_iff_eLpNorm_lt_top
  条件: {f : α ->ₘ[μ] E}
  结论: f in Lp E p μ ↔ eLpNorm f p μ < ∞
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_Lp_iff_eLpNorm_lt_top {f : α ->ₘ[μ] E} : f in Lp E p μ ↔ eLpNorm f p μ < ∞ := Iff.rfl

/--
theorem `mem_Lp_iff_memLp` / 定理 `mem_Lp_iff_memLp`

English:
theorem mem_Lp_iff_memLp
  given: {f : α ->ₘ[μ] E}
  statement: f in Lp E p μ ↔ MemLp f p μ
  proof: by
  simp [mem_Lp_iff_eLpNorm_lt_top, MemLp, f.stronglyMeasurable.aestronglyMeasurable]

中文:
定理 mem_Lp_iff_memLp
  条件: {f : α ->ₘ[μ] E}
  结论: f in Lp E p μ ↔ MemLp f p μ
  证明: by
  simp [mem_Lp_iff_eLpNorm_lt_top, MemLp, f.stronglyMeasurable.aestronglyMeasurable]

Depends on / 依赖: aestronglyMeasurable, f.stronglyMeasurable.aestronglyMeasurable, mem_Lp_iff_eLpNorm_lt_top, stronglyMeasurable
-/
theorem mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f in Lp E p μ ↔ MemLp f p μ := by
  simp [mem_Lp_iff_eLpNorm_lt_top, MemLp, f.stronglyMeasurable.aestronglyMeasurable]

/--
theorem `antitone` / 定理 `antitone`

English:
theorem antitone
  given: [IsFiniteMeasure μ] {p q : Real>=0∞} (hpq : p <= q)
  statement: Lp E q μ <= Lp E p μ
  proof: fun f hf => (MemLp.mono_exponent ⟨f.aestronglyMeasurable, hf⟩ hpq).2

@[simp]

中文:
定理 antitone
  条件: [IsFiniteMeasure μ] {p q : 实数>=0∞} (hpq : p <= q)
  结论: Lp E q μ <= Lp E p μ
  证明: fun f hf => (MemLp.mono_exponent ⟨f.aestronglyMeasurable, hf⟩ hpq).2

@[simp]
-/
protected theorem antitone [IsFiniteMeasure μ] {p q : Real>=0∞} (hpq : p <= q) : Lp E q μ <= Lp E p μ :=
  fun f hf => (MemLp.mono_exponent ⟨f.aestronglyMeasurable, hf⟩ hpq).2

@[simp]
/--
theorem `coeFn_mk` / 定理 `coeFn_mk`

English:
theorem coeFn_mk
  given: {f : α ->ₘ[μ] E} (hf : eLpNorm f p μ < ∞)
  statement: ((⟨f, hf⟩ : Lp E p μ) : α -> E) = f
  proof: rfl

中文:
定理 coeFn_mk
  条件: {f : α ->ₘ[μ] E} (hf : eLpNorm f p μ < ∞)
  结论: ((⟨f, hf⟩ : Lp E p μ) : α -> E) = f
  证明: rfl
-/
theorem coeFn_mk {f : α ->ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α -> E) = f :=
  rfl

-- not @[simp] because dsimp can prove this
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {f : α ->ₘ[μ] E} (hf : eLpNorm f p μ < ∞)
  statement: ((⟨f, hf⟩ : Lp E p μ) : α ->ₘ[μ] E) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: {f : α ->ₘ[μ] E} (hf : eLpNorm f p μ < ∞)
  结论: ((⟨f, hf⟩ : Lp E p μ) : α ->ₘ[μ] E) = f
  证明: rfl

@[simp]
-/
theorem coe_mk {f : α ->ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α ->ₘ[μ] E) = f :=
  rfl

@[simp]
/--
theorem `toLp_coeFn` / 定理 `toLp_coeFn`

English:
theorem toLp_coeFn
  given: (f : Lp E p μ) (hf : MemLp f p μ)
  statement: hf.toLp f = f
  proof: by
  simp [MemLp.toLp]

中文:
定理 toLp_coeFn
  条件: (f : Lp E p μ) (hf : MemLp f p μ)
  结论: hf.toLp f = f
  证明: by
  simp [MemLp.toLp]

Depends on / 依赖: MemLp.toLp
-/
theorem toLp_coeFn (f : Lp E p μ) (hf : MemLp f p μ) : hf.toLp f = f := by
  simp [MemLp.toLp]

/--
theorem `eLpNorm_lt_top` / 定理 `eLpNorm_lt_top`

English:
theorem eLpNorm_lt_top
  given: (f : Lp E p μ)
  statement: eLpNorm f p μ < ∞
  proof: f.prop

@[aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 eLpNorm_lt_top
  条件: (f : Lp E p μ)
  结论: eLpNorm f p μ < ∞
  证明: f.prop

@[aesop (rule_sets := [finiteness]) safe apply]

Depends on / 依赖: f.prop
-/
theorem eLpNorm_lt_top (f : Lp E p μ) : eLpNorm f p μ < ∞ :=
  f.prop

@[aesop (rule_sets := [finiteness]) safe apply]
/--
theorem `eLpNorm_ne_top` / 定理 `eLpNorm_ne_top`

English:
theorem eLpNorm_ne_top
  given: (f : Lp E p μ)
  statement: eLpNorm f p μ != ∞
  proof: (eLpNorm_lt_top f).ne

@[fun_prop]

中文:
定理 eLpNorm_ne_top
  条件: (f : Lp E p μ)
  结论: eLpNorm f p μ != ∞
  证明: (eLpNorm_lt_top f).ne

@[fun_prop]

Depends on / 依赖: eLpNorm_lt_top
-/
theorem eLpNorm_ne_top (f : Lp E p μ) : eLpNorm f p μ != ∞ :=
  (eLpNorm_lt_top f).ne

@[fun_prop]
/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  given: (f : Lp E p μ)
  statement: StronglyMeasurable f
  proof: f.val.stronglyMeasurable

@[fun_prop]

中文:
定理 stronglyMeasurable
  条件: (f : Lp E p μ)
  结论: StronglyMeasurable f
  证明: f.val.stronglyMeasurable

@[fun_prop]
-/
protected theorem stronglyMeasurable (f : Lp E p μ) : StronglyMeasurable f :=
  f.val.stronglyMeasurable

@[fun_prop]
/--
theorem `aestronglyMeasurable` / 定理 `aestronglyMeasurable`

English:
theorem aestronglyMeasurable
  given: (f : Lp E p μ)
  statement: AEStronglyMeasurable f μ
  proof: f.val.aestronglyMeasurable

中文:
定理 aestronglyMeasurable
  条件: (f : Lp E p μ)
  结论: AEStronglyMeasurable f μ
  证明: f.val.aestronglyMeasurable
-/
protected theorem aestronglyMeasurable (f : Lp E p μ) : AEStronglyMeasurable f μ :=
  f.val.aestronglyMeasurable

/--
theorem `memLp` / 定理 `memLp`

English:
theorem memLp
  given: (f : Lp E p μ)
  statement: MemLp f p μ
  proof: ⟨Lp.aestronglyMeasurable f, f.prop⟩

中文:
定理 memLp
  条件: (f : Lp E p μ)
  结论: MemLp f p μ
  证明: ⟨Lp.aestronglyMeasurable f, f.prop⟩
-/
protected theorem memLp (f : Lp E p μ) : MemLp f p μ :=
  ⟨Lp.aestronglyMeasurable f, f.prop⟩

variable (E p μ)

/--
theorem `coeFn_zero` / 定理 `coeFn_zero`

English:
theorem coeFn_zero
  statement: ⇑(0 : Lp E p μ) =ᵐ[μ] 0
  proof: AEEqFun.coeFn_zero

中文:
定理 coeFn_zero
  结论: ⇑(0 : Lp E p μ) =ᵐ[μ] 0
  证明: AEEqFun.coeFn_zero

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_zero, coeFn_zero
-/
theorem coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0 :=
  AEEqFun.coeFn_zero

variable {E p μ}

/--
theorem `coeFn_neg` / 定理 `coeFn_neg`

English:
theorem coeFn_neg
  given: (f : Lp E p μ)
  statement: ⇑(-f) =ᵐ[μ] -f
  proof: AEEqFun.coeFn_neg _

中文:
定理 coeFn_neg
  条件: (f : Lp E p μ)
  结论: ⇑(-f) =ᵐ[μ] -f
  证明: AEEqFun.coeFn_neg _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_neg, coeFn_neg
-/
theorem coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f :=
  AEEqFun.coeFn_neg _

/--
theorem `coeFn_add` / 定理 `coeFn_add`

English:
theorem coeFn_add
  given: (f g : Lp E p μ)
  statement: ⇑(f + g) =ᵐ[μ] f + g
  proof: AEEqFun.coeFn_add _ _

中文:
定理 coeFn_add
  条件: (f g : Lp E p μ)
  结论: ⇑(f + g) =ᵐ[μ] f + g
  证明: AEEqFun.coeFn_add _ _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_add, coeFn_add
-/
theorem coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g :=
  AEEqFun.coeFn_add _ _

/--
theorem `coeFn_sub` / 定理 `coeFn_sub`

English:
theorem coeFn_sub
  given: (f g : Lp E p μ)
  statement: ⇑(f - g) =ᵐ[μ] f - g
  proof: AEEqFun.coeFn_sub _ _

中文:
定理 coeFn_sub
  条件: (f g : Lp E p μ)
  结论: ⇑(f - g) =ᵐ[μ] f - g
  证明: AEEqFun.coeFn_sub _ _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_sub, coeFn_sub
-/
theorem coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g :=
  AEEqFun.coeFn_sub _ _

/--
theorem `coeFn_finsetSum` / 定理 `coeFn_finsetSum`

English:
theorem coeFn_finsetSum
  given: {ι : Type*} (s : Finset ι) (f : ι -> Lp E p μ)
  proof: by
  simp [AEEqFun.coeFn_finsetSum]

中文:
定理 coeFn_finsetSum
  条件: {ι : 类型} (s : Finset ι) (f : ι -> Lp E p μ)
  证明: by
  simp [AEEqFun.coeFn_finsetSum]

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_finsetSum, coeFn_finsetSum
-/
theorem coeFn_finsetSum {ι : Type*} (s : Finset ι) (f : ι -> Lp E p μ) :
    ⇑(∑ i in s, f i) =ᵐ[μ] ∑ i in s, ⇑(f i) := by
  simp [AEEqFun.coeFn_finsetSum]

/--
theorem `coeFn_fun_finsetSum` / 定理 `coeFn_fun_finsetSum`

English:
theorem coeFn_fun_finsetSum
  given: {ι : Type*} (s : Finset ι) (f : ι -> Lp E p μ)
  proof: by
  grw [coeFn_finsetSum]
  filter_upwards with x using by simp

中文:
定理 coeFn_fun_finsetSum
  条件: {ι : 类型} (s : Finset ι) (f : ι -> Lp E p μ)
  证明: by
  grw [coeFn_finsetSum]
  filter_upwards with x using by simp

Depends on / 依赖: coeFn_finsetSum, filter_upwards
-/
theorem coeFn_fun_finsetSum {ι : Type*} (s : Finset ι) (f : ι -> Lp E p μ) :
    ⇑(∑ i in s, f i) =ᵐ[μ] fun x => ∑ i in s, f i x := by
  grw [coeFn_finsetSum]
  filter_upwards with x using by simp

/--
theorem `const_mem_Lp` / 定理 `const_mem_Lp`

English:
theorem const_mem_Lp
  given: (α) {_ : MeasurableSpace α} (μ : Measure α) (c : E) [IsFiniteMeasure μ]
  proof: (memLp_const c).eLpNorm_mk_lt_top

中文:
定理 const_mem_Lp
  条件: (α) {_ : MeasurableSpace α} (μ : Measure α) (c : E) [IsFiniteMeasure μ]
  证明: (memLp_const c).eLpNorm_mk_lt_top

Depends on / 依赖: eLpNorm_mk_lt_top, memLp_const
-/
theorem const_mem_Lp (α) {_ : MeasurableSpace α} (μ : Measure α) (c : E) [IsFiniteMeasure μ] :
    @AEEqFun.const α _ _ μ _ c in Lp E p μ :=
  (memLp_const c).eLpNorm_mk_lt_top

/--
Instance `instNorm` / 实例 `instNorm`

English:
instance instNorm
  signature: : Norm (Lp E p μ) where norm f
  body: ENNReal.toReal (eLpNorm f p μ)

中文:
实例 instNorm
  签名: : Norm (Lp E p μ) where norm f
  定义体: ENNReal.toReal (eLpNorm f p μ)

Depends on / 依赖: ENNReal, ENNReal.toReal, eLpNorm, toReal
-/
instance instNorm : Norm (Lp E p μ) where norm f := ENNReal.toReal (eLpNorm f p μ)

-- note: we need this to be defeq to the instance from `SeminormedAddGroup.toNNNorm`, so
-- can't use `ENNReal.toNNReal (eLpNorm f p μ)`
/--
Instance `instNNNorm` / 实例 `instNNNorm`

English:
instance instNNNorm
  signature: : NNNorm (Lp E p μ) where nnnorm f
  body: .mk ‖f‖ ENNReal.toReal_nonneg

中文:
实例 instNNNorm
  签名: : NNNorm (Lp E p μ) where nnnorm f
  定义体: .mk ‖f‖ ENNReal.toReal_nonneg

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, toReal_nonneg
-/
instance instNNNorm : NNNorm (Lp E p μ) where nnnorm f := .mk ‖f‖ ENNReal.toReal_nonneg

/--
Instance `instDist` / 实例 `instDist`

English:
instance instDist
  signature: : Dist (Lp E p μ) where dist f g
  body: ‖-f + g‖

中文:
实例 instDist
  签名: : Dist (Lp E p μ) where dist f g
  定义体: ‖-f + g‖
-/
instance instDist : Dist (Lp E p μ) where dist f g := ‖-f + g‖

/--
Instance `instEDist` / 实例 `instEDist`

English:
instance instEDist
  signature: : EDist (Lp E p μ) where edist f g
  body: eLpNorm (-⇑f + ⇑g) p μ

中文:
实例 instEDist
  签名: : EDist (Lp E p μ) where edist f g
  定义体: eLpNorm (-⇑f + ⇑g) p μ

Depends on / 依赖: eLpNorm
-/
instance instEDist : EDist (Lp E p μ) where edist f g := eLpNorm (-⇑f + ⇑g) p μ

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (f : Lp E p μ)
  statement: ‖f‖ = ENNReal.toReal (eLpNorm f p μ)
  proof: rfl

中文:
定理 norm_def
  条件: (f : Lp E p μ)
  结论: ‖f‖ = ENN实数.to实数 (eLpNorm f p μ)
  证明: rfl
-/
theorem norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toReal (eLpNorm f p μ) :=
  rfl

/--
theorem `nnnorm_def` / 定理 `nnnorm_def`

English:
theorem nnnorm_def
  given: (f : Lp E p μ)
  statement: ‖f‖₊ = ENNReal.toNNReal (eLpNorm f p μ)
  proof: rfl

@[simp, norm_cast]

中文:
定理 nnnorm_def
  条件: (f : Lp E p μ)
  结论: ‖f‖₊ = ENN实数.toNN实数 (eLpNorm f p μ)
  证明: rfl

@[simp, norm_cast]
-/
theorem nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ENNReal.toNNReal (eLpNorm f p μ) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_nnnorm` / 定理 `coe_nnnorm`

English:
theorem coe_nnnorm
  given: (f : Lp E p μ)
  statement: (‖f‖₊ : Real) = ‖f‖
  proof: rfl

中文:
定理 coe_nnnorm
  条件: (f : Lp E p μ)
  结论: (‖f‖₊ : 实数) = ‖f‖
  证明: rfl
-/
protected theorem coe_nnnorm (f : Lp E p μ) : (‖f‖₊ : Real) = ‖f‖ :=
  rfl

/--
theorem `enorm_def` / 定理 `enorm_def`

English:
theorem enorm_def
  given: (f : Lp E p μ)
  statement: ‖f‖ₑ = eLpNorm f p μ
  proof: ENNReal.coe_toNNReal Lp.eLpNorm_ne_top f

@[simp]

中文:
定理 enorm_def
  条件: (f : Lp E p μ)
  结论: ‖f‖ₑ = eLpNorm f p μ
  证明: ENNReal.coe_toNNReal Lp.eLpNorm_ne_top f

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, Lp.eLpNorm_ne_top, coe_toNNReal, eLpNorm_ne_top
-/
theorem enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f p μ :=
ENNReal.coe_toNNReal Lp.eLpNorm_ne_top f

@[simp]
/--
lemma `norm_toLp` / 引理 `norm_toLp`

English:
lemma norm_toLp
  given: (f : α -> E) (hf : MemLp f p μ)
  statement: ‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ)
  proof: by
  rw [norm_def]; rw [eLpNorm_congr_ae (MemLp.coeFn_toLp hf)]

@[simp]

中文:
引理 norm_toLp
  条件: (f : α -> E) (hf : MemLp f p μ)
  结论: ‖hf.toLp f‖ = ENN实数.to实数 (eLpNorm f p μ)
  证明: by
  rw [norm_def]; rw [eLpNorm_congr_ae (MemLp.coeFn_toLp hf)]

@[simp]

Depends on / 依赖: MemLp.coeFn_toLp, coeFn_toLp, eLpNorm_congr_ae, norm_def
-/
lemma norm_toLp (f : α -> E) (hf : MemLp f p μ) : ‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ) := by
  rw [norm_def]; rw [eLpNorm_congr_ae (MemLp.coeFn_toLp hf)]

@[simp]
/--
theorem `nnnorm_toLp` / 定理 `nnnorm_toLp`

English:
theorem nnnorm_toLp
  given: (f : α -> E) (hf : MemLp f p μ)
  proof: NNReal.eq norm_toLp f hf

@[simp]

中文:
定理 nnnorm_toLp
  条件: (f : α -> E) (hf : MemLp f p μ)
  证明: NNReal.eq norm_toLp f hf

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, norm_toLp
-/
theorem nnnorm_toLp (f : α -> E) (hf : MemLp f p μ) :
    ‖hf.toLp f‖₊ = ENNReal.toNNReal (eLpNorm f p μ) :=
NNReal.eq norm_toLp f hf

@[simp]
/--
lemma `enorm_toLp` / 引理 `enorm_toLp`

English:
lemma enorm_toLp
  given: {f : α -> E} (hf : MemLp f p μ)
  statement: ‖hf.toLp f‖ₑ = eLpNorm f p μ
  proof: by
  simp_rw [enorm, nnnorm_toLp f hf, ENNReal.coe_toNNReal hf.2.ne]

中文:
引理 enorm_toLp
  条件: {f : α -> E} (hf : MemLp f p μ)
  结论: ‖hf.toLp f‖ₑ = eLpNorm f p μ
  证明: by
  simp_rw [enorm, nnnorm_toLp f hf, ENNReal.coe_toNNReal hf.2.ne]

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, coe_toNNReal, nnnorm_toLp, simp_rw
-/
lemma enorm_toLp {f : α -> E} (hf : MemLp f p μ) : ‖hf.toLp f‖ₑ = eLpNorm f p μ := by
  simp_rw [enorm, nnnorm_toLp f hf, ENNReal.coe_toNNReal hf.2.ne]

/--
theorem `dist_eq_eLpNorm_neg_add` / 定理 `dist_eq_eLpNorm_neg_add`

English:
theorem dist_eq_eLpNorm_neg_add
  given: (f g : Lp E p μ)
  statement: dist f g = (eLpNorm (-⇑f + ⇑g) p μ).toReal
  proof: by
  simp_rw [dist, norm_def]
  congr 1
  apply eLpNorm_congr_ae
  exact (coeFn_add _ _).trans ((coeFn_neg f).add ae_eq_rfl)

中文:
定理 dist_eq_eLpNorm_neg_add
  条件: (f g : Lp E p μ)
  结论: dist f g = (eLpNorm (-⇑f + ⇑g) p μ).to实数
  证明: by
  simp_rw [dist, norm_def]
  congr 1
  apply eLpNorm_congr_ae
  exact (coeFn_add _ _).trans ((coeFn_neg f).add ae_eq_rfl)

Depends on / 依赖: ae_eq_rfl, coeFn_add, coeFn_neg, eLpNorm_congr_ae, norm_def, simp_rw
-/
theorem dist_eq_eLpNorm_neg_add (f g : Lp E p μ) : dist f g = (eLpNorm (-⇑f + ⇑g) p μ).toReal := by
  simp_rw [dist, norm_def]
  congr 1
  apply eLpNorm_congr_ae
  exact (coeFn_add _ _).trans ((coeFn_neg f).add ae_eq_rfl)

/--
theorem `dist_def` / 定理 `dist_def`

English:
theorem dist_def
  given: (f g : Lp E p μ)
  statement: dist f g = (eLpNorm (⇑f - ⇑g) p μ).toReal
  proof: by
  rw [dist_eq_eLpNorm_neg_add]; rw [← eLpNorm_neg]; rw [neg_add]; rw [neg_neg]; rw [sub_eq_add_neg]

中文:
定理 dist_def
  条件: (f g : Lp E p μ)
  结论: dist f g = (eLpNorm (⇑f - ⇑g) p μ).to实数
  证明: by
  rw [dist_eq_eLpNorm_neg_add]; rw [← eLpNorm_neg]; rw [neg_add]; rw [neg_neg]; rw [sub_eq_add_neg]

Depends on / 依赖: dist_eq_eLpNorm_neg_add, eLpNorm_neg, neg_add, neg_neg, sub_eq_add_neg
-/
theorem dist_def (f g : Lp E p μ) : dist f g = (eLpNorm (⇑f - ⇑g) p μ).toReal := by
  rw [dist_eq_eLpNorm_neg_add]; rw [← eLpNorm_neg]; rw [neg_add]; rw [neg_neg]; rw [sub_eq_add_neg]

/--
theorem `edist_eq_eLpNorm_neg_add` / 定理 `edist_eq_eLpNorm_neg_add`

English:
theorem edist_eq_eLpNorm_neg_add
  given: (f g : Lp E p μ)
  statement: edist f g = eLpNorm (-⇑f + ⇑g) p μ
  proof: rfl

中文:
定理 edist_eq_eLpNorm_neg_add
  条件: (f g : Lp E p μ)
  结论: edist f g = eLpNorm (-⇑f + ⇑g) p μ
  证明: rfl
-/
theorem edist_eq_eLpNorm_neg_add (f g : Lp E p μ) : edist f g = eLpNorm (-⇑f + ⇑g) p μ := rfl

/--
theorem `edist_def` / 定理 `edist_def`

English:
theorem edist_def
  given: (f g : Lp E p μ)
  statement: edist f g = eLpNorm (⇑f - ⇑g) p μ
  proof: by
  rw [edist_eq_eLpNorm_neg_add]; rw [← eLpNorm_neg]; rw [neg_add]; rw [neg_neg]; rw [sub_eq_add_neg]

中文:
定理 edist_def
  条件: (f g : Lp E p μ)
  结论: edist f g = eLpNorm (⇑f - ⇑g) p μ
  证明: by
  rw [edist_eq_eLpNorm_neg_add]; rw [← eLpNorm_neg]; rw [neg_add]; rw [neg_neg]; rw [sub_eq_add_neg]

Depends on / 依赖: eLpNorm_neg, edist_eq_eLpNorm_neg_add, neg_add, neg_neg, sub_eq_add_neg
-/
theorem edist_def (f g : Lp E p μ) : edist f g = eLpNorm (⇑f - ⇑g) p μ := by
  rw [edist_eq_eLpNorm_neg_add]; rw [← eLpNorm_neg]; rw [neg_add]; rw [neg_neg]; rw [sub_eq_add_neg]

/--
theorem `edist_dist` / 定理 `edist_dist`

English:
theorem edist_dist
  given: (f g : Lp E p μ)
  statement: edist f g = .ofReal (dist f g)
  proof: by
  rw [edist_def]; rw [dist_def]; rw [← eLpNorm_congr_ae (coeFn_sub _ _)]; rw [ENNReal.ofReal_toReal (eLpNorm_ne_top (f - g))]

中文:
定理 edist_dist
  条件: (f g : Lp E p μ)
  结论: edist f g = .of实数 (dist f g)
  证明: by
  rw [edist_def]; rw [dist_def]; rw [← eLpNorm_congr_ae (coeFn_sub _ _)]; rw [ENNReal.ofReal_toReal (eLpNorm_ne_top (f - g))]
-/
protected theorem edist_dist (f g : Lp E p μ) : edist f g = .ofReal (dist f g) := by
  rw [edist_def]; rw [dist_def]; rw [← eLpNorm_congr_ae (coeFn_sub _ _)]; rw [ENNReal.ofReal_toReal (eLpNorm_ne_top (f - g))]

/--
theorem `dist_edist` / 定理 `dist_edist`

English:
theorem dist_edist
  given: (f g : Lp E p μ)
  statement: dist f g = (edist f g).toReal
  proof: MeasureTheory.Lp.dist_eq_eLpNorm_neg_add ..

中文:
定理 dist_edist
  条件: (f g : Lp E p μ)
  结论: dist f g = (edist f g).to实数
  证明: MeasureTheory.Lp.dist_eq_eLpNorm_neg_add ..
-/
protected theorem dist_edist (f g : Lp E p μ) : dist f g = (edist f g).toReal :=
  MeasureTheory.Lp.dist_eq_eLpNorm_neg_add ..

/--
theorem `dist_eq_norm` / 定理 `dist_eq_norm`

English:
theorem dist_eq_norm
  given: (f g : Lp E p μ)
  statement: dist f g = ‖-f + g‖
  proof: rfl

@[simp]

中文:
定理 dist_eq_norm
  条件: (f g : Lp E p μ)
  结论: dist f g = ‖-f + g‖
  证明: rfl

@[simp]
-/
theorem dist_eq_norm (f g : Lp E p μ) : dist f g = ‖-f + g‖ := rfl

@[simp]
/--
theorem `edist_toLp_toLp` / 定理 `edist_toLp_toLp`

English:
theorem edist_toLp_toLp
  given: (f g : α -> E) (hf : MemLp f p μ) (hg : MemLp g p μ)
  proof: by
  rw [edist_def]
  exact eLpNorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp)

@[simp]

中文:
定理 edist_toLp_toLp
  条件: (f g : α -> E) (hf : MemLp f p μ) (hg : MemLp g p μ)
  证明: by
  rw [edist_def]
  exact eLpNorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp)

@[simp]

Depends on / 依赖: coeFn_toLp, eLpNorm_congr_ae, edist_def, hf.coeFn_toLp.sub, hg.coeFn_toLp
-/
theorem edist_toLp_toLp (f g : α -> E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    edist (hf.toLp f) (hg.toLp g) = eLpNorm (f - g) p μ := by
  rw [edist_def]
  exact eLpNorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp)

@[simp]
/--
theorem `edist_toLp_zero` / 定理 `edist_toLp_zero`

English:
theorem edist_toLp_zero
  given: (f : α -> E) (hf : MemLp f p μ)
  statement: edist (hf.toLp f) 0 = eLpNorm f p μ
  proof: by
  simpa using edist_toLp_toLp f 0 hf .zero

@[simp]

中文:
定理 edist_toLp_zero
  条件: (f : α -> E) (hf : MemLp f p μ)
  结论: edist (hf.toLp f) 0 = eLpNorm f p μ
  证明: by
  simpa using edist_toLp_toLp f 0 hf .zero

@[simp]

Depends on / 依赖: edist_toLp_toLp
-/
theorem edist_toLp_zero (f : α -> E) (hf : MemLp f p μ) : edist (hf.toLp f) 0 = eLpNorm f p μ := by
  simpa using edist_toLp_toLp f 0 hf .zero

@[simp]
/--
theorem `nnnorm_zero` / 定理 `nnnorm_zero`

English:
theorem nnnorm_zero
  statement: ‖(0 : Lp E p μ)‖₊ = 0
  proof: by
  rw [nnnorm_def]; rw [ZeroMemClass.coe_zero]
  simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]

@[simp]

中文:
定理 nnnorm_zero
  结论: ‖(0 : Lp E p μ)‖₊ = 0
  证明: by
  rw [nnnorm_def]; rw [ZeroMemClass.coe_zero]
  simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]

@[simp]

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_zero, ZeroMemClass, ZeroMemClass.coe_zero, coeFn_zero, coe_zero, eLpNorm_congr_ae, eLpNorm_zero, nnnorm_def
-/
theorem nnnorm_zero : ‖(0 : Lp E p μ)‖₊ = 0 := by
  rw [nnnorm_def]; rw [ZeroMemClass.coe_zero]
  simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]

@[simp]
/--
theorem `norm_zero` / 定理 `norm_zero`

English:
theorem norm_zero
  statement: ‖(0 : Lp E p μ)‖ = 0
  proof: congr_arg ((↑) : Real>=0 -> Real) nnnorm_zero

@[simp]

中文:
定理 norm_zero
  结论: ‖(0 : Lp E p μ)‖ = 0
  证明: congr_arg ((↑) : Real>=0 -> Real) nnnorm_zero

@[simp]

Depends on / 依赖: congr_arg, nnnorm_zero
-/
theorem norm_zero : ‖(0 : Lp E p μ)‖ = 0 :=
  congr_arg ((↑) : Real>=0 -> Real) nnnorm_zero

@[simp]
/--
theorem `norm_measure_zero` / 定理 `norm_measure_zero`

English:
theorem norm_measure_zero
  given: (f : Lp E p (0 : MeasureTheory.Measure α))
  statement: ‖f‖ = 0
  proof: by
  -- Squeezed for performance reasons
  simp_rw [norm_def, eLpNorm_measure_zero, ENNReal.toReal_zero]

中文:
定理 norm_measure_zero
  条件: (f : Lp E p (0 : MeasureTheory.Measure α))
  结论: ‖f‖ = 0
  证明: by
  -- Squeezed for performance reasons
  simp_rw [norm_def, eLpNorm_measure_zero, ENNReal.toReal_zero]
-/
theorem norm_measure_zero (f : Lp E p (0 : MeasureTheory.Measure α)) : ‖f‖ = 0 := by
  -- Squeezed for performance reasons
  simp_rw [norm_def, eLpNorm_measure_zero, ENNReal.toReal_zero]

/--
theorem `norm_exponent_zero` / 定理 `norm_exponent_zero`

English:
theorem norm_exponent_zero
  given: (f : Lp E 0 μ)
  statement: ‖f‖ = 0
  proof: by
  -- Squeezed for performance reasons
  simp_rw [norm_def, eLpNorm_exponent_zero, ENNReal.toReal_zero]

中文:
定理 norm_exponent_zero
  条件: (f : Lp E 0 μ)
  结论: ‖f‖ = 0
  证明: by
  -- Squeezed for performance reasons
  simp_rw [norm_def, eLpNorm_exponent_zero, ENNReal.toReal_zero]
-/
@[simp] theorem norm_exponent_zero (f : Lp E 0 μ) : ‖f‖ = 0 := by
  -- Squeezed for performance reasons
  simp_rw [norm_def, eLpNorm_exponent_zero, ENNReal.toReal_zero]

/--
theorem `eq_zero_iff_ae_eq_zero` / 定理 `eq_zero_iff_ae_eq_zero`

English:
theorem eq_zero_iff_ae_eq_zero
  given: {f : Lp E p μ}
  statement: f = 0 ↔ f =ᵐ[μ] 0
  proof: by
  rw [Lp.ext_iff]
  exact EventuallyEq.congr_right AEEqFun.coeFn_zero

中文:
定理 eq_zero_iff_ae_eq_zero
  条件: {f : Lp E p μ}
  结论: f = 0 ↔ f =ᵐ[μ] 0
  证明: by
  rw [Lp.ext_iff]
  exact EventuallyEq.congr_right AEEqFun.coeFn_zero

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_zero, EventuallyEq, EventuallyEq.congr_right, Lp.ext_iff, coeFn_zero, congr_right, ext_iff
-/
theorem eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 := by
  rw [Lp.ext_iff]
  exact EventuallyEq.congr_right AEEqFun.coeFn_zero

/--
theorem `nnnorm_eq_zero_iff` / 定理 `nnnorm_eq_zero_iff`

English:
theorem nnnorm_eq_zero_iff
  given: {f : Lp E p μ} (hp : 0 < p)
  statement: ‖f‖₊ = 0 ↔ f = 0
  proof: by
  refine ⟨fun hf => ?_, fun hf => by simp [hf]⟩
  simp_rw [nnnorm_def, ENNReal.toNNReal_eq_zero_iff, eLpNorm_ne_top, or_false] at hf
  simp_rw [eq_zero_iff_ae_eq_zero, ← eLpNorm_eq_zero_iff (Lp.aestronglyMeasurable f) hp.ne.symm, hf]

中文:
定理 nnnorm_eq_zero_iff
  条件: {f : Lp E p μ} (hp : 0 < p)
  结论: ‖f‖₊ = 0 ↔ f = 0
  证明: by
  refine ⟨fun hf => ?_, fun hf => by simp [hf]⟩
  simp_rw [nnnorm_def, ENNReal.toNNReal_eq_zero_iff, eLpNorm_ne_top, or_false] at hf
  simp_rw [eq_zero_iff_ae_eq_zero, ← eLpNorm_eq_zero_iff (Lp.aestronglyMeasurable f) hp.ne.symm, hf]

Depends on / 依赖: ENNReal, ENNReal.toNNReal_eq_zero_iff, Lp.aestronglyMeasurable, aestronglyMeasurable, eLpNorm_eq_zero_iff, eLpNorm_ne_top, eq_zero_iff_ae_eq_zero, hp.ne.symm, nnnorm_def, or_false, simp_rw, toNNReal_eq_zero_iff
-/
theorem nnnorm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0 := by
  refine ⟨fun hf => ?_, fun hf => by simp [hf]⟩
  simp_rw [nnnorm_def, ENNReal.toNNReal_eq_zero_iff, eLpNorm_ne_top, or_false] at hf
  simp_rw [eq_zero_iff_ae_eq_zero, ← eLpNorm_eq_zero_iff (Lp.aestronglyMeasurable f) hp.ne.symm, hf]

/--
theorem `norm_eq_zero_iff` / 定理 `norm_eq_zero_iff`

English:
theorem norm_eq_zero_iff
  given: {f : Lp E p μ} (hp : 0 < p)
  statement: ‖f‖ = 0 ↔ f = 0
  proof: NNReal.coe_eq_zero.trans (nnnorm_eq_zero_iff hp)

@[simp]

中文:
定理 norm_eq_zero_iff
  条件: {f : Lp E p μ} (hp : 0 < p)
  结论: ‖f‖ = 0 ↔ f = 0
  证明: NNReal.coe_eq_zero.trans (nnnorm_eq_zero_iff hp)

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_eq_zero.trans, coe_eq_zero, nnnorm_eq_zero_iff
-/
theorem norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0 :=
  NNReal.coe_eq_zero.trans (nnnorm_eq_zero_iff hp)

@[simp]
/--
theorem `nnnorm_neg` / 定理 `nnnorm_neg`

English:
theorem nnnorm_neg
  given: (f : Lp E p μ)
  statement: ‖-f‖₊ = ‖f‖₊
  proof: by
  rw [nnnorm_def]; rw [nnnorm_def]; rw [eLpNorm_congr_ae (coeFn_neg _)]; rw [eLpNorm_neg]

@[simp]

中文:
定理 nnnorm_neg
  条件: (f : Lp E p μ)
  结论: ‖-f‖₊ = ‖f‖₊
  证明: by
  rw [nnnorm_def]; rw [nnnorm_def]; rw [eLpNorm_congr_ae (coeFn_neg _)]; rw [eLpNorm_neg]

@[simp]

Depends on / 依赖: coeFn_neg, eLpNorm_congr_ae, eLpNorm_neg, nnnorm_def
-/
theorem nnnorm_neg (f : Lp E p μ) : ‖-f‖₊ = ‖f‖₊ := by
  rw [nnnorm_def]; rw [nnnorm_def]; rw [eLpNorm_congr_ae (coeFn_neg _)]; rw [eLpNorm_neg]

@[simp]
/--
theorem `norm_neg` / 定理 `norm_neg`

English:
theorem norm_neg
  given: (f : Lp E p μ)
  statement: ‖-f‖ = ‖f‖
  proof: congr_arg ((↑) : Real>=0 -> Real) (nnnorm_neg f)

中文:
定理 norm_neg
  条件: (f : Lp E p μ)
  结论: ‖-f‖ = ‖f‖
  证明: congr_arg ((↑) : Real>=0 -> Real) (nnnorm_neg f)

Depends on / 依赖: congr_arg, nnnorm_neg
-/
theorem norm_neg (f : Lp E p μ) : ‖-f‖ = ‖f‖ :=
  congr_arg ((↑) : Real>=0 -> Real) (nnnorm_neg f)

/--
theorem `nnnorm_le_mul_nnnorm_of_ae_le_mul` / 定理 `nnnorm_le_mul_nnnorm_of_ae_le_mul`

English:
theorem nnnorm_le_mul_nnnorm_of_ae_le_mul
  statement: {c : Real>=0} {f : Lp E p μ} {g : Lp F p μ}
  proof: by
  simp only [nnnorm_def]
  have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul h p
  rwa [← ENNReal.toNNReal_le_toNNReal, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
    ENNReal.toNNReal_coe] at this
  · finiteness
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by finiteness)

中文:
定理 nnnorm_le_mul_nnnorm_of_ae_le_mul
  结论: {c : 实数>=0} {f : Lp E p μ} {g : Lp F p μ}
  证明: by
  simp only [nnnorm_def]
  have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul h p
  rwa [← ENNReal.toNNReal_le_toNNReal, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
    ENNReal.toNNReal_coe] at this
  · finiteness
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by finiteness)

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.mul_ne_top, ENNReal.smul_def, ENNReal.toNNReal_coe, ENNReal.toNNReal_le_toNNReal, ENNReal.toNNReal_mul, coe_ne_top, eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul, finiteness, mul_ne_top, nnnorm_def, smul_def, smul_eq_mul, toNNReal_coe, toNNReal_le_toNNReal, toNNReal_mul
-/
theorem nnnorm_le_mul_nnnorm_of_ae_le_mul {c : Real>=0} {f : Lp E p μ} {g : Lp F p μ}
    (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) : ‖f‖₊ <= c * ‖g‖₊ := by
  simp only [nnnorm_def]
  have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul h p
  rwa [← ENNReal.toNNReal_le_toNNReal, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
    ENNReal.toNNReal_coe] at this
  · finiteness
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by finiteness)

/--
theorem `norm_le_mul_norm_of_ae_le_mul` / 定理 `norm_le_mul_norm_of_ae_le_mul`

English:
theorem norm_le_mul_norm_of_ae_le_mul
  statement: {c : Real} {f : Lp E p μ} {g : Lp F p μ}
  proof: by
  rcases le_or_gt 0 c with hc | hc
  · lift c to Real>=0 using hc
    exact NNReal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
  · simp only [norm_def]
    have := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    simp [this]

中文:
定理 norm_le_mul_norm_of_ae_le_mul
  结论: {c : 实数} {f : Lp E p μ} {g : Lp F p μ}
  证明: by
  rcases le_or_gt 0 c with hc | hc
  · lift c to Real>=0 using hc
    exact NNReal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
  · simp only [norm_def]
    have := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    simp [this]

Depends on / 依赖: NNReal, NNReal.coe_le_coe.mpr, coe_le_coe, eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg, le_or_gt, nnnorm_le_mul_nnnorm_of_ae_le_mul, norm_def
-/
theorem norm_le_mul_norm_of_ae_le_mul {c : Real} {f : Lp E p μ} {g : Lp F p μ}
    (h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖) : ‖f‖ <= c * ‖g‖ := by
  rcases le_or_gt 0 c with hc | hc
  · lift c to Real>=0 using hc
    exact NNReal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
  · simp only [norm_def]
    have := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    simp [this]

/--
theorem `norm_le_norm_of_ae_le` / 定理 `norm_le_norm_of_ae_le`

English:
theorem norm_le_norm_of_ae_le
  given: {f : Lp E p μ} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖)
  proof: by
  rw [norm_def]; rw [norm_def]
  exact ENNReal.toReal_mono (by finiteness) (eLpNorm_mono_ae h)

中文:
定理 norm_le_norm_of_ae_le
  条件: {f : Lp E p μ} {g : Lp F p μ} (h : 对任意ᵐ x ∂μ, ‖f x‖ <= ‖g x‖)
  证明: by
  rw [norm_def]; rw [norm_def]
  exact ENNReal.toReal_mono (by finiteness) (eLpNorm_mono_ae h)

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, eLpNorm_mono_ae, finiteness, norm_def, toReal_mono
-/
theorem norm_le_norm_of_ae_le {f : Lp E p μ} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) :
    ‖f‖ <= ‖g‖ := by
  rw [norm_def]; rw [norm_def]
  exact ENNReal.toReal_mono (by finiteness) (eLpNorm_mono_ae h)

/--
theorem `mem_Lp_of_nnnorm_ae_le_mul` / 定理 `mem_Lp_of_nnnorm_ae_le_mul`

English:
theorem mem_Lp_of_nnnorm_ae_le_mul
  statement: {c : Real>=0} {f : α ->ₘ[μ] E} {g : Lp F p μ}
  proof: mem_Lp_iff_memLp.2 MemLp.of_nnnorm_le_mul (Lp.memLp g) f.aestronglyMeasurable h

中文:
定理 mem_Lp_of_nnnorm_ae_le_mul
  结论: {c : 实数>=0} {f : α ->ₘ[μ] E} {g : Lp F p μ}
  证明: mem_Lp_iff_memLp.2 MemLp.of_nnnorm_le_mul (Lp.memLp g) f.aestronglyMeasurable h

Depends on / 依赖: Lp.memLp, MemLp.of_nnnorm_le_mul, aestronglyMeasurable, f.aestronglyMeasurable, mem_Lp_iff_memLp, of_nnnorm_le_mul
-/
theorem mem_Lp_of_nnnorm_ae_le_mul {c : Real>=0} {f : α ->ₘ[μ] E} {g : Lp F p μ}
    (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) : f in Lp E p μ :=
mem_Lp_iff_memLp.2 MemLp.of_nnnorm_le_mul (Lp.memLp g) f.aestronglyMeasurable h

/--
theorem `mem_Lp_of_ae_le_mul` / 定理 `mem_Lp_of_ae_le_mul`

English:
theorem mem_Lp_of_ae_le_mul
  statement: {c : Real} {f : α ->ₘ[μ] E} {g : Lp F p μ}
  proof: mem_Lp_iff_memLp.2 MemLp.of_le_mul (Lp.memLp g) f.aestronglyMeasurable h

中文:
定理 mem_Lp_of_ae_le_mul
  结论: {c : 实数} {f : α ->ₘ[μ] E} {g : Lp F p μ}
  证明: mem_Lp_iff_memLp.2 MemLp.of_le_mul (Lp.memLp g) f.aestronglyMeasurable h

Depends on / 依赖: Lp.memLp, MemLp.of_le_mul, aestronglyMeasurable, f.aestronglyMeasurable, mem_Lp_iff_memLp, of_le_mul
-/
theorem mem_Lp_of_ae_le_mul {c : Real} {f : α ->ₘ[μ] E} {g : Lp F p μ}
    (h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖) : f in Lp E p μ :=
mem_Lp_iff_memLp.2 MemLp.of_le_mul (Lp.memLp g) f.aestronglyMeasurable h

/--
theorem `mem_Lp_of_nnnorm_ae_le` / 定理 `mem_Lp_of_nnnorm_ae_le`

English:
theorem mem_Lp_of_nnnorm_ae_le
  given: {f : α ->ₘ[μ] E} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊)
  proof: mem_Lp_iff_memLp.2 MemLp.of_le (Lp.memLp g) f.aestronglyMeasurable h

中文:
定理 mem_Lp_of_nnnorm_ae_le
  条件: {f : α ->ₘ[μ] E} {g : Lp F p μ} (h : 对任意ᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊)
  证明: mem_Lp_iff_memLp.2 MemLp.of_le (Lp.memLp g) f.aestronglyMeasurable h

Depends on / 依赖: Lp.memLp, MemLp.of_le, aestronglyMeasurable, f.aestronglyMeasurable, mem_Lp_iff_memLp, of_le
-/
theorem mem_Lp_of_nnnorm_ae_le {f : α ->ₘ[μ] E} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊) :
    f in Lp E p μ :=
mem_Lp_iff_memLp.2 MemLp.of_le (Lp.memLp g) f.aestronglyMeasurable h

/--
theorem `mem_Lp_of_ae_le` / 定理 `mem_Lp_of_ae_le`

English:
theorem mem_Lp_of_ae_le
  given: {f : α ->ₘ[μ] E} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖)
  proof: mem_Lp_of_nnnorm_ae_le h

中文:
定理 mem_Lp_of_ae_le
  条件: {f : α ->ₘ[μ] E} {g : Lp F p μ} (h : 对任意ᵐ x ∂μ, ‖f x‖ <= ‖g x‖)
  证明: mem_Lp_of_nnnorm_ae_le h

Depends on / 依赖: mem_Lp_of_nnnorm_ae_le
-/
theorem mem_Lp_of_ae_le {f : α ->ₘ[μ] E} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) :
    f in Lp E p μ :=
  mem_Lp_of_nnnorm_ae_le h

/--
theorem `mem_Lp_of_ae_nnnorm_bound` / 定理 `mem_Lp_of_ae_nnnorm_bound`

English:
theorem mem_Lp_of_ae_nnnorm_bound
  statement: [IsFiniteMeasure μ] {f : α ->ₘ[μ] E} (C : Real>=0)
  proof: mem_Lp_iff_memLp.2 MemLp.of_bound f.aestronglyMeasurable _ hfC

中文:
定理 mem_Lp_of_ae_nnnorm_bound
  结论: [IsFiniteMeasure μ] {f : α ->ₘ[μ] E} (C : 实数>=0)
  证明: mem_Lp_iff_memLp.2 MemLp.of_bound f.aestronglyMeasurable _ hfC

Depends on / 依赖: MemLp.of_bound, aestronglyMeasurable, f.aestronglyMeasurable, mem_Lp_iff_memLp, of_bound
-/
theorem mem_Lp_of_ae_nnnorm_bound [IsFiniteMeasure μ] {f : α ->ₘ[μ] E} (C : Real>=0)
    (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) : f in Lp E p μ :=
mem_Lp_iff_memLp.2 MemLp.of_bound f.aestronglyMeasurable _ hfC

/--
theorem `mem_Lp_of_ae_bound` / 定理 `mem_Lp_of_ae_bound`

English:
theorem mem_Lp_of_ae_bound
  given: [IsFiniteMeasure μ] {f : α ->ₘ[μ] E} (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C)
  proof: mem_Lp_iff_memLp.2 MemLp.of_bound f.aestronglyMeasurable _ hfC

中文:
定理 mem_Lp_of_ae_bound
  条件: [IsFiniteMeasure μ] {f : α ->ₘ[μ] E} (C : 实数) (hfC : 对任意ᵐ x ∂μ, ‖f x‖ <= C)
  证明: mem_Lp_iff_memLp.2 MemLp.of_bound f.aestronglyMeasurable _ hfC

Depends on / 依赖: MemLp.of_bound, aestronglyMeasurable, f.aestronglyMeasurable, mem_Lp_iff_memLp, of_bound
-/
theorem mem_Lp_of_ae_bound [IsFiniteMeasure μ] {f : α ->ₘ[μ] E} (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) :
    f in Lp E p μ :=
mem_Lp_iff_memLp.2 MemLp.of_bound f.aestronglyMeasurable _ hfC

/--
theorem `nnnorm_le_of_ae_bound` / 定理 `nnnorm_le_of_ae_bound`

English:
theorem nnnorm_le_of_ae_bound
  statement: [IsFiniteMeasure μ] {f : Lp E p μ} {C : Real>=0}
  proof: by
  by_cases hμ : μ = 0
  · simp [hμ, nnnorm_def]
  rw [← ENNReal.coe_le_coe]; rw [nnnorm_def]; rw [ENNReal.coe_toNNReal (eLpNorm_ne_top _)]
  refine (eLpNorm_le_of_ae_nnnorm_bound hfC).trans_eq ?_
  rw [← coe_measureUnivNNReal μ]; rw [← ENNReal.coe_rpow_of_ne_zero (measureUnivNNReal_pos hμ).ne']; 

中文:
定理 nnnorm_le_of_ae_bound
  结论: [IsFiniteMeasure μ] {f : Lp E p μ} {C : 实数>=0}
  证明: by
  by_cases hμ : μ = 0
  · simp [hμ, nnnorm_def]
  rw [← ENNReal.coe_le_coe]; rw [nnnorm_def]; rw [ENNReal.coe_toNNReal (eLpNorm_ne_top _)]
  refine (eLpNorm_le_of_ae_nnnorm_bound hfC).trans_eq ?_
  rw [← coe_measureUnivNNReal μ]; rw [← ENNReal.coe_rpow_of_ne_zero (measureUnivNNReal_pos hμ).ne']; 

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero, ENNReal.coe_toNNReal, ENNReal.smul_def, coe_le_coe, coe_measureUnivNNReal, coe_mul, coe_rpow_of_ne_zero, coe_toNNReal, eLpNorm_le_of_ae_nnnorm_bound, eLpNorm_ne_top, measureUnivNNReal_pos, mul_comm, nnnorm_def, smul_def, smul_eq_mul, trans_eq
-/
theorem nnnorm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : Real>=0}
    (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) : ‖f‖₊ <= measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
  by_cases hμ : μ = 0
  · simp [hμ, nnnorm_def]
  rw [← ENNReal.coe_le_coe]; rw [nnnorm_def]; rw [ENNReal.coe_toNNReal (eLpNorm_ne_top _)]
  refine (eLpNorm_le_of_ae_nnnorm_bound hfC).trans_eq ?_
  rw [← coe_measureUnivNNReal μ]; rw [← ENNReal.coe_rpow_of_ne_zero (measureUnivNNReal_pos hμ).ne']; rw [ENNReal.coe_mul]; rw [mul_comm]; rw [ENNReal.smul_def]; rw [smul_eq_mul]

/--
theorem `norm_le_of_ae_bound` / 定理 `norm_le_of_ae_bound`

English:
theorem norm_le_of_ae_bound
  statement: [IsFiniteMeasure μ] {f : Lp E p μ} {C : Real} (hC : 0 <= C)
  proof: by
  lift C to Real>=0 using hC
  have := nnnorm_le_of_ae_bound hfC
  rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow] at this

中文:
定理 norm_le_of_ae_bound
  结论: [IsFiniteMeasure μ] {f : Lp E p μ} {C : 实数} (hC : 0 <= C)
  证明: by
  lift C to Real>=0 using hC
  have := nnnorm_le_of_ae_bound hfC
  rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow] at this

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow, coe_le_coe, coe_mul, coe_rpow, nnnorm_le_of_ae_bound
-/
theorem norm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : Real} (hC : 0 <= C)
    (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : ‖f‖ <= measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
  lift C to Real>=0 using hC
  have := nnnorm_le_of_ae_bound hfC
  rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow] at this

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (Lp E p μ)
  body: inferInstance

中文:
实例 instAddCommGroup
  签名: : AddCommGroup (Lp E p μ)
  定义体: inferInstance
-/
instance instAddCommGroup : AddCommGroup (Lp E p μ) := inferInstance

/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: [hp : Fact (1 <= p)]
  body: fast_instance%
  { AddGroupNorm.toNormedAddCommGroup
      { toFun := (norm : Lp E p μ -> Real)
        map_zero' := norm_zero
        neg' := by simp only [norm_neg, implies_true] -- squeezed for performance reasons
        add_le' := fun f g => by
          suffices ‖f + g‖ₑ <= ‖f‖ₑ + ‖g‖ₑ by
    

中文:
实例 instNormedAddCommGroup
  签名: [hp : Fact (1 <= p)]
  定义体: fast_instance%
  { AddGroupNorm.toNormedAddCommGroup
      { toFun := (norm : Lp E p μ -> Real)
        map_zero' := norm_zero
        neg' := by simp only [norm_neg, implies_true] -- squeezed for performance reasons
        add_le' := fun f g => by
          suffices ‖f + g‖ₑ <= ‖f‖ₑ + ‖g‖ₑ by
    

Depends on / 依赖: AddGroupNorm, AddGroupNorm.toNormedAddCommGroup, add_le, fast_instance, implies_true, map_zero, norm_neg, norm_zero, performance, reasons, squeezed, toNormedAddCommGroup
-/
instance instNormedAddCommGroup [hp : Fact (1 <= p)] : NormedAddCommGroup (Lp E p μ) :=
  fast_instance%
  { AddGroupNorm.toNormedAddCommGroup
      { toFun := (norm : Lp E p μ -> Real)
        map_zero' := norm_zero
        neg' := by simp only [norm_neg, implies_true] -- squeezed for performance reasons
        add_le' := fun f g => by
          suffices ‖f + g‖ₑ <= ‖f‖ₑ + ‖g‖ₑ by
            -- Squeezed for performance reasons
            simpa only [ge_iff_le, enorm, ← ENNReal.coe_add, ENNReal.coe_le_coe] using! this
          simp only [Lp.enorm_def]
          exact (eLpNorm_congr_ae (AEEqFun.coeFn_add _ _)).trans_le
            (eLpNorm_add_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) hp.out)
        eq_zero_of_map_eq_zero' _ := (norm_eq_zero_iff <| zero_lt_one.trans_le hp.1).1 } with
    edist := edist
    edist_dist := Lp.edist_dist }

-- check no diamond is created
example [Fact (1 <= p)] : PseudoEMetricSpace.toEDist = (Lp.instEDist : EDist (Lp E p μ)) := by
  with_reducible_and_instances rfl

example [Fact (1 <= p)] : SeminormedAddGroup.toNNNorm = (Lp.instNNNorm : NNNorm (Lp E p μ)) := by
  with_reducible_and_instances rfl

section IsBoundedSMul

variable [NormedRing 𝕜] [NormedRing 𝕜'] [Module 𝕜 E] [Module 𝕜' E]
variable [IsBoundedSMul 𝕜 E] [IsBoundedSMul 𝕜' E]

/--
theorem `const_smul_mem_Lp` / 定理 `const_smul_mem_Lp`

English:
theorem const_smul_mem_Lp
  given: (c : 𝕜) (f : Lp E p μ)
  statement: c • (f : α ->ₘ[μ] E) in Lp E p μ
  proof: by
  rw [mem_Lp_iff_eLpNorm_lt_top]; rw [eLpNorm_congr_ae (AEEqFun.coeFn_smul _ _)]
exact eLpNorm_const_smul_le.trans_lt (by finiteness)

中文:
定理 const_smul_mem_Lp
  条件: (c : 𝕜) (f : Lp E p μ)
  结论: c • (f : α ->ₘ[μ] E) in Lp E p μ
  证明: by
  rw [mem_Lp_iff_eLpNorm_lt_top]; rw [eLpNorm_congr_ae (AEEqFun.coeFn_smul _ _)]
exact eLpNorm_const_smul_le.trans_lt (by finiteness)

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_smul, coeFn_smul, eLpNorm_congr_ae, eLpNorm_const_smul_le, eLpNorm_const_smul_le.trans_lt, finiteness, mem_Lp_iff_eLpNorm_lt_top, trans_lt
-/
theorem const_smul_mem_Lp (c : 𝕜) (f : Lp E p μ) : c • (f : α ->ₘ[μ] E) in Lp E p μ := by
  rw [mem_Lp_iff_eLpNorm_lt_top]; rw [eLpNorm_congr_ae (AEEqFun.coeFn_smul _ _)]
exact eLpNorm_const_smul_le.trans_lt (by finiteness)

variable (𝕜 E p μ)

/--
Definition of `LpSubmodule` / `LpSubmodule` 的定义

English:
definition LpSubmodule
  signature: : Submodule 𝕜 (α ->ₘ[μ] E)
  body: { Lp E p μ with smul_mem' := fun c f hf => by simpa using const_smul_mem_Lp c ⟨f, hf⟩ }

中文:
定义 LpSubmodule
  签名: : Submodule 𝕜 (α ->ₘ[μ] E)
  定义体: { Lp E p μ with smul_mem' := fun c f hf => by simpa using const_smul_mem_Lp c ⟨f, hf⟩ }

Depends on / 依赖: const_smul_mem_Lp, smul_mem
-/
def LpSubmodule : Submodule 𝕜 (α ->ₘ[μ] E) :=
  { Lp E p μ with smul_mem' := fun c f hf => by simpa using const_smul_mem_Lp c ⟨f, hf⟩ }

variable {𝕜 E p μ}

/--
theorem `coe_LpSubmodule` / 定理 `coe_LpSubmodule`

English:
theorem coe_LpSubmodule
  statement: (LpSubmodule 𝕜 E p μ).toAddSubgroup = Lp E p μ
  proof: rfl

中文:
定理 coe_LpSubmodule
  结论: (LpSubmodule 𝕜 E p μ).toAddSubgroup = Lp E p μ
  证明: rfl
-/
theorem coe_LpSubmodule : (LpSubmodule 𝕜 E p μ).toAddSubgroup = Lp E p μ :=
  rfl

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module 𝕜 (Lp E p μ)
  body: fast_instance% (LpSubmodule 𝕜 E p μ).module

中文:
实例 instModule
  签名: : Module 𝕜 (Lp E p μ)
  定义体: fast_instance% (LpSubmodule 𝕜 E p μ).module

Depends on / 依赖: LpSubmodule, fast_instance, module
-/
instance instModule : Module 𝕜 (Lp E p μ) :=
  fast_instance% (LpSubmodule 𝕜 E p μ).module

/--
theorem `coeFn_smul` / 定理 `coeFn_smul`

English:
theorem coeFn_smul
  given: (c : 𝕜) (f : Lp E p μ)
  statement: ⇑(c • f) =ᵐ[μ] c • ⇑f
  proof: AEEqFun.coeFn_smul _ _

中文:
定理 coeFn_smul
  条件: (c : 𝕜) (f : Lp E p μ)
  结论: ⇑(c • f) =ᵐ[μ] c • ⇑f
  证明: AEEqFun.coeFn_smul _ _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_smul, coeFn_smul
-/
theorem coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f) =ᵐ[μ] c • ⇑f :=
  AEEqFun.coeFn_smul _ _

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [Module 𝕜ᵐᵒᵖ E] [IsBoundedSMul 𝕜ᵐᵒᵖ E] [IsCentralScalar 𝕜 E]
  body: Subtype.ext op_smul_eq_smul k (f : α ->ₘ[μ] E)

中文:
实例 instIsCentralScalar
  签名: [Module 𝕜ᵐᵒᵖ E] [IsBoundedSMul 𝕜ᵐᵒᵖ E] [IsCentralScalar 𝕜 E]
  定义体: Subtype.ext op_smul_eq_smul k (f : α ->ₘ[μ] E)

Depends on / 依赖: Subtype, Subtype.ext, op_smul_eq_smul
-/
instance instIsCentralScalar [Module 𝕜ᵐᵒᵖ E] [IsBoundedSMul 𝕜ᵐᵒᵖ E] [IsCentralScalar 𝕜 E] :
    IsCentralScalar 𝕜 (Lp E p μ) where
op_smul_eq_smul k f := Subtype.ext op_smul_eq_smul k (f : α ->ₘ[μ] E)

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass 𝕜 𝕜' E]
  body: Subtype.ext smul_comm k k' (f : α ->ₘ[μ] E)

中文:
实例 instSMulCommClass
  签名: [SMulCommClass 𝕜 𝕜' E]
  定义体: Subtype.ext smul_comm k k' (f : α ->ₘ[μ] E)

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass [SMulCommClass 𝕜 𝕜' E] : SMulCommClass 𝕜 𝕜' (Lp E p μ) where
smul_comm k k' f := Subtype.ext smul_comm k k' (f : α ->ₘ[μ] E)

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E]
  body: Subtype.ext smul_assoc k k' (f : α ->ₘ[μ] E)

中文:
实例 instIsScalarTower
  签名: [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E]
  定义体: Subtype.ext smul_assoc k k' (f : α ->ₘ[μ] E)

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E] : IsScalarTower 𝕜 𝕜' (Lp E p μ) where
smul_assoc k k' f := Subtype.ext smul_assoc k k' (f : α ->ₘ[μ] E)

/--
Instance `instIsBoundedSMul` / 实例 `instIsBoundedSMul`

English:
instance instIsBoundedSMul
  signature: [Fact (1 <= p)]
  body: IsBoundedSMul.of_enorm_smul_le fun r f => by
    simpa only [eLpNorm_congr_ae (coeFn_smul _ _), enorm_def]
      using eLpNorm_const_smul_le (c := r) (f := f) (p := p)

中文:
实例 instIsBoundedSMul
  签名: [Fact (1 <= p)]
  定义体: IsBoundedSMul.of_enorm_smul_le fun r f => by
    simpa only [eLpNorm_congr_ae (coeFn_smul _ _), enorm_def]
      using eLpNorm_const_smul_le (c := r) (f := f) (p := p)

Depends on / 依赖: IsBoundedSMul, IsBoundedSMul.of_enorm_smul_le, coeFn_smul, eLpNorm_congr_ae, eLpNorm_const_smul_le, enorm_def, of_enorm_smul_le
-/
instance instIsBoundedSMul [Fact (1 <= p)] : IsBoundedSMul 𝕜 (Lp E p μ) :=
  IsBoundedSMul.of_enorm_smul_le fun r f => by
    simpa only [eLpNorm_congr_ae (coeFn_smul _ _), enorm_def]
      using eLpNorm_const_smul_le (c := r) (f := f) (p := p)

end IsBoundedSMul

section NormedSpace

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

/--
Instance `instNormedSpace` / 实例 `instNormedSpace`

English:
instance instNormedSpace
  signature: [Fact (1 <= p)]
  body: norm_smul_le _ _

中文:
实例 instNormedSpace
  签名: [Fact (1 <= p)]
  定义体: norm_smul_le _ _

Depends on / 依赖: norm_smul_le
-/
instance instNormedSpace [Fact (1 <= p)] : NormedSpace 𝕜 (Lp E p μ) where
  norm_smul_le _ _ := norm_smul_le _ _

end NormedSpace

end Lp

namespace MemLp

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
theorem `toLp_const_smul` / 定理 `toLp_const_smul`

English:
theorem toLp_const_smul
  given: {f : α -> E} (c : 𝕜) (hf : MemLp f p μ)
  proof: rfl

中文:
定理 toLp_const_smul
  条件: {f : α -> E} (c : 𝕜) (hf : MemLp f p μ)
  证明: rfl
-/
theorem toLp_const_smul {f : α -> E} (c : 𝕜) (hf : MemLp f p μ) :
    (hf.const_smul c).toLp (c • f) = c • hf.toLp f :=
  rfl

end MemLp

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/--
theorem `MemLp.enorm_rpow_div` / 定理 `MemLp.enorm_rpow_div`

English:
theorem MemLp.enorm_rpow_div
  given: {f : α -> ε} (hf : MemLp f p μ) (q : Real>=0∞)
  proof: by
  refine ⟨(hf.1.enorm.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    simpa only [ENNReal.rpow_zero, e

中文:
定理 MemLp.enorm_rpow_div
  条件: {f : α -> ε} (hf : MemLp f p μ) (q : 实数>=0∞)
  证明: by
  refine ⟨(hf.1.enorm.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    simpa only [ENNReal.rpow_zero, e

Depends on / 依赖: ENNReal, ENNReal.div_zero, ENNReal.ofReal_toReal, ENNReal.rpow_lt_top_of_nonneg, ENNReal.rpow_zero, ENNReal.toReal_nonneg, ENNReal.toReal_pos, ENNReal.toReal_zero, aestronglyMeasurable, div_eq_, div_zero, eLpNorm_enorm_rpow, eLpNorm_exponent_top, enorm.pow_const, memLp_top_const_enorm, ofReal_toReal, p_zero, pow_const, q.toReal, q_top
-/
theorem MemLp.enorm_rpow_div {f : α -> ε} (hf : MemLp f p μ) (q : Real>=0∞) :
    MemLp (‖f ·‖ₑ ^ q.toReal) (p / q) μ := by
  refine ⟨(hf.1.enorm.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    simpa only [ENNReal.rpow_zero, eLpNorm_exponent_top] using (memLp_top_const_enorm (by simp)).2
  rw [eLpNorm_enorm_rpow _ (ENNReal.toReal_pos q_zero q_top)]
  apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal q_top]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [ENNReal.inv_mul_cancel q_zero q_top]; rw [mul_one]
  exact hf.2.ne

/--
theorem `MemLp.norm_rpow_div` / 定理 `MemLp.norm_rpow_div`

English:
theorem MemLp.norm_rpow_div
  given: {f : α -> E} (hf : MemLp f p μ) (q : Real>=0∞)
  proof: by
  refine ⟨(hf.1.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero, Real.rpow_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    exac

中文:
定理 MemLp.norm_rpow_div
  条件: {f : α -> E} (hf : MemLp f p μ) (q : 实数>=0∞)
  证明: by
  refine ⟨(hf.1.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero, Real.rpow_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    exac

Depends on / 依赖: ENNReal, ENNReal.div_zero, ENNReal.ofReal_toReal, ENNReal.rpow_lt_top_of_nonneg, ENNReal.toReal_nonneg, ENNReal.toReal_pos, ENNReal.toReal_zero, Real.rpow_zero, aemeasurable, aestronglyMeasurable, div_eq_mul_inv, div_zero, eLpNorm_norm_rpow, memLp_top_const, mul_assoc, norm.aemeasurable.pow_const, ofReal_toReal, p_zero, pow_const, q.toReal
-/
theorem MemLp.norm_rpow_div {f : α -> E} (hf : MemLp f p μ) (q : Real>=0∞) :
    MemLp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ := by
  refine ⟨(hf.1.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero, Real.rpow_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    exact (memLp_top_const (1 : Real)).2
  rw [eLpNorm_norm_rpow _ (ENNReal.toReal_pos q_zero q_top)]
  apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal q_top]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [ENNReal.inv_mul_cancel q_zero q_top]; rw [mul_one]
  exact hf.2.ne

/--
theorem `memLp_enorm_rpow_iff` / 定理 `memLp_enorm_rpow_iff`

English:
theorem memLp_enorm_rpow_iff
  statement: {q : Real>=0∞} {f : α -> ε} (hf : AEStronglyMeasurable f μ) (q_zero : q != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => h.enorm_rpow_div q⟩
  apply (memLp_enorm_iff hf).1
  convert! h.enorm_rpow_div q⁻¹ using 1
  · ext x
    have : q.toReal * q.toReal⁻¹ = 1 :=
CommGroupWithZero.mul_inv_cancel q.toReal ENNReal.toReal_ne_zero.mpr ⟨q_zero, q_top⟩
    simp [← ENNReal.rpow_mul, this, ENN

中文:
定理 memLp_enorm_rpow_iff
  结论: {q : 实数>=0∞} {f : α -> ε} (hf : AEStronglyMeasurable f μ) (q_zero : q != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => h.enorm_rpow_div q⟩
  apply (memLp_enorm_iff hf).1
  convert! h.enorm_rpow_div q⁻¹ using 1
  · ext x
    have : q.toReal * q.toReal⁻¹ = 1 :=
CommGroupWithZero.mul_inv_cancel q.toReal ENNReal.toReal_ne_zero.mpr ⟨q_zero, q_top⟩
    simp [← ENNReal.rpow_mul, this, ENN

Depends on / 依赖: CommGroupWithZero, CommGroupWithZero.mul_inv_cancel, ENNReal, ENNReal.inv_mul_cancel, ENNReal.rpow_mul, ENNReal.rpow_one, ENNReal.toReal_ne_zero.mpr, convert, div_eq_mul_inv, enorm_rpow_div, h.enorm_rpow_div, inv_inv, inv_mul_cancel, memLp_enorm_iff, mul_assoc, mul_inv_cancel, mul_one, q.toReal, q_top, q_zero
-/
theorem memLp_enorm_rpow_iff {q : Real>=0∞} {f : α -> ε} (hf : AEStronglyMeasurable f μ) (q_zero : q != 0)
    (q_top : q != ∞) : MemLp (‖f ·‖ₑ ^ q.toReal) (p / q) μ ↔ MemLp f p μ := by
  refine ⟨fun h => ?_, fun h => h.enorm_rpow_div q⟩
  apply (memLp_enorm_iff hf).1
  convert! h.enorm_rpow_div q⁻¹ using 1
  · ext x
    have : q.toReal * q.toReal⁻¹ = 1 :=
CommGroupWithZero.mul_inv_cancel q.toReal ENNReal.toReal_ne_zero.mpr ⟨q_zero, q_top⟩
    simp [← ENNReal.rpow_mul, this, ENNReal.rpow_one]
  · rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
      mul_one]

/--
theorem `memLp_norm_rpow_iff` / 定理 `memLp_norm_rpow_iff`

English:
theorem memLp_norm_rpow_iff
  statement: {q : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ) (q_zero : q != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => h.norm_rpow_div q⟩
  apply (memLp_norm_iff hf).1
  convert! h.norm_rpow_div q⁻¹ using 1
  · ext x
    rw [Real.norm_eq_abs]; rw [Real.abs_rpow_of_nonneg (norm_nonneg _)]; rw [← Real.rpow_mul (abs_nonneg _)]; rw [ENNReal.toReal_inv]; rw [mul_inv_cancel₀]; rw [abs_of

中文:
定理 memLp_norm_rpow_iff
  结论: {q : 实数>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ) (q_zero : q != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => h.norm_rpow_div q⟩
  apply (memLp_norm_iff hf).1
  convert! h.norm_rpow_div q⁻¹ using 1
  · ext x
    rw [Real.norm_eq_abs]; rw [Real.abs_rpow_of_nonneg (norm_nonneg _)]; rw [← Real.rpow_mul (abs_nonneg _)]; rw [ENNReal.toReal_inv]; rw [mul_inv_cancel₀]; rw [abs_of

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, ENNReal.toReal_eq_zero_iff, ENNReal.toReal_inv, Real.abs_rpow_of_nonneg, Real.norm_eq_abs, Real.rpow_mul, Real.rpow_one, abs_nonneg, abs_of_nonneg, abs_rpow_of_nonneg, convert, div_eq_mul_inv, h.norm_rpow_div, inv_inv, inv_mul_cancel, memLp_norm_iff, mul_assoc, mul_one, norm_eq_abs
-/
theorem memLp_norm_rpow_iff {q : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ) (q_zero : q != 0)
    (q_top : q != ∞) : MemLp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ ↔ MemLp f p μ := by
  refine ⟨fun h => ?_, fun h => h.norm_rpow_div q⟩
  apply (memLp_norm_iff hf).1
  convert! h.norm_rpow_div q⁻¹ using 1
  · ext x
    rw [Real.norm_eq_abs]; rw [Real.abs_rpow_of_nonneg (norm_nonneg _)]; rw [← Real.rpow_mul (abs_nonneg _)]; rw [ENNReal.toReal_inv]; rw [mul_inv_cancel₀]; rw [abs_of_nonneg (norm_nonneg _)]; rw [Real.rpow_one]
    simp [ENNReal.toReal_eq_zero_iff, q_zero, q_top]
  · rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
      mul_one]

/--
theorem `MemLp.enorm_rpow` / 定理 `MemLp.enorm_rpow`

English:
theorem MemLp.enorm_rpow
  given: {f : α -> ε} (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: by
  convert! hf.enorm_rpow_div p
  rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]

中文:
定理 MemLp.enorm_rpow
  条件: {f : α -> ε} (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: by
  convert! hf.enorm_rpow_div p
  rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, convert, div_eq_mul_inv, enorm_rpow_div, hf.enorm_rpow_div, hp_ne_top, hp_ne_zero, mul_inv_cancel
-/
theorem MemLp.enorm_rpow {f : α -> ε} (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    MemLp (fun x : α => ‖f x‖ₑ ^ p.toReal) 1 μ := by
  convert! hf.enorm_rpow_div p
  rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]

/--
theorem `MemLp.norm_rpow` / 定理 `MemLp.norm_rpow`

English:
theorem MemLp.norm_rpow
  given: {f : α -> E} (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: by
  convert! hf.norm_rpow_div p
  rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]

中文:
定理 MemLp.norm_rpow
  条件: {f : α -> E} (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: by
  convert! hf.norm_rpow_div p
  rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, convert, div_eq_mul_inv, hf.norm_rpow_div, hp_ne_top, hp_ne_zero, mul_inv_cancel, norm_rpow_div
-/
theorem MemLp.norm_rpow {f : α -> E} (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    MemLp (fun x : α => ‖f x‖ ^ p.toReal) 1 μ := by
  convert! hf.norm_rpow_div p
  rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]

/--
theorem `AEEqFun.compMeasurePreserving_mem_Lp` / 定理 `AEEqFun.compMeasurePreserving_mem_Lp`

English:
theorem AEEqFun.compMeasurePreserving_mem_Lp
  statement: {β : Type*} [MeasurableSpace β]
  proof: by
  rw [Lp.mem_Lp_iff_eLpNorm_lt_top] at hg ⊢
  rwa [eLpNorm_compMeasurePreserving]

中文:
定理 AEEqFun.compMeasurePreserving_mem_Lp
  结论: {β : 类型} [MeasurableSpace β]
  证明: by
  rw [Lp.mem_Lp_iff_eLpNorm_lt_top] at hg ⊢
  rwa [eLpNorm_compMeasurePreserving]

Depends on / 依赖: Lp.mem_Lp_iff_eLpNorm_lt_top, eLpNorm_compMeasurePreserving, mem_Lp_iff_eLpNorm_lt_top
-/
theorem AEEqFun.compMeasurePreserving_mem_Lp {β : Type*} [MeasurableSpace β]
    {μb : MeasureTheory.Measure β} {g : β ->ₘ[μb] E} (hg : g in Lp E p μb) {f : α -> β}
    (hf : MeasurePreserving f μ μb) :
    g.compMeasurePreserving f hf in Lp E p μ := by
  rw [Lp.mem_Lp_iff_eLpNorm_lt_top] at hg ⊢
  rwa [eLpNorm_compMeasurePreserving]

namespace Lp

/-! ### Composition with a measure-preserving function -/

variable {β : Type*} [MeasurableSpace β] {μb : MeasureTheory.Measure β} {f : α -> β}

/--
Definition of `compMeasurePreserving` / `compMeasurePreserving` 的定义

English:
definition compMeasurePreserving
  signature: (f : α -> β) (hf : MeasurePreserving f μ μb)
  body: ⟨g.1.compMeasurePreserving f hf, g.1.compMeasurePreserving_mem_Lp g.2 hf⟩
  map_zero' := rfl
  map_add' := by rintro ⟨⟨_⟩, _⟩ ⟨⟨_⟩, _⟩; rfl

@[simp]

中文:
定义 compMeasurePreserving
  签名: (f : α -> β) (hf : MeasurePreserving f μ μb)
  定义体: ⟨g.1.compMeasurePreserving f hf, g.1.compMeasurePreserving_mem_Lp g.2 hf⟩
  map_zero' := rfl
  map_add' := by rintro ⟨⟨_⟩, _⟩ ⟨⟨_⟩, _⟩; rfl

@[simp]

Depends on / 依赖: compMeasurePreserving, compMeasurePreserving_mem_Lp
-/
def compMeasurePreserving (f : α -> β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb ->+ Lp E p μ where
  toFun g := ⟨g.1.compMeasurePreserving f hf, g.1.compMeasurePreserving_mem_Lp g.2 hf⟩
  map_zero' := rfl
  map_add' := by rintro ⟨⟨_⟩, _⟩ ⟨⟨_⟩, _⟩; rfl

@[simp]
/--
theorem `compMeasurePreserving_val` / 定理 `compMeasurePreserving_val`

English:
theorem compMeasurePreserving_val
  given: (g : Lp E p μb) (hf : MeasurePreserving f μ μb)
  proof: rfl

中文:
定理 compMeasurePreserving_val
  条件: (g : Lp E p μb) (hf : MeasurePreserving f μ μb)
  证明: rfl
-/
theorem compMeasurePreserving_val (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    (compMeasurePreserving f hf g).1 = g.1.compMeasurePreserving f hf :=
  rfl

/--
theorem `coeFn_compMeasurePreserving` / 定理 `coeFn_compMeasurePreserving`

English:
theorem coeFn_compMeasurePreserving
  given: (g : Lp E p μb) (hf : MeasurePreserving f μ μb)
  proof: g.1.coeFn_compMeasurePreserving hf

@[simp]

中文:
定理 coeFn_compMeasurePreserving
  条件: (g : Lp E p μb) (hf : MeasurePreserving f μ μb)
  证明: g.1.coeFn_compMeasurePreserving hf

@[simp]

Depends on / 依赖: coeFn_compMeasurePreserving
-/
theorem coeFn_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    compMeasurePreserving f hf g =ᵐ[μ] g ∘ f :=
  g.1.coeFn_compMeasurePreserving hf

@[simp]
/--
theorem `norm_compMeasurePreserving` / 定理 `norm_compMeasurePreserving`

English:
theorem norm_compMeasurePreserving
  given: (g : Lp E p μb) (hf : MeasurePreserving f μ μb)
  proof: congr_arg ENNReal.toReal g.1.eLpNorm_compMeasurePreserving hf

中文:
定理 norm_compMeasurePreserving
  条件: (g : Lp E p μb) (hf : MeasurePreserving f μ μb)
  证明: congr_arg ENNReal.toReal g.1.eLpNorm_compMeasurePreserving hf

Depends on / 依赖: ENNReal, ENNReal.toReal, congr_arg, eLpNorm_compMeasurePreserving, toReal
-/
theorem norm_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    ‖compMeasurePreserving f hf g‖ = ‖g‖ :=
congr_arg ENNReal.toReal g.1.eLpNorm_compMeasurePreserving hf

/--
theorem `isometry_compMeasurePreserving` / 定理 `isometry_compMeasurePreserving`

English:
theorem isometry_compMeasurePreserving
  given: [Fact (1 <= p)] (hf : MeasurePreserving f μ μb)
  proof: AddMonoidHomClass.isometry_of_norm _ (norm_compMeasurePreserving · hf)

中文:
定理 isometry_compMeasurePreserving
  条件: [Fact (1 <= p)] (hf : MeasurePreserving f μ μb)
  证明: AddMonoidHomClass.isometry_of_norm _ (norm_compMeasurePreserving · hf)

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, isometry_of_norm, norm_compMeasurePreserving
-/
theorem isometry_compMeasurePreserving [Fact (1 <= p)] (hf : MeasurePreserving f μ μb) :
    Isometry (compMeasurePreserving f hf : Lp E p μb -> Lp E p μ) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_compMeasurePreserving · hf)

/--
theorem `toLp_compMeasurePreserving` / 定理 `toLp_compMeasurePreserving`

English:
theorem toLp_compMeasurePreserving
  given: {g : β -> E} (hg : MemLp g p μb) (hf : MeasurePreserving f μ μb)
  proof: rfl

@[simp]

中文:
定理 toLp_compMeasurePreserving
  条件: {g : β -> E} (hg : MemLp g p μb) (hf : MeasurePreserving f μ μb)
  证明: rfl

@[simp]
-/
theorem toLp_compMeasurePreserving {g : β -> E} (hg : MemLp g p μb) (hf : MeasurePreserving f μ μb) :
    compMeasurePreserving f hf (hg.toLp g) = (hg.comp_measurePreserving hf).toLp _ := rfl

@[simp]
/--
theorem `compMeasurePreserving_id` / 定理 `compMeasurePreserving_id`

English:
theorem compMeasurePreserving_id
  proof: by
  ext
  simp

中文:
定理 compMeasurePreserving_id
  证明: by
  ext
  simp

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id
-/
theorem compMeasurePreserving_id :
    compMeasurePreserving (E := E) (p := p) id (.id μb) = AddMonoidHom.id _ := by
  ext
  simp

/--
theorem `compMeasurePreserving_id_apply` / 定理 `compMeasurePreserving_id_apply`

English:
theorem compMeasurePreserving_id_apply
  given: (g : Lp E p μb)
  proof: by simp

中文:
定理 compMeasurePreserving_id_apply
  条件: (g : Lp E p μb)
  证明: by simp
-/
theorem compMeasurePreserving_id_apply (g : Lp E p μb) :
    compMeasurePreserving id (MeasurePreserving.id μb) g = g := by simp

/--
theorem `compMeasurePreserving_comp` / 定理 `compMeasurePreserving_comp`

English:
theorem compMeasurePreserving_comp
  statement: {γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ}
  proof: by
  ext g
  simp [AEEqFun.compMeasurePreserving_comp _ hf hf']

中文:
定理 compMeasurePreserving_comp
  结论: {γ : 类型} {mγ : MeasurableSpace γ} {μc : Measure γ}
  证明: by
  ext g
  simp [AEEqFun.compMeasurePreserving_comp _ hf hf']

Depends on / 依赖: hf.comp
-/
theorem compMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ}
    {f : β -> γ} (hf : MeasurePreserving f μb μc) {f' : α -> β} (hf' : MeasurePreserving f' μ μb) :
    compMeasurePreserving (E := E) (p := p) (f ∘ f') (hf.comp hf') =
    (compMeasurePreserving f' hf').comp (compMeasurePreserving f hf) := by
  ext g
  simp [AEEqFun.compMeasurePreserving_comp _ hf hf']

/--
theorem `compMeasurePreserving_comp_apply` / 定理 `compMeasurePreserving_comp_apply`

English:
theorem compMeasurePreserving_comp_apply
  statement: {γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ}
  proof: by
  simp [compMeasurePreserving_comp hf hf']

中文:
定理 compMeasurePreserving_comp_apply
  结论: {γ : 类型} {mγ : MeasurableSpace γ} {μc : Measure γ}
  证明: by
  simp [compMeasurePreserving_comp hf hf']

Depends on / 依赖: compMeasurePreserving_comp
-/
theorem compMeasurePreserving_comp_apply {γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ}
    (g : Lp E p μc) {f : β -> γ} (hf : MeasurePreserving f μb μc) {f' : α -> β}
    (hf' : MeasurePreserving f' μ μb) :
    (compMeasurePreserving (f ∘ f') (hf.comp hf')) g =
    (compMeasurePreserving f' hf') ((compMeasurePreserving f hf) g) := by
  simp [compMeasurePreserving_comp hf hf']

/--
theorem `compMeasurePreserving_iterate` / 定理 `compMeasurePreserving_iterate`

English:
theorem compMeasurePreserving_iterate
  given: {f : α -> α} (hf : MeasurePreserving f μ μ) (n : Nat)
  proof: by
  funext
  induction n with
  | zero => simp
  | succ n h =>
    nth_rewrite 1 [add_comm n 1]
    simp [Function.iterate_add, h, compMeasurePreserving_comp (hf.iterate n) hf]

中文:
定理 compMeasurePreserving_iterate
  条件: {f : α -> α} (hf : MeasurePreserving f μ μ) (n : 自然数)
  证明: by
  funext
  induction n with
  | zero => simp
  | succ n h =>
    nth_rewrite 1 [add_comm n 1]
    simp [Function.iterate_add, h, compMeasurePreserving_comp (hf.iterate n) hf]
-/
theorem compMeasurePreserving_iterate {f : α -> α} (hf : MeasurePreserving f μ μ) (n : Nat) :
    (compMeasurePreserving (E := E) (p := p) f hf)^[n] =
    compMeasurePreserving f^[n] (MeasurePreserving.iterate hf n) := by
  funext
  induction n with
  | zero => simp
  | succ n h =>
    nth_rewrite 1 [add_comm n 1]
    simp [Function.iterate_add, h, compMeasurePreserving_comp (hf.iterate n) hf]

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- `MeasureTheory.Lp.compMeasurePreserving` as a linear map. -/
@[simps]
/--
Definition of `compMeasurePreservingₗ` / `compMeasurePreservingₗ` 的定义

English:
definition compMeasurePreservingₗ
  signature: (f : α -> β) (hf : MeasurePreserving f μ μb)
  body: compMeasurePreserving f hf
  map_smul' c g := by rcases g with ⟨⟨_⟩, _⟩; rfl

中文:
定义 compMeasurePreservingₗ
  签名: (f : α -> β) (hf : MeasurePreserving f μ μb)
  定义体: compMeasurePreserving f hf
  map_smul' c g := by rcases g with ⟨⟨_⟩, _⟩; rfl

Depends on / 依赖: compMeasurePreserving
-/
def compMeasurePreservingₗ (f : α -> β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb ->ₗ[𝕜] Lp E p μ where
  __ := compMeasurePreserving f hf
  map_smul' c g := by rcases g with ⟨⟨_⟩, _⟩; rfl

/-- `MeasureTheory.Lp.compMeasurePreserving` as a linear isometry. -/
@[simps!]
/--
Definition of `compMeasurePreservingₗᵢ` / `compMeasurePreservingₗᵢ` 的定义

English:
definition compMeasurePreservingₗᵢ
  signature: [Fact (1 <= p)] (f : α -> β) (hf : MeasurePreserving f μ μb)
  body: compMeasurePreservingₗ 𝕜 f hf
  norm_map' := (norm_compMeasurePreserving · hf)

中文:
定义 compMeasurePreservingₗᵢ
  签名: [Fact (1 <= p)] (f : α -> β) (hf : MeasurePreserving f μ μb)
  定义体: compMeasurePreservingₗ 𝕜 f hf
  norm_map' := (norm_compMeasurePreserving · hf)
-/
def compMeasurePreservingₗᵢ [Fact (1 <= p)] (f : α -> β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb ->ₗᵢ[𝕜] Lp E p μ where
  toLinearMap := compMeasurePreservingₗ 𝕜 f hf
  norm_map' := (norm_compMeasurePreserving · hf)

end Lp

end MeasureTheory

open MeasureTheory

/-!
### Composition on `L^p`

We show that Lipschitz functions vanishing at zero act by composition on `L^p`, and specialize
this to the composition with continuous linear maps, and to the definition of the positive
part of an `L^p` function.
-/


section Composition

variable {g : E -> F} {c : Real>=0}

/--
theorem `LipschitzWith.comp_memLp` / 定理 `LipschitzWith.comp_memLp`

English:
theorem LipschitzWith.comp_memLp
  statement: {α E F} {K} [MeasurableSpace α] {μ : Measure α}
  proof: have : forall x, ‖g (f x)‖ <= K * ‖f x‖ := fun x => by
    -- TODO: add `LipschitzWith.nnnorm_sub_le` and `LipschitzWith.nnnorm_le`
    simpa [g0] using hg.norm_sub_le (f x) 0
  hL.of_le_mul (hg.continuous.comp_aestronglyMeasurable hL.1) (Eventually.of_forall this)

中文:
定理 LipschitzWith.comp_memLp
  结论: {α E F} {K} [MeasurableSpace α] {μ : Measure α}
  证明: have : forall x, ‖g (f x)‖ <= K * ‖f x‖ := fun x => by
    -- TODO: add `LipschitzWith.nnnorm_sub_le` and `LipschitzWith.nnnorm_le`
    simpa [g0] using hg.norm_sub_le (f x) 0
  hL.of_le_mul (hg.continuous.comp_aestronglyMeasurable hL.1) (Eventually.of_forall this)
-/
theorem LipschitzWith.comp_memLp {α E F} {K} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α -> E} {g : E -> F} (hg : LipschitzWith K g)
    (g0 : g 0 = 0) (hL : MemLp f p μ) : MemLp (g ∘ f) p μ :=
  have : forall x, ‖g (f x)‖ <= K * ‖f x‖ := fun x => by
    -- TODO: add `LipschitzWith.nnnorm_sub_le` and `LipschitzWith.nnnorm_le`
    simpa [g0] using hg.norm_sub_le (f x) 0
  hL.of_le_mul (hg.continuous.comp_aestronglyMeasurable hL.1) (Eventually.of_forall this)

/--
theorem `MeasureTheory.MemLp.of_comp_antilipschitzWith` / 定理 `MeasureTheory.MemLp.of_comp_antilipschitzWith`

English:
theorem MeasureTheory.MemLp.of_comp_antilipschitzWith
  statement: {α E F} {K'} [MeasurableSpace α]
  proof: by
  have A : forall x, ‖f x‖ <= K' * ‖g (f x)‖ := by
    intro x
    -- TODO: add `AntilipschitzWith.le_mul_nnnorm_sub` and `AntilipschitzWith.le_mul_norm`
    rw [← dist_zero_right]; rw [← dist_zero_right]; rw [← g0]
    apply hg'.le_mul_dist
  have B : AEStronglyMeasurable f μ :=
    (hg'.isUnifo

中文:
定理 MeasureTheory.MemLp.of_comp_antilipschitzWith
  结论: {α E F} {K'} [MeasurableSpace α]
  证明: by
  have A : forall x, ‖f x‖ <= K' * ‖g (f x)‖ := by
    intro x
    -- TODO: add `AntilipschitzWith.le_mul_nnnorm_sub` and `AntilipschitzWith.le_mul_norm`
    rw [← dist_zero_right]; rw [← dist_zero_right]; rw [← g0]
    apply hg'.le_mul_dist
  have B : AEStronglyMeasurable f μ :=
    (hg'.isUnifo
-/
theorem MeasureTheory.MemLp.of_comp_antilipschitzWith {α E F} {K'} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α -> E} {g : E -> F}
    (hL : MemLp (g ∘ f) p μ) (hg : UniformContinuous g) (hg' : AntilipschitzWith K' g)
    (g0 : g 0 = 0) : MemLp f p μ := by
  have A : forall x, ‖f x‖ <= K' * ‖g (f x)‖ := by
    intro x
    -- TODO: add `AntilipschitzWith.le_mul_nnnorm_sub` and `AntilipschitzWith.le_mul_norm`
    rw [← dist_zero_right]; rw [← dist_zero_right]; rw [← g0]
    apply hg'.le_mul_dist
  have B : AEStronglyMeasurable f μ :=
    (hg'.isUniformEmbedding hg).isEmbedding.aestronglyMeasurable_comp_iff.1 hL.1
  exact hL.of_le_mul B (Filter.Eventually.of_forall A)

/--
lemma `MeasureTheory.MemLp.continuousLinearMap_comp` / 引理 `MeasureTheory.MemLp.continuousLinearMap_comp`

English:
lemma MeasureTheory.MemLp.continuousLinearMap_comp
  statement: [NontriviallyNormedField 𝕜]
  proof: LipschitzWith.comp_memLp L.lipschitz (by simp) h_Lp

中文:
引理 MeasureTheory.MemLp.continuousLinearMap_comp
  结论: [NontriviallyNormedField 𝕜]
  证明: LipschitzWith.comp_memLp L.lipschitz (by simp) h_Lp

Depends on / 依赖: L.lipschitz, LipschitzWith, LipschitzWith.comp_memLp, comp_memLp, h_Lp, lipschitz
-/
lemma MeasureTheory.MemLp.continuousLinearMap_comp [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {f : α -> E}
    (h_Lp : MemLp f p μ) (L : E ->L[𝕜] F) :
    MemLp (fun x => L (f x)) p μ :=
  LipschitzWith.comp_memLp L.lipschitz (by simp) h_Lp

namespace LipschitzWith

/--
theorem `memLp_comp_iff_of_antilipschitz` / 定理 `memLp_comp_iff_of_antilipschitz`

English:
theorem memLp_comp_iff_of_antilipschitz
  statement: {α E F} {K K'} [MeasurableSpace α] {μ : Measure α}
  proof: ⟨fun h => h.of_comp_antilipschitzWith hg.uniformContinuous hg' g0, fun h => hg.comp_memLp g0 h⟩

中文:
定理 memLp_comp_iff_of_antilipschitz
  结论: {α E F} {K K'} [MeasurableSpace α] {μ : Measure α}
  证明: ⟨fun h => h.of_comp_antilipschitzWith hg.uniformContinuous hg' g0, fun h => hg.comp_memLp g0 h⟩

Depends on / 依赖: comp_memLp, h.of_comp_antilipschitzWith, hg.comp_memLp, hg.uniformContinuous, of_comp_antilipschitzWith, uniformContinuous
-/
theorem memLp_comp_iff_of_antilipschitz {α E F} {K K'} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α -> E} {g : E -> F} (hg : LipschitzWith K g)
    (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) : MemLp (g ∘ f) p μ ↔ MemLp f p μ :=
  ⟨fun h => h.of_comp_antilipschitzWith hg.uniformContinuous hg' g0, fun h => hg.comp_memLp g0 h⟩

/--
Definition of `compLp` / `compLp` 的定义

English:
definition compLp
  signature: (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ)
  body: ⟨AEEqFun.comp g hg.continuous (f : α ->ₘ[μ] E), by
    rw [Lp.mem_Lp_iff_memLp]
    exact (hg.comp_memLp g0 (Lp.memLp f)).ae_eq (AEEqFun.coeFn_comp _ hg.continuous _).symm⟩

中文:
定义 compLp
  签名: (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ)
  定义体: ⟨AEEqFun.comp g hg.continuous (f : α ->ₘ[μ] E), by
    rw [Lp.mem_Lp_iff_memLp]
    exact (hg.comp_memLp g0 (Lp.memLp f)).ae_eq (AEEqFun.coeFn_comp _ hg.continuous _).symm⟩

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_comp, AEEqFun.comp, Lp.memLp, Lp.mem_Lp_iff_memLp, ae_eq, coeFn_comp, comp_memLp, continuous, hg.comp_memLp, hg.continuous, mem_Lp_iff_memLp
-/
def compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ :=
  ⟨AEEqFun.comp g hg.continuous (f : α ->ₘ[μ] E), by
    rw [Lp.mem_Lp_iff_memLp]
    exact (hg.comp_memLp g0 (Lp.memLp f)).ae_eq (AEEqFun.coeFn_comp _ hg.continuous _).symm⟩

/--
theorem `coeFn_compLp` / 定理 `coeFn_compLp`

English:
theorem coeFn_compLp
  given: (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ)
  proof: AEEqFun.coeFn_comp _ hg.continuous _

@[simp]

中文:
定理 coeFn_compLp
  条件: (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ)
  证明: AEEqFun.coeFn_comp _ hg.continuous _

@[simp]

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_comp, coeFn_comp, continuous, hg.continuous
-/
theorem coeFn_compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) :
    hg.compLp g0 f =ᵐ[μ] g ∘ f :=
  AEEqFun.coeFn_comp _ hg.continuous _

@[simp]
/--
theorem `compLp_zero` / 定理 `compLp_zero`

English:
theorem compLp_zero
  given: (hg : LipschitzWith c g) (g0 : g 0 = 0)
  statement: hg.compLp g0 (0 : Lp E p μ) = 0
  proof: by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  apply (coeFn_compLp _ _ _).trans
  filter_upwards [Lp.coeFn_zero E p μ] with _ ha
  simp only [ha, g0, Function.comp_apply, Pi.zero_apply]

中文:
定理 compLp_zero
  条件: (hg : LipschitzWith c g) (g0 : g 0 = 0)
  结论: hg.compLp g0 (0 : Lp E p μ) = 0
  证明: by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  apply (coeFn_compLp _ _ _).trans
  filter_upwards [Lp.coeFn_zero E p μ] with _ ha
  simp only [ha, g0, Function.comp_apply, Pi.zero_apply]

Depends on / 依赖: Function, Function.comp_apply, Lp.coeFn_zero, Lp.eq_zero_iff_ae_eq_zero, Pi.zero_apply, coeFn_compLp, coeFn_zero, comp_apply, eq_zero_iff_ae_eq_zero, filter_upwards, zero_apply
-/
theorem compLp_zero (hg : LipschitzWith c g) (g0 : g 0 = 0) : hg.compLp g0 (0 : Lp E p μ) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  apply (coeFn_compLp _ _ _).trans
  filter_upwards [Lp.coeFn_zero E p μ] with _ ha
  simp only [ha, g0, Function.comp_apply, Pi.zero_apply]

/--
theorem `norm_compLp_sub_le` / 定理 `norm_compLp_sub_le`

English:
theorem norm_compLp_sub_le
  given: (hg : LipschitzWith c g) (g0 : g 0 = 0) (f f' : Lp E p μ)
  proof: by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hg.coeFn_compLp g0 f, hg.coeFn_compLp g0 f',
    Lp.coeFn_sub (hg.compLp g0 f) (hg.compLp g0 f'), Lp.coeFn_sub f f'] with a ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, ← dist_eq_norm, Pi.sub_apply, Function.comp_apply]
  exact hg.dis

中文:
定理 norm_compLp_sub_le
  条件: (hg : LipschitzWith c g) (g0 : g 0 = 0) (f f' : Lp E p μ)
  证明: by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hg.coeFn_compLp g0 f, hg.coeFn_compLp g0 f',
    Lp.coeFn_sub (hg.compLp g0 f) (hg.compLp g0 f'), Lp.coeFn_sub f f'] with a ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, ← dist_eq_norm, Pi.sub_apply, Function.comp_apply]
  exact hg.dis

Depends on / 依赖: Function, Function.comp_apply, Lp.coeFn_sub, Lp.norm_le_mul_norm_of_ae_le_mul, Pi.sub_apply, coeFn_compLp, coeFn_sub, compLp, comp_apply, dist_eq_norm, dist_le_mul, filter_upwards, hg.coeFn_compLp, hg.compLp, hg.dist_le_mul, norm_le_mul_norm_of_ae_le_mul, sub_apply
-/
theorem norm_compLp_sub_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f f' : Lp E p μ) :
    ‖hg.compLp g0 f - hg.compLp g0 f'‖ <= c * ‖f - f'‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hg.coeFn_compLp g0 f, hg.coeFn_compLp g0 f',
    Lp.coeFn_sub (hg.compLp g0 f) (hg.compLp g0 f'), Lp.coeFn_sub f f'] with a ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, ← dist_eq_norm, Pi.sub_apply, Function.comp_apply]
  exact hg.dist_le_mul (f a) (f' a)

/--
theorem `norm_compLp_le` / 定理 `norm_compLp_le`

English:
theorem norm_compLp_le
  given: (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ)
  proof: by
  -- squeezed for performance reasons
  simpa only [compLp_zero, sub_zero] using hg.norm_compLp_sub_le g0 f 0

中文:
定理 norm_compLp_le
  条件: (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ)
  证明: by
  -- squeezed for performance reasons
  simpa only [compLp_zero, sub_zero] using hg.norm_compLp_sub_le g0 f 0
-/
theorem norm_compLp_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) :
    ‖hg.compLp g0 f‖ <= c * ‖f‖ := by
  -- squeezed for performance reasons
  simpa only [compLp_zero, sub_zero] using hg.norm_compLp_sub_le g0 f 0

/--
theorem `lipschitzWith_compLp` / 定理 `lipschitzWith_compLp`

English:
theorem lipschitzWith_compLp
  given: [Fact (1 <= p)] (hg : LipschitzWith c g) (g0 : g 0 = 0)
  proof: -- squeezed for performance reasons
  LipschitzWith.of_dist_le_mul fun f g => by simp only [dist_eq_norm, norm_compLp_sub_le]

中文:
定理 lipschitzWith_compLp
  条件: [Fact (1 <= p)] (hg : LipschitzWith c g) (g0 : g 0 = 0)
  证明: -- squeezed for performance reasons
  LipschitzWith.of_dist_le_mul fun f g => by simp only [dist_eq_norm, norm_compLp_sub_le]
-/
theorem lipschitzWith_compLp [Fact (1 <= p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    LipschitzWith c (hg.compLp g0 : Lp E p μ -> Lp F p μ) :=
  -- squeezed for performance reasons
  LipschitzWith.of_dist_le_mul fun f g => by simp only [dist_eq_norm, norm_compLp_sub_le]

/--
theorem `continuous_compLp` / 定理 `continuous_compLp`

English:
theorem continuous_compLp
  given: [Fact (1 <= p)] (hg : LipschitzWith c g) (g0 : g 0 = 0)
  proof: (lipschitzWith_compLp hg g0).continuous

中文:
定理 continuous_compLp
  条件: [Fact (1 <= p)] (hg : LipschitzWith c g) (g0 : g 0 = 0)
  证明: (lipschitzWith_compLp hg g0).continuous

Depends on / 依赖: continuous, lipschitzWith_compLp
-/
theorem continuous_compLp [Fact (1 <= p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    Continuous (hg.compLp g0 : Lp E p μ -> Lp F p μ) :=
  (lipschitzWith_compLp hg g0).continuous

end LipschitzWith

namespace ContinuousLinearMap

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜' F]
variable {σ : 𝕜 ->+* 𝕜'} [RingHomIsometric σ]

/--
Definition of `compLp` / `compLp` 的定义

English:
definition compLp
  signature: (L : E ->SL[σ] F) (f : Lp E p μ)
  body: L.lipschitz.compLp (map_zero L) f

中文:
定义 compLp
  签名: (L : E ->SL[σ] F) (f : Lp E p μ)
  定义体: L.lipschitz.compLp (map_zero L) f

Depends on / 依赖: L.lipschitz.compLp, compLp, lipschitz, map_zero
-/
def compLp (L : E ->SL[σ] F) (f : Lp E p μ) : Lp F p μ :=
  L.lipschitz.compLp (map_zero L) f

/--
theorem `coeFn_compLp` / 定理 `coeFn_compLp`

English:
theorem coeFn_compLp
  given: (L : E ->SL[σ] F) (f : Lp E p μ)
  statement: forallᵐ a ∂μ, (L.compLp f) a = L (f a)
  proof: LipschitzWith.coeFn_compLp _ _ _

中文:
定理 coeFn_compLp
  条件: (L : E ->SL[σ] F) (f : Lp E p μ)
  结论: 对任意ᵐ a ∂μ, (L.compLp f) a = L (f a)
  证明: LipschitzWith.coeFn_compLp _ _ _

Depends on / 依赖: LipschitzWith, LipschitzWith.coeFn_compLp, coeFn_compLp
-/
theorem coeFn_compLp (L : E ->SL[σ] F) (f : Lp E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a) :=
  LipschitzWith.coeFn_compLp _ _ _

/--
theorem `coeFn_compLp'` / 定理 `coeFn_compLp'`

English:
theorem coeFn_compLp'
  given: (L : E ->SL[σ] F) (f : Lp E p μ)
  statement: L.compLp f =ᵐ[μ] fun a => L (f a)
  proof: L.coeFn_compLp f

中文:
定理 coeFn_compLp'
  条件: (L : E ->SL[σ] F) (f : Lp E p μ)
  结论: L.compLp f =ᵐ[μ] fun a => L (f a)
  证明: L.coeFn_compLp f

Depends on / 依赖: L.coeFn_compLp, coeFn_compLp
-/
theorem coeFn_compLp' (L : E ->SL[σ] F) (f : Lp E p μ) : L.compLp f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f

/--
theorem `comp_memLp` / 定理 `comp_memLp`

English:
theorem comp_memLp
  given: (L : E ->SL[σ] F) (f : Lp E p μ)
  statement: MemLp (L ∘ f) p μ
  proof: (Lp.memLp (L.compLp f)).ae_eq (L.coeFn_compLp' f)

中文:
定理 comp_memLp
  条件: (L : E ->SL[σ] F) (f : Lp E p μ)
  结论: MemLp (L ∘ f) p μ
  证明: (Lp.memLp (L.compLp f)).ae_eq (L.coeFn_compLp' f)

Depends on / 依赖: L.coeFn_compLp, L.compLp, Lp.memLp, ae_eq, coeFn_compLp, compLp
-/
theorem comp_memLp (L : E ->SL[σ] F) (f : Lp E p μ) : MemLp (L ∘ f) p μ :=
  (Lp.memLp (L.compLp f)).ae_eq (L.coeFn_compLp' f)

/--
theorem `comp_memLp'` / 定理 `comp_memLp'`

English:
theorem comp_memLp'
  given: (L : E ->SL[σ] F) {f : α -> E} (hf : MemLp f p μ)
  statement: MemLp (L ∘ f) p μ
  proof: (L.comp_memLp (hf.toLp f)).ae_eq (EventuallyEq.fun_comp hf.coeFn_toLp _)

中文:
定理 comp_memLp'
  条件: (L : E ->SL[σ] F) {f : α -> E} (hf : MemLp f p μ)
  结论: MemLp (L ∘ f) p μ
  证明: (L.comp_memLp (hf.toLp f)).ae_eq (EventuallyEq.fun_comp hf.coeFn_toLp _)

Depends on / 依赖: EventuallyEq, EventuallyEq.fun_comp, L.comp_memLp, ae_eq, coeFn_toLp, comp_memLp, fun_comp, hf.coeFn_toLp, hf.toLp
-/
theorem comp_memLp' (L : E ->SL[σ] F) {f : α -> E} (hf : MemLp f p μ) : MemLp (L ∘ f) p μ :=
  (L.comp_memLp (hf.toLp f)).ae_eq (EventuallyEq.fun_comp hf.coeFn_toLp _)

section RCLike

variable {K : Type*} [RCLike K]

/--
theorem `_root_.MeasureTheory.MemLp.ofReal` / 定理 `_root_.MeasureTheory.MemLp.ofReal`

English:
theorem _root_.MeasureTheory.MemLp.ofReal
  given: {f : α -> Real} (hf : MemLp f p μ)
  proof: (@RCLike.ofRealCLM K _).comp_memLp' hf

中文:
定理 _root_.MeasureTheory.MemLp.ofReal
  条件: {f : α -> 实数} (hf : MemLp f p μ)
  证明: (@RCLike.ofRealCLM K _).comp_memLp' hf

Depends on / 依赖: RCLike, RCLike.ofRealCLM, comp_memLp, ofRealCLM
-/
theorem _root_.MeasureTheory.MemLp.ofReal {f : α -> Real} (hf : MemLp f p μ) :
    MemLp (fun x => (f x : K)) p μ :=
  (@RCLike.ofRealCLM K _).comp_memLp' hf

/--
theorem `_root_.MeasureTheory.memLp_re_im_iff` / 定理 `_root_.MeasureTheory.memLp_re_im_iff`

English:
theorem _root_.MeasureTheory.memLp_re_im_iff
  given: {f : α -> K}
  proof: by
  refine ⟨?_, fun hf => ⟨hf.re, hf.im⟩⟩
  rintro ⟨hre, him⟩
  convert! MeasureTheory.MemLp.add (ε := K) hre.ofReal (him.ofReal.const_mul RCLike.I)
  ext1 x
  rw [Pi.add_apply]; rw [mul_comm]; rw [RCLike.re_add_im]

中文:
定理 _root_.MeasureTheory.memLp_re_im_iff
  条件: {f : α -> K}
  证明: by
  refine ⟨?_, fun hf => ⟨hf.re, hf.im⟩⟩
  rintro ⟨hre, him⟩
  convert! MeasureTheory.MemLp.add (ε := K) hre.ofReal (him.ofReal.const_mul RCLike.I)
  ext1 x
  rw [Pi.add_apply]; rw [mul_comm]; rw [RCLike.re_add_im]

Depends on / 依赖: MeasureTheory, MeasureTheory.MemLp.add, Pi.add_apply, RCLike, RCLike.I, RCLike.re_add_im, add_apply, const_mul, convert, hf.im, hf.re, him.ofReal.const_mul, hre.ofReal, mul_comm, ofReal, re_add_im
-/
theorem _root_.MeasureTheory.memLp_re_im_iff {f : α -> K} :
    MemLp (fun x => RCLike.re (f x)) p μ ∧ MemLp (fun x => RCLike.im (f x)) p μ ↔
      MemLp f p μ := by
  refine ⟨?_, fun hf => ⟨hf.re, hf.im⟩⟩
  rintro ⟨hre, him⟩
  convert! MeasureTheory.MemLp.add (ε := K) hre.ofReal (him.ofReal.const_mul RCLike.I)
  ext1 x
  rw [Pi.add_apply]; rw [mul_comm]; rw [RCLike.re_add_im]

end RCLike

/--
theorem `add_compLp` / 定理 `add_compLp`

English:
theorem add_compLp
  given: (L L' : E ->SL[σ] F) (f : Lp E p μ)
  proof: by
  ext1
  grw [Lp.coeFn_add, coeFn_compLp', coeFn_compLp', coeFn_compLp']
  rfl

中文:
定理 add_compLp
  条件: (L L' : E ->SL[σ] F) (f : Lp E p μ)
  证明: by
  ext1
  grw [Lp.coeFn_add, coeFn_compLp', coeFn_compLp', coeFn_compLp']
  rfl

Depends on / 依赖: Lp.coeFn_add, coeFn_add, coeFn_compLp
-/
theorem add_compLp (L L' : E ->SL[σ] F) (f : Lp E p μ) :
    (L + L').compLp f = L.compLp f + L'.compLp f := by
  ext1
  grw [Lp.coeFn_add, coeFn_compLp', coeFn_compLp', coeFn_compLp']
  rfl

/--
theorem `smul_compLp` / 定理 `smul_compLp`

English:
theorem smul_compLp
  statement: {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F]
  proof: by
  ext1
  grw [Lp.coeFn_smul, coeFn_compLp', coeFn_compLp']
  rfl

中文:
定理 smul_compLp
  结论: {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F]
  证明: by
  ext1
  grw [Lp.coeFn_smul, coeFn_compLp', coeFn_compLp']
  rfl

Depends on / 依赖: Lp.coeFn_smul, coeFn_compLp, coeFn_smul
-/
theorem smul_compLp {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F]
    [SMulCommClass 𝕜' 𝕜'' F] (c : 𝕜'') (L : E ->SL[σ] F) (f : Lp E p μ) :
    (c • L).compLp f = c • L.compLp f := by
  ext1
  grw [Lp.coeFn_smul, coeFn_compLp', coeFn_compLp']
  rfl

/--
theorem `norm_compLp_le` / 定理 `norm_compLp_le`

English:
theorem norm_compLp_le
  given: (L : E ->SL[σ] F) (f : Lp E p μ)
  statement: ‖L.compLp f‖ <= ‖L‖ * ‖f‖
  proof: LipschitzWith.norm_compLp_le _ _ _

中文:
定理 norm_compLp_le
  条件: (L : E ->SL[σ] F) (f : Lp E p μ)
  结论: ‖L.compLp f‖ <= ‖L‖ * ‖f‖
  证明: LipschitzWith.norm_compLp_le _ _ _

Depends on / 依赖: LipschitzWith, LipschitzWith.norm_compLp_le, norm_compLp_le
-/
theorem norm_compLp_le (L : E ->SL[σ] F) (f : Lp E p μ) : ‖L.compLp f‖ <= ‖L‖ * ‖f‖ :=
  LipschitzWith.norm_compLp_le _ _ _

variable (μ p)

/--
Definition of `compLpₗ` / `compLpₗ` 的定义

English:
definition compLpₗ
  signature: (L : E ->SL[σ] F)
  body: L.compLp f
  map_add' f g := by
    ext1
    filter_upwards [Lp.coeFn_add f g, coeFn_compLp L (f + g), coeFn_compLp L f,
      coeFn_compLp L g, Lp.coeFn_add (L.compLp f) (L.compLp g)]
    intro a ha1 ha2 ha3 ha4 ha5
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, Pi.add_apply]
  map_smul' c f := b

中文:
定义 compLpₗ
  签名: (L : E ->SL[σ] F)
  定义体: L.compLp f
  map_add' f g := by
    ext1
    filter_upwards [Lp.coeFn_add f g, coeFn_compLp L (f + g), coeFn_compLp L f,
      coeFn_compLp L g, Lp.coeFn_add (L.compLp f) (L.compLp g)]
    intro a ha1 ha2 ha3 ha4 ha5
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, Pi.add_apply]
  map_smul' c f := b
-/
@[simps] def compLpₗ (L : E ->SL[σ] F) : Lp E p μ ->ₛₗ[σ] Lp F p μ where
  toFun f := L.compLp f
  map_add' f g := by
    ext1
    filter_upwards [Lp.coeFn_add f g, coeFn_compLp L (f + g), coeFn_compLp L f,
      coeFn_compLp L g, Lp.coeFn_add (L.compLp f) (L.compLp g)]
    intro a ha1 ha2 ha3 ha4 ha5
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, Pi.add_apply]
  map_smul' c f := by
    ext1
    filter_upwards [Lp.coeFn_smul c f, coeFn_compLp L (c • f), Lp.coeFn_smul (σ c) (L.compLp f),
      coeFn_compLp L f] with _ ha1 ha2 ha3 ha4
    simp only [ha1, ha2, ha3, ha4, Pi.smul_apply, map_smulₛₗ]

/--
Definition of `compLpL` / `compLpL` 的定义

English:
definition compLpL
  signature: [Fact (1 <= p)] (L : E ->SL[σ] F)
  body: LinearMap.mkContinuous (L.compLpₗ p μ) ‖L‖ L.norm_compLp_le

中文:
定义 compLpL
  签名: [Fact (1 <= p)] (L : E ->SL[σ] F)
  定义体: LinearMap.mkContinuous (L.compLpₗ p μ) ‖L‖ L.norm_compLp_le

Depends on / 依赖: L.compLp, L.norm_compLp_le, LinearMap, LinearMap.mkContinuous, mkContinuous, norm_compLp_le
-/
def compLpL [Fact (1 <= p)] (L : E ->SL[σ] F) : Lp E p μ ->SL[σ] Lp F p μ :=
  LinearMap.mkContinuous (L.compLpₗ p μ) ‖L‖ L.norm_compLp_le

variable {μ p}

/--
theorem `coeFn_compLpL` / 定理 `coeFn_compLpL`

English:
theorem coeFn_compLpL
  given: [Fact (1 <= p)] (L : E ->SL[σ] F) (f : Lp E p μ)
  proof: L.coeFn_compLp f

中文:
定理 coeFn_compLpL
  条件: [Fact (1 <= p)] (L : E ->SL[σ] F) (f : Lp E p μ)
  证明: L.coeFn_compLp f

Depends on / 依赖: L.coeFn_compLp, coeFn_compLp
-/
theorem coeFn_compLpL [Fact (1 <= p)] (L : E ->SL[σ] F) (f : Lp E p μ) :
    L.compLpL p μ f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f

/--
theorem `add_compLpL` / 定理 `add_compLpL`

English:
theorem add_compLpL
  given: [Fact (1 <= p)] (L L' : E ->SL[σ] F)
  proof: by ext1 f; exact add_compLp L L' f

中文:
定理 add_compLpL
  条件: [Fact (1 <= p)] (L L' : E ->SL[σ] F)
  证明: by ext1 f; exact add_compLp L L' f

Depends on / 依赖: add_compLp
-/
theorem add_compLpL [Fact (1 <= p)] (L L' : E ->SL[σ] F) :
    (L + L').compLpL p μ = L.compLpL p μ + L'.compLpL p μ := by ext1 f; exact add_compLp L L' f

/--
theorem `smul_compLpL` / 定理 `smul_compLpL`

English:
theorem smul_compLpL
  statement: [Fact (1 <= p)] {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F]
  proof: by
  ext1 f; exact smul_compLp c L f

中文:
定理 smul_compLpL
  结论: [Fact (1 <= p)] {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F]
  证明: by
  ext1 f; exact smul_compLp c L f

Depends on / 依赖: smul_compLp
-/
theorem smul_compLpL [Fact (1 <= p)] {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F]
    [SMulCommClass 𝕜' 𝕜'' F] (c : 𝕜'') (L : E ->SL[σ] F) :
    (c • L).compLpL p μ = c • L.compLpL p μ := by
  ext1 f; exact smul_compLp c L f

/--
theorem `norm_compLpL_le` / 定理 `norm_compLpL_le`

English:
theorem norm_compLpL_le
  given: [Fact (1 <= p)] (L : E ->SL[σ] F)
  statement: ‖L.compLpL p μ‖ <= ‖L‖
  proof: LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

中文:
定理 norm_compLpL_le
  条件: [Fact (1 <= p)] (L : E ->SL[σ] F)
  结论: ‖L.compLpL p μ‖ <= ‖L‖
  证明: LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, mkContinuous_norm_le, norm_nonneg
-/
theorem norm_compLpL_le [Fact (1 <= p)] (L : E ->SL[σ] F) : ‖L.compLpL p μ‖ <= ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

section Bilinear

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (μ p) in
/--
Definition of `compLpₗ₂` / `compLpₗ₂` 的定义

English:
definition compLpₗ₂
  signature: (B : G ->L[𝕜] E ->L[𝕜] F)
  body: (B g).compLpₗ p μ
  map_add' g h := by
    ext f
    filter_upwards [(B (g + h)).coeFn_compLp f, (B g).coeFn_compLp f, (B h).coeFn_compLp f,
      Lp.coeFn_add ((B g).compLp f) ((B h).compLp f)] with x hx hg hh hadd
    simp only [compLpₗ_apply, LinearMap.add_apply, hx, hadd]
    simp only [map_add,

中文:
定义 compLpₗ₂
  签名: (B : G ->L[𝕜] E ->L[𝕜] F)
  定义体: (B g).compLpₗ p μ
  map_add' g h := by
    ext f
    filter_upwards [(B (g + h)).coeFn_compLp f, (B g).coeFn_compLp f, (B h).coeFn_compLp f,
      Lp.coeFn_add ((B g).compLp f) ((B h).compLp f)] with x hx hg hh hadd
    simp only [compLpₗ_apply, LinearMap.add_apply, hx, hadd]
    simp only [map_add,
-/
@[simps] def compLpₗ₂ (B : G ->L[𝕜] E ->L[𝕜] F) : G ->ₗ[𝕜] Lp E p μ ->ₗ[𝕜] Lp F p μ where
  toFun g := (B g).compLpₗ p μ
  map_add' g h := by
    ext f
    filter_upwards [(B (g + h)).coeFn_compLp f, (B g).coeFn_compLp f, (B h).coeFn_compLp f,
      Lp.coeFn_add ((B g).compLp f) ((B h).compLp f)] with x hx hg hh hadd
    simp only [compLpₗ_apply, LinearMap.add_apply, hx, hadd]
    simp only [map_add, add_apply, Pi.add_apply, hg, hh]
  map_smul' c g := by
    ext f
    filter_upwards [(c • B g).coeFn_compLp f, (B g).coeFn_compLp f,
      Lp.coeFn_smul c ((B g).compLp f)] with x hx hg hsmul
    simp [hx, hsmul, hg]

variable (μ p) in
/--
Definition of `compLpL₂` / `compLpL₂` 的定义

English:
definition compLpL₂
  signature: [Fact (1 <= p)] (B : G ->L[𝕜] E ->L[𝕜] F)
  body: (B.compLpₗ₂ p μ).mkContinuous₂ ‖B‖ (fun c f => by
    simp only [compLpₗ₂_apply, compLpₗ_apply]
    grw [norm_compLp_le, le_opNorm])

中文:
定义 compLpL₂
  签名: [Fact (1 <= p)] (B : G ->L[𝕜] E ->L[𝕜] F)
  定义体: (B.compLpₗ₂ p μ).mkContinuous₂ ‖B‖ (fun c f => by
    simp only [compLpₗ₂_apply, compLpₗ_apply]
    grw [norm_compLp_le, le_opNorm])

Depends on / 依赖: B.compLp, le_opNorm, norm_compLp_le
-/
def compLpL₂ [Fact (1 <= p)] (B : G ->L[𝕜] E ->L[𝕜] F) :
    G ->L[𝕜] Lp E p μ ->L[𝕜] Lp F p μ :=
  (B.compLpₗ₂ p μ).mkContinuous₂ ‖B‖ (fun c f => by
    simp only [compLpₗ₂_apply, compLpₗ_apply]
    grw [norm_compLp_le, le_opNorm])

/--
theorem `compLpL₂_apply_apply` / 定理 `compLpL₂_apply_apply`

English:
theorem compLpL₂_apply_apply
  given: [Fact (1 <= p)] (B : G ->L[𝕜] E ->L[𝕜] F) (g : G) (f : Lp E p μ)
  proof: rfl

中文:
定理 compLpL₂_apply_apply
  条件: [Fact (1 <= p)] (B : G ->L[𝕜] E ->L[𝕜] F) (g : G) (f : Lp E p μ)
  证明: rfl
-/
@[simp] theorem compLpL₂_apply_apply [Fact (1 <= p)] (B : G ->L[𝕜] E ->L[𝕜] F) (g : G) (f : Lp E p μ) :
    compLpL₂ p μ B g f = (B g).compLp f := rfl

/--
theorem `norm_compLpL₂_le` / 定理 `norm_compLpL₂_le`

English:
theorem norm_compLpL₂_le
  given: [Fact (1 <= p)] (B : G ->L[𝕜] E ->L[𝕜] F)
  proof: LinearMap.mkContinuous₂_norm_le _ (norm_nonneg _) _

中文:
定理 norm_compLpL₂_le
  条件: [Fact (1 <= p)] (B : G ->L[𝕜] E ->L[𝕜] F)
  证明: LinearMap.mkContinuous₂_norm_le _ (norm_nonneg _) _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, norm_nonneg
-/
theorem norm_compLpL₂_le [Fact (1 <= p)] (B : G ->L[𝕜] E ->L[𝕜] F) :
    ‖B.compLpL₂ p μ‖ <= ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg _) _

end Bilinear

end ContinuousLinearMap

namespace MeasureTheory.Lp

section LpToLpOfMeasureLeSMul

variable [NormedSpace Real E] {ν : Measure α} {c : Real>=0∞}

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def LpToLpOfMeasureLeSMulₗ (hc : c != ∞) (h : μ <= c • ν)
  body: ((Lp.memLp f).of_measure_le_smul hc h).toLp f
  map_add' f g := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    have : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
    apply this.ae_eq
    grw [Lp.coeFn_add]
  map_smul' c f := by
    ext
    grw [Mem

中文:
定义 noncomputable
  签名: def LpToLpOfMeasureLeSMulₗ (hc : c != ∞) (h : μ <= c • ν)
  定义体: ((Lp.memLp f).of_measure_le_smul hc h).toLp f
  map_add' f g := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    have : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
    apply this.ae_eq
    grw [Lp.coeFn_add]
  map_smul' c f := by
    ext
    grw [Mem
-/
private noncomputable def LpToLpOfMeasureLeSMulₗ (hc : c != ∞) (h : μ <= c • ν) :
    Lp E p ν ->ₗ[Real] Lp E p μ where
  toFun f := ((Lp.memLp f).of_measure_le_smul hc h).toLp f
  map_add' f g := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    have : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
    apply this.ae_eq
    grw [Lp.coeFn_add]
  map_smul' c f := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
    have : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
    apply this.ae_eq
    grw [Lp.coeFn_smul]
    rfl

/--
lemma `coeFn_LpToLpOfMeasureLeSMulₗ` / 引理 `coeFn_LpToLpOfMeasureLeSMulₗ`

English:
lemma coeFn_LpToLpOfMeasureLeSMulₗ
  given: (hc : c != ∞) (h : μ <= c • ν) (f : Lp E p ν)
  proof: by
  simp [LpToLpOfMeasureLeSMulₗ, MemLp.coeFn_toLp]

中文:
引理 coeFn_LpToLpOfMeasureLeSMulₗ
  条件: (hc : c != ∞) (h : μ <= c • ν) (f : Lp E p ν)
  证明: by
  simp [LpToLpOfMeasureLeSMulₗ, MemLp.coeFn_toLp]
-/
private lemma coeFn_LpToLpOfMeasureLeSMulₗ (hc : c != ∞) (h : μ <= c • ν) (f : Lp E p ν) :
    LpToLpOfMeasureLeSMulₗ hc h f =ᵐ[μ] f := by
  simp [LpToLpOfMeasureLeSMulₗ, MemLp.coeFn_toLp]

/--
lemma `enorm_LpToLpOfMeasureLeSMulₗ_apply_le` / 引理 `enorm_LpToLpOfMeasureLeSMulₗ_apply_le`

English:
lemma enorm_LpToLpOfMeasureLeSMulₗ_apply_le
  proof: by
  simp only [Lp.enorm_def]
  rw [eLpNorm_congr_ae (coeFn_LpToLpOfMeasureLeSMulₗ hc h f)]
  exact eLpNorm_le_of_measure_le_smul h

中文:
引理 enorm_LpToLpOfMeasureLeSMulₗ_apply_le
  证明: by
  simp only [Lp.enorm_def]
  rw [eLpNorm_congr_ae (coeFn_LpToLpOfMeasureLeSMulₗ hc h f)]
  exact eLpNorm_le_of_measure_le_smul h
-/
private lemma enorm_LpToLpOfMeasureLeSMulₗ_apply_le
    (hc : c != ∞) (h : μ <= c • ν) [Fact (1 <= p)] {f : Lp E p ν} :
    ‖LpToLpOfMeasureLeSMulₗ hc h f‖ₑ <= c ^ (1 / p).toReal * ‖f‖ₑ := by
  simp only [Lp.enorm_def]
  rw [eLpNorm_congr_ae (coeFn_LpToLpOfMeasureLeSMulₗ hc h f)]
  exact eLpNorm_le_of_measure_le_smul h

/--
lemma `norm_LpToLpOfMeasureLeSMulₗ_apply_le` / 引理 `norm_LpToLpOfMeasureLeSMulₗ_apply_le`

English:
lemma norm_LpToLpOfMeasureLeSMulₗ_apply_le
  proof: by
  simp only [← toReal_enorm]
  rw [ENNReal.toReal_rpow]; rw [← ENNReal.toReal_mul]
  grw [enorm_LpToLpOfMeasureLeSMulₗ_apply_le]
  simp [ENNReal.mul_eq_top, hc]

中文:
引理 norm_LpToLpOfMeasureLeSMulₗ_apply_le
  证明: by
  simp only [← toReal_enorm]
  rw [ENNReal.toReal_rpow]; rw [← ENNReal.toReal_mul]
  grw [enorm_LpToLpOfMeasureLeSMulₗ_apply_le]
  simp [ENNReal.mul_eq_top, hc]
-/
private lemma norm_LpToLpOfMeasureLeSMulₗ_apply_le
    (hc : c != ∞) (h : μ <= c • ν) [Fact (1 <= p)] {f : Lp E p ν} :
    ‖LpToLpOfMeasureLeSMulₗ hc h f‖ <= c.toReal ^ (1 / p).toReal * ‖f‖ := by
  simp only [← toReal_enorm]
  rw [ENNReal.toReal_rpow]; rw [← ENNReal.toReal_mul]
  grw [enorm_LpToLpOfMeasureLeSMulₗ_apply_le]
  simp [ENNReal.mul_eq_top, hc]

/-- The canonical map from `Lᵖ ν` to `Lᵖ μ` when `μ` is bounded by a finite multiple of `ν`. -/
@[no_expose]
/--
Definition of `LpToLpOfMeasureLeSMul` / `LpToLpOfMeasureLeSMul` 的定义

English:
definition LpToLpOfMeasureLeSMul
  signature: [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν)
  body: LinearMap.mkContinuous (LpToLpOfMeasureLeSMulₗ hc h) (c.toReal ^ (1 / p).toReal)
    (fun _ => norm_LpToLpOfMeasureLeSMulₗ_apply_le hc h)

中文:
定义 LpToLpOfMeasureLeSMul
  签名: [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν)
  定义体: LinearMap.mkContinuous (LpToLpOfMeasureLeSMulₗ hc h) (c.toReal ^ (1 / p).toReal)
    (fun _ => norm_LpToLpOfMeasureLeSMulₗ_apply_le hc h)

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, c.toReal, mkContinuous, toReal
-/
noncomputable def LpToLpOfMeasureLeSMul [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν) :
    Lp E p ν ->L[Real] Lp E p μ :=
  LinearMap.mkContinuous (LpToLpOfMeasureLeSMulₗ hc h) (c.toReal ^ (1 / p).toReal)
    (fun _ => norm_LpToLpOfMeasureLeSMulₗ_apply_le hc h)

/--
lemma `coeFn_LpToLpOfMeasureLeSMul` / 引理 `coeFn_LpToLpOfMeasureLeSMul`

English:
lemma coeFn_LpToLpOfMeasureLeSMul
  given: [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν) (f : Lp E p ν)
  proof: coeFn_LpToLpOfMeasureLeSMulₗ hc h f

中文:
引理 coeFn_LpToLpOfMeasureLeSMul
  条件: [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν) (f : Lp E p ν)
  证明: coeFn_LpToLpOfMeasureLeSMulₗ hc h f
-/
lemma coeFn_LpToLpOfMeasureLeSMul [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν) (f : Lp E p ν) :
    LpToLpOfMeasureLeSMul hc h f =ᵐ[μ] f :=
  coeFn_LpToLpOfMeasureLeSMulₗ hc h f

/--
lemma `norm_LpToLpOfMeasureLeSMul_le` / 引理 `norm_LpToLpOfMeasureLeSMul_le`

English:
lemma norm_LpToLpOfMeasureLeSMul_le
  given: [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν)
  proof: LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg (by simp) _) _

中文:
引理 norm_LpToLpOfMeasureLeSMul_le
  条件: [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν)
  证明: LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg (by simp) _) _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, Real.rpow_nonneg, mkContinuous_norm_le, rpow_nonneg
-/
lemma norm_LpToLpOfMeasureLeSMul_le [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν) :
    ‖(LpToLpOfMeasureLeSMul hc h : Lp E p ν ->L[Real] Lp E p μ)‖ <= c.toReal ^ (1 / p).toReal :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg (by simp) _) _

end LpToLpOfMeasureLeSMul

section PosPart

/--
theorem `lipschitzWith_pos_part` / 定理 `lipschitzWith_pos_part`

English:
theorem lipschitzWith_pos_part
  statement: LipschitzWith 1 fun x : Real => max x 0
  proof: LipschitzWith.id.max_const _

中文:
定理 lipschitzWith_pos_part
  结论: LipschitzWith 1 fun x : 实数 => max x 0
  证明: LipschitzWith.id.max_const _

Depends on / 依赖: LipschitzWith, LipschitzWith.id.max_const, max_const
-/
theorem lipschitzWith_pos_part : LipschitzWith 1 fun x : Real => max x 0 :=
  LipschitzWith.id.max_const _

/--
theorem `_root_.MeasureTheory.MemLp.pos_part` / 定理 `_root_.MeasureTheory.MemLp.pos_part`

English:
theorem _root_.MeasureTheory.MemLp.pos_part
  given: {f : α -> Real} (hf : MemLp f p μ)
  proof: lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf

中文:
定理 _root_.MeasureTheory.MemLp.pos_part
  条件: {f : α -> 实数} (hf : MemLp f p μ)
  证明: lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf

Depends on / 依赖: comp_memLp, le_rfl, lipschitzWith_pos_part, lipschitzWith_pos_part.comp_memLp, max_eq_right
-/
theorem _root_.MeasureTheory.MemLp.pos_part {f : α -> Real} (hf : MemLp f p μ) :
    MemLp (fun x => max (f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf

/--
theorem `_root_.MeasureTheory.MemLp.neg_part` / 定理 `_root_.MeasureTheory.MemLp.neg_part`

English:
theorem _root_.MeasureTheory.MemLp.neg_part
  given: {f : α -> Real} (hf : MemLp f p μ)
  proof: lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf.neg

中文:
定理 _root_.MeasureTheory.MemLp.neg_part
  条件: {f : α -> 实数} (hf : MemLp f p μ)
  证明: lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf.neg

Depends on / 依赖: comp_memLp, hf.neg, le_rfl, lipschitzWith_pos_part, lipschitzWith_pos_part.comp_memLp, max_eq_right
-/
theorem _root_.MeasureTheory.MemLp.neg_part {f : α -> Real} (hf : MemLp f p μ) :
    MemLp (fun x => max (-f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf.neg

/--
Definition of `posPart` / `posPart` 的定义

English:
definition posPart
  signature: (f : Lp Real p μ)
  body: lipschitzWith_pos_part.compLp (max_eq_right le_rfl) f

中文:
定义 posPart
  签名: (f : Lp 实数 p μ)
  定义体: lipschitzWith_pos_part.compLp (max_eq_right le_rfl) f

Depends on / 依赖: compLp, le_rfl, lipschitzWith_pos_part, lipschitzWith_pos_part.compLp, max_eq_right
-/
def posPart (f : Lp Real p μ) : Lp Real p μ :=
  lipschitzWith_pos_part.compLp (max_eq_right le_rfl) f

/--
Definition of `negPart` / `negPart` 的定义

English:
definition negPart
  signature: (f : Lp Real p μ)
  body: posPart (-f)

@[norm_cast]

中文:
定义 negPart
  签名: (f : Lp 实数 p μ)
  定义体: posPart (-f)

@[norm_cast]

Depends on / 依赖: posPart
-/
def negPart (f : Lp Real p μ) : Lp Real p μ :=
  posPart (-f)

@[norm_cast]
/--
theorem `coe_posPart` / 定理 `coe_posPart`

English:
theorem coe_posPart
  given: (f : Lp Real p μ)
  statement: (posPart f : α ->ₘ[μ] Real) = (f : α ->ₘ[μ] Real).posPart
  proof: rfl

中文:
定理 coe_posPart
  条件: (f : Lp 实数 p μ)
  结论: (posPart f : α ->ₘ[μ] 实数) = (f : α ->ₘ[μ] 实数).posPart
  证明: rfl
-/
theorem coe_posPart (f : Lp Real p μ) : (posPart f : α ->ₘ[μ] Real) = (f : α ->ₘ[μ] Real).posPart :=
  rfl

/--
theorem `coeFn_posPart` / 定理 `coeFn_posPart`

English:
theorem coeFn_posPart
  given: (f : Lp Real p μ)
  statement: ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0
  proof: AEEqFun.coeFn_posPart _

中文:
定理 coeFn_posPart
  条件: (f : Lp 实数 p μ)
  结论: ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0
  证明: AEEqFun.coeFn_posPart _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_posPart, coeFn_posPart
-/
theorem coeFn_posPart (f : Lp Real p μ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  AEEqFun.coeFn_posPart _

/--
theorem `coeFn_negPart_eq_max` / 定理 `coeFn_negPart_eq_max`

English:
theorem coeFn_negPart_eq_max
  given: (f : Lp Real p μ)
  statement: forallᵐ a ∂μ, negPart f a = max (-f a) 0
  proof: by
  rw [negPart]
  filter_upwards [coeFn_posPart (-f), coeFn_neg f] with _ h₁ h₂
  rw [h₁]; rw [h₂]; rw [Pi.neg_apply]

中文:
定理 coeFn_negPart_eq_max
  条件: (f : Lp 实数 p μ)
  结论: 对任意ᵐ a ∂μ, negPart f a = max (-f a) 0
  证明: by
  rw [negPart]
  filter_upwards [coeFn_posPart (-f), coeFn_neg f] with _ h₁ h₂
  rw [h₁]; rw [h₂]; rw [Pi.neg_apply]

Depends on / 依赖: Pi.neg_apply, coeFn_neg, coeFn_posPart, filter_upwards, negPart, neg_apply
-/
theorem coeFn_negPart_eq_max (f : Lp Real p μ) : forallᵐ a ∂μ, negPart f a = max (-f a) 0 := by
  rw [negPart]
  filter_upwards [coeFn_posPart (-f), coeFn_neg f] with _ h₁ h₂
  rw [h₁]; rw [h₂]; rw [Pi.neg_apply]

/--
theorem `coeFn_negPart` / 定理 `coeFn_negPart`

English:
theorem coeFn_negPart
  given: (f : Lp Real p μ)
  statement: forallᵐ a ∂μ, negPart f a = -min (f a) 0
  proof: (coeFn_negPart_eq_max f).mono fun a h => by rw [h, ← max_neg_neg, neg_zero]

中文:
定理 coeFn_negPart
  条件: (f : Lp 实数 p μ)
  结论: 对任意ᵐ a ∂μ, negPart f a = -min (f a) 0
  证明: (coeFn_negPart_eq_max f).mono fun a h => by rw [h, ← max_neg_neg, neg_zero]

Depends on / 依赖: coeFn_negPart_eq_max, max_neg_neg, neg_zero
-/
theorem coeFn_negPart (f : Lp Real p μ) : forallᵐ a ∂μ, negPart f a = -min (f a) 0 :=
  (coeFn_negPart_eq_max f).mono fun a h => by rw [h, ← max_neg_neg, neg_zero]

/--
theorem `continuous_posPart` / 定理 `continuous_posPart`

English:
theorem continuous_posPart
  given: [Fact (1 <= p)]
  statement: Continuous fun f : Lp Real p μ => posPart f
  proof: LipschitzWith.continuous_compLp _ _

中文:
定理 continuous_posPart
  条件: [Fact (1 <= p)]
  结论: Continuous fun f : Lp 实数 p μ => posPart f
  证明: LipschitzWith.continuous_compLp _ _

Depends on / 依赖: LipschitzWith, LipschitzWith.continuous_compLp, continuous_compLp
-/
theorem continuous_posPart [Fact (1 <= p)] : Continuous fun f : Lp Real p μ => posPart f :=
  LipschitzWith.continuous_compLp _ _

/--
theorem `continuous_negPart` / 定理 `continuous_negPart`

English:
theorem continuous_negPart
  given: [Fact (1 <= p)]
  statement: Continuous fun f : Lp Real p μ => negPart f
  proof: by
  unfold negPart
  exact continuous_posPart.comp continuous_neg

中文:
定理 continuous_negPart
  条件: [Fact (1 <= p)]
  结论: Continuous fun f : Lp 实数 p μ => negPart f
  证明: by
  unfold negPart
  exact continuous_posPart.comp continuous_neg

Depends on / 依赖: continuous_neg, continuous_posPart, continuous_posPart.comp, negPart
-/
theorem continuous_negPart [Fact (1 <= p)] : Continuous fun f : Lp Real p μ => negPart f := by
  unfold negPart
  exact continuous_posPart.comp continuous_neg

end PosPart

end MeasureTheory.Lp

end Composition

namespace MeasureTheory.Lp

/--
lemma `pow_mul_meas_ge_le_enorm` / 引理 `pow_mul_meas_ge_le_enorm`

English:
lemma pow_mul_meas_ge_le_enorm
  given: (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) (ε : Real>=0∞)
  proof: (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    pow_mul_meas_ge_le_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

中文:
引理 pow_mul_meas_ge_le_enorm
  条件: (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) (ε : 实数>=0∞)
  证明: (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    pow_mul_meas_ge_le_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, Lp.aestronglyMeasurable, aestronglyMeasurable, eLpNorm_ne_top, hp_ne_top, hp_ne_zero, ofReal_toReal, pow_mul_meas_ge_le_eLpNorm
-/
lemma pow_mul_meas_ge_le_enorm (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) (ε : Real>=0∞) :
    (ε * μ {x | ε <= ‖f x‖ₑ ^ p.toReal}) ^ (1 / p.toReal) <= ENNReal.ofReal ‖f‖ :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    pow_mul_meas_ge_le_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

/--
lemma `mul_meas_ge_le_pow_enorm` / 引理 `mul_meas_ge_le_pow_enorm`

English:
lemma mul_meas_ge_le_pow_enorm
  given: (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) (ε : Real>=0∞)
  proof: (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

中文:
引理 mul_meas_ge_le_pow_enorm
  条件: (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) (ε : 实数>=0∞)
  证明: (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, Lp.aestronglyMeasurable, aestronglyMeasurable, eLpNorm_ne_top, hp_ne_top, hp_ne_zero, mul_meas_ge_le_pow_eLpNorm, ofReal_toReal
-/
lemma mul_meas_ge_le_pow_enorm (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) (ε : Real>=0∞) :
    ε * μ {x | ε <= ‖f x‖ₑ ^ p.toReal} <= ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

/--
theorem `mul_meas_ge_le_pow_enorm'` / 定理 `mul_meas_ge_le_pow_enorm'`

English:
theorem mul_meas_ge_le_pow_enorm'
  statement: (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

中文:
定理 mul_meas_ge_le_pow_enorm'
  结论: (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, Lp.aestronglyMeasurable, aestronglyMeasurable, eLpNorm_ne_top, hp_ne_top, hp_ne_zero, mul_meas_ge_le_pow_eLpNorm, ofReal_toReal
-/
theorem mul_meas_ge_le_pow_enorm' (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    (ε : Real>=0∞) : ε ^ p.toReal * μ {x | ε <= ‖f x‖₊ } <= ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

/--
theorem `meas_ge_le_mul_pow_enorm` / 定理 `meas_ge_le_mul_pow_enorm`

English:
theorem meas_ge_le_mul_pow_enorm
  statement: (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {ε : Real>=0∞}
  proof: (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) hε (by simp)

中文:
定理 meas_ge_le_mul_pow_enorm
  结论: (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {ε : 实数>=0∞}
  证明: (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) hε (by simp)

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, Lp.aestronglyMeasurable, aestronglyMeasurable, eLpNorm_ne_top, hp_ne_top, hp_ne_zero, meas_ge_le_mul_pow_eLpNorm_enorm, ofReal_toReal
-/
theorem meas_ge_le_mul_pow_enorm (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {ε : Real>=0∞}
    (hε : ε != 0) : μ {x | ε <= ‖f x‖₊} <= ε⁻¹ ^ p.toReal * ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) hε (by simp)

section Star

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

/--
Instance `noncomputable` / 实例 `noncomputable`

English:
instance noncomputable
  signature: instance {p : Real>=0∞}
  body: ⟨star (f : α ->ₘ[μ] R),
    by simpa [Lp.mem_Lp_iff_eLpNorm_lt_top] using Lp.eLpNorm_lt_top f⟩

中文:
实例 noncomputable
  签名: instance {p : 实数>=0∞}
  定义体: ⟨star (f : α ->ₘ[μ] R),
    by simpa [Lp.mem_Lp_iff_eLpNorm_lt_top] using Lp.eLpNorm_lt_top f⟩
-/
protected noncomputable instance {p : Real>=0∞} : Star (Lp R p μ) where
  star f := ⟨star (f : α ->ₘ[μ] R),
    by simpa [Lp.mem_Lp_iff_eLpNorm_lt_top] using Lp.eLpNorm_lt_top f⟩

/--
lemma `coeFn_star` / 引理 `coeFn_star`

English:
lemma coeFn_star
  given: {p : Real>=0∞} (f : Lp R p μ)
  statement: (star f : Lp R p μ) =ᵐ[μ] star f
  proof: (f : α ->ₘ[μ] R).coeFn_star

中文:
引理 coeFn_star
  条件: {p : 实数>=0∞} (f : Lp R p μ)
  结论: (star f : Lp R p μ) =ᵐ[μ] star f
  证明: (f : α ->ₘ[μ] R).coeFn_star

Depends on / 依赖: coeFn_star
-/
lemma coeFn_star {p : Real>=0∞} (f : Lp R p μ) : (star f : Lp R p μ) =ᵐ[μ] star f :=
    (f : α ->ₘ[μ] R).coeFn_star

noncomputable instance {p : Real>=0∞} : InvolutiveStar (Lp R p μ) where
star_involutive _ := Subtype.ext star_involutive _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TrivialStar
  signature: R] {p
  body: Subtype.ext star_trivial _

中文:
实例 [TrivialStar
  签名: R] {p
  定义体: Subtype.ext star_trivial _

Depends on / 依赖: Subtype, Subtype.ext, star_trivial
-/
noncomputable instance [TrivialStar R] {p : Real>=0∞} : TrivialStar (Lp R p μ) where
star_trivial _ := Subtype.ext star_trivial _

end Star

end MeasureTheory.Lp
