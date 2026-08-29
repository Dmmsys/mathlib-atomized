/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Order.WithTop

/-!
# Borel measurable space on `WithTop`

For `ι` a linear order with the order topology, we define the Borel measurable space on `WithTop ι`.
We then prove that the natural inclusion `ι → WithTop ι` is measurable, and that the function
`WithTop.untopA : WithTop ι → ι` (which sends `⊤` to an arbitrary element of `ι`) is measurable.

## Main statements

* `measurable_of_measurable_comp_coe`: if `f : WithTop ι → α` is such that `f ∘ coe` is measurable,
  then `f` is measurable.
* `Measurable.withTop_coe`: the function `fun x : ι ↦ (x : WithTop ι)` is measurable.
* `Measurable.untopD`: for `d : ι`, the function `WithTop.untopD d : WithTop ι → ι` is measurable.
* `Measurable.untopA`: the function `WithTop.untopA : WithTop ι → ι` is measurable.

-/

@[expose] public section


namespace WithTop

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MeasurableSpace (WithTop ι)
  body: borel _

中文:
实例 :
  签名: 可测空间 (WithTop ι)
  定义体: borel _
-/
instance : MeasurableSpace (WithTop ι) := borel _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BorelSpace (WithTop ι)
  body: ⟨rfl⟩

中文:
实例 :
  签名: Borel空间 (WithTop ι)
  定义体: ⟨rfl⟩
-/
instance : BorelSpace (WithTop ι) := ⟨rfl⟩

variable [MeasurableSpace ι] [BorelSpace ι]

/-- Measurable equivalence between the non-top elements of `WithTop ι` and `ι`. -/
noncomputable
/--
Definition of `MeasurableEquiv.neTopEquiv` / `MeasurableEquiv.neTopEquiv` 的定义

English:
definition MeasurableEquiv.neTopEquiv
  signature: : { r : WithTop ι | r != ⊤ } ≃ᵐ ι
  body: (WithTop.neTopHomeomorph ι).toMeasurableEquiv

中文:
定义 可测等价.neTopEquiv
  签名: : { r : WithTop ι | r != ⊤ } ≃ᵐ ι
  定义体: (WithTop.neTopHomeomorph ι).toMeasurableEquiv

Depends on / 依赖: WithTop, WithTop.neTopHomeomorph, neTopHomeomorph, toMeasurableEquiv
-/
def MeasurableEquiv.neTopEquiv : { r : WithTop ι | r != ⊤ } ≃ᵐ ι :=
  (WithTop.neTopHomeomorph ι).toMeasurableEquiv

/--
lemma `measurable_of_measurable_comp_coe` / 引理 `measurable_of_measurable_comp_coe`

English:
lemma measurable_of_measurable_comp_coe
  statement: {α : Type*} {mα : MeasurableSpace α}
  proof: measurable_of_measurable_on_compl_singleton ⊤
    (MeasurableEquiv.neTopEquiv.symm.measurable_comp_iff.1 h)

中文:
引理 measurable_of_measurable_comp_coe
  结论: {α : 类型} {mα : 可测空间 α}
  证明: measurable_of_measurable_on_compl_singleton ⊤
    (MeasurableEquiv.neTopEquiv.symm.measurable_comp_iff.1 h)

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.neTopEquiv.symm.measurable_comp_iff, measurable_comp_iff, measurable_of_measurable_on_compl_singleton, neTopEquiv
-/
lemma measurable_of_measurable_comp_coe {α : Type*} {mα : MeasurableSpace α}
    {f : WithTop ι -> α} (h : Measurable fun p : ι => f p) :
    Measurable f :=
  measurable_of_measurable_on_compl_singleton ⊤
    (MeasurableEquiv.neTopEquiv.symm.measurable_comp_iff.1 h)

/--
lemma `measurable_untopD` / 引理 `measurable_untopD`

English:
lemma measurable_untopD
  given: (d : ι)
  statement: Measurable (untopD d)
  proof: measurable_of_measurable_comp_coe measurable_id

中文:
引理 measurable_untopD
  条件: (d : ι)
  结论: 可测 (untopD d)
  证明: measurable_of_measurable_comp_coe measurable_id

Depends on / 依赖: measurable_id, measurable_of_measurable_comp_coe
-/
lemma measurable_untopD (d : ι) : Measurable (untopD d) :=
  measurable_of_measurable_comp_coe measurable_id

/--
lemma `measurable_untopA` / 引理 `measurable_untopA`

English:
lemma measurable_untopA
  given: [Nonempty ι]
  statement: Measurable (WithTop.untopA (α := ι))
  proof: measurable_untopD _

中文:
引理 measurable_untopA
  条件: [非空 ι]
  结论: 可测 (WithTop.untopA (α := ι))
  证明: measurable_untopD _
-/
lemma measurable_untopA [Nonempty ι] : Measurable (WithTop.untopA (α := ι)) :=
  measurable_untopD _

/--
lemma `measurable_coe` / 引理 `measurable_coe`

English:
lemma measurable_coe
  statement: Measurable (fun x : ι => (x : WithTop ι))
  proof: continuous_coe.measurable

@[fun_prop]

中文:
引理 measurable_coe
  结论: 可测 (fun x : ι => (x : WithTop ι))
  证明: continuous_coe.measurable

@[fun_prop]

Depends on / 依赖: continuous_coe, continuous_coe.measurable, measurable
-/
lemma measurable_coe : Measurable (fun x : ι => (x : WithTop ι)) := continuous_coe.measurable

@[fun_prop]
/--
lemma `_root_.Measurable.withTop_coe` / 引理 `_root_.Measurable.withTop_coe`

English:
lemma _root_.Measurable.withTop_coe
  given: {α} {mα : MeasurableSpace α} {f : α -> ι} (hf : Measurable f)
  proof: measurable_coe.comp hf

@[fun_prop]

中文:
引理 _root_.可测.withTop_coe
  条件: {α} {mα : 可测空间 α} {f : α -> ι} (hf : 可测 f)
  证明: measurable_coe.comp hf

@[fun_prop]

Depends on / 依赖: measurable_coe, measurable_coe.comp
-/
lemma _root_.Measurable.withTop_coe {α} {mα : MeasurableSpace α} {f : α -> ι} (hf : Measurable f) :
    Measurable (fun x => (f x : WithTop ι)) :=
  measurable_coe.comp hf

@[fun_prop]
/--
lemma `_root_.Measurable.untopD` / 引理 `_root_.Measurable.untopD`

English:
lemma _root_.Measurable.untopD
  statement: {α} {mα : MeasurableSpace α} (d : ι)
  proof: (measurable_untopD d).comp hf

@[fun_prop]

中文:
引理 _root_.可测.untopD
  结论: {α} {mα : 可测空间 α} (d : ι)
  证明: (measurable_untopD d).comp hf

@[fun_prop]

Depends on / 依赖: measurable_untopD
-/
lemma _root_.Measurable.untopD {α} {mα : MeasurableSpace α} (d : ι)
    {f : α -> WithTop ι} (hf : Measurable f) :
    Measurable (fun x => (f x).untopD d) := (measurable_untopD d).comp hf

@[fun_prop]
/--
lemma `_root_.Measurable.untopA` / 引理 `_root_.Measurable.untopA`

English:
lemma _root_.Measurable.untopA
  statement: {α} {mα : MeasurableSpace α} [Nonempty ι]
  proof: hf.untopD _

中文:
引理 _root_.可测.untopA
  结论: {α} {mα : 可测空间 α} [非空 ι]
  证明: hf.untopD _

Depends on / 依赖: hf.untopD, untopD
-/
lemma _root_.Measurable.untopA {α} {mα : MeasurableSpace α} [Nonempty ι]
    {f : α -> WithTop ι} (hf : Measurable f) :
    Measurable (fun x => (f x).untopA) := hf.untopD _

/--
Definition of `measurableEquivSum` / `measurableEquivSum` 的定义

English:
definition measurableEquivSum
  signature: : WithTop ι ≃ᵐ ι oplus Unit
  body: { Equiv.optionEquivSumPUnit ι with
    measurable_toFun := measurable_of_measurable_comp_coe measurable_inl
    measurable_invFun := measurable_fun_sum measurable_coe (@measurable_const _ Unit _ _ ⊤) }

中文:
定义 measurableEquivSum
  签名: : WithTop ι ≃ᵐ ι oplus 单元
  定义体: { Equiv.optionEquivSumPUnit ι with
    measurable_toFun := measurable_of_measurable_comp_coe measurable_inl
    measurable_invFun := measurable_fun_sum measurable_coe (@measurable_const _ Unit _ _ ⊤) }

Depends on / 依赖: Equiv.optionEquivSumPUnit, measurable_coe, measurable_const, measurable_fun_sum, measurable_inl, measurable_invFun, measurable_of_measurable_comp_coe, measurable_toFun, optionEquivSumPUnit
-/
def measurableEquivSum : WithTop ι ≃ᵐ ι oplus Unit :=
  { Equiv.optionEquivSumPUnit ι with
    measurable_toFun := measurable_of_measurable_comp_coe measurable_inl
    measurable_invFun := measurable_fun_sum measurable_coe (@measurable_const _ Unit _ _ ⊤) }

end WithTop
