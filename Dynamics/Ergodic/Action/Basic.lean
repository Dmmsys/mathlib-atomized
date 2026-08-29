/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Group.AEStabilizer
public import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Ergodic group actions

A group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar multiplication `(g • ·)`, `g : G`,
then it is either null or conull.
-/

public section

open Set Filter MeasureTheory MulAction
open scoped Pointwise

/--
Definition of `ErgodicVAdd` / `ErgodicVAdd` 的定义

English:
class ErgodicVAdd
  parameters: (G α : Type*) [VAdd G α] {_ : MeasurableSpace α} (μ : Measure α)
  extends: VAddInvariantMeasure G α μ
  axioms and operations (1):
    - aeconst_of_forall_preimage_vadd_ae_eq({s : Set α}) : MeasurableSet s -> (forall g : G, (g +ᵥ ·) ⁻¹' s =ᵐ[μ] s) -> EventuallyConst s (ae μ)

中文:
类 ErgodicVAdd
  参数: (G α : 类型) [VAdd G α] {_ : MeasurableSpace α} (μ : Measure α)
  继承: VAddInvariantMeasure G α μ
  公理与运算 (1 个):
    - aeconst_of_forall_preimage_vadd_ae_eq({s : Set α}) : MeasurableSet s -> (对任意 g : G, (g +ᵥ ·) ⁻¹' s =ᵐ[μ] s) -> EventuallyConst s (ae μ)
-/
class ErgodicVAdd (G α : Type*) [VAdd G α] {_ : MeasurableSpace α} (μ : Measure α) : Prop
    extends VAddInvariantMeasure G α μ where
  aeconst_of_forall_preimage_vadd_ae_eq {s : Set α} : MeasurableSet s ->
    (forall g : G, (g +ᵥ ·) ⁻¹' s =ᵐ[μ] s) -> EventuallyConst s (ae μ)

/--
A group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar multiplication `(g • ·)`, `g : G`,
then it is either null or conull.
-/
@[to_additive, mk_iff]
/--
Definition of `ErgodicSMul` / `ErgodicSMul` 的定义

English:
class ErgodicSMul
  parameters: (G α : Type*) [SMul G α] {_ : MeasurableSpace α} (μ : Measure α)
  extends: SMulInvariantMeasure G α μ
  axioms and operations (1):
    - aeconst_of_forall_preimage_smul_ae_eq({s : Set α}) : MeasurableSet s -> (forall g : G, (g • ·) ⁻¹' s =ᵐ[μ] s) -> EventuallyConst s (ae μ)

中文:
类 ErgodicSMul
  参数: (G α : 类型) [SMul G α] {_ : MeasurableSpace α} (μ : Measure α)
  继承: SMulInvariantMeasure G α μ
  公理与运算 (1 个):
    - aeconst_of_forall_preimage_smul_ae_eq({s : Set α}) : MeasurableSet s -> (对任意 g : G, (g • ·) ⁻¹' s =ᵐ[μ] s) -> EventuallyConst s (ae μ)
-/
class ErgodicSMul (G α : Type*) [SMul G α] {_ : MeasurableSpace α} (μ : Measure α) : Prop
    extends SMulInvariantMeasure G α μ where
  aeconst_of_forall_preimage_smul_ae_eq {s : Set α} : MeasurableSet s ->
    (forall g : G, (g • ·) ⁻¹' s =ᵐ[μ] s) -> EventuallyConst s (ae μ)

attribute [to_additive] ergodicSMul_iff

namespace MeasureTheory

variable (G : Type*) {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

@[to_additive]
/--
theorem `aeconst_of_forall_preimage_smul_ae_eq` / 定理 `aeconst_of_forall_preimage_smul_ae_eq`

English:
theorem aeconst_of_forall_preimage_smul_ae_eq
  statement: [SMul G α] [ErgodicSMul G α μ] {s : Set α}
  proof: by
  rcases hm with ⟨t, htm, hst⟩
  refine .congr ?_ hst.symm
  refine ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq htm fun g : G => ?_
  refine .trans (.trans ?_ (h g)) hst
  exact tendsto_smul_ae _ _ hst.symm

中文:
定理 aeconst_of_forall_preimage_smul_ae_eq
  结论: [SMul G α] [ErgodicSMul G α μ] {s : Set α}
  证明: by
  rcases hm with ⟨t, htm, hst⟩
  refine .congr ?_ hst.symm
  refine ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq htm fun g : G => ?_
  refine .trans (.trans ?_ (h g)) hst
  exact tendsto_smul_ae _ _ hst.symm

Depends on / 依赖: ErgodicSMul, ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq, aeconst_of_forall_preimage_smul_ae_eq, hst.symm, tendsto_smul_ae
-/
theorem aeconst_of_forall_preimage_smul_ae_eq [SMul G α] [ErgodicSMul G α μ] {s : Set α}
    (hm : NullMeasurableSet s μ) (h : forall g : G, (g • ·) ⁻¹' s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) := by
  rcases hm with ⟨t, htm, hst⟩
  refine .congr ?_ hst.symm
  refine ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq htm fun g : G => ?_
  refine .trans (.trans ?_ (h g)) hst
  exact tendsto_smul_ae _ _ hst.symm

section Group

variable [Group G] [MulAction G α] [ErgodicSMul G α μ] {s : Set α}

@[to_additive]
/--
theorem `aeconst_of_forall_smul_ae_eq` / 定理 `aeconst_of_forall_smul_ae_eq`

English:
theorem aeconst_of_forall_smul_ae_eq
  given: (hm : NullMeasurableSet s μ) (h : forall g : G, g • s =ᵐ[μ] s)
  proof: aeconst_of_forall_preimage_smul_ae_eq G hm fun g => by
    simpa only [preimage_smul] using h g⁻¹

@[to_additive]

中文:
定理 aeconst_of_forall_smul_ae_eq
  条件: (hm : NullMeasurableSet s μ) (h : 对任意 g : G, g • s =ᵐ[μ] s)
  证明: aeconst_of_forall_preimage_smul_ae_eq G hm fun g => by
    simpa only [preimage_smul] using h g⁻¹

@[to_additive]

Depends on / 依赖: aeconst_of_forall_preimage_smul_ae_eq, preimage_smul
-/
theorem aeconst_of_forall_smul_ae_eq (hm : NullMeasurableSet s μ) (h : forall g : G, g • s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) :=
  aeconst_of_forall_preimage_smul_ae_eq G hm fun g => by
    simpa only [preimage_smul] using h g⁻¹

@[to_additive]
/--
theorem `_root_.MulAction.aeconst_of_aestabilizer_eq_top` / 定理 `_root_.MulAction.aeconst_of_aestabilizer_eq_top`

English:
theorem _root_.MulAction.aeconst_of_aestabilizer_eq_top
  proof: aeconst_of_forall_smul_ae_eq G hm (Subgroup.eq_top_iff' _).1 h

中文:
定理 _root_.MulAction.aeconst_of_aestabilizer_eq_top
  证明: aeconst_of_forall_smul_ae_eq G hm (Subgroup.eq_top_iff' _).1 h

Depends on / 依赖: Subgroup, Subgroup.eq_top_iff, aeconst_of_forall_smul_ae_eq, eq_top_iff
-/
theorem _root_.MulAction.aeconst_of_aestabilizer_eq_top
    (hm : NullMeasurableSet s μ) (h : aestabilizer G μ s = ⊤) : EventuallyConst s (ae μ) :=
aeconst_of_forall_smul_ae_eq G hm (Subgroup.eq_top_iff' _).1 h

end Group

/--
theorem `_root_.ErgodicSMul.of_aestabilizer` / 定理 `_root_.ErgodicSMul.of_aestabilizer`

English:
theorem _root_.ErgodicSMul.of_aestabilizer
  statement: [Group G] [MulAction G α] [SMulInvariantMeasure G α μ]
  proof: ⟨fun hm hs => h _ hm (Subgroup.eq_top_iff' _).2 fun g => by
    simpa only [preimage_smul_inv] using! hs g⁻¹⟩

中文:
定理 _root_.ErgodicSMul.of_aestabilizer
  结论: [Group G] [MulAction G α] [SMulInvariantMeasure G α μ]
  证明: ⟨fun hm hs => h _ hm (Subgroup.eq_top_iff' _).2 fun g => by
    simpa only [preimage_smul_inv] using! hs g⁻¹⟩

Depends on / 依赖: Subgroup, Subgroup.eq_top_iff, eq_top_iff, preimage_smul_inv
-/
theorem _root_.ErgodicSMul.of_aestabilizer [Group G] [MulAction G α] [SMulInvariantMeasure G α μ]
    (h : forall s, MeasurableSet s -> aestabilizer G μ s = ⊤ -> EventuallyConst s (ae μ)) :
    ErgodicSMul G α μ :=
⟨fun hm hs => h _ hm (Subgroup.eq_top_iff' _).2 fun g => by
    simpa only [preimage_smul_inv] using! hs g⁻¹⟩

/--
theorem `ergodicSMul_iterateMulAct` / 定理 `ergodicSMul_iterateMulAct`

English:
theorem ergodicSMul_iterateMulAct
  given: {f : α -> α} (hf : Measurable f)
  proof: by
  simp only [ergodicSMul_iff, smulInvariantMeasure_iterateMulAct, hf]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, ⟨?_⟩⟩, fun h => ⟨h.1, ?_⟩⟩
  · intro s hm hs
    refine h₂ hm fun n => ?_
    nth_rewrite 2 [← Function.IsFixedPt.preimage_iterate hs n.val]
    rfl
  · intro s hm hs
exact h.quasiErgodic.aeconst_

中文:
定理 ergodicSMul_iterateMulAct
  条件: {f : α -> α} (hf : Measurable f)
  证明: by
  simp only [ergodicSMul_iff, smulInvariantMeasure_iterateMulAct, hf]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, ⟨?_⟩⟩, fun h => ⟨h.1, ?_⟩⟩
  · intro s hm hs
    refine h₂ hm fun n => ?_
    nth_rewrite 2 [← Function.IsFixedPt.preimage_iterate hs n.val]
    rfl
  · intro s hm hs
exact h.quasiErgodic.aeconst_

Depends on / 依赖: Function, Function.IsFixedPt.preimage_iterate, IsFixedPt, ergodicSMul_iff, h.quasiErgodic.aeconst_set, hm.nullMeasurableSet, n.val, nth_rewrite, nullMeasurableSet, preimage_iterate, quasiErgodic, smulInvariantMeasure_iterateMulAct
-/
theorem ergodicSMul_iterateMulAct {f : α -> α} (hf : Measurable f) :
    ErgodicSMul (IterateMulAct f) α μ ↔ Ergodic f μ := by
  simp only [ergodicSMul_iff, smulInvariantMeasure_iterateMulAct, hf]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, ⟨?_⟩⟩, fun h => ⟨h.1, ?_⟩⟩
  · intro s hm hs
    refine h₂ hm fun n => ?_
    nth_rewrite 2 [← Function.IsFixedPt.preimage_iterate hs n.val]
    rfl
  · intro s hm hs
exact h.quasiErgodic.aeconst_set₀ hm.nullMeasurableSet hs (.mk 1)

end MeasureTheory
