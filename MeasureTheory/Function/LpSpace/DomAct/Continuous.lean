/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Topology.Algebra.Constructions.DomMulAct

/-!
# Continuity of the action of `Mᵈᵐᵃ` on `MeasureSpace.Lp E p μ`

In this file we prove that under certain conditions,
the action of `Mᵈᵐᵃ` on `MeasureTheory.Lp E p μ` is continuous in both variables.

Recall that `Mᵈᵐᵃ` acts on `MeasureTheory.Lp E p μ`
by `mk c • f = MeasureTheory.Lp.compMeasurePreserving (c • ·) _ f`.
This action is defined, if `M` acts on `X` by measure-preserving maps.

If `M` acts on `X` by continuous maps
preserving a locally finite measure
which is inner regular for finite measure sets with respect to compact sets,
then the action of `Mᵈᵐᵃ` on `Lp E p μ` described above, `1 ≤ p < ∞`,
is continuous in both arguments.

In particular, it applies to the case when `X = M` is a locally compact topological group,
and `μ` is the Haar measure.

## Tags

measure theory, group action, domain action, continuous action, Lp space
-/

public section

open scoped ENNReal
open DomMulAct

namespace MeasureTheory

variable {X M E : Type*}
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [Monoid M] [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [SMul M X] [ContinuousSMul M X]
  [NormedAddCommGroup E]
  {μ : Measure X} [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [SMulInvariantMeasure M X μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [hp : Fact (p ≠ ∞)]

@[to_additive]
/-
**MeasureTheory.Lp.instContinuousSMulDomMulAct** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Lp`。
形式化陈述：∀ {X : Type u_1} {M : Type u_2} {E : Type u_3} [inst : TopologicalSpace X]
 [R1Space X] [inst_2 : MeasurableSpace X]   [inst_3 : BorelSpace X] [inst_4 : To
pologicalSpace M] [inst_5 : MeasurableSpace M] [inst_6 : OpensMeasurableSpace M]
   [inst_7 : SMul M X] [inst_8 : ContinuousSMul M X] [inst_9 : NormedAddCommGrou
p E] {μ : MeasureTheory.Measure X}   [MeasureTheory.IsLocallyFiniteMeasure μ] [μ
.InnerRegularCompactLTTop]   [inst_12 : MeasureTheory.SMulInvariantMeasure M X μ
] {p : ENNReal} [inst_13 : Fact (1 ≤ p)] [hp : Fact (p ≠ ⊤)],   ContinuousSMul M
ᵈᵐᵃ ↥(MeasureTheory.Lp E p μ)
参数：1 ≤ p；p ≠ ⊤；MeasureTheory.Lp E p μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DomAddAct.continuous_mk_symm`：∀ {M : Type u_1} [inst : TopologicalSpace 
M], Continuous ⇑DomAddAct.mk.symm
· 使用定理 `Continuous.compMeasurePreservingLp`：Continuous.compMeasurePreservingLp (
hf : Continuous f) (hg : Continuous g) (hgm : forall z, MeasurePreserving (g z) 
μ ν) (hp : p != ∞) : Con…
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
instance Lp.instContinuousSMulDomMulAct : ContinuousSMul Mᵈᵐᵃ (Lp E p μ) where
  continuous_smul :=
    let g : C(Mᵈᵐᵃ × Lp E p μ, C(X, X)) :=
      (ContinuousMap.mk (fun a : M × X ↦ a.1 • a.2) continuous_smul).curry.comp <|
        .comp (.mk DomMulAct.mk.symm) ContinuousMap.fst
    continuous_snd.compMeasurePreservingLp g.continuous _ Fact.out

end MeasureTheory

