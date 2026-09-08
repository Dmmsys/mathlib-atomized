/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# The reals are complete

This file provides the instances `CompleteSpace ℝ` and `CompleteSpace ℝ≥0`.
Along the way, we add a shortcut instance for the natural topology on `ℝ≥0`
(the one induced from `ℝ`), and add some basic API.
-/

@[expose] public section

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

noncomputable section

open Filter Metric Set

/-
**Real.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.instCompleteSpace : CompleteSpace Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.complete_of_cauchySeq_tendsto`：Metric.complete_of_cauchySeq_tends
to : (forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) -> Co
mpleteSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.cauchySeq_iff'`：Metric.cauchySeq_iff' {u : β -> α} : CauchySeq u 
↔ forall ε > 0, exists N, forall n >= N, dist (u n) (u N) < ε
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Real.instIsCompleteAbs`：CauSeq.IsComplete ℝ abs
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
instance Real.instCompleteSpace : CompleteSpace ℝ := by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq ℝ abs := ⟨u, Metric.cauchySeq_iff'.1 hu⟩
  refine ⟨c.lim, fun s h => ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets]
  exact this.imp fun N hN n hn => hε (hN n hn)

namespace NNReal

/-!
### Topology on `ℝ≥0`
All the instances are inherited from the corresponding structures on the reals.

-/

/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Topology on `ℝ≥0`
All the instances are inherited from the corresponding structures on the reals.
-/
instance : TopologicalSpace ℝ≥0 := inferInstance
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSpace ℝ≥0 :=
  isClosed_Ici.completeSpace_coe

@[fun_prop]
/-
**NNReal.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：continuous_coe : Continuous ((↑) : Real>=0 -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuous_coe : Continuous ((↑) : ℝ≥0 → ℝ) :=
  continuous_subtype_val

/-- Embedding of `ℝ≥0` to `ℝ` as a bundled continuous map. -/
@[simps -fullyApplied]
/-
**NNReal._root_.ContinuousMap.coeNNRealReal** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of `ℝ≥0` to `ℝ` as a bundled continuous map.
-/
def _root_.ContinuousMap.coeNNRealReal : C(ℝ≥0, ℝ) :=
  ⟨(↑), continuous_coe⟩

@[simp]
/-
**NNReal.coeNNRealReal_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：coeNNRealReal_zero : ContinuousMap.coeNNRealReal 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeNNRealReal_zero : ContinuousMap.coeNNRealReal 0 = 0 := rfl
/-
**NNReal.ContinuousMap.canLift** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.ContinuousMap`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X],   CanLift C(X, ℝ) C(X, NNRea
l) ContinuousMap.coeNNRealReal.comp fun f => ∀ (x : X), 0 ≤ f x
参数：X, ℝ；X, NNReal；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
instance ContinuousMap.canLift {X : Type*} [TopologicalSpace X] :
    CanLift C(X, ℝ) C(X, ℝ≥0) ContinuousMap.coeNNRealReal.comp fun f => ∀ x, 0 ≤ f x where
  prf f hf := ⟨⟨fun x => .mk (f x) (hf x), f.2.subtype_mk _⟩, DFunLike.ext' rfl⟩

end NNReal

