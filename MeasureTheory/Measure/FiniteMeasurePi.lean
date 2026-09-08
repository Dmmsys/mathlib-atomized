/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Products of finite measures and probability measures

This file introduces finite products of finite measures and probability measures. The constructions
are obtained from special cases of products of general measures. Taking products nevertheless has
specific properties in the cases of finite measures and probability measures, notably the fact that
the product measures depend continuously on their factors in the topology of weak convergence when
the underlying space is metrizable and separable.

## Main definitions

* `MeasureTheory.FiniteMeasure.pi`: The product of finitely many finite measures.
* `MeasureTheory.ProbabilityMeasure.pi`: The product of finitely many probability measures.

## Main results

`MeasureTheory.ProbabilityMeasure.continuous_pi`: the product probability measure depends
continuously on the factors.

-/

@[expose] public section

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]

namespace FiniteMeasure

/-- The product of finitely many finite measures. -/
/-
**MeasureTheory.FiniteMeasure.pi** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Finite
Measure`。
形式化陈述：pi (μ : Π i, FiniteMeasure (α i)) : FiniteMeasure (Π i, α i)
参数：μ : Π i, FiniteMeasure (α i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of finitely many finite measures.
-/
noncomputable def pi (μ : Π i, FiniteMeasure (α i)) : FiniteMeasure (Π i, α i) :=
  ⟨Measure.pi (fun i ↦ μ i), inferInstance⟩

variable (μ : Π i, FiniteMeasure (α i))
/-
**MeasureTheory.FiniteMeasure.toMeasure_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.FiniteMeasure`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.FiniteMeasure (α i)),   ↑
(MeasureTheory.FiniteMeasure.pi μ) = MeasureTheory.Measure.pi fun i => ↑(μ i)
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.FiniteMeasure (α i)；MeasureTheory.Finit
eMeasure.pi μ；μ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMeasure_pi : (FiniteMeasure.pi μ).toMeasure = Measure.pi (fun i ↦ μ i) := rfl
/-
**MeasureTheory.FiniteMeasure.pi_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fin
iteMeasure`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.FiniteMeasure (α i)) (s :
 (i : ι) → Set (α i)),   (MeasureTheory.FiniteMeasure.pi μ) (Set.univ.pi s) = ∏ 
i, (μ i) (s i)
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.FiniteMeasure (α i)；s : (i : ι) → Set (
α i)；MeasureTheory.FiniteMeasure.pi μ；Set.univ.pi s；μ i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ENNReal.toNNReal_prod`：toNNReal_prod (s : Finset ι) (f : ι -> Real>=0∞) 
: (∏ i in s, f i).toNNReal = ∏ i in s, (f i).toNNReal
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma pi_pi (s : Π i, Set (α i)) :
    (FiniteMeasure.pi μ) (Set.pi univ s) = ∏ i, μ i (s i) := by
  simp [coeFn_def]
/-
**MeasureTheory.FiniteMeasure.mass_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.F
initeMeasure`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.FiniteMeasure (α i)), (Me
asureTheory.FiniteMeasure.pi μ).mass = ∏ i, (μ i).mass
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.FiniteMeasure (α i)；MeasureTheory.Finit
eMeasure.pi μ；μ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `MeasureTheory.FiniteMeasure.pi_pi`：∀ {ι : Type u_1} {α : ι → Type u_2} [
inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Me
asureTheory.FiniteMeasu…
-/
@[simp] lemma mass_pi : (FiniteMeasure.pi μ).mass = ∏ i, (μ i).mass := by
  simp only [mass]
  rw [← pi_univ (univ : Set ι), pi_pi]
/-
**MeasureTheory.FiniteMeasure.pi_map_pi** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.FiniteMeasure`。
形式化陈述：pi_map_pi {β : ι -> Type*} [forall i, MeasurableSpace (β i)] {f : Π i, α i
 -> β i} (f_mble : forall i, AEMeasurable (f i) (μ i)) : (FiniteMeasure.pi μ).ma
p (fun x i => (f i (x i))) = FiniteMeasure.pi (fun i => (μ i).map (f i))
参数：β i；f_mble : forall i, AEMeasurable (f i) (μ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.pi_map_pi`：pi_map_pi {X Y : ι -> Type*} {mX : fora
ll i, MeasurableSpace (X i)} {μ : (i : ι) -> Measure (X i)} [forall i, Measurabl
eSpace (Y i)] {f : (i…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
-/
lemma pi_map_pi {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {f : Π i, α i → β i}
    (f_mble : ∀ i, AEMeasurable (f i) (μ i)) :
    (FiniteMeasure.pi μ).map (fun x i ↦ (f i (x i))) =
      FiniteMeasure.pi (fun i ↦ (μ i).map (f i)) := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_map, toMeasure_pi]
  rw [Measure.pi_map_pi f_mble]

end FiniteMeasure

namespace ProbabilityMeasure

/-- The product of finitely many probability measures. -/
/-
**MeasureTheory.ProbabilityMeasure.pi** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.P
robabilityMeasure`。
形式化陈述：pi (μ : Π i, ProbabilityMeasure (α i)) : ProbabilityMeasure (Π i, α i)
参数：μ : Π i, ProbabilityMeasure (α i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of finitely many probability measures.
-/
noncomputable def pi (μ : Π i, ProbabilityMeasure (α i)) : ProbabilityMeasure (Π i, α i) :=
  ⟨Measure.pi (fun i ↦ μ i), inferInstance⟩

variable (μ : Π i, ProbabilityMeasure (α i))
/-
**MeasureTheory.ProbabilityMeasure.toMeasure_pi** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.ProbabilityMeasure`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.ProbabilityMeasure (α i))
,   ↑(MeasureTheory.ProbabilityMeasure.pi μ) = MeasureTheory.Measure.pi fun i =>
 ↑(μ i)
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.ProbabilityMeasure (α i)；MeasureTheory.
ProbabilityMeasure.pi μ；μ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMeasure_pi :
    (ProbabilityMeasure.pi μ).toMeasure = Measure.pi (fun i ↦ μ i) := rfl
/-
**MeasureTheory.ProbabilityMeasure.pi_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.ProbabilityMeasure`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.ProbabilityMeasure (α i))
 (s : (i : ι) → Set (α i)),   (MeasureTheory.ProbabilityMeasure.pi μ) (Set.univ.
pi s) = ∏ i, (μ i) (s i)
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.ProbabilityMeasure (α i)；s : (i : ι) → 
Set (α i)；MeasureTheory.ProbabilityMeasure.pi μ；Set.univ.pi s；μ i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `ENNReal.toNNReal_prod`：toNNReal_prod (s : Finset ι) (f : ι -> Real>=0∞) 
: (∏ i in s, f i).toNNReal = ∏ i in s, (f i).toNNReal
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma pi_pi (s : Π i, Set (α i)) :
    ProbabilityMeasure.pi μ (Set.pi univ s) = ∏ i, μ i (s i) := by
  simp [coeFn_def]

open TopologicalSpace

/-- The map associating to finitely many probability measures their product is a continuous map. -/
@[fun_prop]
/-
**MeasureTheory.ProbabilityMeasure.continuous_pi** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.ProbabilityMeasure`。
形式化陈述：continuous_pi [forall i, TopologicalSpace (α i)] [forall i, SecondCountabl
eTopology (α i)] [forall i, PseudoMetrizableSpace (α i)] [forall i, OpensMeasura
bleSpace (α i)] : Continuous (fun (μ : Π i, ProbabilityMeasure (α i)) => Probabi
lityMeasure.pi μ)
参数：α i；α i；α i；α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_inter_distrib`：pi_inter_distrib : (s.pi fun i => t i inter t₁ i) 
= s.pi t inter s.pi t₁
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `null_frontier_inter`：null_frontier_inter {μ : Measure α'} {s s' : Set α'
} (h : μ (frontier s) = 0) (h' : μ (frontier s') = 0) : μ (frontier (s inter s')
) = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`：∀ {Ω : Type u_1
} {ι : Type u_2} [inst : MeasurableSpace Ω] [inst_1 : TopologicalSpace Ω] [Secon
dCountableTopology Ω]   [inst_3 : OpensMeasur…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.instFirstCountableTopologyForallOfCountable`：∀ {ι : Typ
e u_1} {X : ι → Type u_2} [Countable ι] [inst : (i : ι) → TopologicalSpace (X i)
]   [∀ (i : ι), FirstCountableTopology (X i)], Fir…
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `MeasureTheory.instPseudoMetrizableSpaceProbabilityMeasureOfSeparableSpac
e`：∀ (X : Type u_2) [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizab
leSpace X]   [TopologicalSpace.SeparableSpace X] [inst_3 : Meas…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `MeasureTheory.exists_null_frontier_thickening`：exists_null_frontier_thic
kening (μ : Measure Ω) [SFinite μ] (s : Set Ω) {a b : Real} (hab : a < b) : exis
ts r in Ioo a b, μ (frontier (Metri…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_singleton`：thickening_singleton (δ : Real) (x : X) : t
hickening δ ({x} : Set X) = ball x δ
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
The map associating to finitely many probability measures their product is a con
tinuous map.
-/
theorem continuous_pi [∀ i, TopologicalSpace (α i)] [∀ i, SecondCountableTopology (α i)]
    [∀ i, PseudoMetrizableSpace (α i)] [∀ i, OpensMeasurableSpace (α i)] :
    Continuous (fun (μ : Π i, ProbabilityMeasure (α i)) ↦ ProbabilityMeasure.pi μ) := by
  refine continuous_iff_continuousAt.2 (fun μ ↦ ?_)
  /- It suffices to check the convergence along elements of a π-system containing arbitrarily
  small neighborhoods of any point, by `tendsto_probabilityMeasure_of_tendsto_of_mem`.
  We take as a π-system the sets of the form `s₁ × ... × sₙ` where all the `sᵢ` have
  null frontier. -/
  let S : Set (Set (Π i, α i)) := {t | ∃ (s : Π i, Set (α i)), t = univ.pi s ∧
    (∀ i, MeasurableSet (s i)) ∧ (∀ i, μ i (frontier (s i)) = 0)}
  have : IsPiSystem S := by
    rintro - ⟨s, rfl, smeas, hs⟩ - ⟨s', rfl, s'meas, hs'⟩ -
    refine ⟨fun i ↦ s i ∩ s' i, pi_inter_distrib.symm, fun i ↦ (smeas i).inter (s'meas i),
      fun i ↦ ?_⟩
    simp_rw [null_iff_toMeasure_null] at hs hs' ⊢
    exact null_frontier_inter (hs i) (hs' i)
  apply this.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro - ⟨s, rfl, smeas, hs⟩
    exact MeasurableSet.univ_pi smeas
  · let : ∀ i, PseudoMetricSpace (α i) :=
      fun i ↦ TopologicalSpace.pseudoMetrizableSpacePseudoMetric (α i)
    intro u u_open x xu
    obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ball x ε ⊆ u := Metric.isOpen_iff.1 u_open x xu
    have A (i) : ∃ r ∈ Ioo 0 ε, (μ i : Measure (α i)) (frontier (Metric.thickening r {x i})) = 0 :=
      exists_null_frontier_thickening _ _ εpos
    choose! r rpos hr using A
    refine ⟨univ.pi (fun i ↦ ball (x i) (r i)), ⟨fun i ↦ ball (x i) (r i), rfl,
      fun i ↦ measurableSet_ball, fun i ↦ by simpa using hr i⟩, ?_, ?_⟩
    · apply IsOpen.mem_nhds
      · exact isOpen_set_pi finite_univ (by simp)
      · simpa using fun i ↦ (rpos i).1
    · calc univ.pi fun i ↦ ball (x i) (r i)
      _ ⊆ univ.pi fun i ↦ ball (x i) ε := by gcongr with i hi; exact (rpos i).2.le
      _ ⊆ u := by rwa [← ball_pi _ εpos]
  · rintro - ⟨s, rfl, smeas, hs⟩
    simp only [pi_pi]
    apply tendsto_finsetProd _ (fun i hi ↦ ?_)
    exact tendsto_measure_of_null_frontier_of_tendsto (Tendsto.apply_nhds (fun ⦃U⦄ a ↦ a) i) (hs i)

end ProbabilityMeasure

end MeasureTheory

