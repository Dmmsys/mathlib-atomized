/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A Polish Borel space is measurably equivalent to a set of reals
-/

@[expose] public section

open Set Function PolishSpace PiNat TopologicalSpace Bornology Metric Filter Topology MeasureTheory

namespace MeasureTheory
variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α]

/-
**MeasureTheory.exists_nat_measurableEquiv_range_coe_fin_of_finite** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_nat_measurableEquiv_range_coe_fin_of_finite [Finite α] : exists n :
 Nat, Nonempty (α ≃ᵐ range ((↑) : Fin n -> Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `MeasurableSingletonClass.toDiscreteMeasurableSpace`：∀ {α : Type u_1} [in
st : MeasurableSpace α] [MeasurableSingletonClass α] [Countable α], DiscreteMeas
urableSpace α
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
-/
theorem exists_nat_measurableEquiv_range_coe_fin_of_finite [Finite α] :
    ∃ n : ℕ, Nonempty (α ≃ᵐ range ((↑) : Fin n → ℝ)) := by
  obtain ⟨n, ⟨n_equiv⟩⟩ := Finite.exists_equiv_fin α
  refine ⟨n, ⟨PolishSpace.Equiv.measurableEquiv (n_equiv.trans ?_)⟩⟩
  exact Equiv.ofInjective _ (Nat.cast_injective.comp Fin.val_injective)
/-
**MeasureTheory.measurableEquiv_range_coe_nat_of_infinite_of_countable** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measurableEquiv_range_coe_nat_of_infinite_of_countable [Infinite α] [Count
able α] : Nonempty (α ≃ᵐ range ((↑) : Nat -> Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.polishSpace`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Poli
shSpace α] {s : Set α}, IsClosed s → PolishSpace ↑s
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `Nat.isClosedEmbedding_coe_real`：isClosedEmbedding_coe_real : IsClosedEmb
edding ((↑) : Nat -> Real)
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem measurableEquiv_range_coe_nat_of_infinite_of_countable [Infinite α] [Countable α] :
    Nonempty (α ≃ᵐ range ((↑) : ℕ → ℝ)) := by
  have : PolishSpace (range ((↑) : ℕ → ℝ)) :=
    Nat.isClosedEmbedding_coe_real.isClosedMap.isClosed_range.polishSpace
  refine ⟨PolishSpace.Equiv.measurableEquiv ?_⟩
  refine (nonempty_equiv_of_countable.some : α ≃ ℕ).trans ?_
  exact Equiv.ofInjective ((↑) : ℕ → ℝ) Nat.cast_injective

/-- Any standard Borel space is measurably equivalent to a subset of the reals. -/
/-
**MeasureTheory.exists_subset_real_measurableEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：exists_subset_real_measurableEquiv : exists s : Set Real, MeasurableSet s 
∧ Nonempty (α ≃ᵐ s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `MeasureTheory.exists_nat_measurableEquiv_range_coe_fin_of_finite`：exists
_nat_measurableEquiv_range_coe_fin_of_finite [Finite α] : exists n : Nat, Nonemp
ty (α ≃ᵐ range ((↑) : Fin n -> Real))
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Nat.isClosedEmbedding_coe_real`：isClosedEmbedding_coe_real : IsClosedEmb
edding ((↑) : Nat -> Real)
· 使用定理 `MeasureTheory.measurableEquiv_range_coe_nat_of_infinite_of_countable`：me
asurableEquiv_range_coe_nat_of_infinite_of_countable [Infinite α] [Countable α] 
: Nonempty (α ≃ᵐ range ((↑) : Nat -> Real))
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.countable_coe_iff`：countable_coe_iff {s : Set α} : Countable s ↔ s.C
ountable
· 使用定理 `Cardinal.not_countable_real`：not_countable_real : ¬(Set.univ : Set Real)
.Countable

--- 原说明 ---
Any standard Borel space is measurably equivalent to a subset of the reals.
-/
theorem exists_subset_real_measurableEquiv : ∃ s : Set ℝ, MeasurableSet s ∧ Nonempty (α ≃ᵐ s) := by
  by_cases hα : Countable α
  · cases finite_or_infinite α
    · obtain ⟨n, h_nonempty_equiv⟩ := exists_nat_measurableEquiv_range_coe_fin_of_finite α
      refine ⟨_, ?_, h_nonempty_equiv⟩
      exact (Set.finite_range ((↑) : Fin n → ℝ)).measurableSet
    · refine ⟨_, ?_, measurableEquiv_range_coe_nat_of_infinite_of_countable α⟩
      exact Nat.isClosedEmbedding_coe_real.isClosed_range.measurableSet
  · refine
      ⟨univ, MeasurableSet.univ,
        ⟨(PolishSpace.measurableEquivOfNotCountable hα ?_ : α ≃ᵐ (univ : Set ℝ))⟩⟩
    rw [countable_coe_iff]
    exact Cardinal.not_countable_real

/-- Any standard Borel space embeds measurably into the reals. -/
/-
**MeasureTheory.exists_measurableEmbedding_real** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：exists_measurableEmbedding_real : exists f : α -> Real, MeasurableEmbeddin
g f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_subset_real_measurableEquiv`：exists_subset_real_mea
surableEquiv : exists s : Set Real, MeasurableSet s ∧ Nonempty (α ≃ᵐ s)
· 使用定理 `MeasurableEmbedding.comp`：comp (hg : MeasurableEmbedding g) (hf : Measur
ableEmbedding f) : MeasurableEmbedding (g ∘ f)
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e

--- 原说明 ---
Any standard Borel space embeds measurably into the reals.
-/
theorem exists_measurableEmbedding_real : ∃ f : α → ℝ, MeasurableEmbedding f := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_subset_real_measurableEquiv α
  exact ⟨(↑) ∘ e, (MeasurableEmbedding.subtype_coe hs).comp e.measurableEmbedding⟩

/-- A measurable embedding of a standard Borel space into `ℝ`. -/
noncomputable
/-
**MeasureTheory.embeddingReal** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : Ω -
> Real
参数：Ω : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_measurableEmbedding_real`：exists_measurableEmbeddin
g_real : exists f : α -> Real, MeasurableEmbedding f
-/
def embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : Ω → ℝ :=
  (exists_measurableEmbedding_real Ω).choose
/-
**MeasureTheory.measurableEmbedding_embeddingReal** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：measurableEmbedding_embeddingReal (Ω : Type*) [MeasurableSpace Ω] [Standar
dBorelSpace Ω] : MeasurableEmbedding (embeddingReal Ω)
参数：Ω : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `MeasureTheory.exists_measurableEmbedding_real`：exists_measurableEmbeddin
g_real : exists f : α -> Real, MeasurableEmbedding f
-/
lemma measurableEmbedding_embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] :
    MeasurableEmbedding (embeddingReal Ω) :=
  (exists_measurableEmbedding_real Ω).choose_spec

@[fun_prop]
/-
**MeasureTheory.measurable_embeddingReal** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measurable_embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpa
ce Ω] : Measurable (embeddingReal Ω)
参数：Ω : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
-/
lemma measurable_embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] :
    Measurable (embeddingReal Ω) :=
  (measurableEmbedding_embeddingReal Ω).measurable

end MeasureTheory

