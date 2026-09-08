/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Topology on the quotient group

In this file we define topology on `G ⧸ N`, where `N` is a subgroup of `G`,
and prove basic properties of this topology.
-/

public section

assert_not_exists Cardinal

open Topology
open scoped Pointwise

variable {G : Type*} [TopologicalSpace G] [Group G]

namespace QuotientGroup

@[to_additive]
/-
**QuotientGroup.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：instTopologicalSpace (N : Subgroup G) : TopologicalSpace (G ⧸ N)
参数：N : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace (N : Subgroup G) : TopologicalSpace (G ⧸ N) :=
  instTopologicalSpaceQuotient

@[to_additive]
/-
**QuotientGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace G] (N : Subgroup G) : CompactSpace (G ⧸ N) :=
  Quotient.compactSpace

@[to_additive]
/-
**QuotientGroup.isQuotientMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：isQuotientMap_mk (N : Subgroup G) : IsQuotientMap (mk : G -> G ⧸ N)
参数：N : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isQuotientMap_quot_mk`：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X
 r)
-/
theorem isQuotientMap_mk (N : Subgroup G) : IsQuotientMap (mk : G → G ⧸ N) :=
  isQuotientMap_quot_mk

@[to_additive (attr := continuity, fun_prop)]
/-
**QuotientGroup.continuous_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：continuous_mk {N : Subgroup G} : Continuous (mk : G -> G ⧸ N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
-/
theorem continuous_mk {N : Subgroup G} : Continuous (mk : G → G ⧸ N) :=
  continuous_quot_mk

section ContinuousMul

variable [SeparatelyContinuousMul G] {N : Subgroup G}

@[to_additive]
/-
**QuotientGroup.isOpenMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：isOpenMap_coe : IsOpenMap ((↑) : G -> G ⧸ N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpenMap_quotient_mk'_mul`：∀ {Γ : Type u_4} [inst : Group Γ] {T : Type 
u_5} [inst_1 : TopologicalSpace T] [inst_2 : MulAction Γ T]   [ContinuousConstSM
ul Γ T], IsOpenM…
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
-/
theorem isOpenMap_coe : IsOpenMap ((↑) : G → G ⧸ N) := isOpenMap_quotient_mk'_mul

@[to_additive]
/-
**QuotientGroup.isOpenQuotientMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：isOpenQuotientMap_mk : IsOpenQuotientMap (mk : G -> G ⧸ N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isOpenQuotientMap_quotientMk`：MulAction.isOpenQuotientMap_quot
ientMk [ContinuousConstSMul Γ T] : IsOpenQuotientMap (Quotient.mk (MulAction.orb
itRel Γ T))
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
-/
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk : G → G ⧸ N) :=
  MulAction.isOpenQuotientMap_quotientMk

@[to_additive (attr := simp)]
/-
**QuotientGroup.dense_preimage_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：dense_preimage_mk {s : Set (G ⧸ N)} : Dense ((↑) ⁻¹' s : Set G) ↔ Dense s
参数：G ⧸ N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.dense_preimage_iff`：dense_preimage_iff (h : IsOpenQuot
ientMap f) {s : Set Y} : Dense (f ⁻¹' s) ↔ Dense s
· 使用定理 `QuotientGroup.isOpenQuotientMap_mk`：isOpenQuotientMap_mk : IsOpenQuotien
tMap (mk : G -> G ⧸ N)
-/
theorem dense_preimage_mk {s : Set (G ⧸ N)} : Dense ((↑) ⁻¹' s : Set G) ↔ Dense s :=
  isOpenQuotientMap_mk.dense_preimage_iff

@[to_additive]
/-
**QuotientGroup.dense_image_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：dense_image_mk {s : Set G} : Dense (mk '' s : Set (G ⧸ N)) ↔ Dense (s * (N
 : Set G))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.dense_preimage_mk`：dense_preimage_mk {s : Set (G ⧸ N)} : D
ense ((↑) ⁻¹' s : Set G) ↔ Dense s
· 使用定理 `QuotientGroup.preimage_image_mk_eq_mul`：preimage_image_mk_eq_mul (N : Su
bgroup α) (s : Set α) : mk ⁻¹' ((mk : α -> α ⧸ N) '' s) = s * N
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dense_image_mk {s : Set G} :
    Dense (mk '' s : Set (G ⧸ N)) ↔ Dense (s * (N : Set G)) := by
  rw [← dense_preimage_mk, preimage_image_mk_eq_mul]

@[to_additive]
/-
**QuotientGroup.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：instContinuousSMul {G : Type*} [Group G] [TopologicalSpace G] [ContinuousM
ul G] {N : Subgroup G} : ContinuousSMul G (G ⧸ N) where continuous_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenQuotientMap.continuous_comp_iff`：continuous_comp_iff (h : IsOpenQu
otientMap f) {g : Y -> Z} : Continuous (g ∘ f) ↔ Continuous g
· 使用定理 `IsOpenQuotientMap.prodMap`：IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z
 -> W} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap
 (Prod.map f g)
· 使用定理 `IsOpenQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOp
enQuotientMap id
· 使用定理 `QuotientGroup.isOpenQuotientMap_mk`：isOpenQuotientMap_mk : IsOpenQuotien
tMap (mk : G -> G ⧸ N)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `QuotientGroup.continuous_mk`：continuous_mk {N : Subgroup G} : Continuous
 (mk : G -> G ⧸ N)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
-/
instance instContinuousSMul {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    {N : Subgroup G} : ContinuousSMul G (G ⧸ N) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul

@[to_additive]
/-
**QuotientGroup.instContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup
`。
形式化陈述：instContinuousConstSMul : ContinuousConstSMul G (G ⧸ N) where continuous_c
onst_smul γ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenQuotientMap.continuous_comp_iff`：continuous_comp_iff (h : IsOpenQu
otientMap f) {g : Y -> Z} : Continuous (g ∘ f) ↔ Continuous g
· 使用定理 `QuotientGroup.isOpenQuotientMap_mk`：isOpenQuotientMap_mk : IsOpenQuotien
tMap (mk : G -> G ⧸ N)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `QuotientGroup.continuous_mk`：continuous_mk {N : Subgroup G} : Continuous
 (mk : G -> G ⧸ N)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
instance instContinuousConstSMul : ContinuousConstSMul G (G ⧸ N) where
  continuous_const_smul γ := by
    rw [← isOpenQuotientMap_mk.continuous_comp_iff]
    exact continuous_mk.comp <| continuous_const_smul γ

@[to_additive]
/-
**QuotientGroup.t1Space_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：t1Space_iff : T1Space (G ⧸ N) ↔ IsClosed (N : Set G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.preimage_mk_one`：preimage_mk_one (N : Subgroup α) : mk ⁻¹'
 {(mk : α -> α ⧸ N) 1} = N
· 使用引理 `MulAction.IsPretransitive.t1Space_iff`：t1Space_iff (x : α) [IsPretransit
ive G α] : T1Space α ↔ IsClosed {x}
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `isClosed_coinduced`：isClosed_coinduced {t : TopologicalSpace α} {s : Set
 β} {f : α -> β} : IsClosed[t.coinduced f] s ↔ IsClosed (f ⁻¹' s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem t1Space_iff :
    T1Space (G ⧸ N) ↔ IsClosed (N : Set G) := by
  rw [← QuotientGroup.preimage_mk_one, MulAction.IsPretransitive.t1Space_iff G (mk 1),
      isClosed_coinduced]
  rfl

@[to_additive]
/-
**QuotientGroup.discreteTopology_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：discreteTopology_iff : DiscreteTopology (G ⧸ N) ↔ IsOpen (N : Set G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.preimage_mk_one`：preimage_mk_one (N : Subgroup α) : mk ⁻¹'
 {(mk : α -> α ⧸ N) 1} = N
· 使用引理 `MulAction.IsPretransitive.discreteTopology_iff`：discreteTopology_iff (x 
: α) [IsPretransitive G α] : DiscreteTopology α ↔ IsOpen {x}
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `isOpen_coinduced`：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} 
{f : α -> β} : IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem discreteTopology_iff :
    DiscreteTopology (G ⧸ N) ↔ IsOpen (N : Set G) := by
  rw [← QuotientGroup.preimage_mk_one, MulAction.IsPretransitive.discreteTopology_iff G (mk 1),
      isOpen_coinduced]
  rfl

/-- The quotient of a topological group `G` by a closed subgroup `N` is T1.

When `G` is normal, this implies (because `G ⧸ N` is a topological group) that the quotient is T3
(see `QuotientGroup.instT3Space`).

Back to the general case, we will show later that the quotient is in fact T2
since `N` acts on `G` properly. -/
@[to_additive
/-- The quotient of a topological additive group `G` by a closed subgroup `N` is T1.

When `G` is normal, this implies (because `G ⧸ N` is a topological additive group) that the
quotient is T3 (see `QuotientAddGroup.instT3Space`).

Back to the general case, we will show later that the quotient is in fact T2
since `N` acts on `G` properly. -/]
/-
**QuotientGroup.instT1Space** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：instT1Space [hN : IsClosed (N : Set G)] : T1Space (G ⧸ N)
参数：N : Set G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientGroup.t1Space_iff`：t1Space_iff : T1Space (G ⧸ N) ↔ IsClosed (N :
 Set G)
-/
instance instT1Space [hN : IsClosed (N : Set G)] :
    T1Space (G ⧸ N) :=
  t1Space_iff.mpr hN

-- TODO: `IsOpen` should be a class and this should be an instance
@[to_additive]
/-
**QuotientGroup.discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：discreteTopology (hN : IsOpen (N : Set G)) : DiscreteTopology (G ⧸ N)
参数：hN : IsOpen (N : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientGroup.discreteTopology_iff`：discreteTopology_iff : DiscreteTopol
ogy (G ⧸ N) ↔ IsOpen (N : Set G)
-/
theorem discreteTopology (hN : IsOpen (N : Set G)) :
    DiscreteTopology (G ⧸ N) :=
  discreteTopology_iff.mpr hN

/-- A quotient of a locally compact group is locally compact. -/
@[to_additive]
/-
**QuotientGroup.instLocallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup
`。
形式化陈述：instLocallyCompactSpace [LocallyCompactSpace G] (N : Subgroup G) : Locally
CompactSpace (G ⧸ N)
参数：N : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.locallyCompactSpace`：IsOpenQuotientMap.locallyCompactS
pace [LocallyCompactSpace X] {f : X -> Y} (hf : IsOpenQuotientMap f) : LocallyCo
mpactSpace Y where local_co…
· 使用定理 `QuotientGroup.isOpenQuotientMap_mk`：isOpenQuotientMap_mk : IsOpenQuotien
tMap (mk : G -> G ⧸ N)

--- 原说明 ---
A quotient of a locally compact group is locally compact.
-/
instance instLocallyCompactSpace [LocallyCompactSpace G] (N : Subgroup G) :
    LocallyCompactSpace (G ⧸ N) :=
  QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace

variable (N)

/-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/
@[to_additive
  /-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/]
/-
**QuotientGroup.nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = Filter.map (↑) (𝓝 x)
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenQuotientMap.map_nhds_eq`：map_nhds_eq (h : IsOpenQuotientMap f) (x 
: X) : map f (𝓝 x) = 𝓝 (f x)
· 使用定理 `QuotientGroup.isOpenQuotientMap_mk`：isOpenQuotientMap_mk : IsOpenQuotien
tMap (mk : G -> G ⧸ N)
-/
theorem nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = Filter.map (↑) (𝓝 x) :=
  (isOpenQuotientMap_mk.map_nhds_eq _).symm

@[to_additive]
/-
**QuotientGroup.instFirstCountableTopology** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGr
oup`。
形式化陈述：instFirstCountableTopology [FirstCountableTopology G] : FirstCountableTopo
logy (G ⧸ N) where nhds_generated_countable
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
· 使用定理 `Filter.map.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : Fi
lter α) [l.IsCountablyGenerated] (f : α → β),   (Filter.map f l).IsCountablyGene
rated
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.nhds_eq`：nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = Filter.map (↑) 
(𝓝 x)
-/
instance instFirstCountableTopology [FirstCountableTopology G] :
    FirstCountableTopology (G ⧸ N) where
  nhds_generated_countable := mk_surjective.forall.2 fun x ↦ nhds_eq N x ▸ inferInstance

/-- The quotient of a second countable topological group by a subgroup is second countable. -/
@[to_additive
  /-- The quotient of a second countable additive topological group by a subgroup is second
  countable. -/]
/-
**QuotientGroup.instSecondCountableTopology** 是 Mathlib 中的一个实例，位于命名空间 `QuotientG
roup`。
形式化陈述：instSecondCountableTopology [SecondCountableTopology G] : SecondCountableT
opology (G ⧸ N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousConstSMul.secondCountableTopology`：ContinuousConstSMul.secondC
ountableTopology [SecondCountableTopology T] [ContinuousConstSMul Γ T] : SecondC
ountableTopology (Quotient (MulAc…
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
-/
instance instSecondCountableTopology [SecondCountableTopology G] :
    SecondCountableTopology (G ⧸ N) :=
  ContinuousConstSMul.secondCountableTopology

end ContinuousMul

variable [IsTopologicalGroup G] (N : Subgroup G)

@[to_additive]
/-
**QuotientGroup.instIsTopologicalGroup** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`
。
形式化陈述：instIsTopologicalGroup [N.Normal] : IsTopologicalGroup (G ⧸ N) where conti
nuous_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenQuotientMap.continuous_comp_iff`：continuous_comp_iff (h : IsOpenQu
otientMap f) {g : Y -> Z} : Continuous (g ∘ f) ↔ Continuous g
· 使用定理 `IsOpenQuotientMap.prodMap`：IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z
 -> W} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap
 (Prod.map f g)
· 使用定理 `QuotientGroup.isOpenQuotientMap_mk`：isOpenQuotientMap_mk : IsOpenQuotien
tMap (mk : G -> G ⧸ N)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `QuotientGroup.continuous_mk`：continuous_mk {N : Subgroup G} : Continuous
 (mk : G -> G ⧸ N)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `Continuous.quotient_map'`：Continuous.quotient_map' {t : Setoid Y} {f : X
 -> Y} (hf : Continuous f) (H : (s.r ⇒ t.r) f f) : Continuous (Quotient.map' f H
)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
instance instIsTopologicalGroup [N.Normal] : IsTopologicalGroup (G ⧸ N) where
  continuous_mul := by
    rw [← (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul
  continuous_inv := continuous_inv.quotient_map' _

@[to_additive]
/-
**QuotientGroup.isClosedMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：isClosedMap_coe {H : Subgroup G} (hH : IsCompact (H : Set G)) : IsClosedMa
p ((↑) : G -> G ⧸ H)
参数：hH : IsCompact (H : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isClosed_preimage`：∀ {X : Type u_1} {Y : Type u_2}
 {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolo
gy.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `QuotientGroup.isQuotientMap_mk`：isQuotientMap_mk (N : Subgroup G) : IsQu
otientMap (mk : G -> G ⧸ N)
· 使用定理 `QuotientGroup.preimage_image_mk_eq_mul`：preimage_image_mk_eq_mul (N : Su
bgroup α) (s : Set α) : mk ⁻¹' ((mk : α -> α ⧸ N) '' s) = s * N
· 使用定理 `IsClosed.mul_right_of_isCompact`：IsClosed.mul_right_of_isCompact (ht : I
sClosed t) (hs : IsCompact s) : IsClosed (t * s)
-/
theorem isClosedMap_coe {H : Subgroup G} (hH : IsCompact (H : Set G)) :
    IsClosedMap ((↑) : G → G ⧸ H) := by
  intro t ht
  rw [← (isQuotientMap_mk H).isClosed_preimage, preimage_image_mk_eq_mul]
  exact ht.mul_right_of_isCompact hH

@[to_additive]
/-
**QuotientGroup.instT3Space** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：instT3Space [N.Normal] [hN : IsClosed (N : Set G)] : T3Space (G ⧸ N)
参数：N : Set G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
-/
instance instT3Space [N.Normal] [hN : IsClosed (N : Set G)] : T3Space (G ⧸ N) := by
  infer_instance

end QuotientGroup

