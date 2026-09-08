/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.Bornology.BoundedOperation
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Bounded continuous functions

The type of bounded continuous functions taking values in a metric space, with the uniform distance.
-/

@[expose] public section

assert_not_exists CStarRing

noncomputable section

open Topology Bornology NNReal UniformConvergence

open Set Filter Metric Function

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}

/-- `α →ᵇ β` is the type of bounded continuous functions `α → β` from a topological space to a
metric space.

When possible, instead of parametrizing results over `(f : α →ᵇ β)`,
you should parametrize over `(F : Type*) [BoundedContinuousMapClass F α β] (f : F)`.

When you extend this structure, make sure to extend `BoundedContinuousMapClass`. -/
/-
**BoundedContinuousFunction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → (β : Type v) → [TopologicalSpace α] → [PseudoMetricSpace β]
 → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α →ᵇ β` is the type of bounded continuous functions `α → β` from a topological 
space to a
metric space.

When possible, instead of parametrizing results over `(f : α →ᵇ β)`,
you should parametrize over `(F : Type*) [BoundedContinuousMapClass F α β] (f : 
F)`.

When you extend this structure, make sure to extend `BoundedContinuousMapClass`.
-/
structure BoundedContinuousFunction (α : Type u) (β : Type v) [TopologicalSpace α]
    [PseudoMetricSpace β] : Type max u v extends ContinuousMap α β where
  map_bounded' : ∃ C, ∀ x y, dist (toFun x) (toFun y) ≤ C

@[inherit_doc] scoped[BoundedContinuousFunction] infixr:25 " →ᵇ " => BoundedContinuousFunction

section

/-- `BoundedContinuousMapClass F α β` states that `F` is a type of bounded continuous maps.

You should also extend this typeclass when you extend `BoundedContinuousFunction`. -/
/-
**BoundedContinuousMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_2) →   (α : outParam (Type u_3)) →     (β : outParam (Type u_4
)) → [TopologicalSpace α] → [PseudoMetricSpace β] → [FunLike F α β] → Prop
参数：Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BoundedContinuousMapClass F α β` states that `F` is a type of bounded continuou
s maps.

You should also extend this typeclass when you extend `BoundedContinuousFunction
`.
-/
class BoundedContinuousMapClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
    [PseudoMetricSpace β] [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  map_bounded (f : F) : ∃ C, ∀ x y, dist (f x) (f y) ≤ C

end

export BoundedContinuousMapClass (map_bounded)

namespace BoundedContinuousFunction

section Basics

variable [TopologicalSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {f g : α →ᵇ β} {x : α} {C : ℝ}

/-
**BoundedContinuousFunction.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：instFunLike : FunLike (α ->ᵇ β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (α →ᵇ β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
/-
**BoundedContinuousFunction.instBoundedContinuousMapClass** 是 Mathlib 中的一个实例，位于命
名空间 `BoundedContinuousFunction`。
形式化陈述：instBoundedContinuousMapClass : BoundedContinuousMapClass (α ->ᵇ β) α β wh
ere map_continuous f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `BoundedContinuousFunction.map_bounded'`：∀ {α : Type u} {β : Type v} [ins
t : TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (self : BoundedContinuo
usFunction α β), ∃ C, ∀ (x y…
-/
instance instBoundedContinuousMapClass : BoundedContinuousMapClass (α →ᵇ β) α β where
  map_continuous f := f.continuous_toFun
  map_bounded f := f.map_bounded'
/-
**BoundedContinuousFunction.instCoeTC** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：instCoeTC [FunLike F α β] [BoundedContinuousMapClass F α β] : CoeTC F (α -
>ᵇ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousMapClass.map_bounded`：∀ {F : Type u_2} {α : outParam (T
ype u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst_1 : Pseu
doMetricSpace β} {inst_2 : …
-/
instance instCoeTC [FunLike F α β] [BoundedContinuousMapClass F α β] : CoeTC F (α →ᵇ β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      map_bounded' := map_bounded f }⟩

@[simp]
/-
**BoundedContinuousFunction.coe_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：coe_toContinuousMap (f : α ->ᵇ β) : (f.toContinuousMap : α -> β) = f
参数：f : α ->ᵇ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMap (f : α →ᵇ β) : (f.toContinuousMap : α → β) = f := rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**BoundedContinuousFunction.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContin
uousFunction.Simps`。
形式化陈述：{α : Type u} →   {β : Type v} → [inst : TopologicalSpace α] → [inst_1 : Ps
eudoMetricSpace β] → BoundedContinuousFunction α β → α → β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (h : α →ᵇ β) : α → β := h

initialize_simps_projections BoundedContinuousFunction (toFun → apply)
/-
**BoundedContinuousFunction.bounded** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : PseudoMe
tricSpace β]   (f : BoundedContinuousFunction α β), ∃ C, ∀ (x y : α), dist (f x)
 (f y) ≤ C
参数：f : BoundedContinuousFunction α β；x y : α；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.map_bounded'`：∀ {α : Type u} {β : Type v} [ins
t : TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (self : BoundedContinuo
usFunction α β), ∃ C, ∀ (x y…
-/
protected theorem bounded (f : α →ᵇ β) : ∃ C, ∀ x y : α, dist (f x) (f y) ≤ C :=
  f.map_bounded'
/-
**BoundedContinuousFunction.continuous** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : PseudoMe
tricSpace β]   (f : BoundedContinuousFunction α β), Continuous ⇑f
参数：f : BoundedContinuousFunction α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
protected theorem continuous (f : α →ᵇ β) : Continuous f :=
  f.toContinuousMap.continuous

@[ext]
/-
**BoundedContinuousFunction.ext** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuousFunc
tion`。
形式化陈述：ext (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
/-
**BoundedContinuousFunction.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuousF
unction`。
形式化陈述：coe_mk (f : α -> β) (h : _) (h' : _) : BoundedContinuousFunction.mk ⟨f, h⟩
 h' = f
参数：f : α -> β；h : _；h' : _。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : α → β) (h : _) (h' : _) :
    BoundedContinuousFunction.mk ⟨f, h⟩ h' = f :=
  rfl
/-
**BoundedContinuousFunction.isBounded_range** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：isBounded_range (f : α ->ᵇ β) : IsBounded (range f)
参数：f : α ->ᵇ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_range_iff`：isBounded_range_iff {f : β -> α} : IsBounded
 (range f) ↔ exists C, forall x y, dist (f x) (f y) <= C
· 使用定理 `BoundedContinuousFunction.bounded`：∀ {α : Type u} {β : Type v} [inst : T
opologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFuncti
on α β), ∃ C, ∀ (x y : …
-/
theorem isBounded_range (f : α →ᵇ β) : IsBounded (range f) :=
  isBounded_range_iff.2 f.bounded
/-
**BoundedContinuousFunction.isBounded_image** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：isBounded_image (f : α ->ᵇ β) (s : Set α) : IsBounded (f '' s)
参数：f : α ->ᵇ β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `BoundedContinuousFunction.isBounded_range`：isBounded_range (f : α ->ᵇ β)
 : IsBounded (range f)
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem isBounded_image (f : α →ᵇ β) (s : Set α) : IsBounded (f '' s) :=
  f.isBounded_range.subset <| image_subset_range _ _
/-
**BoundedContinuousFunction.eq_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：eq_of_empty [h : IsEmpty α] (f g : α ->ᵇ β) : f = g
参数：f g : α ->ᵇ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
-/
theorem eq_of_empty [h : IsEmpty α] (f g : α →ᵇ β) : f = g :=
  ext <| h.elim

/-- A continuous function with an explicit bound is a bounded continuous function. -/
/-
**BoundedContinuousFunction.mkOfBound** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：mkOfBound (f : C(α, β)) (C : Real) (h : forall x y : α, dist (f x) (f y) <
= C) : α ->ᵇ β
参数：f : C(α, β)；C : Real；h : forall x y : α, dist (f x) (f y) <= C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function with an explicit bound is a bounded continuous function.
-/
def mkOfBound (f : C(α, β)) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) : α →ᵇ β :=
  ⟨f, ⟨C, h⟩⟩

@[simp]
/-
**BoundedContinuousFunction.mkOfBound_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：mkOfBound_coe {f} {C} {h} : (mkOfBound f C h : α -> β) = (f : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkOfBound_coe {f} {C} {h} : (mkOfBound f C h : α → β) = (f : α → β) := rfl

/-- A continuous function on a compact space is automatically a bounded continuous function. -/
/-
**BoundedContinuousFunction.mkOfCompact** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：mkOfCompact [CompactSpace α] (f : C(α, β)) : α ->ᵇ β
参数：f : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function on a compact space is automatically a bounded continuous f
unction.
-/
def mkOfCompact [CompactSpace α] (f : C(α, β)) : α →ᵇ β :=
  ⟨f, isBounded_range_iff.1 (isCompact_range f.continuous).isBounded⟩

@[simp]
/-
**BoundedContinuousFunction.mkOfCompact_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：mkOfCompact_apply [CompactSpace α] (f : C(α, β)) (a : α) : mkOfCompact f a
 = f a
参数：f : C(α, β)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkOfCompact_apply [CompactSpace α] (f : C(α, β)) (a : α) : mkOfCompact f a = f a := rfl

/-- If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functions. -/
@[simps]
/-
**BoundedContinuousFunction.mkOfDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：mkOfDiscrete [DiscreteTopology α] (f : α -> β) (C : Real) (h : forall x y 
: α, dist (f x) (f y) <= C) : α ->ᵇ β
参数：f : α -> β；C : Real；h : forall x y : α, dist (f x) (f y) <= C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functio
ns.
-/
def mkOfDiscrete [DiscreteTopology α] (f : α → β) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) :
    α →ᵇ β :=
  ⟨⟨f, continuous_of_discreteTopology⟩, ⟨C, h⟩⟩

/-- The uniform distance between two bounded continuous functions. -/
/-
**BoundedContinuousFunction.instDist** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：instDist : Dist (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform distance between two bounded continuous functions.
-/
instance instDist : Dist (α →ᵇ β) :=
  ⟨fun f g => sInf { C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C }⟩
/-
**BoundedContinuousFunction.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：dist_eq : dist f g = sInf { C | 0 <= C ∧ forall x : α, dist (f x) (g x) <=
 C }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq : dist f g = sInf { C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C } := rfl
/-
**BoundedContinuousFunction.dist_set_exists** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：dist_set_exists : exists C, 0 <= C ∧ forall x : α, dist (f x) (g x) <= C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `Bornology.IsBounded.union`：∀ {α : Type u_2} {x : Bornology α} {s t : Set
 α},   Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s ∪ 
t)
· 使用定理 `BoundedContinuousFunction.isBounded_range`：isBounded_range (f : α ->ᵇ β)
 : IsBounded (range f)
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem dist_set_exists : ∃ C, 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C := by
  rcases isBounded_iff.1 (f.isBounded_range.union g.isBounded_range) with ⟨C, hC⟩
  refine ⟨max 0 C, le_max_left _ _, fun x => (hC ?_ ?_).trans (le_max_right _ _)⟩
    <;> [left; right]
    <;> apply mem_range_self

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
/-
**BoundedContinuousFunction.dist_coe_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：dist_coe_le_dist (x : α) : dist (f x) (g x) <= dist f g
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `BoundedContinuousFunction.dist_set_exists`：dist_set_exists : exists C, 0
 <= C ∧ forall x : α, dist (f x) (g x) <= C
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The pointwise distance is controlled by the distance between functions, by defin
ition.
-/
theorem dist_coe_le_dist (x : α) : dist (f x) (g x) ≤ dist f g :=
  le_csInf dist_set_exists fun _ hb => hb.2 x

/- This lemma will be needed in the proof of the metric space instance, but it will become
useless afterwards as it will be superseded by the general result that the distance is nonnegative
in metric spaces. -/

set_option backward.privateInPublic true in
/-
**BoundedContinuousFunction.dist_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `BoundedConti
nuousFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma will be needed in the proof of the metric space instance, but it will
 become
useless afterwards as it will be superseded by the general result that the dista
nce is nonnegative
in metric spaces.
-/
private theorem dist_nonneg' : 0 ≤ dist f g :=
  le_csInf dist_set_exists fun _ => And.left

/-- The distance between two functions is controlled by the supremum of the pointwise distances. -/
/-
**BoundedContinuousFunction.dist_le** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：dist_le (C0 : (0 : Real) <= C) : dist f g <= C ↔ forall x : α, dist (f x) 
(g x) <= C
参数：C0 : (0 : Real) <= C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
The distance between two functions is controlled by the supremum of the pointwis
e distances.
-/
theorem dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C :=
  ⟨fun h x => le_trans (dist_coe_le_dist x) h, fun H => csInf_le ⟨0, fun _ => And.left⟩ ⟨C0, H⟩⟩
/-
**BoundedContinuousFunction.dist_le_iff_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `B
oundedContinuousFunction`。
形式化陈述：dist_le_iff_of_nonempty [Nonempty α] : dist f g <= C ↔ forall x, dist (f x
) (g x) <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C :=
  ⟨fun h x => le_trans (dist_coe_le_dist x) h,
    fun w => (dist_le (le_trans dist_nonneg (w (Nonempty.some ‹_›)))).mpr w⟩
/-
**BoundedContinuousFunction.dist_lt_of_nonempty_compact** 是 Mathlib 中的一个定理，位于命名空
间 `BoundedContinuousFunction`。
形式化陈述：dist_lt_of_nonempty_compact [Nonempty α] [CompactSpace α] (w : forall x : 
α, dist (f x) (g x) < C) : dist f g < C
参数：w : forall x : α, dist (f x) (g x) < C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `BoundedContinuousMapClass.toContinuousMapClass`：∀ {F : Type u_2} {α : ou
tParam (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst
_1 : PseudoMetricSpace β} {inst_2 : …
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.dist_le_iff_of_nonempty`：dist_le_iff_of_nonemp
ty [Nonempty α] : dist f g <= C ↔ forall x, dist (f x) (g x) <= C
· 使用定理 `trivial`：True
-/
theorem dist_lt_of_nonempty_compact [Nonempty α] [CompactSpace α]
    (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C := by
  have c : Continuous fun x => dist (f x) (g x) := by fun_prop
  obtain ⟨x, -, le⟩ :=
    IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty (Continuous.continuousOn c)
  exact lt_of_le_of_lt (dist_le_iff_of_nonempty.mpr fun y => le trivial) (w x)
/-
**BoundedContinuousFunction.dist_lt_iff_of_compact** 是 Mathlib 中的一个定理，位于命名空间 `Bo
undedContinuousFunction`。
形式化陈述：dist_lt_iff_of_compact [CompactSpace α] (C0 : (0 : Real) < C) : dist f g <
 C ↔ forall x : α, dist (f x) (g x) < C
参数：C0 : (0 : Real) < C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `BoundedContinuousFunction.dist_lt_of_nonempty_compact`：dist_lt_of_nonemp
ty_compact [Nonempty α] [CompactSpace α] (w : forall x : α, dist (f x) (g x) < C
) : dist f g < C
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.dist_eq`：dist_eq : dist f g = sInf { C | 0 <= 
C ∧ forall x : α, dist (f x) (g x) <= C }
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `_private.Mathlib.Topology.ContinuousMap.Bounded.Basic.0.BoundedContinuou
sFunction.dist_nonneg'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : PseudoMetricSpace β]   {f g : BoundedContinuousFunction α β}, 0 ≤ dist
 f g
-/
theorem dist_lt_iff_of_compact [CompactSpace α] (C0 : (0 : ℝ) < C) :
    dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  fconstructor
  · intro w x
    exact lt_of_le_of_lt (dist_coe_le_dist x) w
  · by_cases h : Nonempty α
    · exact dist_lt_of_nonempty_compact
    · rintro -
      convert! C0
      apply le_antisymm _ dist_nonneg'
      rw [dist_eq]
      exact csInf_le ⟨0, fun C => And.left⟩ ⟨le_rfl, fun x => False.elim (h (Nonempty.intro x))⟩
/-
**BoundedContinuousFunction.dist_lt_iff_of_nonempty_compact** 是 Mathlib 中的一个定理，位
于命名空间 `BoundedContinuousFunction`。
形式化陈述：dist_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] : dist f g <
 C ↔ forall x : α, dist (f x) (g x) < C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `BoundedContinuousFunction.dist_lt_of_nonempty_compact`：dist_lt_of_nonemp
ty_compact [Nonempty α] [CompactSpace α] (w : forall x : α, dist (f x) (g x) < C
) : dist f g < C
-/
theorem dist_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] :
    dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C :=
  ⟨fun w x => lt_of_le_of_lt (dist_coe_le_dist x) w, dist_lt_of_nonempty_compact⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The type of bounded continuous functions, with the uniform distance, is a pseudometric space. -/
/-
**BoundedContinuousFunction.instPseudoMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `Bou
ndedContinuousFunction`。
形式化陈述：instPseudoMetricSpace : PseudoMetricSpace (α ->ᵇ β) where dist_self f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of bounded continuous functions, with the uniform distance, is a pseudo
metric space.
-/
instance instPseudoMetricSpace : PseudoMetricSpace (α →ᵇ β) where
  dist_self f := le_antisymm ((dist_le le_rfl).2 fun x => by simp) dist_nonneg'
  dist_comm f g := by simp [dist_eq, dist_comm]
  dist_triangle _ _ _ := (dist_le (add_nonneg dist_nonneg' dist_nonneg')).2
    fun _ => le_trans (dist_triangle _ _ _) (add_le_add (dist_coe_le_dist _) (dist_coe_le_dist _))

/-- The type of bounded continuous functions, with the uniform distance, is a metric space. -/
/-
**BoundedContinuousFunction.instMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：instMetricSpace {β} [MetricSpace β] : MetricSpace (α ->ᵇ β) where eq_of_di
st_eq_zero hfg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of bounded continuous functions, with the uniform distance, is a metric
 space.
-/
instance instMetricSpace {β} [MetricSpace β] : MetricSpace (α →ᵇ β) where
  eq_of_dist_eq_zero hfg := by
    ext x
    exact eq_of_dist_eq_zero (le_antisymm (hfg ▸ dist_coe_le_dist _) dist_nonneg)
/-
**BoundedContinuousFunction.nndist_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：nndist_eq : nndist f g = sInf { C | forall x : α, nndist (f x) (g x) <= C 
}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoundedContinuousFunction.dist_eq`：dist_eq : dist f g = sInf { C | 0 <= 
C ∧ forall x : α, dist (f x) (g x) <= C }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.val_eq_coe`：val_eq_coe (n : Real>=0) : n.val = n
· 使用定理 `NNReal.coe_sInf`：coe_sInf (s : Set Real>=0) : (↑(sInf s) : Real) = sInf 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `NNReal.coe_image`：coe_image {s : Set Real>=0} : (↑) '' s = { x : Real | 
exists h : 0 <= x, .mk x h in s }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nndist_eq : nndist f g = sInf { C | ∀ x : α, nndist (f x) (g x) ≤ C } :=
  Subtype.ext <| dist_eq.trans <| by
    rw [val_eq_coe, coe_sInf, coe_image]
    simp_rw [mem_ofPred_eq, ← NNReal.coe_le_coe, NNReal.coe_mk, exists_prop, coe_nndist]
/-
**BoundedContinuousFunction.nndist_set_exists** 是 Mathlib 中的一个定理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：nndist_set_exists : exists C, forall x : α, nndist (f x) (g x) <= C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `BoundedContinuousFunction.dist_set_exists`：dist_set_exists : exists C, 0
 <= C ∧ forall x : α, dist (f x) (g x) <= C
-/
theorem nndist_set_exists : ∃ C, ∀ x : α, nndist (f x) (g x) ≤ C :=
  Subtype.exists.mpr <| dist_set_exists.imp fun _ ⟨ha, h⟩ => ⟨ha, h⟩
/-
**BoundedContinuousFunction.nndist_coe_le_nndist** 是 Mathlib 中的一个定理，位于命名空间 `Boun
dedContinuousFunction`。
形式化陈述：nndist_coe_le_nndist (x : α) : nndist (f x) (g x) <= nndist f g
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
-/
theorem nndist_coe_le_nndist (x : α) : nndist (f x) (g x) ≤ nndist f g :=
  dist_coe_le_dist x

/-- On an empty space, bounded continuous functions are at distance 0. -/
/-
**BoundedContinuousFunction.dist_zero_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：dist_zero_of_empty [IsEmpty α] : dist f g = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0

--- 原说明 ---
On an empty space, bounded continuous functions are at distance 0.
-/
theorem dist_zero_of_empty [IsEmpty α] : dist f g = 0 := by
  rw [(ext isEmptyElim : f = g), dist_self]
/-
**BoundedContinuousFunction.dist_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：dist_eq_iSup : dist f g = ⨆ x : α, dist (f x) (g x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `BoundedContinuousFunction.dist_zero_of_empty`：dist_zero_of_empty [IsEmpt
y α] : dist f g = 0
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.dist_le_iff_of_nonempty`：dist_le_iff_of_nonemp
ty [Nonempty α] : dist f g <= C ↔ forall x, dist (f x) (g x) <= C
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoundedContinuousFunction.dist_set_exists`：dist_set_exists : exists C, 0
 <= C ∧ forall x : α, dist (f x) (g x) <= C
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
-/
theorem dist_eq_iSup : dist f g = ⨆ x : α, dist (f x) (g x) := by
  cases isEmpty_or_nonempty α
  · rw [iSup_of_empty', Real.sSup_empty, dist_zero_of_empty]
  refine (dist_le_iff_of_nonempty.mpr <| le_ciSup ?_).antisymm (ciSup_le dist_coe_le_dist)
  exact dist_set_exists.imp fun C hC => forall_mem_range.2 hC.2
/-
**BoundedContinuousFunction.nndist_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：nndist_eq_iSup : nndist f g = ⨆ x : α, nndist (f x) (g x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoundedContinuousFunction.dist_eq_iSup`：dist_eq_iSup : dist f g = ⨆ x : 
α, dist (f x) (g x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_iSup`：coe_iSup {ι : Sort*} (s : ι -> Real>=0) : (↑(⨆ i, s i) 
: Real) = ⨆ i, ↑(s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nndist_eq_iSup : nndist f g = ⨆ x : α, nndist (f x) (g x) :=
  Subtype.ext <| dist_eq_iSup.trans <| by simp_rw [val_eq_coe, coe_iSup, coe_nndist]
/-
**BoundedContinuousFunction.edist_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：edist_eq_iSup : edist f g = ⨆ x, edist (f x) (g x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoundedContinuousFunction.nndist_eq_iSup`：nndist_eq_iSup : nndist f g = 
⨆ x : α, nndist (f x) (g x)
· 使用定理 `ENNReal.coe_iSup`：coe_iSup {ι : Sort*} {f : ι -> Real>=0} (hf : BddAbove
 (range f)) : (↑(iSup f) : Real>=0∞) = ⨆ a, ↑(f a)
· 使用定理 `BoundedContinuousFunction.nndist_coe_le_nndist`：nndist_coe_le_nndist (x 
: α) : nndist (f x) (g x) <= nndist f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem edist_eq_iSup : edist f g = ⨆ x, edist (f x) (g x) := by
  simp_rw [edist_nndist, nndist_eq_iSup]
  refine ENNReal.coe_iSup ⟨nndist f g, ?_⟩
  rintro - ⟨x, hx, rfl⟩
  exact nndist_coe_le_nndist x
/-
**BoundedContinuousFunction.tendsto_iff_tendstoUniformly** 是 Mathlib 中的一个定理，位于命名
空间 `BoundedContinuousFunction`。
形式化陈述：tendsto_iff_tendstoUniformly {ι : Type*} {F : ι -> α ->ᵇ β} {f : α ->ᵇ β} 
{l : Filter ι} : Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => F i) f l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendstoUniformly_iff`：tendstoUniformly_iff {F : ι -> β -> α} {f :
 β -> α} {p : Filter ι} : TendstoUniformly F f p ↔ forall ε > 0, forallᶠ n in p,
 forall x, dist (…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
-/
theorem tendsto_iff_tendstoUniformly {ι : Type*} {F : ι → α →ᵇ β} {f : α →ᵇ β} {l : Filter ι} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => F i) f l :=
  Iff.intro
    (fun h =>
      tendstoUniformly_iff.2 fun ε ε0 =>
        (Metric.tendsto_nhds.mp h ε ε0).mp
          (Eventually.of_forall fun n hn x =>
            lt_of_le_of_lt (dist_coe_le_dist x) (dist_comm (F n) f ▸ hn)))
    fun h =>
    Metric.tendsto_nhds.mpr fun _ ε_pos =>
      (h _ (dist_mem_uniformity <| half_pos ε_pos)).mp
        (Eventually.of_forall fun n hn =>
          lt_of_le_of_lt
            ((dist_le (half_pos ε_pos).le).mpr fun x => dist_comm (f x) (F n x) ▸ le_of_lt (hn x))
            (half_lt_self ε_pos))

/-- The topology on `α →ᵇ β` is exactly the topology induced by the natural map to `α →ᵤ β`. -/
/-
**BoundedContinuousFunction.isInducing_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：isInducing_coeFn : IsInducing (UniformFun.ofFun ∘ (⇑) : (α ->ᵇ β) -> α ->ᵤ
 β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `BoundedContinuousFunction.tendsto_iff_tendstoUniformly`：tendsto_iff_tend
stoUniformly {ι : Type*} {F : ι -> α ->ᵇ β} {f : α ->ᵇ β} {l : Filter ι} : Tends
to F l (𝓝 f) ↔ TendstoUniformly (fun i => F …
· 使用定理 `UniformFun.tendsto_iff_tendstoUniformly`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_4} {p : Filter ι} [inst : UniformSpace β] {F : ι → UniformFun α β} 
  {f : UniformFun α β}, Filte…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The topology on `α →ᵇ β` is exactly the topology induced by the natural map to `
α →ᵤ β`.
-/
theorem isInducing_coeFn : IsInducing (UniformFun.ofFun ∘ (⇑) : (α →ᵇ β) → α →ᵤ β) := by
  rw [isInducing_iff_nhds]
  refine fun f => eq_of_forall_le_iff fun l => ?_
  rw [← tendsto_iff_comap, ← tendsto_id', tendsto_iff_tendstoUniformly,
    UniformFun.tendsto_iff_tendstoUniformly]
  simp [comp_def]

-- TODO: upgrade to `IsUniformEmbedding`
/-
**BoundedContinuousFunction.isEmbedding_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：isEmbedding_coeFn : IsEmbedding (UniformFun.ofFun ∘ (⇑) : (α ->ᵇ β) -> α -
>ᵤ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.isInducing_coeFn`：isInducing_coeFn : IsInducin
g (UniformFun.ofFun ∘ (⇑) : (α ->ᵇ β) -> α ->ᵤ β)
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem isEmbedding_coeFn : IsEmbedding (UniformFun.ofFun ∘ (⇑) : (α →ᵇ β) → α →ᵤ β) :=
  ⟨isInducing_coeFn, fun _ _ h => ext fun x => congr_fun h x⟩

variable (α) in
/-- Constant as a continuous bounded function. -/
@[simps! -fullyApplied]
/-
**BoundedContinuousFunction.const** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuousFu
nction`。
形式化陈述：const (b : β) : α ->ᵇ β
参数：b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constant as a continuous bounded function.
-/
def const (b : β) : α →ᵇ β :=
  ⟨ContinuousMap.const α b, 0, by simp⟩
/-
**BoundedContinuousFunction.const_apply'** 是 Mathlib 中的一个定理，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：const_apply' (a : α) (b : β) : (const α b : α -> β) a = b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply' (a : α) (b : β) : (const α b : α → β) a = b := rfl

/-- If the target space is inhabited, so is the space of bounded continuous functions. -/
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the target space is inhabited, so is the space of bounded continuous function
s.
-/
instance [Inhabited β] : Inhabited (α →ᵇ β) :=
  ⟨const α default⟩
/-
**BoundedContinuousFunction.lipschitz_eval_const** 是 Mathlib 中的一个定理，位于命名空间 `Boun
dedContinuousFunction`。
形式化陈述：lipschitz_eval_const (x : α) : LipschitzWith 1 fun f : α ->ᵇ β => f x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.mk_one`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSp
ace α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f
 y) ≤ dist…
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
-/
theorem lipschitz_eval_const (x : α) : LipschitzWith 1 fun f : α →ᵇ β => f x :=
  LipschitzWith.mk_one fun _ _ => dist_coe_le_dist x

@[fun_prop]
/-
**BoundedContinuousFunction.uniformContinuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `Bou
ndedContinuousFunction`。
形式化陈述：uniformContinuous_coe : @UniformContinuous (α ->ᵇ β) (α -> β) _ _ (⇑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniformContinuous_pi`：uniformContinuous_pi {β : Type*} [UniformSpace β] 
{f : β -> forall i, α i} : UniformContinuous f ↔ forall i, UniformContinuous fun
 x => f x …
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `BoundedContinuousFunction.lipschitz_eval_const`：lipschitz_eval_const (x 
: α) : LipschitzWith 1 fun f : α ->ᵇ β => f x
-/
theorem uniformContinuous_coe : @UniformContinuous (α →ᵇ β) (α → β) _ _ (⇑) :=
  uniformContinuous_pi.2 fun x => (lipschitz_eval_const x).uniformContinuous
/-
**BoundedContinuousFunction.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：continuous_coe : Continuous fun (f : α ->ᵇ β) x => f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `BoundedContinuousFunction.uniformContinuous_coe`：uniformContinuous_coe :
 @UniformContinuous (α ->ᵇ β) (α -> β) _ _ (⇑)
-/
theorem continuous_coe : Continuous fun (f : α →ᵇ β) x => f x :=
  UniformContinuous.continuous uniformContinuous_coe

/-- The evaluation map is continuous, as a joint function of `u` and `x`. -/
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation map is continuous, as a joint function of `u` and `x`.
-/
instance : ContinuousEval (α →ᵇ β) α β where
  continuous_eval := continuous_prod_of_continuous_lipschitzWith _ 1
    (fun f ↦ f.continuous) lipschitz_eval_const

/-- When `x` is fixed, `(f : α →ᵇ β) ↦ f x` is continuous. -/
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `x` is fixed, `(f : α →ᵇ β) ↦ f x` is continuous.
-/
instance : ContinuousEvalConst (α →ᵇ β) α β := inferInstance

/-- Bounded continuous functions taking values in a complete space form a complete space. -/
/-
**BoundedContinuousFunction.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：instCompleteSpace [CompleteSpace β] : CompleteSpace (α ->ᵇ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.complete_of_cauchySeq_tendsto`：Metric.complete_of_cauchySeq_tends
to : (forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) -> Co
mpleteSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchySeq_iff_le_tendsto_0`：cauchySeq_iff_le_tendsto_0 {s : Nat -> α} : 
CauchySeq s ↔ exists b : Nat -> Real, (forall n, 0 <= b n) ∧ (forall n m N : Nat
, N <= n -> N <=…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetri
cSpace α] {f g : β → α} {x : Filter β} {a b : α},   Filter.Tendsto f x (nhds a) 
→     Fil…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Metric.tendstoUniformly_iff`：tendstoUniformly_iff {F : ι -> β -> α} {f :
 β -> α} {p : Filter ι} : TendstoUniformly F f p ↔ forall ε > 0, forallᶠ n in p,
 forall x, dist (…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `TendstoUniformly.continuous`：∀ {α : Type u_1} {β : Type u_2} {ι : Type u
_3} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → α → β}   {f :
 α → β} {p : Filt…
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `BoundedContinuousFunction.bounded`：∀ {α : Type u} {β : Type v} [inst : T
opologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFuncti
on α β), ∃ C, ∀ (x y : …
· 使用定理 `dist_triangle4_left`：dist_triangle4_left (x₁ y₁ x₂ y₂ : α) : dist x₂ y₂ 
<= dist x₁ y₁ + (dist x₁ x₂ + dist y₁ y₂)
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Bounded continuous functions taking values in a complete space form a complete s
pace.
-/
instance instCompleteSpace [CompleteSpace β] : CompleteSpace (α →ᵇ β) :=
  complete_of_cauchySeq_tendsto fun (f : ℕ → α →ᵇ β) (hf : CauchySeq f) => by
    /- We have to show that `f n` converges to a bounded continuous function.
      For this, we prove pointwise convergence to define the limit, then check
      it is a continuous bounded function, and then check the norm convergence. -/
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have f_bdd := fun x n m N hn hm => le_trans (dist_coe_le_dist x) (b_bound n m N hn hm)
    have fx_cau : ∀ x, CauchySeq fun n => f n x :=
      fun x => cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, f_bdd x, b_lim⟩
    choose F hF using fun x => cauchySeq_tendsto_of_complete (fx_cau x)
    /- `F : α → β`, `hF : ∀ (x : α), Tendsto (fun n ↦ ↑(f n) x) atTop (𝓝 (F x))`
      `F` is the desired limit function. Check that it is uniformly approximated by `f N`. -/
    have fF_bdd : ∀ x N, dist (f N x) (F x) ≤ b N :=
      fun x N => le_of_tendsto (tendsto_const_nhds.dist (hF x))
        (Filter.eventually_atTop.2 ⟨N, fun n hn => f_bdd x N n N (le_refl N) hn⟩)
    refine ⟨⟨⟨F, ?_⟩, ?_⟩, ?_⟩
    · -- Check that `F` is continuous, as a uniform limit of continuous functions
      have : TendstoUniformly (fun n x => f n x) F atTop := by
        refine Metric.tendstoUniformly_iff.2 fun ε ε0 => ?_
        refine ((tendsto_order.1 b_lim).2 ε ε0).mono fun n hn x => ?_
        rw [dist_comm]
        exact lt_of_le_of_lt (fF_bdd x n) hn
      exact this.continuous (Frequently.of_forall fun N => (f N).continuous)
    · -- Check that `F` is bounded
      rcases (f 0).bounded with ⟨C, hC⟩
      refine ⟨C + (b 0 + b 0), fun x y => ?_⟩
      calc
        dist (F x) (F y) ≤ dist (f 0 x) (f 0 y) + (dist (f 0 x) (F x) + dist (f 0 y) (F y)) :=
          dist_triangle4_left _ _ _ _
        _ ≤ C + (b 0 + b 0) := add_le_add (hC x y) (add_le_add (fF_bdd x 0) (fF_bdd y 0))
    · -- Check that `F` is close to `f N` in distance terms
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) ?_ b_lim)
      exact fun N => (dist_le (b0 _)).2 fun x => fF_bdd x N

/-- Composition of a bounded continuous function and a continuous function. -/
/-
**BoundedContinuousFunction.compContinuous** 是 Mathlib 中的一个定义，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：compContinuous {δ : Type*} [TopologicalSpace δ] (f : α ->ᵇ β) (g : C(δ, α)
) : δ ->ᵇ β where toContinuousMap
参数：f : α ->ᵇ β；g : C(δ, α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a bounded continuous function and a continuous function.
-/
def compContinuous {δ : Type*} [TopologicalSpace δ] (f : α →ᵇ β) (g : C(δ, α)) : δ →ᵇ β where
  toContinuousMap := f.1.comp g
  map_bounded' := f.map_bounded'.imp fun _ hC _ _ => hC _ _

@[simp]
/-
**BoundedContinuousFunction.coe_compContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：coe_compContinuous {δ : Type*} [TopologicalSpace δ] (f : α ->ᵇ β) (g : C(δ
, α)) : ⇑(f.compContinuous g) = f ∘ g
参数：f : α ->ᵇ β；g : C(δ, α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compContinuous {δ : Type*} [TopologicalSpace δ] (f : α →ᵇ β) (g : C(δ, α)) :
    ⇑(f.compContinuous g) = f ∘ g := rfl

@[simp]
/-
**BoundedContinuousFunction.compContinuous_apply** 是 Mathlib 中的一个定理，位于命名空间 `Boun
dedContinuousFunction`。
形式化陈述：compContinuous_apply {δ : Type*} [TopologicalSpace δ] (f : α ->ᵇ β) (g : C
(δ, α)) (x : δ) : f.compContinuous g x = f (g x)
参数：f : α ->ᵇ β；g : C(δ, α)；x : δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compContinuous_apply {δ : Type*} [TopologicalSpace δ] (f : α →ᵇ β) (g : C(δ, α)) (x : δ) :
    f.compContinuous g x = f (g x) := rfl
/-
**BoundedContinuousFunction.lipschitz_compContinuous** 是 Mathlib 中的一个定理，位于命名空间 `
BoundedContinuousFunction`。
形式化陈述：lipschitz_compContinuous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) : 
LipschitzWith 1 fun f : α ->ᵇ β => f.compContinuous g
参数：g : C(δ, α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.mk_one`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSp
ace α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f
 y) ≤ dist…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
-/
theorem lipschitz_compContinuous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) :
    LipschitzWith 1 fun f : α →ᵇ β => f.compContinuous g :=
  LipschitzWith.mk_one fun _ _ => (dist_le dist_nonneg).2 fun x => dist_coe_le_dist (g x)
/-
**BoundedContinuousFunction.continuous_compContinuous** 是 Mathlib 中的一个定理，位于命名空间 
`BoundedContinuousFunction`。
形式化陈述：continuous_compContinuous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) :
 Continuous fun f : α ->ᵇ β => f.compContinuous g
参数：g : C(δ, α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `BoundedContinuousFunction.lipschitz_compContinuous`：lipschitz_compContin
uous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) : LipschitzWith 1 fun f : α 
->ᵇ β => f.compContinuous g
-/
theorem continuous_compContinuous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) :
    Continuous fun f : α →ᵇ β => f.compContinuous g :=
  (lipschitz_compContinuous g).continuous

/-- Restrict the domain of a bounded continuous function to a set. -/
/-
**BoundedContinuousFunction.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：domRestrict (f : α ->ᵇ β) (s : Set α) : s ->ᵇ β
参数：f : α ->ᵇ β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the domain of a bounded continuous function to a set.
-/
def domRestrict (f : α →ᵇ β) (s : Set α) : s →ᵇ β :=
  f.compContinuous <| (ContinuousMap.id _).restrict s

@[simp]
/-
**BoundedContinuousFunction.coe_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：coe_domRestrict (f : α ->ᵇ β) (s : Set α) : ⇑(f.domRestrict s) = f ∘ (↑)
参数：f : α ->ᵇ β；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_domRestrict (f : α →ᵇ β) (s : Set α) : ⇑(f.domRestrict s) = f ∘ (↑) := rfl

@[simp]
/-
**BoundedContinuousFunction.domRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：domRestrict_apply (f : α ->ᵇ β) (s : Set α) (x : s) : f.domRestrict s x = 
f x
参数：f : α ->ᵇ β；s : Set α；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_apply (f : α →ᵇ β) (s : Set α) (x : s) : f.domRestrict s x = f x := rfl

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias coe_restrict := coe_domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

/-- Composition (in the target) of a bounded continuous function with a Lipschitz map again
gives a bounded continuous function. -/
/-
**BoundedContinuousFunction.comp** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuousFun
ction`。
形式化陈述：comp (G : β -> γ) {C : Real>=0} (H : LipschitzWith C G) (f : α ->ᵇ β) : α 
->ᵇ γ
参数：G : β -> γ；H : LipschitzWith C G；f : α ->ᵇ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition (in the target) of a bounded continuous function with a Lipschitz ma
p again
gives a bounded continuous function.
-/
def comp (G : β → γ) {C : ℝ≥0} (H : LipschitzWith C G) (f : α →ᵇ β) : α →ᵇ γ :=
  ⟨⟨fun x => G (f x), H.continuous.comp f.continuous⟩,
    let ⟨D, hD⟩ := f.bounded
    ⟨max C 0 * D, fun x y =>
      calc
        dist (G (f x)) (G (f y)) ≤ C * dist (f x) (f y) := H.dist_le_mul _ _
        _ ≤ max C 0 * dist (f x) (f y) := by gcongr; apply le_max_left
        _ ≤ max C 0 * D := by gcongr; apply hD
        ⟩⟩

@[simp]
/-
**BoundedContinuousFunction.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：comp_apply (G : β -> γ) {C : Real>=0} (H : LipschitzWith C G) (f : α ->ᵇ β
) (a : α) : (f.comp G H) a = G (f a)
参数：G : β -> γ；H : LipschitzWith C G；f : α ->ᵇ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (G : β → γ) {C : ℝ≥0} (H : LipschitzWith C G) (f : α →ᵇ β) (a : α) :
    (f.comp G H) a = G (f a) := rfl

/-- The composition operator (in the target) with a Lipschitz map is Lipschitz. -/
/-
**BoundedContinuousFunction.lipschitz_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：lipschitz_comp {G : β -> γ} {C : Real>=0} (H : LipschitzWith C G) : Lipsch
itzWith C (comp G H : (α ->ᵇ β) -> α ->ᵇ γ)
参数：H : LipschitzWith C G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r

--- 原说明 ---
The composition operator (in the target) with a Lipschitz map is Lipschitz.
-/
theorem lipschitz_comp {G : β → γ} {C : ℝ≥0} (H : LipschitzWith C G) :
    LipschitzWith C (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
  LipschitzWith.of_dist_le_mul fun f g =>
    (dist_le (mul_nonneg C.2 dist_nonneg)).2 fun x =>
      calc
        dist (G (f x)) (G (g x)) ≤ C * dist (f x) (g x) := H.dist_le_mul _ _
        _ ≤ C * dist f g := by gcongr; apply dist_coe_le_dist

/-- The composition operator (in the target) with a Lipschitz map is uniformly continuous. -/
@[fun_prop]
/-
**BoundedContinuousFunction.uniformContinuous_comp** 是 Mathlib 中的一个定理，位于命名空间 `Bo
undedContinuousFunction`。
形式化陈述：uniformContinuous_comp {G : β -> γ} {C : Real>=0} (H : LipschitzWith C G) 
: UniformContinuous (comp G H : (α ->ᵇ β) -> α ->ᵇ γ)
参数：H : LipschitzWith C G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `BoundedContinuousFunction.lipschitz_comp`：lipschitz_comp {G : β -> γ} {C
 : Real>=0} (H : LipschitzWith C G) : LipschitzWith C (comp G H : (α ->ᵇ β) -> α
 ->ᵇ γ)

--- 原说明 ---
The composition operator (in the target) with a Lipschitz map is uniformly conti
nuous.
-/
theorem uniformContinuous_comp {G : β → γ} {C : ℝ≥0} (H : LipschitzWith C G) :
    UniformContinuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
  (lipschitz_comp H).uniformContinuous

/-- The composition operator (in the target) with a Lipschitz map is continuous. -/
/-
**BoundedContinuousFunction.continuous_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：continuous_comp {G : β -> γ} {C : Real>=0} (H : LipschitzWith C G) : Conti
nuous (comp G H : (α ->ᵇ β) -> α ->ᵇ γ)
参数：H : LipschitzWith C G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `BoundedContinuousFunction.lipschitz_comp`：lipschitz_comp {G : β -> γ} {C
 : Real>=0} (H : LipschitzWith C G) : LipschitzWith C (comp G H : (α ->ᵇ β) -> α
 ->ᵇ γ)

--- 原说明 ---
The composition operator (in the target) with a Lipschitz map is continuous.
-/
theorem continuous_comp {G : β → γ} {C : ℝ≥0} (H : LipschitzWith C G) :
    Continuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
  (lipschitz_comp H).continuous

/-- Restriction (in the target) of a bounded continuous function taking values in a subset. -/
/-
**BoundedContinuousFunction.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：codRestrict (s : Set β) (f : α ->ᵇ β) (H : forall x, f x in s) : α ->ᵇ s
参数：s : Set β；f : α ->ᵇ β；H : forall x, f x in s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.bounded`：∀ {α : Type u} {β : Type v} [inst : T
opologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFuncti
on α β), ∃ C, ∀ (x y : …

--- 原说明 ---
Restriction (in the target) of a bounded continuous function taking values in a 
subset.
-/
def codRestrict (s : Set β) (f : α →ᵇ β) (H : ∀ x, f x ∈ s) : α →ᵇ s :=
  ⟨⟨s.codRestrict f H, f.continuous.subtype_mk _⟩, f.bounded⟩

section Extend

variable {δ : Type*} [TopologicalSpace δ] [DiscreteTopology δ]

/-- A version of `Function.extend` for bounded continuous maps. We assume that the domain has
discrete topology, so we only need to verify boundedness. -/
nonrec def extend (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : δ →ᵇ β where
  toFun := extend f g h
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := by
    rw [← isBounded_range_iff, range_extend f.injective]
    exact g.isBounded_range.union (h.isBounded_image _)

@[simp]
/-
**BoundedContinuousFunction.extend_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：extend_apply (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) (x : α) : extend f g 
h (f x) = g x
参数：f : α ↪ δ；g : α ->ᵇ β；h : δ ->ᵇ β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem extend_apply (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) (x : α) : extend f g h (f x) = g x :=
  f.injective.extend_apply _ _ _

@[simp]
nonrec theorem extend_comp (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : extend f g h ∘ f = g :=
  extend_comp f.injective _ _

nonrec theorem extend_apply' {f : α ↪ δ} {x : δ} (hx : x ∉ range f) (g : α →ᵇ β) (h : δ →ᵇ β) :
    extend f g h x = h x :=
  extend_apply' _ _ _ hx
/-
**BoundedContinuousFunction.extend_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：extend_of_empty [IsEmpty α] (f : α ↪ δ) (g : α ->ᵇ β) (h : δ ->ᵇ β) : exte
nd f g h = h
参数：f : α ↪ δ；g : α ->ᵇ β；h : δ ->ᵇ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Function.extend_of_isEmpty`：Function.extend_of_isEmpty [IsEmpty α] (f : 
α -> β) (g : α -> γ) (h : β -> γ) : Function.extend f g h = h
-/
theorem extend_of_empty [IsEmpty α] (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : extend f g h = h :=
  DFunLike.coe_injective <| Function.extend_of_isEmpty f g h

@[simp]
/-
**BoundedContinuousFunction.dist_extend_extend** 是 Mathlib 中的一个定理，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：dist_extend_extend (f : α ↪ δ) (g₁ g₂ : α ->ᵇ β) (h₁ h₂ : δ ->ᵇ β) : dist 
(g₁.extend f h₁) (g₂.extend f h₂) = max (dist g₁ g₂) (dist (h₁.domRestrict (rang
e f)ᶜ) (h₂.domRestrict (range f)ᶜ))
参数：f : α ↪ δ；g₁ g₂ : α ->ᵇ β；h₁ h₂ : δ ->ᵇ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `BoundedContinuousFunction.extend_apply`：extend_apply (f : α ↪ δ) (g : α 
->ᵇ β) (h : δ ->ᵇ β) (x : α) : extend f g h (f x) = g x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `BoundedContinuousFunction.extend_apply'`：∀ {α : Type u} {β : Type v} [in
st : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] {δ : Type u_2}   [inst_2
 : TopologicalSpace δ] [inst_…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
-/
theorem dist_extend_extend (f : α ↪ δ) (g₁ g₂ : α →ᵇ β) (h₁ h₂ : δ →ᵇ β) :
    dist (g₁.extend f h₁) (g₂.extend f h₂) =
      max (dist g₁ g₂) (dist (h₁.domRestrict (range f)ᶜ) (h₂.domRestrict (range f)ᶜ)) := by
  refine le_antisymm ((dist_le <| le_max_iff.2 <| Or.inl dist_nonneg).2 fun x => ?_) (max_le ?_ ?_)
  · rcases em (∃ y, f y = x) with (⟨x, rfl⟩ | hx)
    · simp only [extend_apply]
      exact (dist_coe_le_dist x).trans (le_max_left _ _)
    · simp only [extend_apply' hx]
      lift x to ((range f)ᶜ : Set δ) using hx
      calc
        dist (h₁ x) (h₂ x) = dist (h₁.domRestrict (range f)ᶜ x) (h₂.domRestrict (range f)ᶜ x) := rfl
        _ ≤ dist (h₁.domRestrict (range f)ᶜ) (h₂.domRestrict (range f)ᶜ) := dist_coe_le_dist x
        _ ≤ _ := le_max_right _ _
  · refine (dist_le dist_nonneg).2 fun x => ?_
    rw [← extend_apply f g₁ h₁, ← extend_apply f g₂ h₂]
    exact dist_coe_le_dist _
  · refine (dist_le dist_nonneg).2 fun x => ?_
    calc
      dist (h₁ x) (h₂ x) = dist (extend f g₁ h₁ x) (extend f g₂ h₂ x) := by
        rw [extend_apply' x.coe_prop, extend_apply' x.coe_prop]
      _ ≤ _ := dist_coe_le_dist _
/-
**BoundedContinuousFunction.isometry_extend** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：isometry_extend (f : α ↪ δ) (h : δ ->ᵇ β) : Isometry fun g : α ->ᵇ β => ex
tend f g h
参数：f : α ↪ δ；h : δ ->ᵇ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.dist_extend_extend`：dist_extend_extend (f : α 
↪ δ) (g₁ g₂ : α ->ᵇ β) (h₁ h₂ : δ ->ᵇ β) : dist (g₁.extend f h₁) (g₂.extend f h₂
) = max (dist g₁ g₂) (dist (h₁.dom…
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isometry_extend (f : α ↪ δ) (h : δ →ᵇ β) : Isometry fun g : α →ᵇ β => extend f g h :=
  Isometry.of_dist_eq fun g₁ g₂ => by simp

end Extend

/-- The indicator function of a clopen set, as a bounded continuous function. -/
@[simps]
/-
**BoundedContinuousFunction.indicator** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：indicator (s : Set α) (hs : IsClopen s) : BoundedContinuousFunction α Real
 where toFun
参数：s : Set α；hs : IsClopen s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indicator function of a clopen set, as a bounded continuous function.
-/
noncomputable def indicator (s : Set α) (hs : IsClopen s) : BoundedContinuousFunction α ℝ where
  toFun := s.indicator 1
  continuous_toFun := continuous_indicator (by simp [hs]) <| continuous_const.continuousOn
  map_bounded' := ⟨1, fun x y ↦ by by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp [hx, hy]⟩

end Basics

section One

variable [TopologicalSpace α] [PseudoMetricSpace β] [One β]

/-
**BoundedContinuousFunction.instOne** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : TopologicalSpace α] → [inst_1 
: PseudoMetricSpace β] → [One β] → One (BoundedContinuousFunction α β)
参数：BoundedContinuousFunction α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instOne : One (α →ᵇ β) := ⟨const α 1⟩

@[to_additive (attr := simp)]
/-
**BoundedContinuousFunction.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：coe_one : ((1 : α ->ᵇ β) : α -> β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : α →ᵇ β) : α → β) = 1 := rfl

@[to_additive (attr := simp)]
/-
**BoundedContinuousFunction.mkOfCompact_one** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：mkOfCompact_one [CompactSpace α] : mkOfCompact (1 : C(α, β)) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkOfCompact_one [CompactSpace α] : mkOfCompact (1 : C(α, β)) = 1 := rfl

@[to_additive]
/-
**BoundedContinuousFunction.forall_coe_one_iff_one** 是 Mathlib 中的一个定理，位于命名空间 `Bo
undedContinuousFunction`。
形式化陈述：forall_coe_one_iff_one (f : α ->ᵇ β) : (forall x, f x = 1) ↔ f = 1
参数：f : α ->ᵇ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem forall_coe_one_iff_one (f : α →ᵇ β) : (∀ x, f x = 1) ↔ f = 1 :=
  (@DFunLike.ext_iff _ _ _ _ f 1).symm

@[to_additive (attr := simp)]
/-
**BoundedContinuousFunction.one_compContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：one_compContinuous [TopologicalSpace γ] (f : C(γ, α)) : (1 : α ->ᵇ β).comp
Continuous f = 1
参数：f : C(γ, α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_compContinuous [TopologicalSpace γ] (f : C(γ, α)) : (1 : α →ᵇ β).compContinuous f = 1 :=
  rfl

end One

section mul

variable {R : Type*} [TopologicalSpace α] [PseudoMetricSpace R]

@[to_additive]
/-
**BoundedContinuousFunction.instMul** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：instMul [Mul R] [BoundedMul R] [ContinuousMul R] : Mul (α ->ᵇ R) where mul
 f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul [Mul R] [BoundedMul R] [ContinuousMul R] :
    Mul (α →ᵇ R) where
  mul f g :=
    { toFun := fun x ↦ f x * g x
      continuous_toFun := f.continuous.mul g.continuous
      map_bounded' := mul_bounded_of_bounded_of_bounded (map_bounded f) (map_bounded g) }

@[to_additive (attr := simp)]
/-
**BoundedContinuousFunction.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：coe_mul [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α ->ᵇ R) : ⇑(f * g
) = f * g
参数：f g : α ->ᵇ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α →ᵇ R) : ⇑(f * g) = f * g := rfl

@[to_additive]
/-
**BoundedContinuousFunction.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：mul_apply [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α ->ᵇ R) (x : α)
 : (f * g) x = f x * g x
参数：f g : α ->ᵇ R；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α →ᵇ R) (x : α) :
    (f * g) x = f x * g x := rfl

@[deprecated "dont use `nsmulRec` directly" (since := "2026-03-06")]
/-
**BoundedContinuousFunction.coe_nsmulRec** 是 Mathlib 中的一个定理，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : PseudoMe
tricSpace β] [inst_2 : AddMonoid β]   [inst_3 : BoundedAdd β] [inst_4 : Continuo
usAdd β] (f : BoundedContinuousFunction α β) (n : ℕ),   ⇑(nsmulRec n f) = n • ⇑f
参数：f : BoundedContinuousFunction α β；n : ℕ；nsmulRec n f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nsmulRec [PseudoMetricSpace β] [AddMonoid β] [BoundedAdd β] [ContinuousAdd β]
    (f : α →ᵇ β) : ∀ n, ⇑(nsmulRec n f) = n • ⇑f
  | 0 => by rw [nsmulRec, zero_smul, coe_zero]
  | n + 1 => by rw [nsmulRec, succ_nsmul, coe_add, coe_nsmulRec _ n]

@[to_additive]
/-
**BoundedContinuousFunction.instPow** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：instPow [Monoid R] [BoundedMul R] [ContinuousMul R] : Pow (α ->ᵇ R) Nat wh
ere pow f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPow [Monoid R] [BoundedMul R] [ContinuousMul R] : Pow (α →ᵇ R) ℕ where
  pow f n :=
    { toFun := fun x ↦ (f x) ^ n
      continuous_toFun := f.continuous.pow n
      map_bounded' := by
        obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp <| isBounded_pow (isBounded_range f) n
        exact ⟨C, fun x y ↦ hC (by simp) (by simp)⟩ }

@[to_additive]
/-
**BoundedContinuousFunction.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：coe_pow [Monoid R] [BoundedMul R] [ContinuousMul R] (n : Nat) (f : α ->ᵇ R
) : ⇑(f ^ n) = (⇑f) ^ n
参数：n : Nat；f : α ->ᵇ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow [Monoid R] [BoundedMul R] [ContinuousMul R] (n : ℕ) (f : α →ᵇ R) :
    ⇑(f ^ n) = (⇑f) ^ n := rfl

@[to_additive (attr := simp)]
/-
**BoundedContinuousFunction.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：pow_apply [Monoid R] [BoundedMul R] [ContinuousMul R] (n : Nat) (f : α ->ᵇ
 R) (x : α) : (f ^ n) x = f x ^ n
参数：n : Nat；f : α ->ᵇ R；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_apply [Monoid R] [BoundedMul R] [ContinuousMul R] (n : ℕ) (f : α →ᵇ R) (x : α) :
    (f ^ n) x = f x ^ n := rfl

@[to_additive]
/-
**BoundedContinuousFunction.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：instMonoid [Monoid R] [BoundedMul R] [ContinuousMul R] : Monoid (α ->ᵇ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid [Monoid R] [BoundedMul R] [ContinuousMul R] :
    Monoid (α →ᵇ R) := fast_instance%
  Injective.monoid _ DFunLike.coe_injective rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive]
/-
**BoundedContinuousFunction.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：instCommMonoid [CommMonoid R] [BoundedMul R] [ContinuousMul R] : CommMonoi
d (α ->ᵇ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid [CommMonoid R] [BoundedMul R] [ContinuousMul R] :
    CommMonoid (α →ᵇ R) := fast_instance%
  Injective.commMonoid _ DFunLike.coe_injective rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Coercion of a `BoundedContinuousFunction` is a `MonoidHom`. Similar to `MonoidHom.coeFn`. -/
@[to_additive (attr := simps) /-- Coercion of a `BoundedContinuousFunction` is an `AddMonoidHom`.
Similar to `AddMonoidHom.coeFn`. -/]
/-
**BoundedContinuousFunction.coeFnMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：coeFnMonoidHom [Monoid R] [BoundedMul R] [ContinuousMul R] : (α ->ᵇ R) ->*
 α -> R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coeFnMonoidHom [Monoid R] [BoundedMul R] [ContinuousMul R] : (α →ᵇ R) →* α → R where
  toFun := (⇑)
  map_one' := coe_one
  map_mul' := coe_mul

variable (α R) in
/-- The multiplicative map forgetting that a bounded continuous function is bounded. -/
@[to_additive (attr := simps) /-- The additive map forgetting that a bounded continuous
function is bounded.-/]
/-
**BoundedContinuousFunction.toContinuousMapMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `
BoundedContinuousFunction`。
形式化陈述：toContinuousMapMonoidHom [Monoid R] [BoundedMul R] [ContinuousMul R] : (α 
->ᵇ R) ->* C(α, R) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toContinuousMapMonoidHom [Monoid R] [BoundedMul R] [ContinuousMul R] : (α →ᵇ R) →* C(α, R) where
  toFun := toContinuousMap
  map_one' := rfl
  map_mul' := by
    intros
    ext
    simp

@[to_additive (attr := simp)]
/-
**BoundedContinuousFunction.coe_prod** 是 Mathlib 中的一个引理，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：coe_prod {ι : Type*} (s : Finset ι) [CommMonoid R] [BoundedMul R] [Continu
ousMul R] (f : ι -> α ->ᵇ R) : ⇑(∏ i in s, f i) = ∏ i in s, ⇑(f i)
参数：s : Finset ι；f : ι -> α ->ᵇ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
lemma coe_prod {ι : Type*} (s : Finset ι) [CommMonoid R] [BoundedMul R] [ContinuousMul R]
    (f : ι → α →ᵇ R) :
    ⇑(∏ i ∈ s, f i) = ∏ i ∈ s, ⇑(f i) := map_prod coeFnMonoidHom f s

@[to_additive]
/-
**BoundedContinuousFunction.prod_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：prod_apply {ι : Type*} (s : Finset ι) [CommMonoid R] [BoundedMul R] [Conti
nuousMul R] (f : ι -> α ->ᵇ R) (a : α) : (∏ i in s, f i) a = ∏ i in s, f i a
参数：s : Finset ι；f : ι -> α ->ᵇ R；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `BoundedContinuousFunction.coe_prod`：coe_prod {ι : Type*} (s : Finset ι) 
[CommMonoid R] [BoundedMul R] [ContinuousMul R] (f : ι -> α ->ᵇ R) : ⇑(∏ i in s,
 f i) = ∏ i in s, ⇑(f i)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_apply {ι : Type*} (s : Finset ι) [CommMonoid R] [BoundedMul R] [ContinuousMul R]
    (f : ι → α →ᵇ R) (a : α) :
    (∏ i ∈ s, f i) a = ∏ i ∈ s, f i a := by simp

@[to_additive]
/-
**BoundedContinuousFunction.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：instMulOneClass [MulOneClass R] [BoundedMul R] [ContinuousMul R] : MulOneC
lass (α ->ᵇ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulOneClass [MulOneClass R] [BoundedMul R] [ContinuousMul R] : MulOneClass (α →ᵇ R) :=
  fast_instance% DFunLike.coe_injective.mulOneClass _ coe_one coe_mul

/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological monoids, as a
`MonoidHom`. Similar to `MonoidHom.compLeftContinuous`. -/
@[to_additive (attr := simps)
/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological `AddMonoid`s,
as a `AddMonoidHom`. Similar to `AddMonoidHom.compLeftContinuous`. -/]
/-
**BoundedContinuousFunction._root_.MonoidHom.compLeftContinuousBounded** 是 Mathl
ib 中的一个定义，位于命名空间 `BoundedContinuousFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def _root_.MonoidHom.compLeftContinuousBounded (α : Type*)
    [TopologicalSpace α] [PseudoMetricSpace β] [Monoid β] [BoundedMul β] [ContinuousMul β]
    [PseudoMetricSpace γ] [Monoid γ] [BoundedMul γ] [ContinuousMul γ]
    (g : β →* γ) {C : NNReal} (hg : LipschitzWith C g) :
    (α →ᵇ β) →* (α →ᵇ γ) where
  toFun f := f.comp g hg
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _

end mul

section add

variable [TopologicalSpace α] [PseudoMetricSpace β]
variable {C : ℝ}

@[simp]
/-
**BoundedContinuousFunction.mkOfCompact_add** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：mkOfCompact_add [CompactSpace α] [Add β] [BoundedAdd β] [ContinuousAdd β] 
(f g : C(α, β)) : mkOfCompact (f + g) = mkOfCompact f + mkOfCompact g
参数：f g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkOfCompact_add [CompactSpace α] [Add β] [BoundedAdd β] [ContinuousAdd β] (f g : C(α, β)) :
    mkOfCompact (f + g) = mkOfCompact f + mkOfCompact g := rfl
/-
**BoundedContinuousFunction.add_compContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：add_compContinuous [Add β] [BoundedAdd β] [ContinuousAdd β] [TopologicalSp
ace γ] (f g : α ->ᵇ β) (h : C(γ, α)) : (g + f).compContinuous h = g.compContinuo
us h + f.compContinuous h
参数：f g : α ->ᵇ β；h : C(γ, α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_compContinuous [Add β] [BoundedAdd β] [ContinuousAdd β] [TopologicalSpace γ]
    (f g : α →ᵇ β) (h : C(γ, α)) :
    (g + f).compContinuous h = g.compContinuous h + f.compContinuous h := rfl

end add

section LipschitzAdd

/- In this section, if `β` is an `AddMonoid` whose addition operation is Lipschitz, then we show
that the space of bounded continuous functions from `α` to `β` inherits a topological `AddMonoid`
structure, by using pointwise operations and checking that they are compatible with the uniform
distance.

Implementation note: The material in this section could have been written for `LipschitzMul`
and transported by `@[to_additive]`. We choose not to do this because this causes a few lemma
names (for example, `coe_mul`) to conflict with later lemma names for normed rings; this is only a
trivial inconvenience, but in any case there are no obvious applications of the multiplicative
version. -/

variable [TopologicalSpace α] [PseudoMetricSpace β] [AddMonoid β] [LipschitzAdd β]
variable (f g : α →ᵇ β) {x : α} {C : ℝ}

/-
**BoundedContinuousFunction.instLipschitzAdd** 是 Mathlib 中的一个实例，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：instLipschitzAdd : LipschitzAdd (α ->ᵇ β) where lipschitz_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `LipschitzAdd.continuousAdd`：∀ {β : Type u_2} [inst : PseudoMetricSpace β
] [inst_1 : AddMonoid β] [LipschitzAdd β], ContinuousAdd β
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lipschitzWith_iff_dist_le_mul`：lipschitzWith_iff_dist_le_mul [PseudoMetr
icSpace α] [PseudoMetricSpace β] {K : Real>=0} {f : α -> β} : LipschitzWith K f 
↔ forall x y, dist …
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `lipschitz_with_lipschitz_const_add`：∀ {β : Type u_2} [inst : PseudoMetri
cSpace β] [inst_1 : AddMonoid β] [inst_2 : LipschitzAdd β] (p q : β × β),   dist
 (p.1 + p.2) (q.1 + q.2)…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
-/
instance instLipschitzAdd : LipschitzAdd (α →ᵇ β) where
  lipschitz_add :=
    ⟨LipschitzAdd.C β, by
      have C_nonneg := (LipschitzAdd.C β).coe_nonneg
      rw [lipschitzWith_iff_dist_le_mul]
      rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
      rw [dist_le (mul_nonneg C_nonneg dist_nonneg)]
      intro x
      refine le_trans (lipschitz_with_lipschitz_const_add ⟨f₁ x, g₁ x⟩ ⟨f₂ x, g₂ x⟩) ?_
      gcongr
      apply max_le_max <;> exact dist_coe_le_dist x⟩

end LipschitzAdd

section sub

variable [TopologicalSpace α]
variable {R : Type*} [PseudoMetricSpace R] [Sub R] [BoundedSub R] [ContinuousSub R]
variable (f g : α →ᵇ R)

/-- The pointwise difference of two bounded continuous functions is again bounded continuous. -/
/-
**BoundedContinuousFunction.instSub** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：instSub : Sub (α ->ᵇ R) where sub f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pointwise difference of two bounded continuous functions is again bounded co
ntinuous.
-/
instance instSub : Sub (α →ᵇ R) where
  sub f g :=
    { toFun := fun x ↦ (f x - g x),
      map_bounded' := sub_bounded_of_bounded_of_bounded f.map_bounded' g.map_bounded' }
/-
**BoundedContinuousFunction.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：sub_apply {x : α} : (f - g) x = f x - g x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply {x : α} : (f - g) x = f x - g x := rfl

@[simp]
/-
**BoundedContinuousFunction.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：coe_sub : ⇑(f - g) = f - g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub : ⇑(f - g) = f - g := rfl

end sub

section casts

variable [TopologicalSpace α] {β : Type*} [PseudoMetricSpace β]

/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NatCast β] : NatCast (α →ᵇ β) := ⟨fun n ↦ BoundedContinuousFunction.const _ n⟩

@[simp]
/-
**BoundedContinuousFunction.natCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：natCast_apply [NatCast β] (n : Nat) (x : α) : (n : α ->ᵇ β) x = n
参数：n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_apply [NatCast β] (n : ℕ) (x : α) : (n : α →ᵇ β) x = n := rfl
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IntCast β] : IntCast (α →ᵇ β) := ⟨fun m ↦ BoundedContinuousFunction.const _ m⟩

@[simp]
/-
**BoundedContinuousFunction.intCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：intCast_apply [IntCast β] (m : Int) (x : α) : (m : α ->ᵇ β) x = m
参数：m : Int；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_apply [IntCast β] (m : ℤ) (x : α) : (m : α →ᵇ β) x = m := rfl

end casts

/-
**BoundedContinuousFunction.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：instSemiring {R : Type*} [TopologicalSpace α] [PseudoMetricSpace R] [Semir
ing R] [BoundedMul R] [ContinuousMul R] [BoundedAdd R] [ContinuousAdd R] : Semir
ing (α ->ᵇ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring {R : Type*} [TopologicalSpace α] [PseudoMetricSpace R]
    [Semiring R] [BoundedMul R] [ContinuousMul R] [BoundedAdd R] [ContinuousAdd R] :
    Semiring (α →ᵇ R) := fast_instance%
  Injective.semiring _ DFunLike.coe_injective
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)

section IsBoundedSMul

/-!
### `IsBoundedSMul` (in particular, topological module) structure

In this section, if `β` is a metric space and a `𝕜`-module whose addition and scalar multiplication
are compatible with the metric structure, then we show that the space of bounded continuous
functions from `α` to `β` inherits a so-called `IsBoundedSMul` structure (in particular, a
`ContinuousMul` structure, which is the mathlib formulation of being a topological module), by
using pointwise operations and checking that they are compatible with the uniform distance. -/


variable {𝕜 : Type*} [PseudoMetricSpace 𝕜] [TopologicalSpace α] [PseudoMetricSpace β]

section SMul

variable [Zero 𝕜] [Zero β] [SMul 𝕜 β] [IsBoundedSMul 𝕜 β]

/-
**BoundedContinuousFunction.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：instSMul : SMul 𝕜 (α ->ᵇ β) where smul c f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul 𝕜 (α →ᵇ β) where
  smul c f :=
    { toContinuousMap := c • f.toContinuousMap
      map_bounded' :=
        let ⟨b, hb⟩ := f.bounded
        ⟨dist c 0 * b, fun x y => by
          refine (dist_smul_pair c (f x) (f y)).trans ?_
          gcongr
          apply hb⟩ }

@[simp]
/-
**BoundedContinuousFunction.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：coe_smul (c : 𝕜) (f : α ->ᵇ β) : ⇑(c • f) = fun x => c • f x
参数：c : 𝕜；f : α ->ᵇ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (c : 𝕜) (f : α →ᵇ β) : ⇑(c • f) = fun x => c • f x := rfl
/-
**BoundedContinuousFunction.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：smul_apply (c : 𝕜) (f : α ->ᵇ β) (x : α) : (c • f) x = c • f x
参数：c : 𝕜；f : α ->ᵇ β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (c : 𝕜) (f : α →ᵇ β) (x : α) : (c • f) x = c • f x := rfl
/-
**BoundedContinuousFunction.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：instIsScalarTower {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β
] [IsBoundedSMul 𝕜' β] [SMul 𝕜' 𝕜] [IsScalarTower 𝕜' 𝕜 β] : IsScalarTower 𝕜' 𝕜 (
α ->ᵇ β) where smul_assoc _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β]
    [IsBoundedSMul 𝕜' β] [SMul 𝕜' 𝕜] [IsScalarTower 𝕜' 𝕜 β] :
    IsScalarTower 𝕜' 𝕜 (α →ᵇ β) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc ..
/-
**BoundedContinuousFunction.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：instSMulCommClass {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β
] [IsBoundedSMul 𝕜' β] [SMulCommClass 𝕜' 𝕜 β] : SMulCommClass 𝕜' 𝕜 (α ->ᵇ β) whe
re smul_comm _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β]
    [IsBoundedSMul 𝕜' β] [SMulCommClass 𝕜' 𝕜 β] :
    SMulCommClass 𝕜' 𝕜 (α →ᵇ β) where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..
/-
**BoundedContinuousFunction.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：instIsCentralScalar [SMul 𝕜ᵐᵒᵖ β] [IsCentralScalar 𝕜 β] : IsCentralScalar 
𝕜 (α ->ᵇ β) where op_smul_eq_smul _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance instIsCentralScalar [SMul 𝕜ᵐᵒᵖ β] [IsCentralScalar 𝕜 β] : IsCentralScalar 𝕜 (α →ᵇ β) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _
/-
**BoundedContinuousFunction.instIsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：instIsBoundedSMul : IsBoundedSMul 𝕜 (α ->ᵇ β) where dist_smul_pair' c f₁ f
₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0
-/
instance instIsBoundedSMul : IsBoundedSMul 𝕜 (α →ᵇ β) where
  dist_smul_pair' c f₁ f₂ := by
    rw [dist_le (mul_nonneg dist_nonneg dist_nonneg)]
    intro x
    refine (dist_smul_pair c (f₁ x) (f₂ x)).trans ?_
    gcongr
    apply dist_coe_le_dist
  dist_pair_smul' c₁ c₂ f := by
    rw [dist_le (by positivity)]
    intro x
    refine (dist_pair_smul c₁ c₂ (f x)).trans ?_
    gcongr
    apply dist_coe_le_dist (g := 0)

end SMul

section MulAction

variable [MonoidWithZero 𝕜] [Zero β] [MulAction 𝕜 β] [IsBoundedSMul 𝕜 β]

/-
**BoundedContinuousFunction.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：instMulAction : MulAction 𝕜 (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction : MulAction 𝕜 (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.mulAction _ coe_smul

end MulAction

section DistribMulAction

variable [MonoidWithZero 𝕜] [AddMonoid β] [DistribMulAction 𝕜 β] [IsBoundedSMul 𝕜 β]
variable [BoundedAdd β] [ContinuousAdd β]

/-
**BoundedContinuousFunction.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Boun
dedContinuousFunction`。
形式化陈述：instDistribMulAction : DistribMulAction 𝕜 (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction : DistribMulAction 𝕜 (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

end DistribMulAction

section Module

variable [Semiring 𝕜] [AddCommMonoid β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
variable {f g : α →ᵇ β} {x : α} {C : ℝ}
variable [BoundedAdd β] [ContinuousAdd β]

/-
**BoundedContinuousFunction.instModule** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：instModule : Module 𝕜 (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule : Module 𝕜 (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.module _ ⟨⟨_, coe_zero⟩, coe_add⟩  coe_smul

variable (𝕜)

/-- The evaluation at a point, as a continuous linear map from `α →ᵇ β` to `β`. -/
@[simps]
/-
**BoundedContinuousFunction.evalCLM** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：evalCLM (x : α) : (α ->ᵇ β) ->L[𝕜] β where toFun f
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation at a point, as a continuous linear map from `α →ᵇ β` to `β`.
-/
def evalCLM (x : α) : (α →ᵇ β) →L[𝕜] β where
  toFun f := f x
  map_add' _ _ := add_apply _ _ _
  map_smul' _ _ := smul_apply _ _ _

variable (α β)

/-- The linear map forgetting that a bounded continuous function is bounded. -/
@[simps]
/-
**BoundedContinuousFunction.toContinuousMapLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `
BoundedContinuousFunction`。
形式化陈述：toContinuousMapLinearMap : (α ->ᵇ β) ->ₗ[𝕜] C(α, β) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map forgetting that a bounded continuous function is bounded.
-/
def toContinuousMapLinearMap : (α →ᵇ β) →ₗ[𝕜] C(α, β) where
  toFun := toContinuousMap
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

end Module

end IsBoundedSMul

/-
**BoundedContinuousFunction.NNReal.upper_bound** 是 Mathlib 中的一个定理，位于命名空间 `Bounde
dContinuousFunction.NNReal`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (f : BoundedContinuousFunctio
n α NNReal) (x : α), f x ≤ nndist f 0
参数：f : BoundedContinuousFunction α NNReal；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.nndist_zero_eq_val'`：NNReal.nndist_zero_eq_val' (z : Real>=0) : n
ndist z 0 = z
-/
theorem NNReal.upper_bound {α : Type*} [TopologicalSpace α] (f : α →ᵇ ℝ≥0) (x : α) :
    f x ≤ nndist f 0 := by
  have key : nndist (f x) ((0 : α →ᵇ ℝ≥0) x) ≤ nndist f 0 := @dist_coe_le_dist α ℝ≥0 _ _ f 0 x
  simp only [coe_zero, Pi.zero_apply] at key
  rwa [NNReal.nndist_zero_eq_val' (f x)] at key

end BoundedContinuousFunction

