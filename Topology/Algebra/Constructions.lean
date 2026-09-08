/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological space structure on the opposite monoid and on the units group

In this file we define `TopologicalSpace` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `AddUnits M`.
This file does not import definitions of a topological monoid and/or a continuous multiplicative
action, so we postpone the proofs of `ContinuousMul Mᵐᵒᵖ` etc. till we have these definitions.

## Tags

topological space, opposite monoid, units
-/

@[expose] public section


variable {M N X : Type*}

open Filter Topology

namespace MulOpposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
@[to_additive /-- Put the same topological space structure on the opposite monoid as on the original
space. -/]
/-
**MulOpposite.instTopologicalSpaceMulOpposite** 是 Mathlib 中的一个实例，位于命名空间 `MulOppo
site`。
形式化陈述：instTopologicalSpaceMulOpposite [TopologicalSpace M] : TopologicalSpace Mᵐ
ᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpaceMulOpposite [TopologicalSpace M] : TopologicalSpace Mᵐᵒᵖ :=
  TopologicalSpace.induced (unop : Mᵐᵒᵖ → M) ‹_›

variable [TopologicalSpace M]

@[to_additive (attr := continuity, fun_prop)]
/-
**MulOpposite.continuous_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：continuous_unop : Continuous (unop : Mᵐᵒᵖ -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem continuous_unop : Continuous (unop : Mᵐᵒᵖ → M) :=
  continuous_induced_dom

@[to_additive (attr := continuity, fun_prop)]
/-
**MulOpposite.continuous_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：continuous_op : Continuous (op : M -> Mᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_op : Continuous (op : M → Mᵐᵒᵖ) :=
  continuous_induced_rng.2 continuous_id

/-- `MulOpposite.op` as a homeomorphism. -/
@[to_additive (attr := simps!) /-- `AddOpposite.op` as a homeomorphism. -/]
/-
**MulOpposite.opHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：opHomeomorph : M ≃ₜ Mᵐᵒᵖ where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulOpposite.op` as a homeomorphism.
-/
def opHomeomorph : M ≃ₜ Mᵐᵒᵖ where
  toEquiv := opEquiv

@[to_additive]
/-
**MulOpposite.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instT2Space [T2Space M] : T2Space Mᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t2Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y),   T2Space Y
-/
instance instT2Space [T2Space M] : T2Space Mᵐᵒᵖ := opHomeomorph.t2Space

@[to_additive]
/-
**MulOpposite.instDiscreteTopology** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [Discrete
Topology Y], Topology.IsEmb…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
instance instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mᵐᵒᵖ :=
  opHomeomorph.symm.isEmbedding.discreteTopology

@[to_additive]
/-
**MulOpposite.instCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instCompactSpace [CompactSpace M] : CompactSpace Mᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.compactSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] (h : X ≃ₜ Y),   Comp
actSpace Y
-/
instance instCompactSpace [CompactSpace M] : CompactSpace Mᵐᵒᵖ :=
  opHomeomorph.compactSpace

@[to_additive]
/-
**MulOpposite.instWeaklyLocallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposi
te`。
形式化陈述：instWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace M] : WeaklyLocall
yCompactSpace Mᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.weaklyLocallyCompactSpace`：∀ {X : Type u_1} {
Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [WeaklyL
ocallyCompactSpace Y]   {f : X → Y}, Topol…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
instance instWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace M] :
    WeaklyLocallyCompactSpace Mᵐᵒᵖ :=
  opHomeomorph.symm.isClosedEmbedding.weaklyLocallyCompactSpace

@[to_additive]
/-
**MulOpposite.instLocallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instLocallyCompactSpace [LocallyCompactSpace M] : LocallyCompactSpace Mᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.locallyCompactSpace`：∀ {X : Type u_1} {Y : Ty
pe u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompac
tSpace Y]   {f : X → Y}, Topology.Is…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
instance instLocallyCompactSpace [LocallyCompactSpace M] :
    LocallyCompactSpace Mᵐᵒᵖ :=
  opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace

@[to_additive (attr := simp)]
/-
**MulOpposite.map_op_nhds** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：map_op_nhds (x : M) : map (op : M -> Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
theorem map_op_nhds (x : M) : map (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.map_nhds_eq x

@[to_additive (attr := simp)]
/-
**MulOpposite.map_unop_nhds** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：map_unop_nhds (x : Mᵐᵒᵖ) : map (unop : Mᵐᵒᵖ -> M) (𝓝 x) = 𝓝 (unop x)
参数：x : Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
theorem map_unop_nhds (x : Mᵐᵒᵖ) : map (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]
/-
**MulOpposite.comap_op_nhds** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：comap_op_nhds (x : Mᵐᵒᵖ) : comap (op : M -> Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x)
参数：x : Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comap_nhds_eq`：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (
𝓝 y) = 𝓝 (h.symm y)
-/
theorem comap_op_nhds (x : Mᵐᵒᵖ) : comap (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]
/-
**MulOpposite.comap_unop_nhds** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：comap_unop_nhds (x : M) : comap (unop : Mᵐᵒᵖ -> M) (𝓝 x) = 𝓝 (op x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comap_nhds_eq`：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (
𝓝 y) = 𝓝 (h.symm y)
-/
theorem comap_unop_nhds (x : M) : comap (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.symm.comap_nhds_eq x

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace M] [Monoid M] [TopologicalSpace N] [Monoid N] [TopologicalSpace X]

/-- The units of a monoid are equipped with a topology, via the embedding into `M × M`. -/
@[to_additive
/-- The additive units of a monoid are equipped with a topology, via the embedding into `M × M`. -/]
/-
**Units.instTopologicalSpaceUnits** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instTopologicalSpaceUnits : TopologicalSpace Mˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpaceUnits : TopologicalSpace Mˣ :=
  TopologicalSpace.induced (embedProduct M) inferInstance

@[to_additive]
/-
**Units.isInducing_embedProduct** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：isInducing_embedProduct : IsInducing (embedProduct M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInducing_embedProduct : IsInducing (embedProduct M) := ⟨rfl⟩

@[to_additive]
/-
**Units.isEmbedding_embedProduct** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：isEmbedding_embedProduct : IsEmbedding (embedProduct M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isInducing_embedProduct`：isInducing_embedProduct : IsInducing (emb
edProduct M)
· 使用定理 `Units.embedProduct_injective`：embedProduct_injective (α : Type*) [Monoid
 α] : Function.Injective (embedProduct α)
-/
theorem isEmbedding_embedProduct : IsEmbedding (embedProduct M) :=
  ⟨isInducing_embedProduct, embedProduct_injective M⟩

@[to_additive]
/-
**Units.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instT2Space [T2Space M] : T2Space Mˣ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t2Space`：Topology.IsEmbedding.t2Space [TopologicalS
pace Y] [T2Space Y] {f : X -> Y} (hf : IsEmbedding f) : T2Space X
· 使用定理 `Units.isEmbedding_embedProduct`：isEmbedding_embedProduct : IsEmbedding (
embedProduct M)
-/
instance instT2Space [T2Space M] : T2Space Mˣ := isEmbedding_embedProduct.t2Space

@[to_additive]
/-
**Units.instDiscreteTopology** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mˣ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [Discrete
Topology Y], Topology.IsEmb…
· 使用定理 `instDiscreteTopologyProd`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   [DiscreteTopology
 Y], DiscreteT…
· 使用定理 `Units.isEmbedding_embedProduct`：isEmbedding_embedProduct : IsEmbedding (
embedProduct M)
-/
instance instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mˣ :=
  isEmbedding_embedProduct.discreteTopology
/-
**Units.topology_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : Monoid M],   Units.
instTopologicalSpaceUnits =     TopologicalSpace.induced Units.val inst ⊓ Topolo
gicalSpace.induced (fun u => ↑u⁻¹) inst
参数：fun u => ↑u⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `Units.isInducing_embedProduct`：isInducing_embedProduct : IsInducing (emb
edProduct M)
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
@[to_additive] lemma topology_eq_inf :
    instTopologicalSpaceUnits =
      .induced (val : Mˣ → M) ‹_› ⊓ .induced (fun u ↦ ↑u⁻¹ : Mˣ → M) ‹_› := by
  simp only [isInducing_embedProduct.1, instTopologicalSpaceProd, induced_inf,
    instTopologicalSpaceMulOpposite, induced_compose]; rfl

/-- An auxiliary lemma that can be used to prove that coercion `Mˣ → M` is a topological embedding.
Use `Units.isEmbedding_val₀`, `Units.isEmbedding_val`, or `toUnits_homeomorph` instead. -/
@[to_additive /-- An auxiliary lemma that can be used to prove that coercion `AddUnits M → M` is a
topological embedding. Use `AddUnits.isEmbedding_val` or `toAddUnits_homeomorph` instead. -/]
/-
**Units.isEmbedding_val_mk'** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：isEmbedding_val_mk' {M : Type*} [Monoid M] [TopologicalSpace M] {f : M -> 
M} (hc : ContinuousOn f {x : M | IsUnit x}) (hf : forall u : Mˣ, f u.1 = ↑u⁻¹) :
 IsEmbedding (val : Mˣ -> M)
参数：hc : ContinuousOn f {x : M | IsUnit x}；hf : forall u : Mˣ, f u.1 = ↑u⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.topology_eq_inf`：∀ {M : Type u_1} [inst : TopologicalSpace M] [ins
t_1 : Monoid M],   Units.instTopologicalSpaceUnits =     TopologicalSpace.induce
d Units.val…
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.mem_inf_principal`：mem_inf_principal {f : Filter α} {s t : Set α}
 : s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
-/
lemma isEmbedding_val_mk' {M : Type*} [Monoid M] [TopologicalSpace M] {f : M → M}
    (hc : ContinuousOn f {x : M | IsUnit x}) (hf : ∀ u : Mˣ, f u.1 = ↑u⁻¹) :
    IsEmbedding (val : Mˣ → M) := by
  refine ⟨⟨?_⟩, val_injective⟩
  rw [topology_eq_inf, inf_eq_left, ← continuous_iff_le_induced,
    @continuous_iff_continuousAt _ _ (.induced _ _)]
  intro u s hs
  simp only [← hf, nhds_induced, Filter.mem_map] at hs ⊢
  exact ⟨_, mem_inf_principal.1 (hc u u.isUnit hs), fun u' hu' ↦ hu' u'.isUnit⟩

/-- An auxiliary lemma that can be used to prove that coercion `Mˣ → M` is a topological embedding.
Use `Units.isEmbedding_val₀`, `Units.isEmbedding_val`, or `toUnits_homeomorph` instead. -/
@[to_additive /-- An auxiliary lemma that can be used to prove that coercion `AddUnits M → M` is a
topological embedding. Use `AddUnits.isEmbedding_val` or `toAddUnits_homeomorph` instead. -/]
/-
**Units.embedding_val_mk** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：embedding_val_mk {M : Type*} [DivisionMonoid M] [TopologicalSpace M] (h : 
ContinuousOn Inv.inv {x : M | IsUnit x}) : IsEmbedding (val : Mˣ -> M)
参数：h : ContinuousOn Inv.inv {x : M | IsUnit x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Units.isEmbedding_val_mk'`：isEmbedding_val_mk' {M : Type*} [Monoid M] [T
opologicalSpace M] {f : M -> M} (hc : ContinuousOn f {x : M | IsUnit x}) (hf : f
orall u : Mˣ, f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
-/
lemma embedding_val_mk {M : Type*} [DivisionMonoid M] [TopologicalSpace M]
    (h : ContinuousOn Inv.inv {x : M | IsUnit x}) : IsEmbedding (val : Mˣ → M) :=
  isEmbedding_val_mk' h fun u ↦ (val_inv_eq_inv_val u).symm

@[to_additive]
/-
**Units.continuous_embedProduct** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：continuous_embedProduct : Continuous (embedProduct M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem continuous_embedProduct : Continuous (embedProduct M) :=
  continuous_induced_dom

@[to_additive (attr := fun_prop)]
/-
**Units.continuous_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：continuous_val : Continuous ((↑) : Mˣ -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `Units.continuous_embedProduct`：continuous_embedProduct : Continuous (emb
edProduct M)
-/
theorem continuous_val : Continuous ((↑) : Mˣ → M) :=
  (@continuous_embedProduct M _ _).fst

@[to_additive]
/-
**Units.continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {M : Type u_1} {X : Type u_3} [inst : TopologicalSpace M] [inst_1 : Mono
id M] [inst_2 : TopologicalSpace X]   {f : X → Mˣ}, Continuous f ↔ Continuous (U
nits.val ∘ f) ∧ Continuous fun x => ↑(f x)⁻¹
参数：Units.val ∘ f；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `Units.isInducing_embedProduct`：isInducing_embedProduct : IsInducing (emb
edProduct M)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Units.embedProduct_apply`：∀ (α : Type u_6) [inst : Monoid α] (x : αˣ), (
Units.embedProduct α) x = (↑x, MulOpposite.op ↑x⁻¹)
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `MulOpposite.opHomeomorph_symm_apply`：∀ {M : Type u_1} [inst : Topologica
lSpace M] (a : Mᵐᵒᵖ), MulOpposite.opHomeomorph.symm a = MulOpposite.unop a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem continuous_iff {f : X → Mˣ} :
    Continuous f ↔ Continuous (val ∘ f) ∧ Continuous (fun x => ↑(f x)⁻¹ : X → M) := by
  simp only [isInducing_embedProduct.continuous_iff, embedProduct_apply, Function.comp_def,
    continuous_prodMk, opHomeomorph.symm.isInducing.continuous_iff, opHomeomorph_symm_apply,
    unop_op]

@[to_additive (attr := fun_prop)]
/-
**Units.continuous_coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：continuous_coe_inv : Continuous (fun u => ↑u⁻¹ : Mˣ -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.continuous_iff`：∀ {M : Type u_1} {X : Type u_3} [inst : Topologica
lSpace M] [inst_1 : Monoid M] [inst_2 : TopologicalSpace X]   {f : X → Mˣ}, Cont
inuous f ↔…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_coe_inv : Continuous (fun u => ↑u⁻¹ : Mˣ → M) :=
  (Units.continuous_iff.1 continuous_id).2

@[to_additive]
/-
**Units.continuous_map** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：continuous_map {f : M ->* N} (hf : Continuous f) : Continuous (map f)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Units.continuous_iff`：∀ {M : Type u_1} {X : Type u_3} [inst : Topologica
lSpace M] [inst_1 : Monoid M] [inst_2 : TopologicalSpace X]   {f : X → Mˣ}, Cont
inuous f ↔…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Units.continuous_val`：continuous_val : Continuous ((↑) : Mˣ -> M)
· 使用定理 `Units.continuous_coe_inv`：continuous_coe_inv : Continuous (fun u => ↑u⁻¹
 : Mˣ -> M)
-/
lemma continuous_map {f : M →* N} (hf : Continuous f) : Continuous (map f) :=
  Units.continuous_iff.mpr ⟨hf.comp continuous_val, hf.comp continuous_coe_inv⟩

@[to_additive]
/-
**Units.isOpenMap_map** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：isOpenMap_map {f : M ->* N} (hf_inj : Function.Injective f) (hf : IsOpenMa
p f) : IsOpenMap (map f)
参数：hf_inj : Function.Injective f；hf : IsOpenMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.prodMap`：∀ {X : Type u} {Y : Type v} {W : Type u_1} {Z : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : Topol
ogicalS…
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulOpposite.opHomeomorph_symm_apply`：∀ {M : Type u_1} [inst : Topologica
lSpace M] (a : Mᵐᵒᵖ), MulOpposite.opHomeomorph.symm a = MulOpposite.unop a
· 使用定理 `MulOpposite.opHomeomorph_apply`：∀ {M : Type u_1} [inst : TopologicalSpac
e M] (a : M), MulOpposite.opHomeomorph a = MulOpposite.op a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Units.mk.congr_simp`：∀ {α : Type u} [inst : Monoid α] (val val_1 : α) (e
_val : val = val_1) (inv inv_1 : α) (e_inv : inv = inv_1)   (val_inv : val * inv
 = 1) (in…
· 使用定理 `Units.mk_val`：mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isOpenMap_map {f : M →* N} (hf_inj : Function.Injective f) (hf : IsOpenMap f) :
    IsOpenMap (map f) := by
  rintro _ ⟨U, hU, rfl⟩
  have hg_openMap := hf.prodMap <| opHomeomorph.isOpenMap.comp (hf.comp opHomeomorph.symm.isOpenMap)
  refine ⟨_, hg_openMap U hU, Set.ext fun y ↦ ?_⟩
  simp only [embedProduct, OneHom.coe_mk, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
    Prod.map, Prod.exists, MulOpposite.exists, MonoidHom.coe_mk]
  refine ⟨fun ⟨a, b, h, ha, hb⟩ ↦ ⟨⟨a, b, hf_inj ?_, hf_inj ?_⟩, ?_⟩,
    fun ⟨x, hxV, hx⟩ ↦ ⟨x, x.inv, by simp [hxV, ← hx]⟩⟩
  all_goals simp_all

@[to_additive]
/-
**Units._root_.Topology.IsInducing.units_map** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsInducing.units_map {f : M →* N} (hf : IsInducing f) :
    IsInducing (map f) := by
  refine .of_comp (continuous_map hf.continuous) continuous_embedProduct ?_
  exact hf.prodMap (opHomeomorph.isInducing.comp <| hf.comp opHomeomorph.symm.isInducing)
    |>.comp isInducing_embedProduct

@[to_additive]
/-
**Units._root_.Topology.IsEmbedding.units_map** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsEmbedding.units_map {f : M →* N} (hf : IsEmbedding f) :
    IsEmbedding (map f) := by
  refine .of_comp (continuous_map hf.continuous) continuous_embedProduct ?_
  exact hf.prodMap (opHomeomorph.isEmbedding.comp <| hf.comp opHomeomorph.symm.isEmbedding)
    |>.comp isEmbedding_embedProduct

end Units

