/-
Copyright (c) 2022 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
module

public import Mathlib.Topology.Order
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Any T0 space embeds in a product of copies of the Sierpinski space.

We consider `Prop` with the Sierpinski topology. If `X` is a topological space, there is a
continuous map `productOfMemOpens` from `X` to `Opens X → Prop` which is the product of the maps
`X → Prop` given by `x ↦ x ∈ u`.

The map `productOfMemOpens` is always inducing. Whenever `X` is T0, `productOfMemOpens` is
also injective and therefore an embedding.
-/

@[expose] public section

open Topology

noncomputable section

namespace TopologicalSpace

/-
**TopologicalSpace.eq_induced_by_maps_to_sierpinski** 是 Mathlib 中的一个定理，位于命名空间 `T
opologicalSpace`。
形式化陈述：eq_induced_by_maps_to_sierpinski (X : Type*) [t : TopologicalSpace X] : t 
= ⨅ u : Opens X, sierpinskiSpace.induced (· in u)
参数：X : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `Continuous.le_induced`：Continuous.le_induced (h : Continuous[t, t'] f) :
 t <= t'.induced f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_iff_continuous_mem`：isOpen_iff_continuous_mem {s : Set α} : IsOpe
n s ↔ Continuous (· in s)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `generateFrom_iUnion_isOpen`：generateFrom_iUnion_isOpen (f : ι -> Topolog
icalSpace α) : generateFrom (⋃ i, { s | IsOpen[f i] s }) = ⨅ i, f i
· 使用定理 `TopologicalSpace.isOpen_generateFrom_of_mem`：isOpen_generateFrom_of_mem 
{g : Set (Set α)} {s : Set α} (hs : s in g) : IsOpen[generateFrom g] s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isOpen_singleton_true`：isOpen_singleton_true : IsOpen ({True} : Set Prop
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_induced_by_maps_to_sierpinski (X : Type*) [t : TopologicalSpace X] :
    t = ⨅ u : Opens X, sierpinskiSpace.induced (· ∈ u) := by
  apply le_antisymm
  · rw [le_iInf_iff]
    exact fun u => Continuous.le_induced (isOpen_iff_continuous_mem.mp u.2)
  · intro u h
    rw [← generateFrom_iUnion_isOpen]
    apply isOpen_generateFrom_of_mem
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, isOpen_induced_iff]
    exact ⟨⟨u, h⟩, {True}, isOpen_singleton_true, by simp [Set.preimage]⟩

variable (X : Type*) [TopologicalSpace X]

/-- The continuous map from `X` to the product of copies of the Sierpinski space, (one copy for each
open subset `u` of `X`). The `u` coordinate of `productOfMemOpens x` is given by `x ∈ u`.
-/
/-
**TopologicalSpace.productOfMemOpens** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace
`。
形式化陈述：productOfMemOpens : C(X, Opens X -> Prop) where toFun x u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous map from `X` to the product of copies of the Sierpinski space, (o
ne copy for each
open subset `u` of `X`). The `u` coordinate of `productOfMemOpens x` is given by
 `x ∈ u`.
-/
def productOfMemOpens : C(X, Opens X → Prop) where
  toFun x u := x ∈ u
  continuous_toFun := continuous_pi_iff.2 fun u => continuous_Prop.2 u.isOpen
/-
**TopologicalSpace.productOfMemOpens_isInducing** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace`。
形式化陈述：productOfMemOpens_isInducing : IsInducing (productOfMemOpens X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.eq_induced_by_maps_to_sierpinski`：eq_induced_by_maps_to
_sierpinski (X : Type*) [t : TopologicalSpace X] : t = ⨅ u : Opens X, sierpinski
Space.induced (· in u)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inducing_iInf_to_pi`：inducing_iInf_to_pi {X : Type*} (f : forall i, X ->
 A i) : @IsInducing X (forall i, A i) (⨅ i, induced (f i) inferInstance) _ fun x
 i => f i…
-/
theorem productOfMemOpens_isInducing : IsInducing (productOfMemOpens X) := by
  convert! inducing_iInf_to_pi fun (u : Opens X) (x : X) => x ∈ u
  apply eq_induced_by_maps_to_sierpinski
/-
**TopologicalSpace.productOfMemOpens_injective** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace`。
形式化陈述：productOfMemOpens_injective [T0Space X] : Function.Injective (productOfMem
Opens X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.inseparable_iff`：Topology.IsInducing.inseparable_iff
 (hf : IsInducing f) : (f x ~ᵢ f y) ↔ (x ~ᵢ y)
· 使用定理 `TopologicalSpace.productOfMemOpens_isInducing`：productOfMemOpens_isInduc
ing : IsInducing (productOfMemOpens X)
· 使用定理 `Inseparable.refl`：refl (x : X) : x ~ᵢ x
-/
theorem productOfMemOpens_injective [T0Space X] : Function.Injective (productOfMemOpens X) := by
  intro x1 x2 h
  apply Inseparable.eq
  rw [← IsInducing.inseparable_iff (productOfMemOpens_isInducing X), h]
/-
**TopologicalSpace.productOfMemOpens_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace`。
形式化陈述：productOfMemOpens_isEmbedding [T0Space X] : IsEmbedding (productOfMemOpens
 X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.productOfMemOpens_isInducing`：productOfMemOpens_isInduc
ing : IsInducing (productOfMemOpens X)
· 使用定理 `TopologicalSpace.productOfMemOpens_injective`：productOfMemOpens_injectiv
e [T0Space X] : Function.Injective (productOfMemOpens X)
-/
theorem productOfMemOpens_isEmbedding [T0Space X] : IsEmbedding (productOfMemOpens X) :=
  .mk (productOfMemOpens_isInducing X) (productOfMemOpens_injective X)

end TopologicalSpace

