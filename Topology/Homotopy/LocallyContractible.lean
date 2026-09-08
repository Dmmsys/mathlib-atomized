/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Strongly locally contractible spaces

This file defines `LocallyContractibleSpace` and `StronglyLocallyContractibleSpace`.

## Main definitions

* `LocallyContractibleSpace X`: classical local contractibility (null-homotopic inclusions).
* `StronglyLocallyContractibleSpace X`: a space where each point has a neighborhood basis
  consisting of contractible sets (not necessarily open).

## Main results

* `StronglyLocallyContractibleSpace.locallyContractible`: SLC implies classical LC
* `instLocallyPathConnectedSpace`: strongly locally contractible spaces are locally path-connected
* `StronglyLocallyContractibleSpace.of_bases`: a helper to construct strongly locally contractible
  spaces from a neighborhood basis
* `contractible_subset_basis`: basis of contractible neighborhoods contained in an open set
* `IsOpenEmbedding.stronglyLocallyContractibleSpace`: open embeddings preserve strong local
  contractibility
* `IsOpen.stronglyLocallyContractibleSpace`: open subsets of strongly locally contractible spaces
  are strongly locally contractible
* Products of strongly locally contractible spaces are strongly locally contractible

## TODO

* Define contractible components and prove they are open in strongly locally contractible spaces
* Add examples: convex sets, real vector spaces, star-shaped sets

## Notes

**Terminology:** The classical definition of *locally contractible* (LC) requires that for every
point `x` and neighborhood `U ∋ x`, there exists a neighborhood `V ∋ x` with `V ⊆ U` such that the
inclusion `V ↪ U` is null-homotopic. The definition here is **strictly stronger**: we require
contractible neighborhoods to form a neighborhood basis. This is often called **strongly locally
contractible** (SLC).

**Hierarchy of notions:**
* "Basis of open contractible neighborhoods" (strongest)
* "Basis of contractible neighborhoods" (this file, SLC)
* "Null-homotopic inclusions" (classical LC, weakest)

This naming is not used uniformly: according to
https://ncatlab.org/nlab/show/locally+contractible+space
the second and third notion here could also be called
"locally contractible" and "semilocally contractible" respectively.
We've enquired at
https://math.stackexchange.com/questions/5109428/terminology-for-local-contractibility-locally-contractible-vs-strongly-local
in the hope of getting definitive naming advice.

The Borsuk-Mazurkiewicz counterexample [borsuk_mazurkiewicz1934] shows that classical LC does not
imply SLC. Moreover, from a contractible neighborhood `S` one generally cannot shrink to an open
`V ⊆ S` that remains contractible, so requiring neighborhoods to be open is potentially strictly
stronger than SLC.
-/

@[expose] public section

noncomputable section

open Topology Filter Set Function ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X} {ι : Type*}

section LocallyContractible

/-- Classical **local contractibility**: for every point and every neighborhood U,
there exists a neighborhood V ⊆ U such that the inclusion V ↪ U is null-homotopic.

This is weaker than `StronglyLocallyContractibleSpace`. -/
/-
**LocallyContractibleSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyContractibleSpace (X : Type*) [TopologicalSpace X] : Prop
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Classical **local contractibility**: for every point and every neighborhood U,
there exists a neighborhood V ⊆ U such that the inclusion V ↪ U is null-homotopi
c.

This is weaker than `StronglyLocallyContractibleSpace`.
-/
def LocallyContractibleSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (U : Set X), U ∈ 𝓝 x →
    ∃ (V : Set X) (hVU : V ⊆ U), V ∈ 𝓝 x ∧ Nullhomotopic (inclusion hVU)

end LocallyContractible

section StronglyLocallyContractibleSpace

/-- A topological space is **strongly locally contractible** if, at every point, contractible
neighborhoods form a neighborhood basis. Here "contractible" means contractible as a subspace.

This is strictly stronger than the classical notion of locally contractible, which only requires
null-homotopic inclusions.
This distinction is witnessed by an example from Borsuk-Mazurkiewicz [borsuk_mazurkiewicz1934];
see also [MO88628] for discussion and the Whitehead manifold example. -/
/-
**StronglyLocallyContractibleSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_4) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is **strongly locally contractible** if, at every point, con
tractible
neighborhoods form a neighborhood basis. Here "contractible" means contractible 
as a subspace.

This is strictly stronger than the classical notion of locally contractible, whi
ch only requires
null-homotopic inclusions.
This distinction is witnessed by an example from Borsuk-Mazurkiewicz [borsuk_maz
urkiewicz1934];
see also [MO88628] for discussion and the Whitehead manifold example.
-/
class StronglyLocallyContractibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of contractible subspace neighborhoods. -/
  contractible_basis : ∀ x : X,
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ ContractibleSpace s) id

export StronglyLocallyContractibleSpace (contractible_basis)

/-- A helper to construct a strongly locally contractible space from a neighborhood basis where
each basis element is contractible as a subspace. -/
/-
**StronglyLocallyContractibleSpace.of_bases** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StronglyLocallyContractibleSpace.of_bases {p : X -> ι -> Prop} {s : X -> ι
 -> Set X} (h : forall x, (𝓝 x).HasBasis (p x) (s x)) (h' : forall x i, p x i ->
 ContractibleSpace (s x i)) : StronglyLocallyContractibleSpace X where contracti
ble_basis x
参数：h : forall x, (𝓝 x).HasBasis (p x) (s x)；h' : forall x i, p x i -> Contractib
leSpace (s x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l

--- 原说明 ---
A helper to construct a strongly locally contractible space from a neighborhood 
basis where
each basis element is contractible as a subspace.
-/
theorem StronglyLocallyContractibleSpace.of_bases {p : X → ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis (p x) (s x)) (h' : ∀ x i, p x i → ContractibleSpace (s x i)) :
    StronglyLocallyContractibleSpace X where
  contractible_basis x := by
    rw [hasBasis_self]
    intro t ht
    obtain ⟨i, hpi, hi⟩ := (h x).mem_iff.mp ht
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

variable [StronglyLocallyContractibleSpace X]

/-- In a strongly locally contractible space, for any open set `U` containing `x`, there is a basis
of contractible neighborhoods of `x` contained in `U`. -/
/-
**contractible_subset_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contractible_subset_basis {U : Set X} (h : IsOpen U) (hx : x in U) : (𝓝 x)
.HasBasis (fun s : Set X => s in 𝓝 x ∧ ContractibleSpace s ∧ s subseteq U) id
参数：h : IsOpen U；hx : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.hasBasis_self_subset`：∀ {α : Type u_1} {l : Filter α} {p
 : Set α → Prop},   l.HasBasis (fun s => s ∈ l ∧ p s) id → ∀ {V : Set α}, V ∈ l 
→ l.HasBasis (fun s => s ∈…
· 使用定理 `StronglyLocallyContractibleSpace.contractible_basis`：∀ {X : Type u_4} {i
nst : TopologicalSpace X} [self : StronglyLocallyContractibleSpace X] (x : X),  
 (nhds x).HasBasis (fun s => s ∈ nhds x ∧…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
In a strongly locally contractible space, for any open set `U` containing `x`, t
here is a basis
of contractible neighborhoods of `x` contained in `U`.
-/
theorem contractible_subset_basis {U : Set X} (h : IsOpen U) (hx : x ∈ U) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ ContractibleSpace s ∧ s ⊆ U) id :=
  (contractible_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

/-- Strongly locally contractible spaces are locally path-connected. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strongly locally contractible spaces are locally path-connected.
-/
instance (priority := 100) instLocallyPathConnectedSpace : LocallyPathConnectedSpace X where
  path_connected_basis x := by
    refine contractible_basis x |>.to_hasBasis'
      (fun s ⟨hs, hs'⟩ ↦ ⟨s, ⟨hs, ?_⟩, le_rfl⟩) (fun s hs ↦ hs.1)
    rw [isPathConnected_iff_pathConnectedSpace]
    infer_instance

/-- Open embeddings preserve strong local contractibility: if `X` is strongly locally contractible
and `e : Y → X` is an open embedding, then `Y` is strongly locally contractible. -/
/-
**Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace {e : Y -> X} (he
 : IsOpenEmbedding e) : StronglyLocallyContractibleSpace Y
参数：he : IsOpenEmbedding e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StronglyLocallyContractibleSpace.of_bases`：StronglyLocallyContractibleSp
ace.of_bases {p : X -> ι -> Prop} {s : X -> ι -> Set X} (h : forall x, (𝓝 x).Has
Basis (p x) (s x)) (h' : forall…
· 使用引理 `Topology.IsInducing.basis_nhds`：basis_nhds {p : ι -> Prop} {s : ι -> Set
 Y} (hf : IsInducing f) {x : X} (h_basis : (𝓝 (f x)).HasBasis p s) : (𝓝 x).HasBa
sis p (preimage f ∘ …
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `contractible_subset_basis`：contractible_subset_basis {U : Set X} (h : Is
Open U) (hx : x in U) : (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ Contractible
Space s ∧ s sub…
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.contractibleSpace_iff`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   Contractible
Space X ↔ Contractible…

--- 原说明 ---
Open embeddings preserve strong local contractibility: if `X` is strongly locall
y contractible
and `e : Y → X` is an open embedding, then `Y` is strongly locally contractible.
-/
theorem Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace {e : Y → X}
    (he : IsOpenEmbedding e) : StronglyLocallyContractibleSpace Y :=
  .of_bases
    (fun _ ↦ he.basis_nhds <| contractible_subset_basis he.isOpen_range (mem_range_self _))
    fun _ _ ⟨_, hs, hse⟩ ↦
      (he.toIsEmbedding.homeomorphOfSubsetRange hse).contractibleSpace_iff.mpr hs

/-- Open subsets of strongly locally contractible spaces are strongly locally contractible. -/
/-
**IsOpen.stronglyLocallyContractibleSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.stronglyLocallyContractibleSpace {U : Set X} (h : IsOpen U) : Stron
glyLocallyContractibleSpace U
参数：h : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace`：Topology.IsOp
enEmbedding.stronglyLocallyContractibleSpace {e : Y -> X} (he : IsOpenEmbedding 
e) : StronglyLocallyContractibleSpace Y
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)

--- 原说明 ---
Open subsets of strongly locally contractible spaces are strongly locally contra
ctible.
-/
theorem IsOpen.stronglyLocallyContractibleSpace {U : Set X} (h : IsOpen U) :
    StronglyLocallyContractibleSpace U :=
  h.isOpenEmbedding_subtypeVal.stronglyLocallyContractibleSpace

end StronglyLocallyContractibleSpace

section Products

/-- The product of two strongly locally contractible spaces is strongly locally contractible. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two strongly locally contractible spaces is strongly locally cont
ractible.
-/
instance [StronglyLocallyContractibleSpace X] [StronglyLocallyContractibleSpace Y] :
    StronglyLocallyContractibleSpace (X × Y) := by
  refine .of_bases (ι := Set X × Set Y)
    (p := fun (x, y) (Ux, Uy) =>
      (Ux ∈ 𝓝 x ∧ ContractibleSpace Ux) ∧ (Uy ∈ 𝓝 y ∧ ContractibleSpace Uy))
    (s := fun _ (Ux, Uy) => Ux ×ˢ Uy) ?_ ?_
  · intro (x, y)
    rw [nhds_prod_eq]
    exact (contractible_basis x).prod (contractible_basis y)
  · intro (x, y) (Ux, Uy) ⟨hUx, hUy⟩
    have : ContractibleSpace Ux := hUx.2
    have : ContractibleSpace Uy := hUy.2
    exact (Homeomorph.Set.prod Ux Uy).contractibleSpace

end Products

section Implications

/-- The strong notion (contractible neighborhood basis)
implies the classical notion (null-homotopic inclusions).
The converse is false by the Borsuk-Mazurkiewicz counterexample [borsuk_mazurkiewicz1934];
see also [MO88628] for discussion and the Whitehead manifold example. -/
/-
**StronglyLocallyContractibleSpace.locallyContractible** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：StronglyLocallyContractibleSpace.locallyContractible [StronglyLocallyContr
actibleSpace X] : LocallyContractibleSpace X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `StronglyLocallyContractibleSpace.contractible_basis`：∀ {X : Type u_4} {i
nst : TopologicalSpace X} [self : StronglyLocallyContractibleSpace X] (x : X),  
 (nhds x).HasBasis (fun s => s ∈ nhds x ∧…
· 使用定理 `id_nullhomotopic`：id_nullhomotopic (X : Type*) [TopologicalSpace X] [Con
tractibleSpace X] : (ContinuousMap.id X).Nullhomotopic
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousMap.comp_id`：comp_id (f : C(α, β)) : f.comp (ContinuousMap.id 
_) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMap.Homotopic.comp`：comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (
hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁) : Homotopic (g₀.comp f₀) (g₁.comp f
₁)
· 使用定理 `ContinuousMap.Homotopic.refl`：refl (f : C(X, Y)) : Homotopic f f

--- 原说明 ---
The strong notion (contractible neighborhood basis)
implies the classical notion (null-homotopic inclusions).
The converse is false by the Borsuk-Mazurkiewicz counterexample [borsuk_mazurkie
wicz1934];
see also [MO88628] for discussion and the Whitehead manifold example.
-/
theorem StronglyLocallyContractibleSpace.locallyContractible [StronglyLocallyContractibleSpace X] :
    LocallyContractibleSpace X := by
  intro x U hU
  obtain ⟨V, ⟨hVmem, hVcontractible⟩, hVU⟩ := (contractible_basis x).mem_iff.mp hU
  refine ⟨V, hVU, hVmem, ?_⟩
  -- V is contractible, so the identity on V is nullhomotopic to a constant map
  obtain ⟨v₀, hid⟩ := id_nullhomotopic V
  -- The inclusion V ↪ U is homotopic to the constant map at (inclusion v₀)
  refine ⟨ContinuousMap.inclusion hVU v₀, ?_⟩
  convert! Homotopic.comp (.refl _) hid
  ext
  simp

end Implications

