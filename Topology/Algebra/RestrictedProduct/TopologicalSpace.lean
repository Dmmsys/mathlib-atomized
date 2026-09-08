/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Restricted products of topological spaces, topological groups and rings

We endow a restricted product of topological spaces with a natural topology,
which we describe below. We also show various compatibility results when we change
filters, and extend the construction of restricted products of algebraic structures
to the topological setting.

In particular, with the theory of adeles in mind, we show that if each `R i` is a locally compact
topological ring with open subring `A i`, and if all but finitely many of the `A i`s are also
compact, then `Πʳ i, [R i, A i]` is a locally compact topological ring.

## Main definitions

* `RestrictedProduct.topologicalSpace`: the `TopologicalSpace` instance on
  the restricted product `Πʳ i, [R i, A i]_[𝓕]`.

## Topology on the restricted product

The topology on the restricted product `Πʳ i, [R i, A i]_[𝓕]` is defined in the following way:
1. If `𝓕` is some principal filter `𝓟 s`, recall that `Πʳ i, [R i, A i]_[𝓟 s]` is canonically
   identified with `(Π i ∈ s, A i) × (Π i ∉ s, R i)`. We endow it with the product topology,
   which is also the topology induced from the full product `Π i, R i`.
2. In general, we note that `𝓕` is the infimum of the principal filters coarser than `𝓕`. We
   then endow `Πʳ i, [R i, A i]_[𝓕]` with the inductive limit / final topology associated to the
   inclusion maps `Πʳ i, [R i, A i]_[𝓟 s] → Πʳ i, [R i, A i]_[𝓕]` where `𝓕 ≤ 𝓟 s`.

In particular:
* On the classical restricted product, with respect to the cofinite filter, this corresponds to
  taking the inductive limit of the `Πʳ i, [R i, A i]_[𝓟 s]` over all *cofinite* sets `s : Set ι`.
* If `𝓕 = 𝓟 s` is a principal filter, this second step clearly does not change the topology, since
  `s` belongs to the indexing set of the inductive limit.

Taking advantage of that second remark, we do not actually declare an instance specific to
principal filters. Instead, we provide directly the general instance (corresponding to step 2 above)
as `RestrictedProduct.topologicalSpace`. We then prove that, for a principal filter, the
map to the full product is an inducing (`RestrictedProduct.isEmbedding_coe_of_principal`),
and that the topology for a general `𝓕` is indeed the expected inductive limit
(`RestrictedProduct.topologicalSpace_eq_iSup`).

## Main statements

* `RestrictedProduct.isEmbedding_coe_of_principal`: for any set `S`, `Πʳ i, [R i, A i]_[𝓟 S]`
  is endowed with the subset topology coming from `Π i, R i`.
* `RestrictedProduct.topologicalSpace_eq_iSup`: the topology on `Πʳ i, [R i, A i]_[𝓕]` is the
  inductive limit / final topology associated to the natural maps
  `Πʳ i, [R i, A i]_[𝓟 S] → Πʳ i, [R i, A i]_[𝓕]`, where `𝓕 ≤ 𝓟 S`.
* `RestrictedProduct.continuous_dom`: a map from `Πʳ i, [R i, A i]_[𝓕]` is continuous
  *if and only if* its restriction to each `Πʳ i, [R i, A i]_[𝓟 s]` (with `𝓕 ≤ 𝓟 s`) is continuous.
  * `RestrictedProduct.continuous_dom_prod_left`: assume that each `A i` is an **open** subset of
    `R i`. Then, for any topological space `Y`, a map from `Y × Πʳ i, [R i, A i]` is continuous
    *if and only if* its restriction to each `Y × Πʳ i, [R i, A i]_[𝓟 S]` (with `S` cofinite)
    is continuous.

* `RestrictedProduct.isTopologicalGroup`: if each `R i` is a topological group and each `A i` is an
  open subgroup of `R i`, then `Πʳ i, [R i, A i]` is a topological group.
* `RestrictedProduct.isTopologicalRing`: if each `R i` is a topological ring and each `A i` is an
  open subring of `R i`, then `Πʳ i, [R i, A i]` is a topological ring.
* `RestrictedProduct.continuousSMul`: if some topological monoid `G` acts on each `M i`, and each
  `A i` is stable for that action, then the natural action of `G` on `Πʳ i, [M i, A i]` is also
  continuous. In particular, if each `M i` is a topological `R`-module and each `A i` is an open
  sub-`R`-module of `M i`, then `Πʳ i, [M i, A i]` is a topological `R`-module.

* `RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite`:  if each `R i` is weakly locally
  compact, each `A i` is open, and all but finitely many `A i`s are also compact, then the
  restricted product `Πʳ i, [R i, A i]` is weakly locally compact.
* `RestrictedProduct.locallyCompactSpace_of_group`: assume that each `R i` is a locally compact
  group with `A i` an open subgroup. Assume also that all but finitely many `A i`s are compact.
  Then the restricted product `Πʳ i, [R i, A i]` is a locally compact group.

## Implementation details

Outside of principal filters and the cofinite filter, the topology we define on the restricted
product does not seem well-behaved. While declaring a single instance is practical, it may conflict
with more interesting topologies in some other cases. Thus, future contributions should not
restrain from specializing these instances to principal and cofinite filters if necessary.

## Tags

restricted product, adeles, ideles
-/

@[expose] public section

open Set Topology Filter

variable {ι : Type*}
variable (R : ι → Type*) (A : (i : ι) → Set (R i))

namespace RestrictedProduct

open scoped RestrictedProduct

variable {𝓕 𝓖 : Filter ι}

section Topology
/-!
## Topology on the restricted product

The topology on the restricted product `Πʳ i, [R i, A i]_[𝓕]` is defined in the following way:
1. If `𝓕` is some principal filter `𝓟 s`, recall that `Πʳ i, [R i, A i]_[𝓟 s]` is canonically
   identified with `(Π i ∈ s, A i) × (Π i ∉ s, R i)`. We endow it with the product topology,
   which is also the topology induced from the full product `Π i, R i`.
2. In general, we note that `𝓕` is the infimum of the principal filters coarser than `𝓕`. We
   then endow `Πʳ i, [R i, A i]_[𝓕]` with the inductive limit / final topology associated to the
   inclusion maps `Πʳ i, [R i, A i]_[𝓟 s] → Πʳ i, [R i, A i]_[𝓕]` where `𝓕 ≤ 𝓟 s`.

In particular:
* On the classical restricted product, with respect to the cofinite filter, this corresponds to
  taking the inductive limit of the `Πʳ i, [R i, A i]_[𝓟 s]` over all *cofinite* sets `s : Set ι`.
* If `𝓕 = 𝓟 s` is a principal filter, this second step clearly does not change the topology, since
  `s` belongs to the indexing set of the inductive limit.

Taking advantage of that second remark, we do not actually declare an instance specific to
principal filters. Instead, we provide directly the general instance (corresponding to step 2 above)
as `RestrictedProduct.topologicalSpace`. We then prove that, for a principal filter, the
map to the full product is an inducing (`RestrictedProduct.isEmbedding_coe_of_principal`),
and that the topology for a general `𝓕` is indeed the expected inductive limit
(`RestrictedProduct.topologicalSpace_eq_iSup`).

Note: outside of these two cases, this topology on the restricted product does not seem
well-behaved. While declaring a single instance is practical, it may conflict with more interesting
topologies in some other cases. Thus, future contributions should not restrain from specializing
these instances to principal and cofinite filters if necessary.
-/

/-!
### Definition of the topology
-/

variable {R A R' A'}
variable {𝓕 : Filter ι}
variable [∀ i, TopologicalSpace (R i)]

variable (R A 𝓕) in
/-
**RestrictedProduct.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduc
t`。
形式化陈述：topologicalSpace : TopologicalSpace (Πʳ i, [R i, A i]_[𝓕])
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalSpace : TopologicalSpace (Πʳ i, [R i, A i]_[𝓕]) :=
  ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S), .coinduced (inclusion R A hS)
    (.induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) inferInstance)

@[fun_prop]
/-
**RestrictedProduct.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProduct`
。
形式化陈述：continuous_coe : Continuous ((↑) : Πʳ i, [R i, A i]_[𝓕] -> Π i, R i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iSup_dom`：continuous_iSup_dom {t₁ : ι -> TopologicalSpace α} 
{t₂ : TopologicalSpace β} : Continuous[iSup t₁, t₂] f ↔ forall i, Continuous[t₁ 
i, t₂] f
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem continuous_coe :
    Continuous ((↑) : Πʳ i, [R i, A i]_[𝓕] → Π i, R i) :=
  continuous_iSup_dom.mpr fun _ ↦ continuous_iSup_dom.mpr fun _ ↦
    continuous_coinduced_dom.mpr continuous_induced_dom

@[fun_prop]
/-
**RestrictedProduct.continuous_eval** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProduct
`。
形式化陈述：continuous_eval (i : ι) : Continuous (fun (x : Πʳ i, [R i, A i]_[𝓕]) => x 
i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `RestrictedProduct.continuous_coe`：continuous_coe : Continuous ((↑) : Πʳ 
i, [R i, A i]_[𝓕] -> Π i, R i)
-/
theorem continuous_eval (i : ι) :
    Continuous (fun (x : Πʳ i, [R i, A i]_[𝓕]) ↦ x i) :=
  continuous_apply _ |>.comp continuous_coe

@[fun_prop]
/-
**RestrictedProduct.continuous_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedPr
oduct`。
形式化陈述：continuous_inclusion {𝓖 : Filter ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R
 A h)
参数：h : 𝓕 <= 𝓖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `coinduced_iSup`：coinduced_iSup {ι : Sort w} {t : ι -> TopologicalSpace α
} : (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `coinduced_compose`：coinduced_compose [tα : TopologicalSpace α] {f : α ->
 β} {g : β -> γ} : (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f)
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem continuous_inclusion {𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Continuous (inclusion R A h) := by
  simp_rw [continuous_iff_coinduced_le, topologicalSpace, coinduced_iSup, coinduced_compose]
  exact iSup₂_le fun S hS ↦ le_iSup₂_of_le S (le_trans h hS) le_rfl
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, T0Space (R i)] : T0Space (Πʳ i, [R i, A i]_[𝓕]) :=
  t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, T1Space (R i)] : T1Space (Πʳ i, [R i, A i]_[𝓕]) :=
  t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, T2Space (R i)] : T2Space (Πʳ i, [R i, A i]_[𝓕]) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coe

section principal
/-!
### Topological facts in the principal case
-/

variable {S : Set ι}

/-
**RestrictedProduct.topologicalSpace_eq_of_principal** 是 Mathlib 中的一个定理，位于命名空间 `
RestrictedProduct`。
形式化陈述：topologicalSpace_eq_of_principal : topologicalSpace R A (𝓟 S) = .induced (
(↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) inferInstance
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `RestrictedProduct.continuous_coe`：continuous_coe : Continuous ((↑) : Πʳ 
i, [R i, A i]_[𝓕] -> Π i, R i)
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `RestrictedProduct.inclusion_eq_id`：inclusion_eq_id : inclusion R A (le_r
efl 𝓕) = id
· 使用定理 `coinduced_id`：coinduced_id [t : TopologicalSpace α] : t.coinduced id = t
-/
theorem topologicalSpace_eq_of_principal :
    topologicalSpace R A (𝓟 S) =
      .induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) inferInstance :=
  le_antisymm (continuous_iff_le_induced.mp continuous_coe) <|
    (le_iSup₂_of_le S le_rfl <| by rw [inclusion_eq_id R A (𝓟 S), @coinduced_id])
/-
**RestrictedProduct.topologicalSpace_eq_of_top** 是 Mathlib 中的一个定理，位于命名空间 `Restri
ctedProduct`。
形式化陈述：topologicalSpace_eq_of_top : topologicalSpace R A ⊤ = .induced ((↑) : Πʳ i
, [R i, A i]_[⊤] -> Π i, R i) inferInstance
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.topologicalSpace_eq_of_principal`：topologicalSpace_eq_
of_principal : topologicalSpace R A (𝓟 S) = .induced ((↑) : Πʳ i, [R i, A i]_[𝓟 
S] -> Π i, R i) inferInstance
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
theorem topologicalSpace_eq_of_top :
    topologicalSpace R A ⊤ =
      .induced ((↑) : Πʳ i, [R i, A i]_[⊤] → Π i, R i) inferInstance :=
  principal_univ ▸ topologicalSpace_eq_of_principal
/-
**RestrictedProduct.topologicalSpace_eq_of_bot** 是 Mathlib 中的一个定理，位于命名空间 `Restri
ctedProduct`。
形式化陈述：topologicalSpace_eq_of_bot : topologicalSpace R A ⊥ = .induced ((↑) : Πʳ i
, [R i, A i]_[⊥] -> Π i, R i) inferInstance
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.topologicalSpace_eq_of_principal`：topologicalSpace_eq_
of_principal : topologicalSpace R A (𝓟 S) = .induced ((↑) : Πʳ i, [R i, A i]_[𝓟 
S] -> Π i, R i) inferInstance
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
-/
theorem topologicalSpace_eq_of_bot :
    topologicalSpace R A ⊥ =
      .induced ((↑) : Πʳ i, [R i, A i]_[⊥] → Π i, R i) inferInstance :=
  principal_empty ▸ topologicalSpace_eq_of_principal
/-
**RestrictedProduct.isEmbedding_coe_of_principal** 是 Mathlib 中的一个定理，位于命名空间 `Rest
rictedProduct`。
形式化陈述：isEmbedding_coe_of_principal : IsEmbedding ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -
> Π i, R i) where eq_induced
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.topologicalSpace_eq_of_principal`：topologicalSpace_eq_
of_principal : topologicalSpace R A (𝓟 S) = .induced ((↑) : Πʳ i, [R i, A i]_[𝓟 
S] -> Π i, R i) inferInstance
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem isEmbedding_coe_of_principal :
    IsEmbedding ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) where
  eq_induced := topologicalSpace_eq_of_principal
  injective := DFunLike.coe_injective
/-
**RestrictedProduct.isEmbedding_coe_of_top** 是 Mathlib 中的一个定理，位于命名空间 `Restricted
Product`。
形式化陈述：isEmbedding_coe_of_top : IsEmbedding ((↑) : Πʳ i, [R i, A i]_[⊤] -> Π i, R
 i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.isEmbedding_coe_of_principal`：isEmbedding_coe_of_princ
ipal : IsEmbedding ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) where eq_induced
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
theorem isEmbedding_coe_of_top :
    IsEmbedding ((↑) : Πʳ i, [R i, A i]_[⊤] → Π i, R i) :=
  principal_univ ▸ isEmbedding_coe_of_principal
/-
**RestrictedProduct.isEmbedding_coe_of_bot** 是 Mathlib 中的一个定理，位于命名空间 `Restricted
Product`。
形式化陈述：isEmbedding_coe_of_bot : IsEmbedding ((↑) : Πʳ i, [R i, A i]_[⊥] -> Π i, R
 i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.isEmbedding_coe_of_principal`：isEmbedding_coe_of_princ
ipal : IsEmbedding ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) where eq_induced
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
-/
theorem isEmbedding_coe_of_bot :
    IsEmbedding ((↑) : Πʳ i, [R i, A i]_[⊥] → Π i, R i) :=
  principal_empty ▸ isEmbedding_coe_of_principal
/-
**RestrictedProduct.continuous_rng_of_principal** 是 Mathlib 中的一个定理，位于命名空间 `Restr
ictedProduct`。
形式化陈述：continuous_rng_of_principal {X : Type*} [TopologicalSpace X] {f : X -> Πʳ 
i, [R i, A i]_[𝓟 S]} : Continuous f ↔ Continuous ((↑) ∘ f : X -> Π i, R i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `RestrictedProduct.isEmbedding_coe_of_principal`：isEmbedding_coe_of_princ
ipal : IsEmbedding ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) where eq_induced
-/
theorem continuous_rng_of_principal {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ i, [R i, A i]_[𝓟 S]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  isEmbedding_coe_of_principal.continuous_iff
/-
**RestrictedProduct.continuous_rng_of_top** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedP
roduct`。
形式化陈述：continuous_rng_of_top {X : Type*} [TopologicalSpace X] {f : X -> Πʳ i, [R 
i, A i]_[⊤]} : Continuous f ↔ Continuous ((↑) ∘ f : X -> Π i, R i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `RestrictedProduct.isEmbedding_coe_of_top`：isEmbedding_coe_of_top : IsEmb
edding ((↑) : Πʳ i, [R i, A i]_[⊤] -> Π i, R i)
-/
theorem continuous_rng_of_top {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ i, [R i, A i]_[⊤]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  isEmbedding_coe_of_top.continuous_iff
/-
**RestrictedProduct.continuous_rng_of_bot** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedP
roduct`。
形式化陈述：continuous_rng_of_bot {X : Type*} [TopologicalSpace X] {f : X -> Πʳ i, [R 
i, A i]_[⊥]} : Continuous f ↔ Continuous ((↑) ∘ f : X -> Π i, R i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `RestrictedProduct.isEmbedding_coe_of_bot`：isEmbedding_coe_of_bot : IsEmb
edding ((↑) : Πʳ i, [R i, A i]_[⊥] -> Π i, R i)
-/
theorem continuous_rng_of_bot {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ i, [R i, A i]_[⊥]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  isEmbedding_coe_of_bot.continuous_iff
/-
**RestrictedProduct.continuous_rng_of_principal_iff_forall** 是 Mathlib 中的一个引理，位于
命名空间 `RestrictedProduct`。
形式化陈述：continuous_rng_of_principal_iff_forall {X : Type*} [TopologicalSpace X] {f
 : X -> Πʳ (i : ι), [R i, A i]_[𝓟 S]} : Continuous f ↔ forall i : ι, Continuous 
((fun x => x i) ∘ f)
参数：i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `RestrictedProduct.continuous_rng_of_principal`：continuous_rng_of_princip
al {X : Type*} [TopologicalSpace X] {f : X -> Πʳ i, [R i, A i]_[𝓟 S]} : Continuo
us f ↔ Continuous ((↑) ∘ f : X -> Π…
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
-/
lemma continuous_rng_of_principal_iff_forall {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ (i : ι), [R i, A i]_[𝓟 S]} :
    Continuous f ↔ ∀ i : ι, Continuous ((fun x ↦ x i) ∘ f) :=
  continuous_rng_of_principal.trans continuous_pi_iff

/-- The obvious bijection between `Πʳ i, [R i, A i]_[⊤]` and `Π i, A i` is a homeomorphism. -/
/-
**RestrictedProduct.homeoTop** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：homeoTop : (Π i, A i) ≃ₜ (Πʳ i, [R i, A i]_[⊤]) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious bijection between `Πʳ i, [R i, A i]_[⊤]` and `Π i, A i` is a homeomo
rphism.
-/
def homeoTop : (Π i, A i) ≃ₜ (Πʳ i, [R i, A i]_[⊤]) where
  toFun f := ⟨fun i ↦ f i, fun i ↦ (f i).2⟩
  invFun f i := ⟨f i, f.2 i⟩
  continuous_toFun := continuous_rng_of_top.mpr <| continuous_pi fun i ↦
    continuous_subtype_val.comp <| continuous_apply i
  continuous_invFun := continuous_pi fun i ↦ continuous_induced_rng.mpr <| continuous_eval i

/-- The obvious bijection between `Πʳ i, [R i, A i]_[⊥]` and `Π i, R i` is a homeomorphism. -/
/-
**RestrictedProduct.homeoBot** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：homeoBot : (Π i, R i) ≃ₜ (Πʳ i, [R i, A i]_[⊥]) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious bijection between `Πʳ i, [R i, A i]_[⊥]` and `Π i, R i` is a homeomo
rphism.
-/
def homeoBot : (Π i, R i) ≃ₜ (Πʳ i, [R i, A i]_[⊥]) where
  toFun f := ⟨fun i ↦ f i, eventually_bot⟩
  invFun f i := f i
  continuous_toFun := continuous_rng_of_bot.mpr <| continuous_pi fun i ↦ continuous_apply i
  continuous_invFun := continuous_pi continuous_eval

/-- Assume that `S` is a subset of `ι` with finite complement, that each `R i` is weakly locally
compact, and that `A i` is *compact* for all `i ∈ S`. Then the restricted product
`Πʳ i, [R i, A i]_[𝓟 S]` is locally compact.

Note: we spell "`S` has finite complement" as `cofinite ≤ 𝓟 S`. -/
/-
**RestrictedProduct.weaklyLocallyCompactSpace_of_principal** 是 Mathlib 中的一个定理，位于
命名空间 `RestrictedProduct`。
形式化陈述：weaklyLocallyCompactSpace_of_principal [forall i, WeaklyLocallyCompactSpac
e (R i)] (hS : cofinite <= 𝓟 S) (hAcompact : forall i in S, IsCompact (A i)) : W
eaklyLocallyCompactSpace (Πʳ i, [R i, A i]_[𝓟 S]) where exists_compact_mem_nhds
参数：R i；hS : cofinite <= 𝓟 S；hAcompact : forall i in S, IsCompact (A i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `set_pi_mem_nhds`：set_pi_mem_nhds {i : Set ι} {s : forall a, Set (A a)} {
x : forall a, A a} (hi : i.Finite) (hs : forall a in i, s a in 𝓝 (x a)) : pi i s
 in 𝓝…
· 使用定理 `Filter.mem_cofinite`：mem_cofinite {s : Set α} : s in @cofinite α ↔ sᶜ.Fi
nite
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsInducing.isCompact_preimage_iff`：Topology.IsInducing.isCompac
t_preimage_iff {f : X -> Y} (hf : IsInducing f) {K : Set Y} (Kf : K subseteq ran
ge f) : IsCompact (f ⁻¹' K) ↔ Is…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `RestrictedProduct.isEmbedding_coe_of_principal`：isEmbedding_coe_of_princ
ipal : IsEmbedding ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) where eq_induced
· 使用引理 `RestrictedProduct.range_coe_principal`：range_coe_principal {S : Set ι} :
 range ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) = S.pi A
· 使用定理 `Set.pi_if`：pi_if {p : ι -> Prop} [h : DecidablePred p] (s : Set ι) (t₁ t
₂ : forall i, Set (α i)) : (pi s fun i => if p i then t₁ i else t₂ i) = pi ({ i…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Assume that `S` is a subset of `ι` with finite complement, that each `R i` is we
akly locally
compact, and that `A i` is *compact* for all `i ∈ S`. Then the restricted produc
t
`Πʳ i, [R i, A i]_[𝓟 S]` is locally compact.

Note: we spell "`S` has finite complement" as `cofinite ≤ 𝓟 S`.
-/
theorem weaklyLocallyCompactSpace_of_principal [∀ i, WeaklyLocallyCompactSpace (R i)]
    (hS : cofinite ≤ 𝓟 S) (hAcompact : ∀ i ∈ S, IsCompact (A i)) :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]_[𝓟 S]) where
  exists_compact_mem_nhds := fun x ↦ by
    rw [le_principal_iff, mem_cofinite] at hS
    classical
    have : ∀ i, ∃ K, IsCompact K ∧ K ∈ 𝓝 (x i) := fun i ↦ exists_compact_mem_nhds (x i)
    choose K K_compact hK using this
    set Q : Set (Π i, R i) := univ.pi (fun i ↦ if i ∈ S then A i else K i) with Q_def
    have Q_compact : IsCompact Q := isCompact_univ_pi fun i ↦ by
      split_ifs with his
      · exact hAcompact i his
      · exact K_compact i
    set U : Set (Π i, R i) := Sᶜ.pi K
    have U_nhds : U ∈ 𝓝 (x : Π i, R i) := set_pi_mem_nhds hS fun i _ ↦ hK i
    have QU : (↑) ⁻¹' U ⊆ ((↑) ⁻¹' Q : Set (Πʳ i, [R i, A i]_[𝓟 S])) := fun y H i _ ↦ by
      dsimp only
      split_ifs with hi
      · exact y.2 hi
      · exact H i hi
    refine ⟨((↑) ⁻¹' Q), ?_, mem_of_superset ?_ QU⟩
    · refine isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr Q_compact
      simp_rw [range_coe_principal, Q_def, pi_if, mem_univ, true_and]
      exact inter_subset_left
    · simpa only [isEmbedding_coe_of_principal.nhds_eq_comap] using preimage_mem_comap U_nhds
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, WeaklyLocallyCompactSpace (R i)] [hS : Fact (cofinite ≤ 𝓟 S)]
    [hAcompact : ∀ i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]_[𝓟 S]) :=
  weaklyLocallyCompactSpace_of_principal hS.out
    fun _ _ ↦ isCompact_iff_compactSpace.mpr inferInstance

end principal

section general
/-!
### Topological facts in the general case
-/

variable (𝓕) in
/-
**RestrictedProduct.topologicalSpace_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Restrict
edProduct`。
形式化陈述：topologicalSpace_eq_iSup : topologicalSpace R A 𝓕 = ⨆ (S : Set ι) (hS : 𝓕 
<= 𝓟 S), .coinduced (inclusion R A hS) (topologicalSpace R A (𝓟 S))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `RestrictedProduct.topologicalSpace_eq_of_principal`：topologicalSpace_eq_
of_principal : topologicalSpace R A (𝓟 S) = .induced ((↑) : Πʳ i, [R i, A i]_[𝓟 
S] -> Π i, R i) inferInstance
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem topologicalSpace_eq_iSup :
    topologicalSpace R A 𝓕 = ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S),
      .coinduced (inclusion R A hS) (topologicalSpace R A (𝓟 S)) := by
  simp_rw [topologicalSpace_eq_of_principal, topologicalSpace]

/-- The **universal property** of the topology on the restricted product: a map from
`Πʳ i, [R i, A i]_[𝓕]` is continuous *iff* its restriction to each `Πʳ i, [R i, A i]_[𝓟 s]`
(with `𝓕 ≤ 𝓟 s`) is continuous.

See also `RestrictedProduct.continuous_dom_prod_left`. -/
/-
**RestrictedProduct.continuous_dom** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProduct`
。
形式化陈述：continuous_dom {X : Type*} [TopologicalSpace X] {f : Πʳ i, [R i, A i]_[𝓕] 
-> X} : Continuous f ↔ forall (S : Set ι) (hS : 𝓕 <= 𝓟 S), Continuous (f ∘ inclu
sion R A hS)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RestrictedProduct.topologicalSpace_eq_of_principal`：topologicalSpace_eq_
of_principal : topologicalSpace R A (𝓟 S) = .induced ((↑) : Πʳ i, [R i, A i]_[𝓟 
S] -> Π i, R i) inferInstance
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The **universal property** of the topology on the restricted product: a map from
`Πʳ i, [R i, A i]_[𝓕]` is continuous *iff* its restriction to each `Πʳ i, [R i, 
A i]_[𝓟 s]`
(with `𝓕 ≤ 𝓟 s`) is continuous.

See also `RestrictedProduct.continuous_dom_prod_left`.
-/
theorem continuous_dom {X : Type*} [TopologicalSpace X]
    {f : Πʳ i, [R i, A i]_[𝓕] → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S), Continuous (f ∘ inclusion R A hS) := by
  simp_rw +instances [topologicalSpace_eq_of_principal, continuous_iSup_dom,
    continuous_coinduced_dom]
/-
**RestrictedProduct.isEmbedding_inclusion_principal** 是 Mathlib 中的一个定理，位于命名空间 `R
estrictedProduct`。
形式化陈述：isEmbedding_inclusion_principal {S : Set ι} (hS : 𝓕 <= 𝓟 S) : IsEmbedding 
(inclusion R A hS)
参数：hS : 𝓕 <= 𝓟 S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `RestrictedProduct.continuous_inclusion`：continuous_inclusion {𝓖 : Filter
 ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R A h)
· 使用定理 `RestrictedProduct.continuous_coe`：continuous_coe : Continuous ((↑) : Πʳ 
i, [R i, A i]_[𝓕] -> Π i, R i)
· 使用定理 `RestrictedProduct.isEmbedding_coe_of_principal`：isEmbedding_coe_of_princ
ipal : IsEmbedding ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) where eq_induced
-/
theorem isEmbedding_inclusion_principal {S : Set ι} (hS : 𝓕 ≤ 𝓟 S) :
    IsEmbedding (inclusion R A hS) :=
  .of_comp (continuous_inclusion hS) continuous_coe isEmbedding_coe_of_principal
/-
**RestrictedProduct.isEmbedding_inclusion_top** 是 Mathlib 中的一个定理，位于命名空间 `Restric
tedProduct`。
形式化陈述：isEmbedding_inclusion_top : IsEmbedding (inclusion R A (le_top : 𝓕 <= ⊤))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `RestrictedProduct.continuous_inclusion`：continuous_inclusion {𝓖 : Filter
 ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R A h)
· 使用定理 `RestrictedProduct.continuous_coe`：continuous_coe : Continuous ((↑) : Πʳ 
i, [R i, A i]_[𝓕] -> Π i, R i)
· 使用定理 `RestrictedProduct.isEmbedding_coe_of_top`：isEmbedding_coe_of_top : IsEmb
edding ((↑) : Πʳ i, [R i, A i]_[⊤] -> Π i, R i)
-/
theorem isEmbedding_inclusion_top :
    IsEmbedding (inclusion R A (le_top : 𝓕 ≤ ⊤)) :=
  .of_comp (continuous_inclusion _) continuous_coe isEmbedding_coe_of_top

/-- `Π i, A i` has the subset topology from the restricted product. -/
/-
**RestrictedProduct.isEmbedding_structureMap** 是 Mathlib 中的一个定理，位于命名空间 `Restrict
edProduct`。
形式化陈述：isEmbedding_structureMap : IsEmbedding (structureMap R A 𝓕)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `RestrictedProduct.isEmbedding_inclusion_top`：isEmbedding_inclusion_top :
 IsEmbedding (inclusion R A (le_top : 𝓕 <= ⊤))
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
`Π i, A i` has the subset topology from the restricted product.
-/
theorem isEmbedding_structureMap :
    IsEmbedding (structureMap R A 𝓕) :=
  isEmbedding_inclusion_top.comp homeoTop.isEmbedding

end general

section cofinite
/-!
### Topological facts in the case where `𝓕 = cofinite` and all `A i`s are open

The classical restricted product, associated to the cofinite filter, satisfies more topological
properties when each `A i` is an open subset of `R i`. The key fact is that each
`Πʳ i, [R i, A i]_[𝓟 S]` (with `S` cofinite) then embeds **as an open subset** in
`Πʳ i, [R i, A i]`.

This allows us to prove a "universal property with parameters", expressing that for any
arbitrary topological space `X` (of "parameters"), the product `X × Πʳ i, [R i, A i]`
is still the inductive limit of the `X × Πʳ i, [R i, A i]_[𝓟 S]` for `S` cofinite.

This fact, which is **not true** for a general inductive limit, will allow us to prove continuity
of functions of two variables (e.g algebraic operations), which would otherwise be inaccessible.
-/

variable (hAopen : ∀ i, IsOpen (A i))

include hAopen in
/-
**RestrictedProduct.isOpen_forall_imp_mem_of_principal** 是 Mathlib 中的一个定理，位于命名空间
 `RestrictedProduct`。
形式化陈述：isOpen_forall_imp_mem_of_principal {S : Set ι} (hS : cofinite <= 𝓟 S) {p :
 ι -> Prop} : IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S] | forall i, p i -> f.1 i in A i
}
参数：hS : cofinite <= 𝓟 S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `RestrictedProduct.continuous_coe`：continuous_coe : Continuous ((↑) : Πʳ 
i, [R i, A i]_[𝓕] -> Π i, R i)
· 使用定理 `isOpen_set_pi`：isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi :
 i.Finite) (hs : forall a in i, IsOpen (s a)) : IsOpen (pi i s)
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem isOpen_forall_imp_mem_of_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) {p : ι → Prop} :
    IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S] | ∀ i, p i → f.1 i ∈ A i} := by
  rw [le_principal_iff] at hS
  convert!
    isOpen_set_pi (hS.inter_of_left {i | p i}) (fun i _ ↦ hAopen i) |>.preimage continuous_coe
  ext f
  refine ⟨fun H i hi ↦ H i hi.2, fun H i hiT ↦ ?_⟩
  by_cases hiS : i ∈ S
  · exact f.2 hiS
  · exact H i ⟨hiS, hiT⟩

include hAopen in
/-
**RestrictedProduct.isOpen_forall_mem_of_principal** 是 Mathlib 中的一个定理，位于命名空间 `Re
strictedProduct`。
形式化陈述：isOpen_forall_mem_of_principal {S : Set ι} (hS : cofinite <= 𝓟 S) : IsOpen
 {f : Πʳ i, [R i, A i]_[𝓟 S] | forall i, f.1 i in A i}
参数：hS : cofinite <= 𝓟 S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `RestrictedProduct.isOpen_forall_imp_mem_of_principal`：isOpen_forall_imp_
mem_of_principal {S : Set ι} (hS : cofinite <= 𝓟 S) {p : ι -> Prop} : IsOpen {f 
: Πʳ i, [R i, A i]_[𝓟 S] | forall i, p i -…
-/
theorem isOpen_forall_mem_of_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) :
    IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S] | ∀ i, f.1 i ∈ A i} := by
  convert! isOpen_forall_imp_mem_of_principal hAopen hS (p := fun _ ↦ True)
  simp

include hAopen in
/-
**RestrictedProduct.isOpen_forall_imp_mem** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedP
roduct`。
形式化陈述：isOpen_forall_imp_mem {p : ι -> Prop} : IsOpen {f : Πʳ i, [R i, A i] | for
all i, p i -> f.1 i in A i}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RestrictedProduct.topologicalSpace_eq_iSup`：topologicalSpace_eq_iSup : t
opologicalSpace R A 𝓕 = ⨆ (S : Set ι) (hS : 𝓕 <= 𝓟 S), .coinduced (inclusion R A
 hS) (topologicalSpace R A (𝓟 S)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `RestrictedProduct.isOpen_forall_imp_mem_of_principal`：isOpen_forall_imp_
mem_of_principal {S : Set ι} (hS : cofinite <= 𝓟 S) {p : ι -> Prop} : IsOpen {f 
: Πʳ i, [R i, A i]_[𝓟 S] | forall i, p i -…
-/
theorem isOpen_forall_imp_mem {p : ι → Prop} :
    IsOpen {f : Πʳ i, [R i, A i] | ∀ i, p i → f.1 i ∈ A i} := by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS ↦ isOpen_forall_imp_mem_of_principal hAopen hS

include hAopen in
/-
**RestrictedProduct.isOpen_forall_mem** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProdu
ct`。
形式化陈述：isOpen_forall_mem : IsOpen {f : Πʳ i, [R i, A i] | forall i, f.1 i in A i}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RestrictedProduct.topologicalSpace_eq_iSup`：topologicalSpace_eq_iSup : t
opologicalSpace R A 𝓕 = ⨆ (S : Set ι) (hS : 𝓕 <= 𝓟 S), .coinduced (inclusion R A
 hS) (topologicalSpace R A (𝓟 S)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `RestrictedProduct.isOpen_forall_mem_of_principal`：isOpen_forall_mem_of_p
rincipal {S : Set ι} (hS : cofinite <= 𝓟 S) : IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S]
 | forall i, f.1 i in A i}
-/
theorem isOpen_forall_mem :
    IsOpen {f : Πʳ i, [R i, A i] | ∀ i, f.1 i ∈ A i} := by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS ↦ isOpen_forall_mem_of_principal hAopen hS

include hAopen in
/-
**RestrictedProduct.isOpenEmbedding_inclusion_principal** 是 Mathlib 中的一个定理，位于命名空
间 `RestrictedProduct`。
形式化陈述：isOpenEmbedding_inclusion_principal {S : Set ι} (hS : cofinite <= 𝓟 S) : I
sOpenEmbedding (inclusion R A hS) where toIsEmbedding
参数：hS : cofinite <= 𝓟 S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.isEmbedding_inclusion_principal`：isEmbedding_inclusion
_principal {S : Set ι} (hS : 𝓕 <= 𝓟 S) : IsEmbedding (inclusion R A hS)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RestrictedProduct.range_inclusion`：range_inclusion (h : 𝓕 <= 𝓖) : Set.ra
nge (inclusion R A h) = {x | forallᶠ i in 𝓖, x i in A i}
· 使用定理 `RestrictedProduct.isOpen_forall_imp_mem`：isOpen_forall_imp_mem {p : ι ->
 Prop} : IsOpen {f : Πʳ i, [R i, A i] | forall i, p i -> f.1 i in A i}
-/
theorem isOpenEmbedding_inclusion_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) :
    IsOpenEmbedding (inclusion R A hS) where
  toIsEmbedding := isEmbedding_inclusion_principal hS
  isOpen_range := by
    rw [range_inclusion]
    exact isOpen_forall_imp_mem hAopen

include hAopen in
/-- `Π i, A i` is homeomorphic to an open subset of the restricted product. -/
/-
**RestrictedProduct.isOpenEmbedding_structureMap** 是 Mathlib 中的一个定理，位于命名空间 `Rest
rictedProduct`。
形式化陈述：isOpenEmbedding_structureMap : IsOpenEmbedding (structureMap R A cofinite)
 where toIsEmbedding
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.isEmbedding_structureMap`：isEmbedding_structureMap : I
sEmbedding (structureMap R A 𝓕)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RestrictedProduct.range_structureMap`：range_structureMap : Set.range (st
ructureMap R A 𝓕) = {f | forall i, f.1 i in A i}
· 使用定理 `RestrictedProduct.isOpen_forall_mem`：isOpen_forall_mem : IsOpen {f : Πʳ 
i, [R i, A i] | forall i, f.1 i in A i}

--- 原说明 ---
`Π i, A i` is homeomorphic to an open subset of the restricted product.
-/
theorem isOpenEmbedding_structureMap :
    IsOpenEmbedding (structureMap R A cofinite) where
  toIsEmbedding := isEmbedding_structureMap
  isOpen_range := by
    rw [range_structureMap]
    exact isOpen_forall_mem hAopen

include hAopen in
/-
**RestrictedProduct.nhds_eq_map_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedP
roduct`。
形式化陈述：nhds_eq_map_inclusion {S : Set ι} (hS : cofinite <= 𝓟 S) (x : Πʳ i, [R i, 
A i]_[𝓟 S]) : (𝓝 (inclusion R A hS x)) = .map (inclusion R A hS) (𝓝 x)
参数：hS : cofinite <= 𝓟 S；x : Πʳ i, [R i, A i]_[𝓟 S]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `RestrictedProduct.isOpenEmbedding_inclusion_principal`：isOpenEmbedding_i
nclusion_principal {S : Set ι} (hS : cofinite <= 𝓟 S) : IsOpenEmbedding (inclusi
on R A hS) where toIsEmbedding
-/
theorem nhds_eq_map_inclusion {S : Set ι} (hS : cofinite ≤ 𝓟 S)
    (x : Πʳ i, [R i, A i]_[𝓟 S]) :
    (𝓝 (inclusion R A hS x)) = .map (inclusion R A hS) (𝓝 x) := by
  rw [isOpenEmbedding_inclusion_principal hAopen hS |>.map_nhds_eq x]

include hAopen in
/-
**RestrictedProduct.nhds_eq_map_structureMap** 是 Mathlib 中的一个定理，位于命名空间 `Restrict
edProduct`。
形式化陈述：nhds_eq_map_structureMap (x : Π i, A i) : (𝓝 (structureMap R A cofinite x)
) = .map (structureMap R A cofinite) (𝓝 x)
参数：x : Π i, A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `RestrictedProduct.isOpenEmbedding_structureMap`：isOpenEmbedding_structur
eMap : IsOpenEmbedding (structureMap R A cofinite) where toIsEmbedding
-/
theorem nhds_eq_map_structureMap
    (x : Π i, A i) :
    (𝓝 (structureMap R A cofinite x)) = .map (structureMap R A cofinite) (𝓝 x) := by
  rw [isOpenEmbedding_structureMap hAopen |>.map_nhds_eq x]

include hAopen in
/-- If each `R i` is weakly locally compact, each `A i` is open, and all but finitely many `A i`s
are also compact, then the restricted product `Πʳ i, [R i, A i]` is weakly locally compact. -/
/-
**RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite** 是 Mathlib 中的一个定理，位于命
名空间 `RestrictedProduct`。
形式化陈述：weaklyLocallyCompactSpace_of_cofinite [forall i, WeaklyLocallyCompactSpace
 (R i)] (hAcompact : forallᶠ i in cofinite, IsCompact (A i)) : WeaklyLocallyComp
actSpace (Πʳ i, [R i, A i]) where exists_compact_mem_nhds
参数：R i；hAcompact : forallᶠ i in cofinite, IsCompact (A i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RestrictedProduct.weaklyLocallyCompactSpace_of_principal`：weaklyLocallyC
ompactSpace_of_principal [forall i, WeaklyLocallyCompactSpace (R i)] (hS : cofin
ite <= 𝓟 S) (hAcompact : forall i in S, IsComp…
· 使用引理 `RestrictedProduct.exists_inclusion_eq_of_eventually`：exists_inclusion_eq
_of_eventually (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]} (hx𝓖 : forallᶠ i in 𝓖, x 
i in A i) : exists x' : Πʳ i, [R i, A i]_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RestrictedProduct.nhds_eq_map_inclusion`：nhds_eq_map_inclusion {S : Set 
ι} (hS : cofinite <= 𝓟 S) (x : Πʳ i, [R i, A i]_[𝓟 S]) : (𝓝 (inclusion R A hS x)
) = .map (inclusion R A hS) (…
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `RestrictedProduct.continuous_inclusion`：continuous_inclusion {𝓖 : Filter
 ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R A h)
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f

--- 原说明 ---
If each `R i` is weakly locally compact, each `A i` is open, and all but finitel
y many `A i`s
are also compact, then the restricted product `Πʳ i, [R i, A i]` is weakly local
ly compact.
-/
theorem weaklyLocallyCompactSpace_of_cofinite [∀ i, WeaklyLocallyCompactSpace (R i)]
    (hAcompact : ∀ᶠ i in cofinite, IsCompact (A i)) :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]) where
  exists_compact_mem_nhds := fun x ↦ by
    set S := {i | IsCompact (A i) ∧ x i ∈ A i}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr (hAcompact.and x.2)
    have hSx : ∀ i ∈ S, x i ∈ A i := fun i hi ↦ hi.2
    have hSA : ∀ i ∈ S, IsCompact (A i) := fun i hi ↦ hi.1
    have := weaklyLocallyCompactSpace_of_principal hS hSA
    rcases exists_inclusion_eq_of_eventually R A hS hSx with ⟨x', hxx'⟩
    rw [← hxx', nhds_eq_map_inclusion hAopen]
    rcases exists_compact_mem_nhds x' with ⟨K, K_compact, hK⟩
    exact ⟨inclusion R A hS '' K, K_compact.image (continuous_inclusion hS), image_mem_map hK⟩
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hAopen : Fact (∀ i, IsOpen (A i))] [∀ i, WeaklyLocallyCompactSpace (R i)]
    [hAcompact : ∀ i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]) :=
  weaklyLocallyCompactSpace_of_cofinite hAopen.out <|
    .of_forall fun _ ↦ isCompact_iff_compactSpace.mpr inferInstance

include hAopen in
/-- The **universal property with parameters** of the topology on the restricted product:
for any topological space `Y` of "parameters", a map from `(Πʳ i, [R i, A i]) × Y` is continuous
*iff* its restriction to each `(Πʳ i, [R i, A i]_[𝓟 S]) × Y` (with `S` cofinite) is continuous. -/
/-
**RestrictedProduct.continuous_dom_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Restric
tedProduct`。
形式化陈述：continuous_dom_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalS
pace Y] {f : Πʳ i, [R i, A i] × Y -> X} : Continuous f ↔ forall (S : Set ι) (hS 
: cofinite <= 𝓟 S), Continuous (f ∘ (Prod.map (inclusion R A hS) id))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `RestrictedProduct.continuous_inclusion`：continuous_inclusion {𝓖 : Filter
 ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R A h)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `RestrictedProduct.exists_inclusion_eq_of_eventually`：exists_inclusion_eq
_of_eventually (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]} (hx𝓖 : forallᶠ i in 𝓖, x 
i in A i) : exists x' : Πʳ i, [R i, A i]_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `RestrictedProduct.nhds_eq_map_inclusion`：nhds_eq_map_inclusion {S : Set 
ι} (hS : cofinite <= 𝓟 S) (x : Πʳ i, [R i, A i]_[𝓟 S]) : (𝓝 (inclusion R A hS x)
) = .map (inclusion R A hS) (…
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))

--- 原说明 ---
The **universal property with parameters** of the topology on the restricted pro
duct:
for any topological space `Y` of "parameters", a map from `(Πʳ i, [R i, A i]) × 
Y` is continuous
*iff* its restriction to each `(Πʳ i, [R i, A i]_[𝓟 S]) × Y` (with `S` cofinite)
 is continuous.
-/
theorem continuous_dom_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Πʳ i, [R i, A i] × Y → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S),
      Continuous (f ∘ (Prod.map (inclusion R A hS) id)) := by
  refine ⟨fun H S hS ↦ H.comp ((continuous_inclusion hS).prodMap continuous_id),
    fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, y⟩
  set S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  have hxS : ∀ i ∈ S, x i ∈ A i := fun i hi ↦ hi
  rcases exists_inclusion_eq_of_eventually R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx', nhds_prod_eq, nhds_eq_map_inclusion hAopen hS x',
    ← Filter.map_id (f := 𝓝 y), prod_map_map_eq, ← nhds_prod_eq, tendsto_map'_iff]
  exact H S hS |>.tendsto ⟨x', y⟩

-- TODO: get from the previous one instead of copy-pasting
include hAopen in
/-- The **universal property with parameters** of the topology on the restricted product:
for any topological space `Y` of "parameters", a map from `Y × Πʳ i, [R i, A i]` is continuous
*iff* its restriction to each `Y × Πʳ i, [R i, A i]_[𝓟 S]` (with `S` cofinite) is continuous. -/
/-
**RestrictedProduct.continuous_dom_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Restrict
edProduct`。
形式化陈述：continuous_dom_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSp
ace Y] {f : Y × Πʳ i, [R i, A i] -> X} : Continuous f ↔ forall (S : Set ι) (hS :
 cofinite <= 𝓟 S), Continuous (f ∘ (Prod.map id (inclusion R A hS)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `RestrictedProduct.continuous_inclusion`：continuous_inclusion {𝓖 : Filter
 ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R A h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `RestrictedProduct.exists_inclusion_eq_of_eventually`：exists_inclusion_eq
_of_eventually (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]} (hx𝓖 : forallᶠ i in 𝓖, x 
i in A i) : exists x' : Πʳ i, [R i, A i]_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `RestrictedProduct.nhds_eq_map_inclusion`：nhds_eq_map_inclusion {S : Set 
ι} (hS : cofinite <= 𝓟 S) (x : Πʳ i, [R i, A i]_[𝓟 S]) : (𝓝 (inclusion R A hS x)
) = .map (inclusion R A hS) (…
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))

--- 原说明 ---
The **universal property with parameters** of the topology on the restricted pro
duct:
for any topological space `Y` of "parameters", a map from `Y × Πʳ i, [R i, A i]`
 is continuous
*iff* its restriction to each `Y × Πʳ i, [R i, A i]_[𝓟 S]` (with `S` cofinite) i
s continuous.
-/
theorem continuous_dom_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y × Πʳ i, [R i, A i] → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S),
      Continuous (f ∘ (Prod.map id (inclusion R A hS))) := by
  refine ⟨fun H S hS ↦ H.comp (continuous_id.prodMap (continuous_inclusion hS)),
    fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨y, x⟩
  set S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  have hxS : ∀ i ∈ S, x i ∈ A i := fun i hi ↦ hi
  rcases exists_inclusion_eq_of_eventually R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx', nhds_prod_eq, nhds_eq_map_inclusion hAopen hS x',
    ← Filter.map_id (f := 𝓝 y), prod_map_map_eq, ← nhds_prod_eq, tendsto_map'_iff]
  exact H S hS |>.tendsto ⟨y, x'⟩

include hAopen in
/-- A map from `Πʳ i, [R i, A i] × Πʳ i, [R' i, A' i]` is continuous
*iff* its restriction to each `Πʳ i, [R i, A i]_[𝓟 S] × Πʳ i, [R' i, A' i]_[𝓟 S]`
(with `S` cofinite) is continuous.

This is the key result for continuity of multiplication and addition. -/
/-
**RestrictedProduct.continuous_dom_prod** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedPro
duct`。
形式化陈述：continuous_dom_prod {R' : ι -> Type*} {A' : (i : ι) -> Set (R' i)} [forall
 i, TopologicalSpace (R' i)] (hAopen' : forall i, IsOpen (A' i)) {X : Type*} [To
pologicalSpace X] {f : Πʳ i, [R i, A i] × Πʳ i, [R' i, A' i] -> X} : Continuous 
f ↔ forall (S : Set ι) (hS : cofinite <= 𝓟 S), Continuous (f ∘ (Prod.map (inclus
ion R A hS) (inclusion R' A' hS)))
参数：i : ι；R' i；R' i；hAopen' : forall i, IsOpen (A' i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RestrictedProduct.continuous_dom_prod_right`：continuous_dom_prod_right {
X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Πʳ i, [R i, A i] × Y
 -> X} : Continuous f ↔ forall (S…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `RestrictedProduct.continuous_dom_prod_left`：continuous_dom_prod_left {X 
Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Y × Πʳ i, [R i, A i] -
> X} : Continuous f ↔ forall (S …
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `RestrictedProduct.continuous_inclusion`：continuous_inclusion {𝓖 : Filter
 ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R A h)

--- 原说明 ---
A map from `Πʳ i, [R i, A i] × Πʳ i, [R' i, A' i]` is continuous
*iff* its restriction to each `Πʳ i, [R i, A i]_[𝓟 S] × Πʳ i, [R' i, A' i]_[𝓟 S]
`
(with `S` cofinite) is continuous.

This is the key result for continuity of multiplication and addition.
-/
theorem continuous_dom_prod {R' : ι → Type*} {A' : (i : ι) → Set (R' i)}
    [∀ i, TopologicalSpace (R' i)] (hAopen' : ∀ i, IsOpen (A' i))
    {X : Type*} [TopologicalSpace X]
    {f : Πʳ i, [R i, A i] × Πʳ i, [R' i, A' i] → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S),
      Continuous (f ∘ (Prod.map (inclusion R A hS) (inclusion R' A' hS))) := by
  simp_rw [continuous_dom_prod_right hAopen, continuous_dom_prod_left hAopen']
  refine ⟨fun H S hS ↦ H S hS S hS, fun H S hS T hT ↦ ?_⟩
  set U := S ∩ T
  have hU : cofinite ≤ 𝓟 (S ∩ T) := inf_principal ▸ le_inf hS hT
  have hSU : 𝓟 U ≤ 𝓟 S := principal_mono.mpr inter_subset_left
  have hTU : 𝓟 U ≤ 𝓟 T := principal_mono.mpr inter_subset_right
  exact (H U hU).comp ((continuous_inclusion hSU).prodMap (continuous_inclusion hTU))

/-- A finitary (instead of binary) version of `continuous_dom_prod`. -/
/-
**RestrictedProduct.continuous_dom_pi** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProdu
ct`。
形式化陈述：continuous_dom_pi {n : Type*} [Finite n] {X : Type*} [TopologicalSpace X] 
{A : n -> ι -> Type*} [forall j i, TopologicalSpace (A j i)] {C : (j : n) -> (i 
: ι) -> Set (A j i)} (hCopen : forall j i, IsOpen (C j i)) {f : (Π j : n, Πʳ i :
 ι, [A j i, C j i]) -> X} : Continuous f ↔ forall (S : Set ι) (hS : cofinite <= 
𝓟 S), Continuous (f ∘ Pi.map fun _ => inclusion _ _ hS)
参数：A j i；j : n；i : ι；A j i；hCopen : forall j i, IsOpen (C j i)；Π j : n, Πʳ i : ι
, [A j i, C j i]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7}
 [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B 
i)] {f…
· 使用定理 `RestrictedProduct.continuous_inclusion`：continuous_inclusion {𝓖 : Filter
 ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R A h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RestrictedProduct.nhds_eq_map_inclusion`：nhds_eq_map_inclusion {S : Set 
ι} (hS : cofinite <= 𝓟 S) (x : Πʳ i, [R i, A i]_[𝓟 S]) : (𝓝 (inclusion R A hS x)
) = .map (inclusion R A hS) (…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))

--- 原说明 ---
A finitary (instead of binary) version of `continuous_dom_prod`.
-/
theorem continuous_dom_pi {n : Type*} [Finite n] {X : Type*}
    [TopologicalSpace X] {A : n → ι → Type*}
    [∀ j i, TopologicalSpace (A j i)]
    {C : (j : n) → (i : ι) → Set (A j i)}
    (hCopen : ∀ j i, IsOpen (C j i))
    {f : (Π j : n, Πʳ i : ι, [A j i, C j i]) → X} :
    Continuous f ↔
      ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S), Continuous (f ∘ Pi.map fun _ ↦ inclusion _ _ hS) := by
  refine ⟨by fun_prop, fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  intro x
  set S : Set ι := {i | ∀ j, x j i ∈ C j i}
  have hS : cofinite ≤ 𝓟 S := by
    rw [le_principal_iff]
    change ∀ᶠ i in cofinite, ∀ j : n, x j i ∈ C j i
    simp [-eventually_cofinite]
  let x' (j : n) : Πʳ i : ι, [A j i, C j i]_[𝓟 S] := .mk (fun i ↦ x j i) (fun i hi ↦ hi _)
  have hxx' : Pi.map (fun j ↦ inclusion _ _ hS) x' = x := rfl
  simp_rw [← hxx', nhds_pi, Pi.map_apply, nhds_eq_map_inclusion (hCopen _), ← map_piMap_pi_finite,
    tendsto_map'_iff, ← nhds_pi]
  exact (H _ _).tendsto _

end cofinite

end Topology

section Compatibility
/-!
## Compatibility properties between algebra and topology
-/

variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}
variable {T : Set ι} {𝓕 : Filter ι}
variable [Π i, TopologicalSpace (R i)]

section general

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] [∀ i, ContinuousInv (R i)] :
    ContinuousInv (Πʳ i, [R i, B i]_[𝓕]) where
  continuous_inv := by
    rw [continuous_dom]
    intro T hT
    have : ContinuousInv (Πʳ i, [R i, B i]_[𝓟 T]) :=
      isEmbedding_coe_of_principal.continuousInv fun _ ↦ rfl
    exact (continuous_inclusion hT).comp continuous_inv

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousConstSMul G (R i)] :
    ContinuousConstSMul G (Πʳ i, [R i, B i]_[𝓕]) where
  continuous_const_smul g := by
    rw [continuous_dom]
    intro T hT
    have : ContinuousConstSMul G (Πʳ i, [R i, B i]_[𝓟 T]) :=
      isEmbedding_coe_of_principal.continuousConstSMul id rfl
    exact (continuous_inclusion hT).comp (continuous_const_smul g)

end general

section principal

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] [∀ i, ContinuousMul (R i)] :
    ContinuousMul (Πʳ i, [R i, B i]_[𝓟 T]) :=
  let φ : Πʳ i, [R i, B i]_[𝓟 T] →ₙ* Π i, R i :=
  { toFun := (↑)
    map_mul' := fun _ _ ↦ rfl }
  isEmbedding_coe_of_principal.continuousMul φ

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousSMul G (R i)] :
    ContinuousSMul G (Πʳ i, [R i, B i]_[𝓟 T]) :=
  isEmbedding_coe_of_principal.continuousSMul continuous_id rfl

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (Πʳ i, [R i, B i]_[𝓟 T]) where
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (Πʳ i, [R i, B i]_[𝓟 T]) where

end principal

section cofinite

/-
**RestrictedProduct.nhds_zero_eq_map_ofPre** 是 Mathlib 中的一个定理，位于命名空间 `Restricted
Product`。
形式化陈述：nhds_zero_eq_map_ofPre [Π i, Zero (R i)] [forall i, ZeroMemClass (S i) (R 
i)] (hBopen : forall i, IsOpen (B i : Set (R i))) (hT : cofinite <= 𝓟 T) : (𝓝 (i
nclusion R (fun i => B i) hT 0)) = .map (inclusion R (fun i => B i) hT) (𝓝 0)
参数：R i；S i；R i；hBopen : forall i, IsOpen (B i : Set (R i))；hT : cofinite <= 𝓟 T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.nhds_eq_map_inclusion`：nhds_eq_map_inclusion {S : Set 
ι} (hS : cofinite <= 𝓟 S) (x : Πʳ i, [R i, A i]_[𝓟 S]) : (𝓝 (inclusion R A hS x)
) = .map (inclusion R A hS) (…
-/
theorem nhds_zero_eq_map_ofPre [Π i, Zero (R i)] [∀ i, ZeroMemClass (S i) (R i)]
    (hBopen : ∀ i, IsOpen (B i : Set (R i))) (hT : cofinite ≤ 𝓟 T) :
    (𝓝 (inclusion R (fun i ↦ B i) hT 0)) = .map (inclusion R (fun i ↦ B i) hT) (𝓝 0) :=
  nhds_eq_map_inclusion hBopen hT 0
/-
**RestrictedProduct.nhds_zero_eq_map_structureMap** 是 Mathlib 中的一个定理，位于命名空间 `Res
trictedProduct`。
形式化陈述：nhds_zero_eq_map_structureMap [Π i, Zero (R i)] [forall i, ZeroMemClass (S
 i) (R i)] (hBopen : forall i, IsOpen (B i : Set (R i))) : (𝓝 (structureMap R (f
un i => B i) cofinite 0)) = .map (structureMap R (fun i => B i) cofinite) (𝓝 0)
参数：R i；S i；R i；hBopen : forall i, IsOpen (B i : Set (R i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.nhds_eq_map_structureMap`：nhds_eq_map_structureMap (x 
: Π i, A i) : (𝓝 (structureMap R A cofinite x)) = .map (structureMap R A cofinit
e) (𝓝 x)
-/
theorem nhds_zero_eq_map_structureMap [Π i, Zero (R i)] [∀ i, ZeroMemClass (S i) (R i)]
    (hBopen : ∀ i, IsOpen (B i : Set (R i))) :
    (𝓝 (structureMap R (fun i ↦ B i) cofinite 0)) =
      .map (structureMap R (fun i ↦ B i) cofinite) (𝓝 0) :=
  nhds_eq_map_structureMap hBopen 0

-- TODO: Make `IsOpen` a class like `IsClosed` ?
variable [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] [∀ i, ContinuousMul (R i)] :
    ContinuousMul (Πʳ i, [R i, B i]) where
  continuous_mul := by
    rw [continuous_dom_prod hBopen.out hBopen.out]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_mul

@[to_additive]
/-
**RestrictedProduct.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`
。
形式化陈述：continuousSMul {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)] [foral
l i, SMulMemClass (S i) G (R i)] [forall i, ContinuousSMul G (R i)] : Continuous
SMul G (Πʳ i, [R i, B i]) where continuous_smul
参数：R i；S i；R i；R i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RestrictedProduct.continuous_dom_prod_left`：continuous_dom_prod_left {X 
Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Y × Πʳ i, [R i, A i] -
> X} : Continuous f ↔ forall (S …
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `RestrictedProduct.continuous_inclusion`：continuous_inclusion {𝓖 : Filter
 ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R A h)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `RestrictedProduct.instContinuousSMulCoePrincipal`：∀ {ι : Type u_1} (R : 
ι → Type u_2) {S : ι → Type u_3} [inst : (i : ι) → SetLike (S i) (R i)] {B : (i 
: ι) → S i}   {T : Set ι} [inst_1 : (i…
-/
instance continuousSMul {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)]
    [∀ i, SMulMemClass (S i) G (R i)] [∀ i, ContinuousSMul G (R i)] :
    ContinuousSMul G (Πʳ i, [R i, B i]) where
  continuous_smul := by
    rw [continuous_dom_prod_left hBopen.out]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_smul

@[to_additive]
/-
**RestrictedProduct.isTopologicalGroup** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProd
uct`。
形式化陈述：∀ {ι : Type u_1} (R : ι → Type u_2) {S : ι → Type u_3} [inst : (i : ι) → S
etLike (S i) (R i)] {B : (i : ι) → S i}   [inst_1 : (i : ι) → TopologicalSpace (
R i)] [hBopen : Fact (∀ (i : ι), IsOpen ↑(B i))]   [inst_2 : (i : ι) → Group (R 
i)] [inst_3 : ∀ (i : ι), SubgroupClass (S i) (R i)]   [∀ (i : ι), IsTopologicalG
roup (R i)],   IsTopologicalGroup (RestrictedProduct (fun i => R i) (fun i => ↑(
B i)) Filter.cofinite)
参数：R : ι → Type u_2；i : ι；S i；R i；i : ι；i : ι；R i；∀ (i : ι), IsOpen ↑(B i)；i : ι
；R i；i : ι；S i；R i；i : ι；R i；RestrictedProduct (fun i => R i) (fun i => ↑(B i)) 
Filter.cofinite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.instContinuousMulCoeCofinite`：∀ {ι : Type u_1} (R : ι 
→ Type u_2) {S : ι → Type u_3} [inst : (i : ι) → SetLike (S i) (R i)] {B : (i : 
ι) → S i}   [inst_1 : (i : ι) → Topo…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `RestrictedProduct.instContinuousInvCoe`：∀ {ι : Type u_1} (R : ι → Type u
_2) {S : ι → Type u_3} [inst : (i : ι) → SetLike (S i) (R i)] {B : (i : ι) → S i
}   {𝓕 : Filter ι} [inst_1 :…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
instance isTopologicalGroup [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)]
    [∀ i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (Πʳ i, [R i, B i]) where
/-
**RestrictedProduct.isTopologicalRing** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProdu
ct`。
形式化陈述：∀ {ι : Type u_1} (R : ι → Type u_2) {S : ι → Type u_3} [inst : (i : ι) → S
etLike (S i) (R i)] {B : (i : ι) → S i}   [inst_1 : (i : ι) → TopologicalSpace (
R i)] [hBopen : Fact (∀ (i : ι), IsOpen ↑(B i))] [inst_2 : (i : ι) → Ring (R i)]
   [inst_3 : ∀ (i : ι), SubringClass (S i) (R i)] [∀ (i : ι), IsTopologicalRing 
(R i)],   IsTopologicalRing (RestrictedProduct (fun i => R i) (fun i => ↑(B i)) 
Filter.cofinite)
参数：R : ι → Type u_2；i : ι；S i；R i；i : ι；i : ι；R i；∀ (i : ι), IsOpen ↑(B i)；i : ι
；R i；i : ι；S i；R i；i : ι；R i；RestrictedProduct (fun i => R i) (fun i => ↑(B i)) 
Filter.cofinite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.instContinuousAddCoeCofinite`：∀ {ι : Type u_1} (R : ι 
→ Type u_2) {S : ι → Type u_3} [inst : (i : ι) → SetLike (S i) (R i)] {B : (i : 
ι) → S i}   [inst_1 : (i : ι) → Topo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `RestrictedProduct.instContinuousMulCoeCofinite`：∀ {ι : Type u_1} (R : ι 
→ Type u_2) {S : ι → Type u_3} [inst : (i : ι) → SetLike (S i) (R i)] {B : (i : 
ι) → S i}   [inst_1 : (i : ι) → Topo…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `RestrictedProduct.instContinuousNegCoe`：∀ {ι : Type u_1} (R : ι → Type u
_2) {S : ι → Type u_3} [inst : (i : ι) → SetLike (S i) (R i)] {B : (i : ι) → S i
}   {𝓕 : Filter ι} [inst_1 :…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
-/
instance isTopologicalRing [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)]
    [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (Πʳ i, [R i, B i]) where

/-- Assume that each `R i` is a locally compact group with `A i` an open subgroup.
Assume also that all but finitely many `A i`s are compact.
Then the restricted product `Πʳ i, [R i, A i]` is a locally compact group. -/
@[to_additive
/-- Assume that each `R i` is a locally compact additive group with `A i` an open subgroup.
Assume also that all but finitely many `A i`s are compact.
Then the restricted product `Πʳ i, [R i, A i]` is a locally compact additive group. -/]
/-
**RestrictedProduct.locallyCompactSpace_of_group** 是 Mathlib 中的一个定理，位于命名空间 `Rest
rictedProduct`。
形式化陈述：locallyCompactSpace_of_group [Π i, Group (R i)] [forall i, SubgroupClass (
S i) (R i)] [forall i, IsTopologicalGroup (R i)] [forall i, LocallyCompactSpace 
(R i)] (hBcompact : forallᶠ i in cofinite, IsCompact (B i : Set (R i))) : Locall
yCompactSpace (Πʳ i, [R i, B i])
参数：R i；S i；R i；R i；R i；hBcompact : forallᶠ i in cofinite, IsCompact (B i : Set (
R i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `RestrictedProduct.isTopologicalGroup`：∀ {ι : Type u_1} (R : ι → Type u_2
) {S : ι → Type u_3} [inst : (i : ι) → SetLike (S i) (R i)] {B : (i : ι) → S i} 
  [inst_1 : (i : ι) → Topo…
· 使用定理 `RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite`：weaklyLocallyCo
mpactSpace_of_cofinite [forall i, WeaklyLocallyCompactSpace (R i)] (hAcompact : 
forallᶠ i in cofinite, IsCompact (A i)) : Wea…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
-/
theorem locallyCompactSpace_of_group [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)]
    [∀ i, IsTopologicalGroup (R i)] [∀ i, LocallyCompactSpace (R i)]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (R i))) :
    LocallyCompactSpace (Πʳ i, [R i, B i]) :=
  haveI : WeaklyLocallyCompactSpace (Πʳ i, [R i, B i]) :=
    weaklyLocallyCompactSpace_of_cofinite hBopen.out hBcompact
  inferInstance

open scoped Pointwise in
@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)]
    [hAcompact : ∀ i, CompactSpace (B i)] : LocallyCompactSpace (Πʳ i, [R i, B i]) :=
  -- TODO: extract as a lemma
  haveI : ∀ i, WeaklyLocallyCompactSpace (R i) := fun i ↦ .mk fun x ↦
    ⟨x • (B i : Set (R i)), .smul _ (isCompact_iff_compactSpace.mpr inferInstance),
      hBopen.out i |>.smul _ |>.mem_nhds <| by
      simpa using smul_mem_smul_set (a := x) (one_mem (B i))⟩
  locallyCompactSpace_of_group _ <| .of_forall fun _ ↦ isCompact_iff_compactSpace.mpr inferInstance

end cofinite

end Compatibility

section map_continuous

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable [∀ i, TopologicalSpace (R₁ i)] [∀ i, TopologicalSpace (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}
variable (f : ι₂ → ι₁) (hf : Tendsto f 𝓕₂ 𝓕₁)

variable (φ : ∀ j, R₁ (f j) → R₂ j) (hφ : ∀ᶠ j in 𝓕₂, MapsTo (φ j) (A₁ (f j)) (A₂ j))

/-
**RestrictedProduct.mapAlong_continuous** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedPro
duct`。
形式化陈述：mapAlong_continuous (φ_cont : forall j, Continuous (φ j)) : Continuous (ma
pAlong R₁ R₂ f hf φ hφ)
参数：φ_cont : forall j, Continuous (φ j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RestrictedProduct.continuous_dom`：continuous_dom {X : Type*} [Topologica
lSpace X] {f : Πʳ i, [R i, A i]_[𝓕] -> X} : Continuous f ↔ forall (S : Set ι) (h
S : 𝓕 <= 𝓟 S), Continu…
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `RestrictedProduct.continuous_inclusion`：continuous_inclusion {𝓖 : Filter
 ι} (h : 𝓕 <= 𝓖) : Continuous (inclusion R A h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RestrictedProduct.continuous_rng_of_principal`：continuous_rng_of_princip
al {X : Type*} [TopologicalSpace X] {f : X -> Πʳ i, [R i, A i]_[𝓟 S]} : Continuo
us f ↔ Continuous ((↑) ∘ f : X -> Π…
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `RestrictedProduct.continuous_eval`：continuous_eval (i : ι) : Continuous 
(fun (x : Πʳ i, [R i, A i]_[𝓕]) => x i)
-/
theorem mapAlong_continuous (φ_cont : ∀ j, Continuous (φ j)) :
    Continuous (mapAlong R₁ R₂ f hf φ hφ) := by
  rw [continuous_dom]
  intro S hS
  set T := f ⁻¹' S ∩ {j | MapsTo (φ j) (A₁ (f j)) (A₂ j)}
  have hT : 𝓕₂ ≤ 𝓟 T := by
    rw [le_principal_iff] at hS ⊢
    exact inter_mem (hf hS) hφ
  have hf' : Tendsto f (𝓟 T) (𝓟 S) := by aesop
  have hφ' : ∀ᶠ j in 𝓟 T, MapsTo (φ j) (A₁ (f j)) (A₂ j) := by aesop
  have key : mapAlong R₁ R₂ f hf φ hφ ∘ inclusion R₁ A₁ hS =
      inclusion R₂ A₂ hT ∘ mapAlong R₁ R₂ f hf' φ hφ' := rfl
  rw [key]
  exact continuous_inclusion _ |>.comp <|
    continuous_rng_of_principal.mpr <|
    continuous_pi fun j ↦ φ_cont j |>.comp <| continuous_eval (f j)

end map_continuous

end RestrictedProduct

