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

* `RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite`: if each `R i` is weakly locally
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
variable (R : ι -> Type*) (A : (i : ι) -> Set (R i))

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
variable [forall i, TopologicalSpace (R i)]

variable (R A 𝓕) in
/--
Instance `topologicalSpace` / 实例 `topologicalSpace`

English:
instance topologicalSpace
  signature: : TopologicalSpace (Πʳ i, [R i, A i]_[𝓕])
  body: ⨆ (S : Set ι) (hS : 𝓕 <= 𝓟 S), .coinduced (inclusion R A hS)
    (.induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) inferInstance)

@[fun_prop]

中文:
实例 topologicalSpace
  签名: : TopologicalSpace (Πʳ i, [R i, A i]_[𝓕])
  定义体: ⨆ (S : Set ι) (hS : 𝓕 <= 𝓟 S), .coinduced (inclusion R A hS)
    (.induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) inferInstance)

@[fun_prop]

Depends on / 依赖: coinduced, inclusion, induced
-/
instance topologicalSpace : TopologicalSpace (Πʳ i, [R i, A i]_[𝓕]) :=
  ⨆ (S : Set ι) (hS : 𝓕 <= 𝓟 S), .coinduced (inclusion R A hS)
    (.induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) inferInstance)

@[fun_prop]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  proof: continuous_iSup_dom.mpr fun _ => continuous_iSup_dom.mpr fun _ =>
    continuous_coinduced_dom.mpr continuous_induced_dom

@[fun_prop]

中文:
定理 continuous_coe
  证明: continuous_iSup_dom.mpr fun _ => continuous_iSup_dom.mpr fun _ =>
    continuous_coinduced_dom.mpr continuous_induced_dom

@[fun_prop]

Depends on / 依赖: continuous_coinduced_dom, continuous_coinduced_dom.mpr, continuous_iSup_dom, continuous_iSup_dom.mpr, continuous_induced_dom
-/
theorem continuous_coe :
    Continuous ((↑) : Πʳ i, [R i, A i]_[𝓕] -> Π i, R i) :=
  continuous_iSup_dom.mpr fun _ => continuous_iSup_dom.mpr fun _ =>
    continuous_coinduced_dom.mpr continuous_induced_dom

@[fun_prop]
/--
theorem `continuous_eval` / 定理 `continuous_eval`

English:
theorem continuous_eval
  given: (i : ι)
  proof: .comp continuous_coe continuous_apply _

@[fun_prop]

中文:
定理 continuous_eval
  条件: (i : ι)
  证明: .comp continuous_coe continuous_apply _

@[fun_prop]

Depends on / 依赖: continuous_apply, continuous_coe
-/
theorem continuous_eval (i : ι) :
    Continuous (fun (x : Πʳ i, [R i, A i]_[𝓕]) => x i) :=
.comp continuous_coe continuous_apply _

@[fun_prop]
/--
theorem `continuous_inclusion` / 定理 `continuous_inclusion`

English:
theorem continuous_inclusion
  given: {𝓖 : Filter ι} (h : 𝓕 <= 𝓖)
  proof: by
  simp_rw [continuous_iff_coinduced_le, topologicalSpace, coinduced_iSup, coinduced_compose]
  exact iSup₂_le fun S hS => le_iSup₂_of_le S (le_trans h hS) le_rfl

中文:
定理 continuous_inclusion
  条件: {𝓖 : Filter ι} (h : 𝓕 <= 𝓖)
  证明: by
  simp_rw [continuous_iff_coinduced_le, topologicalSpace, coinduced_iSup, coinduced_compose]
  exact iSup₂_le fun S hS => le_iSup₂_of_le S (le_trans h hS) le_rfl

Depends on / 依赖: coinduced_compose, coinduced_iSup, continuous_iff_coinduced_le, le_rfl, le_trans, simp_rw, topologicalSpace
-/
theorem continuous_inclusion {𝓖 : Filter ι} (h : 𝓕 <= 𝓖) :
    Continuous (inclusion R A h) := by
  simp_rw [continuous_iff_coinduced_le, topologicalSpace, coinduced_iSup, coinduced_compose]
  exact iSup₂_le fun S hS => le_iSup₂_of_le S (le_trans h hS) le_rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, T0Space (R i)] : T0Space (Πʳ i, [R i, A i]_[𝓕])
  body: t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe

中文:
实例 [forall
  签名: i, T0Space (R i)] : T0Space (Πʳ i, [R i, A i]_[𝓕])
  定义体: t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, continuous_coe, t0Space_of_injective_of_continuous
-/
instance [forall i, T0Space (R i)] : T0Space (Πʳ i, [R i, A i]_[𝓕]) :=
  t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, T1Space (R i)] : T1Space (Πʳ i, [R i, A i]_[𝓕])
  body: t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe

中文:
实例 [forall
  签名: i, T1Space (R i)] : T1Space (Πʳ i, [R i, A i]_[𝓕])
  定义体: t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, continuous_coe, t1Space_of_injective_of_continuous
-/
instance [forall i, T1Space (R i)] : T1Space (Πʳ i, [R i, A i]_[𝓕]) :=
  t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, T2Space (R i)] : T2Space (Πʳ i, [R i, A i]_[𝓕])
  body: .of_injective_continuous DFunLike.coe_injective continuous_coe

中文:
实例 [forall
  签名: i, T2Space (R i)] : T2Space (Πʳ i, [R i, A i]_[𝓕])
  定义体: .of_injective_continuous DFunLike.coe_injective continuous_coe

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, continuous_coe, of_injective_continuous
-/
instance [forall i, T2Space (R i)] : T2Space (Πʳ i, [R i, A i]_[𝓕]) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coe

section principal
/-!
### Topological facts in the principal case
-/

variable {S : Set ι}

/--
theorem `topologicalSpace_eq_of_principal` / 定理 `topologicalSpace_eq_of_principal`

English:
theorem topologicalSpace_eq_of_principal
  proof: le_antisymm (continuous_iff_le_induced.mp continuous_coe)
    (le_iSup₂_of_le S le_rfl <| by rw [inclusion_eq_id R A (𝓟 S), @coinduced_id])

中文:
定理 topologicalSpace_eq_of_principal
  证明: le_antisymm (continuous_iff_le_induced.mp continuous_coe)
    (le_iSup₂_of_le S le_rfl <| by rw [inclusion_eq_id R A (𝓟 S), @coinduced_id])

Depends on / 依赖: coinduced_id, continuous_coe, continuous_iff_le_induced, continuous_iff_le_induced.mp, inclusion_eq_id, le_antisymm, le_rfl
-/
theorem topologicalSpace_eq_of_principal :
    topologicalSpace R A (𝓟 S) =
      .induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) inferInstance :=
le_antisymm (continuous_iff_le_induced.mp continuous_coe)
    (le_iSup₂_of_le S le_rfl <| by rw [inclusion_eq_id R A (𝓟 S), @coinduced_id])

/--
theorem `topologicalSpace_eq_of_top` / 定理 `topologicalSpace_eq_of_top`

English:
theorem topologicalSpace_eq_of_top
  proof: principal_univ ▸ topologicalSpace_eq_of_principal

中文:
定理 topologicalSpace_eq_of_top
  证明: principal_univ ▸ topologicalSpace_eq_of_principal

Depends on / 依赖: principal_univ, topologicalSpace_eq_of_principal
-/
theorem topologicalSpace_eq_of_top :
    topologicalSpace R A ⊤ =
      .induced ((↑) : Πʳ i, [R i, A i]_[⊤] -> Π i, R i) inferInstance :=
  principal_univ ▸ topologicalSpace_eq_of_principal

/--
theorem `topologicalSpace_eq_of_bot` / 定理 `topologicalSpace_eq_of_bot`

English:
theorem topologicalSpace_eq_of_bot
  proof: principal_empty ▸ topologicalSpace_eq_of_principal

中文:
定理 topologicalSpace_eq_of_bot
  证明: principal_empty ▸ topologicalSpace_eq_of_principal

Depends on / 依赖: principal_empty, topologicalSpace_eq_of_principal
-/
theorem topologicalSpace_eq_of_bot :
    topologicalSpace R A ⊥ =
      .induced ((↑) : Πʳ i, [R i, A i]_[⊥] -> Π i, R i) inferInstance :=
  principal_empty ▸ topologicalSpace_eq_of_principal

/--
theorem `isEmbedding_coe_of_principal` / 定理 `isEmbedding_coe_of_principal`

English:
theorem isEmbedding_coe_of_principal
  proof: topologicalSpace_eq_of_principal
  injective := DFunLike.coe_injective

中文:
定理 isEmbedding_coe_of_principal
  证明: topologicalSpace_eq_of_principal
  injective := DFunLike.coe_injective

Depends on / 依赖: topologicalSpace_eq_of_principal
-/
theorem isEmbedding_coe_of_principal :
    IsEmbedding ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) where
  eq_induced := topologicalSpace_eq_of_principal
  injective := DFunLike.coe_injective

/--
theorem `isEmbedding_coe_of_top` / 定理 `isEmbedding_coe_of_top`

English:
theorem isEmbedding_coe_of_top
  proof: principal_univ ▸ isEmbedding_coe_of_principal

中文:
定理 isEmbedding_coe_of_top
  证明: principal_univ ▸ isEmbedding_coe_of_principal

Depends on / 依赖: isEmbedding_coe_of_principal, principal_univ
-/
theorem isEmbedding_coe_of_top :
    IsEmbedding ((↑) : Πʳ i, [R i, A i]_[⊤] -> Π i, R i) :=
  principal_univ ▸ isEmbedding_coe_of_principal

/--
theorem `isEmbedding_coe_of_bot` / 定理 `isEmbedding_coe_of_bot`

English:
theorem isEmbedding_coe_of_bot
  proof: principal_empty ▸ isEmbedding_coe_of_principal

中文:
定理 isEmbedding_coe_of_bot
  证明: principal_empty ▸ isEmbedding_coe_of_principal

Depends on / 依赖: isEmbedding_coe_of_principal, principal_empty
-/
theorem isEmbedding_coe_of_bot :
    IsEmbedding ((↑) : Πʳ i, [R i, A i]_[⊥] -> Π i, R i) :=
  principal_empty ▸ isEmbedding_coe_of_principal

/--
theorem `continuous_rng_of_principal` / 定理 `continuous_rng_of_principal`

English:
theorem continuous_rng_of_principal
  statement: {X : Type*} [TopologicalSpace X]
  proof: isEmbedding_coe_of_principal.continuous_iff

中文:
定理 continuous_rng_of_principal
  结论: {X : 类型} [TopologicalSpace X]
  证明: isEmbedding_coe_of_principal.continuous_iff

Depends on / 依赖: continuous_iff, isEmbedding_coe_of_principal, isEmbedding_coe_of_principal.continuous_iff
-/
theorem continuous_rng_of_principal {X : Type*} [TopologicalSpace X]
    {f : X -> Πʳ i, [R i, A i]_[𝓟 S]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X -> Π i, R i) :=
  isEmbedding_coe_of_principal.continuous_iff

/--
theorem `continuous_rng_of_top` / 定理 `continuous_rng_of_top`

English:
theorem continuous_rng_of_top
  statement: {X : Type*} [TopologicalSpace X]
  proof: isEmbedding_coe_of_top.continuous_iff

中文:
定理 continuous_rng_of_top
  结论: {X : 类型} [TopologicalSpace X]
  证明: isEmbedding_coe_of_top.continuous_iff

Depends on / 依赖: continuous_iff, isEmbedding_coe_of_top, isEmbedding_coe_of_top.continuous_iff
-/
theorem continuous_rng_of_top {X : Type*} [TopologicalSpace X]
    {f : X -> Πʳ i, [R i, A i]_[⊤]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X -> Π i, R i) :=
  isEmbedding_coe_of_top.continuous_iff

/--
theorem `continuous_rng_of_bot` / 定理 `continuous_rng_of_bot`

English:
theorem continuous_rng_of_bot
  statement: {X : Type*} [TopologicalSpace X]
  proof: isEmbedding_coe_of_bot.continuous_iff

中文:
定理 continuous_rng_of_bot
  结论: {X : 类型} [TopologicalSpace X]
  证明: isEmbedding_coe_of_bot.continuous_iff

Depends on / 依赖: continuous_iff, isEmbedding_coe_of_bot, isEmbedding_coe_of_bot.continuous_iff
-/
theorem continuous_rng_of_bot {X : Type*} [TopologicalSpace X]
    {f : X -> Πʳ i, [R i, A i]_[⊥]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X -> Π i, R i) :=
  isEmbedding_coe_of_bot.continuous_iff

/--
lemma `continuous_rng_of_principal_iff_forall` / 引理 `continuous_rng_of_principal_iff_forall`

English:
lemma continuous_rng_of_principal_iff_forall
  statement: {X : Type*} [TopologicalSpace X]
  proof: continuous_rng_of_principal.trans continuous_pi_iff

中文:
引理 continuous_rng_of_principal_iff_forall
  结论: {X : 类型} [TopologicalSpace X]
  证明: continuous_rng_of_principal.trans continuous_pi_iff

Depends on / 依赖: continuous_pi_iff, continuous_rng_of_principal, continuous_rng_of_principal.trans
-/
lemma continuous_rng_of_principal_iff_forall {X : Type*} [TopologicalSpace X]
    {f : X -> Πʳ (i : ι), [R i, A i]_[𝓟 S]} :
    Continuous f ↔ forall i : ι, Continuous ((fun x => x i) ∘ f) :=
  continuous_rng_of_principal.trans continuous_pi_iff

/--
Definition of `homeoTop` / `homeoTop` 的定义

English:
definition homeoTop
  signature: : (Π i, A i) ≃ₜ (Πʳ i, [R i, A i]_[⊤]) where
  body: ⟨fun i => f i, fun i => (f i).2⟩
  invFun f i := ⟨f i, f.2 i⟩
continuous_toFun := continuous_rng_of_top.mpr continuous_pi fun i =>
continuous_subtype_val.comp continuous_apply i
continuous_invFun := continuous_pi fun i => continuous_induced_rng.mpr continuous_eval i

中文:
定义 homeoTop
  签名: : (Π i, A i) ≃ₜ (Πʳ i, [R i, A i]_[⊤]) where
  定义体: ⟨fun i => f i, fun i => (f i).2⟩
  invFun f i := ⟨f i, f.2 i⟩
continuous_toFun := continuous_rng_of_top.mpr continuous_pi fun i =>
continuous_subtype_val.comp continuous_apply i
continuous_invFun := continuous_pi fun i => continuous_induced_rng.mpr continuous_eval i
-/
def homeoTop : (Π i, A i) ≃ₜ (Πʳ i, [R i, A i]_[⊤]) where
  toFun f := ⟨fun i => f i, fun i => (f i).2⟩
  invFun f i := ⟨f i, f.2 i⟩
continuous_toFun := continuous_rng_of_top.mpr continuous_pi fun i =>
continuous_subtype_val.comp continuous_apply i
continuous_invFun := continuous_pi fun i => continuous_induced_rng.mpr continuous_eval i

/--
Definition of `homeoBot` / `homeoBot` 的定义

English:
definition homeoBot
  signature: : (Π i, R i) ≃ₜ (Πʳ i, [R i, A i]_[⊥]) where
  body: ⟨fun i => f i, eventually_bot⟩
  invFun f i := f i
continuous_toFun := continuous_rng_of_bot.mpr continuous_pi fun i => continuous_apply i
  continuous_invFun := continuous_pi continuous_eval

中文:
定义 homeoBot
  签名: : (Π i, R i) ≃ₜ (Πʳ i, [R i, A i]_[⊥]) where
  定义体: ⟨fun i => f i, eventually_bot⟩
  invFun f i := f i
continuous_toFun := continuous_rng_of_bot.mpr continuous_pi fun i => continuous_apply i
  continuous_invFun := continuous_pi continuous_eval

Depends on / 依赖: eventually_bot
-/
def homeoBot : (Π i, R i) ≃ₜ (Πʳ i, [R i, A i]_[⊥]) where
  toFun f := ⟨fun i => f i, eventually_bot⟩
  invFun f i := f i
continuous_toFun := continuous_rng_of_bot.mpr continuous_pi fun i => continuous_apply i
  continuous_invFun := continuous_pi continuous_eval

/--
theorem `weaklyLocallyCompactSpace_of_principal` / 定理 `weaklyLocallyCompactSpace_of_principal`

English:
theorem weaklyLocallyCompactSpace_of_principal
  statement: [forall i, WeaklyLocallyCompactSpace (R i)]
  proof: fun x => by
    rw [le_principal_iff]; rw [mem_cofinite] at hS
    classical
    have : forall i, exists K, IsCompact K ∧ K in 𝓝 (x i) := fun i => exists_compact_mem_nhds (x i)
    choose K K_compact hK using this
    set Q : Set (Π i, R i) := univ.pi (fun i => if i in S then A i else K i) with Q_de

中文:
定理 weaklyLocallyCompactSpace_of_principal
  结论: [对任意 i, WeaklyLocallyCompactSpace (R i)]
  证明: fun x => by
    rw [le_principal_iff]; rw [mem_cofinite] at hS
    classical
    have : forall i, exists K, IsCompact K ∧ K in 𝓝 (x i) := fun i => exists_compact_mem_nhds (x i)
    choose K K_compact hK using this
    set Q : Set (Π i, R i) := univ.pi (fun i => if i in S then A i else K i) with Q_de

Depends on / 依赖: IsCompact, K_compact, Q_compact, Q_def, U_nhds, classical, exists_compact_mem_nhds, hAcompact, isCompact_univ_pi, le_principal_iff, mem_cofinite, set_pi_mem_nhds, split_ifs, univ.pi
-/
theorem weaklyLocallyCompactSpace_of_principal [forall i, WeaklyLocallyCompactSpace (R i)]
    (hS : cofinite <= 𝓟 S) (hAcompact : forall i in S, IsCompact (A i)) :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]_[𝓟 S]) where
  exists_compact_mem_nhds := fun x => by
    rw [le_principal_iff]; rw [mem_cofinite] at hS
    classical
    have : forall i, exists K, IsCompact K ∧ K in 𝓝 (x i) := fun i => exists_compact_mem_nhds (x i)
    choose K K_compact hK using this
    set Q : Set (Π i, R i) := univ.pi (fun i => if i in S then A i else K i) with Q_def
    have Q_compact : IsCompact Q := isCompact_univ_pi fun i => by
      split_ifs with his
      · exact hAcompact i his
      · exact K_compact i
    set U : Set (Π i, R i) := Sᶜ.pi K
    have U_nhds : U in 𝓝 (x : Π i, R i) := set_pi_mem_nhds hS fun i _ => hK i
    have QU : (↑) ⁻¹' U subseteq ((↑) ⁻¹' Q : Set (Πʳ i, [R i, A i]_[𝓟 S])) := fun y H i _ => by
      dsimp only
      split_ifs with hi
      · exact y.2 hi
      · exact H i hi
    refine ⟨((↑) ⁻¹' Q), ?_, mem_of_superset ?_ QU⟩
.mpr Q_compact · refine isEmbedding_coe_of_principal.isCompact_preimage_iff ?_
      simp_rw [range_coe_principal, Q_def, pi_if, mem_univ, true_and]
      exact inter_subset_left
    · simpa only [isEmbedding_coe_of_principal.nhds_eq_comap] using preimage_mem_comap U_nhds

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, WeaklyLocallyCompactSpace (R i)] [hS
  body: weaklyLocallyCompactSpace_of_principal hS.out
    fun _ _ => isCompact_iff_compactSpace.mpr inferInstance

中文:
实例 [forall
  签名: i, WeaklyLocallyCompactSpace (R i)] [hS
  定义体: weaklyLocallyCompactSpace_of_principal hS.out
    fun _ _ => isCompact_iff_compactSpace.mpr inferInstance

Depends on / 依赖: hS.out, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mpr, weaklyLocallyCompactSpace_of_principal
-/
instance [forall i, WeaklyLocallyCompactSpace (R i)] [hS : Fact (cofinite <= 𝓟 S)]
    [hAcompact : forall i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]_[𝓟 S]) :=
  weaklyLocallyCompactSpace_of_principal hS.out
    fun _ _ => isCompact_iff_compactSpace.mpr inferInstance

end principal

section general
/-!
### Topological facts in the general case
-/

variable (𝓕) in
/--
theorem `topologicalSpace_eq_iSup` / 定理 `topologicalSpace_eq_iSup`

English:
theorem topologicalSpace_eq_iSup
  proof: by
  simp_rw [topologicalSpace_eq_of_principal, topologicalSpace]

中文:
定理 topologicalSpace_eq_iSup
  证明: by
  simp_rw [topologicalSpace_eq_of_principal, topologicalSpace]

Depends on / 依赖: simp_rw, topologicalSpace, topologicalSpace_eq_of_principal
-/
theorem topologicalSpace_eq_iSup :
    topologicalSpace R A 𝓕 = ⨆ (S : Set ι) (hS : 𝓕 <= 𝓟 S),
      .coinduced (inclusion R A hS) (topologicalSpace R A (𝓟 S)) := by
  simp_rw [topologicalSpace_eq_of_principal, topologicalSpace]

/--
theorem `continuous_dom` / 定理 `continuous_dom`

English:
theorem continuous_dom
  statement: {X : Type*} [TopologicalSpace X]
  proof: by
  simp_rw +instances [topologicalSpace_eq_of_principal, continuous_iSup_dom,
    continuous_coinduced_dom]

中文:
定理 continuous_dom
  结论: {X : 类型} [TopologicalSpace X]
  证明: by
  simp_rw +instances [topologicalSpace_eq_of_principal, continuous_iSup_dom,
    continuous_coinduced_dom]

Depends on / 依赖: continuous_coinduced_dom, continuous_iSup_dom, instances, simp_rw, topologicalSpace_eq_of_principal
-/
theorem continuous_dom {X : Type*} [TopologicalSpace X]
    {f : Πʳ i, [R i, A i]_[𝓕] -> X} :
    Continuous f ↔ forall (S : Set ι) (hS : 𝓕 <= 𝓟 S), Continuous (f ∘ inclusion R A hS) := by
  simp_rw +instances [topologicalSpace_eq_of_principal, continuous_iSup_dom,
    continuous_coinduced_dom]

/--
theorem `isEmbedding_inclusion_principal` / 定理 `isEmbedding_inclusion_principal`

English:
theorem isEmbedding_inclusion_principal
  given: {S : Set ι} (hS : 𝓕 <= 𝓟 S)
  proof: .of_comp (continuous_inclusion hS) continuous_coe isEmbedding_coe_of_principal

中文:
定理 isEmbedding_inclusion_principal
  条件: {S : Set ι} (hS : 𝓕 <= 𝓟 S)
  证明: .of_comp (continuous_inclusion hS) continuous_coe isEmbedding_coe_of_principal

Depends on / 依赖: continuous_coe, continuous_inclusion, isEmbedding_coe_of_principal, of_comp
-/
theorem isEmbedding_inclusion_principal {S : Set ι} (hS : 𝓕 <= 𝓟 S) :
    IsEmbedding (inclusion R A hS) :=
  .of_comp (continuous_inclusion hS) continuous_coe isEmbedding_coe_of_principal

/--
theorem `isEmbedding_inclusion_top` / 定理 `isEmbedding_inclusion_top`

English:
theorem isEmbedding_inclusion_top
  proof: .of_comp (continuous_inclusion _) continuous_coe isEmbedding_coe_of_top

中文:
定理 isEmbedding_inclusion_top
  证明: .of_comp (continuous_inclusion _) continuous_coe isEmbedding_coe_of_top

Depends on / 依赖: continuous_coe, continuous_inclusion, isEmbedding_coe_of_top, of_comp
-/
theorem isEmbedding_inclusion_top :
    IsEmbedding (inclusion R A (le_top : 𝓕 <= ⊤)) :=
  .of_comp (continuous_inclusion _) continuous_coe isEmbedding_coe_of_top

/--
theorem `isEmbedding_structureMap` / 定理 `isEmbedding_structureMap`

English:
theorem isEmbedding_structureMap
  proof: isEmbedding_inclusion_top.comp homeoTop.isEmbedding

中文:
定理 isEmbedding_structureMap
  证明: isEmbedding_inclusion_top.comp homeoTop.isEmbedding

Depends on / 依赖: homeoTop, homeoTop.isEmbedding, isEmbedding, isEmbedding_inclusion_top, isEmbedding_inclusion_top.comp
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

variable (hAopen : forall i, IsOpen (A i))

include hAopen in
/--
theorem `isOpen_forall_imp_mem_of_principal` / 定理 `isOpen_forall_imp_mem_of_principal`

English:
theorem isOpen_forall_imp_mem_of_principal
  given: {S : Set ι} (hS : cofinite <= 𝓟 S) {p : ι -> Prop}
  proof: by
  rw [le_principal_iff] at hS
  convert!
.preimage continuous_coe isOpen_set_pi (hS.inter_of_left {i | p i}) (fun i _ => hAopen i)
  ext f
  refine ⟨fun H i hi => H i hi.2, fun H i hiT => ?_⟩
  by_cases hiS : i in S
  · exact f.2 hiS
  · exact H i ⟨hiS, hiT⟩

include hAopen in

中文:
定理 isOpen_forall_imp_mem_of_principal
  条件: {S : Set ι} (hS : cofinite <= 𝓟 S) {p : ι -> 命题}
  证明: by
  rw [le_principal_iff] at hS
  convert!
.preimage continuous_coe isOpen_set_pi (hS.inter_of_left {i | p i}) (fun i _ => hAopen i)
  ext f
  refine ⟨fun H i hi => H i hi.2, fun H i hiT => ?_⟩
  by_cases hiS : i in S
  · exact f.2 hiS
  · exact H i ⟨hiS, hiT⟩

include hAopen in

Depends on / 依赖: continuous_coe, convert, hAopen, hS.inter_of_left, inter_of_left, isOpen_set_pi, le_principal_iff, preimage
-/
theorem isOpen_forall_imp_mem_of_principal {S : Set ι} (hS : cofinite <= 𝓟 S) {p : ι -> Prop} :
    IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S] | forall i, p i -> f.1 i in A i} := by
  rw [le_principal_iff] at hS
  convert!
.preimage continuous_coe isOpen_set_pi (hS.inter_of_left {i | p i}) (fun i _ => hAopen i)
  ext f
  refine ⟨fun H i hi => H i hi.2, fun H i hiT => ?_⟩
  by_cases hiS : i in S
  · exact f.2 hiS
  · exact H i ⟨hiS, hiT⟩

include hAopen in
/--
theorem `isOpen_forall_mem_of_principal` / 定理 `isOpen_forall_mem_of_principal`

English:
theorem isOpen_forall_mem_of_principal
  given: {S : Set ι} (hS : cofinite <= 𝓟 S)
  proof: by
  convert! isOpen_forall_imp_mem_of_principal hAopen hS (p := fun _ => True)
  simp

include hAopen in

中文:
定理 isOpen_forall_mem_of_principal
  条件: {S : Set ι} (hS : cofinite <= 𝓟 S)
  证明: by
  convert! isOpen_forall_imp_mem_of_principal hAopen hS (p := fun _ => True)
  simp

include hAopen in

Depends on / 依赖: convert, hAopen, isOpen_forall_imp_mem_of_principal
-/
theorem isOpen_forall_mem_of_principal {S : Set ι} (hS : cofinite <= 𝓟 S) :
    IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S] | forall i, f.1 i in A i} := by
  convert! isOpen_forall_imp_mem_of_principal hAopen hS (p := fun _ => True)
  simp

include hAopen in
/--
theorem `isOpen_forall_imp_mem` / 定理 `isOpen_forall_imp_mem`

English:
theorem isOpen_forall_imp_mem
  given: {p : ι -> Prop}
  proof: by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS => isOpen_forall_imp_mem_of_principal hAopen hS

include hAopen in

中文:
定理 isOpen_forall_imp_mem
  条件: {p : ι -> 命题}
  证明: by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS => isOpen_forall_imp_mem_of_principal hAopen hS

include hAopen in

Depends on / 依赖: cofinite, hAopen, instances, isOpen_coinduced, isOpen_forall_imp_mem_of_principal, isOpen_iSup_iff, simp_rw, topologicalSpace_eq_iSup
-/
theorem isOpen_forall_imp_mem {p : ι -> Prop} :
    IsOpen {f : Πʳ i, [R i, A i] | forall i, p i -> f.1 i in A i} := by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS => isOpen_forall_imp_mem_of_principal hAopen hS

include hAopen in
/--
theorem `isOpen_forall_mem` / 定理 `isOpen_forall_mem`

English:
theorem isOpen_forall_mem
  proof: by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS => isOpen_forall_mem_of_principal hAopen hS

include hAopen in

中文:
定理 isOpen_forall_mem
  证明: by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS => isOpen_forall_mem_of_principal hAopen hS

include hAopen in

Depends on / 依赖: cofinite, hAopen, instances, isOpen_coinduced, isOpen_forall_mem_of_principal, isOpen_iSup_iff, simp_rw, topologicalSpace_eq_iSup
-/
theorem isOpen_forall_mem :
    IsOpen {f : Πʳ i, [R i, A i] | forall i, f.1 i in A i} := by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS => isOpen_forall_mem_of_principal hAopen hS

include hAopen in
/--
theorem `isOpenEmbedding_inclusion_principal` / 定理 `isOpenEmbedding_inclusion_principal`

English:
theorem isOpenEmbedding_inclusion_principal
  given: {S : Set ι} (hS : cofinite <= 𝓟 S)
  proof: isEmbedding_inclusion_principal hS
  isOpen_range := by
    rw [range_inclusion]
    exact isOpen_forall_imp_mem hAopen

include hAopen in

中文:
定理 isOpenEmbedding_inclusion_principal
  条件: {S : Set ι} (hS : cofinite <= 𝓟 S)
  证明: isEmbedding_inclusion_principal hS
  isOpen_range := by
    rw [range_inclusion]
    exact isOpen_forall_imp_mem hAopen

include hAopen in

Depends on / 依赖: isEmbedding_inclusion_principal
-/
theorem isOpenEmbedding_inclusion_principal {S : Set ι} (hS : cofinite <= 𝓟 S) :
    IsOpenEmbedding (inclusion R A hS) where
  toIsEmbedding := isEmbedding_inclusion_principal hS
  isOpen_range := by
    rw [range_inclusion]
    exact isOpen_forall_imp_mem hAopen

include hAopen in
/--
theorem `isOpenEmbedding_structureMap` / 定理 `isOpenEmbedding_structureMap`

English:
theorem isOpenEmbedding_structureMap
  proof: isEmbedding_structureMap
  isOpen_range := by
    rw [range_structureMap]
    exact isOpen_forall_mem hAopen

include hAopen in

中文:
定理 isOpenEmbedding_structureMap
  证明: isEmbedding_structureMap
  isOpen_range := by
    rw [range_structureMap]
    exact isOpen_forall_mem hAopen

include hAopen in

Depends on / 依赖: isEmbedding_structureMap
-/
theorem isOpenEmbedding_structureMap :
    IsOpenEmbedding (structureMap R A cofinite) where
  toIsEmbedding := isEmbedding_structureMap
  isOpen_range := by
    rw [range_structureMap]
    exact isOpen_forall_mem hAopen

include hAopen in
/--
theorem `nhds_eq_map_inclusion` / 定理 `nhds_eq_map_inclusion`

English:
theorem nhds_eq_map_inclusion
  statement: {S : Set ι} (hS : cofinite <= 𝓟 S)
  proof: by
  rw [isOpenEmbedding_inclusion_principal hAopen hS |>.map_nhds_eq x]

include hAopen in

中文:
定理 nhds_eq_map_inclusion
  结论: {S : Set ι} (hS : cofinite <= 𝓟 S)
  证明: by
  rw [isOpenEmbedding_inclusion_principal hAopen hS |>.map_nhds_eq x]

include hAopen in

Depends on / 依赖: hAopen, isOpenEmbedding_inclusion_principal, map_nhds_eq
-/
theorem nhds_eq_map_inclusion {S : Set ι} (hS : cofinite <= 𝓟 S)
    (x : Πʳ i, [R i, A i]_[𝓟 S]) :
    (𝓝 (inclusion R A hS x)) = .map (inclusion R A hS) (𝓝 x) := by
  rw [isOpenEmbedding_inclusion_principal hAopen hS |>.map_nhds_eq x]

include hAopen in
/--
theorem `nhds_eq_map_structureMap` / 定理 `nhds_eq_map_structureMap`

English:
theorem nhds_eq_map_structureMap
  proof: by
  rw [isOpenEmbedding_structureMap hAopen |>.map_nhds_eq x]

include hAopen in

中文:
定理 nhds_eq_map_structureMap
  证明: by
  rw [isOpenEmbedding_structureMap hAopen |>.map_nhds_eq x]

include hAopen in

Depends on / 依赖: hAopen, isOpenEmbedding_structureMap, map_nhds_eq
-/
theorem nhds_eq_map_structureMap
    (x : Π i, A i) :
    (𝓝 (structureMap R A cofinite x)) = .map (structureMap R A cofinite) (𝓝 x) := by
  rw [isOpenEmbedding_structureMap hAopen |>.map_nhds_eq x]

include hAopen in
/--
theorem `weaklyLocallyCompactSpace_of_cofinite` / 定理 `weaklyLocallyCompactSpace_of_cofinite`

English:
theorem weaklyLocallyCompactSpace_of_cofinite
  statement: [forall i, WeaklyLocallyCompactSpace (R i)]
  proof: fun x => by
    set S := {i | IsCompact (A i) ∧ x i in A i}
    have hS : cofinite <= 𝓟 S := le_principal_iff.mpr (hAcompact.and x.2)
    have hSx : forall i in S, x i in A i := fun i hi => hi.2
    have hSA : forall i in S, IsCompact (A i) := fun i hi => hi.1
    have := weaklyLocallyCompactSpace_o

中文:
定理 weaklyLocallyCompactSpace_of_cofinite
  结论: [对任意 i, WeaklyLocallyCompactSpace (R i)]
  证明: fun x => by
    set S := {i | IsCompact (A i) ∧ x i in A i}
    have hS : cofinite <= 𝓟 S := le_principal_iff.mpr (hAcompact.and x.2)
    have hSx : forall i in S, x i in A i := fun i hi => hi.2
    have hSA : forall i in S, IsCompact (A i) := fun i hi => hi.1
    have := weaklyLocallyCompactSpace_o

Depends on / 依赖: IsCompact, K_compact, cofinite, exists_compact_mem_nhds, exists_inclusion_eq_of_eventually, hAcompact, hAcompact.and, hAopen, inclusion, le_principal_iff, le_principal_iff.mpr, nhds_eq_map_inclusion, weaklyLocallyCompactSpace_of_principal
-/
theorem weaklyLocallyCompactSpace_of_cofinite [forall i, WeaklyLocallyCompactSpace (R i)]
    (hAcompact : forallᶠ i in cofinite, IsCompact (A i)) :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]) where
  exists_compact_mem_nhds := fun x => by
    set S := {i | IsCompact (A i) ∧ x i in A i}
    have hS : cofinite <= 𝓟 S := le_principal_iff.mpr (hAcompact.and x.2)
    have hSx : forall i in S, x i in A i := fun i hi => hi.2
    have hSA : forall i in S, IsCompact (A i) := fun i hi => hi.1
    have := weaklyLocallyCompactSpace_of_principal hS hSA
    rcases exists_inclusion_eq_of_eventually R A hS hSx with ⟨x', hxx'⟩
    rw [← hxx']; rw [nhds_eq_map_inclusion hAopen]
    rcases exists_compact_mem_nhds x' with ⟨K, K_compact, hK⟩
    exact ⟨inclusion R A hS '' K, K_compact.image (continuous_inclusion hS), image_mem_map hK⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hAopen
  signature: : Fact (forall i, IsOpen (A i))] [forall i, WeaklyLocallyCompactSpace (R i)]
  body: weaklyLocallyCompactSpace_of_cofinite hAopen.out
    .of_forall fun _ => isCompact_iff_compactSpace.mpr inferInstance

include hAopen in

中文:
实例 [hAopen
  签名: : Fact (对任意 i, IsOpen (A i))] [对任意 i, WeaklyLocallyCompactSpace (R i)]
  定义体: weaklyLocallyCompactSpace_of_cofinite hAopen.out
    .of_forall fun _ => isCompact_iff_compactSpace.mpr inferInstance

include hAopen in

Depends on / 依赖: hAopen, hAopen.out, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mpr, of_forall, weaklyLocallyCompactSpace_of_cofinite
-/
instance [hAopen : Fact (forall i, IsOpen (A i))] [forall i, WeaklyLocallyCompactSpace (R i)]
    [hAcompact : forall i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]) :=
weaklyLocallyCompactSpace_of_cofinite hAopen.out
    .of_forall fun _ => isCompact_iff_compactSpace.mpr inferInstance

include hAopen in
/--
theorem `continuous_dom_prod_right` / 定理 `continuous_dom_prod_right`

English:
theorem continuous_dom_prod_right
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  proof: by
  refine ⟨fun H S hS => H.comp ((continuous_inclusion hS).prodMap continuous_id),
    fun H => ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, y⟩
  set S : Set ι := {i | x i in A i}
  have hS : cofinite <= 𝓟 S := le_principal_iff.mpr x.2
  have hxS : forall i in S, x i in A

中文:
定理 continuous_dom_prod_right
  结论: {X Y : 类型} [TopologicalSpace X] [TopologicalSpace Y]
  证明: by
  refine ⟨fun H S hS => H.comp ((continuous_inclusion hS).prodMap continuous_id),
    fun H => ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, y⟩
  set S : Set ι := {i | x i in A i}
  have hS : cofinite <= 𝓟 S := le_principal_iff.mpr x.2
  have hxS : forall i in S, x i in A

Depends on / 依赖: ContinuousAt, Filter, Filter.map_id, H.comp, cofinite, continuous_id, continuous_iff_continuousAt, continuous_inclusion, exists_inclusion_eq_of_eventually, hAopen, le_principal_iff, le_principal_iff.mpr, map_id, nhds_eq_map_inclusion, nhds_prod_eq, prodMap, prod_map_map_eq, simp_rw
-/
theorem continuous_dom_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Πʳ i, [R i, A i] × Y -> X} :
    Continuous f ↔ forall (S : Set ι) (hS : cofinite <= 𝓟 S),
      Continuous (f ∘ (Prod.map (inclusion R A hS) id)) := by
  refine ⟨fun H S hS => H.comp ((continuous_inclusion hS).prodMap continuous_id),
    fun H => ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, y⟩
  set S : Set ι := {i | x i in A i}
  have hS : cofinite <= 𝓟 S := le_principal_iff.mpr x.2
  have hxS : forall i in S, x i in A i := fun i hi => hi
  rcases exists_inclusion_eq_of_eventually R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx']; rw [nhds_prod_eq]; rw [nhds_eq_map_inclusion hAopen hS x']; rw [← Filter.map_id (f := 𝓝 y)]; rw [prod_map_map_eq]; rw [← nhds_prod_eq]; rw [tendsto_map'_iff]
.tendsto ⟨x', y⟩ exact H S hS

-- TODO: get from the previous one instead of copy-pasting
include hAopen in
/--
theorem `continuous_dom_prod_left` / 定理 `continuous_dom_prod_left`

English:
theorem continuous_dom_prod_left
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  proof: by
  refine ⟨fun H S hS => H.comp (continuous_id.prodMap (continuous_inclusion hS)),
    fun H => ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨y, x⟩
  set S : Set ι := {i | x i in A i}
  have hS : cofinite <= 𝓟 S := le_principal_iff.mpr x.2
  have hxS : forall i in S, x i in A

中文:
定理 continuous_dom_prod_left
  结论: {X Y : 类型} [TopologicalSpace X] [TopologicalSpace Y]
  证明: by
  refine ⟨fun H S hS => H.comp (continuous_id.prodMap (continuous_inclusion hS)),
    fun H => ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨y, x⟩
  set S : Set ι := {i | x i in A i}
  have hS : cofinite <= 𝓟 S := le_principal_iff.mpr x.2
  have hxS : forall i in S, x i in A

Depends on / 依赖: ContinuousAt, Filter, Filter.map_id, H.comp, cofinite, continuous_id, continuous_id.prodMap, continuous_iff_continuousAt, continuous_inclusion, exists_inclusion_eq_of_eventually, hAopen, le_principal_iff, le_principal_iff.mpr, map_id, nhds_eq_map_inclusion, nhds_prod_eq, prodMap, prod_map_map_eq, simp_rw
-/
theorem continuous_dom_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y × Πʳ i, [R i, A i] -> X} :
    Continuous f ↔ forall (S : Set ι) (hS : cofinite <= 𝓟 S),
      Continuous (f ∘ (Prod.map id (inclusion R A hS))) := by
  refine ⟨fun H S hS => H.comp (continuous_id.prodMap (continuous_inclusion hS)),
    fun H => ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨y, x⟩
  set S : Set ι := {i | x i in A i}
  have hS : cofinite <= 𝓟 S := le_principal_iff.mpr x.2
  have hxS : forall i in S, x i in A i := fun i hi => hi
  rcases exists_inclusion_eq_of_eventually R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx']; rw [nhds_prod_eq]; rw [nhds_eq_map_inclusion hAopen hS x']; rw [← Filter.map_id (f := 𝓝 y)]; rw [prod_map_map_eq]; rw [← nhds_prod_eq]; rw [tendsto_map'_iff]
.tendsto ⟨y, x'⟩ exact H S hS

include hAopen in
/--
theorem `continuous_dom_prod` / 定理 `continuous_dom_prod`

English:
theorem continuous_dom_prod
  statement: {R' : ι -> Type*} {A' : (i : ι) -> Set (R' i)}
  proof: by
  simp_rw [continuous_dom_prod_right hAopen, continuous_dom_prod_left hAopen']
  refine ⟨fun H S hS => H S hS S hS, fun H S hS T hT => ?_⟩
  set U := S inter T
  have hU : cofinite <= 𝓟 (S inter T) := inf_principal ▸ le_inf hS hT
  have hSU : 𝓟 U <= 𝓟 S := principal_mono.mpr inter_subset_left
  h

中文:
定理 continuous_dom_prod
  结论: {R' : ι -> 类型} {A' : (i : ι) -> Set (R' i)}
  证明: by
  simp_rw [continuous_dom_prod_right hAopen, continuous_dom_prod_left hAopen']
  refine ⟨fun H S hS => H S hS S hS, fun H S hS T hT => ?_⟩
  set U := S inter T
  have hU : cofinite <= 𝓟 (S inter T) := inf_principal ▸ le_inf hS hT
  have hSU : 𝓟 U <= 𝓟 S := principal_mono.mpr inter_subset_left
  h

Depends on / 依赖: cofinite, continuous_dom_prod_left, continuous_dom_prod_right, continuous_inclusion, hAopen, inf_principal, inter_subset_left, inter_subset_right, le_inf, principal_mono, principal_mono.mpr, prodMap, simp_rw
-/
theorem continuous_dom_prod {R' : ι -> Type*} {A' : (i : ι) -> Set (R' i)}
    [forall i, TopologicalSpace (R' i)] (hAopen' : forall i, IsOpen (A' i))
    {X : Type*} [TopologicalSpace X]
    {f : Πʳ i, [R i, A i] × Πʳ i, [R' i, A' i] -> X} :
    Continuous f ↔ forall (S : Set ι) (hS : cofinite <= 𝓟 S),
      Continuous (f ∘ (Prod.map (inclusion R A hS) (inclusion R' A' hS))) := by
  simp_rw [continuous_dom_prod_right hAopen, continuous_dom_prod_left hAopen']
  refine ⟨fun H S hS => H S hS S hS, fun H S hS T hT => ?_⟩
  set U := S inter T
  have hU : cofinite <= 𝓟 (S inter T) := inf_principal ▸ le_inf hS hT
  have hSU : 𝓟 U <= 𝓟 S := principal_mono.mpr inter_subset_left
  have hTU : 𝓟 U <= 𝓟 T := principal_mono.mpr inter_subset_right
  exact (H U hU).comp ((continuous_inclusion hSU).prodMap (continuous_inclusion hTU))

/--
theorem `continuous_dom_pi` / 定理 `continuous_dom_pi`

English:
theorem continuous_dom_pi
  statement: {n : Type*} [Finite n] {X : Type*}
  proof: by
  refine ⟨by fun_prop, fun H => ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  intro x
  set S : Set ι := {i | forall j, x j i in C j i}
  have hS : cofinite <= 𝓟 S := by
    rw [le_principal_iff]
    change forallᶠ i in cofinite, forall j : n, x j i in C j i
    simp [-eventually_co

中文:
定理 continuous_dom_pi
  结论: {n : 类型} [Finite n] {X : 类型}
  证明: by
  refine ⟨by fun_prop, fun H => ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  intro x
  set S : Set ι := {i | forall j, x j i in C j i}
  have hS : cofinite <= 𝓟 S := by
    rw [le_principal_iff]
    change forallᶠ i in cofinite, forall j : n, x j i in C j i
    simp [-eventually_co

Depends on / 依赖: ContinuousAt, Pi.map, Pi.map_apply, cofinite, continuous_iff_continuousAt, eventually_cofinite, fun_prop, inclusion, le_principal_iff, map_apply, nhds_eq_map_inclusion, nhds_pi, simp_rw
-/
theorem continuous_dom_pi {n : Type*} [Finite n] {X : Type*}
    [TopologicalSpace X] {A : n -> ι -> Type*}
    [forall j i, TopologicalSpace (A j i)]
    {C : (j : n) -> (i : ι) -> Set (A j i)}
    (hCopen : forall j i, IsOpen (C j i))
    {f : (Π j : n, Πʳ i : ι, [A j i, C j i]) -> X} :
    Continuous f ↔
      forall (S : Set ι) (hS : cofinite <= 𝓟 S), Continuous (f ∘ Pi.map fun _ => inclusion _ _ hS) := by
  refine ⟨by fun_prop, fun H => ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  intro x
  set S : Set ι := {i | forall j, x j i in C j i}
  have hS : cofinite <= 𝓟 S := by
    rw [le_principal_iff]
    change forallᶠ i in cofinite, forall j : n, x j i in C j i
    simp [-eventually_cofinite]
  let x' (j : n) : Πʳ i : ι, [A j i, C j i]_[𝓟 S] := .mk (fun i => x j i) (fun i hi => hi _)
  have hxx' : Pi.map (fun j => inclusion _ _ hS) x' = x := rfl
  simp_rw [← hxx', nhds_pi, Pi.map_apply, nhds_eq_map_inclusion (hCopen _), ← map_piMap_pi_finite,
    tendsto_map'_iff, ← nhds_pi]
  exact (H _ _).tendsto _

end cofinite

end Topology

section Compatibility
/-!
## Compatibility properties between algebra and topology
-/

variable {S : ι -> Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}
variable {T : Set ι} {𝓕 : Filter ι}
variable [Π i, TopologicalSpace (R i)]

section general

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Inv (R i)] [forall i, InvMemClass (S i) (R i)] [forall i, ContinuousInv (R i)] :
  body: by
    rw [continuous_dom]
    intro T hT
    have : ContinuousInv (Πʳ i, [R i, B i]_[𝓟 T]) :=
      isEmbedding_coe_of_principal.continuousInv fun _ => rfl
    exact (continuous_inclusion hT).comp continuous_inv

@[to_additive]

中文:
实例 [Π
  签名: i, Inv (R i)] [对任意 i, InvMemClass (S i) (R i)] [对任意 i, ContinuousInv (R i)] :
  定义体: by
    rw [continuous_dom]
    intro T hT
    have : ContinuousInv (Πʳ i, [R i, B i]_[𝓟 T]) :=
      isEmbedding_coe_of_principal.continuousInv fun _ => rfl
    exact (continuous_inclusion hT).comp continuous_inv

@[to_additive]

Depends on / 依赖: ContinuousInv, continuousInv, continuous_dom, continuous_inclusion, continuous_inv, isEmbedding_coe_of_principal, isEmbedding_coe_of_principal.continuousInv
-/
instance [Π i, Inv (R i)] [forall i, InvMemClass (S i) (R i)] [forall i, ContinuousInv (R i)] :
    ContinuousInv (Πʳ i, [R i, B i]_[𝓕]) where
  continuous_inv := by
    rw [continuous_dom]
    intro T hT
    have : ContinuousInv (Πʳ i, [R i, B i]_[𝓟 T]) :=
      isEmbedding_coe_of_principal.continuousInv fun _ => rfl
    exact (continuous_inclusion hT).comp continuous_inv

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [forall i, SMulMemClass (S i) G (R i)]
    [forall i, ContinuousConstSMul G (R i)] :
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Mul (R i)] [forall i, MulMemClass (S i) (R i)] [forall i, ContinuousMul (R i)] :
  body: let φ : Πʳ i, [R i, B i]_[𝓟 T] ->ₙ* Π i, R i :=
  { toFun := (↑)
    map_mul' := fun _ _ => rfl }
  isEmbedding_coe_of_principal.continuousMul φ

@[to_additive]

中文:
实例 [Π
  签名: i, Mul (R i)] [对任意 i, MulMemClass (S i) (R i)] [对任意 i, ContinuousMul (R i)] :
  定义体: let φ : Πʳ i, [R i, B i]_[𝓟 T] ->ₙ* Π i, R i :=
  { toFun := (↑)
    map_mul' := fun _ _ => rfl }
  isEmbedding_coe_of_principal.continuousMul φ

@[to_additive]

Depends on / 依赖: continuousMul, isEmbedding_coe_of_principal, isEmbedding_coe_of_principal.continuousMul, map_mul
-/
instance [Π i, Mul (R i)] [forall i, MulMemClass (S i) (R i)] [forall i, ContinuousMul (R i)] :
    ContinuousMul (Πʳ i, [R i, B i]_[𝓟 T]) :=
  let φ : Πʳ i, [R i, B i]_[𝓟 T] ->ₙ* Π i, R i :=
  { toFun := (↑)
    map_mul' := fun _ _ => rfl }
  isEmbedding_coe_of_principal.continuousMul φ

@[to_additive]
instance {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)] [forall i, SMulMemClass (S i) G (R i)]
    [forall i, ContinuousSMul G (R i)] :
    ContinuousSMul G (Πʳ i, [R i, B i]_[𝓟 T]) :=
  isEmbedding_coe_of_principal.continuousSMul continuous_id rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Group (R i)] [forall i, SubgroupClass (S i) (R i)] [forall i, IsTopologicalGroup (R i)] :

中文:
实例 [Π
  签名: i, Group (R i)] [对任意 i, SubgroupClass (S i) (R i)] [对任意 i, IsTopologicalGroup (R i)] :
-/
instance [Π i, Group (R i)] [forall i, SubgroupClass (S i) (R i)] [forall i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (Πʳ i, [R i, B i]_[𝓟 T]) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Ring (R i)] [forall i, SubringClass (S i) (R i)] [forall i, IsTopologicalRing (R i)] :

中文:
实例 [Π
  签名: i, Ring (R i)] [对任意 i, SubringClass (S i) (R i)] [对任意 i, IsTopologicalRing (R i)] :
-/
instance [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)] [forall i, IsTopologicalRing (R i)] :
    IsTopologicalRing (Πʳ i, [R i, B i]_[𝓟 T]) where

end principal

section cofinite

/--
theorem `nhds_zero_eq_map_ofPre` / 定理 `nhds_zero_eq_map_ofPre`

English:
theorem nhds_zero_eq_map_ofPre
  statement: [Π i, Zero (R i)] [forall i, ZeroMemClass (S i) (R i)]
  proof: nhds_eq_map_inclusion hBopen hT 0

中文:
定理 nhds_zero_eq_map_ofPre
  结论: [Π i, Zero (R i)] [对任意 i, ZeroMemClass (S i) (R i)]
  证明: nhds_eq_map_inclusion hBopen hT 0

Depends on / 依赖: hBopen, nhds_eq_map_inclusion
-/
theorem nhds_zero_eq_map_ofPre [Π i, Zero (R i)] [forall i, ZeroMemClass (S i) (R i)]
    (hBopen : forall i, IsOpen (B i : Set (R i))) (hT : cofinite <= 𝓟 T) :
    (𝓝 (inclusion R (fun i => B i) hT 0)) = .map (inclusion R (fun i => B i) hT) (𝓝 0) :=
  nhds_eq_map_inclusion hBopen hT 0

/--
theorem `nhds_zero_eq_map_structureMap` / 定理 `nhds_zero_eq_map_structureMap`

English:
theorem nhds_zero_eq_map_structureMap
  statement: [Π i, Zero (R i)] [forall i, ZeroMemClass (S i) (R i)]
  proof: nhds_eq_map_structureMap hBopen 0

中文:
定理 nhds_zero_eq_map_structureMap
  结论: [Π i, Zero (R i)] [对任意 i, ZeroMemClass (S i) (R i)]
  证明: nhds_eq_map_structureMap hBopen 0

Depends on / 依赖: hBopen, nhds_eq_map_structureMap
-/
theorem nhds_zero_eq_map_structureMap [Π i, Zero (R i)] [forall i, ZeroMemClass (S i) (R i)]
    (hBopen : forall i, IsOpen (B i : Set (R i))) :
    (𝓝 (structureMap R (fun i => B i) cofinite 0)) =
      .map (structureMap R (fun i => B i) cofinite) (𝓝 0) :=
  nhds_eq_map_structureMap hBopen 0

-- TODO: Make `IsOpen` a class like `IsClosed` ?
variable [hBopen : Fact (forall i, IsOpen (B i : Set (R i)))]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Mul (R i)] [forall i, MulMemClass (S i) (R i)] [forall i, ContinuousMul (R i)] :
  body: by
    rw [continuous_dom_prod hBopen.out hBopen.out]
    exact fun S hS => (continuous_inclusion hS).comp continuous_mul

@[to_additive]

中文:
实例 [Π
  签名: i, Mul (R i)] [对任意 i, MulMemClass (S i) (R i)] [对任意 i, ContinuousMul (R i)] :
  定义体: by
    rw [continuous_dom_prod hBopen.out hBopen.out]
    exact fun S hS => (continuous_inclusion hS).comp continuous_mul

@[to_additive]

Depends on / 依赖: continuous_dom_prod, continuous_inclusion, continuous_mul, hBopen, hBopen.out
-/
instance [Π i, Mul (R i)] [forall i, MulMemClass (S i) (R i)] [forall i, ContinuousMul (R i)] :
    ContinuousMul (Πʳ i, [R i, B i]) where
  continuous_mul := by
    rw [continuous_dom_prod hBopen.out hBopen.out]
    exact fun S hS => (continuous_inclusion hS).comp continuous_mul

@[to_additive]
/--
Instance `continuousSMul` / 实例 `continuousSMul`

English:
instance continuousSMul
  signature: {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)]
  body: by
    rw [continuous_dom_prod_left hBopen.out]
    exact fun S hS => (continuous_inclusion hS).comp continuous_smul

@[to_additive]

中文:
实例 continuousSMul
  签名: {G : 类型} [TopologicalSpace G] [Π i, SMul G (R i)]
  定义体: by
    rw [continuous_dom_prod_left hBopen.out]
    exact fun S hS => (continuous_inclusion hS).comp continuous_smul

@[to_additive]

Depends on / 依赖: continuous_dom_prod_left, continuous_inclusion, continuous_smul, hBopen, hBopen.out
-/
instance continuousSMul {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)]
    [forall i, SMulMemClass (S i) G (R i)] [forall i, ContinuousSMul G (R i)] :
    ContinuousSMul G (Πʳ i, [R i, B i]) where
  continuous_smul := by
    rw [continuous_dom_prod_left hBopen.out]
    exact fun S hS => (continuous_inclusion hS).comp continuous_smul

@[to_additive]
/--
Instance `isTopologicalGroup` / 实例 `isTopologicalGroup`

English:
instance isTopologicalGroup
  signature: [Π i, Group (R i)] [forall i, SubgroupClass (S i) (R i)]

中文:
实例 isTopologicalGroup
  签名: [Π i, Group (R i)] [对任意 i, SubgroupClass (S i) (R i)]
-/
instance isTopologicalGroup [Π i, Group (R i)] [forall i, SubgroupClass (S i) (R i)]
    [forall i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (Πʳ i, [R i, B i]) where

/--
Instance `isTopologicalRing` / 实例 `isTopologicalRing`

English:
instance isTopologicalRing
  signature: [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)]

中文:
实例 isTopologicalRing
  签名: [Π i, Ring (R i)] [对任意 i, SubringClass (S i) (R i)]
-/
instance isTopologicalRing [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)]
    [forall i, IsTopologicalRing (R i)] :
    IsTopologicalRing (Πʳ i, [R i, B i]) where

/-- Assume that each `R i` is a locally compact group with `A i` an open subgroup.
Assume also that all but finitely many `A i`s are compact.
Then the restricted product `Πʳ i, [R i, A i]` is a locally compact group. -/
@[to_additive
/-- Assume that each `R i` is a locally compact additive group with `A i` an open subgroup.
Assume also that all but finitely many `A i`s are compact.
Then the restricted product `Πʳ i, [R i, A i]` is a locally compact additive group. -/]
/--
theorem `locallyCompactSpace_of_group` / 定理 `locallyCompactSpace_of_group`

English:
theorem locallyCompactSpace_of_group
  statement: [Π i, Group (R i)] [forall i, SubgroupClass (S i) (R i)]
  proof: haveI : WeaklyLocallyCompactSpace (Πʳ i, [R i, B i]) :=
    weaklyLocallyCompactSpace_of_cofinite hBopen.out hBcompact
  inferInstance

中文:
定理 locallyCompactSpace_of_group
  结论: [Π i, Group (R i)] [对任意 i, SubgroupClass (S i) (R i)]
  证明: haveI : WeaklyLocallyCompactSpace (Πʳ i, [R i, B i]) :=
    weaklyLocallyCompactSpace_of_cofinite hBopen.out hBcompact
  inferInstance

Depends on / 依赖: WeaklyLocallyCompactSpace, hBcompact, hBopen, hBopen.out, weaklyLocallyCompactSpace_of_cofinite
-/
theorem locallyCompactSpace_of_group [Π i, Group (R i)] [forall i, SubgroupClass (S i) (R i)]
    [forall i, IsTopologicalGroup (R i)] [forall i, LocallyCompactSpace (R i)]
    (hBcompact : forallᶠ i in cofinite, IsCompact (B i : Set (R i))) :
    LocallyCompactSpace (Πʳ i, [R i, B i]) :=
  haveI : WeaklyLocallyCompactSpace (Πʳ i, [R i, B i]) :=
    weaklyLocallyCompactSpace_of_cofinite hBopen.out hBcompact
  inferInstance

open scoped Pointwise in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Group (R i)] [forall i, SubgroupClass (S i) (R i)] [forall i, IsTopologicalGroup (R i)]
  body: -- TODO: extract as a lemma
  haveI : forall i, WeaklyLocallyCompactSpace (R i) := fun i => .mk fun x =>
    ⟨x • (B i : Set (R i)), .smul _ (isCompact_iff_compactSpace.mpr inferInstance),
.mem_nhds by .smul _ hBopen.out i
      simpa using smul_mem_smul_set (a := x) (one_mem (B i))⟩
locallyCompactS

中文:
实例 [Π
  签名: i, Group (R i)] [对任意 i, SubgroupClass (S i) (R i)] [对任意 i, IsTopologicalGroup (R i)]
  定义体: -- TODO: extract as a lemma
  haveI : forall i, WeaklyLocallyCompactSpace (R i) := fun i => .mk fun x =>
    ⟨x • (B i : Set (R i)), .smul _ (isCompact_iff_compactSpace.mpr inferInstance),
.mem_nhds by .smul _ hBopen.out i
      simpa using smul_mem_smul_set (a := x) (one_mem (B i))⟩
locallyCompactS
-/
instance [Π i, Group (R i)] [forall i, SubgroupClass (S i) (R i)] [forall i, IsTopologicalGroup (R i)]
    [hAcompact : forall i, CompactSpace (B i)] : LocallyCompactSpace (Πʳ i, [R i, B i]) :=
  -- TODO: extract as a lemma
  haveI : forall i, WeaklyLocallyCompactSpace (R i) := fun i => .mk fun x =>
    ⟨x • (B i : Set (R i)), .smul _ (isCompact_iff_compactSpace.mpr inferInstance),
.mem_nhds by .smul _ hBopen.out i
      simpa using smul_mem_smul_set (a := x) (one_mem (B i))⟩
locallyCompactSpace_of_group _ .of_forall fun _ => isCompact_iff_compactSpace.mpr inferInstance

end cofinite

end Compatibility

section map_continuous

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ -> Type*) (R₂ : ι₂ -> Type*)
variable [forall i, TopologicalSpace (R₁ i)] [forall i, TopologicalSpace (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) -> Set (R₁ i)} {A₂ : (i : ι₂) -> Set (R₂ i)}
variable (f : ι₂ -> ι₁) (hf : Tendsto f 𝓕₂ 𝓕₁)

variable (φ : forall j, R₁ (f j) -> R₂ j) (hφ : forallᶠ j in 𝓕₂, MapsTo (φ j) (A₁ (f j)) (A₂ j))

/--
theorem `mapAlong_continuous` / 定理 `mapAlong_continuous`

English:
theorem mapAlong_continuous
  given: (φ_cont : forall j, Continuous (φ j))
  proof: by
  rw [continuous_dom]
  intro S hS
  set T := f ⁻¹' S inter {j | MapsTo (φ j) (A₁ (f j)) (A₂ j)}
  have hT : 𝓕₂ <= 𝓟 T := by
    rw [le_principal_iff] at hS ⊢
    exact inter_mem (hf hS) hφ
  have hf' : Tendsto f (𝓟 T) (𝓟 S) := by aesop
  have hφ' : forallᶠ j in 𝓟 T, MapsTo (φ j) (A₁ (f j)) (A₂ j

中文:
定理 mapAlong_continuous
  条件: (φ_cont : 对任意 j, Continuous (φ j))
  证明: by
  rw [continuous_dom]
  intro S hS
  set T := f ⁻¹' S inter {j | MapsTo (φ j) (A₁ (f j)) (A₂ j)}
  have hT : 𝓕₂ <= 𝓟 T := by
    rw [le_principal_iff] at hS ⊢
    exact inter_mem (hf hS) hφ
  have hf' : Tendsto f (𝓟 T) (𝓟 S) := by aesop
  have hφ' : forallᶠ j in 𝓟 T, MapsTo (φ j) (A₁ (f j)) (A₂ j

Depends on / 依赖: MapsTo, Tendsto, continuous, continuous_dom, continuous_inclusion, continuous_rng_of_principal, continuous_rng_of_principal.mpr, inclusion, inter_mem, le_principal_iff, mapAlong
-/
theorem mapAlong_continuous (φ_cont : forall j, Continuous (φ j)) :
    Continuous (mapAlong R₁ R₂ f hf φ hφ) := by
  rw [continuous_dom]
  intro S hS
  set T := f ⁻¹' S inter {j | MapsTo (φ j) (A₁ (f j)) (A₂ j)}
  have hT : 𝓕₂ <= 𝓟 T := by
    rw [le_principal_iff] at hS ⊢
    exact inter_mem (hf hS) hφ
  have hf' : Tendsto f (𝓟 T) (𝓟 S) := by aesop
  have hφ' : forallᶠ j in 𝓟 T, MapsTo (φ j) (A₁ (f j)) (A₂ j) := by aesop
  have key : mapAlong R₁ R₂ f hf φ hφ ∘ inclusion R₁ A₁ hS =
      inclusion R₂ A₂ hT ∘ mapAlong R₁ R₂ f hf' φ hφ' := rfl
  rw [key]
.comp exact continuous_inclusion _
continuous_rng_of_principal.mpr
.comp continuous_eval (f j) continuous_pi fun j => φ_cont j

end map_continuous

end RestrictedProduct
