/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Topology.Compactness.Bases
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.Copy

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

### Bundled open sets

- `TopologicalSpace.Opens α` is the type of open subsets of a topological space `α`.
- `TopologicalSpace.Opens.IsBasis` is a predicate saying that a set of `Opens`s form a topological
  basis.
- `TopologicalSpace.Opens.comap`: preimage of an open set under a continuous map as a `FrameHom`.
- `Homeomorph.opensCongr`: order-preserving equivalence between open sets in the domain and the
  codomain of a homeomorphism.

### Bundled open neighborhoods

- `TopologicalSpace.OpenNhdsOf x` is the type of open subsets of a topological space `α` containing
  `x : α`.
- `TopologicalSpace.OpenNhdsOf.comap f x U` is the preimage of open neighborhood `U` of `f x` under
  `f : C(α, β)`.

## Main results

We define order structures on both `Opens α` (`CompleteLattice`, `Frame`) and `OpenNhdsOf x`
(`OrderTop`, `DistribLattice`).

## TODO

- Rename `TopologicalSpace.Opens` to `Open`?
- Port the `auto_cases` tactic version (as a plugin if the ported `auto_cases` will allow plugins).
-/

@[expose] public section

universe u

open Filter Function Order Set

open Topology

variable {ι α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

variable (α) in
/--
Definition of `Opens` / `Opens` 的定义

English:
structure Opens
  parameters: where
  axioms and operations (2):
    - carrier : Set α
    - is_open' : IsOpen carrier

中文:
结构 Opens
  参数: where
  公理与运算 (2 个):
    - carrier : Set α
    - is_open' : IsOpen carrier
-/
structure Opens where
  /-- The underlying set of a bundled `TopologicalSpace.Opens` object. -/
  carrier : Set α
  /-- The `TopologicalSpace.Opens.carrier _` is an open set. -/
  is_open' : IsOpen carrier

namespace Opens

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Opens α) α
  body: Opens.carrier
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

中文:
实例 :
  签名: SetLike (Opens α) α
  定义体: Opens.carrier
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

Depends on / 依赖: Opens.carrier, carrier
-/
instance : SetLike (Opens α) α where
  coe := Opens.carrier
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Opens α)
  body: fast_instance% .ofSetLike (Opens α) α

中文:
实例 :
  签名: PartialOrder (Opens α)
  定义体: fast_instance% .ofSetLike (Opens α) α

Depends on / 依赖: fast_instance, ofSetLike
-/
instance : PartialOrder (Opens α) := fast_instance% .ofSetLike (Opens α) α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (Set α) (Opens α) (↑) IsOpen
  body: ⟨fun s h => ⟨⟨s, h⟩, rfl⟩⟩

中文:
实例 :
  签名: CanLift (Set α) (Opens α) (↑) IsOpen
  定义体: ⟨fun s h => ⟨⟨s, h⟩, rfl⟩⟩
-/
instance : CanLift (Set α) (Opens α) (↑) IsOpen :=
  ⟨fun s h => ⟨⟨s, h⟩, rfl⟩⟩

/--
Instance `instSecondCountableOpens` / 实例 `instSecondCountableOpens`

English:
instance instSecondCountableOpens
  signature: [SecondCountableTopology α] (U : Opens α)
  body: inferInstanceAs (SecondCountableTopology U.1)

中文:
实例 instSecondCountableOpens
  签名: [SecondCountableTopology α] (U : Opens α)
  定义体: inferInstanceAs (SecondCountableTopology U.1)

Depends on / 依赖: SecondCountableTopology
-/
instance instSecondCountableOpens [SecondCountableTopology α] (U : Opens α) :
    SecondCountableTopology U := inferInstanceAs (SecondCountableTopology U.1)

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : Opens α -> Prop}
  statement: (forall U, p U) ↔ forall (U : Set α) (hU : IsOpen U), p ⟨U, hU⟩
  proof: ⟨fun h _ _ => h _, fun h _ => h _ _⟩

中文:
定理 «forall»
  条件: {p : Opens α -> 命题}
  结论: (对任意 U, p U) ↔ 对任意 (U : Set α) (hU : IsOpen U), p ⟨U, hU⟩
  证明: ⟨fun h _ _ => h _, fun h _ => h _ _⟩
-/
theorem «forall» {p : Opens α -> Prop} : (forall U, p U) ↔ forall (U : Set α) (hU : IsOpen U), p ⟨U, hU⟩ :=
  ⟨fun h _ _ => h _, fun h _ => h _ _⟩

/--
theorem `carrier_eq_coe` / 定理 `carrier_eq_coe`

English:
theorem carrier_eq_coe
  given: (U : Opens α)
  statement: U.1 = ↑U
  proof: rfl

中文:
定理 carrier_eq_coe
  条件: (U : Opens α)
  结论: U.1 = ↑U
  证明: rfl
-/
@[simp] theorem carrier_eq_coe (U : Opens α) : U.1 = ↑U := rfl

/-- the coercion `Opens α → Set α` applied to a pair is the same as taking the first component -/
@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {U : Set α} {hU : IsOpen U}
  statement: ↑(⟨U, hU⟩ : Opens α) = U
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: {U : Set α} {hU : IsOpen U}
  结论: ↑(⟨U, hU⟩ : Opens α) = U
  证明: rfl

@[simp]
-/
theorem coe_mk {U : Set α} {hU : IsOpen U} : ↑(⟨U, hU⟩ : Opens α) = U :=
  rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {x : α} {U : Set α} {h : IsOpen U}
  statement: x in mk U h ↔ x in U
  proof: Iff.rfl

中文:
定理 mem_mk
  条件: {x : α} {U : Set α} {h : IsOpen U}
  结论: x in mk U h ↔ x in U
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {x : α} {U : Set α} {h : IsOpen U} : x in mk U h ↔ x in U := Iff.rfl

/--
theorem `nonempty_coeSort` / 定理 `nonempty_coeSort`

English:
theorem nonempty_coeSort
  given: {U : Opens α}
  statement: Nonempty U ↔ (U : Set α).Nonempty
  proof: Set.nonempty_coe_sort

中文:
定理 nonempty_coeSort
  条件: {U : Opens α}
  结论: Nonempty U ↔ (U : Set α).Nonempty
  证明: Set.nonempty_coe_sort
-/
protected theorem nonempty_coeSort {U : Opens α} : Nonempty U ↔ (U : Set α).Nonempty :=
  Set.nonempty_coe_sort

-- TODO: should this theorem be proved for a `SetLike`?
/--
theorem `nonempty_coe` / 定理 `nonempty_coe`

English:
theorem nonempty_coe
  given: {U : Opens α}
  statement: (U : Set α).Nonempty ↔ exists x, x in U
  proof: Iff.rfl

@[ext] -- TODO: replace with `∀ x, x ∈ U ↔ x ∈ V`?

中文:
定理 nonempty_coe
  条件: {U : Opens α}
  结论: (U : Set α).Nonempty ↔ 存在 x, x in U
  证明: Iff.rfl

@[ext] -- TODO: replace with `∀ x, x ∈ U ↔ x ∈ V`?
-/
protected theorem nonempty_coe {U : Opens α} : (U : Set α).Nonempty ↔ exists x, x in U :=
  Iff.rfl

@[ext] -- TODO: replace with `∀ x, x ∈ U ↔ x ∈ V`?
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {U V : Opens α} (h : (U : Set α) = V)
  statement: U = V
  proof: SetLike.coe_injective h

中文:
定理 ext
  条件: {U V : Opens α} (h : (U : Set α) = V)
  结论: U = V
  证明: SetLike.coe_injective h

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem ext {U V : Opens α} (h : (U : Set α) = V) : U = V :=
  SetLike.coe_injective h

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {U V : Opens α}
  statement: (U : Set α) = V ↔ U = V
  proof: SetLike.ext'_iff.symm

中文:
定理 coe_inj
  条件: {U V : Opens α}
  结论: (U : Set α) = V ↔ U = V
  证明: SetLike.ext'_iff.symm

Depends on / 依赖: SetLike, SetLike.ext, _iff, _iff.symm
-/
theorem coe_inj {U V : Opens α} : (U : Set α) = V ↔ U = V :=
  SetLike.ext'_iff.symm

/--
Definition of `inclusion` / `inclusion` 的定义

English:
abbreviation inclusion
  signature: {U V : Opens α} (h : U <= V)
  body: Set.inclusion h

中文:
缩写 inclusion
  签名: {U V : Opens α} (h : U <= V)
  定义体: Set.inclusion h

Depends on / 依赖: Set.inclusion, inclusion
-/
abbrev inclusion {U V : Opens α} (h : U <= V) : U -> V := Set.inclusion h

/--
theorem `isOpen` / 定理 `isOpen`

English:
theorem isOpen
  given: (U : Opens α)
  statement: IsOpen (U : Set α)
  proof: U.is_open'

中文:
定理 isOpen
  条件: (U : Opens α)
  结论: IsOpen (U : Set α)
  证明: U.is_open'
-/
protected theorem isOpen (U : Opens α) : IsOpen (U : Set α) :=
  U.is_open'

/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (U : Opens α)
  statement: mk (↑U) U.isOpen = U
  proof: rfl

中文:
定理 mk_coe
  条件: (U : Opens α)
  结论: mk (↑U) U.isOpen = U
  证明: rfl
-/
@[simp] theorem mk_coe (U : Opens α) : mk (↑U) U.isOpen = U := rfl

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (U : Opens α)
  body: U

initialize_simps_projections Opens (carrier -> coe, as_prefix coe)

中文:
定义 Simps.coe
  签名: (U : Opens α)
  定义体: U

initialize_simps_projections Opens (carrier -> coe, as_prefix coe)
-/
def Simps.coe (U : Opens α) : Set α := U

initialize_simps_projections Opens (carrier -> coe, as_prefix coe)

/-- The interior of a set, as an element of `Opens`. -/
@[simps]
/--
Definition of `interior` / `interior` 的定义

English:
definition interior
  signature: (s : Set α)
  body: ⟨interior s, isOpen_interior⟩

@[simp]

中文:
定义 interior
  签名: (s : Set α)
  定义体: ⟨interior s, isOpen_interior⟩

@[simp]
-/
protected def interior (s : Set α) : Opens α :=
  ⟨interior s, isOpen_interior⟩

@[simp]
/--
theorem `mem_interior` / 定理 `mem_interior`

English:
theorem mem_interior
  given: {s : Set α} {x : α}
  statement: x in Opens.interior s ↔ x in _root_.interior s
  proof: .rfl

中文:
定理 mem_interior
  条件: {s : Set α} {x : α}
  结论: x in Opens.interior s ↔ x in _root_.interior s
  证明: .rfl
-/
theorem mem_interior {s : Set α} {x : α} : x in Opens.interior s ↔ x in _root_.interior s := .rfl

/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  statement: GaloisConnection ((↑) : Opens α -> Set α) Opens.interior
  proof: fun U _ =>
  ⟨fun h => interior_maximal h U.isOpen, fun h => le_trans h interior_subset⟩

中文:
定理 gc
  结论: GaloisConnection ((↑) : Opens α -> Set α) Opens.interior
  证明: fun U _ =>
  ⟨fun h => interior_maximal h U.isOpen, fun h => le_trans h interior_subset⟩
-/
theorem gc : GaloisConnection ((↑) : Opens α -> Set α) Opens.interior := fun U _ =>
  ⟨fun h => interior_maximal h U.isOpen, fun h => le_trans h interior_subset⟩

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisCoinsertion (↑) (@Opens.interior α _) where
  body: ⟨s, interior_eq_iff_isOpen.mp le_antisymm interior_subset hs⟩
  gc := gc
  u_l_le _ := interior_subset
  choice_eq _s hs := le_antisymm hs interior_subset

中文:
定义 gi
  签名: : GaloisCoinsertion (↑) (@Opens.interior α _) where
  定义体: ⟨s, interior_eq_iff_isOpen.mp le_antisymm interior_subset hs⟩
  gc := gc
  u_l_le _ := interior_subset
  choice_eq _s hs := le_antisymm hs interior_subset

Depends on / 依赖: interior_eq_iff_isOpen, interior_eq_iff_isOpen.mp, interior_subset, le_antisymm
-/
def gi : GaloisCoinsertion (↑) (@Opens.interior α _) where
choice s hs := ⟨s, interior_eq_iff_isOpen.mp le_antisymm interior_subset hs⟩
  gc := gc
  u_l_le _ := interior_subset
  choice_eq _s hs := le_antisymm hs interior_subset

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Opens α)
  body: fast_instance% CompleteLattice.copy (GaloisCoinsertion.liftCompleteLattice gi)
    -- le
    (fun U V => (U : Set α) subseteq V) rfl
    -- top
    ⟨univ, isOpen_univ⟩ (ext interior_univ.symm)
    -- bot
    ⟨∅, isOpen_empty⟩ rfl
    -- sup
    (fun U V => ⟨↑U union ↑V, U.2.union V.2⟩) rfl
    -- in

中文:
实例 :
  签名: CompleteLattice (Opens α)
  定义体: fast_instance% CompleteLattice.copy (GaloisCoinsertion.liftCompleteLattice gi)
    -- le
    (fun U V => (U : Set α) subseteq V) rfl
    -- top
    ⟨univ, isOpen_univ⟩ (ext interior_univ.symm)
    -- bot
    ⟨∅, isOpen_empty⟩ rfl
    -- sup
    (fun U V => ⟨↑U union ↑V, U.2.union V.2⟩) rfl
    -- in

Depends on / 依赖: CompleteLattice, CompleteLattice.copy, GaloisCoinsertion, GaloisCoinsertion.liftCompleteLattice, fast_instance, liftCompleteLattice
-/
instance : CompleteLattice (Opens α) :=
  fast_instance% CompleteLattice.copy (GaloisCoinsertion.liftCompleteLattice gi)
    -- le
    (fun U V => (U : Set α) subseteq V) rfl
    -- top
    ⟨univ, isOpen_univ⟩ (ext interior_univ.symm)
    -- bot
    ⟨∅, isOpen_empty⟩ rfl
    -- sup
    (fun U V => ⟨↑U union ↑V, U.2.union V.2⟩) rfl
    -- inf
    (fun U V => ⟨↑U inter ↑V, U.2.inter V.2⟩)
    (funext₂ fun U V => ext (U.2.inter V.2).interior_eq.symm)
    -- sSup
    (fun S => ⟨⋃ s in S, ↑s, isOpen_biUnion fun s _ => s.2⟩)
    (funext fun _ => ext sSup_image.symm)
    -- sInf
    _ rfl

@[simp]
/--
theorem `mk_inf_mk` / 定理 `mk_inf_mk`

English:
theorem mk_inf_mk
  given: {U V : Set α} {hU : IsOpen U} {hV : IsOpen V}
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_inf_mk
  条件: {U V : Set α} {hU : IsOpen U} {hV : IsOpen V}
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_inf_mk {U V : Set α} {hU : IsOpen U} {hV : IsOpen V} :
    (⟨U, hU⟩ ⊓ ⟨V, hV⟩ : Opens α) = ⟨U ⊓ V, IsOpen.inter hU hV⟩ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (s t : Opens α)
  statement: (↑(s ⊓ t) : Set α) = ↑s inter ↑t
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (s t : Opens α)
  结论: (↑(s ⊓ t) : Set α) = ↑s inter ↑t
  证明: rfl

@[simp]
-/
theorem coe_inf (s t : Opens α) : (↑(s ⊓ t) : Set α) = ↑s inter ↑t :=
  rfl

@[simp]
/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  given: {s t : Opens α} {x : α}
  statement: x in s ⊓ t ↔ x in s ∧ x in t
  proof: Iff.rfl

@[simp, norm_cast]

中文:
引理 mem_inf
  条件: {s t : Opens α} {x : α}
  结论: x in s ⊓ t ↔ x in s ∧ x in t
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
lemma mem_inf {s t : Opens α} {x : α} : x in s ⊓ t ↔ x in s ∧ x in t := Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (s t : Opens α)
  statement: (↑(s ⊔ t) : Set α) = ↑s union ↑t
  proof: rfl

@[simp]

中文:
定理 coe_sup
  条件: (s t : Opens α)
  结论: (↑(s ⊔ t) : Set α) = ↑s union ↑t
  证明: rfl

@[simp]
-/
theorem coe_sup (s t : Opens α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t :=
  rfl

@[simp]
/--
theorem `mem_sup` / 定理 `mem_sup`

English:
theorem mem_sup
  given: {s t : Opens α} {x : α}
  statement: x in (s ⊔ t) ↔ x in s ∨ x in t
  proof: .rfl

@[simp, norm_cast]

中文:
定理 mem_sup
  条件: {s t : Opens α} {x : α}
  结论: x in (s ⊔ t) ↔ x in s ∨ x in t
  证明: .rfl

@[simp, norm_cast]
-/
theorem mem_sup {s t : Opens α} {x : α} : x in (s ⊔ t) ↔ x in s ∨ x in t :=
  .rfl

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : Opens α) : Set α) = ∅
  proof: rfl

@[simp]

中文:
定理 coe_bot
  结论: ((⊥ : Opens α) : Set α) = ∅
  证明: rfl

@[simp]
-/
theorem coe_bot : ((⊥ : Opens α) : Set α) = ∅ :=
  rfl

@[simp]
/--
lemma `mem_bot` / 引理 `mem_bot`

English:
lemma mem_bot
  given: {x : α}
  statement: x in (⊥ : Opens α) ↔ False
  proof: Iff.rfl

中文:
引理 mem_bot
  条件: {x : α}
  结论: x in (⊥ : Opens α) ↔ False
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_bot {x : α} : x in (⊥ : Opens α) ↔ False := Iff.rfl

/--
theorem `mk_empty` / 定理 `mk_empty`

English:
theorem mk_empty
  statement: (⟨∅, isOpen_empty⟩ : Opens α) = ⊥
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_empty
  结论: (⟨∅, isOpen_empty⟩ : Opens α) = ⊥
  证明: rfl

@[simp, norm_cast]
-/
@[simp] theorem mk_empty : (⟨∅, isOpen_empty⟩ : Opens α) = ⊥ := rfl

@[simp, norm_cast]
/--
theorem `coe_eq_empty` / 定理 `coe_eq_empty`

English:
theorem coe_eq_empty
  given: {U : Opens α}
  statement: (U : Set α) = ∅ ↔ U = ⊥
  proof: SetLike.coe_injective.eq_iff' rfl

@[simp]

中文:
定理 coe_eq_empty
  条件: {U : Opens α}
  结论: (U : Set α) = ∅ ↔ U = ⊥
  证明: SetLike.coe_injective.eq_iff' rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective.eq_iff, coe_injective, eq_iff
-/
theorem coe_eq_empty {U : Opens α} : (U : Set α) = ∅ ↔ U = ⊥ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp]
/--
lemma `mem_top` / 引理 `mem_top`

English:
lemma mem_top
  given: (x : α)
  statement: x in (⊤ : Opens α)
  proof: trivial

@[simp, norm_cast]

中文:
引理 mem_top
  条件: (x : α)
  结论: x in (⊤ : Opens α)
  证明: trivial

@[simp, norm_cast]
-/
lemma mem_top (x : α) : x in (⊤ : Opens α) := trivial

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : Opens α) : Set α) = Set.univ
  proof: rfl

中文:
定理 coe_top
  结论: ((⊤ : Opens α) : Set α) = Set.univ
  证明: rfl
-/
theorem coe_top : ((⊤ : Opens α) : Set α) = Set.univ :=
  rfl

/--
theorem `mk_univ` / 定理 `mk_univ`

English:
theorem mk_univ
  statement: (⟨univ, isOpen_univ⟩ : Opens α) = ⊤
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_univ
  结论: (⟨univ, isOpen_univ⟩ : Opens α) = ⊤
  证明: rfl

@[simp, norm_cast]
-/
@[simp] theorem mk_univ : (⟨univ, isOpen_univ⟩ : Opens α) = ⊤ := rfl

@[simp, norm_cast]
/--
theorem `coe_eq_univ` / 定理 `coe_eq_univ`

English:
theorem coe_eq_univ
  given: {U : Opens α}
  statement: (U : Set α) = univ ↔ U = ⊤
  proof: SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]

中文:
定理 coe_eq_univ
  条件: {U : Opens α}
  结论: (U : Set α) = univ ↔ U = ⊤
  证明: SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective.eq_iff, coe_injective, eq_iff
-/
theorem coe_eq_univ {U : Opens α} : (U : Set α) = univ ↔ U = ⊤ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]
/--
theorem `coe_sSup` / 定理 `coe_sSup`

English:
theorem coe_sSup
  given: {S : Set (Opens α)}
  statement: (↑(sSup S) : Set α) = ⋃ i in S, ↑i
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sSup
  条件: {S : Set (Opens α)}
  结论: (↑(sSup S) : Set α) = ⋃ i in S, ↑i
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sSup {S : Set (Opens α)} : (↑(sSup S) : Set α) = ⋃ i in S, ↑i :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_finset_sup` / 定理 `coe_finset_sup`

English:
theorem coe_finset_sup
  given: (f : ι -> Opens α) (s : Finset ι)
  statement: (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f)
  proof: map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Opens α) (Set α)) _ _

@[simp, norm_cast]

中文:
定理 coe_finset_sup
  条件: (f : ι -> Opens α) (s : Finset ι)
  结论: (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f)
  证明: map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Opens α) (Set α)) _ _

@[simp, norm_cast]

Depends on / 依赖: SupBotHom, coe_bot, coe_sup, map_finset_sup
-/
theorem coe_finset_sup (f : ι -> Opens α) (s : Finset ι) : (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f) :=
  map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Opens α) (Set α)) _ _

@[simp, norm_cast]
/--
theorem `coe_finset_inf` / 定理 `coe_finset_inf`

English:
theorem coe_finset_inf
  given: (f : ι -> Opens α) (s : Finset ι)
  statement: (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f)
  proof: map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Opens α) (Set α)) _ _

@[simp, norm_cast]

中文:
定理 coe_finset_inf
  条件: (f : ι -> Opens α) (s : Finset ι)
  结论: (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f)
  证明: map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Opens α) (Set α)) _ _

@[simp, norm_cast]

Depends on / 依赖: InfTopHom, coe_inf, coe_top, map_finset_inf
-/
theorem coe_finset_inf (f : ι -> Opens α) (s : Finset ι) : (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f) :=
  map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Opens α) (Set α)) _ _

@[simp, norm_cast]
/--
lemma `coe_disjoint` / 引理 `coe_disjoint`

English:
lemma coe_disjoint
  given: {s t : Opens α}
  statement: Disjoint (s : Set α) t ↔ Disjoint s t
  proof: by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

中文:
引理 coe_disjoint
  条件: {s t : Opens α}
  结论: Disjoint (s : Set α) t ↔ Disjoint s t
  证明: by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq, disjoint_iff
-/
lemma coe_disjoint {s t : Opens α} : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Opens α)
  body: ⟨⊥⟩

中文:
实例 :
  签名: Inhabited (Opens α)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (Opens α) := ⟨⊥⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (Opens α) where
  body: ext Subsingleton.elim _ _

中文:
实例 [IsEmpty
  签名: α] : Unique (Opens α) where
  定义体: ext Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance [IsEmpty α] : Unique (Opens α) where
uniq _ := ext Subsingleton.elim _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nontrivial (Opens α) where
  body: ⟨⊥, ⊤, mt coe_inj.2 empty_ne_univ⟩

@[simp, norm_cast]

中文:
实例 [Nonempty
  签名: α] : Nontrivial (Opens α) where
  定义体: ⟨⊥, ⊤, mt coe_inj.2 empty_ne_univ⟩

@[simp, norm_cast]

Depends on / 依赖: coe_inj, empty_ne_univ
-/
instance [Nonempty α] : Nontrivial (Opens α) where
  exists_pair_ne := ⟨⊥, ⊤, mt coe_inj.2 empty_ne_univ⟩

@[simp, norm_cast]
/--
theorem `coe_iSup` / 定理 `coe_iSup`

English:
theorem coe_iSup
  given: {ι} (s : ι -> Opens α)
  statement: ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s i
  proof: by
  simp [iSup]

中文:
定理 coe_iSup
  条件: {ι} (s : ι -> Opens α)
  结论: ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s i
  证明: by
  simp [iSup]
-/
theorem coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s i := by
  simp [iSup]

/--
lemma `coe_iInf` / 引理 `coe_iInf`

English:
lemma coe_iInf
  given: {ι : Type*} [Finite ι] (U : ι -> TopologicalSpace.Opens α)
  proof: by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => rw [← e.iInf_comp, ← e.surjective.iInter_comp, ih]
  | h_empty => simp
  | h_option ih => rw [iInf_option, Set.iInter_option, Opens.coe_inf, ih]

中文:
引理 coe_iInf
  条件: {ι : 类型} [Finite ι] (U : ι -> TopologicalSpace.Opens α)
  证明: by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => rw [← e.iInf_comp, ← e.surjective.iInter_comp, ih]
  | h_empty => simp
  | h_option ih => rw [iInf_option, Set.iInter_option, Opens.coe_inf, ih]

Depends on / 依赖: Finite, Finite.induction_empty_option, Opens.coe_inf, Set.iInter_option, coe_inf, e.iInf_comp, e.surjective.iInter_comp, h_empty, h_option, iInf_comp, iInf_option, iInter_comp, iInter_option, induction_empty_option, of_equiv, surjective
-/
lemma coe_iInf {ι : Type*} [Finite ι] (U : ι -> TopologicalSpace.Opens α) :
    (((⨅ i, U i) : Opens α) : Set α) = ⋂ i, U i := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => rw [← e.iInf_comp, ← e.surjective.iInter_comp, ih]
  | h_empty => simp
  | h_option ih => rw [iInf_option, Set.iInter_option, Opens.coe_inf, ih]

/--
theorem `iSup_def` / 定理 `iSup_def`

English:
theorem iSup_def
  given: {ι} (s : ι -> Opens α)
  statement: ⨆ i, s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩
  proof: ext coe_iSup s

@[simp]

中文:
定理 iSup_def
  条件: {ι} (s : ι -> Opens α)
  结论: ⨆ i, s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩
  证明: ext coe_iSup s

@[simp]

Depends on / 依赖: coe_iSup
-/
theorem iSup_def {ι} (s : ι -> Opens α) : ⨆ i, s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩ :=
ext coe_iSup s

@[simp]
/--
theorem `iSup_mk` / 定理 `iSup_mk`

English:
theorem iSup_mk
  given: {ι} (s : ι -> Set α) (h : forall i, IsOpen (s i))
  proof: iSup_def _

@[simp]

中文:
定理 iSup_mk
  条件: {ι} (s : ι -> Set α) (h : 对任意 i, IsOpen (s i))
  证明: iSup_def _

@[simp]

Depends on / 依赖: iSup_def
-/
theorem iSup_mk {ι} (s : ι -> Set α) (h : forall i, IsOpen (s i)) :
    (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩ :=
  iSup_def _

@[simp]
/--
theorem `mem_iSup` / 定理 `mem_iSup`

English:
theorem mem_iSup
  given: {ι} {x : α} {s : ι -> Opens α}
  statement: x in iSup s ↔ exists i, x in s i
  proof: by
  rw [← SetLike.mem_coe]
  simp

@[simp]

中文:
定理 mem_iSup
  条件: {ι} {x : α} {s : ι -> Opens α}
  结论: x in iSup s ↔ 存在 i, x in s i
  证明: by
  rw [← SetLike.mem_coe]
  simp

@[simp]

Depends on / 依赖: SetLike, SetLike.mem_coe, mem_coe
-/
theorem mem_iSup {ι} {x : α} {s : ι -> Opens α} : x in iSup s ↔ exists i, x in s i := by
  rw [← SetLike.mem_coe]
  simp

@[simp]
/--
theorem `mem_sSup` / 定理 `mem_sSup`

English:
theorem mem_sSup
  given: {Us : Set (Opens α)} {x : α}
  statement: x in sSup Us ↔ exists u in Us, x in u
  proof: by
  simp_rw [sSup_eq_iSup, mem_iSup, exists_prop]

中文:
定理 mem_sSup
  条件: {Us : Set (Opens α)} {x : α}
  结论: x in sSup Us ↔ 存在 u in Us, x in u
  证明: by
  simp_rw [sSup_eq_iSup, mem_iSup, exists_prop]

Depends on / 依赖: exists_prop, mem_iSup, sSup_eq_iSup, simp_rw
-/
theorem mem_sSup {Us : Set (Opens α)} {x : α} : x in sSup Us ↔ exists u in Us, x in u := by
  simp_rw [sSup_eq_iSup, mem_iSup, exists_prop]

/--
Instance `instFrame` / 实例 `instFrame`

English:
instance instFrame
  signature: : Frame (Opens α)
  body: fast_instance% .ofMinimalAxioms {
  inf_sSup_le_iSup_inf a s :=
    (ext <| by simp only [coe_inf, coe_iSup, coe_sSup, Set.inter_iUnion₂]).le }

中文:
实例 instFrame
  签名: : Frame (Opens α)
  定义体: fast_instance% .ofMinimalAxioms {
  inf_sSup_le_iSup_inf a s :=
    (ext <| by simp only [coe_inf, coe_iSup, coe_sSup, Set.inter_iUnion₂]).le }

Depends on / 依赖: fast_instance, ofMinimalAxioms
-/
instance instFrame : Frame (Opens α) := fast_instance% .ofMinimalAxioms {
  inf_sSup_le_iSup_inf a s :=
    (ext <| by simp only [coe_inf, coe_iSup, coe_sSup, Set.inter_iUnion₂]).le }

/--
theorem `mem_himp` / 定理 `mem_himp`

English:
theorem mem_himp
  given: {U V : Opens α} {x : α}
  statement: x in U ⇨ V ↔ exists W : Opens α, W ⊓ U <= V ∧ x in W
  proof: by
  simp [himp_eq_sSup]

中文:
定理 mem_himp
  条件: {U V : Opens α} {x : α}
  结论: x in U ⇨ V ↔ 存在 W : Opens α, W ⊓ U <= V ∧ x in W
  证明: by
  simp [himp_eq_sSup]

Depends on / 依赖: himp_eq_sSup
-/
theorem mem_himp {U V : Opens α} {x : α} : x in U ⇨ V ↔ exists W : Opens α, W ⊓ U <= V ∧ x in W := by
  simp [himp_eq_sSup]

/--
theorem `himp_def` / 定理 `himp_def`

English:
theorem himp_def
  given: {U V : Opens α}
  statement: U ⇨ V = Opens.interior ((U : Set α) ⇨ V)
  proof: by
  ext x
  simp_rw [BooleanAlgebra.himp_eq, sup_eq_union, coe_interior, _root_.mem_interior,
    SetLike.mem_coe, mem_himp, ← SetLike.coe_subset_coe, coe_inf, inter_subset]
  exact ⟨fun ⟨⟨W, hW⟩, hsub, hx⟩ => ⟨W, union_comm _ _ ▸ hsub, hW, hx⟩,
    fun ⟨W, hsub, hW, hx⟩ => ⟨⟨W, hW⟩, union_comm _ _

中文:
定理 himp_def
  条件: {U V : Opens α}
  结论: U ⇨ V = Opens.interior ((U : Set α) ⇨ V)
  证明: by
  ext x
  simp_rw [BooleanAlgebra.himp_eq, sup_eq_union, coe_interior, _root_.mem_interior,
    SetLike.mem_coe, mem_himp, ← SetLike.coe_subset_coe, coe_inf, inter_subset]
  exact ⟨fun ⟨⟨W, hW⟩, hsub, hx⟩ => ⟨W, union_comm _ _ ▸ hsub, hW, hx⟩,
    fun ⟨W, hsub, hW, hx⟩ => ⟨⟨W, hW⟩, union_comm _ _

Depends on / 依赖: BooleanAlgebra, BooleanAlgebra.himp_eq, SetLike, SetLike.coe_subset_coe, SetLike.mem_coe, _root_, _root_.mem_interior, coe_inf, coe_interior, coe_subset_coe, himp_eq, inter_subset, mem_coe, mem_himp, mem_interior, simp_rw, sup_eq_union, union_comm
-/
theorem himp_def {U V : Opens α} : U ⇨ V = Opens.interior ((U : Set α) ⇨ V) := by
  ext x
  simp_rw [BooleanAlgebra.himp_eq, sup_eq_union, coe_interior, _root_.mem_interior,
    SetLike.mem_coe, mem_himp, ← SetLike.coe_subset_coe, coe_inf, inter_subset]
  exact ⟨fun ⟨⟨W, hW⟩, hsub, hx⟩ => ⟨W, union_comm _ _ ▸ hsub, hW, hx⟩,
    fun ⟨W, hsub, hW, hx⟩ => ⟨⟨W, hW⟩, union_comm _ _ ▸ hsub, hx⟩⟩

/--
theorem `coe_himp` / 定理 `coe_himp`

English:
theorem coe_himp
  given: {U V : Opens α}
  statement: ↑(U ⇨ V) = interior ((U : Set α) ⇨ V)
  proof: by
  rw [himp_def]; rw [coe_interior]

中文:
定理 coe_himp
  条件: {U V : Opens α}
  结论: ↑(U ⇨ V) = interior ((U : Set α) ⇨ V)
  证明: by
  rw [himp_def]; rw [coe_interior]

Depends on / 依赖: coe_interior, himp_def
-/
theorem coe_himp {U V : Opens α} : ↑(U ⇨ V) = interior ((U : Set α) ⇨ V) := by
  rw [himp_def]; rw [coe_interior]

/--
theorem `mem_compl` / 定理 `mem_compl`

English:
theorem mem_compl
  given: {U : Opens α} {x : α}
  statement: x in Uᶜ ↔ exists V : Opens α, Disjoint V U ∧ x in V
  proof: by
  simp [compl_eq_sSup_disjoint]

中文:
定理 mem_compl
  条件: {U : Opens α} {x : α}
  结论: x in Uᶜ ↔ 存在 V : Opens α, Disjoint V U ∧ x in V
  证明: by
  simp [compl_eq_sSup_disjoint]

Depends on / 依赖: compl_eq_sSup_disjoint
-/
theorem mem_compl {U : Opens α} {x : α} : x in Uᶜ ↔ exists V : Opens α, Disjoint V U ∧ x in V := by
  simp [compl_eq_sSup_disjoint]

/--
theorem `interior_compl` / 定理 `interior_compl`

English:
theorem interior_compl
  given: {U : Opens α}
  statement: Opens.interior (U : Set α)ᶜ = Uᶜ
  proof: by
  simp [← himp_bot, himp_def]

中文:
定理 interior_compl
  条件: {U : Opens α}
  结论: Opens.interior (U : Set α)ᶜ = Uᶜ
  证明: by
  simp [← himp_bot, himp_def]

Depends on / 依赖: himp_bot, himp_def
-/
theorem interior_compl {U : Opens α} : Opens.interior (U : Set α)ᶜ = Uᶜ := by
  simp [← himp_bot, himp_def]

/--
theorem `coe_compl_eq_interior_compl` / 定理 `coe_compl_eq_interior_compl`

English:
theorem coe_compl_eq_interior_compl
  given: {U : Opens α}
  statement: ↑(Uᶜ) = interior (U : Set α)ᶜ
  proof: by
  rw [← interior_compl]; rw [coe_interior]

中文:
定理 coe_compl_eq_interior_compl
  条件: {U : Opens α}
  结论: ↑(Uᶜ) = interior (U : Set α)ᶜ
  证明: by
  rw [← interior_compl]; rw [coe_interior]

Depends on / 依赖: coe_interior, interior_compl
-/
theorem coe_compl_eq_interior_compl {U : Opens α} : ↑(Uᶜ) = interior (U : Set α)ᶜ := by
  rw [← interior_compl]; rw [coe_interior]

/--
Definition of `frameHom` / `frameHom` 的定义

English:
definition frameHom
  signature: : FrameHom (Opens α) (Set α) where
  body: (·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by simp

中文:
定义 frameHom
  签名: : FrameHom (Opens α) (Set α) where
  定义体: (·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by simp
-/
@[simps] protected def frameHom : FrameHom (Opens α) (Set α) where
  toFun := (·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by simp

/--
theorem `isOpenEmbedding'` / 定理 `isOpenEmbedding'`

English:
theorem isOpenEmbedding'
  given: (U : Opens α)
  statement: IsOpenEmbedding (Subtype.val : U -> α)
  proof: U.isOpen.isOpenEmbedding_subtypeVal

中文:
定理 isOpenEmbedding'
  条件: (U : Opens α)
  结论: IsOpenEmbedding (Subtype.val : U -> α)
  证明: U.isOpen.isOpenEmbedding_subtypeVal

Depends on / 依赖: U.isOpen.isOpenEmbedding_subtypeVal, isOpen, isOpenEmbedding_subtypeVal
-/
theorem isOpenEmbedding' (U : Opens α) : IsOpenEmbedding (Subtype.val : U -> α) :=
  U.isOpen.isOpenEmbedding_subtypeVal

/--
theorem `isOpenEmbedding_of_le` / 定理 `isOpenEmbedding_of_le`

English:
theorem isOpenEmbedding_of_le
  given: {U V : Opens α} (i : U <= V)
  proof: .inclusion i
  isOpen_range := by
    rw [Set.range_inclusion i]
    exact U.isOpen.preimage continuous_subtype_val

中文:
定理 isOpenEmbedding_of_le
  条件: {U V : Opens α} (i : U <= V)
  证明: .inclusion i
  isOpen_range := by
    rw [Set.range_inclusion i]
    exact U.isOpen.preimage continuous_subtype_val

Depends on / 依赖: inclusion
-/
theorem isOpenEmbedding_of_le {U V : Opens α} (i : U <= V) :
    IsOpenEmbedding (Set.inclusion <| SetLike.coe_subset_coe.2 i) where
  toIsEmbedding := .inclusion i
  isOpen_range := by
    rw [Set.range_inclusion i]
    exact U.isOpen.preimage continuous_subtype_val

/--
theorem `not_nonempty_iff_eq_bot` / 定理 `not_nonempty_iff_eq_bot`

English:
theorem not_nonempty_iff_eq_bot
  given: (U : Opens α)
  statement: ¬Set.Nonempty (U : Set α) ↔ U = ⊥
  proof: by
  rw [← coe_inj]; rw [coe_bot]; rw [← Set.not_nonempty_iff_eq_empty]

中文:
定理 not_nonempty_iff_eq_bot
  条件: (U : Opens α)
  结论: ¬Set.Nonempty (U : Set α) ↔ U = ⊥
  证明: by
  rw [← coe_inj]; rw [coe_bot]; rw [← Set.not_nonempty_iff_eq_empty]

Depends on / 依赖: Set.not_nonempty_iff_eq_empty, coe_bot, coe_inj, not_nonempty_iff_eq_empty
-/
theorem not_nonempty_iff_eq_bot (U : Opens α) : ¬Set.Nonempty (U : Set α) ↔ U = ⊥ := by
  rw [← coe_inj]; rw [coe_bot]; rw [← Set.not_nonempty_iff_eq_empty]

/--
theorem `ne_bot_iff_nonempty` / 定理 `ne_bot_iff_nonempty`

English:
theorem ne_bot_iff_nonempty
  given: (U : Opens α)
  statement: U != ⊥ ↔ Set.Nonempty (U : Set α)
  proof: by
  rw [Ne]; rw [← not_nonempty_iff_eq_bot]; rw [not_not]

中文:
定理 ne_bot_iff_nonempty
  条件: (U : Opens α)
  结论: U != ⊥ ↔ Set.Nonempty (U : Set α)
  证明: by
  rw [Ne]; rw [← not_nonempty_iff_eq_bot]; rw [not_not]

Depends on / 依赖: not_nonempty_iff_eq_bot, not_not
-/
theorem ne_bot_iff_nonempty (U : Opens α) : U != ⊥ ↔ Set.Nonempty (U : Set α) := by
  rw [Ne]; rw [← not_nonempty_iff_eq_bot]; rw [not_not]

/--
theorem `eq_bot_or_top` / 定理 `eq_bot_or_top`

English:
theorem eq_bot_or_top
  given: [IndiscreteTopology α] (U : Opens α)
  proof: by
  rw [← coe_eq_empty]; rw [← coe_eq_univ]; rw [← IndiscreteTopology.isOpen_iff]
  exact U.2

中文:
定理 eq_bot_or_top
  条件: [IndiscreteTopology α] (U : Opens α)
  证明: by
  rw [← coe_eq_empty]; rw [← coe_eq_univ]; rw [← IndiscreteTopology.isOpen_iff]
  exact U.2

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.isOpen_iff, coe_eq_empty, coe_eq_univ, isOpen_iff
-/
theorem eq_bot_or_top [IndiscreteTopology α] (U : Opens α) :
    U = ⊥ ∨ U = ⊤ := by
  rw [← coe_eq_empty]; rw [← coe_eq_univ]; rw [← IndiscreteTopology.isOpen_iff]
  exact U.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] [IndiscreteTopology α] : IsSimpleOrder (Opens α) where
  body: eq_bot_or_top

中文:
实例 [Nonempty
  签名: α] [IndiscreteTopology α] : IsSimpleOrder (Opens α) where
  定义体: eq_bot_or_top

Depends on / 依赖: eq_bot_or_top
-/
instance [Nonempty α] [IndiscreteTopology α] : IsSimpleOrder (Opens α) where
  eq_bot_or_eq_top := eq_bot_or_top

/--
Definition of `IsBasis` / `IsBasis` 的定义

English:
definition IsBasis
  signature: (B : Set (Opens α))
  body: IsTopologicalBasis (((↑) : _ -> Set α) '' B)

中文:
定义 IsBasis
  签名: (B : Set (Opens α))
  定义体: IsTopologicalBasis (((↑) : _ -> Set α) '' B)

Depends on / 依赖: IsTopologicalBasis
-/
def IsBasis (B : Set (Opens α)) : Prop :=
  IsTopologicalBasis (((↑) : _ -> Set α) '' B)

/--
theorem `isBasis_iff_nbhd` / 定理 `isBasis_iff_nbhd`

English:
theorem isBasis_iff_nbhd
  given: {B : Set (Opens α)}
  proof: by
  constructor <;> intro h
  · rintro ⟨sU, hU⟩ x hx
    rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
    refine ⟨V, H₁, ?_⟩
    cases V
    dsimp at H₂
    subst H₂
    exact hsV
  · refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro sU ⟨U, -, rfl⟩
   

中文:
定理 isBasis_iff_nbhd
  条件: {B : Set (Opens α)}
  证明: by
  constructor <;> intro h
  · rintro ⟨sU, hU⟩ x hx
    rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
    refine ⟨V, H₁, ?_⟩
    cases V
    dsimp at H₂
    subst H₂
    exact hsV
  · refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro sU ⟨U, -, rfl⟩
   

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, h.mem_nhds_iff.mp, isTopologicalBasis_of_isOpen_of_nhds, mem_nhds, mem_nhds_iff
-/
theorem isBasis_iff_nbhd {B : Set (Opens α)} :
    IsBasis B ↔ forall {U : Opens α} {x}, x in U -> exists U' in B, x in U' ∧ U' <= U := by
  constructor <;> intro h
  · rintro ⟨sU, hU⟩ x hx
    rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
    refine ⟨V, H₁, ?_⟩
    cases V
    dsimp at H₂
    subst H₂
    exact hsV
  · refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro sU ⟨U, -, rfl⟩
      exact U.2
    · intro x sU hx hsU
      rcases @h ⟨sU, hsU⟩ x hx with ⟨V, hV, H⟩
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩

/--
theorem `isBasis_iff_cover` / 定理 `isBasis_iff_cover`

English:
theorem isBasis_iff_cover
  given: {B : Set (Opens α)}
  proof: by
  constructor
  · intro hB U
    refine ⟨{ V : Opens α | V in B ∧ V <= U }, fun U hU => hU.left, ext ?_⟩
    rw [coe_sSup]; rw [hB.open_eq_sUnion' U.isOpen]
    simp_rw [sUnion_eq_biUnion, iUnion, mem_ofPred_eq, iSup_and, iSup_image]
    rfl
  · intro h
    rw [isBasis_iff_nbhd]
    intro U x hx


中文:
定理 isBasis_iff_cover
  条件: {B : Set (Opens α)}
  证明: by
  constructor
  · intro hB U
    refine ⟨{ V : Opens α | V in B ∧ V <= U }, fun U hU => hU.left, ext ?_⟩
    rw [coe_sSup]; rw [hB.open_eq_sUnion' U.isOpen]
    simp_rw [sUnion_eq_biUnion, iUnion, mem_ofPred_eq, iSup_and, iSup_image]
    rfl
  · intro h
    rw [isBasis_iff_nbhd]
    intro U x hx


Depends on / 依赖: U.isOpen, coe_sSup, hB.open_eq_sUnion, hU.left, iSup_and, iSup_image, iUnion, isBasis_iff_nbhd, isOpen, le_sSup, mem_ofPred_eq, mem_sSup, open_eq_sUnion, sUnion_eq_biUnion, simp_rw
-/
theorem isBasis_iff_cover {B : Set (Opens α)} :
    IsBasis B ↔ forall U : Opens α, exists Us, Us subseteq B ∧ U = sSup Us := by
  constructor
  · intro hB U
    refine ⟨{ V : Opens α | V in B ∧ V <= U }, fun U hU => hU.left, ext ?_⟩
    rw [coe_sSup]; rw [hB.open_eq_sUnion' U.isOpen]
    simp_rw [sUnion_eq_biUnion, iUnion, mem_ofPred_eq, iSup_and, iSup_image]
    rfl
  · intro h
    rw [isBasis_iff_nbhd]
    intro U x hx
    rcases h U with ⟨Us, hUs, rfl⟩
    rcases mem_sSup.1 hx with ⟨U, Us, xU⟩
    exact ⟨U, hUs Us, xU, le_sSup Us⟩

/--
lemma `IsBasis.exists_iSup_eq` / 引理 `IsBasis.exists_iSup_eq`

English:
lemma IsBasis.exists_iSup_eq
  statement: {X : Type u} [TopologicalSpace X] {ι : Type*}
  proof: by
  obtain ⟨Us, hsub, hUs⟩ := Opens.isBasis_iff_cover.mp hU W
  choose a ha using hsub
  use Us, fun i => a i.2
  simp [hUs, ha, sSup_eq_iSup' Us]

中文:
引理 IsBasis.exists_iSup_eq
  结论: {X : 类型u} [TopologicalSpace X] {ι : 类型}
  证明: by
  obtain ⟨Us, hsub, hUs⟩ := Opens.isBasis_iff_cover.mp hU W
  choose a ha using hsub
  use Us, fun i => a i.2
  simp [hUs, ha, sSup_eq_iSup' Us]

Depends on / 依赖: Opens.isBasis_iff_cover.mp, isBasis_iff_cover, sSup_eq_iSup
-/
lemma IsBasis.exists_iSup_eq {X : Type u} [TopologicalSpace X] {ι : Type*}
    {U : ι -> TopologicalSpace.Opens X} (hU : TopologicalSpace.Opens.IsBasis (Set.range U))
    (W : TopologicalSpace.Opens X) : exists (κ : Type u) (a : κ -> ι), W = ⨆ (k : κ), U (a k) := by
  obtain ⟨Us, hsub, hUs⟩ := Opens.isBasis_iff_cover.mp hU W
  choose a ha using hsub
  use Us, fun i => a i.2
  simp [hUs, ha, sSup_eq_iSup' Us]

/--
lemma `IsBasis.exists_iSup_eq_of_isCompact` / 引理 `IsBasis.exists_iSup_eq_of_isCompact`

English:
lemma IsBasis.exists_iSup_eq_of_isCompact
  statement: {X : Type u} [TopologicalSpace X] {ι : Type*}
  proof: by
  obtain ⟨κ, a, heq⟩ := hU.exists_iSup_eq W
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover _ (fun k : κ => (U (a k)).2) (by simp [heq])
  use s, s.finite_toSet, a ∘ Subtype.val
  refine le_antisymm ?_ ?_
  · simpa [← SetLike.coe_subset_coe, Set.iUnion_subtype]
  · rw [heq, iSup_le_iff]
    intro i
 

中文:
引理 IsBasis.exists_iSup_eq_of_isCompact
  结论: {X : 类型u} [TopologicalSpace X] {ι : 类型}
  证明: by
  obtain ⟨κ, a, heq⟩ := hU.exists_iSup_eq W
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover _ (fun k : κ => (U (a k)).2) (by simp [heq])
  use s, s.finite_toSet, a ∘ Subtype.val
  refine le_antisymm ?_ ?_
  · simpa [← SetLike.coe_subset_coe, Set.iUnion_subtype]
  · rw [heq, iSup_le_iff]
    intro i
 

Depends on / 依赖: Set.iUnion_subtype, SetLike, SetLike.coe_subset_coe, Subtype, Subtype.val, coe_subset_coe, elim_finite_subcover, exists_iSup_eq, finite_toSet, hU.exists_iSup_eq, hW.elim_finite_subcover, iSup_le_iff, iUnion_subtype, le_antisymm, le_iSup_of_le, le_rfl, s.finite_toSet
-/
lemma IsBasis.exists_iSup_eq_of_isCompact {X : Type u} [TopologicalSpace X] {ι : Type*}
    {U : ι -> TopologicalSpace.Opens X} (hU : TopologicalSpace.Opens.IsBasis (Set.range U))
    (W : TopologicalSpace.Opens X) (hW : IsCompact W.1) :
    exists (κ : Type u) (_ : Finite κ) (a : κ -> ι), W = ⨆ (k : κ), U (a k) := by
  obtain ⟨κ, a, heq⟩ := hU.exists_iSup_eq W
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover _ (fun k : κ => (U (a k)).2) (by simp [heq])
  use s, s.finite_toSet, a ∘ Subtype.val
  refine le_antisymm ?_ ?_
  · simpa [← SetLike.coe_subset_coe, Set.iUnion_subtype]
  · rw [heq, iSup_le_iff]
    intro i
    exact le_iSup_of_le _ le_rfl

/--
theorem `IsBasis.isCompact_open_iff_eq_finite_iUnion` / 定理 `IsBasis.isCompact_open_iff_eq_finite_iUnion`

English:
theorem IsBasis.isCompact_open_iff_eq_finite_iUnion
  statement: {ι : Type*} (b : ι -> Opens α)
  proof: by
  apply isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis fun i : ι => (b i).1
  · convert! (config := { transparency := .default }) hb
    ext
    simp
  · exact hb'

中文:
定理 IsBasis.isCompact_open_iff_eq_finite_iUnion
  结论: {ι : 类型} (b : ι -> Opens α)
  证明: by
  apply isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis fun i : ι => (b i).1
  · convert! (config := { transparency := .default }) hb
    ext
    simp
  · exact hb'

Depends on / 依赖: config, convert, isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis, transparency
-/
theorem IsBasis.isCompact_open_iff_eq_finite_iUnion {ι : Type*} (b : ι -> Opens α)
    (hb : IsBasis (Set.range b)) (hb' : forall i, IsCompact (b i : Set α)) (U : Set α) :
    IsCompact U ∧ IsOpen U ↔ exists s : Set ι, s.Finite ∧ U = ⋃ i in s, b i := by
  apply isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis fun i : ι => (b i).1
  · convert! (config := { transparency := .default }) hb
    ext
    simp
  · exact hb'

/--
lemma `IsBasis.exists_finite_of_isCompact` / 引理 `IsBasis.exists_finite_of_isCompact`

English:
lemma IsBasis.exists_finite_of_isCompact
  statement: {B : Set (Opens α)} (hB : IsBasis B) {U : Opens α}
  proof: by
  classical
  obtain ⟨Us', hsub, hsup⟩ := isBasis_iff_cover.mp hB U
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun s : Us' => s.1) (fun s => s.1.2) (by simp [hsup])
  refine ⟨Finset.image Subtype.val t, subset_trans (by simp) hsub, Finset.finite_toSet _, ?_⟩
  exact le_antisymm (subset_trans (a

中文:
引理 IsBasis.exists_finite_of_isCompact
  结论: {B : Set (Opens α)} (hB : IsBasis B) {U : Opens α}
  证明: by
  classical
  obtain ⟨Us', hsub, hsup⟩ := isBasis_iff_cover.mp hB U
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun s : Us' => s.1) (fun s => s.1.2) (by simp [hsup])
  refine ⟨Finset.image Subtype.val t, subset_trans (by simp) hsub, Finset.finite_toSet _, ?_⟩
  exact le_antisymm (subset_trans (a

Depends on / 依赖: Finset, Finset.finite_toSet, Finset.image, Subtype, Subtype.val, U.carrier, carrier, classical, elim_finite_subcover, finite_toSet, hU.elim_finite_subcover, hsup.ge, isBasis_iff_cover, isBasis_iff_cover.mp, le_antisymm, le_trans, sSup_le_sSup, subset_trans
-/
lemma IsBasis.exists_finite_of_isCompact {B : Set (Opens α)} (hB : IsBasis B) {U : Opens α}
    (hU : IsCompact U.1) : exists Us subseteq B, Us.Finite ∧ U = sSup Us := by
  classical
  obtain ⟨Us', hsub, hsup⟩ := isBasis_iff_cover.mp hB U
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun s : Us' => s.1) (fun s => s.1.2) (by simp [hsup])
  refine ⟨Finset.image Subtype.val t, subset_trans (by simp) hsub, Finset.finite_toSet _, ?_⟩
  exact le_antisymm (subset_trans (a := U.carrier) ht (by simp))
    (le_trans (sSup_le_sSup (by simp)) hsup.ge)

/--
lemma `IsBasis.le_iff` / 引理 `IsBasis.le_iff`

English:
lemma IsBasis.le_iff
  statement: {α} {t₁ t₂ : TopologicalSpace α}
  proof: by
  conv_lhs => rw [hUs.eq_generateFrom]
  simp [Set.subset_def, le_generateFrom_iff_subset_isOpen]

中文:
引理 IsBasis.le_iff
  结论: {α} {t₁ t₂ : TopologicalSpace α}
  证明: by
  conv_lhs => rw [hUs.eq_generateFrom]
  simp [Set.subset_def, le_generateFrom_iff_subset_isOpen]

Depends on / 依赖: Set.subset_def, conv_lhs, eq_generateFrom, hUs.eq_generateFrom, le_generateFrom_iff_subset_isOpen, subset_def
-/
lemma IsBasis.le_iff {α} {t₁ t₂ : TopologicalSpace α}
    {Us : Set (Opens α)} (hUs : @IsBasis α t₂ Us) :
    t₁ <= t₂ ↔ forall U in Us, IsOpen[t₁] U := by
  conv_lhs => rw [hUs.eq_generateFrom]
  simp [Set.subset_def, le_generateFrom_iff_subset_isOpen]

/--
lemma `isBasis_sigma` / 引理 `isBasis_sigma`

English:
lemma isBasis_sigma
  statement: {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α i)]
  proof: by
  convert! TopologicalSpace.IsTopologicalBasis.sigma hB
  simp only [IsBasis, Set.image_iUnion, ← Set.image_comp]
  simp

中文:
引理 isBasis_sigma
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, TopologicalSpace (α i)]
  证明: by
  convert! TopologicalSpace.IsTopologicalBasis.sigma hB
  simp only [IsBasis, Set.image_iUnion, ← Set.image_comp]
  simp

Depends on / 依赖: IsBasis, IsTopologicalBasis, Set.image_comp, Set.image_iUnion, TopologicalSpace, TopologicalSpace.IsTopologicalBasis.sigma, convert, image_comp, image_iUnion
-/
lemma isBasis_sigma {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α i)]
    {B : forall i, Set (Opens (α i))} (hB : forall i, IsBasis (B i)) :
    IsBasis (⋃ i : ι, (fun U => ⟨Sigma.mk i '' U.1, isOpenMap_sigmaMk _ U.2⟩) '' B i) := by
  convert! TopologicalSpace.IsTopologicalBasis.sigma hB
  simp only [IsBasis, Set.image_iUnion, ← Set.image_comp]
  simp

/--
lemma `IsBasis.of_isInducing` / 引理 `IsBasis.of_isInducing`

English:
lemma IsBasis.of_isInducing
  given: {B : Set (Opens β)} (H : IsBasis B) {f : α -> β} (h : IsInducing f)
  proof: by
  simp only [IsBasis] at H ⊢
  convert! H.isInducing h
  ext; simp

@[simp]

中文:
引理 IsBasis.of_isInducing
  条件: {B : Set (Opens β)} (H : IsBasis B) {f : α -> β} (h : IsInducing f)
  证明: by
  simp only [IsBasis] at H ⊢
  convert! H.isInducing h
  ext; simp

@[simp]

Depends on / 依赖: H.isInducing, IsBasis, convert, isInducing
-/
lemma IsBasis.of_isInducing {B : Set (Opens β)} (H : IsBasis B) {f : α -> β} (h : IsInducing f) :
    IsBasis { ⟨f ⁻¹' U, U.2.preimage h.continuous⟩ | U in B } := by
  simp only [IsBasis] at H ⊢
  convert! H.isInducing h
  ext; simp

@[simp]
/--
theorem `isCompactElement_iff` / 定理 `isCompactElement_iff`

English:
theorem isCompactElement_iff
  given: (s : Opens α)
  proof: by
  rw [isCompact_iff_finite_subcover]; rw [CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup]
  refine ⟨?_, fun H ι U hU => ?_⟩
  · introv H hU hU'
    obtain ⟨t, ht⟩ := H ι (fun i => ⟨U i, hU i⟩) (by simpa)
    refine ⟨t, Set.Subset.trans ht ?_⟩
    rw [coe_finset_sup]; rw [Finset.su

中文:
定理 isCompactElement_iff
  条件: (s : Opens α)
  证明: by
  rw [isCompact_iff_finite_subcover]; rw [CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup]
  refine ⟨?_, fun H ι U hU => ?_⟩
  · introv H hU hU'
    obtain ⟨t, ht⟩ := H ι (fun i => ⟨U i, hU i⟩) (by simpa)
    refine ⟨t, Set.Subset.trans ht ?_⟩
    rw [coe_finset_sup]; rw [Finset.su

Depends on / 依赖: CompleteLattice, CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup, Finset, Finset.sup_eq_iSup, Set.Subset.trans, Set.iUnion_subset_iff, Subset, coe_finset_sup, iUnion_subset_iff, introv, isCompactElement_iff_exists_le_iSup_of_le_iSup, isCompact_iff_finite_subcover, isOpen, subseteq, sup_eq_iSup
-/
theorem isCompactElement_iff (s : Opens α) :
    IsCompactElement s ↔ IsCompact (s : Set α) := by
  rw [isCompact_iff_finite_subcover]; rw [CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup]
  refine ⟨?_, fun H ι U hU => ?_⟩
  · introv H hU hU'
    obtain ⟨t, ht⟩ := H ι (fun i => ⟨U i, hU i⟩) (by simpa)
    refine ⟨t, Set.Subset.trans ht ?_⟩
    rw [coe_finset_sup]; rw [Finset.sup_eq_iSup]
    rfl
  · obtain ⟨t, ht⟩ :=
      H (fun i => U i) (fun i => (U i).isOpen) (by simpa using show (s : Set α) subseteq ↑(iSup U) from hU)
    refine ⟨t, Set.Subset.trans ht ?_⟩
    simp only [Set.iUnion_subset_iff]
    change forall i in t, U i <= t.sup U
    exact fun i => Finset.le_sup

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : C(α, β))
  body: ⟨f ⁻¹' s, s.2.preimage f.continuous⟩
map_sSup' s := ext by simp only [coe_sSup, preimage_iUnion, biUnion_image, coe_mk]
  map_inf' _ _ := rfl
  map_top' := rfl

@[simp]

中文:
定义 comap
  签名: (f : C(α, β))
  定义体: ⟨f ⁻¹' s, s.2.preimage f.continuous⟩
map_sSup' s := ext by simp only [coe_sSup, preimage_iUnion, biUnion_image, coe_mk]
  map_inf' _ _ := rfl
  map_top' := rfl

@[simp]

Depends on / 依赖: continuous, f.continuous, preimage
-/
def comap (f : C(α, β)) : FrameHom (Opens β) (Opens α) where
  toFun s := ⟨f ⁻¹' s, s.2.preimage f.continuous⟩
map_sSup' s := ext by simp only [coe_sSup, preimage_iUnion, biUnion_image, coe_mk]
  map_inf' _ _ := rfl
  map_top' := rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: comap (ContinuousMap.id α) = FrameHom.id _
  proof: FrameHom.ext fun _ => ext rfl

@[gcongr]

中文:
定理 comap_id
  结论: comap (ContinuousMap.id α) = FrameHom.id _
  证明: FrameHom.ext fun _ => ext rfl

@[gcongr]

Depends on / 依赖: FrameHom, FrameHom.ext
-/
theorem comap_id : comap (ContinuousMap.id α) = FrameHom.id _ :=
  FrameHom.ext fun _ => ext rfl

@[gcongr]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: (f : C(α, β)) {s t : Opens β} (h : s <= t)
  statement: comap f s <= comap f t
  proof: OrderHomClass.mono (comap f) h

@[simp]

中文:
定理 comap_mono
  条件: (f : C(α, β)) {s t : Opens β} (h : s <= t)
  结论: comap f s <= comap f t
  证明: OrderHomClass.mono (comap f) h

@[simp]

Depends on / 依赖: OrderHomClass, OrderHomClass.mono
-/
theorem comap_mono (f : C(α, β)) {s t : Opens β} (h : s <= t) : comap f s <= comap f t :=
  OrderHomClass.mono (comap f) h

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (f : C(α, β)) (U : Opens β)
  statement: ↑(comap f U) = f ⁻¹' U
  proof: rfl

@[simp]

中文:
定理 coe_comap
  条件: (f : C(α, β)) (U : Opens β)
  结论: ↑(comap f U) = f ⁻¹' U
  证明: rfl

@[simp]
-/
theorem coe_comap (f : C(α, β)) (U : Opens β) : ↑(comap f U) = f ⁻¹' U :=
  rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {f : C(α, β)} {U : Opens β} {x : α}
  statement: x in comap f U ↔ f x in U
  proof: .rfl

中文:
定理 mem_comap
  条件: {f : C(α, β)} {U : Opens β} {x : α}
  结论: x in comap f U ↔ f x in U
  证明: .rfl
-/
theorem mem_comap {f : C(α, β)} {U : Opens β} {x : α} : x in comap f U ↔ f x in U := .rfl

/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: (g : C(β, γ)) (f : C(α, β))
  proof: rfl

中文:
定理 comap_comp
  条件: (g : C(β, γ)) (f : C(α, β))
  证明: rfl
-/
protected theorem comap_comp (g : C(β, γ)) (f : C(α, β)) :
    comap (g.comp f) = (comap f).comp (comap g) :=
  rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (g : C(β, γ)) (f : C(α, β)) (U : Opens γ)
  proof: rfl

中文:
定理 comap_comap
  条件: (g : C(β, γ)) (f : C(α, β)) (U : Opens γ)
  证明: rfl
-/
protected theorem comap_comap (g : C(β, γ)) (f : C(α, β)) (U : Opens γ) :
    comap f (comap g U) = comap (g.comp f) U :=
  rfl

/--
theorem `comap_injective` / 定理 `comap_injective`

English:
theorem comap_injective
  given: [T0Space β]
  statement: Injective (comap : C(α, β) -> FrameHom (Opens β) (Opens α))
  proof: fun f g h =>
  ContinuousMap.ext fun a =>
Inseparable.eq
      inseparable_iff_forall_isOpen.2 fun s hs =>
        have : comap f ⟨s, hs⟩ = comap g ⟨s, hs⟩ := DFunLike.congr_fun h ⟨_, hs⟩
        show a in f ⁻¹' s ↔ a in g ⁻¹' s from Set.ext_iff.1 (coe_inj.2 this) a

中文:
定理 comap_injective
  条件: [T0Space β]
  结论: Injective (comap : C(α, β) -> FrameHom (Opens β) (Opens α))
  证明: fun f g h =>
  ContinuousMap.ext fun a =>
Inseparable.eq
      inseparable_iff_forall_isOpen.2 fun s hs =>
        have : comap f ⟨s, hs⟩ = comap g ⟨s, hs⟩ := DFunLike.congr_fun h ⟨_, hs⟩
        show a in f ⁻¹' s ↔ a in g ⁻¹' s from Set.ext_iff.1 (coe_inj.2 this) a

Depends on / 依赖: ContinuousMap, ContinuousMap.ext, DFunLike, DFunLike.congr_fun, Inseparable, Inseparable.eq, Set.ext_iff, coe_inj, congr_fun, ext_iff, inseparable_iff_forall_isOpen
-/
theorem comap_injective [T0Space β] : Injective (comap : C(α, β) -> FrameHom (Opens β) (Opens α)) :=
  fun f g h =>
  ContinuousMap.ext fun a =>
Inseparable.eq
      inseparable_iff_forall_isOpen.2 fun s hs =>
        have : comap f ⟨s, hs⟩ = comap g ⟨s, hs⟩ := DFunLike.congr_fun h ⟨_, hs⟩
        show a in f ⁻¹' s ↔ a in g ⁻¹' s from Set.ext_iff.1 (coe_inj.2 this) a

/-- A homeomorphism induces an order-preserving equivalence on open sets, by taking comaps. -/
@[simps -fullyApplied apply]
/--
Definition of `_root_.Homeomorph.opensCongr` / `_root_.Homeomorph.opensCongr` 的定义

English:
definition _root_.Homeomorph.opensCongr
  signature: (f : α ≃ₜ β)
  body: Opens.comap (f.symm : C(β, α))
  invFun := Opens.comap (f : C(α, β))
left_inv _ := ext f.toEquiv.preimage_symm_preimage _
right_inv _ := ext f.toEquiv.symm_preimage_preimage _
  map_rel_iff' := by
    simp only [← SetLike.coe_subset_coe]; exact f.symm.surjective.preimage_subset_preimage_iff

@[simp]

中文:
定义 _root_.Homeomorph.opensCongr
  签名: (f : α ≃ₜ β)
  定义体: Opens.comap (f.symm : C(β, α))
  invFun := Opens.comap (f : C(α, β))
left_inv _ := ext f.toEquiv.preimage_symm_preimage _
right_inv _ := ext f.toEquiv.symm_preimage_preimage _
  map_rel_iff' := by
    simp only [← SetLike.coe_subset_coe]; exact f.symm.surjective.preimage_subset_preimage_iff

@[simp]

Depends on / 依赖: Opens.comap, f.symm
-/
def _root_.Homeomorph.opensCongr (f : α ≃ₜ β) : Opens α ≃o Opens β where
  toFun := Opens.comap (f.symm : C(β, α))
  invFun := Opens.comap (f : C(α, β))
left_inv _ := ext f.toEquiv.preimage_symm_preimage _
right_inv _ := ext f.toEquiv.symm_preimage_preimage _
  map_rel_iff' := by
    simp only [← SetLike.coe_subset_coe]; exact f.symm.surjective.preimage_subset_preimage_iff

@[simp]
/--
theorem `_root_.Homeomorph.opensCongr_symm` / 定理 `_root_.Homeomorph.opensCongr_symm`

English:
theorem _root_.Homeomorph.opensCongr_symm
  given: (f : α ≃ₜ β)
  statement: f.opensCongr.symm = f.symm.opensCongr
  proof: rfl

中文:
定理 _root_.Homeomorph.opensCongr_symm
  条件: (f : α ≃ₜ β)
  结论: f.opensCongr.symm = f.symm.opensCongr
  证明: rfl
-/
theorem _root_.Homeomorph.opensCongr_symm (f : α ≃ₜ β) : f.opensCongr.symm = f.symm.opensCongr :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] : Finite (Opens α)
  body: Finite.of_injective _ SetLike.coe_injective

中文:
实例 [Finite
  签名: α] : Finite (Opens α)
  定义体: Finite.of_injective _ SetLike.coe_injective

Depends on / 依赖: Finite, Finite.of_injective, SetLike, SetLike.coe_injective, coe_injective, of_injective
-/
instance [Finite α] : Finite (Opens α) :=
  Finite.of_injective _ SetLike.coe_injective

end Opens

/--
Definition of `OpenNhdsOf` / `OpenNhdsOf` 的定义

English:
structure OpenNhdsOf
  parameters: (x : α)
  extends: Opens α
  axioms and operations (1):
    - mem' : x in carrier

中文:
结构 OpenNhdsOf
  参数: (x : α)
  继承: Opens α
  公理与运算 (1 个):
    - mem' : x in carrier
-/
structure OpenNhdsOf (x : α) extends Opens α where
  /-- The point `x` belongs to every `U : TopologicalSpace.OpenNhdsOf x`. -/
  mem' : x in carrier

namespace OpenNhdsOf

variable {x : α}

/--
theorem `toOpens_injective` / 定理 `toOpens_injective`

English:
theorem toOpens_injective
  statement: Injective (toOpens : OpenNhdsOf x -> Opens α)

中文:
定理 toOpens_injective
  结论: Injective (toOpens : OpenNhdsOf x -> Opens α)
-/
theorem toOpens_injective : Injective (toOpens : OpenNhdsOf x -> Opens α)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (OpenNhdsOf x) α
  body: U.1
  coe_injective := SetLike.coe_injective.comp toOpens_injective

中文:
实例 :
  签名: SetLike (OpenNhdsOf x) α
  定义体: U.1
  coe_injective := SetLike.coe_injective.comp toOpens_injective
-/
instance : SetLike (OpenNhdsOf x) α where
  coe U := U.1
  coe_injective := SetLike.coe_injective.comp toOpens_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (OpenNhdsOf x)
  body: fast_instance% .ofSetLike (OpenNhdsOf x) α

中文:
实例 :
  签名: PartialOrder (OpenNhdsOf x)
  定义体: fast_instance% .ofSetLike (OpenNhdsOf x) α

Depends on / 依赖: OpenNhdsOf, fast_instance, ofSetLike
-/
instance : PartialOrder (OpenNhdsOf x) := fast_instance% .ofSetLike (OpenNhdsOf x) α

/--
Instance `canLiftSet` / 实例 `canLiftSet`

English:
instance canLiftSet
  signature: : CanLift (Set α) (OpenNhdsOf x) (↑) fun s => IsOpen s ∧ x in s
  body: ⟨fun s hs => ⟨⟨⟨s, hs.1⟩, hs.2⟩, rfl⟩⟩

中文:
实例 canLiftSet
  签名: : CanLift (Set α) (OpenNhdsOf x) (↑) fun s => IsOpen s ∧ x in s
  定义体: ⟨fun s hs => ⟨⟨⟨s, hs.1⟩, hs.2⟩, rfl⟩⟩
-/
instance canLiftSet : CanLift (Set α) (OpenNhdsOf x) (↑) fun s => IsOpen s ∧ x in s :=
  ⟨fun s hs => ⟨⟨⟨s, hs.1⟩, hs.2⟩, rfl⟩⟩

/--
theorem `mem` / 定理 `mem`

English:
theorem mem
  given: (U : OpenNhdsOf x)
  statement: x in U
  proof: U.mem'

中文:
定理 mem
  条件: (U : OpenNhdsOf x)
  结论: x in U
  证明: U.mem'
-/
protected theorem mem (U : OpenNhdsOf x) : x in U :=
  U.mem'

/--
theorem `isOpen` / 定理 `isOpen`

English:
theorem isOpen
  given: (U : OpenNhdsOf x)
  statement: IsOpen (U : Set α)
  proof: U.is_open'

中文:
定理 isOpen
  条件: (U : OpenNhdsOf x)
  结论: IsOpen (U : Set α)
  证明: U.is_open'
-/
protected theorem isOpen (U : OpenNhdsOf x) : IsOpen (U : Set α) :=
  U.is_open'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (OpenNhdsOf x)
  body: ⟨⊤, Set.mem_univ _⟩
  le_top _ := subset_univ _

中文:
实例 :
  签名: OrderTop (OpenNhdsOf x)
  定义体: ⟨⊤, Set.mem_univ _⟩
  le_top _ := subset_univ _

Depends on / 依赖: Set.mem_univ, mem_univ
-/
instance : OrderTop (OpenNhdsOf x) where
  top := ⟨⊤, Set.mem_univ _⟩
  le_top _ := subset_univ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (OpenNhdsOf x)
  body: ⟨⊤⟩

中文:
实例 :
  签名: Inhabited (OpenNhdsOf x)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (OpenNhdsOf x) := ⟨⊤⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (OpenNhdsOf x)
  body: ⟨fun U V => ⟨U.1 ⊓ V.1, U.2, V.2⟩⟩

中文:
实例 :
  签名: Min (OpenNhdsOf x)
  定义体: ⟨fun U V => ⟨U.1 ⊓ V.1, U.2, V.2⟩⟩
-/
instance : Min (OpenNhdsOf x) := ⟨fun U V => ⟨U.1 ⊓ V.1, U.2, V.2⟩⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (OpenNhdsOf x)
  body: ⟨fun U V => ⟨U.1 ⊔ V.1, Or.inl U.2⟩⟩

中文:
实例 :
  签名: Max (OpenNhdsOf x)
  定义体: ⟨fun U V => ⟨U.1 ⊔ V.1, Or.inl U.2⟩⟩

Depends on / 依赖: Or.inl
-/
instance : Max (OpenNhdsOf x) := ⟨fun U V => ⟨U.1 ⊔ V.1, Or.inl U.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Unique (OpenNhdsOf x) where
  body: SetLike.ext' Subsingleton.eq_univ_of_nonempty ⟨x, U.mem⟩

中文:
实例 [Subsingleton
  签名: α] : Unique (OpenNhdsOf x) where
  定义体: SetLike.ext' Subsingleton.eq_univ_of_nonempty ⟨x, U.mem⟩

Depends on / 依赖: SetLike, SetLike.ext, Subsingleton, Subsingleton.eq_univ_of_nonempty, U.mem, eq_univ_of_nonempty
-/
instance [Subsingleton α] : Unique (OpenNhdsOf x) where
uniq U := SetLike.ext' Subsingleton.eq_univ_of_nonempty ⟨x, U.mem⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribLattice (OpenNhdsOf x)
  body: fast_instance%
  toOpens_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: DistribLattice (OpenNhdsOf x)
  定义体: fast_instance%
  toOpens_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance : DistribLattice (OpenNhdsOf x) := fast_instance%
  toOpens_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

/--
theorem `basis_nhds` / 定理 `basis_nhds`

English:
theorem basis_nhds
  statement: (𝓝 x).HasBasis (fun _ : OpenNhdsOf x => True) (↑)
  proof: (nhds_basis_opens x).to_hasBasis (fun U hU => ⟨⟨⟨U, hU.2⟩, hU.1⟩, trivial, Subset.rfl⟩) fun U _ =>
    ⟨U, ⟨⟨U.mem, U.isOpen⟩, Subset.rfl⟩⟩

中文:
定理 basis_nhds
  结论: (𝓝 x).HasBasis (fun _ : OpenNhdsOf x => True) (↑)
  证明: (nhds_basis_opens x).to_hasBasis (fun U hU => ⟨⟨⟨U, hU.2⟩, hU.1⟩, trivial, Subset.rfl⟩) fun U _ =>
    ⟨U, ⟨⟨U.mem, U.isOpen⟩, Subset.rfl⟩⟩

Depends on / 依赖: Subset, Subset.rfl, U.isOpen, U.mem, isOpen, nhds_basis_opens, to_hasBasis
-/
theorem basis_nhds : (𝓝 x).HasBasis (fun _ : OpenNhdsOf x => True) (↑) :=
  (nhds_basis_opens x).to_hasBasis (fun U hU => ⟨⟨⟨U, hU.2⟩, hU.1⟩, trivial, Subset.rfl⟩) fun U _ =>
    ⟨U, ⟨⟨U.mem, U.isOpen⟩, Subset.rfl⟩⟩

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : C(α, β)) (x : α)
  body: ⟨Opens.comap f U.1, U.mem⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 comap
  签名: (f : C(α, β)) (x : α)
  定义体: ⟨Opens.comap f U.1, U.mem⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

Depends on / 依赖: Opens.comap, U.mem
-/
def comap (f : C(α, β)) (x : α) : LatticeHom (OpenNhdsOf (f x)) (OpenNhdsOf x) where
  toFun U := ⟨Opens.comap f U.1, U.mem⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

end OpenNhdsOf

end TopologicalSpace

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: once we port `auto_cases`, port this
-- namespace Tactic

-- namespace AutoCases

-- /-- Find an `auto_cases_tac` which matches `TopologicalSpace.Opens`. -/
-- unsafe def opens_find_tac : expr → Option auto_cases_tac
-- | q(TopologicalSpace.Opens _) => tac_cases
-- | _ => none

-- end AutoCases

-- /-- A version of `tactic.auto_cases` that works for `TopologicalSpace.Opens`. -/
-- @[hint_tactic]
-- unsafe def auto_cases_opens : tactic String :=
-- auto_cases tactic.auto_cases.opens_find_tac

-- end Tactic
