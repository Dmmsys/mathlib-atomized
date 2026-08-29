/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.QuasiSeparated

/-!
# Compact sets

We define a few types of compact sets in a topological space.

## Main Definitions

For a topological space `α`,
* `TopologicalSpace.Compacts α`: The type of compact sets.
* `TopologicalSpace.NonemptyCompacts α`: The type of non-empty compact sets.
* `TopologicalSpace.PositiveCompacts α`: The type of compact sets with non-empty interior.
* `TopologicalSpace.CompactOpens α`: The type of compact open sets. This is a central object in the
  study of spectral spaces.
-/

@[expose] public section


open Set

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

/-! ### Compact sets -/

/--
Definition of `Compacts` / `Compacts` 的定义

English:
structure Compacts
  parameters: (α : Type*) [TopologicalSpace α]
  axioms and operations (2):
    - carrier : Set α
    - isCompact' : IsCompact carrier

中文:
结构 余mpacts
  参数: (α : 类型) [拓扑空间 α]
  公理与运算 (2 个):
    - carrier : 集合 α
    - isCompact' : 是紧集 carrier
-/
structure Compacts (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isCompact' : IsCompact carrier

namespace Compacts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Compacts α) α
  body: Compacts.carrier
  coe_injective s t h := by cases s; cases t; congr

中文:
实例 :
  签名: 集合状 (余mpacts α) α
  定义体: Compacts.carrier
  coe_injective s t h := by cases s; cases t; congr

Depends on / 依赖: Compacts, Compacts.carrier, carrier
-/
instance : SetLike (Compacts α) α where
  coe := Compacts.carrier
  coe_injective s t h := by cases s; cases t; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Compacts α)
  body: .ofSetLike (Compacts α) α

中文:
实例 :
  签名: 偏序 (余mpacts α)
  定义体: .ofSetLike (Compacts α) α

Depends on / 依赖: Compacts, ofSetLike
-/
instance : PartialOrder (Compacts α) := .ofSetLike (Compacts α) α

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (s : Compacts α)
  body: s

initialize_simps_projections Compacts (carrier -> coe, as_prefix coe)

中文:
定义 Simps.coe
  签名: (s : 余mpacts α)
  定义体: s

initialize_simps_projections Compacts (carrier -> coe, as_prefix coe)
-/
def Simps.coe (s : Compacts α) : Set α := s

initialize_simps_projections Compacts (carrier -> coe, as_prefix coe)

/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  given: (s : Compacts α)
  statement: IsCompact (s : Set α)
  proof: s.isCompact'

中文:
定理 isCompact
  条件: (s : 余mpacts α)
  结论: 是紧集 (s : 集合 α)
  证明: s.isCompact'
-/
protected theorem isCompact (s : Compacts α) : IsCompact (s : Set α) :=
  s.isCompact'

instance (K : Compacts α) : CompactSpace K :=
  isCompact_iff_compactSpace.1 K.isCompact

/-- Reinterpret a compact as a closed set. -/
@[simps]
/--
Definition of `toCloseds` / `toCloseds` 的定义

English:
definition toCloseds
  signature: [T2Space α] (s : Compacts α)
  body: ⟨s, s.isCompact.isClosed⟩

@[simp]

中文:
定义 toCloseds
  签名: [T2空间 α] (s : 余mpacts α)
  定义体: ⟨s, s.isCompact.isClosed⟩

@[simp]

Depends on / 依赖: isClosed, isCompact, s.isCompact.isClosed
-/
def toCloseds [T2Space α] (s : Compacts α) : Closeds α :=
  ⟨s, s.isCompact.isClosed⟩

@[simp]
/--
theorem `mem_toCloseds` / 定理 `mem_toCloseds`

English:
theorem mem_toCloseds
  given: [T2Space α] {x : α} {s : Compacts α}
  proof: Iff.rfl

中文:
定理 mem_toCloseds
  条件: [T2空间 α] {x : α} {s : 余mpacts α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toCloseds [T2Space α] {x : α} {s : Compacts α} :
    x in s.toCloseds ↔ x in s :=
  Iff.rfl

/--
theorem `toCloseds_injective` / 定理 `toCloseds_injective`

English:
theorem toCloseds_injective
  given: [T2Space α]
  statement: Function.Injective (toCloseds (α := α))
  proof: .of_comp (f := SetLike.coe) SetLike.coe_injective

中文:
定理 toCloseds_injective
  条件: [T2空间 α]
  结论: 函数.单射 (toCloseds (α := α))
  证明: .of_comp (f := SetLike.coe) SetLike.coe_injective
-/
theorem toCloseds_injective [T2Space α] : Function.Injective (toCloseds (α := α)) :=
  .of_comp (f := SetLike.coe) SetLike.coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (Set α) (Compacts α) (↑) IsCompact
  body: ⟨⟨K, hK⟩, rfl⟩

@[ext]

中文:
实例 :
  签名: CanLift (集合 α) (余mpacts α) (↑) 是紧集
  定义体: ⟨⟨K, hK⟩, rfl⟩

@[ext]
-/
instance : CanLift (Set α) (Compacts α) (↑) IsCompact where prf K hK := ⟨⟨K, hK⟩, rfl⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : Compacts α} (h : (s : Set α) = t)
  statement: s = t
  proof: SetLike.ext' h

@[simp]

中文:
定理 ext
  条件: {s t : 余mpacts α} (h : (s : 集合 α) = t)
  结论: s = t
  证明: SetLike.ext' h

@[simp]
-/
protected theorem ext {s t : Compacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Set α) (h)
  statement: (mk s h : Set α) = s
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (s : 集合 α) (h)
  结论: (mk s h : 集合 α) = s
  证明: rfl

@[simp]
-/
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp]
/--
theorem `carrier_eq_coe` / 定理 `carrier_eq_coe`

English:
theorem carrier_eq_coe
  given: (s : Compacts α)
  statement: s.carrier = s
  proof: rfl

中文:
定理 carrier_eq_coe
  条件: (s : 余mpacts α)
  结论: s.carrier = s
  证明: rfl
-/
theorem carrier_eq_coe (s : Compacts α) : s.carrier = s :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Compacts α)
  body: ⟨fun s t => ⟨s union t, s.isCompact.union t.isCompact⟩⟩

中文:
实例 :
  签名: 最大值 (余mpacts α)
  定义体: ⟨fun s t => ⟨s union t, s.isCompact.union t.isCompact⟩⟩

Depends on / 依赖: isCompact, s.isCompact.union, t.isCompact
-/
instance : Max (Compacts α) :=
  ⟨fun s t => ⟨s union t, s.isCompact.union t.isCompact⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: α] : Min (Compacts α)
  body: ⟨fun s t => ⟨s inter t, s.isCompact.inter t.isCompact⟩⟩

中文:
实例 [T2空间
  签名: α] : 最小值 (余mpacts α)
  定义体: ⟨fun s t => ⟨s inter t, s.isCompact.inter t.isCompact⟩⟩

Depends on / 依赖: isCompact, s.isCompact.inter, t.isCompact
-/
instance [T2Space α] : Min (Compacts α) :=
  ⟨fun s t => ⟨s inter t, s.isCompact.inter t.isCompact⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] : Top (Compacts α)
  body: ⟨⟨univ, isCompact_univ⟩⟩

中文:
实例 [紧空间
  签名: α] : 顶元素 (余mpacts α)
  定义体: ⟨⟨univ, isCompact_univ⟩⟩

Depends on / 依赖: isCompact_univ
-/
instance [CompactSpace α] : Top (Compacts α) :=
  ⟨⟨univ, isCompact_univ⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Compacts α)
  body: ⟨⟨∅, isCompact_empty⟩⟩

中文:
实例 :
  签名: 底元素 (余mpacts α)
  定义体: ⟨⟨∅, isCompact_empty⟩⟩

Depends on / 依赖: isCompact_empty
-/
instance : Bot (Compacts α) :=
  ⟨⟨∅, isCompact_empty⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (Compacts α)
  body: fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

中文:
实例 :
  签名: SemilatticeSup (余mpacts α)
  定义体: fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

Depends on / 依赖: SetLike, SetLike.coe_injective.semilatticeSup, coe_injective, fast_instance, semilatticeSup
-/
instance : SemilatticeSup (Compacts α) :=
  fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: α] : DistribLattice (Compacts α)
  body: fast_instance% SetLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [T2空间
  签名: α] : Distrib格 (余mpacts α)
  定义体: fast_instance% SetLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: SetLike, SetLike.coe_injective.distribLattice, coe_injective, distribLattice, fast_instance
-/
instance [T2Space α] : DistribLattice (Compacts α) :=
  fast_instance% SetLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (Compacts α)
  body: fast_instance% OrderBot.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl

中文:
实例 :
  签名: 有底序 (余mpacts α)
  定义体: fast_instance% OrderBot.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl

Depends on / 依赖: OrderBot, OrderBot.lift, fast_instance
-/
instance : OrderBot (Compacts α) :=
  fast_instance% OrderBot.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] : BoundedOrder (Compacts α)
  body: fast_instance% BoundedOrder.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl rfl

中文:
实例 [紧空间
  签名: α] : 有界序 (余mpacts α)
  定义体: fast_instance% BoundedOrder.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl rfl

Depends on / 依赖: BoundedOrder, BoundedOrder.lift, fast_instance
-/
instance [CompactSpace α] : BoundedOrder (Compacts α) :=
  fast_instance% BoundedOrder.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Compacts α)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (余mpacts α)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (Compacts α) := ⟨⊥⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (Compacts α) where
  body: Compacts.ext (Subsingleton.elim _ _)

@[simp]

中文:
实例 [是空
  签名: α] : 唯一 (余mpacts α) where
  定义体: Compacts.ext (Subsingleton.elim _ _)

@[simp]

Depends on / 依赖: Compacts, Compacts.ext, Subsingleton, Subsingleton.elim
-/
instance [IsEmpty α] : Unique (Compacts α) where
  uniq _ := Compacts.ext (Subsingleton.elim _ _)

@[simp]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (s t : Compacts α)
  statement: (↑(s ⊔ t) : Set α) = ↑s union ↑t
  proof: rfl

@[simp]

中文:
定理 coe_sup
  条件: (s t : 余mpacts α)
  结论: (↑(s ⊔ t) : 集合 α) = ↑s union ↑t
  证明: rfl

@[simp]
-/
theorem coe_sup (s t : Compacts α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t :=
  rfl

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: [T2Space α] (s t : Compacts α)
  statement: (↑(s ⊓ t) : Set α) = ↑s inter ↑t
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: [T2空间 α] (s t : 余mpacts α)
  结论: (↑(s ⊓ t) : 集合 α) = ↑s inter ↑t
  证明: rfl

@[simp]
-/
theorem coe_inf [T2Space α] (s t : Compacts α) : (↑(s ⊓ t) : Set α) = ↑s inter ↑t :=
  rfl

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  given: [CompactSpace α]
  statement: (↑(⊤ : Compacts α) : Set α) = univ
  proof: rfl

@[simp]

中文:
定理 coe_top
  条件: [紧空间 α]
  结论: (↑(⊤ : 余mpacts α) : 集合 α) = univ
  证明: rfl

@[simp]
-/
theorem coe_top [CompactSpace α] : (↑(⊤ : Compacts α) : Set α) = univ :=
  rfl

@[simp]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: (↑(⊥ : Compacts α) : Set α) = ∅
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_bot
  结论: (↑(⊥ : 余mpacts α) : 集合 α) = ∅
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_bot : (↑(⊥ : Compacts α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_eq_empty` / 定理 `coe_eq_empty`

English:
theorem coe_eq_empty
  given: {s : Compacts α}
  statement: (s : Set α) = ∅ ↔ s = ⊥
  proof: SetLike.coe_injective.eq_iff' rfl

@[simp]

中文:
定理 coe_eq_empty
  条件: {s : 余mpacts α}
  结论: (s : 集合 α) = ∅ ↔ s = ⊥
  证明: SetLike.coe_injective.eq_iff' rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective.eq_iff, coe_injective, eq_iff
-/
theorem coe_eq_empty {s : Compacts α} : (s : Set α) = ∅ ↔ s = ⊥ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp]
/--
theorem `coe_nonempty` / 定理 `coe_nonempty`

English:
theorem coe_nonempty
  given: {s : Compacts α}
  statement: (s : Set α).Nonempty ↔ s != ⊥
  proof: nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp]

中文:
定理 coe_nonempty
  条件: {s : 余mpacts α}
  结论: (s : 集合 α).非空 ↔ s != ⊥
  证明: nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp]

Depends on / 依赖: coe_eq_empty, coe_eq_empty.not, nonempty_iff_ne_empty, nonempty_iff_ne_empty.trans
-/
theorem coe_nonempty {s : Compacts α} : (s : Set α).Nonempty ↔ s != ⊥ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp]
/--
theorem `coe_finset_sup` / 定理 `coe_finset_sup`

English:
theorem coe_finset_sup
  given: {ι : Type*} {s : Finset ι} {f : ι -> Compacts α}
  proof: by
  refine Finset.cons_induction_on s rfl fun a s _ h => ?_
  simp_rw [Finset.sup_cons, coe_sup, sup_eq_union]
  congr

@[simps]

中文:
定理 coe_finset_sup
  条件: {ι : 类型} {s : 有限集 ι} {f : ι -> 余mpacts α}
  证明: by
  refine Finset.cons_induction_on s rfl fun a s _ h => ?_
  simp_rw [Finset.sup_cons, coe_sup, sup_eq_union]
  congr

@[simps]

Depends on / 依赖: Finset, Finset.cons_induction_on, Finset.sup_cons, coe_sup, cons_induction_on, simp_rw, sup_cons, sup_eq_union
-/
theorem coe_finset_sup {ι : Type*} {s : Finset ι} {f : ι -> Compacts α} :
    (↑(s.sup f) : Set α) = s.sup fun i => ↑(f i) := by
  refine Finset.cons_induction_on s rfl fun a s _ h => ?_
  simp_rw [Finset.sup_cons, coe_sup, sup_eq_union]
  congr

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Singleton α (Compacts α)
  body: ⟨{x}, isCompact_singleton⟩

@[simp]

中文:
实例 :
  签名: 单例 α (余mpacts α)
  定义体: ⟨{x}, isCompact_singleton⟩

@[simp]

Depends on / 依赖: isCompact_singleton
-/
instance : Singleton α (Compacts α) where
  singleton x := ⟨{x}, isCompact_singleton⟩

@[simp]
/--
theorem `mem_singleton` / 定理 `mem_singleton`

English:
theorem mem_singleton
  given: (x y : α)
  statement: x in ({y} : Compacts α) ↔ x = y
  proof: Iff.rfl

@[simp]

中文:
定理 mem_singleton
  条件: (x y : α)
  结论: x in ({y} : 余mpacts α) ↔ x = y
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_singleton (x y : α) : x in ({y} : Compacts α) ↔ x = y :=
  Iff.rfl

@[simp]
/--
theorem `toCloseds_singleton` / 定理 `toCloseds_singleton`

English:
theorem toCloseds_singleton
  given: [T2Space α] (x : α)
  statement: toCloseds {x} = {x}
  proof: rfl

中文:
定理 toCloseds_singleton
  条件: [T2空间 α] (x : α)
  结论: toCloseds {x} = {x}
  证明: rfl
-/
theorem toCloseds_singleton [T2Space α] (x : α) : toCloseds {x} = {x} :=
  rfl

/--
theorem `singleton_injective` / 定理 `singleton_injective`

English:
theorem singleton_injective
  statement: Function.Injective ({·} : α -> Compacts α)
  proof: .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]

中文:
定理 singleton_injective
  结论: 函数.单射 ({·} : α -> 余mpacts α)
  证明: .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]

Depends on / 依赖: Set.singleton_injective, SetLike, SetLike.coe, of_comp, singleton_injective
-/
theorem singleton_injective : Function.Injective ({·} : α -> Compacts α) :=
  .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]
/--
theorem `singleton_inj` / 定理 `singleton_inj`

English:
theorem singleton_inj
  given: {x y : α}
  statement: ({x} : Compacts α) = {y} ↔ x = y
  proof: singleton_injective.eq_iff

中文:
定理 singleton_inj
  条件: {x y : α}
  结论: ({x} : 余mpacts α) = {y} ↔ x = y
  证明: singleton_injective.eq_iff

Depends on / 依赖: eq_iff, singleton_injective, singleton_injective.eq_iff
-/
theorem singleton_inj {x y : α} : ({x} : Compacts α) = {y} ↔ x = y :=
  singleton_injective.eq_iff

/--
theorem `disjoint_coe_iff` / 定理 `disjoint_coe_iff`

English:
theorem disjoint_coe_iff
  given: (K L : Compacts α)
  statement: Disjoint (K : Set α) L ↔ Disjoint K L where
  proof: .of_orderEmbedding (.ofMapLEIff SetLike.coe (fun _ _ => SetLike.coe_subset_coe)) h
  mpr h := by
    rw [Set.disjoint_iff]
    intro x ⟨hxK, hxL⟩
    specialize @h {x}
    simp_rw [← SetLike.coe_subset_coe, coe_singleton, singleton_subset_iff] at h
    exact h hxK hxL

中文:
定理 disjoint_coe_iff
  条件: (K L : 余mpacts α)
  结论: Disjoint (K : 集合 α) L ↔ Disjoint K L where
  证明: .of_orderEmbedding (.ofMapLEIff SetLike.coe (fun _ _ => SetLike.coe_subset_coe)) h
  mpr h := by
    rw [Set.disjoint_iff]
    intro x ⟨hxK, hxL⟩
    specialize @h {x}
    simp_rw [← SetLike.coe_subset_coe, coe_singleton, singleton_subset_iff] at h
    exact h hxK hxL

Depends on / 依赖: SetLike, SetLike.coe, SetLike.coe_subset_coe, coe_subset_coe, ofMapLEIff, of_orderEmbedding
-/
theorem disjoint_coe_iff (K L : Compacts α) : Disjoint (K : Set α) L ↔ Disjoint K L where
  mp h := .of_orderEmbedding (.ofMapLEIff SetLike.coe (fun _ _ => SetLike.coe_subset_coe)) h
  mpr h := by
    rw [Set.disjoint_iff]
    intro x ⟨hxK, hxL⟩
    specialize @h {x}
    simp_rw [← SetLike.coe_subset_coe, coe_singleton, singleton_subset_iff] at h
    exact h hxK hxL

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nontrivial (Compacts α)
  body: by
  constructor
  obtain ⟨x⟩ := ‹Nonempty α›
  exact ⟨⊥, {x}, ne_of_apply_ne SetLike.coe (Set.empty_ne_singleton x)⟩

@[simp]

中文:
实例 [非空
  签名: α] : 非平凡 (余mpacts α)
  定义体: by
  constructor
  obtain ⟨x⟩ := ‹Nonempty α›
  exact ⟨⊥, {x}, ne_of_apply_ne SetLike.coe (Set.empty_ne_singleton x)⟩

@[simp]

Depends on / 依赖: Nonempty, Set.empty_ne_singleton, SetLike, SetLike.coe, empty_ne_singleton, ne_of_apply_ne
-/
instance [Nonempty α] : Nontrivial (Compacts α) := by
  constructor
  obtain ⟨x⟩ := ‹Nonempty α›
  exact ⟨⊥, {x}, ne_of_apply_ne SetLike.coe (Set.empty_ne_singleton x)⟩

@[simp]
/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton (Compacts α) ↔ IsEmpty α
  proof: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  contrapose! h
  infer_instance

@[simp]

中文:
定理 subsingleton_iff
  结论: 子单例 (余mpacts α) ↔ 是空 α
  证明: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  contrapose! h
  infer_instance

@[simp]

Depends on / 依赖: contrapose, infer_instance
-/
theorem subsingleton_iff : Subsingleton (Compacts α) ↔ IsEmpty α := by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  contrapose! h
  infer_instance

@[simp]
/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  statement: Nontrivial (Compacts α) ↔ Nonempty α
  proof: by
  rw [← not_subsingleton_iff_nontrivial]; rw [subsingleton_iff]; rw [not_isEmpty_iff]

中文:
定理 nontrivial_iff
  结论: 非平凡 (余mpacts α) ↔ 非空 α
  证明: by
  rw [← not_subsingleton_iff_nontrivial]; rw [subsingleton_iff]; rw [not_isEmpty_iff]

Depends on / 依赖: not_isEmpty_iff, not_subsingleton_iff_nontrivial, subsingleton_iff
-/
theorem nontrivial_iff : Nontrivial (Compacts α) ↔ Nonempty α := by
  rw [← not_subsingleton_iff_nontrivial]; rw [subsingleton_iff]; rw [not_isEmpty_iff]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (hf : Continuous f) (K : Compacts α)
  body: ⟨f '' K.1, K.2.image hf⟩

@[simp, norm_cast]

中文:
定义 map
  签名: (f : α -> β) (hf : 连续 f) (K : 余mpacts α)
  定义体: ⟨f '' K.1, K.2.image hf⟩

@[simp, norm_cast]
-/
protected def map (f : α -> β) (hf : Continuous f) (K : Compacts α) : Compacts β :=
  ⟨f '' K.1, K.2.image hf⟩

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: {f : α -> β} (hf : Continuous f) (s : Compacts α)
  statement: (s.map f hf : Set β) = f '' s
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: {f : α -> β} (hf : 连续 f) (s : 余mpacts α)
  结论: (s.map f hf : 集合 β) = f '' s
  证明: rfl

@[simp]
-/
theorem coe_map {f : α -> β} (hf : Continuous f) (s : Compacts α) : (s.map f hf : Set β) = f '' s :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (K : Compacts α)
  statement: K.map id continuous_id = K
  proof: Compacts.ext Set.image_id _

中文:
定理 map_id
  条件: (K : 余mpacts α)
  结论: K.map id continuous_id = K
  证明: Compacts.ext Set.image_id _

Depends on / 依赖: Compacts, Compacts.ext, Set.image_id, image_id
-/
theorem map_id (K : Compacts α) : K.map id continuous_id = K :=
Compacts.ext Set.image_id _

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g) (K : Compacts α)
  proof: Compacts.ext Set.image_comp _ _ _

中文:
定理 map_comp
  条件: (f : β -> γ) (g : α -> β) (hf : 连续 f) (hg : 连续 g) (K : 余mpacts α)
  证明: Compacts.ext Set.image_comp _ _ _

Depends on / 依赖: Compacts, Compacts.ext, Set.image_comp, image_comp
-/
theorem map_comp (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g) (K : Compacts α) :
    K.map (f ∘ g) (hf.comp hg) = (K.map g hg).map f hf :=
Compacts.ext Set.image_comp _ _ _

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : α -> β} (hf : Continuous f) (hf' : Function.Injective f)
  proof: .of_comp (f := SetLike.coe) hf'.image_injective.comp SetLike.coe_injective

@[simp]

中文:
定理 map_injective
  条件: {f : α -> β} (hf : 连续 f) (hf' : 函数.单射 f)
  证明: .of_comp (f := SetLike.coe) hf'.image_injective.comp SetLike.coe_injective

@[simp]

Depends on / 依赖: SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_injective, image_injective.comp, of_comp
-/
theorem map_injective {f : α -> β} (hf : Continuous f) (hf' : Function.Injective f) :
    Function.Injective (Compacts.map f hf) :=
.of_comp (f := SetLike.coe) hf'.image_injective.comp SetLike.coe_injective

@[simp]
/--
theorem `map_singleton` / 定理 `map_singleton`

English:
theorem map_singleton
  given: {f : α -> β} (hf : Continuous f) (x : α)
  statement: Compacts.map f hf {x} = {f x}
  proof: Compacts.ext Set.image_singleton

@[simp]

中文:
定理 map_singleton
  条件: {f : α -> β} (hf : 连续 f) (x : α)
  结论: 余mpacts.map f hf {x} = {f x}
  证明: Compacts.ext Set.image_singleton

@[simp]

Depends on / 依赖: Compacts, Compacts.ext, Set.image_singleton, image_singleton
-/
theorem map_singleton {f : α -> β} (hf : Continuous f) (x : α) : Compacts.map f hf {x} = {f x} :=
  Compacts.ext Set.image_singleton

@[simp]
/--
theorem `map_injective_iff` / 定理 `map_injective_iff`

English:
theorem map_injective_iff
  given: {f : α -> β} (hf : Continuous f)
  proof: by
  refine ⟨fun h => .of_comp (f := ({·} : β -> Compacts β)) ?_, map_injective hf⟩
  simp_rw [Function.comp_def, ← map_singleton hf]
  exact h.comp singleton_injective

中文:
定理 map_injective_iff
  条件: {f : α -> β} (hf : 连续 f)
  证明: by
  refine ⟨fun h => .of_comp (f := ({·} : β -> Compacts β)) ?_, map_injective hf⟩
  simp_rw [Function.comp_def, ← map_singleton hf]
  exact h.comp singleton_injective

Depends on / 依赖: Compacts, Function, Function.comp_def, comp_def, h.comp, map_injective, map_singleton, of_comp, simp_rw, singleton_injective
-/
theorem map_injective_iff {f : α -> β} (hf : Continuous f) :
    Function.Injective (Compacts.map f hf) ↔ Function.Injective f := by
  refine ⟨fun h => .of_comp (f := ({·} : β -> Compacts β)) ?_, map_injective hf⟩
  simp_rw [Function.comp_def, ← map_singleton hf]
  exact h.comp singleton_injective

/--
theorem `range_map` / 定理 `range_map`

English:
theorem range_map
  given: {f : α -> β} (hf : Topology.IsInducing f)
  proof: subset_antisymm
    (range_subset_iff.mpr fun _ => image_subset_range _ _)
    (fun L hL => ⟨
      { carrier := f ⁻¹' L
        isCompact' := hf.isCompact_preimage' L.isCompact hL },
      Compacts.ext (image_preimage_eq_of_subset hL)⟩)

中文:
定理 range_map
  条件: {f : α -> β} (hf : 拓扑.是Inducing f)
  证明: subset_antisymm
    (range_subset_iff.mpr fun _ => image_subset_range _ _)
    (fun L hL => ⟨
      { carrier := f ⁻¹' L
        isCompact' := hf.isCompact_preimage' L.isCompact hL },
      Compacts.ext (image_preimage_eq_of_subset hL)⟩)

Depends on / 依赖: Compacts, Compacts.ext, L.isCompact, carrier, hf.isCompact_preimage, image_preimage_eq_of_subset, image_subset_range, isCompact, isCompact_preimage, range_subset_iff, range_subset_iff.mpr, subset_antisymm
-/
theorem range_map {f : α -> β} (hf : Topology.IsInducing f) :
    range (Compacts.map f hf.continuous) = {K : Compacts β | ↑K subseteq range f} :=
  subset_antisymm
    (range_subset_iff.mpr fun _ => image_subset_range _ _)
    (fun L hL => ⟨
      { carrier := f ⁻¹' L
        isCompact' := hf.isCompact_preimage' L.isCompact hL },
      Compacts.ext (image_preimage_eq_of_subset hL)⟩)

/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simps]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (f : α ≃ₜ β)
  body: Compacts.map f f.continuous
  invFun := Compacts.map _ f.symm.continuous
  left_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.symm_comp_self, image_id]
  right_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.self_comp_symm, image_id]

@[simp]

中文:
定义 equiv
  签名: (f : α ≃ₜ β)
  定义体: Compacts.map f f.continuous
  invFun := Compacts.map _ f.symm.continuous
  left_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.symm_comp_self, image_id]
  right_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.self_comp_symm, image_id]

@[simp]
-/
protected def equiv (f : α ≃ₜ β) : Compacts α ≃ Compacts β where
  toFun := Compacts.map f f.continuous
  invFun := Compacts.map _ f.symm.continuous
  left_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.symm_comp_self, image_id]
  right_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.self_comp_symm, image_id]

@[simp]
/--
theorem `equiv_refl` / 定理 `equiv_refl`

English:
theorem equiv_refl
  statement: Compacts.equiv (Homeomorph.refl α) = Equiv.refl _
  proof: Equiv.ext map_id

@[simp]

中文:
定理 equiv_refl
  结论: 余mpacts.equiv (同胚.refl α) = 等价.refl _
  证明: Equiv.ext map_id

@[simp]

Depends on / 依赖: Equiv.ext, map_id
-/
theorem equiv_refl : Compacts.equiv (Homeomorph.refl α) = Equiv.refl _ :=
  Equiv.ext map_id

@[simp]
/--
theorem `equiv_trans` / 定理 `equiv_trans`

English:
theorem equiv_trans
  given: (f : α ≃ₜ β) (g : β ≃ₜ γ)
  proof: Equiv.ext map_comp g f g.continuous f.continuous

@[simp]

中文:
定理 equiv_trans
  条件: (f : α ≃ₜ β) (g : β ≃ₜ γ)
  证明: Equiv.ext map_comp g f g.continuous f.continuous

@[simp]

Depends on / 依赖: Equiv.ext, continuous, f.continuous, g.continuous, map_comp
-/
theorem equiv_trans (f : α ≃ₜ β) (g : β ≃ₜ γ) :
    Compacts.equiv (f.trans g) = (Compacts.equiv f).trans (Compacts.equiv g) :=
Equiv.ext map_comp g f g.continuous f.continuous

@[simp]
/--
theorem `equiv_symm` / 定理 `equiv_symm`

English:
theorem equiv_symm
  given: (f : α ≃ₜ β)
  statement: Compacts.equiv f.symm = (Compacts.equiv f).symm
  proof: rfl

中文:
定理 equiv_symm
  条件: (f : α ≃ₜ β)
  结论: 余mpacts.equiv f.symm = (余mpacts.equiv f).symm
  证明: rfl
-/
theorem equiv_symm (f : α ≃ₜ β) : Compacts.equiv f.symm = (Compacts.equiv f).symm :=
  rfl

/--
theorem `coe_equiv_apply_eq_preimage` / 定理 `coe_equiv_apply_eq_preimage`

English:
theorem coe_equiv_apply_eq_preimage
  given: (f : α ≃ₜ β) (K : Compacts α)
  proof: f.toEquiv.image_eq_preimage_symm K

中文:
定理 coe_equiv_apply_eq_preimage
  条件: (f : α ≃ₜ β) (K : 余mpacts α)
  证明: f.toEquiv.image_eq_preimage_symm K

Depends on / 依赖: f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem coe_equiv_apply_eq_preimage (f : α ≃ₜ β) (K : Compacts α) :
    (Compacts.equiv f K : Set β) = f.symm ⁻¹' (K : Set α) :=
  f.toEquiv.image_eq_preimage_symm K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SProd (Compacts α) (Compacts β) (Compacts (α × β))
  body: { carrier := K ×ˢ L, isCompact' := IsCompact.prod K.2 L.2 }

@[simp]

中文:
实例 :
  签名: SProd (余mpacts α) (余mpacts β) (余mpacts (α × β))
  定义体: { carrier := K ×ˢ L, isCompact' := IsCompact.prod K.2 L.2 }

@[simp]

Depends on / 依赖: IsCompact, IsCompact.prod, carrier, isCompact
-/
instance : SProd (Compacts α) (Compacts β) (Compacts (α × β)) where
  sprod K L := { carrier := K ×ˢ L, isCompact' := IsCompact.prod K.2 L.2 }

@[simp]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (K : Compacts α) (L : Compacts β)
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (K : 余mpacts α) (L : 余mpacts β)
  证明: rfl

@[simp]
-/
theorem coe_prod (K : Compacts α) (L : Compacts β) :
    (K ×ˢ L : Compacts (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

@[simp]
/--
theorem `toCloseds_prod` / 定理 `toCloseds_prod`

English:
theorem toCloseds_prod
  given: [T2Space α] [T2Space β] (K : Compacts α) (L : Compacts β)
  proof: by
  rfl

@[simp]

中文:
定理 toCloseds_prod
  条件: [T2空间 α] [T2空间 β] (K : 余mpacts α) (L : 余mpacts β)
  证明: by
  rfl

@[simp]
-/
theorem toCloseds_prod [T2Space α] [T2Space β] (K : Compacts α) (L : Compacts β) :
    (K ×ˢ L).toCloseds = K.toCloseds ×ˢ L.toCloseds := by
  rfl

@[simp]
/--
theorem `singleton_prod_singleton` / 定理 `singleton_prod_singleton`

English:
theorem singleton_prod_singleton
  given: (x : α) (y : β)
  proof: Compacts.ext Set.singleton_prod_singleton

中文:
定理 singleton_prod_singleton
  条件: (x : α) (y : β)
  证明: Compacts.ext Set.singleton_prod_singleton

Depends on / 依赖: Compacts, Compacts.ext, Set.singleton_prod_singleton, singleton_prod_singleton
-/
theorem singleton_prod_singleton (x : α) (y : β) :
    ({x} ×ˢ {y} : Compacts (α × β)) = {(x, y)} :=
  Compacts.ext Set.singleton_prod_singleton

-- todo: add `pi`

open Topology

/--
Definition of `compactNhds` / `compactNhds` 的定义

English:
definition compactNhds
  signature: (K : Compacts α)
  body: {K' | forall (x : K), (K': Set α) in 𝓝 x.val}

中文:
定义 compactNhds
  签名: (K : 余mpacts α)
  定义体: {K' | forall (x : K), (K': Set α) in 𝓝 x.val}

Depends on / 依赖: x.val
-/
def compactNhds (K : Compacts α) : Set (Compacts α) :=
  {K' | forall (x : K), (K': Set α) in 𝓝 x.val}

/--
lemma `subset_of_mem_compactNhds` / 引理 `subset_of_mem_compactNhds`

English:
lemma subset_of_mem_compactNhds
  given: {K K' : Compacts α} (h : K' in K.compactNhds)
  proof: fun x hx => mem_of_mem_nhds (h ⟨x, hx⟩)

中文:
引理 subset_of_mem_compactNhds
  条件: {K K' : 余mpacts α} (h : K' in K.compactNhds)
  证明: fun x hx => mem_of_mem_nhds (h ⟨x, hx⟩)

Depends on / 依赖: mem_of_mem_nhds
-/
lemma subset_of_mem_compactNhds {K K' : Compacts α} (h : K' in K.compactNhds) :
    (K : Set α) subseteq K' :=
  fun x hx => mem_of_mem_nhds (h ⟨x, hx⟩)

/--
lemma `exists_open_set_nhds_of_compactsNhds` / 引理 `exists_open_set_nhds_of_compactsNhds`

English:
lemma exists_open_set_nhds_of_compactsNhds
  given: {K : Compacts α} (L : K.compactNhds)
  proof: by
  obtain ⟨U, KsubU, openU, UsubL⟩ := exists_open_set_nhds (fun x hx => L.2 ⟨x, hx⟩)
  exact ⟨⟨U, openU⟩, KsubU, UsubL⟩

中文:
引理 存在_open_set_nhds_of_compactsNhds
  条件: {K : 余mpacts α} (L : K.compactNhds)
  证明: by
  obtain ⟨U, KsubU, openU, UsubL⟩ := exists_open_set_nhds (fun x hx => L.2 ⟨x, hx⟩)
  exact ⟨⟨U, openU⟩, KsubU, UsubL⟩

Depends on / 依赖: exists_open_set_nhds
-/
lemma exists_open_set_nhds_of_compactsNhds {K : Compacts α} (L : K.compactNhds) :
    exists U : Opens α, (K : Set α) subseteq U ∧ (U : Set α) subseteq L := by
  obtain ⟨U, KsubU, openU, UsubL⟩ := exists_open_set_nhds (fun x hx => L.2 ⟨x, hx⟩)
  exact ⟨⟨U, openU⟩, KsubU, UsubL⟩

/--
lemma `exists_open_set_nhds_of_mem_compactsNhds` / 引理 `exists_open_set_nhds_of_mem_compactsNhds`

English:
lemma exists_open_set_nhds_of_mem_compactsNhds
  given: {K K' : Compacts α} (h : K' in K.compactNhds)
  proof: exists_open_set_nhds_of_compactsNhds ⟨K', h⟩

中文:
引理 存在_open_set_nhds_of_mem_compactsNhds
  条件: {K K' : 余mpacts α} (h : K' in K.compactNhds)
  证明: exists_open_set_nhds_of_compactsNhds ⟨K', h⟩

Depends on / 依赖: exists_open_set_nhds_of_compactsNhds
-/
lemma exists_open_set_nhds_of_mem_compactsNhds {K K' : Compacts α} (h : K' in K.compactNhds) :
    exists U : Opens α, (K : Set α) subseteq U ∧ (U : Set α) subseteq K' :=
  exists_open_set_nhds_of_compactsNhds ⟨K', h⟩

/--
Definition of `compactNhdsMkOfOpens` / `compactNhdsMkOfOpens` 的定义

English:
definition compactNhdsMkOfOpens
  signature: {K : Compacts α} (L : Compacts α) (U : Opens α)
  body: ⟨L, fun _ => Filter.mem_of_superset (IsOpen.mem_nhds U.is_open' (h1 (Subtype.coe_prop _))) h2⟩

中文:
定义 compactNhdsMkOfOpens
  签名: {K : 余mpacts α} (L : 余mpacts α) (U : Opens α)
  定义体: ⟨L, fun _ => Filter.mem_of_superset (IsOpen.mem_nhds U.is_open' (h1 (Subtype.coe_prop _))) h2⟩

Depends on / 依赖: Filter, Filter.mem_of_superset, IsOpen, IsOpen.mem_nhds, Subtype, Subtype.coe_prop, U.is_open, coe_prop, is_open, mem_nhds, mem_of_superset
-/
def compactNhdsMkOfOpens {K : Compacts α} (L : Compacts α) (U : Opens α)
    (h1 : (K : Set α) subseteq U) (h2 : (U : Set α) subseteq L) :
    K.compactNhds :=
  ⟨L, fun _ => Filter.mem_of_superset (IsOpen.mem_nhds U.is_open' (h1 (Subtype.coe_prop _))) h2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: α] (K
  body: ⟨L.1 ⊓ M.1, fun x => Filter.inter_mem_iff.2 ⟨L.2 x, M.2 x⟩⟩
  inf_le_right _ _ := Subtype.coe_le_coe.mp inf_le_right
  inf_le_left _ _:= Subtype.coe_le_coe.mp inf_le_left
  le_inf _ _ _ h k :=
    Subtype.coe_le_coe.mp (le_inf (Subtype.coe_le_coe.mpr h) (Subtype.coe_le_coe.mpr k))

中文:
实例 [T2空间
  签名: α] (K
  定义体: ⟨L.1 ⊓ M.1, fun x => Filter.inter_mem_iff.2 ⟨L.2 x, M.2 x⟩⟩
  inf_le_right _ _ := Subtype.coe_le_coe.mp inf_le_right
  inf_le_left _ _:= Subtype.coe_le_coe.mp inf_le_left
  le_inf _ _ _ h k :=
    Subtype.coe_le_coe.mp (le_inf (Subtype.coe_le_coe.mpr h) (Subtype.coe_le_coe.mpr k))

Depends on / 依赖: Filter, Filter.inter_mem_iff, inter_mem_iff
-/
instance [T2Space α] (K : Compacts α) : SemilatticeInf (K.compactNhds) where
  inf L M := ⟨L.1 ⊓ M.1, fun x => Filter.inter_mem_iff.2 ⟨L.2 x, M.2 x⟩⟩
  inf_le_right _ _ := Subtype.coe_le_coe.mp inf_le_right
  inf_le_left _ _:= Subtype.coe_le_coe.mp inf_le_left
  le_inf _ _ _ h k :=
    Subtype.coe_le_coe.mp (le_inf (Subtype.coe_le_coe.mpr h) (Subtype.coe_le_coe.mpr k))

/--
Definition of `openNhds` / `openNhds` 的定义

English:
definition openNhds
  signature: (K : Compacts α)
  body: {U | (K : Set α) subseteq U}

中文:
定义 openNhds
  签名: (K : 余mpacts α)
  定义体: {U | (K : Set α) subseteq U}

Depends on / 依赖: subseteq
-/
def openNhds (K : Compacts α) : Set (Opens α) := {U | (K : Set α) subseteq U}

instance (K : Compacts α) : IsCodirectedOrder K.openNhds where
  directed U1 U2 := ⟨⟨U1.val ⊓ U2.val, Set.subset_inter U1.property U2.property⟩,
  ⟨Subtype.mk_le_mk.2 inf_le_left, Subtype.mk_le_mk.2 inf_le_right⟩⟩

instance (K : Compacts α) : Top K.openNhds := ⟨⊤, Set.subset_univ _⟩
-- in particular `K.openNhds` is not empty and thus the induced category is cofiltered

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (⊥ : Compacts α).openNhds
  body: ⟨⊥, fun _ h => h⟩

中文:
实例 :
  签名: 底元素 (⊥ : 余mpacts α).openNhds
  定义体: ⟨⊥, fun _ h => h⟩
-/
instance : Bot (⊥ : Compacts α).openNhds := ⟨⊥, fun _ h => h⟩

/--
Definition of `openRcNhds` / `openRcNhds` 的定义

English:
definition openRcNhds
  signature: (K : Compacts α)
  body: {U | IsCompact (closure (U : Set α )) ∧ (K : Set α) subseteq U}

中文:
定义 openRcNhds
  签名: (K : 余mpacts α)
  定义体: {U | IsCompact (closure (U : Set α )) ∧ (K : Set α) subseteq U}

Depends on / 依赖: IsCompact, closure, subseteq
-/
def openRcNhds (K : Compacts α) : Set (Opens α) :=
  {U | IsCompact (closure (U : Set α )) ∧ (K : Set α) subseteq U}

/--
lemma `subset_of_mem_openRcNhds` / 引理 `subset_of_mem_openRcNhds`

English:
lemma subset_of_mem_openRcNhds
  given: {K : Compacts α} {U : Opens α} (h : U in K.openRcNhds)
  proof: fun _ hx => h.right hx

中文:
引理 subset_of_mem_openRcNhds
  条件: {K : 余mpacts α} {U : Opens α} (h : U in K.openRcNhds)
  证明: fun _ hx => h.right hx

Depends on / 依赖: h.right
-/
lemma subset_of_mem_openRcNhds {K : Compacts α} {U : Opens α} (h : U in K.openRcNhds) :
    (K : Set α) subseteq U :=
  fun _ hx => h.right hx

/--
lemma `isCompact_closure_of_mem_openRcNhds` / 引理 `isCompact_closure_of_mem_openRcNhds`

English:
lemma isCompact_closure_of_mem_openRcNhds
  given: {K : Compacts α} {U : Opens α} (h : U in K.openRcNhds)
  proof: h.left

中文:
引理 isCompact_closure_of_mem_openRcNhds
  条件: {K : 余mpacts α} {U : Opens α} (h : U in K.openRcNhds)
  证明: h.left

Depends on / 依赖: h.left
-/
lemma isCompact_closure_of_mem_openRcNhds {K : Compacts α} {U : Opens α} (h : U in K.openRcNhds) :
  IsCompact (closure (U : Set α)) := h.left

/--
lemma `closure_mem_compactNhds_of_mem_openRcNhds` / 引理 `closure_mem_compactNhds_of_mem_openRcNhds`

English:
lemma closure_mem_compactNhds_of_mem_openRcNhds
  statement: {K : Compacts α} {U : Opens α}
  proof: by
  intro x
  have H : (U : Set α) in 𝓝 (x : α) :=
U.isOpen.mem_nhds Compacts.subset_of_mem_openRcNhds h (by simp)
  exact Filter.mem_of_superset H subset_closure

中文:
引理 closure_mem_compactNhds_of_mem_openRcNhds
  结论: {K : 余mpacts α} {U : Opens α}
  证明: by
  intro x
  have H : (U : Set α) in 𝓝 (x : α) :=
U.isOpen.mem_nhds Compacts.subset_of_mem_openRcNhds h (by simp)
  exact Filter.mem_of_superset H subset_closure

Depends on / 依赖: Compacts, Compacts.subset_of_mem_openRcNhds, Filter, Filter.mem_of_superset, U.isOpen.mem_nhds, isOpen, mem_nhds, mem_of_superset, subset_closure, subset_of_mem_openRcNhds
-/
lemma closure_mem_compactNhds_of_mem_openRcNhds {K : Compacts α} {U : Opens α}
    (h : U in K.openRcNhds) :
    ⟨closure (U : Set α), isCompact_closure_of_mem_openRcNhds h⟩ in K.compactNhds := by
  intro x
  have H : (U : Set α) in 𝓝 (x : α) :=
U.isOpen.mem_nhds Compacts.subset_of_mem_openRcNhds h (by simp)
  exact Filter.mem_of_superset H subset_closure

/--
Definition of `openRcNhdsToOpenNhds` / `openRcNhdsToOpenNhds` 的定义

English:
definition openRcNhdsToOpenNhds
  signature: (K : Compacts α)
  body: fun U => ⟨_, U.property.2⟩

中文:
定义 openRcNhdsToOpenNhds
  签名: (K : 余mpacts α)
  定义体: fun U => ⟨_, U.property.2⟩

Depends on / 依赖: U.property, property
-/
def openRcNhdsToOpenNhds (K : Compacts α) : K.openRcNhds -> K.openNhds :=
  fun U => ⟨_, U.property.2⟩

/--
lemma `openRcNhdsToOpenNhds_mono` / 引理 `openRcNhdsToOpenNhds_mono`

English:
lemma openRcNhdsToOpenNhds_mono
  given: (K : Compacts α)
  proof: fun _ _ h => h

中文:
引理 openRcNhdsToOpenNhds_mono
  条件: (K : 余mpacts α)
  证明: fun _ _ h => h
-/
lemma openRcNhdsToOpenNhds_mono (K : Compacts α) :
    Monotone K.openRcNhdsToOpenNhds := fun _ _ h => h

/--
Definition of `openRcNhdsToCompactNhds` / `openRcNhdsToCompactNhds` 的定义

English:
definition openRcNhdsToCompactNhds
  signature: (K : Compacts α)
  body: fun U => ⟨_, closure_mem_compactNhds_of_mem_openRcNhds (Subtype.coe_prop U)⟩

中文:
定义 openRcNhdsToCompactNhds
  签名: (K : 余mpacts α)
  定义体: fun U => ⟨_, closure_mem_compactNhds_of_mem_openRcNhds (Subtype.coe_prop U)⟩

Depends on / 依赖: Subtype, Subtype.coe_prop, closure_mem_compactNhds_of_mem_openRcNhds, coe_prop
-/
def openRcNhdsToCompactNhds (K : Compacts α) : K.openRcNhds -> K.compactNhds :=
  fun U => ⟨_, closure_mem_compactNhds_of_mem_openRcNhds (Subtype.coe_prop U)⟩

/--
lemma `openRcNhdsToCompactNhds_mono` / 引理 `openRcNhdsToCompactNhds_mono`

English:
lemma openRcNhdsToCompactNhds_mono
  given: (K : Compacts α)
  statement: Monotone K.openRcNhdsToCompactNhds
  proof: fun _ _ h => closure_mono h

中文:
引理 openRcNhdsToCompactNhds_mono
  条件: (K : 余mpacts α)
  结论: 递增 K.openRcNhdsToCompactNhds
  证明: fun _ _ h => closure_mono h

Depends on / 依赖: closure_mono
-/
lemma openRcNhdsToCompactNhds_mono (K : Compacts α) : Monotone K.openRcNhdsToCompactNhds :=
  fun _ _ h => closure_mono h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: α] (K
  body: ⟨⟨U1 ⊓ U2, (isCompact_closure_of_mem_openRcNhds (Subtype.coe_prop U1) |>.inter
 isCompact_closure_of_mem_openRcNhds U2.coe_prop).of_isClosed_subset
isClosed_closure closure_inter_subset_inter_closure ..,
      le_inf (subset_of_mem_openRcNhds (Subtype.coe_prop U1))
 subset_of_mem_openRcNhds (Subtype

中文:
实例 [T2空间
  签名: α] (K
  定义体: ⟨⟨U1 ⊓ U2, (isCompact_closure_of_mem_openRcNhds (Subtype.coe_prop U1) |>.inter
 isCompact_closure_of_mem_openRcNhds U2.coe_prop).of_isClosed_subset
isClosed_closure closure_inter_subset_inter_closure ..,
      le_inf (subset_of_mem_openRcNhds (Subtype.coe_prop U1))
 subset_of_mem_openRcNhds (Subtype

Depends on / 依赖: Subtype, Subtype.coe_prop, coe_prop, isCompact_closure_of_mem_openRcNhds
-/
instance [T2Space α] (K : Compacts α) : IsCodirectedOrder K.openRcNhds where
  directed U1 U2 := ⟨⟨U1 ⊓ U2, (isCompact_closure_of_mem_openRcNhds (Subtype.coe_prop U1) |>.inter
 isCompact_closure_of_mem_openRcNhds U2.coe_prop).of_isClosed_subset
isClosed_closure closure_inter_subset_inter_closure ..,
      le_inf (subset_of_mem_openRcNhds (Subtype.coe_prop U1))
 subset_of_mem_openRcNhds (Subtype.coe_prop U2)⟩,
         Subtype.coe_le_coe.mp inf_le_left,
         Subtype.coe_le_coe.mp inf_le_right⟩

end Compacts

namespace Opens

/--
Definition of `compactsInside` / `compactsInside` 的定义

English:
definition compactsInside
  signature: (U : Opens α)
  body: {K | (K : Set α) subseteq U}

中文:
定义 compactsInside
  签名: (U : Opens α)
  定义体: {K | (K : Set α) subseteq U}

Depends on / 依赖: subseteq
-/
def compactsInside (U : Opens α) : Set (Compacts α) := {K | (K : Set α) subseteq U}

/--
Definition of `openNhdsOfCompactsInside` / `openNhdsOfCompactsInside` 的定义

English:
definition openNhdsOfCompactsInside
  signature: {U : Opens α} (K : U.compactsInside)
  body: ⟨U, K.property⟩

中文:
定义 openNhdsOfCompactsInside
  签名: {U : Opens α} (K : U.compactsInside)
  定义体: ⟨U, K.property⟩

Depends on / 依赖: K.property, property
-/
def openNhdsOfCompactsInside {U : Opens α} (K : U.compactsInside) : (K.val).openNhds :=
  ⟨U, K.property⟩

end Opens

/--
Definition of `Compacts.compactsInsideOfOpenNhds` / `Compacts.compactsInsideOfOpenNhds` 的定义

English:
definition Compacts.compactsInsideOfOpenNhds
  signature: {K : Compacts α} (U : K.openNhds)
  body: ⟨K, U.property⟩

中文:
定义 余mpacts.compactsInsideOfOpenNhds
  签名: {K : 余mpacts α} (U : K.openNhds)
  定义体: ⟨K, U.property⟩

Depends on / 依赖: U.property, property
-/
def Compacts.compactsInsideOfOpenNhds {K : Compacts α} (U : K.openNhds) : (U.val).compactsInside :=
  ⟨K, U.property⟩

/-! ### Nonempty compact sets -/

/--
Definition of `NonemptyCompacts` / `NonemptyCompacts` 的定义

English:
structure NonemptyCompacts
  parameters: (α : Type*) [TopologicalSpace α]
  extends: Compacts α
  axioms and operations (1):
    - nonempty' : carrier.Nonempty

中文:
结构 NonemptyCompacts
  参数: (α : 类型) [拓扑空间 α]
  继承: 余mpacts α
  公理与运算 (1 个):
    - nonempty' : carrier.非空
-/
structure NonemptyCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty

namespace NonemptyCompacts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (NonemptyCompacts α) α
  body: s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

中文:
实例 :
  签名: 集合状 (NonemptyCompacts α) α
  定义体: s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (NonemptyCompacts α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (NonemptyCompacts α)
  body: .ofSetLike (NonemptyCompacts α) α

中文:
实例 :
  签名: 偏序 (NonemptyCompacts α)
  定义体: .ofSetLike (NonemptyCompacts α) α

Depends on / 依赖: NonemptyCompacts, ofSetLike
-/
instance : PartialOrder (NonemptyCompacts α) := .ofSetLike (NonemptyCompacts α) α

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (s : NonemptyCompacts α)
  body: s

initialize_simps_projections NonemptyCompacts (carrier -> coe, as_prefix coe, as_prefix toCompacts)

中文:
定义 Simps.coe
  签名: (s : NonemptyCompacts α)
  定义体: s

initialize_simps_projections NonemptyCompacts (carrier -> coe, as_prefix coe, as_prefix toCompacts)
-/
def Simps.coe (s : NonemptyCompacts α) : Set α := s

initialize_simps_projections NonemptyCompacts (carrier -> coe, as_prefix coe, as_prefix toCompacts)

/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  given: (s : NonemptyCompacts α)
  statement: IsCompact (s : Set α)
  proof: s.isCompact'

中文:
定理 isCompact
  条件: (s : NonemptyCompacts α)
  结论: 是紧集 (s : 集合 α)
  证明: s.isCompact'
-/
protected theorem isCompact (s : NonemptyCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (s : NonemptyCompacts α)
  statement: (s : Set α).Nonempty
  proof: s.nonempty'

中文:
定理 nonempty
  条件: (s : NonemptyCompacts α)
  结论: (s : 集合 α).非空
  证明: s.nonempty'
-/
protected theorem nonempty (s : NonemptyCompacts α) : (s : Set α).Nonempty :=
  s.nonempty'

/-- Reinterpret a nonempty compact as a closed set. -/
@[simps]
/--
Definition of `toCloseds` / `toCloseds` 的定义

English:
definition toCloseds
  signature: [T2Space α] (s : NonemptyCompacts α)
  body: ⟨s, s.isCompact.isClosed⟩

@[simp]

中文:
定义 toCloseds
  签名: [T2空间 α] (s : NonemptyCompacts α)
  定义体: ⟨s, s.isCompact.isClosed⟩

@[simp]

Depends on / 依赖: isClosed, isCompact, s.isCompact.isClosed
-/
def toCloseds [T2Space α] (s : NonemptyCompacts α) : Closeds α :=
  ⟨s, s.isCompact.isClosed⟩

@[simp]
/--
theorem `toCloseds_toCompacts` / 定理 `toCloseds_toCompacts`

English:
theorem toCloseds_toCompacts
  given: [T2Space α] (s : NonemptyCompacts α)
  proof: rfl

@[simp]

中文:
定理 toCloseds_toCompacts
  条件: [T2空间 α] (s : NonemptyCompacts α)
  证明: rfl

@[simp]
-/
theorem toCloseds_toCompacts [T2Space α] (s : NonemptyCompacts α) :
    s.toCompacts.toCloseds = s.toCloseds :=
  rfl

@[simp]
/--
theorem `mem_toCloseds` / 定理 `mem_toCloseds`

English:
theorem mem_toCloseds
  given: [T2Space α] {x : α} {s : NonemptyCompacts α}
  proof: Iff.rfl

中文:
定理 mem_toCloseds
  条件: [T2空间 α] {x : α} {s : NonemptyCompacts α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toCloseds [T2Space α] {x : α} {s : NonemptyCompacts α} :
    x in s.toCloseds ↔ x in s :=
  Iff.rfl

/--
theorem `toCloseds_injective` / 定理 `toCloseds_injective`

English:
theorem toCloseds_injective
  given: [T2Space α]
  statement: Function.Injective (toCloseds (α := α))
  proof: .of_comp (f := SetLike.coe) SetLike.coe_injective

@[ext]

中文:
定理 toCloseds_injective
  条件: [T2空间 α]
  结论: 函数.单射 (toCloseds (α := α))
  证明: .of_comp (f := SetLike.coe) SetLike.coe_injective

@[ext]
-/
theorem toCloseds_injective [T2Space α] : Function.Injective (toCloseds (α := α)) :=
  .of_comp (f := SetLike.coe) SetLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : NonemptyCompacts α} (h : (s : Set α) = t)
  statement: s = t
  proof: SetLike.ext' h

@[simp]

中文:
定理 ext
  条件: {s t : NonemptyCompacts α} (h : (s : 集合 α) = t)
  结论: s = t
  证明: SetLike.ext' h

@[simp]
-/
protected theorem ext {s t : NonemptyCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Compacts α) (h)
  statement: (mk s h : Set α) = s
  proof: rfl

中文:
定理 coe_mk
  条件: (s : 余mpacts α) (h)
  结论: (mk s h : 集合 α) = s
  证明: rfl
-/
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl

/--
theorem `carrier_eq_coe` / 定理 `carrier_eq_coe`

English:
theorem carrier_eq_coe
  given: (s : NonemptyCompacts α)
  statement: s.carrier = s
  proof: rfl

@[simp]

中文:
定理 carrier_eq_coe
  条件: (s : NonemptyCompacts α)
  结论: s.carrier = s
  证明: rfl

@[simp]
-/
theorem carrier_eq_coe (s : NonemptyCompacts α) : s.carrier = s :=
  rfl

@[simp]
/--
theorem `coe_toCompacts` / 定理 `coe_toCompacts`

English:
theorem coe_toCompacts
  given: (s : NonemptyCompacts α)
  statement: (s.toCompacts : Set α) = s
  proof: rfl

@[simp]

中文:
定理 coe_toCompacts
  条件: (s : NonemptyCompacts α)
  结论: (s.toCompacts : 集合 α) = s
  证明: rfl

@[simp]
-/
theorem coe_toCompacts (s : NonemptyCompacts α) : (s.toCompacts : Set α) = s := rfl

@[simp]
/--
theorem `mem_toCompacts` / 定理 `mem_toCompacts`

English:
theorem mem_toCompacts
  given: {x : α} {s : NonemptyCompacts α}
  proof: Iff.rfl

中文:
定理 mem_toCompacts
  条件: {x : α} {s : NonemptyCompacts α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toCompacts {x : α} {s : NonemptyCompacts α} :
    x in s.toCompacts ↔ x in s :=
  Iff.rfl

/--
theorem `toCompacts_injective` / 定理 `toCompacts_injective`

English:
theorem toCompacts_injective
  statement: Function.Injective (toCompacts (α := α))
  proof: .of_comp (f := SetLike.coe) SetLike.coe_injective

@[simp]

中文:
定理 toCompacts_injective
  结论: 函数.单射 (toCompacts (α := α))
  证明: .of_comp (f := SetLike.coe) SetLike.coe_injective

@[simp]
-/
theorem toCompacts_injective : Function.Injective (toCompacts (α := α)) :=
  .of_comp (f := SetLike.coe) SetLike.coe_injective

@[simp]
/--
theorem `range_toCompacts` / 定理 `range_toCompacts`

English:
theorem range_toCompacts
  statement: range (toCompacts (α := α)) = {⊥}ᶜ
  proof: by
  ext K
  rw [mem_compl_singleton_iff]; rw [← Compacts.coe_nonempty]
  refine ⟨?_, fun h => ⟨⟨K, h⟩, rfl⟩⟩
  rintro ⟨K, rfl⟩
  exact K.nonempty

中文:
定理 range_toCompacts
  结论: range (toCompacts (α := α)) = {⊥}ᶜ
  证明: by
  ext K
  rw [mem_compl_singleton_iff]; rw [← Compacts.coe_nonempty]
  refine ⟨?_, fun h => ⟨⟨K, h⟩, rfl⟩⟩
  rintro ⟨K, rfl⟩
  exact K.nonempty

Depends on / 依赖: Compacts, Compacts.coe_nonempty, K.nonempty, coe_nonempty, mem_compl_singleton_iff, nonempty
-/
theorem range_toCompacts : range (toCompacts (α := α)) = {⊥}ᶜ := by
  ext K
  rw [mem_compl_singleton_iff]; rw [← Compacts.coe_nonempty]
  refine ⟨?_, fun h => ⟨⟨K, h⟩, rfl⟩⟩
  rintro ⟨K, rfl⟩
  exact K.nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (NonemptyCompacts α)
  body: ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.nonempty.mono subset_union_left⟩⟩

中文:
实例 :
  签名: 最大值 (NonemptyCompacts α)
  定义体: ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.nonempty.mono subset_union_left⟩⟩

Depends on / 依赖: nonempty, s.nonempty.mono, s.toCompacts, subset_union_left, t.toCompacts, toCompacts
-/
instance : Max (NonemptyCompacts α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.nonempty.mono subset_union_left⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] [Nonempty α] : Top (NonemptyCompacts α)
  body: ⟨⟨⊤, univ_nonempty⟩⟩

中文:
实例 [紧空间
  签名: α] [非空 α] : 顶元素 (NonemptyCompacts α)
  定义体: ⟨⟨⊤, univ_nonempty⟩⟩

Depends on / 依赖: univ_nonempty
-/
instance [CompactSpace α] [Nonempty α] : Top (NonemptyCompacts α) :=
  ⟨⟨⊤, univ_nonempty⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (NonemptyCompacts α)
  body: fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

中文:
实例 :
  签名: SemilatticeSup (NonemptyCompacts α)
  定义体: fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

Depends on / 依赖: SetLike, SetLike.coe_injective.semilatticeSup, coe_injective, fast_instance, semilatticeSup
-/
instance : SemilatticeSup (NonemptyCompacts α) :=
  fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] [Nonempty α] : OrderTop (NonemptyCompacts α)
  body: fast_instance% OrderTop.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl

@[simp]

中文:
实例 [紧空间
  签名: α] [非空 α] : 有顶序 (NonemptyCompacts α)
  定义体: fast_instance% OrderTop.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl

@[simp]

Depends on / 依赖: OrderTop, OrderTop.lift, fast_instance
-/
instance [CompactSpace α] [Nonempty α] : OrderTop (NonemptyCompacts α) :=
  fast_instance% OrderTop.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl

@[simp]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (s t : NonemptyCompacts α)
  statement: (↑(s ⊔ t) : Set α) = ↑s union ↑t
  proof: rfl

@[simp]

中文:
定理 coe_sup
  条件: (s t : NonemptyCompacts α)
  结论: (↑(s ⊔ t) : 集合 α) = ↑s union ↑t
  证明: rfl

@[simp]
-/
theorem coe_sup (s t : NonemptyCompacts α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t :=
  rfl

@[simp]
/--
theorem `toCompacts_sup` / 定理 `toCompacts_sup`

English:
theorem toCompacts_sup
  given: (s t : NonemptyCompacts α)
  proof: rfl

@[simp]

中文:
定理 toCompacts_sup
  条件: (s t : NonemptyCompacts α)
  证明: rfl

@[simp]
-/
theorem toCompacts_sup (s t : NonemptyCompacts α) :
    (s ⊔ t).toCompacts = s.toCompacts ⊔ t.toCompacts :=
  rfl

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  given: [CompactSpace α] [Nonempty α]
  statement: (↑(⊤ : NonemptyCompacts α) : Set α) = univ
  proof: rfl

@[simps! singleton_coe singleton_toCompacts]

中文:
定理 coe_top
  条件: [紧空间 α] [非空 α]
  结论: (↑(⊤ : NonemptyCompacts α) : 集合 α) = univ
  证明: rfl

@[simps! singleton_coe singleton_toCompacts]
-/
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : NonemptyCompacts α) : Set α) = univ :=
  rfl

@[simps! singleton_coe singleton_toCompacts]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Singleton α (NonemptyCompacts α)
  body: ⟨{x}, singleton_nonempty x⟩

@[simp]

中文:
实例 :
  签名: 单例 α (NonemptyCompacts α)
  定义体: ⟨{x}, singleton_nonempty x⟩

@[simp]

Depends on / 依赖: singleton_nonempty
-/
instance : Singleton α (NonemptyCompacts α) where
  singleton x := ⟨{x}, singleton_nonempty x⟩

@[simp]
/--
theorem `mem_singleton` / 定理 `mem_singleton`

English:
theorem mem_singleton
  given: (x y : α)
  statement: x in ({y} : NonemptyCompacts α) ↔ x = y
  proof: Iff.rfl

@[simp]

中文:
定理 mem_singleton
  条件: (x y : α)
  结论: x in ({y} : NonemptyCompacts α) ↔ x = y
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_singleton (x y : α) : x in ({y} : NonemptyCompacts α) ↔ x = y :=
  Iff.rfl

@[simp]
/--
theorem `toCloseds_singleton` / 定理 `toCloseds_singleton`

English:
theorem toCloseds_singleton
  given: [T2Space α] (x : α)
  statement: toCloseds {x} = {x}
  proof: rfl

中文:
定理 toCloseds_singleton
  条件: [T2空间 α] (x : α)
  结论: toCloseds {x} = {x}
  证明: rfl
-/
theorem toCloseds_singleton [T2Space α] (x : α) : toCloseds {x} = {x} :=
  rfl

/--
theorem `singleton_injective` / 定理 `singleton_injective`

English:
theorem singleton_injective
  statement: Function.Injective ({·} : α -> NonemptyCompacts α)
  proof: .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]

中文:
定理 singleton_injective
  结论: 函数.单射 ({·} : α -> NonemptyCompacts α)
  证明: .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]

Depends on / 依赖: Set.singleton_injective, SetLike, SetLike.coe, of_comp, singleton_injective
-/
theorem singleton_injective : Function.Injective ({·} : α -> NonemptyCompacts α) :=
  .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]
/--
theorem `singleton_inj` / 定理 `singleton_inj`

English:
theorem singleton_inj
  given: {x y : α}
  statement: ({x} : NonemptyCompacts α) = {y} ↔ x = y
  proof: singleton_injective.eq_iff

中文:
定理 singleton_inj
  条件: {x y : α}
  结论: ({x} : NonemptyCompacts α) = {y} ↔ x = y
  证明: singleton_injective.eq_iff

Depends on / 依赖: eq_iff, singleton_injective, singleton_injective.eq_iff
-/
theorem singleton_inj {x y : α} : ({x} : NonemptyCompacts α) = {y} ↔ x = y :=
  singleton_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (NonemptyCompacts α)
  body: ⟨{default}⟩

中文:
实例 [可居
  签名: α] : 可居 (NonemptyCompacts α)
  定义体: ⟨{default}⟩
-/
instance [Inhabited α] : Inhabited (NonemptyCompacts α) :=
  ⟨{default}⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : IsEmpty (NonemptyCompacts α)
  body: ⟨fun K => not_isEmpty_iff.mpr K.nonempty.to_type ‹_›⟩

@[simp]

中文:
实例 [是空
  签名: α] : 是空 (NonemptyCompacts α)
  定义体: ⟨fun K => not_isEmpty_iff.mpr K.nonempty.to_type ‹_›⟩

@[simp]

Depends on / 依赖: K.nonempty.to_type, nonempty, not_isEmpty_iff, not_isEmpty_iff.mpr, to_type
-/
instance [IsEmpty α] : IsEmpty (NonemptyCompacts α) :=
  ⟨fun K => not_isEmpty_iff.mpr K.nonempty.to_type ‹_›⟩

@[simp]
/--
theorem `isEmpty_iff` / 定理 `isEmpty_iff`

English:
theorem isEmpty_iff
  statement: IsEmpty (NonemptyCompacts α) ↔ IsEmpty α
  proof: ⟨fun _ => Function.isEmpty ({·} : α -> NonemptyCompacts α), fun _ => inferInstance⟩

中文:
定理 isEmpty_iff
  结论: 是空 (NonemptyCompacts α) ↔ 是空 α
  证明: ⟨fun _ => Function.isEmpty ({·} : α -> NonemptyCompacts α), fun _ => inferInstance⟩

Depends on / 依赖: Function, Function.isEmpty, NonemptyCompacts, isEmpty
-/
theorem isEmpty_iff : IsEmpty (NonemptyCompacts α) ↔ IsEmpty α :=
  ⟨fun _ => Function.isEmpty ({·} : α -> NonemptyCompacts α), fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (NonemptyCompacts α)
  body: .map ({·}) ‹_›

@[simp]

中文:
实例 [非空
  签名: α] : 非空 (NonemptyCompacts α)
  定义体: .map ({·}) ‹_›

@[simp]
-/
instance [Nonempty α] : Nonempty (NonemptyCompacts α) :=
  .map ({·}) ‹_›

@[simp]
/--
theorem `nonempty_iff` / 定理 `nonempty_iff`

English:
theorem nonempty_iff
  statement: Nonempty (NonemptyCompacts α) ↔ Nonempty α
  proof: by
  simp_rw [← not_isEmpty_iff, isEmpty_iff]

中文:
定理 nonempty_iff
  结论: 非空 (NonemptyCompacts α) ↔ 非空 α
  证明: by
  simp_rw [← not_isEmpty_iff, isEmpty_iff]

Depends on / 依赖: isEmpty_iff, not_isEmpty_iff, simp_rw
-/
theorem nonempty_iff : Nonempty (NonemptyCompacts α) ↔ Nonempty α := by
  simp_rw [← not_isEmpty_iff, isEmpty_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton (NonemptyCompacts α)
  body: by
  refine ⟨fun K L => NonemptyCompacts.ext ?_⟩
  rw [Subsingleton.eq_univ_of_nonempty K.nonempty]; rw [Subsingleton.eq_univ_of_nonempty L.nonempty]

@[simp]

中文:
实例 [子单例
  签名: α] : 子单例 (NonemptyCompacts α)
  定义体: by
  refine ⟨fun K L => NonemptyCompacts.ext ?_⟩
  rw [Subsingleton.eq_univ_of_nonempty K.nonempty]; rw [Subsingleton.eq_univ_of_nonempty L.nonempty]

@[simp]

Depends on / 依赖: K.nonempty, L.nonempty, NonemptyCompacts, NonemptyCompacts.ext, Subsingleton, Subsingleton.eq_univ_of_nonempty, eq_univ_of_nonempty, nonempty
-/
instance [Subsingleton α] : Subsingleton (NonemptyCompacts α) := by
  refine ⟨fun K L => NonemptyCompacts.ext ?_⟩
  rw [Subsingleton.eq_univ_of_nonempty K.nonempty]; rw [Subsingleton.eq_univ_of_nonempty L.nonempty]

@[simp]
/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton (NonemptyCompacts α) ↔ Subsingleton α
  proof: ⟨fun _ => singleton_injective.subsingleton, fun _ => inferInstance⟩

中文:
定理 subsingleton_iff
  结论: 子单例 (NonemptyCompacts α) ↔ 子单例 α
  证明: ⟨fun _ => singleton_injective.subsingleton, fun _ => inferInstance⟩

Depends on / 依赖: singleton_injective, singleton_injective.subsingleton, subsingleton
-/
theorem subsingleton_iff : Subsingleton (NonemptyCompacts α) ↔ Subsingleton α :=
  ⟨fun _ => singleton_injective.subsingleton, fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique (NonemptyCompacts α)
  body: .mk' _

中文:
实例 [唯一
  签名: α] : 唯一 (NonemptyCompacts α)
  定义体: .mk' _
-/
instance [Unique α] : Unique (NonemptyCompacts α) :=
  .mk' _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: α] : Nontrivial (NonemptyCompacts α)
  body: singleton_injective.nontrivial

@[simp]

中文:
实例 [非平凡
  签名: α] : 非平凡 (NonemptyCompacts α)
  定义体: singleton_injective.nontrivial

@[simp]

Depends on / 依赖: nontrivial, singleton_injective, singleton_injective.nontrivial
-/
instance [Nontrivial α] : Nontrivial (NonemptyCompacts α) :=
  singleton_injective.nontrivial

@[simp]
/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  statement: Nontrivial (NonemptyCompacts α) ↔ Nontrivial α
  proof: by
  simp_rw [← not_subsingleton_iff_nontrivial, subsingleton_iff]

中文:
定理 nontrivial_iff
  结论: 非平凡 (NonemptyCompacts α) ↔ 非平凡 α
  证明: by
  simp_rw [← not_subsingleton_iff_nontrivial, subsingleton_iff]

Depends on / 依赖: not_subsingleton_iff_nontrivial, simp_rw, subsingleton_iff
-/
theorem nontrivial_iff : Nontrivial (NonemptyCompacts α) ↔ Nontrivial α := by
  simp_rw [← not_subsingleton_iff_nontrivial, subsingleton_iff]

/-- The image of a nonempty compact set under a continuous function. -/
@[simps! toCompacts]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (hf : Continuous f) (K : NonemptyCompacts α)
  body: ⟨K.toCompacts.map f hf, K.nonempty.image f⟩

@[simp, norm_cast]

中文:
定义 map
  签名: (f : α -> β) (hf : 连续 f) (K : NonemptyCompacts α)
  定义体: ⟨K.toCompacts.map f hf, K.nonempty.image f⟩

@[simp, norm_cast]
-/
protected def map (f : α -> β) (hf : Continuous f) (K : NonemptyCompacts α) : NonemptyCompacts β :=
  ⟨K.toCompacts.map f hf, K.nonempty.image f⟩

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: {f : α -> β} (hf : Continuous f) (s : NonemptyCompacts α)
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: {f : α -> β} (hf : 连续 f) (s : NonemptyCompacts α)
  证明: rfl

@[simp]
-/
theorem coe_map {f : α -> β} (hf : Continuous f) (s : NonemptyCompacts α) :
    (s.map f hf : Set β) = f '' s :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (K : NonemptyCompacts α)
  statement: K.map id continuous_id = K
  proof: by
  ext
  simp

中文:
定理 map_id
  条件: (K : NonemptyCompacts α)
  结论: K.map id continuous_id = K
  证明: by
  ext
  simp
-/
theorem map_id (K : NonemptyCompacts α) : K.map id continuous_id = K := by
  ext
  simp

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g)
  proof: by
  ext
  simp

@[simp]

中文:
定理 map_comp
  结论: (f : β -> γ) (g : α -> β) (hf : 连续 f) (hg : 连续 g)
  证明: by
  ext
  simp

@[simp]
-/
theorem map_comp (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g)
    (K : NonemptyCompacts α) : K.map (f ∘ g) (hf.comp hg) = (K.map g hg).map f hf := by
  ext
  simp

@[simp]
/--
theorem `map_singleton` / 定理 `map_singleton`

English:
theorem map_singleton
  given: {f : α -> β} (hf : Continuous f) (x : α)
  proof: by
  ext
  simp

中文:
定理 map_singleton
  条件: {f : α -> β} (hf : 连续 f) (x : α)
  证明: by
  ext
  simp
-/
theorem map_singleton {f : α -> β} (hf : Continuous f) (x : α) :
    NonemptyCompacts.map f hf {x} = {f x} := by
  ext
  simp

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : α -> β} (hf : Continuous f) (hf' : Function.Injective f)
  proof: .of_comp (f := SetLike.coe) hf'.image_injective.comp SetLike.coe_injective

@[simp]

中文:
定理 map_injective
  条件: {f : α -> β} (hf : 连续 f) (hf' : 函数.单射 f)
  证明: .of_comp (f := SetLike.coe) hf'.image_injective.comp SetLike.coe_injective

@[simp]

Depends on / 依赖: SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_injective, image_injective.comp, of_comp
-/
theorem map_injective {f : α -> β} (hf : Continuous f) (hf' : Function.Injective f) :
    Function.Injective (NonemptyCompacts.map f hf) :=
.of_comp (f := SetLike.coe) hf'.image_injective.comp SetLike.coe_injective

@[simp]
/--
theorem `map_injective_iff` / 定理 `map_injective_iff`

English:
theorem map_injective_iff
  given: {f : α -> β} (hf : Continuous f)
  proof: ⟨fun h => .of_comp (f := ({·} : β -> NonemptyCompacts β)) fun _ _ _ =>
    singleton_injective (h (by simp_all)), map_injective hf⟩

中文:
定理 map_injective_iff
  条件: {f : α -> β} (hf : 连续 f)
  证明: ⟨fun h => .of_comp (f := ({·} : β -> NonemptyCompacts β)) fun _ _ _ =>
    singleton_injective (h (by simp_all)), map_injective hf⟩

Depends on / 依赖: NonemptyCompacts, map_injective, of_comp, singleton_injective
-/
theorem map_injective_iff {f : α -> β} (hf : Continuous f) :
    Function.Injective (NonemptyCompacts.map f hf) ↔ Function.Injective f :=
  ⟨fun h => .of_comp (f := ({·} : β -> NonemptyCompacts β)) fun _ _ _ =>
    singleton_injective (h (by simp_all)), map_injective hf⟩

/--
theorem `range_map` / 定理 `range_map`

English:
theorem range_map
  given: {f : α -> β} (hf : Topology.IsInducing f)
  proof: subset_antisymm
    (range_subset_iff.mpr fun _ => image_subset_range _ _)
    (fun L hL => ⟨
      { carrier := f ⁻¹' L
        isCompact' := hf.isCompact_preimage' L.isCompact hL
        nonempty' := L.nonempty.preimage' hL },
      NonemptyCompacts.ext (image_preimage_eq_of_subset hL)⟩)

中文:
定理 range_map
  条件: {f : α -> β} (hf : 拓扑.是Inducing f)
  证明: subset_antisymm
    (range_subset_iff.mpr fun _ => image_subset_range _ _)
    (fun L hL => ⟨
      { carrier := f ⁻¹' L
        isCompact' := hf.isCompact_preimage' L.isCompact hL
        nonempty' := L.nonempty.preimage' hL },
      NonemptyCompacts.ext (image_preimage_eq_of_subset hL)⟩)

Depends on / 依赖: L.isCompact, L.nonempty.preimage, NonemptyCompacts, NonemptyCompacts.ext, carrier, hf.isCompact_preimage, image_preimage_eq_of_subset, image_subset_range, isCompact, isCompact_preimage, nonempty, preimage, range_subset_iff, range_subset_iff.mpr, subset_antisymm
-/
theorem range_map {f : α -> β} (hf : Topology.IsInducing f) :
    range (NonemptyCompacts.map f hf.continuous) = {K : NonemptyCompacts β | ↑K subseteq range f} :=
  subset_antisymm
    (range_subset_iff.mpr fun _ => image_subset_range _ _)
    (fun L hL => ⟨
      { carrier := f ⁻¹' L
        isCompact' := hf.isCompact_preimage' L.isCompact hL
        nonempty' := L.nonempty.preimage' hL },
      NonemptyCompacts.ext (image_preimage_eq_of_subset hL)⟩)

/--
Instance `toCompactSpace` / 实例 `toCompactSpace`

English:
instance toCompactSpace
  signature: {s : NonemptyCompacts α}
  body: isCompact_iff_compactSpace.1 s.isCompact

中文:
实例 toCompactSpace
  签名: {s : NonemptyCompacts α}
  定义体: isCompact_iff_compactSpace.1 s.isCompact

Depends on / 依赖: isCompact, isCompact_iff_compactSpace, s.isCompact
-/
instance toCompactSpace {s : NonemptyCompacts α} : CompactSpace s :=
  isCompact_iff_compactSpace.1 s.isCompact

/--
Instance `toNonempty` / 实例 `toNonempty`

English:
instance toNonempty
  signature: {s : NonemptyCompacts α}
  body: s.nonempty.to_subtype

中文:
实例 toNonempty
  签名: {s : NonemptyCompacts α}
  定义体: s.nonempty.to_subtype

Depends on / 依赖: nonempty, s.nonempty.to_subtype, to_subtype
-/
instance toNonempty {s : NonemptyCompacts α} : Nonempty s :=
  s.nonempty.to_subtype

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SProd (NonemptyCompacts α) (NonemptyCompacts β) (NonemptyCompacts (α × β))
  body: { K.toCompacts ×ˢ L.toCompacts with nonempty' := K.nonempty.prod L.nonempty }

@[simp]

中文:
实例 :
  签名: SProd (NonemptyCompacts α) (NonemptyCompacts β) (NonemptyCompacts (α × β))
  定义体: { K.toCompacts ×ˢ L.toCompacts with nonempty' := K.nonempty.prod L.nonempty }

@[simp]

Depends on / 依赖: K.nonempty.prod, K.toCompacts, L.nonempty, L.toCompacts, nonempty, toCompacts
-/
instance : SProd (NonemptyCompacts α) (NonemptyCompacts β) (NonemptyCompacts (α × β)) where
  sprod K L := { K.toCompacts ×ˢ L.toCompacts with nonempty' := K.nonempty.prod L.nonempty }

@[simp]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (K : NonemptyCompacts α) (L : NonemptyCompacts β)
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (K : NonemptyCompacts α) (L : NonemptyCompacts β)
  证明: rfl

@[simp]
-/
theorem coe_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K ×ˢ L : NonemptyCompacts (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

@[simp]
/--
theorem `toCompacts_prod` / 定理 `toCompacts_prod`

English:
theorem toCompacts_prod
  given: (K : NonemptyCompacts α) (L : NonemptyCompacts β)
  proof: rfl

@[simp]

中文:
定理 toCompacts_prod
  条件: (K : NonemptyCompacts α) (L : NonemptyCompacts β)
  证明: rfl

@[simp]
-/
theorem toCompacts_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K ×ˢ L).toCompacts = K.toCompacts ×ˢ L.toCompacts :=
  rfl

@[simp]
/--
theorem `toCloseds_prod` / 定理 `toCloseds_prod`

English:
theorem toCloseds_prod
  given: [T2Space α] [T2Space β] (K : NonemptyCompacts α) (L : NonemptyCompacts β)
  proof: by
  rfl

@[simp]

中文:
定理 toCloseds_prod
  条件: [T2空间 α] [T2空间 β] (K : NonemptyCompacts α) (L : NonemptyCompacts β)
  证明: by
  rfl

@[simp]
-/
theorem toCloseds_prod [T2Space α] [T2Space β] (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K ×ˢ L).toCloseds = K.toCloseds ×ˢ L.toCloseds := by
  rfl

@[simp]
/--
theorem `singleton_prod_singleton` / 定理 `singleton_prod_singleton`

English:
theorem singleton_prod_singleton
  given: (x : α) (y : β)
  proof: NonemptyCompacts.ext Set.singleton_prod_singleton

中文:
定理 singleton_prod_singleton
  条件: (x : α) (y : β)
  证明: NonemptyCompacts.ext Set.singleton_prod_singleton

Depends on / 依赖: NonemptyCompacts, NonemptyCompacts.ext, Set.singleton_prod_singleton, singleton_prod_singleton
-/
theorem singleton_prod_singleton (x : α) (y : β) :
    ({x} ×ˢ {y} : NonemptyCompacts (α × β)) = {(x, y)} :=
  NonemptyCompacts.ext Set.singleton_prod_singleton

/--
Definition of `toCompactsOrderEmbedding` / `toCompactsOrderEmbedding` 的定义

English:
definition toCompactsOrderEmbedding
  signature: : NonemptyCompacts α ↪o Compacts α
  body: .ofMapLEIff toCompacts fun _ _ => .rfl

@[simp]

中文:
定义 toCompactsOrderEmbedding
  签名: : NonemptyCompacts α ↪o 余mpacts α
  定义体: .ofMapLEIff toCompacts fun _ _ => .rfl

@[simp]

Depends on / 依赖: ofMapLEIff, toCompacts
-/
def toCompactsOrderEmbedding : NonemptyCompacts α ↪o Compacts α :=
  .ofMapLEIff toCompacts fun _ _ => .rfl

@[simp]
/--
theorem `coe_toCompactsOrderEmbedding` / 定理 `coe_toCompactsOrderEmbedding`

English:
theorem coe_toCompactsOrderEmbedding
  statement: ⇑(toCompactsOrderEmbedding (α := α)) = toCompacts
  proof: rfl

中文:
定理 coe_toCompactsOrderEmbedding
  结论: ⇑(toCompactsOrderEmbedding (α := α)) = toCompacts
  证明: rfl

Depends on / 依赖: toCompacts
-/
theorem coe_toCompactsOrderEmbedding : ⇑(toCompactsOrderEmbedding (α := α)) = toCompacts :=
  rfl

end NonemptyCompacts

/-! ### Positive compact sets -/

/--
Definition of `PositiveCompacts` / `PositiveCompacts` 的定义

English:
structure PositiveCompacts
  parameters: (α : Type*) [TopologicalSpace α]
  extends: Compacts α
  axioms and operations (1):
    - interior_nonempty' : (interior carrier).Nonempty

中文:
结构 PositiveCompacts
  参数: (α : 类型) [拓扑空间 α]
  继承: 余mpacts α
  公理与运算 (1 个):
    - interior_nonempty' : (interior carrier).非空
-/
structure PositiveCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  interior_nonempty' : (interior carrier).Nonempty

namespace PositiveCompacts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (PositiveCompacts α) α
  body: s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

中文:
实例 :
  签名: 集合状 (PositiveCompacts α) α
  定义体: s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (PositiveCompacts α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (PositiveCompacts α)
  body: .ofSetLike (PositiveCompacts α) α

中文:
实例 :
  签名: 偏序 (PositiveCompacts α)
  定义体: .ofSetLike (PositiveCompacts α) α

Depends on / 依赖: PositiveCompacts, ofSetLike
-/
instance : PartialOrder (PositiveCompacts α) := .ofSetLike (PositiveCompacts α) α

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (s : PositiveCompacts α)
  body: s

initialize_simps_projections PositiveCompacts (carrier -> coe, as_prefix coe, as_prefix toCompacts)

中文:
定义 Simps.coe
  签名: (s : PositiveCompacts α)
  定义体: s

initialize_simps_projections PositiveCompacts (carrier -> coe, as_prefix coe, as_prefix toCompacts)
-/
def Simps.coe (s : PositiveCompacts α) : Set α := s

initialize_simps_projections PositiveCompacts (carrier -> coe, as_prefix coe, as_prefix toCompacts)

/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  given: (s : PositiveCompacts α)
  statement: IsCompact (s : Set α)
  proof: s.isCompact'

中文:
定理 isCompact
  条件: (s : PositiveCompacts α)
  结论: 是紧集 (s : 集合 α)
  证明: s.isCompact'
-/
protected theorem isCompact (s : PositiveCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'

/--
theorem `interior_nonempty` / 定理 `interior_nonempty`

English:
theorem interior_nonempty
  given: (s : PositiveCompacts α)
  statement: (interior (s : Set α)).Nonempty
  proof: s.interior_nonempty'

中文:
定理 interior_nonempty
  条件: (s : PositiveCompacts α)
  结论: (interior (s : 集合 α)).非空
  证明: s.interior_nonempty'

Depends on / 依赖: interior_nonempty, s.interior_nonempty
-/
theorem interior_nonempty (s : PositiveCompacts α) : (interior (s : Set α)).Nonempty :=
  s.interior_nonempty'

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (s : PositiveCompacts α)
  statement: (s : Set α).Nonempty
  proof: s.interior_nonempty.mono interior_subset

中文:
定理 nonempty
  条件: (s : PositiveCompacts α)
  结论: (s : 集合 α).非空
  证明: s.interior_nonempty.mono interior_subset
-/
protected theorem nonempty (s : PositiveCompacts α) : (s : Set α).Nonempty :=
  s.interior_nonempty.mono interior_subset

/--
Definition of `toNonemptyCompacts` / `toNonemptyCompacts` 的定义

English:
definition toNonemptyCompacts
  signature: (s : PositiveCompacts α)
  body: ⟨s.toCompacts, s.nonempty⟩

@[ext]

中文:
定义 toNonemptyCompacts
  签名: (s : PositiveCompacts α)
  定义体: ⟨s.toCompacts, s.nonempty⟩

@[ext]

Depends on / 依赖: nonempty, s.nonempty, s.toCompacts, toCompacts
-/
def toNonemptyCompacts (s : PositiveCompacts α) : NonemptyCompacts α :=
  ⟨s.toCompacts, s.nonempty⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : PositiveCompacts α} (h : (s : Set α) = t)
  statement: s = t
  proof: SetLike.ext' h

@[simp]

中文:
定理 ext
  条件: {s t : PositiveCompacts α} (h : (s : 集合 α) = t)
  结论: s = t
  证明: SetLike.ext' h

@[simp]
-/
protected theorem ext {s t : PositiveCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Compacts α) (h)
  statement: (mk s h : Set α) = s
  proof: rfl

中文:
定理 coe_mk
  条件: (s : 余mpacts α) (h)
  结论: (mk s h : 集合 α) = s
  证明: rfl
-/
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl

/--
theorem `carrier_eq_coe` / 定理 `carrier_eq_coe`

English:
theorem carrier_eq_coe
  given: (s : PositiveCompacts α)
  statement: s.carrier = s
  proof: rfl

@[simp]

中文:
定理 carrier_eq_coe
  条件: (s : PositiveCompacts α)
  结论: s.carrier = s
  证明: rfl

@[simp]
-/
theorem carrier_eq_coe (s : PositiveCompacts α) : s.carrier = s :=
  rfl

@[simp]
/--
theorem `coe_toCompacts` / 定理 `coe_toCompacts`

English:
theorem coe_toCompacts
  given: (s : PositiveCompacts α)
  statement: (s.toCompacts : Set α) = s
  proof: rfl

中文:
定理 coe_toCompacts
  条件: (s : PositiveCompacts α)
  结论: (s.toCompacts : 集合 α) = s
  证明: rfl
-/
theorem coe_toCompacts (s : PositiveCompacts α) : (s.toCompacts : Set α) = s :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (PositiveCompacts α)
  body: ⟨fun s t =>
    ⟨s.toCompacts ⊔ t.toCompacts,
s.interior_nonempty.mono interior_mono subset_union_left⟩⟩

中文:
实例 :
  签名: 最大值 (PositiveCompacts α)
  定义体: ⟨fun s t =>
    ⟨s.toCompacts ⊔ t.toCompacts,
s.interior_nonempty.mono interior_mono subset_union_left⟩⟩

Depends on / 依赖: interior_mono, interior_nonempty, s.interior_nonempty.mono, s.toCompacts, subset_union_left, t.toCompacts, toCompacts
-/
instance : Max (PositiveCompacts α) :=
  ⟨fun s t =>
    ⟨s.toCompacts ⊔ t.toCompacts,
s.interior_nonempty.mono interior_mono subset_union_left⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] [Nonempty α] : Top (PositiveCompacts α)
  body: ⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩

中文:
实例 [紧空间
  签名: α] [非空 α] : 顶元素 (PositiveCompacts α)
  定义体: ⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩

Depends on / 依赖: interior_univ, interior_univ.symm.subst, univ_nonempty
-/
instance [CompactSpace α] [Nonempty α] : Top (PositiveCompacts α) :=
  ⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (PositiveCompacts α)
  body: fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

中文:
实例 :
  签名: SemilatticeSup (PositiveCompacts α)
  定义体: fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

Depends on / 依赖: SetLike, SetLike.coe_injective.semilatticeSup, coe_injective, fast_instance, semilatticeSup
-/
instance : SemilatticeSup (PositiveCompacts α) :=
  fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] [Nonempty α] : OrderTop (PositiveCompacts α)
  body: fast_instance% OrderTop.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl

@[simp]

中文:
实例 [紧空间
  签名: α] [非空 α] : 有顶序 (PositiveCompacts α)
  定义体: fast_instance% OrderTop.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl

@[simp]

Depends on / 依赖: OrderTop, OrderTop.lift, fast_instance
-/
instance [CompactSpace α] [Nonempty α] : OrderTop (PositiveCompacts α) :=
  fast_instance% OrderTop.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl

@[simp]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (s t : PositiveCompacts α)
  statement: (↑(s ⊔ t) : Set α) = ↑s union ↑t
  proof: rfl

@[simp]

中文:
定理 coe_sup
  条件: (s t : PositiveCompacts α)
  结论: (↑(s ⊔ t) : 集合 α) = ↑s union ↑t
  证明: rfl

@[simp]
-/
theorem coe_sup (s t : PositiveCompacts α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t :=
  rfl

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  given: [CompactSpace α] [Nonempty α]
  statement: (↑(⊤ : PositiveCompacts α) : Set α) = univ
  proof: rfl

中文:
定理 coe_top
  条件: [紧空间 α] [非空 α]
  结论: (↑(⊤ : PositiveCompacts α) : 集合 α) = univ
  证明: rfl
-/
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : PositiveCompacts α) : Set α) = univ :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (hf : Continuous f) (hf' : IsOpenMap f) (K : PositiveCompacts α)
  body: { Compacts.map f hf K.toCompacts with
    interior_nonempty' :=
      (K.interior_nonempty'.image _).mono (hf'.image_interior_subset K.toCompacts) }

@[simp, norm_cast]

中文:
定义 map
  签名: (f : α -> β) (hf : 连续 f) (hf' : 是开映射 f) (K : PositiveCompacts α)
  定义体: { Compacts.map f hf K.toCompacts with
    interior_nonempty' :=
      (K.interior_nonempty'.image _).mono (hf'.image_interior_subset K.toCompacts) }

@[simp, norm_cast]
-/
protected def map (f : α -> β) (hf : Continuous f) (hf' : IsOpenMap f) (K : PositiveCompacts α) :
    PositiveCompacts β :=
  { Compacts.map f hf K.toCompacts with
    interior_nonempty' :=
      (K.interior_nonempty'.image _).mono (hf'.image_interior_subset K.toCompacts) }

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: {f : α -> β} (hf : Continuous f) (hf' : IsOpenMap f) (s : PositiveCompacts α)
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: {f : α -> β} (hf : 连续 f) (hf' : 是开映射 f) (s : PositiveCompacts α)
  证明: rfl

@[simp]
-/
theorem coe_map {f : α -> β} (hf : Continuous f) (hf' : IsOpenMap f) (s : PositiveCompacts α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (K : PositiveCompacts α)
  statement: K.map id continuous_id IsOpenMap.id = K
  proof: PositiveCompacts.ext Set.image_id _

中文:
定理 map_id
  条件: (K : PositiveCompacts α)
  结论: K.map id continuous_id 是开映射.id = K
  证明: PositiveCompacts.ext Set.image_id _

Depends on / 依赖: PositiveCompacts, PositiveCompacts.ext, Set.image_id, image_id
-/
theorem map_id (K : PositiveCompacts α) : K.map id continuous_id IsOpenMap.id = K :=
PositiveCompacts.ext Set.image_id _

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
  proof: PositiveCompacts.ext Set.image_comp _ _ _

中文:
定理 map_comp
  结论: (f : β -> γ) (g : α -> β) (hf : 连续 f) (hg : 连续 g) (hf' : 是开映射 f)
  证明: PositiveCompacts.ext Set.image_comp _ _ _

Depends on / 依赖: PositiveCompacts, PositiveCompacts.ext, Set.image_comp, image_comp
-/
theorem map_comp (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
    (hg' : IsOpenMap g) (K : PositiveCompacts α) :
    K.map (f ∘ g) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf' :=
PositiveCompacts.ext Set.image_comp _ _ _

/--
theorem `_root_.exists_positiveCompacts_subset` / 定理 `_root_.exists_positiveCompacts_subset`

English:
theorem _root_.exists_positiveCompacts_subset
  statement: [LocallyCompactSpace α] {U : Set α} (ho : IsOpen U)
  proof: let ⟨x, hx⟩ := hn
  let ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset ho hx
  ⟨⟨⟨K, hKc⟩, ⟨x, hxK⟩⟩, hKU⟩

中文:
定理 _root_.存在_positiveCompacts_subset
  结论: [局部紧空间 α] {U : 集合 α} (ho : 是开集 U)
  证明: let ⟨x, hx⟩ := hn
  let ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset ho hx
  ⟨⟨⟨K, hKc⟩, ⟨x, hxK⟩⟩, hKU⟩

Depends on / 依赖: exists_compact_subset
-/
theorem _root_.exists_positiveCompacts_subset [LocallyCompactSpace α] {U : Set α} (ho : IsOpen U)
    (hn : U.Nonempty) : exists K : PositiveCompacts α, ↑K subseteq U :=
  let ⟨x, hx⟩ := hn
  let ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset ho hx
  ⟨⟨⟨K, hKc⟩, ⟨x, hxK⟩⟩, hKU⟩

/--
theorem `_root_.IsOpen.exists_positiveCompacts_closure_subset` / 定理 `_root_.IsOpen.exists_positiveCompacts_closure_subset`

English:
theorem _root_.IsOpen.exists_positiveCompacts_closure_subset
  statement: [R1Space α] [LocallyCompactSpace α]
  proof: let ⟨K, hKU⟩ := exists_positiveCompacts_subset ho hn
  ⟨K, K.isCompact.closure_subset_of_isOpen ho hKU⟩

中文:
定理 _root_.是开集.存在_positiveCompacts_closure_subset
  结论: [R1空间 α] [局部紧空间 α]
  证明: let ⟨K, hKU⟩ := exists_positiveCompacts_subset ho hn
  ⟨K, K.isCompact.closure_subset_of_isOpen ho hKU⟩

Depends on / 依赖: K.isCompact.closure_subset_of_isOpen, closure_subset_of_isOpen, exists_positiveCompacts_subset, isCompact
-/
theorem _root_.IsOpen.exists_positiveCompacts_closure_subset [R1Space α] [LocallyCompactSpace α]
    {U : Set α} (ho : IsOpen U) (hn : U.Nonempty) : exists K : PositiveCompacts α, closure ↑K subseteq U :=
  let ⟨K, hKU⟩ := exists_positiveCompacts_subset ho hn
  ⟨K, K.isCompact.closure_subset_of_isOpen ho hKU⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] [Nonempty α] : Inhabited (PositiveCompacts α)
  body: ⟨⊤⟩

中文:
实例 [紧空间
  签名: α] [非空 α] : 可居 (PositiveCompacts α)
  定义体: ⟨⊤⟩
-/
instance [CompactSpace α] [Nonempty α] : Inhabited (PositiveCompacts α) :=
  ⟨⊤⟩

/--
Instance `nonempty'` / 实例 `nonempty'`

English:
instance nonempty'
  signature: [WeaklyLocallyCompactSpace α] [Nonempty α]
  body: by
  inhabit α
  rcases exists_compact_mem_nhds (default : α) with ⟨K, hKc, hK⟩
  exact ⟨⟨K, hKc⟩, _, mem_interior_iff_mem_nhds.2 hK⟩

中文:
实例 nonempty'
  签名: [WeaklyLocallyCompact空间 α] [非空 α]
  定义体: by
  inhabit α
  rcases exists_compact_mem_nhds (default : α) with ⟨K, hKc, hK⟩
  exact ⟨⟨K, hKc⟩, _, mem_interior_iff_mem_nhds.2 hK⟩

Depends on / 依赖: exists_compact_mem_nhds, inhabit, mem_interior_iff_mem_nhds
-/
instance nonempty' [WeaklyLocallyCompactSpace α] [Nonempty α] : Nonempty (PositiveCompacts α) := by
  inhabit α
  rcases exists_compact_mem_nhds (default : α) with ⟨K, hKc, hK⟩
  exact ⟨⟨K, hKc⟩, _, mem_interior_iff_mem_nhds.2 hK⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SProd (PositiveCompacts α) (PositiveCompacts β) (PositiveCompacts (α × β))
  body: { toCompacts := K.toCompacts ×ˢ L.toCompacts
      interior_nonempty' := by
        simp only [Compacts.carrier_eq_coe, Compacts.coe_prod, interior_prod_eq]
        exact K.interior_nonempty.prod L.interior_nonempty }

@[simp]

中文:
实例 :
  签名: SProd (PositiveCompacts α) (PositiveCompacts β) (PositiveCompacts (α × β))
  定义体: { toCompacts := K.toCompacts ×ˢ L.toCompacts
      interior_nonempty' := by
        simp only [Compacts.carrier_eq_coe, Compacts.coe_prod, interior_prod_eq]
        exact K.interior_nonempty.prod L.interior_nonempty }

@[simp]

Depends on / 依赖: Compacts, Compacts.carrier_eq_coe, Compacts.coe_prod, K.interior_nonempty.prod, K.toCompacts, L.interior_nonempty, L.toCompacts, carrier_eq_coe, coe_prod, interior_nonempty, interior_prod_eq, toCompacts
-/
instance : SProd (PositiveCompacts α) (PositiveCompacts β) (PositiveCompacts (α × β)) where
  sprod K L :=
    { toCompacts := K.toCompacts ×ˢ L.toCompacts
      interior_nonempty' := by
        simp only [Compacts.carrier_eq_coe, Compacts.coe_prod, interior_prod_eq]
        exact K.interior_nonempty.prod L.interior_nonempty }

@[simp]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (K : PositiveCompacts α) (L : PositiveCompacts β)
  proof: rfl

中文:
定理 coe_prod
  条件: (K : PositiveCompacts α) (L : PositiveCompacts β)
  证明: rfl
-/
theorem coe_prod (K : PositiveCompacts α) (L : PositiveCompacts β) :
    (K ×ˢ L : PositiveCompacts (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end PositiveCompacts

/-! ### Compact open sets -/

/--
Definition of `CompactOpens` / `CompactOpens` 的定义

English:
structure CompactOpens
  parameters: (α : Type*) [TopologicalSpace α]
  extends: Compacts α
  axioms and operations (1):
    - isOpen' : IsOpen carrier

中文:
结构 余mpactOpens
  参数: (α : 类型) [拓扑空间 α]
  继承: 余mpacts α
  公理与运算 (1 个):
    - isOpen' : 是开集 carrier
-/
structure CompactOpens (α : Type*) [TopologicalSpace α] extends Compacts α where
  isOpen' : IsOpen carrier

namespace CompactOpens

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (CompactOpens α) α
  body: s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

中文:
实例 :
  签名: 集合状 (余mpactOpens α) α
  定义体: s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (CompactOpens α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (CompactOpens α)
  body: .ofSetLike (CompactOpens α) α

中文:
实例 :
  签名: 偏序 (余mpactOpens α)
  定义体: .ofSetLike (CompactOpens α) α

Depends on / 依赖: CompactOpens, ofSetLike
-/
instance : PartialOrder (CompactOpens α) := .ofSetLike (CompactOpens α) α

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (s : CompactOpens α)
  body: s

initialize_simps_projections CompactOpens (carrier -> coe, as_prefix coe, as_prefix toCompacts)

中文:
定义 Simps.coe
  签名: (s : 余mpactOpens α)
  定义体: s

initialize_simps_projections CompactOpens (carrier -> coe, as_prefix coe, as_prefix toCompacts)
-/
def Simps.coe (s : CompactOpens α) : Set α := s

initialize_simps_projections CompactOpens (carrier -> coe, as_prefix coe, as_prefix toCompacts)

/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  given: (s : CompactOpens α)
  statement: IsCompact (s : Set α)
  proof: s.isCompact'

中文:
定理 isCompact
  条件: (s : 余mpactOpens α)
  结论: 是紧集 (s : 集合 α)
  证明: s.isCompact'
-/
protected theorem isCompact (s : CompactOpens α) : IsCompact (s : Set α) :=
  s.isCompact'

/--
theorem `isOpen` / 定理 `isOpen`

English:
theorem isOpen
  given: (s : CompactOpens α)
  statement: IsOpen (s : Set α)
  proof: s.isOpen'

中文:
定理 isOpen
  条件: (s : 余mpactOpens α)
  结论: 是开集 (s : 集合 α)
  证明: s.isOpen'
-/
protected theorem isOpen (s : CompactOpens α) : IsOpen (s : Set α) :=
  s.isOpen'

/-- Reinterpret a compact open as an open. -/
@[simps]
/--
Definition of `toOpens` / `toOpens` 的定义

English:
definition toOpens
  signature: (s : CompactOpens α)
  body: ⟨s, s.isOpen⟩

中文:
定义 toOpens
  签名: (s : 余mpactOpens α)
  定义体: ⟨s, s.isOpen⟩

Depends on / 依赖: isOpen, s.isOpen
-/
def toOpens (s : CompactOpens α) : Opens α := ⟨s, s.isOpen⟩

/-- Reinterpret a compact open as a clopen. -/
@[simps]
/--
Definition of `toClopens` / `toClopens` 的定义

English:
definition toClopens
  signature: [T2Space α] (s : CompactOpens α)
  body: ⟨s, s.isCompact.isClosed, s.isOpen⟩

@[ext]

中文:
定义 toClopens
  签名: [T2空间 α] (s : 余mpactOpens α)
  定义体: ⟨s, s.isCompact.isClosed, s.isOpen⟩

@[ext]

Depends on / 依赖: isClosed, isCompact, isOpen, s.isCompact.isClosed, s.isOpen
-/
def toClopens [T2Space α] (s : CompactOpens α) : Clopens α :=
  ⟨s, s.isCompact.isClosed, s.isOpen⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : CompactOpens α} (h : (s : Set α) = t)
  statement: s = t
  proof: SetLike.ext' h

@[simp]

中文:
定理 ext
  条件: {s t : 余mpactOpens α} (h : (s : 集合 α) = t)
  结论: s = t
  证明: SetLike.ext' h

@[simp]
-/
protected theorem ext {s t : CompactOpens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Compacts α) (h)
  statement: (mk s h : Set α) = s
  proof: rfl

中文:
定理 coe_mk
  条件: (s : 余mpacts α) (h)
  结论: (mk s h : 集合 α) = s
  证明: rfl
-/
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (CompactOpens α)
  body: ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.isOpen.union t.isOpen⟩⟩

中文:
实例 :
  签名: 最大值 (余mpactOpens α)
  定义体: ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.isOpen.union t.isOpen⟩⟩

Depends on / 依赖: isOpen, s.isOpen.union, s.toCompacts, t.isOpen, t.toCompacts, toCompacts
-/
instance : Max (CompactOpens α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.isOpen.union t.isOpen⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (CompactOpens α)
  body: ⟨⊥, isOpen_empty⟩

中文:
实例 :
  签名: 底元素 (余mpactOpens α)
  定义体: ⟨⊥, isOpen_empty⟩

Depends on / 依赖: isOpen_empty
-/
instance : Bot (CompactOpens α) where bot := ⟨⊥, isOpen_empty⟩

/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: (s t : CompactOpens α)
  statement: ↑(s ⊔ t) = (s union t : Set α)
  proof: rfl

中文:
引理 coe_sup
  条件: (s t : 余mpactOpens α)
  结论: ↑(s ⊔ t) = (s union t : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sup (s t : CompactOpens α) : ↑(s ⊔ t) = (s union t : Set α) := rfl
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: ↑(⊥ : CompactOpens α) = (∅ : Set α)
  proof: rfl

中文:
引理 coe_bot
  结论: ↑(⊥ : 余mpactOpens α) = (∅ : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_bot : ↑(⊥ : CompactOpens α) = (∅ : Set α) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (CompactOpens α)
  body: fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

中文:
实例 :
  签名: SemilatticeSup (余mpactOpens α)
  定义体: fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

Depends on / 依赖: SetLike, SetLike.coe_injective.semilatticeSup, coe_injective, coe_sup, fast_instance, semilatticeSup
-/
instance : SemilatticeSup (CompactOpens α) :=
  fast_instance% SetLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (CompactOpens α)
  body: fast_instance% OrderBot.lift ((↑) : _ -> Set α) (fun _ _ => id) coe_bot

@[simp]

中文:
实例 :
  签名: 有底序 (余mpactOpens α)
  定义体: fast_instance% OrderBot.lift ((↑) : _ -> Set α) (fun _ _ => id) coe_bot

@[simp]

Depends on / 依赖: OrderBot, OrderBot.lift, coe_bot, fast_instance
-/
instance : OrderBot (CompactOpens α) :=
  fast_instance% OrderBot.lift ((↑) : _ -> Set α) (fun _ _ => id) coe_bot

@[simp]
/--
lemma `coe_finsetSup` / 引理 `coe_finsetSup`

English:
lemma coe_finsetSup
  given: {ι : Type*} {f : ι -> CompactOpens α} {s : Finset ι}
  proof: by
  classical
  induction s using Finset.induction_on <;> simp [*]

中文:
引理 coe_finsetSup
  条件: {ι : 类型} {f : ι -> 余mpactOpens α} {s : 有限集 ι}
  证明: by
  classical
  induction s using Finset.induction_on <;> simp [*]

Depends on / 依赖: Finset, Finset.induction_on, classical, induction_on
-/
lemma coe_finsetSup {ι : Type*} {f : ι -> CompactOpens α} {s : Finset ι} :
    (↑(s.sup f) : Set α) = ⋃ i in s, f i := by
  classical
  induction s using Finset.induction_on <;> simp [*]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CompactOpens α)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (余mpactOpens α)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (CompactOpens α) :=
  ⟨⊥⟩

section Inf
variable [QuasiSeparatedSpace α]

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (CompactOpens α) where
  body: ⟨⟨U inter V, QuasiSeparatedSpace.inter_isCompact U.1.1 V.1.1 U.2 U.1.2 V.2 V.1.2⟩, U.2.inter V.2⟩

中文:
实例 instInf
  签名: : 最小值 (余mpactOpens α) where
  定义体: ⟨⟨U inter V, QuasiSeparatedSpace.inter_isCompact U.1.1 V.1.1 U.2 U.1.2 V.2 V.1.2⟩, U.2.inter V.2⟩

Depends on / 依赖: QuasiSeparatedSpace, QuasiSeparatedSpace.inter_isCompact, inter_isCompact
-/
instance instInf : Min (CompactOpens α) where
  min U V :=
    ⟨⟨U inter V, QuasiSeparatedSpace.inter_isCompact U.1.1 V.1.1 U.2 U.1.2 V.2 V.1.2⟩, U.2.inter V.2⟩

/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (s t : CompactOpens α)
  statement: ↑(s ⊓ t) = (s inter t : Set α)
  proof: rfl

中文:
引理 coe_inf
  条件: (s t : 余mpactOpens α)
  结论: ↑(s ⊓ t) = (s inter t : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf (s t : CompactOpens α) : ↑(s ⊓ t) = (s inter t : Set α) := rfl

/--
Instance `instSemilatticeInf` / 实例 `instSemilatticeInf`

English:
instance instSemilatticeInf
  signature: : SemilatticeInf (CompactOpens α)
  body: fast_instance% SetLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

中文:
实例 instSemilatticeInf
  签名: : SemilatticeInf (余mpactOpens α)
  定义体: fast_instance% SetLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

Depends on / 依赖: SetLike, SetLike.coe_injective.semilatticeInf, coe_inf, coe_injective, fast_instance, semilatticeInf
-/
instance instSemilatticeInf : SemilatticeInf (CompactOpens α) :=
  fast_instance% SetLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

end Inf

section SDiff
variable [T2Space α]

/--
Instance `instSDiff` / 实例 `instSDiff`

English:
instance instSDiff
  signature: : SDiff (CompactOpens α) where
  body: ⟨⟨s \ t, s.isCompact.diff t.isOpen⟩, s.isOpen.sdiff t.isCompact.isClosed⟩

中文:
实例 instSDiff
  签名: : 对称差 (余mpactOpens α) where
  定义体: ⟨⟨s \ t, s.isCompact.diff t.isOpen⟩, s.isOpen.sdiff t.isCompact.isClosed⟩

Depends on / 依赖: isClosed, isCompact, isOpen, s.isCompact.diff, s.isOpen.sdiff, t.isCompact.isClosed, t.isOpen
-/
instance instSDiff : SDiff (CompactOpens α) where
  sdiff s t := ⟨⟨s \ t, s.isCompact.diff t.isOpen⟩, s.isOpen.sdiff t.isCompact.isClosed⟩

/--
lemma `coe_sdiff` / 引理 `coe_sdiff`

English:
lemma coe_sdiff
  given: (s t : CompactOpens α)
  statement: ↑(s \ t) = (s \ t : Set α)
  proof: rfl

中文:
引理 coe_sdiff
  条件: (s t : 余mpactOpens α)
  结论: ↑(s \ t) = (s \ t : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sdiff (s t : CompactOpens α) : ↑(s \ t) = (s \ t : Set α) := rfl

/--
Instance `instGeneralizedBooleanAlgebra` / 实例 `instGeneralizedBooleanAlgebra`

English:
instance instGeneralizedBooleanAlgebra
  signature: : GeneralizedBooleanAlgebra (CompactOpens α)
  body: fast_instance% SetLike.coe_injective.generalizedBooleanAlgebra _
    .rfl .rfl coe_sup coe_inf coe_bot coe_sdiff

中文:
实例 instGeneralized布尔eanAlgebra
  签名: : Generalized布尔ean代数 (余mpactOpens α)
  定义体: fast_instance% SetLike.coe_injective.generalizedBooleanAlgebra _
    .rfl .rfl coe_sup coe_inf coe_bot coe_sdiff

Depends on / 依赖: SetLike, SetLike.coe_injective.generalizedBooleanAlgebra, coe_bot, coe_inf, coe_injective, coe_sdiff, coe_sup, fast_instance, generalizedBooleanAlgebra
-/
instance instGeneralizedBooleanAlgebra : GeneralizedBooleanAlgebra (CompactOpens α) :=
  fast_instance% SetLike.coe_injective.generalizedBooleanAlgebra _
    .rfl .rfl coe_sup coe_inf coe_bot coe_sdiff

end SDiff

section Top
variable [CompactSpace α]

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top (CompactOpens α) where top
  body: ⟨⊤, isOpen_univ⟩

中文:
实例 instTop
  签名: : 顶元素 (余mpactOpens α) where top
  定义体: ⟨⊤, isOpen_univ⟩

Depends on / 依赖: isOpen_univ
-/
instance instTop : Top (CompactOpens α) where top := ⟨⊤, isOpen_univ⟩

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: ↑(⊤ : CompactOpens α) = (univ : Set α)
  proof: rfl

中文:
引理 coe_top
  结论: ↑(⊤ : 余mpactOpens α) = (univ : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_top : ↑(⊤ : CompactOpens α) = (univ : Set α) := rfl

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: : BoundedOrder (CompactOpens α)
  body: fast_instance% BoundedOrder.lift ((↑) : _ -> Set α) (fun _ _ => id) coe_top coe_bot

中文:
实例 instBoundedOrder
  签名: : 有界序 (余mpactOpens α)
  定义体: fast_instance% BoundedOrder.lift ((↑) : _ -> Set α) (fun _ _ => id) coe_top coe_bot

Depends on / 依赖: BoundedOrder, BoundedOrder.lift, coe_bot, coe_top, fast_instance
-/
instance instBoundedOrder : BoundedOrder (CompactOpens α) :=
  fast_instance% BoundedOrder.lift ((↑) : _ -> Set α) (fun _ _ => id) coe_top coe_bot

section Compl
variable [T2Space α]

/--
Instance `instCompl` / 实例 `instCompl`

English:
instance instCompl
  signature: : Compl (CompactOpens α) where
  body: ⟨⟨sᶜ, s.isOpen.isClosed_compl.isCompact⟩, s.isCompact.isClosed.isOpen_compl⟩

中文:
实例 instCompl
  签名: : 补集 (余mpactOpens α) where
  定义体: ⟨⟨sᶜ, s.isOpen.isClosed_compl.isCompact⟩, s.isCompact.isClosed.isOpen_compl⟩

Depends on / 依赖: isClosed, isClosed_compl, isCompact, isOpen, isOpen_compl, s.isCompact.isClosed.isOpen_compl, s.isOpen.isClosed_compl.isCompact
-/
instance instCompl : Compl (CompactOpens α) where
  compl s := ⟨⟨sᶜ, s.isOpen.isClosed_compl.isCompact⟩, s.isCompact.isClosed.isOpen_compl⟩

/--
Instance `instHImp` / 实例 `instHImp`

English:
instance instHImp
  signature: : HImp (CompactOpens α) where
  body: ⟨⟨s ⇨ t, IsClosed.isCompact
    (by simpa [himp_eq] using t.isCompact.isClosed.union s.isOpen.isClosed_compl)⟩,
    by simpa [himp_eq] using t.isOpen.union s.isCompact.isClosed.isOpen_compl⟩

中文:
实例 instHImp
  签名: : HImp (余mpactOpens α) where
  定义体: ⟨⟨s ⇨ t, IsClosed.isCompact
    (by simpa [himp_eq] using t.isCompact.isClosed.union s.isOpen.isClosed_compl)⟩,
    by simpa [himp_eq] using t.isOpen.union s.isCompact.isClosed.isOpen_compl⟩

Depends on / 依赖: IsClosed, IsClosed.isCompact, isCompact
-/
instance instHImp : HImp (CompactOpens α) where
  himp s t := ⟨⟨s ⇨ t, IsClosed.isCompact
    (by simpa [himp_eq] using t.isCompact.isClosed.union s.isOpen.isClosed_compl)⟩,
    by simpa [himp_eq] using t.isOpen.union s.isCompact.isClosed.isOpen_compl⟩

/--
lemma `coe_compl` / 引理 `coe_compl`

English:
lemma coe_compl
  given: (s : CompactOpens α)
  statement: ↑sᶜ = (sᶜ : Set α)
  proof: rfl

中文:
引理 coe_compl
  条件: (s : 余mpactOpens α)
  结论: ↑sᶜ = (sᶜ : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_compl (s : CompactOpens α) : ↑sᶜ = (sᶜ : Set α) := rfl
/--
lemma `coe_himp` / 引理 `coe_himp`

English:
lemma coe_himp
  given: (s t : CompactOpens α)
  statement: ↑(s ⇨ t) = (s ⇨ t : Set α)
  proof: rfl

中文:
引理 coe_himp
  条件: (s t : 余mpactOpens α)
  结论: ↑(s ⇨ t) = (s ⇨ t : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_himp (s t : CompactOpens α) : ↑(s ⇨ t) = (s ⇨ t : Set α) := rfl

/--
Instance `instBooleanAlgebra` / 实例 `instBooleanAlgebra`

English:
instance instBooleanAlgebra
  signature: : BooleanAlgebra (CompactOpens α)
  body: fast_instance% SetLike.coe_injective.booleanAlgebra _
    .rfl .rfl coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff coe_himp

中文:
实例 inst布尔eanAlgebra
  签名: : 布尔代数 (余mpactOpens α)
  定义体: fast_instance% SetLike.coe_injective.booleanAlgebra _
    .rfl .rfl coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff coe_himp

Depends on / 依赖: SetLike, SetLike.coe_injective.booleanAlgebra, booleanAlgebra, coe_bot, coe_compl, coe_himp, coe_inf, coe_injective, coe_sdiff, coe_sup, coe_top, fast_instance
-/
instance instBooleanAlgebra : BooleanAlgebra (CompactOpens α) :=
  fast_instance% SetLike.coe_injective.booleanAlgebra _
    .rfl .rfl coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff coe_himp

end Top.Compl

/-- The image of a compact open under a continuous open map. -/
@[simps toCompacts]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α)
  body: ⟨s.toCompacts.map f hf, hf' _ s.isOpen⟩

@[simp, norm_cast]

中文:
定义 map
  签名: (f : α -> β) (hf : 连续 f) (hf' : 是开映射 f) (s : 余mpactOpens α)
  定义体: ⟨s.toCompacts.map f hf, hf' _ s.isOpen⟩

@[simp, norm_cast]

Depends on / 依赖: isOpen, s.isOpen, s.toCompacts.map, toCompacts
-/
def map (f : α -> β) (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) : CompactOpens β :=
  ⟨s.toCompacts.map f hf, hf' _ s.isOpen⟩

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: {f : α -> β} (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α)
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: {f : α -> β} (hf : 连续 f) (hf' : 是开映射 f) (s : 余mpactOpens α)
  证明: rfl

@[simp]
-/
theorem coe_map {f : α -> β} (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (K : CompactOpens α)
  statement: K.map id continuous_id IsOpenMap.id = K
  proof: CompactOpens.ext Set.image_id _

中文:
定理 map_id
  条件: (K : 余mpactOpens α)
  结论: K.map id continuous_id 是开映射.id = K
  证明: CompactOpens.ext Set.image_id _

Depends on / 依赖: CompactOpens, CompactOpens.ext, Set.image_id, image_id
-/
theorem map_id (K : CompactOpens α) : K.map id continuous_id IsOpenMap.id = K :=
CompactOpens.ext Set.image_id _

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
  proof: CompactOpens.ext Set.image_comp _ _ _

中文:
定理 map_comp
  结论: (f : β -> γ) (g : α -> β) (hf : 连续 f) (hg : 连续 g) (hf' : 是开映射 f)
  证明: CompactOpens.ext Set.image_comp _ _ _

Depends on / 依赖: CompactOpens, CompactOpens.ext, Set.image_comp, image_comp
-/
theorem map_comp (f : β -> γ) (g : α -> β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
    (hg' : IsOpenMap g) (K : CompactOpens α) :
    K.map (f ∘ g) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf' :=
CompactOpens.ext Set.image_comp _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SProd (CompactOpens α) (CompactOpens β) (CompactOpens (α × β))
  body: { K.toCompacts ×ˢ L.toCompacts with isOpen' := K.isOpen.prod L.isOpen }

@[simp]

中文:
实例 :
  签名: SProd (余mpactOpens α) (余mpactOpens β) (余mpactOpens (α × β))
  定义体: { K.toCompacts ×ˢ L.toCompacts with isOpen' := K.isOpen.prod L.isOpen }

@[simp]

Depends on / 依赖: K.isOpen.prod, K.toCompacts, L.isOpen, L.toCompacts, isOpen, toCompacts
-/
instance : SProd (CompactOpens α) (CompactOpens β) (CompactOpens (α × β)) where
  sprod K L := { K.toCompacts ×ˢ L.toCompacts with isOpen' := K.isOpen.prod L.isOpen }

@[simp]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (K : CompactOpens α) (L : CompactOpens β)
  proof: rfl

中文:
定理 coe_prod
  条件: (K : 余mpactOpens α) (L : 余mpactOpens β)
  证明: rfl
-/
theorem coe_prod (K : CompactOpens α) (L : CompactOpens β) :
    (K ×ˢ L : CompactOpens (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end CompactOpens

end TopologicalSpace
