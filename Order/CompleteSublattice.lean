/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Data.Set.Functor
public import Mathlib.Order.Sublattice
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Complete Sublattices

This file defines complete sublattices. These are subsets of complete lattices which are closed
under arbitrary suprema and infima. As a standard example one could take the complete sublattice of
invariant submodules of some module with respect to a linear map.

## Main definitions:
* `CompleteSublattice`: the definition of a complete sublattice
* `CompleteSublattice.mk'`: an alternate constructor for a complete sublattice, demanding fewer
  hypotheses
* `CompleteSublattice.instCompleteLattice`: a complete sublattice is a complete lattice
* `CompleteSublattice.map`: complete sublattices push forward under complete lattice morphisms.
* `CompleteSublattice.comap`: complete sublattices pull back under complete lattice morphisms.

-/

@[expose] public section

open Function Set

variable (α β : Type*) [CompleteLattice α] [CompleteLattice β] (f : CompleteLatticeHom α β)

/--
Definition of `CompleteSublattice` / `CompleteSublattice` 的定义

English:
structure CompleteSublattice
  parameters: extends Sublattice α
  extends: Sublattice α
  axioms and operations (2):
    - sSupClosed' : forall ⦃s : Set α⦄, s subseteq carrier -> sSup s in carrier
    - sInfClosed' : forall ⦃s : Set α⦄, s subseteq carrier -> sInf s in carrier

中文:
结构 CompleteSublattice
  参数: extends Sublattice α
  继承: Sublattice α
  公理与运算 (2 个):
    - sSupClosed' : 对任意 ⦃s : Set α⦄, s subseteq carrier -> sSup s in carrier
    - sInfClosed' : 对任意 ⦃s : Set α⦄, s subseteq carrier -> sInf s in carrier
-/
structure CompleteSublattice extends Sublattice α where
  sSupClosed' : forall ⦃s : Set α⦄, s subseteq carrier -> sSup s in carrier
  sInfClosed' : forall ⦃s : Set α⦄, s subseteq carrier -> sInf s in carrier

variable {α β}

namespace CompleteSublattice

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (carrier : Set α)
  body: carrier
  sSupClosed' := sSupClosed'
  sInfClosed' := sInfClosed'
  supClosed' := fun x hx y hy => by
    suffices x ⊔ y = sSup {x, y} by exact this ▸ sSupClosed' (fun z hz => by aesop)
    simp [sSup_singleton]
  infClosed' := fun x hx y hy => by
    suffices x ⊓ y = sInf {x, y} by exact this ▸ sIn

中文:
定义 mk'
  签名: (carrier : Set α)
  定义体: carrier
  sSupClosed' := sSupClosed'
  sInfClosed' := sInfClosed'
  supClosed' := fun x hx y hy => by
    suffices x ⊔ y = sSup {x, y} by exact this ▸ sSupClosed' (fun z hz => by aesop)
    simp [sSup_singleton]
  infClosed' := fun x hx y hy => by
    suffices x ⊓ y = sInf {x, y} by exact this ▸ sIn
-/
@[simps] def mk' (carrier : Set α)
    (sSupClosed' : forall ⦃s : Set α⦄, s subseteq carrier -> sSup s in carrier)
    (sInfClosed' : forall ⦃s : Set α⦄, s subseteq carrier -> sInf s in carrier) :
    CompleteSublattice α where
  carrier := carrier
  sSupClosed' := sSupClosed'
  sInfClosed' := sInfClosed'
  supClosed' := fun x hx y hy => by
    suffices x ⊔ y = sSup {x, y} by exact this ▸ sSupClosed' (fun z hz => by aesop)
    simp [sSup_singleton]
  infClosed' := fun x hx y hy => by
    suffices x ⊓ y = sInf {x, y} by exact this ▸ sInfClosed' (fun z hz => by aesop)
    simp [sInf_singleton]

variable {L : CompleteSublattice α}

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: : SetLike (CompleteSublattice α) α where
  body: L.carrier
  coe_injective L M h := by cases L; cases M; congr; exact SetLike.coe_injective h

中文:
实例 instSetLike
  签名: : SetLike (CompleteSublattice α) α where
  定义体: L.carrier
  coe_injective L M h := by cases L; cases M; congr; exact SetLike.coe_injective h

Depends on / 依赖: L.carrier, carrier
-/
instance instSetLike : SetLike (CompleteSublattice α) α where
  coe L := L.carrier
  coe_injective L M h := by cases L; cases M; congr; exact SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (CompleteSublattice α)
  body: .ofSetLike (CompleteSublattice α) α

中文:
实例 :
  签名: PartialOrder (CompleteSublattice α)
  定义体: .ofSetLike (CompleteSublattice α) α

Depends on / 依赖: CompleteSublattice, ofSetLike
-/
instance : PartialOrder (CompleteSublattice α) := .ofSetLike (CompleteSublattice α) α

/--
theorem `top_mem` / 定理 `top_mem`

English:
theorem top_mem
  statement: ⊤ in L
  proof: by simpa using! L.sInfClosed' empty_subset _

中文:
定理 top_mem
  结论: ⊤ in L
  证明: by simpa using! L.sInfClosed' empty_subset _

Depends on / 依赖: L.sInfClosed, empty_subset, sInfClosed
-/
theorem top_mem : ⊤ in L := by simpa using! L.sInfClosed' empty_subset _

/--
theorem `bot_mem` / 定理 `bot_mem`

English:
theorem bot_mem
  statement: ⊥ in L
  proof: by simpa using! L.sSupClosed' empty_subset _

中文:
定理 bot_mem
  结论: ⊥ in L
  证明: by simpa using! L.sSupClosed' empty_subset _

Depends on / 依赖: L.sSupClosed, empty_subset, sSupClosed
-/
theorem bot_mem : ⊥ in L := by simpa using! L.sSupClosed' empty_subset _

/--
Instance `instBot` / 实例 `instBot`

English:
instance instBot
  signature: : Bot L where
  body: ⟨⊥, bot_mem⟩

中文:
实例 instBot
  签名: : Bot L where
  定义体: ⟨⊥, bot_mem⟩

Depends on / 依赖: bot_mem
-/
instance instBot : Bot L where
  bot := ⟨⊥, bot_mem⟩

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top L where
  body: ⟨⊤, top_mem⟩

中文:
实例 instTop
  签名: : Top L where
  定义体: ⟨⊤, top_mem⟩

Depends on / 依赖: top_mem
-/
instance instTop : Top L where
  top := ⟨⊤, top_mem⟩

/--
Instance `instSupSet` / 实例 `instSupSet`

English:
instance instSupSet
  signature: : SupSet L where
  body: ⟨sSup (↑) '' s, L.sSupClosed' image_val_subset⟩

中文:
实例 instSupSet
  签名: : SupSet L where
  定义体: ⟨sSup (↑) '' s, L.sSupClosed' image_val_subset⟩

Depends on / 依赖: L.sSupClosed, image_val_subset, sSupClosed
-/
instance instSupSet : SupSet L where
sSup s := ⟨sSup (↑) '' s, L.sSupClosed' image_val_subset⟩

/--
Instance `instInfSet` / 实例 `instInfSet`

English:
instance instInfSet
  signature: : InfSet L where
  body: ⟨sInf (↑) '' s, L.sInfClosed' image_val_subset⟩

中文:
实例 instInfSet
  签名: : InfSet L where
  定义体: ⟨sInf (↑) '' s, L.sInfClosed' image_val_subset⟩

Depends on / 依赖: L.sInfClosed, image_val_subset, sInfClosed
-/
instance instInfSet : InfSet L where
sInf s := ⟨sInf (↑) '' s, L.sInfClosed' image_val_subset⟩

/--
theorem `sSupClosed` / 定理 `sSupClosed`

English:
theorem sSupClosed
  given: {s : Set α} (h : s subseteq L)
  statement: sSup s in L
  proof: L.sSupClosed' h

中文:
定理 sSupClosed
  条件: {s : Set α} (h : s subseteq L)
  结论: sSup s in L
  证明: L.sSupClosed' h

Depends on / 依赖: L.sSupClosed, sSupClosed
-/
theorem sSupClosed {s : Set α} (h : s subseteq L) : sSup s in L := L.sSupClosed' h

/--
theorem `sInfClosed` / 定理 `sInfClosed`

English:
theorem sInfClosed
  given: {s : Set α} (h : s subseteq L)
  statement: sInf s in L
  proof: L.sInfClosed' h

中文:
定理 sInfClosed
  条件: {s : Set α} (h : s subseteq L)
  结论: sInf s in L
  证明: L.sInfClosed' h

Depends on / 依赖: L.sInfClosed, sInfClosed
-/
theorem sInfClosed {s : Set α} (h : s subseteq L) : sInf s in L := L.sInfClosed' h

/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: (↑(⊥ : L) : α) = ⊥
  proof: rfl

中文:
定理 coe_bot
  结论: (↑(⊥ : L) : α) = ⊥
  证明: rfl
-/
@[simp] theorem coe_bot : (↑(⊥ : L) : α) = ⊥ := rfl

/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: (↑(⊤ : L) : α) = ⊤
  proof: rfl

中文:
定理 coe_top
  结论: (↑(⊤ : L) : α) = ⊤
  证明: rfl
-/
@[simp] theorem coe_top : (↑(⊤ : L) : α) = ⊤ := rfl

/--
theorem `coe_sSup` / 定理 `coe_sSup`

English:
theorem coe_sSup
  given: (S : Set L)
  statement: (↑(sSup S) : α) = sSup {(s : α) | s in S}
  proof: rfl

中文:
定理 coe_sSup
  条件: (S : Set L)
  结论: (↑(sSup S) : α) = sSup {(s : α) | s in S}
  证明: rfl
-/
@[simp] theorem coe_sSup (S : Set L) : (↑(sSup S) : α) = sSup {(s : α) | s in S} := rfl

/--
theorem `coe_sSup'` / 定理 `coe_sSup'`

English:
theorem coe_sSup'
  given: (S : Set L)
  statement: (↑(sSup S) : α) = ⨆ N in S, (N : α)
  proof: by
  rw [coe_sSup]; rw [← Set.image]; rw [sSup_image]

中文:
定理 coe_sSup'
  条件: (S : Set L)
  结论: (↑(sSup S) : α) = ⨆ N in S, (N : α)
  证明: by
  rw [coe_sSup]; rw [← Set.image]; rw [sSup_image]

Depends on / 依赖: Set.image, coe_sSup, sSup_image
-/
theorem coe_sSup' (S : Set L) : (↑(sSup S) : α) = ⨆ N in S, (N : α) := by
  rw [coe_sSup]; rw [← Set.image]; rw [sSup_image]

/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set L)
  statement: (↑(sInf S) : α) = sInf {(s : α) | s in S}
  proof: rfl

中文:
定理 coe_sInf
  条件: (S : Set L)
  结论: (↑(sInf S) : α) = sInf {(s : α) | s in S}
  证明: rfl
-/
@[simp] theorem coe_sInf (S : Set L) : (↑(sInf S) : α) = sInf {(s : α) | s in S} := rfl

/--
theorem `coe_sInf'` / 定理 `coe_sInf'`

English:
theorem coe_sInf'
  given: (S : Set L)
  statement: (↑(sInf S) : α) = ⨅ N in S, (N : α)
  proof: by
  rw [coe_sInf]; rw [← Set.image]; rw [sInf_image]

中文:
定理 coe_sInf'
  条件: (S : Set L)
  结论: (↑(sInf S) : α) = ⨅ N in S, (N : α)
  证明: by
  rw [coe_sInf]; rw [← Set.image]; rw [sInf_image]

Depends on / 依赖: Set.image, coe_sInf, sInf_image
-/
theorem coe_sInf' (S : Set L) : (↑(sInf S) : α) = ⨅ N in S, (N : α) := by
  rw [coe_sInf]; rw [← Set.image]; rw [sInf_image]

/--
theorem `coe_iSup` / 定理 `coe_iSup`

English:
theorem coe_iSup
  given: {ι} (f : ι -> L)
  statement: (↑(iSup f) : α) = ⨆ i, (f i : α)
  proof: by
  rw [iSup]; rw [coe_sSup']; rw [iSup_range]

中文:
定理 coe_iSup
  条件: {ι} (f : ι -> L)
  结论: (↑(iSup f) : α) = ⨆ i, (f i : α)
  证明: by
  rw [iSup]; rw [coe_sSup']; rw [iSup_range]
-/
@[simp] theorem coe_iSup {ι} (f : ι -> L) : (↑(iSup f) : α) = ⨆ i, (f i : α) := by
  rw [iSup]; rw [coe_sSup']; rw [iSup_range]

/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι} (f : ι -> L)
  statement: (↑(iInf f) : α) = ⨅ i, (f i : α)
  proof: by
  rw [iInf]; rw [coe_sInf']; rw [iInf_range]

中文:
定理 coe_iInf
  条件: {ι} (f : ι -> L)
  结论: (↑(iInf f) : α) = ⨅ i, (f i : α)
  证明: by
  rw [iInf]; rw [coe_sInf']; rw [iInf_range]
-/
@[simp] theorem coe_iInf {ι} (f : ι -> L) : (↑(iInf f) : α) = ⨅ i, (f i : α) := by
  rw [iInf]; rw [coe_sInf']; rw [iInf_range]

-- Redeclaring to get proper keys for these instances
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max {x // x in L}
  body: Sublattice.instSupCoe

中文:
实例 :
  签名: Max {x // x in L}
  定义体: Sublattice.instSupCoe

Depends on / 依赖: Sublattice, Sublattice.instSupCoe, instSupCoe
-/
instance : Max {x // x in L} := Sublattice.instSupCoe
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min {x // x in L}
  body: Sublattice.instInfCoe

中文:
实例 :
  签名: Min {x // x in L}
  定义体: Sublattice.instInfCoe

Depends on / 依赖: Sublattice, Sublattice.instInfCoe, instInfCoe
-/
instance : Min {x // x in L} := Sublattice.instInfCoe

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: : CompleteLattice L
  body: Subtype.coe_injective.completeLattice _ .rfl .rfl
    Sublattice.coe_sup Sublattice.coe_inf coe_sSup' coe_sInf' coe_top coe_bot

中文:
实例 instCompleteLattice
  签名: : CompleteLattice L
  定义体: Subtype.coe_injective.completeLattice _ .rfl .rfl
    Sublattice.coe_sup Sublattice.coe_inf coe_sSup' coe_sInf' coe_top coe_bot

Depends on / 依赖: Sublattice, Sublattice.coe_inf, Sublattice.coe_sup, Subtype, Subtype.coe_injective.completeLattice, coe_bot, coe_inf, coe_injective, coe_sInf, coe_sSup, coe_sup, coe_top, completeLattice
-/
instance instCompleteLattice : CompleteLattice L :=
  Subtype.coe_injective.completeLattice _ .rfl .rfl
    Sublattice.coe_sup Sublattice.coe_inf coe_sSup' coe_sInf' coe_top coe_bot

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (L : CompleteSublattice α)
  body: Subtype.val
  map_sInf' _ := rfl
  map_sSup' _ := rfl

中文:
定义 subtype
  签名: (L : CompleteSublattice α)
  定义体: Subtype.val
  map_sInf' _ := rfl
  map_sSup' _ := rfl

Depends on / 依赖: Subtype, Subtype.val
-/
def subtype (L : CompleteSublattice α) : CompleteLatticeHom L α where
  toFun := Subtype.val
  map_sInf' _ := rfl
  map_sSup' _ := rfl

/--
lemma `coe_subtype` / 引理 `coe_subtype`

English:
lemma coe_subtype
  given: (L : CompleteSublattice α)
  statement: L.subtype = ((↑) : L -> α)
  proof: rfl

中文:
引理 coe_subtype
  条件: (L : CompleteSublattice α)
  结论: L.subtype = ((↑) : L -> α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_subtype (L : CompleteSublattice α) : L.subtype = ((↑) : L -> α) := rfl
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: (L : Sublattice α) (a : L)
  statement: L.subtype a = a
  proof: rfl

中文:
引理 subtype_apply
  条件: (L : Sublattice α) (a : L)
  结论: L.subtype a = a
  证明: rfl
-/
lemma subtype_apply (L : Sublattice α) (a : L) : L.subtype a = a := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  given: (L : CompleteSublattice α)
  proof: Subtype.coe_injective

中文:
引理 subtype_injective
  条件: (L : CompleteSublattice α)
  证明: Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective (L : CompleteSublattice α) :
Injective subtype L := Subtype.coe_injective

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (L : CompleteSublattice α)
  body: f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f
  sSupClosed' := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := subset_image_iff.mp hs
    rw [← map_sSup]
    exact mem_image_of_mem f (sSupClosed ht)
  sInfClosed' := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := subset_image_if

中文:
定义 map
  签名: (L : CompleteSublattice α)
  定义体: f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f
  sSupClosed' := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := subset_image_iff.mp hs
    rw [← map_sSup]
    exact mem_image_of_mem f (sSupClosed ht)
  sInfClosed' := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := subset_image_if
-/
@[simps] def map (L : CompleteSublattice α) : CompleteSublattice β where
  carrier := f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f
  sSupClosed' := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := subset_image_iff.mp hs
    rw [← map_sSup]
    exact mem_image_of_mem f (sSupClosed ht)
  sInfClosed' := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := subset_image_iff.mp hs
    rw [← map_sInf]
    exact mem_image_of_mem f (sInfClosed ht)

/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {b : β}
  statement: b in L.map f ↔ exists a in L, f a = b
  proof: Iff.rfl

中文:
定理 mem_map
  条件: {b : β}
  结论: b in L.map f ↔ 存在 a in L, f a = b
  证明: Iff.rfl
-/
@[simp] theorem mem_map {b : β} : b in L.map f ↔ exists a in L, f a = b := Iff.rfl

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (L : CompleteSublattice β)
  body: f ⁻¹' L
  supClosed' := L.supClosed.preimage f
  infClosed' := L.infClosed.preimage f
  sSupClosed' s hs := by
    simpa only [mem_preimage, map_sSup, SetLike.mem_coe] using sSupClosed
 mapsTo_iff_image_subset.mp hs
  sInfClosed' s hs := by
    simpa only [mem_preimage, map_sInf, SetLike.mem_coe] us

中文:
定义 comap
  签名: (L : CompleteSublattice β)
  定义体: f ⁻¹' L
  supClosed' := L.supClosed.preimage f
  infClosed' := L.infClosed.preimage f
  sSupClosed' s hs := by
    simpa only [mem_preimage, map_sSup, SetLike.mem_coe] using sSupClosed
 mapsTo_iff_image_subset.mp hs
  sInfClosed' s hs := by
    simpa only [mem_preimage, map_sInf, SetLike.mem_coe] us
-/
@[simps] def comap (L : CompleteSublattice β) : CompleteSublattice α where
  carrier := f ⁻¹' L
  supClosed' := L.supClosed.preimage f
  infClosed' := L.infClosed.preimage f
  sSupClosed' s hs := by
    simpa only [mem_preimage, map_sSup, SetLike.mem_coe] using sSupClosed
 mapsTo_iff_image_subset.mp hs
  sInfClosed' s hs := by
    simpa only [mem_preimage, map_sInf, SetLike.mem_coe] using sInfClosed
 mapsTo_iff_image_subset.mp hs

/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {L : CompleteSublattice β} {a : α}
  statement: a in L.comap f ↔ f a in L
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {L : CompleteSublattice β} {a : α}
  结论: a in L.comap f ↔ f a in L
  证明: Iff.rfl
-/
@[simp] theorem mem_comap {L : CompleteSublattice β} {a : α} : a in L.comap f ↔ f a in L := Iff.rfl

/--
lemma `disjoint_iff` / 引理 `disjoint_iff`

English:
lemma disjoint_iff
  given: {a b : L}
  proof: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← Sublattice.coe_inf]; rw [← coe_bot (L := L)]; rw [Subtype.coe_injective.eq_iff]

中文:
引理 disjoint_iff
  条件: {a b : L}
  证明: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← Sublattice.coe_inf]; rw [← coe_bot (L := L)]; rw [Subtype.coe_injective.eq_iff]
-/
protected lemma disjoint_iff {a b : L} :
    Disjoint a b ↔ Disjoint (a : α) (b : α) := by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← Sublattice.coe_inf]; rw [← coe_bot (L := L)]; rw [Subtype.coe_injective.eq_iff]

/--
lemma `codisjoint_iff` / 引理 `codisjoint_iff`

English:
lemma codisjoint_iff
  given: {a b : L}
  proof: by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [← Sublattice.coe_sup]; rw [← coe_top (L := L)]; rw [Subtype.coe_injective.eq_iff]

中文:
引理 codisjoint_iff
  条件: {a b : L}
  证明: by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [← Sublattice.coe_sup]; rw [← coe_top (L := L)]; rw [Subtype.coe_injective.eq_iff]
-/
protected lemma codisjoint_iff {a b : L} :
    Codisjoint a b ↔ Codisjoint (a : α) (b : α) := by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [← Sublattice.coe_sup]; rw [← coe_top (L := L)]; rw [Subtype.coe_injective.eq_iff]

/--
lemma `isCompl_iff` / 引理 `isCompl_iff`

English:
lemma isCompl_iff
  given: {a b : L}
  proof: by
  rw [isCompl_iff]; rw [isCompl_iff]; rw [CompleteSublattice.disjoint_iff]; rw [CompleteSublattice.codisjoint_iff]

中文:
引理 isCompl_iff
  条件: {a b : L}
  证明: by
  rw [isCompl_iff]; rw [isCompl_iff]; rw [CompleteSublattice.disjoint_iff]; rw [CompleteSublattice.codisjoint_iff]
-/
protected lemma isCompl_iff {a b : L} :
    IsCompl a b ↔ IsCompl (a : α) (b : α) := by
  rw [isCompl_iff]; rw [isCompl_iff]; rw [CompleteSublattice.disjoint_iff]; rw [CompleteSublattice.codisjoint_iff]

/--
lemma `isComplemented_iff` / 引理 `isComplemented_iff`

English:
lemma isComplemented_iff
  statement: ComplementedLattice L ↔ forall a in L, exists b in L, IsCompl a b
  proof: by
  refine ⟨fun ⟨h⟩ a ha => ?_, fun h => ⟨fun ⟨a, ha⟩ => ?_⟩⟩
  · obtain ⟨b, hb⟩ := h ⟨a, ha⟩
    exact ⟨b, b.property, CompleteSublattice.isCompl_iff.mp hb⟩
  · obtain ⟨b, hb, hb'⟩ := h a ha
    exact ⟨⟨b, hb⟩, CompleteSublattice.isCompl_iff.mpr hb'⟩

中文:
引理 isComplemented_iff
  结论: ComplementedLattice L ↔ 对任意 a in L, 存在 b in L, IsCompl a b
  证明: by
  refine ⟨fun ⟨h⟩ a ha => ?_, fun h => ⟨fun ⟨a, ha⟩ => ?_⟩⟩
  · obtain ⟨b, hb⟩ := h ⟨a, ha⟩
    exact ⟨b, b.property, CompleteSublattice.isCompl_iff.mp hb⟩
  · obtain ⟨b, hb, hb'⟩ := h a ha
    exact ⟨⟨b, hb⟩, CompleteSublattice.isCompl_iff.mpr hb'⟩

Depends on / 依赖: CompleteSublattice, CompleteSublattice.isCompl_iff.mp, CompleteSublattice.isCompl_iff.mpr, b.property, isCompl_iff, property
-/
lemma isComplemented_iff : ComplementedLattice L ↔ forall a in L, exists b in L, IsCompl a b := by
  refine ⟨fun ⟨h⟩ a ha => ?_, fun h => ⟨fun ⟨a, ha⟩ => ?_⟩⟩
  · obtain ⟨b, hb⟩ := h ⟨a, ha⟩
    exact ⟨b, b.property, CompleteSublattice.isCompl_iff.mp hb⟩
  · obtain ⟨b, hb, hb'⟩ := h a ha
    exact ⟨⟨b, hb⟩, CompleteSublattice.isCompl_iff.mpr hb'⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (CompleteSublattice α)
  body: ⟨mk' univ (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)⟩

中文:
实例 :
  签名: Top (CompleteSublattice α)
  定义体: ⟨mk' univ (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)⟩

Depends on / 依赖: mem_univ
-/
instance : Top (CompleteSublattice α) := ⟨mk' univ (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)⟩

variable (L)

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (s : Set α) (hs : s = L)
  body: mk' s (hs ▸ L.sSupClosed') (hs ▸ L.sInfClosed')

中文:
定义 copy
  签名: (s : Set α) (hs : s = L)
  定义体: mk' s (hs ▸ L.sSupClosed') (hs ▸ L.sInfClosed')
-/
protected def copy (s : Set α) (hs : s = L) : CompleteSublattice α :=
  mk' s (hs ▸ L.sSupClosed') (hs ▸ L.sInfClosed')

/--
lemma `coe_copy` / 引理 `coe_copy`

English:
lemma coe_copy
  given: (s : Set α) (hs)
  statement: L.copy s hs = s
  proof: rfl

中文:
引理 coe_copy
  条件: (s : Set α) (hs)
  结论: L.copy s hs = s
  证明: rfl
-/
@[simp, norm_cast] lemma coe_copy (s : Set α) (hs) : L.copy s hs = s := rfl

/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  given: (s : Set α) (hs)
  statement: L.copy s hs = L
  proof: SetLike.coe_injective hs

中文:
引理 copy_eq
  条件: (s : Set α) (hs)
  结论: L.copy s hs = L
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
lemma copy_eq (s : Set α) (hs) : L.copy s hs = L := SetLike.coe_injective hs

end CompleteSublattice

namespace CompleteLatticeHom

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: : CompleteSublattice β
  body: (CompleteSublattice.map f ⊤).copy (range f) image_univ.symm

中文:
定义 range
  签名: : CompleteSublattice β
  定义体: (CompleteSublattice.map f ⊤).copy (range f) image_univ.symm
-/
protected def range : CompleteSublattice β :=
  (CompleteSublattice.map f ⊤).copy (range f) image_univ.symm

/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  statement: (f.range : Set β) = range f
  proof: rfl

中文:
定理 range_coe
  结论: (f.range : Set β) = range f
  证明: rfl
-/
theorem range_coe : (f.range : Set β) = range f := rfl

/--
Definition of `toOrderIsoRangeOfInjective` / `toOrderIsoRangeOfInjective` 的定义

English:
definition toOrderIsoRangeOfInjective
  signature: (hf : Injective f)
  body: (orderEmbeddingOfInjective f hf).orderIso

中文:
定义 toOrderIsoRangeOfInjective
  签名: (hf : Injective f)
  定义体: (orderEmbeddingOfInjective f hf).orderIso
-/
@[simps! apply] noncomputable def toOrderIsoRangeOfInjective (hf : Injective f) : α ≃o f.range :=
  (orderEmbeddingOfInjective f hf).orderIso

end CompleteLatticeHom
