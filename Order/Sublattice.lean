/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.SupClosed

/-!
# Sublattices

This file defines sublattices.

## TODO

Subsemilattices, if people care about them.

## Tags

sublattice
-/

@[expose] public section

open Function Set

variable {ι : Sort*} (α β γ : Type*) [Lattice α] [Lattice β] [Lattice γ]

/--
Definition of `Sublattice` / `Sublattice` 的定义

English:
structure Sublattice
  parameters: where
  axioms and operations (3):
    - carrier : Set α
    - supClosed' : SupClosed carrier
    - infClosed' : InfClosed carrier

中文:
结构 Sublattice
  参数: where
  公理与运算 (3 个):
    - carrier : Set α
    - supClosed' : SupClosed carrier
    - infClosed' : InfClosed carrier
-/
structure Sublattice where
  /-- The underlying set of a sublattice. **Do not use directly**. Instead, use the coercion
  `Sublattice α → Set α`, which Lean should automatically insert for you in most cases. -/
  carrier : Set α
  supClosed' : SupClosed carrier
  infClosed' : InfClosed carrier

variable {α β γ}

namespace Sublattice
variable {L M : Sublattice α} {f : LatticeHom α β} {s t : Set α} {a b : α}

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: : SetLike (Sublattice α) α where
  body: L.carrier
  coe_injective L M h := by cases L; congr

中文:
实例 instSetLike
  签名: : SetLike (Sublattice α) α where
  定义体: L.carrier
  coe_injective L M h := by cases L; congr

Depends on / 依赖: L.carrier, carrier
-/
instance instSetLike : SetLike (Sublattice α) α where
  coe L := L.carrier
  coe_injective L M h := by cases L; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Sublattice α)
  body: .ofSetLike (Sublattice α) α

中文:
实例 :
  签名: PartialOrder (Sublattice α)
  定义体: .ofSetLike (Sublattice α) α

Depends on / 依赖: Sublattice, ofSetLike
-/
instance : PartialOrder (Sublattice α) := .ofSetLike (Sublattice α) α

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (L : Sublattice α)
  body: L

initialize_simps_projections Sublattice (carrier -> coe, as_prefix coe)

中文:
定义 Simps.coe
  签名: (L : Sublattice α)
  定义体: L

initialize_simps_projections Sublattice (carrier -> coe, as_prefix coe)
-/
def Simps.coe (L : Sublattice α) : Set α := L

initialize_simps_projections Sublattice (carrier -> coe, as_prefix coe)

/--
Definition of `ofIsSublattice` / `ofIsSublattice` 的定义

English:
abbreviation ofIsSublattice
  signature: (s : Set α) (hs : IsSublattice s)
  body: ⟨s, hs.1, hs.2⟩

中文:
缩写 ofIsSublattice
  签名: (s : Set α) (hs : IsSublattice s)
  定义体: ⟨s, hs.1, hs.2⟩
-/
abbrev ofIsSublattice (s : Set α) (hs : IsSublattice s) : Sublattice α := ⟨s, hs.1, hs.2⟩

/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  statement: (L : Set α) = M ↔ L = M
  proof: SetLike.coe_set_eq

中文:
引理 coe_inj
  结论: (L : Set α) = M ↔ L = M
  证明: SetLike.coe_set_eq

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq

/--
lemma `supClosed` / 引理 `supClosed`

English:
lemma supClosed
  given: (L : Sublattice α)
  statement: SupClosed (L : Set α)
  proof: L.supClosed'

中文:
引理 supClosed
  条件: (L : Sublattice α)
  结论: SupClosed (L : Set α)
  证明: L.supClosed'
-/
@[simp] lemma supClosed (L : Sublattice α) : SupClosed (L : Set α) := L.supClosed'
/--
lemma `infClosed` / 引理 `infClosed`

English:
lemma infClosed
  given: (L : Sublattice α)
  statement: InfClosed (L : Set α)
  proof: L.infClosed'

中文:
引理 infClosed
  条件: (L : Sublattice α)
  结论: InfClosed (L : Set α)
  证明: L.infClosed'
-/
@[simp] lemma infClosed (L : Sublattice α) : InfClosed (L : Set α) := L.infClosed'
/--
lemma `sup_mem` / 引理 `sup_mem`

English:
lemma sup_mem
  given: (ha : a in L) (hb : b in L)
  statement: a ⊔ b in L
  proof: L.supClosed ha hb

中文:
引理 sup_mem
  条件: (ha : a in L) (hb : b in L)
  结论: a ⊔ b in L
  证明: L.supClosed ha hb

Depends on / 依赖: L.supClosed, supClosed
-/
lemma sup_mem (ha : a in L) (hb : b in L) : a ⊔ b in L := L.supClosed ha hb
/--
lemma `inf_mem` / 引理 `inf_mem`

English:
lemma inf_mem
  given: (ha : a in L) (hb : b in L)
  statement: a ⊓ b in L
  proof: L.infClosed ha hb

中文:
引理 inf_mem
  条件: (ha : a in L) (hb : b in L)
  结论: a ⊓ b in L
  证明: L.infClosed ha hb

Depends on / 依赖: L.infClosed, infClosed
-/
lemma inf_mem (ha : a in L) (hb : b in L) : a ⊓ b in L := L.infClosed ha hb
/--
lemma `isSublattice` / 引理 `isSublattice`

English:
lemma isSublattice
  given: (L : Sublattice α)
  statement: IsSublattice (L : Set α)
  proof: ⟨L.supClosed, L.infClosed⟩

中文:
引理 isSublattice
  条件: (L : Sublattice α)
  结论: IsSublattice (L : Set α)
  证明: ⟨L.supClosed, L.infClosed⟩
-/
@[simp] lemma isSublattice (L : Sublattice α) : IsSublattice (L : Set α) :=
  ⟨L.supClosed, L.infClosed⟩

/--
lemma `mem_carrier` / 引理 `mem_carrier`

English:
lemma mem_carrier
  statement: a in L.carrier ↔ a in L
  proof: Iff.rfl

中文:
引理 mem_carrier
  结论: a in L.carrier ↔ a in L
  证明: Iff.rfl
-/
@[simp] lemma mem_carrier : a in L.carrier ↔ a in L := Iff.rfl
/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: (h_sup h_inf)
  statement: a in mk s h_sup h_inf ↔ a in s
  proof: Iff.rfl

中文:
引理 mem_mk
  条件: (h_sup h_inf)
  结论: a in mk s h_sup h_inf ↔ a in s
  证明: Iff.rfl
-/
@[simp] lemma mem_mk (h_sup h_inf) : a in mk s h_sup h_inf ↔ a in s := Iff.rfl
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (h_sup h_inf)
  statement: mk s h_sup h_inf = s
  proof: rfl

中文:
引理 coe_mk
  条件: (h_sup h_inf)
  结论: mk s h_sup h_inf = s
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mk (h_sup h_inf) : mk s h_sup h_inf = s := rfl
/--
lemma `mk_le_mk` / 引理 `mk_le_mk`

English:
lemma mk_le_mk
  given: (hs_sup hs_inf ht_sup ht_inf)
  proof: Iff.rfl

中文:
引理 mk_le_mk
  条件: (hs_sup hs_inf ht_sup ht_inf)
  证明: Iff.rfl
-/
@[simp] lemma mk_le_mk (hs_sup hs_inf ht_sup ht_inf) :
    mk s hs_sup hs_inf <= mk t ht_sup ht_inf ↔ s subseteq t := Iff.rfl
/--
lemma `mk_lt_mk` / 引理 `mk_lt_mk`

English:
lemma mk_lt_mk
  given: (hs_sup hs_inf ht_sup ht_inf)
  proof: Iff.rfl

中文:
引理 mk_lt_mk
  条件: (hs_sup hs_inf ht_sup ht_inf)
  证明: Iff.rfl
-/
@[simp] lemma mk_lt_mk (hs_sup hs_inf ht_sup ht_inf) :
    mk s hs_sup hs_inf < mk t ht_sup ht_inf ↔ s ⊂ t := Iff.rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (L : Sublattice α) (s : Set α) (hs : s = L)
  body: s
  supClosed' := hs.symm ▸ L.supClosed'
  infClosed' := hs.symm ▸ L.infClosed'

中文:
定义 copy
  签名: (L : Sublattice α) (s : Set α) (hs : s = L)
  定义体: s
  supClosed' := hs.symm ▸ L.supClosed'
  infClosed' := hs.symm ▸ L.infClosed'
-/
protected def copy (L : Sublattice α) (s : Set α) (hs : s = L) : Sublattice α where
  carrier := s
  supClosed' := hs.symm ▸ L.supClosed'
  infClosed' := hs.symm ▸ L.infClosed'

/--
lemma `coe_copy` / 引理 `coe_copy`

English:
lemma coe_copy
  given: (L : Sublattice α) (s : Set α) (hs)
  statement: L.copy s hs = s
  proof: rfl

中文:
引理 coe_copy
  条件: (L : Sublattice α) (s : Set α) (hs)
  结论: L.copy s hs = s
  证明: rfl
-/
@[simp, norm_cast] lemma coe_copy (L : Sublattice α) (s : Set α) (hs) : L.copy s hs = s := rfl

/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  given: (L : Sublattice α) (s : Set α) (hs)
  statement: L.copy s hs = L
  proof: SetLike.coe_injective hs

中文:
引理 copy_eq
  条件: (L : Sublattice α) (s : Set α) (hs)
  结论: L.copy s hs = L
  证明: SetLike.coe_injective hs

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, Module, Module.projective_of_isLocalizedModule, SetLike, SetLike.coe_injective, coe_injective, projective_of_isLocalizedModule, toAlgHom, toLinearMap
-/
lemma copy_eq (L : Sublattice α) (s : Set α) (hs) : L.copy s hs = L := SetLike.coe_injective hs

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (forall a, a in L ↔ a in M) -> L = M
  proof: SetLike.ext

中文:
引理 ext
  结论: (对任意 a, a in L ↔ a in M) -> L = M
  证明: SetLike.ext

Depends on / 依赖: SetLike, SetLike.ext
-/
lemma ext : (forall a, a in L ↔ a in M) -> L = M := SetLike.ext

/--
Instance `instSupCoe` / 实例 `instSupCoe`

English:
instance instSupCoe
  signature: : Max L where
  body: ⟨a ⊔ b, L.supClosed a.2 b.2⟩

中文:
实例 instSupCoe
  签名: : Max L where
  定义体: ⟨a ⊔ b, L.supClosed a.2 b.2⟩

Depends on / 依赖: L.supClosed, supClosed
-/
instance instSupCoe : Max L where
  max a b := ⟨a ⊔ b, L.supClosed a.2 b.2⟩

/--
Instance `instInfCoe` / 实例 `instInfCoe`

English:
instance instInfCoe
  signature: : Min L where
  body: ⟨a ⊓ b, L.infClosed a.2 b.2⟩

中文:
实例 instInfCoe
  签名: : Min L where
  定义体: ⟨a ⊓ b, L.infClosed a.2 b.2⟩

Depends on / 依赖: L.infClosed, infClosed
-/
instance instInfCoe : Min L where
  min a b := ⟨a ⊓ b, L.infClosed a.2 b.2⟩

/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: (a b : L)
  statement: a ⊔ b = (a : α) ⊔ b
  proof: rfl

中文:
引理 coe_sup
  条件: (a b : L)
  结论: a ⊔ b = (a : α) ⊔ b
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sup (a b : L) : a ⊔ b = (a : α) ⊔ b := rfl
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (a b : L)
  statement: a ⊓ b = (a : α) ⊓ b
  proof: rfl

中文:
引理 coe_inf
  条件: (a b : L)
  结论: a ⊓ b = (a : α) ⊓ b
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf (a b : L) : a ⊓ b = (a : α) ⊓ b := rfl
/--
lemma `mk_sup_mk` / 引理 `mk_sup_mk`

English:
lemma mk_sup_mk
  given: (a b : α) (ha hb)
  statement: (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩
  proof: rfl

中文:
引理 mk_sup_mk
  条件: (a b : α) (ha hb)
  结论: (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩
  证明: rfl
-/
@[simp] lemma mk_sup_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩ :=
  rfl
/--
lemma `mk_inf_mk` / 引理 `mk_inf_mk`

English:
lemma mk_inf_mk
  given: (a b : α) (ha hb)
  statement: (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩
  proof: rfl

中文:
引理 mk_inf_mk
  条件: (a b : α) (ha hb)
  结论: (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩
  证明: rfl
-/
@[simp] lemma mk_inf_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩ :=
  rfl

/--
Instance `instLatticeCoe` / 实例 `instLatticeCoe`

English:
instance instLatticeCoe
  signature: (L : Sublattice α)
  body: Subtype.coe_injective.lattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 instLatticeCoe
  签名: (L : Sublattice α)
  定义体: Subtype.coe_injective.lattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: Subtype, Subtype.coe_injective.lattice, coe_injective, lattice
-/
instance instLatticeCoe (L : Sublattice α) : Lattice L :=
  Subtype.coe_injective.lattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `instDistribLatticeCoe` / 实例 `instDistribLatticeCoe`

English:
instance instDistribLatticeCoe
  signature: {α : Type*} [DistribLattice α] (L : Sublattice α)
  body: Subtype.coe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 instDistribLatticeCoe
  签名: {α : 类型} [DistribLattice α] (L : Sublattice α)
  定义体: Subtype.coe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: Subtype, Subtype.coe_injective.distribLattice, coe_injective, distribLattice
-/
instance instDistribLatticeCoe {α : Type*} [DistribLattice α] (L : Sublattice α) :
    DistribLattice L :=
  Subtype.coe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (L : Sublattice α)
  body: ((↑) : L -> α)
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 subtype
  签名: (L : Sublattice α)
  定义体: ((↑) : L -> α)
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
-/
def subtype (L : Sublattice α) : LatticeHom L α where
  toFun := ((↑) : L -> α)
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/--
lemma `coe_subtype` / 引理 `coe_subtype`

English:
lemma coe_subtype
  given: (L : Sublattice α)
  statement: L.subtype = ((↑) : L -> α)
  proof: rfl

中文:
引理 coe_subtype
  条件: (L : Sublattice α)
  结论: L.subtype = ((↑) : L -> α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_subtype (L : Sublattice α) : L.subtype = ((↑) : L -> α) := rfl
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

Depends on / 依赖: isReduced_localizationPreserves
-/
lemma subtype_apply (L : Sublattice α) (a : L) : L.subtype a = a := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  given: (L : Sublattice α)
  statement: Injective subtype L
  proof: Subtype.coe_injective

中文:
引理 subtype_injective
  条件: (L : Sublattice α)
  结论: Injective subtype L
  证明: Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective (L : Sublattice α) : Injective subtype L := Subtype.coe_injective

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: (h : L <= M)
  body: Set.inclusion h
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 inclusion
  签名: (h : L <= M)
  定义体: Set.inclusion h
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

Depends on / 依赖: Set.inclusion, inclusion
-/
def inclusion (h : L <= M) : LatticeHom L M where
  toFun := Set.inclusion h
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/--
lemma `coe_inclusion` / 引理 `coe_inclusion`

English:
lemma coe_inclusion
  given: (h : L <= M)
  statement: inclusion h = Set.inclusion h
  proof: rfl

中文:
引理 coe_inclusion
  条件: (h : L <= M)
  结论: inclusion h = Set.inclusion h
  证明: rfl
-/
@[simp] lemma coe_inclusion (h : L <= M) : inclusion h = Set.inclusion h := rfl
/--
lemma `inclusion_apply` / 引理 `inclusion_apply`

English:
lemma inclusion_apply
  given: (h : L <= M) (a : L)
  statement: inclusion h a = Set.inclusion h a
  proof: rfl

中文:
引理 inclusion_apply
  条件: (h : L <= M) (a : L)
  结论: inclusion h a = Set.inclusion h a
  证明: rfl
-/
lemma inclusion_apply (h : L <= M) (a : L) : inclusion h a = Set.inclusion h a := rfl

/--
lemma `inclusion_injective` / 引理 `inclusion_injective`

English:
lemma inclusion_injective
  given: (h : L <= M)
  statement: Injective inclusion h
  proof: Set.inclusion_injective h

中文:
引理 inclusion_injective
  条件: (h : L <= M)
  结论: Injective inclusion h
  证明: Set.inclusion_injective h

Depends on / 依赖: Set.inclusion_injective, inclusion_injective
-/
lemma inclusion_injective (h : L <= M) : Injective inclusion h := Set.inclusion_injective h

/--
lemma `inclusion_rfl` / 引理 `inclusion_rfl`

English:
lemma inclusion_rfl
  given: (L : Sublattice α)
  statement: inclusion le_rfl = LatticeHom.id L
  proof: rfl

中文:
引理 inclusion_rfl
  条件: (L : Sublattice α)
  结论: inclusion le_rfl = LatticeHom.id L
  证明: rfl
-/
@[simp] lemma inclusion_rfl (L : Sublattice α) : inclusion le_rfl = LatticeHom.id L := rfl
/--
lemma `subtype_comp_inclusion` / 引理 `subtype_comp_inclusion`

English:
lemma subtype_comp_inclusion
  given: (h : L <= M)
  statement: M.subtype.comp (inclusion h) = L.subtype
  proof: rfl

中文:
引理 subtype_comp_inclusion
  条件: (h : L <= M)
  结论: M.subtype.comp (inclusion h) = L.subtype
  证明: rfl
-/
@[simp] lemma subtype_comp_inclusion (h : L <= M) : M.subtype.comp (inclusion h) = L.subtype := rfl

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top (Sublattice α) where
  body: univ
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ

中文:
实例 instTop
  签名: : Top (Sublattice α) where
  定义体: univ
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ
-/
instance instTop : Top (Sublattice α) where
  top.carrier := univ
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ

/--
Instance `instBot` / 实例 `instBot`

English:
instance instBot
  signature: : Bot (Sublattice α) where
  body: ∅
  bot.supClosed' := supClosed_empty
  bot.infClosed' := infClosed_empty

中文:
实例 instBot
  签名: : Bot (Sublattice α) where
  定义体: ∅
  bot.supClosed' := supClosed_empty
  bot.infClosed' := infClosed_empty
-/
instance instBot : Bot (Sublattice α) where
  bot.carrier := ∅
  bot.supClosed' := supClosed_empty
  bot.infClosed' := infClosed_empty

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (Sublattice α) where
  body: { carrier := L inter M
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

中文:
实例 instInf
  签名: : Min (Sublattice α) where
  定义体: { carrier := L inter M
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

Depends on / 依赖: carrier
-/
instance instInf : Min (Sublattice α) where
  min L M := { carrier := L inter M
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

/--
Instance `instInfSet` / 实例 `instInfSet`

English:
instance instInfSet
  signature: : InfSet (Sublattice α) where
  body: { carrier := ⨅ L in S, L
supClosed' := supClosed_sInter forall_mem_range.2 fun L => supClosed_sInter
                forall_mem_range.2 fun _ => L.supClosed
infClosed' := infClosed_sInter forall_mem_range.2 fun L => infClosed_sInter
                forall_mem_range.2 fun _ => L.infClosed }

中文:
实例 instInfSet
  签名: : InfSet (Sublattice α) where
  定义体: { carrier := ⨅ L in S, L
supClosed' := supClosed_sInter forall_mem_range.2 fun L => supClosed_sInter
                forall_mem_range.2 fun _ => L.supClosed
infClosed' := infClosed_sInter forall_mem_range.2 fun L => infClosed_sInter
                forall_mem_range.2 fun _ => L.infClosed }

Depends on / 依赖: carrier
-/
instance instInfSet : InfSet (Sublattice α) where
  sInf S := { carrier := ⨅ L in S, L
supClosed' := supClosed_sInter forall_mem_range.2 fun L => supClosed_sInter
                forall_mem_range.2 fun _ => L.supClosed
infClosed' := infClosed_sInter forall_mem_range.2 fun L => infClosed_sInter
                forall_mem_range.2 fun _ => L.infClosed }

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (Sublattice α)
  body: ⟨⊥⟩

中文:
实例 instInhabited
  签名: : Inhabited (Sublattice α)
  定义体: ⟨⊥⟩
-/
instance instInhabited : Inhabited (Sublattice α) := ⟨⊥⟩

/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : Sublattice α) ≃o α where
  body: Equiv.Set.univ _
  map_rel_iff' := Iff.rfl

中文:
定义 topEquiv
  签名: : (⊤ : Sublattice α) ≃o α where
  定义体: Equiv.Set.univ _
  map_rel_iff' := Iff.rfl

Depends on / 依赖: Equiv.Set.univ
-/
def topEquiv : (⊤ : Sublattice α) ≃o α where
  toEquiv := Equiv.Set.univ _
  map_rel_iff' := Iff.rfl

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: (⊤ : Sublattice α) = (univ : Set α)
  proof: rfl

中文:
引理 coe_top
  结论: (⊤ : Sublattice α) = (univ : Set α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_top : (⊤ : Sublattice α) = (univ : Set α) := rfl
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: (⊥ : Sublattice α) = (∅ : Set α)
  proof: rfl

中文:
引理 coe_bot
  结论: (⊥ : Sublattice α) = (∅ : Set α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_bot : (⊥ : Sublattice α) = (∅ : Set α) := rfl
/--
lemma `coe_inf'` / 引理 `coe_inf'`

English:
lemma coe_inf'
  given: (L M : Sublattice α)
  statement: L ⊓ M = (L : Set α) inter M
  proof: rfl

中文:
引理 coe_inf'
  条件: (L M : Sublattice α)
  结论: L ⊓ M = (L : Set α) inter M
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf' (L M : Sublattice α) : L ⊓ M = (L : Set α) inter M := rfl
/--
lemma `coe_sInf` / 引理 `coe_sInf`

English:
lemma coe_sInf
  given: (S : Set (Sublattice α))
  statement: sInf S = ⋂ L in S, (L : Set α)
  proof: rfl

中文:
引理 coe_sInf
  条件: (S : Set (Sublattice α))
  结论: sInf S = ⋂ L in S, (L : Set α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sInf (S : Set (Sublattice α)) : sInf S = ⋂ L in S, (L : Set α) := rfl
/--
lemma `coe_iInf` / 引理 `coe_iInf`

English:
lemma coe_iInf
  given: (f : ι -> Sublattice α)
  statement: ⨅ i, f i = ⋂ i, (f i : Set α)
  proof: by
  simp [iInf]

中文:
引理 coe_iInf
  条件: (f : ι -> Sublattice α)
  结论: ⨅ i, f i = ⋂ i, (f i : Set α)
  证明: by
  simp [iInf]
-/
@[simp, norm_cast] lemma coe_iInf (f : ι -> Sublattice α) : ⨅ i, f i = ⋂ i, (f i : Set α) := by
  simp [iInf]

/--
lemma `coe_eq_univ` / 引理 `coe_eq_univ`

English:
lemma coe_eq_univ
  statement: L = (univ : Set α) ↔ L = ⊤
  proof: by rw [← coe_top, coe_inj]

中文:
引理 coe_eq_univ
  结论: L = (univ : Set α) ↔ L = ⊤
  证明: by rw [← coe_top, coe_inj]
-/
@[simp, norm_cast] lemma coe_eq_univ : L = (univ : Set α) ↔ L = ⊤ := by rw [← coe_top, coe_inj]
/--
lemma `coe_eq_empty` / 引理 `coe_eq_empty`

English:
lemma coe_eq_empty
  statement: L = (∅ : Set α) ↔ L = ⊥
  proof: by rw [← coe_bot, coe_inj]

中文:
引理 coe_eq_empty
  结论: L = (∅ : Set α) ↔ L = ⊥
  证明: by rw [← coe_bot, coe_inj]
-/
@[simp, norm_cast] lemma coe_eq_empty : L = (∅ : Set α) ↔ L = ⊥ := by rw [← coe_bot, coe_inj]

/--
lemma `notMem_bot` / 引理 `notMem_bot`

English:
lemma notMem_bot
  given: (a : α)
  statement: a ∉ (⊥ : Sublattice α)
  proof: id

中文:
引理 notMem_bot
  条件: (a : α)
  结论: a ∉ (⊥ : Sublattice α)
  证明: id
-/
@[simp] lemma notMem_bot (a : α) : a ∉ (⊥ : Sublattice α) := id
/--
lemma `mem_top` / 引理 `mem_top`

English:
lemma mem_top
  given: (a : α)
  statement: a in (⊤ : Sublattice α)
  proof: mem_univ _

中文:
引理 mem_top
  条件: (a : α)
  结论: a in (⊤ : Sublattice α)
  证明: mem_univ _
-/
@[simp] lemma mem_top (a : α) : a in (⊤ : Sublattice α) := mem_univ _
/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  statement: a in L ⊓ M ↔ a in L ∧ a in M
  proof: Iff.rfl

中文:
引理 mem_inf
  结论: a in L ⊓ M ↔ a in L ∧ a in M
  证明: Iff.rfl
-/
@[simp] lemma mem_inf : a in L ⊓ M ↔ a in L ∧ a in M := Iff.rfl
/--
lemma `mem_sInf` / 引理 `mem_sInf`

English:
lemma mem_sInf
  given: {S : Set (Sublattice α)}
  statement: a in sInf S ↔ forall L in S, a in L
  proof: by
  rw [← SetLike.mem_coe]; simp

中文:
引理 mem_sInf
  条件: {S : Set (Sublattice α)}
  结论: a in sInf S ↔ 对任意 L in S, a in L
  证明: by
  rw [← SetLike.mem_coe]; simp
-/
@[simp] lemma mem_sInf {S : Set (Sublattice α)} : a in sInf S ↔ forall L in S, a in L := by
  rw [← SetLike.mem_coe]; simp
/--
lemma `mem_iInf` / 引理 `mem_iInf`

English:
lemma mem_iInf
  given: {f : ι -> Sublattice α}
  statement: a in ⨅ i, f i ↔ forall i, a in f i
  proof: by
  rw [← SetLike.mem_coe]; simp

中文:
引理 mem_iInf
  条件: {f : ι -> Sublattice α}
  结论: a in ⨅ i, f i ↔ 对任意 i, a in f i
  证明: by
  rw [← SetLike.mem_coe]; simp
-/
@[simp] lemma mem_iInf {f : ι -> Sublattice α} : a in ⨅ i, f i ↔ forall i, a in f i := by
  rw [← SetLike.mem_coe]; simp

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: : CompleteLattice (Sublattice α) where
  body: ⊥
  bot_le := fun _S _a => False.elim
  top := ⊤
  le_top := fun _S a _ha => mem_top a
  inf := (· ⊓ ·)
  le_inf := fun _L _M _N hM hN _a ha => ⟨hM ha, hN ha⟩
  inf_le_left := fun _L _M _a => And.left
  inf_le_right := fun _L _M _a => And.right
  __ := completeLatticeOfInf (Sublattice α)
      fun _

中文:
实例 instCompleteLattice
  签名: : CompleteLattice (Sublattice α) where
  定义体: ⊥
  bot_le := fun _S _a => False.elim
  top := ⊤
  le_top := fun _S a _ha => mem_top a
  inf := (· ⊓ ·)
  le_inf := fun _L _M _N hM hN _a ha => ⟨hM ha, hN ha⟩
  inf_le_left := fun _L _M _a => And.left
  inf_le_right := fun _L _M _a => And.right
  __ := completeLatticeOfInf (Sublattice α)
      fun _
-/
instance instCompleteLattice : CompleteLattice (Sublattice α) where
  bot := ⊥
  bot_le := fun _S _a => False.elim
  top := ⊤
  le_top := fun _S a _ha => mem_top a
  inf := (· ⊓ ·)
  le_inf := fun _L _M _N hM hN _a ha => ⟨hM ha, hN ha⟩
  inf_le_left := fun _L _M _a => And.left
  inf_le_right := fun _L _M _a => And.right
  __ := completeLatticeOfInf (Sublattice α)
      fun _s => IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf

/--
lemma `subsingleton_iff` / 引理 `subsingleton_iff`

English:
lemma subsingleton_iff
  statement: Subsingleton (Sublattice α) ↔ IsEmpty α
  proof: ⟨fun _ => univ_eq_empty_iff.1 coe_inj.2 Subsingleton.elim ⊤ ⊥,
    fun _ => SetLike.coe_injective.subsingleton⟩

中文:
引理 subsingleton_iff
  结论: Subsingleton (Sublattice α) ↔ IsEmpty α
  证明: ⟨fun _ => univ_eq_empty_iff.1 coe_inj.2 Subsingleton.elim ⊤ ⊥,
    fun _ => SetLike.coe_injective.subsingleton⟩

Depends on / 依赖: SetLike, SetLike.coe_injective.subsingleton, Subsingleton, Subsingleton.elim, coe_inj, coe_injective, subsingleton, univ_eq_empty_iff
-/
lemma subsingleton_iff : Subsingleton (Sublattice α) ↔ IsEmpty α :=
⟨fun _ => univ_eq_empty_iff.1 coe_inj.2 Subsingleton.elim ⊤ ⊥,
    fun _ => SetLike.coe_injective.subsingleton⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (Sublattice α) where
  body: @Subsingleton.elim _ (subsingleton_iff.2 ‹_›) _ _

中文:
实例 [IsEmpty
  签名: α] : Unique (Sublattice α) where
  定义体: @Subsingleton.elim _ (subsingleton_iff.2 ‹_›) _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, subsingleton_iff
-/
instance [IsEmpty α] : Unique (Sublattice α) where
  uniq _ := @Subsingleton.elim _ (subsingleton_iff.2 ‹_›) _ _

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : LatticeHom α β) (L : Sublattice β)
  body: f ⁻¹' L
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

中文:
定义 comap
  签名: (f : LatticeHom α β) (L : Sublattice β)
  定义体: f ⁻¹' L
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _
-/
def comap (f : LatticeHom α β) (L : Sublattice β) : Sublattice α where
  carrier := f ⁻¹' L
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

/--
lemma `coe_comap` / 引理 `coe_comap`

English:
lemma coe_comap
  given: (L : Sublattice β) (f : LatticeHom α β)
  statement: L.comap f = f ⁻¹' L
  proof: rfl

中文:
引理 coe_comap
  条件: (L : Sublattice β) (f : LatticeHom α β)
  结论: L.comap f = f ⁻¹' L
  证明: rfl
-/
@[simp, norm_cast] lemma coe_comap (L : Sublattice β) (f : LatticeHom α β) : L.comap f = f ⁻¹' L :=
  rfl

/--
lemma `mem_comap` / 引理 `mem_comap`

English:
lemma mem_comap
  given: {L : Sublattice β}
  statement: a in L.comap f ↔ f a in L
  proof: Iff.rfl

中文:
引理 mem_comap
  条件: {L : Sublattice β}
  结论: a in L.comap f ↔ f a in L
  证明: Iff.rfl
-/
@[simp] lemma mem_comap {L : Sublattice β} : a in L.comap f ↔ f a in L := Iff.rfl

/--
lemma `comap_mono` / 引理 `comap_mono`

English:
lemma comap_mono
  statement: Monotone (comap f)
  proof: fun _ _ => preimage_mono

中文:
引理 comap_mono
  结论: Monotone (comap f)
  证明: fun _ _ => preimage_mono

Depends on / 依赖: preimage_mono
-/
lemma comap_mono : Monotone (comap f) := fun _ _ => preimage_mono

/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (L : Sublattice α)
  statement: L.comap (LatticeHom.id _) = L
  proof: rfl

中文:
引理 comap_id
  条件: (L : Sublattice α)
  结论: L.comap (LatticeHom.id _) = L
  证明: rfl
-/
@[simp] lemma comap_id (L : Sublattice α) : L.comap (LatticeHom.id _) = L := rfl

/--
lemma `comap_comap` / 引理 `comap_comap`

English:
lemma comap_comap
  given: (L : Sublattice γ) (g : LatticeHom β γ) (f : LatticeHom α β)
  proof: rfl

中文:
引理 comap_comap
  条件: (L : Sublattice γ) (g : LatticeHom β γ) (f : LatticeHom α β)
  证明: rfl
-/
@[simp] lemma comap_comap (L : Sublattice γ) (g : LatticeHom β γ) (f : LatticeHom α β) :
    (L.comap g).comap f = L.comap (g.comp f) := rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : LatticeHom α β) (L : Sublattice α)
  body: f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f

中文:
定义 map
  签名: (f : LatticeHom α β) (L : Sublattice α)
  定义体: f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f
-/
def map (f : LatticeHom α β) (L : Sublattice α) : Sublattice β where
  carrier := f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f

/--
lemma `coe_map` / 引理 `coe_map`

English:
lemma coe_map
  given: (f : LatticeHom α β) (L : Sublattice α)
  statement: (L.map f : Set β) = f '' L
  proof: rfl

中文:
引理 coe_map
  条件: (f : LatticeHom α β) (L : Sublattice α)
  结论: (L.map f : Set β) = f '' L
  证明: rfl
-/
@[simp] lemma coe_map (f : LatticeHom α β) (L : Sublattice α) : (L.map f : Set β) = f '' L := rfl
/--
lemma `mem_map` / 引理 `mem_map`

English:
lemma mem_map
  given: {b : β}
  statement: b in L.map f ↔ exists a in L, f a = b
  proof: Iff.rfl

中文:
引理 mem_map
  条件: {b : β}
  结论: b in L.map f ↔ 存在 a in L, f a = b
  证明: Iff.rfl
-/
@[simp] lemma mem_map {b : β} : b in L.map f ↔ exists a in L, f a = b := Iff.rfl

/--
lemma `mem_map_of_mem` / 引理 `mem_map_of_mem`

English:
lemma mem_map_of_mem
  given: (f : LatticeHom α β) {a : α}
  statement: a in L -> f a in L.map f
  proof: mem_image_of_mem f

中文:
引理 mem_map_of_mem
  条件: (f : LatticeHom α β) {a : α}
  结论: a in L -> f a in L.map f
  证明: mem_image_of_mem f

Depends on / 依赖: mem_image_of_mem
-/
lemma mem_map_of_mem (f : LatticeHom α β) {a : α} : a in L -> f a in L.map f := mem_image_of_mem f
/--
lemma `apply_coe_mem_map` / 引理 `apply_coe_mem_map`

English:
lemma apply_coe_mem_map
  given: (f : LatticeHom α β) (a : L)
  statement: f a in L.map f
  proof: mem_map_of_mem f a.prop

中文:
引理 apply_coe_mem_map
  条件: (f : LatticeHom α β) (a : L)
  结论: f a in L.map f
  证明: mem_map_of_mem f a.prop

Depends on / 依赖: a.prop, mem_map_of_mem
-/
lemma apply_coe_mem_map (f : LatticeHom α β) (a : L) : f a in L.map f := mem_map_of_mem f a.prop

/--
lemma `map_mono` / 引理 `map_mono`

English:
lemma map_mono
  statement: Monotone (map f)
  proof: fun _ _ => image_mono

中文:
引理 map_mono
  结论: Monotone (map f)
  证明: fun _ _ => image_mono

Depends on / 依赖: image_mono
-/
lemma map_mono : Monotone (map f) := fun _ _ => image_mono

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: L.map (LatticeHom.id α) = L
  proof: SetLike.coe_injective image_id _

中文:
引理 map_id
  结论: L.map (LatticeHom.id α) = L
  证明: SetLike.coe_injective image_id _
-/
@[simp] lemma map_id : L.map (LatticeHom.id α) = L := SetLike.coe_injective image_id _

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: (g : LatticeHom β γ) (f : LatticeHom α β)
  proof: SetLike.coe_injective image_image _ _ _

中文:
引理 map_map
  条件: (g : LatticeHom β γ) (f : LatticeHom α β)
  证明: SetLike.coe_injective image_image _ _ _

Depends on / 依赖: IsLocalRing, IsLocalRing.of_isUnit_or_isUnit_one_sub_self, IsUnit, IsUnit.mk0, Or.inl, Or.inr, classical, isUnit_one, of_isUnit_or_isUnit_one_sub_self, sub_zero
-/
@[simp] lemma map_map (g : LatticeHom β γ) (f : LatticeHom α β) :
(L.map f).map g = L.map (g.comp f) := SetLike.coe_injective image_image _ _ _

/--
lemma `mem_map_equiv` / 引理 `mem_map_equiv`

English:
lemma mem_map_equiv
  given: {f : α ≃o β} {a : β}
  statement: a in L.map f ↔ f.symm a in L
  proof: Set.mem_image_equiv

中文:
引理 mem_map_equiv
  条件: {f : α ≃o β} {a : β}
  结论: a in L.map f ↔ f.symm a in L
  证明: Set.mem_image_equiv

Depends on / 依赖: Set.mem_image_equiv, mem_image_equiv
-/
lemma mem_map_equiv {f : α ≃o β} {a : β} : a in L.map f ↔ f.symm a in L := Set.mem_image_equiv

/--
lemma `apply_mem_map_iff` / 引理 `apply_mem_map_iff`

English:
lemma apply_mem_map_iff
  given: (hf : Injective f)
  statement: f a in L.map f ↔ a in L
  proof: hf.mem_set_image

中文:
引理 apply_mem_map_iff
  条件: (hf : Injective f)
  结论: f a in L.map f ↔ a in L
  证明: hf.mem_set_image

Depends on / 依赖: hf.mem_set_image, mem_set_image
-/
lemma apply_mem_map_iff (hf : Injective f) : f a in L.map f ↔ a in L := hf.mem_set_image

/--
lemma `map_equiv_eq_comap_symm` / 引理 `map_equiv_eq_comap_symm`

English:
lemma map_equiv_eq_comap_symm
  given: (f : α ≃o β) (L : Sublattice α)
  proof: SetLike.coe_injective f.toEquiv.image_eq_preimage_symm L

中文:
引理 map_equiv_eq_comap_symm
  条件: (f : α ≃o β) (L : Sublattice α)
  证明: SetLike.coe_injective f.toEquiv.image_eq_preimage_symm L

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
lemma map_equiv_eq_comap_symm (f : α ≃o β) (L : Sublattice α) :
    L.map f = L.comap (f.symm : LatticeHom β α) :=
SetLike.coe_injective f.toEquiv.image_eq_preimage_symm L

/--
lemma `comap_equiv_eq_map_symm` / 引理 `comap_equiv_eq_map_symm`

English:
lemma comap_equiv_eq_map_symm
  given: (f : β ≃o α) (L : Sublattice α)
  proof: (map_equiv_eq_comap_symm f.symm L).symm

中文:
引理 comap_equiv_eq_map_symm
  条件: (f : β ≃o α) (L : Sublattice α)
  证明: (map_equiv_eq_comap_symm f.symm L).symm

Depends on / 依赖: f.symm, map_equiv_eq_comap_symm
-/
lemma comap_equiv_eq_map_symm (f : β ≃o α) (L : Sublattice α) :
    L.comap f = L.map (f.symm : LatticeHom α β) := (map_equiv_eq_comap_symm f.symm L).symm

/--
lemma `map_symm_eq_iff_eq_map` / 引理 `map_symm_eq_iff_eq_map`

English:
lemma map_symm_eq_iff_eq_map
  given: {M : Sublattice β} {e : β ≃o α}
  proof: by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm

中文:
引理 map_symm_eq_iff_eq_map
  条件: {M : Sublattice β} {e : β ≃o α}
  证明: by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm

Depends on / 依赖: Equiv.eq_image_iff_symm_image_eq, coe_inj, eq_image_iff_symm_image_eq, simp_rw
-/
lemma map_symm_eq_iff_eq_map {M : Sublattice β} {e : β ≃o α} :
    L.map ↑e.symm = M ↔ L = M.map ↑e := by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm

/--
lemma `map_le_iff_le_comap` / 引理 `map_le_iff_le_comap`

English:
lemma map_le_iff_le_comap
  given: {f : LatticeHom α β} {M : Sublattice β}
  statement: L.map f <= M ↔ L <= M.comap f
  proof: image_subset_iff

中文:
引理 map_le_iff_le_comap
  条件: {f : LatticeHom α β} {M : Sublattice β}
  结论: L.map f <= M ↔ L <= M.comap f
  证明: image_subset_iff

Depends on / 依赖: image_subset_iff
-/
lemma map_le_iff_le_comap {f : LatticeHom α β} {M : Sublattice β} : L.map f <= M ↔ L <= M.comap f :=
  image_subset_iff

/--
lemma `gc_map_comap` / 引理 `gc_map_comap`

English:
lemma gc_map_comap
  given: (f : LatticeHom α β)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ => map_le_iff_le_comap

中文:
引理 gc_map_comap
  条件: (f : LatticeHom α β)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ => map_le_iff_le_comap

Depends on / 依赖: map_le_iff_le_comap
-/
lemma gc_map_comap (f : LatticeHom α β) : GaloisConnection (map f) (comap f) :=
  fun _ _ => map_le_iff_le_comap

/--
lemma `map_bot` / 引理 `map_bot`

English:
lemma map_bot
  given: (f : LatticeHom α β)
  statement: (⊥ : Sublattice α).map f = ⊥
  proof: (gc_map_comap f).l_bot

中文:
引理 map_bot
  条件: (f : LatticeHom α β)
  结论: (⊥ : Sublattice α).map f = ⊥
  证明: (gc_map_comap f).l_bot
-/
@[simp] lemma map_bot (f : LatticeHom α β) : (⊥ : Sublattice α).map f = ⊥ := (gc_map_comap f).l_bot

/--
lemma `map_sup` / 引理 `map_sup`

English:
lemma map_sup
  given: (f : LatticeHom α β) (L M : Sublattice α)
  statement: (L ⊔ M).map f = L.map f ⊔ M.map f
  proof: (gc_map_comap f).l_sup

中文:
引理 map_sup
  条件: (f : LatticeHom α β) (L M : Sublattice α)
  结论: (L ⊔ M).map f = L.map f ⊔ M.map f
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
lemma map_sup (f : LatticeHom α β) (L M : Sublattice α) : (L ⊔ M).map f = L.map f ⊔ M.map f :=
  (gc_map_comap f).l_sup

/--
lemma `map_iSup` / 引理 `map_iSup`

English:
lemma map_iSup
  given: (f : LatticeHom α β) (L : ι -> Sublattice α)
  statement: (⨆ i, L i).map f = ⨆ i, (L i).map f
  proof: (gc_map_comap f).l_iSup

中文:
引理 map_iSup
  条件: (f : LatticeHom α β) (L : ι -> Sublattice α)
  结论: (⨆ i, L i).map f = ⨆ i, (L i).map f
  证明: (gc_map_comap f).l_iSup

Depends on / 依赖: gc_map_comap, l_iSup
-/
lemma map_iSup (f : LatticeHom α β) (L : ι -> Sublattice α) : (⨆ i, L i).map f = ⨆ i, (L i).map f :=
  (gc_map_comap f).l_iSup

/--
lemma `comap_top` / 引理 `comap_top`

English:
lemma comap_top
  given: (f : LatticeHom α β)
  statement: (⊤ : Sublattice β).comap f = ⊤
  proof: (gc_map_comap f).u_top

中文:
引理 comap_top
  条件: (f : LatticeHom α β)
  结论: (⊤ : Sublattice β).comap f = ⊤
  证明: (gc_map_comap f).u_top
-/
@[simp] lemma comap_top (f : LatticeHom α β) : (⊤ : Sublattice β).comap f = ⊤ :=
  (gc_map_comap f).u_top

/--
lemma `comap_inf` / 引理 `comap_inf`

English:
lemma comap_inf
  given: (L M : Sublattice β) (f : LatticeHom α β)
  proof: (gc_map_comap f).u_inf

中文:
引理 comap_inf
  条件: (L M : Sublattice β) (f : LatticeHom α β)
  证明: (gc_map_comap f).u_inf

Depends on / 依赖: gc_map_comap, u_inf
-/
lemma comap_inf (L M : Sublattice β) (f : LatticeHom α β) :
    (L ⊓ M).comap f = L.comap f ⊓ M.comap f := (gc_map_comap f).u_inf

/--
lemma `comap_iInf` / 引理 `comap_iInf`

English:
lemma comap_iInf
  given: (f : LatticeHom α β) (s : ι -> Sublattice β)
  proof: (gc_map_comap f).u_iInf

中文:
引理 comap_iInf
  条件: (f : LatticeHom α β) (s : ι -> Sublattice β)
  证明: (gc_map_comap f).u_iInf

Depends on / 依赖: gc_map_comap, u_iInf
-/
lemma comap_iInf (f : LatticeHom α β) (s : ι -> Sublattice β) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (gc_map_comap f).u_iInf

/--
lemma `map_inf_le` / 引理 `map_inf_le`

English:
lemma map_inf_le
  given: (L M : Sublattice α) (f : LatticeHom α β)
  statement: map f (L ⊓ M) <= map f L ⊓ map f M
  proof: map_mono.map_inf_le _ _

中文:
引理 map_inf_le
  条件: (L M : Sublattice α) (f : LatticeHom α β)
  结论: map f (L ⊓ M) <= map f L ⊓ map f M
  证明: map_mono.map_inf_le _ _

Depends on / 依赖: map_inf_le, map_mono, map_mono.map_inf_le
-/
lemma map_inf_le (L M : Sublattice α) (f : LatticeHom α β) : map f (L ⊓ M) <= map f L ⊓ map f M :=
  map_mono.map_inf_le _ _

/--
lemma `le_comap_sup` / 引理 `le_comap_sup`

English:
lemma le_comap_sup
  given: (L M : Sublattice β) (f : LatticeHom α β)
  proof: comap_mono.le_map_sup _ _

中文:
引理 le_comap_sup
  条件: (L M : Sublattice β) (f : LatticeHom α β)
  证明: comap_mono.le_map_sup _ _

Depends on / 依赖: comap_mono, comap_mono.le_map_sup, le_map_sup
-/
lemma le_comap_sup (L M : Sublattice β) (f : LatticeHom α β) :
    comap f L ⊔ comap f M <= comap f (L ⊔ M) := comap_mono.le_map_sup _ _

/--
lemma `le_comap_iSup` / 引理 `le_comap_iSup`

English:
lemma le_comap_iSup
  given: (f : LatticeHom α β) (L : ι -> Sublattice β)
  proof: comap_mono.le_map_iSup

中文:
引理 le_comap_iSup
  条件: (f : LatticeHom α β) (L : ι -> Sublattice β)
  证明: comap_mono.le_map_iSup

Depends on / 依赖: comap_mono, comap_mono.le_map_iSup, le_map_iSup
-/
lemma le_comap_iSup (f : LatticeHom α β) (L : ι -> Sublattice β) :
    ⨆ i, (L i).comap f <= (⨆ i, L i).comap f := comap_mono.le_map_iSup

/--
lemma `map_inf` / 引理 `map_inf`

English:
lemma map_inf
  given: (L M : Sublattice α) (f : LatticeHom α β) (hf : Injective f)
  proof: by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

中文:
引理 map_inf
  条件: (L M : Sublattice α) (f : LatticeHom α β) (hf : Injective f)
  证明: by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_set_eq, coe_set_eq, image_inter
-/
lemma map_inf (L M : Sublattice α) (f : LatticeHom α β) (hf : Injective f) :
    map f (L ⊓ M) = map f L ⊓ map f M := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

/--
lemma `map_top` / 引理 `map_top`

English:
lemma map_top
  given: (f : LatticeHom α β) (h : Surjective f)
  statement: Sublattice.map f ⊤ = ⊤
  proof: SetLike.coe_injective by simp [h.range_eq]

中文:
引理 map_top
  条件: (f : LatticeHom α β) (h : Surjective f)
  结论: Sublattice.map f ⊤ = ⊤
  证明: SetLike.coe_injective by simp [h.range_eq]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, h.range_eq, range_eq
-/
lemma map_top (f : LatticeHom α β) (h : Surjective f) : Sublattice.map f ⊤ = ⊤ :=
SetLike.coe_injective by simp [h.range_eq]

end Sublattice

namespace Sublattice
variable {L M : Sublattice α} {f : LatticeHom α β} {s t : Set α} {a : α}

/-- Binary product of sublattices as a sublattice. -/
@[simps]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (L : Sublattice α) (M : Sublattice β)
  body: L ×ˢ M
  supClosed' := L.supClosed.prod M.supClosed
  infClosed' := L.infClosed.prod M.infClosed

中文:
定义 prod
  签名: (L : Sublattice α) (M : Sublattice β)
  定义体: L ×ˢ M
  supClosed' := L.supClosed.prod M.supClosed
  infClosed' := L.infClosed.prod M.infClosed
-/
def prod (L : Sublattice α) (M : Sublattice β) : Sublattice (α × β) where
  carrier := L ×ˢ M
  supClosed' := L.supClosed.prod M.supClosed
  infClosed' := L.infClosed.prod M.infClosed

attribute [norm_cast] coe_prod

/--
lemma `mem_prod` / 引理 `mem_prod`

English:
lemma mem_prod
  given: {M : Sublattice β} {p : α × β}
  statement: p in L.prod M ↔ p.1 in L ∧ p.2 in M
  proof: Iff.rfl

@[gcongr]

中文:
引理 mem_prod
  条件: {M : Sublattice β} {p : α × β}
  结论: p in L.prod M ↔ p.1 in L ∧ p.2 in M
  证明: Iff.rfl

@[gcongr]
-/
@[simp] lemma mem_prod {M : Sublattice β} {p : α × β} : p in L.prod M ↔ p.1 in L ∧ p.2 in M := Iff.rfl

@[gcongr]
/--
lemma `prod_mono` / 引理 `prod_mono`

English:
lemma prod_mono
  given: {L₁ L₂ : Sublattice α} {M₁ M₂ : Sublattice β} (hL : L₁ <= L₂) (hM : M₁ <= M₂)
  proof: Set.prod_mono hL hM

中文:
引理 prod_mono
  条件: {L₁ L₂ : Sublattice α} {M₁ M₂ : Sublattice β} (hL : L₁ <= L₂) (hM : M₁ <= M₂)
  证明: Set.prod_mono hL hM

Depends on / 依赖: Set.prod_mono, prod_mono
-/
lemma prod_mono {L₁ L₂ : Sublattice α} {M₁ M₂ : Sublattice β} (hL : L₁ <= L₂) (hM : M₁ <= M₂) :
    L₁.prod M₁ <= L₂.prod M₂ := Set.prod_mono hL hM

/--
lemma `prod_mono_left` / 引理 `prod_mono_left`

English:
lemma prod_mono_left
  given: {L₁ L₂ : Sublattice α} {M : Sublattice β} (hL : L₁ <= L₂)
  proof: prod_mono hL le_rfl

中文:
引理 prod_mono_left
  条件: {L₁ L₂ : Sublattice α} {M : Sublattice β} (hL : L₁ <= L₂)
  证明: prod_mono hL le_rfl

Depends on / 依赖: le_rfl, prod_mono
-/
lemma prod_mono_left {L₁ L₂ : Sublattice α} {M : Sublattice β} (hL : L₁ <= L₂) :
    L₁.prod M <= L₂.prod M := prod_mono hL le_rfl

/--
lemma `prod_mono_right` / 引理 `prod_mono_right`

English:
lemma prod_mono_right
  given: {M₁ M₂ : Sublattice β} (hM : M₁ <= M₂)
  statement: L.prod M₁ <= L.prod M₂
  proof: prod_mono le_rfl hM

中文:
引理 prod_mono_right
  条件: {M₁ M₂ : Sublattice β} (hM : M₁ <= M₂)
  结论: L.prod M₁ <= L.prod M₂
  证明: prod_mono le_rfl hM

Depends on / 依赖: le_rfl, prod_mono
-/
lemma prod_mono_right {M₁ M₂ : Sublattice β} (hM : M₁ <= M₂) : L.prod M₁ <= L.prod M₂ :=
  prod_mono le_rfl hM

/--
lemma `prod_left_mono` / 引理 `prod_left_mono`

English:
lemma prod_left_mono
  statement: Monotone fun L : Sublattice α => L.prod M
  proof: fun _ _ => prod_mono_left

中文:
引理 prod_left_mono
  结论: Monotone fun L : Sublattice α => L.prod M
  证明: fun _ _ => prod_mono_left

Depends on / 依赖: prod_mono_left
-/
lemma prod_left_mono : Monotone fun L : Sublattice α => L.prod M := fun _ _ => prod_mono_left
/--
lemma `prod_right_mono` / 引理 `prod_right_mono`

English:
lemma prod_right_mono
  statement: Monotone fun M : Sublattice β => L.prod M
  proof: fun _ _ => prod_mono_right

中文:
引理 prod_right_mono
  结论: Monotone fun M : Sublattice β => L.prod M
  证明: fun _ _ => prod_mono_right

Depends on / 依赖: prod_mono_right
-/
lemma prod_right_mono : Monotone fun M : Sublattice β => L.prod M := fun _ _ => prod_mono_right

/--
lemma `prod_top` / 引理 `prod_top`

English:
lemma prod_top
  given: (L : Sublattice α)
  statement: L.prod (⊤ : Sublattice β) = L.comap LatticeHom.fst
  proof: ext fun a => by simp [mem_prod, LatticeHom.coe_fst]

中文:
引理 prod_top
  条件: (L : Sublattice α)
  结论: L.prod (⊤ : Sublattice β) = L.comap LatticeHom.fst
  证明: ext fun a => by simp [mem_prod, LatticeHom.coe_fst]

Depends on / 依赖: LatticeHom, LatticeHom.coe_fst, coe_fst, mem_prod
-/
lemma prod_top (L : Sublattice α) : L.prod (⊤ : Sublattice β) = L.comap LatticeHom.fst :=
  ext fun a => by simp [mem_prod, LatticeHom.coe_fst]

/--
lemma `top_prod` / 引理 `top_prod`

English:
lemma top_prod
  given: (L : Sublattice β)
  statement: (⊤ : Sublattice α).prod L = L.comap LatticeHom.snd
  proof: ext fun a => by simp [mem_prod, LatticeHom.coe_snd]

中文:
引理 top_prod
  条件: (L : Sublattice β)
  结论: (⊤ : Sublattice α).prod L = L.comap LatticeHom.snd
  证明: ext fun a => by simp [mem_prod, LatticeHom.coe_snd]

Depends on / 依赖: LatticeHom, LatticeHom.coe_snd, coe_snd, mem_prod
-/
lemma top_prod (L : Sublattice β) : (⊤ : Sublattice α).prod L = L.comap LatticeHom.snd :=
  ext fun a => by simp [mem_prod, LatticeHom.coe_snd]

/--
lemma `top_prod_top` / 引理 `top_prod_top`

English:
lemma top_prod_top
  statement: (⊤ : Sublattice α).prod (⊤ : Sublattice β) = ⊤
  proof: (top_prod _).trans comap_top _

中文:
引理 top_prod_top
  结论: (⊤ : Sublattice α).prod (⊤ : Sublattice β) = ⊤
  证明: (top_prod _).trans comap_top _
-/
@[simp] lemma top_prod_top : (⊤ : Sublattice α).prod (⊤ : Sublattice β) = ⊤ :=
(top_prod _).trans comap_top _

/--
lemma `prod_bot` / 引理 `prod_bot`

English:
lemma prod_bot
  given: (L : Sublattice α)
  statement: L.prod (⊥ : Sublattice β) = ⊥
  proof: SetLike.coe_injective prod_empty

中文:
引理 prod_bot
  条件: (L : Sublattice α)
  结论: L.prod (⊥ : Sublattice β) = ⊥
  证明: SetLike.coe_injective prod_empty
-/
@[simp] lemma prod_bot (L : Sublattice α) : L.prod (⊥ : Sublattice β) = ⊥ :=
  SetLike.coe_injective prod_empty

/--
lemma `bot_prod` / 引理 `bot_prod`

English:
lemma bot_prod
  given: (M : Sublattice β)
  statement: (⊥ : Sublattice α).prod M = ⊥
  proof: SetLike.coe_injective empty_prod

中文:
引理 bot_prod
  条件: (M : Sublattice β)
  结论: (⊥ : Sublattice α).prod M = ⊥
  证明: SetLike.coe_injective empty_prod
-/
@[simp] lemma bot_prod (M : Sublattice β) : (⊥ : Sublattice α).prod M = ⊥ :=
  SetLike.coe_injective empty_prod

/--
lemma `le_prod_iff` / 引理 `le_prod_iff`

English:
lemma le_prod_iff
  given: {M : Sublattice β} {N : Sublattice (α × β)}
  proof: by
  simp [SetLike.le_def, forall_and]

中文:
引理 le_prod_iff
  条件: {M : Sublattice β} {N : Sublattice (α × β)}
  证明: by
  simp [SetLike.le_def, forall_and]

Depends on / 依赖: SetLike, SetLike.le_def, forall_and, le_def
-/
lemma le_prod_iff {M : Sublattice β} {N : Sublattice (α × β)} :
    N <= L.prod M ↔ N <= comap LatticeHom.fst L ∧ N <= comap LatticeHom.snd M := by
  simp [SetLike.le_def, forall_and]

/--
lemma `prod_eq_bot` / 引理 `prod_eq_bot`

English:
lemma prod_eq_bot
  given: {M : Sublattice β}
  statement: L.prod M = ⊥ ↔ L = ⊥ ∨ M = ⊥
  proof: by
  simpa only [← coe_inj] using! Set.prod_eq_empty_iff

中文:
引理 prod_eq_bot
  条件: {M : Sublattice β}
  结论: L.prod M = ⊥ ↔ L = ⊥ ∨ M = ⊥
  证明: by
  simpa only [← coe_inj] using! Set.prod_eq_empty_iff
-/
@[simp] lemma prod_eq_bot {M : Sublattice β} : L.prod M = ⊥ ↔ L = ⊥ ∨ M = ⊥ := by
  simpa only [← coe_inj] using! Set.prod_eq_empty_iff

/--
lemma `prod_eq_top` / 引理 `prod_eq_top`

English:
lemma prod_eq_top
  given: [Nonempty α] [Nonempty β] {M : Sublattice β}
  proof: by simpa only [← coe_inj] using! Set.prod_eq_univ

中文:
引理 prod_eq_top
  条件: [Nonempty α] [Nonempty β] {M : Sublattice β}
  证明: by simpa only [← coe_inj] using! Set.prod_eq_univ
-/
@[simp] lemma prod_eq_top [Nonempty α] [Nonempty β] {M : Sublattice β} :
    L.prod M = ⊤ ↔ L = ⊤ ∧ M = ⊤ := by simpa only [← coe_inj] using! Set.prod_eq_univ

/-- The product of sublattices is isomorphic to their product as lattices. -/
@[simps! toEquiv apply symm_apply]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: (L : Sublattice α) (M : Sublattice β)
  body: Equiv.Set.prod _ _
  map_rel_iff' := Iff.rfl

中文:
定义 prodEquiv
  签名: (L : Sublattice α) (M : Sublattice β)
  定义体: Equiv.Set.prod _ _
  map_rel_iff' := Iff.rfl

Depends on / 依赖: Equiv.Set.prod
-/
def prodEquiv (L : Sublattice α) (M : Sublattice β) : L.prod M ≃o L × M where
  toEquiv := Equiv.Set.prod _ _
  map_rel_iff' := Iff.rfl

section Pi
variable {κ : Type*} {π : κ -> Type*} [forall i, Lattice (π i)]

/-- Arbitrary product of sublattices. Given an index set `s` and a family of sublattices
`L : Π i, Sublattice (α i)`, `pi s L` is the sublattice of dependent functions `f : Π i, α i` such
that `f i` belongs to `L i` whenever `i ∈ s`. -/
@[simps]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (s : Set κ) (L : forall i, Sublattice (π i))
  body: s.pi fun i => L i
  supClosed' := supClosed_pi fun i _ => (L i).supClosed
  infClosed' := infClosed_pi fun i _ => (L i).infClosed

中文:
定义 pi
  签名: (s : Set κ) (L : 对任意 i, Sublattice (π i))
  定义体: s.pi fun i => L i
  supClosed' := supClosed_pi fun i _ => (L i).supClosed
  infClosed' := infClosed_pi fun i _ => (L i).infClosed

Depends on / 依赖: s.pi
-/
def pi (s : Set κ) (L : forall i, Sublattice (π i)) : Sublattice (forall i, π i) where
  carrier := s.pi fun i => L i
  supClosed' := supClosed_pi fun i _ => (L i).supClosed
  infClosed' := infClosed_pi fun i _ => (L i).infClosed

attribute [norm_cast] coe_pi

/--
lemma `mem_pi` / 引理 `mem_pi`

English:
lemma mem_pi
  given: {s : Set κ} {L : forall i, Sublattice (π i)} {x : forall i, π i}
  proof: Iff.rfl

中文:
引理 mem_pi
  条件: {s : Set κ} {L : 对任意 i, Sublattice (π i)} {x : 对任意 i, π i}
  证明: Iff.rfl
-/
@[simp] lemma mem_pi {s : Set κ} {L : forall i, Sublattice (π i)} {x : forall i, π i} :
    x in pi s L ↔ forall i, i in s -> x i in L i := Iff.rfl

/--
lemma `pi_empty` / 引理 `pi_empty`

English:
lemma pi_empty
  given: (L : forall i, Sublattice (π i))
  statement: pi ∅ L = ⊤
  proof: ext fun a => by simp [mem_pi]

中文:
引理 pi_empty
  条件: (L : 对任意 i, Sublattice (π i))
  结论: pi ∅ L = ⊤
  证明: ext fun a => by simp [mem_pi]
-/
@[simp] lemma pi_empty (L : forall i, Sublattice (π i)) : pi ∅ L = ⊤ := ext fun a => by simp [mem_pi]

/--
lemma `pi_top` / 引理 `pi_top`

English:
lemma pi_top
  given: (s : Set κ)
  statement: (pi s fun _ => ⊤ : Sublattice (forall i, π i)) = ⊤
  proof: ext fun a => by simp [mem_pi]

中文:
引理 pi_top
  条件: (s : Set κ)
  结论: (pi s fun _ => ⊤ : Sublattice (对任意 i, π i)) = ⊤
  证明: ext fun a => by simp [mem_pi]
-/
@[simp] lemma pi_top (s : Set κ) : (pi s fun _ => ⊤ : Sublattice (forall i, π i)) = ⊤ :=
  ext fun a => by simp [mem_pi]

/--
lemma `pi_bot` / 引理 `pi_bot`

English:
lemma pi_bot
  given: {s : Set κ} (hs : s.Nonempty)
  statement: (pi s fun _ => ⊥ : Sublattice (forall i, π i)) = ⊥
  proof: ext fun a => by simpa [mem_pi] using! hs

中文:
引理 pi_bot
  条件: {s : Set κ} (hs : s.Nonempty)
  结论: (pi s fun _ => ⊥ : Sublattice (对任意 i, π i)) = ⊥
  证明: ext fun a => by simpa [mem_pi] using! hs
-/
@[simp] lemma pi_bot {s : Set κ} (hs : s.Nonempty) : (pi s fun _ => ⊥ : Sublattice (forall i, π i)) = ⊥ :=
  ext fun a => by simpa [mem_pi] using! hs

/--
lemma `pi_univ_bot` / 引理 `pi_univ_bot`

English:
lemma pi_univ_bot
  given: [Nonempty κ]
  statement: (pi univ fun _ => ⊥ : Sublattice (forall i, π i)) = ⊥
  proof: by simp

中文:
引理 pi_univ_bot
  条件: [Nonempty κ]
  结论: (pi univ fun _ => ⊥ : Sublattice (对任意 i, π i)) = ⊥
  证明: by simp
-/
lemma pi_univ_bot [Nonempty κ] : (pi univ fun _ => ⊥ : Sublattice (forall i, π i)) = ⊥ := by simp

/--
lemma `le_pi` / 引理 `le_pi`

English:
lemma le_pi
  given: {s : Set κ} {L : forall i, Sublattice (π i)} {M : Sublattice (forall i, π i)}
  proof: by simp [SetLike.le_def]; grind

中文:
引理 le_pi
  条件: {s : Set κ} {L : 对任意 i, Sublattice (π i)} {M : Sublattice (对任意 i, π i)}
  证明: by simp [SetLike.le_def]; grind

Depends on / 依赖: SetLike, SetLike.le_def, le_def
-/
lemma le_pi {s : Set κ} {L : forall i, Sublattice (π i)} {M : Sublattice (forall i, π i)} :
    M <= pi s L ↔ forall i in s, M <= comap (Pi.evalLatticeHom i) (L i) := by simp [SetLike.le_def]; grind

/--
lemma `pi_univ_eq_bot_iff` / 引理 `pi_univ_eq_bot_iff`

English:
lemma pi_univ_eq_bot_iff
  given: {L : forall i, Sublattice (π i)}
  statement: pi univ L = ⊥ ↔ exists i, L i = ⊥
  proof: by
  simp_rw [← coe_inj]; simp

中文:
引理 pi_univ_eq_bot_iff
  条件: {L : 对任意 i, Sublattice (π i)}
  结论: pi univ L = ⊥ ↔ 存在 i, L i = ⊥
  证明: by
  simp_rw [← coe_inj]; simp
-/
@[simp] lemma pi_univ_eq_bot_iff {L : forall i, Sublattice (π i)} : pi univ L = ⊥ ↔ exists i, L i = ⊥ := by
  simp_rw [← coe_inj]; simp

/--
lemma `pi_univ_eq_bot` / 引理 `pi_univ_eq_bot`

English:
lemma pi_univ_eq_bot
  given: {L : forall i, Sublattice (π i)} {i : κ} (hL : L i = ⊥)
  statement: pi univ L = ⊥
  proof: pi_univ_eq_bot_iff.2 ⟨i, hL⟩

中文:
引理 pi_univ_eq_bot
  条件: {L : 对任意 i, Sublattice (π i)} {i : κ} (hL : L i = ⊥)
  结论: pi univ L = ⊥
  证明: pi_univ_eq_bot_iff.2 ⟨i, hL⟩

Depends on / 依赖: pi_univ_eq_bot_iff
-/
lemma pi_univ_eq_bot {L : forall i, Sublattice (π i)} {i : κ} (hL : L i = ⊥) : pi univ L = ⊥ :=
  pi_univ_eq_bot_iff.2 ⟨i, hL⟩

end Pi

namespace LatticeHom

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (f : LatticeHom α β)
  body: (Sublattice.map f ⊤).copy (Set.range f) image_univ.symm

中文:
定义 range
  签名: (f : LatticeHom α β)
  定义体: (Sublattice.map f ⊤).copy (Set.range f) image_univ.symm

Depends on / 依赖: Set.range, Sublattice, Sublattice.map, image_univ, image_univ.symm
-/
def range (f : LatticeHom α β) := (Sublattice.map f ⊤).copy (Set.range f) image_univ.symm

/--
lemma `range_coe` / 引理 `range_coe`

English:
lemma range_coe
  statement: (LatticeHom.range f : Set β) = Set.range f
  proof: rfl

中文:
引理 range_coe
  结论: (LatticeHom.range f : Set β) = Set.range f
  证明: rfl
-/
lemma range_coe : (LatticeHom.range f : Set β) = Set.range f := rfl

end LatticeHom

end Sublattice
