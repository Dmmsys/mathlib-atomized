/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.EquivFin

/-!
# fintype instance for `Set α`, when `α` is a fintype
-/

public section


variable {α : Type*}

open Finset

/--
Instance `Finset.fintype` / 实例 `Finset.fintype`

English:
instance Finset.fintype
  signature: [Fintype α]
  body: ⟨univ.powerset, fun _ => Finset.mem_powerset.2 (Finset.subset_univ _)⟩

@[simp]

中文:
实例 Finset.fintype
  签名: [Fintype α]
  定义体: ⟨univ.powerset, fun _ => Finset.mem_powerset.2 (Finset.subset_univ _)⟩

@[simp]

Depends on / 依赖: Finset, Finset.mem_powerset, Finset.subset_univ, mem_powerset, powerset, subset_univ, univ.powerset
-/
instance Finset.fintype [Fintype α] : Fintype (Finset α) :=
  ⟨univ.powerset, fun _ => Finset.mem_powerset.2 (Finset.subset_univ _)⟩

@[simp]
/--
theorem `Fintype.card_finset` / 定理 `Fintype.card_finset`

English:
theorem Fintype.card_finset
  given: [Fintype α]
  statement: Fintype.card (Finset α) = 2 ^ Fintype.card α
  proof: Finset.card_powerset Finset.univ

中文:
定理 Fintype.card_finset
  条件: [Fintype α]
  结论: Fintype.card (Finset α) = 2 ^ Fintype.card α
  证明: Finset.card_powerset Finset.univ

Depends on / 依赖: Finset, Finset.card_powerset, Finset.univ, card_powerset
-/
theorem Fintype.card_finset [Fintype α] : Fintype.card (Finset α) = 2 ^ Fintype.card α :=
  Finset.card_powerset Finset.univ

namespace Finset
variable [Fintype α] {s : Finset α} {k : Nat}

/--
lemma `powerset_univ` / 引理 `powerset_univ`

English:
lemma powerset_univ
  statement: (univ : Finset α).powerset = univ
  proof: coe_injective by simp [-coe_eq_univ]

中文:
引理 powerset_univ
  结论: (univ : Finset α).powerset = univ
  证明: coe_injective by simp [-coe_eq_univ]
-/
@[simp] lemma powerset_univ : (univ : Finset α).powerset = univ :=
coe_injective by simp [-coe_eq_univ]

/--
lemma `filter_subset_univ` / 引理 `filter_subset_univ`

English:
lemma filter_subset_univ
  given: [DecidableEq α] (s : Finset α)
  proof: by ext; simp

中文:
引理 filter_subset_univ
  条件: [DecidableEq α] (s : Finset α)
  证明: by ext; simp
-/
lemma filter_subset_univ [DecidableEq α] (s : Finset α) :
    ({t | t subseteq s} : Finset _) = powerset s := by ext; simp

/--
lemma `powerset_eq_univ` / 引理 `powerset_eq_univ`

English:
lemma powerset_eq_univ
  statement: s.powerset = univ ↔ s = univ
  proof: by
  rw [← Finset.powerset_univ]; rw [powerset_inj]

中文:
引理 powerset_eq_univ
  结论: s.powerset = univ ↔ s = univ
  证明: by
  rw [← Finset.powerset_univ]; rw [powerset_inj]
-/
@[simp] lemma powerset_eq_univ : s.powerset = univ ↔ s = univ := by
  rw [← Finset.powerset_univ]; rw [powerset_inj]

/--
lemma `mem_powersetCard_univ` / 引理 `mem_powersetCard_univ`

English:
lemma mem_powersetCard_univ
  statement: s in powersetCard k (univ : Finset α) ↔ #s = k
  proof: mem_powersetCard.trans and_iff_right subset_univ _

中文:
引理 mem_powersetCard_univ
  结论: s in powersetCard k (univ : Finset α) ↔ #s = k
  证明: mem_powersetCard.trans and_iff_right subset_univ _

Depends on / 依赖: and_iff_right, mem_powersetCard, mem_powersetCard.trans, subset_univ
-/
lemma mem_powersetCard_univ : s in powersetCard k (univ : Finset α) ↔ #s = k :=
mem_powersetCard.trans and_iff_right subset_univ _

variable (α)

/--
lemma `univ_filter_card_eq` / 引理 `univ_filter_card_eq`

English:
lemma univ_filter_card_eq
  given: (k : Nat)
  proof: by ext; simp

中文:
引理 univ_filter_card_eq
  条件: (k : 自然数)
  证明: by ext; simp
-/
@[simp] lemma univ_filter_card_eq (k : Nat) :
    ({s | #s = k} : Finset (Finset α)) = univ.powersetCard k := by ext; simp

end Finset

@[simp]
/--
theorem `Fintype.card_finset_len` / 定理 `Fintype.card_finset_len`

English:
theorem Fintype.card_finset_len
  given: [Fintype α] (k : Nat)
  proof: by
  simp [Fintype.subtype_card, Finset.card_univ]

中文:
定理 Fintype.card_finset_len
  条件: [Fintype α] (k : 自然数)
  证明: by
  simp [Fintype.subtype_card, Finset.card_univ]

Depends on / 依赖: Finset, Finset.card_univ, Fintype, Fintype.subtype_card, card_univ, subtype_card
-/
theorem Fintype.card_finset_len [Fintype α] (k : Nat) :
    Fintype.card { s : Finset α // #s = k } = Nat.choose (Fintype.card α) k := by
  simp [Fintype.subtype_card, Finset.card_univ]

/--
Instance `Set.fintype` / 实例 `Set.fintype`

English:
instance Set.fintype
  signature: [Fintype α]
  body: ⟨(@Finset.univ (Finset α) _).map coeEmb.1, fun s => by
    classical
    refine mem_map.2 ⟨({a | a in s} : Finset _), Finset.mem_univ _, (coe_filter _ _).trans ?_⟩
    simp⟩

中文:
实例 Set.fintype
  签名: [Fintype α]
  定义体: ⟨(@Finset.univ (Finset α) _).map coeEmb.1, fun s => by
    classical
    refine mem_map.2 ⟨({a | a in s} : Finset _), Finset.mem_univ _, (coe_filter _ _).trans ?_⟩
    simp⟩

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ, classical, coeEmb, coe_filter, mem_map, mem_univ
-/
instance Set.fintype [Fintype α] : Fintype (Set α) :=
  ⟨(@Finset.univ (Finset α) _).map coeEmb.1, fun s => by
    classical
    refine mem_map.2 ⟨({a | a in s} : Finset _), Finset.mem_univ _, (coe_filter _ _).trans ?_⟩
    simp⟩

-- Not to be confused with `Set.Finite`, the predicate
/--
Instance `Set.instFinite` / 实例 `Set.instFinite`

English:
instance Set.instFinite
  signature: [Finite α]
  body: by
  cases nonempty_fintype α
  infer_instance

@[simp]

中文:
实例 Set.instFinite
  签名: [Finite α]
  定义体: by
  cases nonempty_fintype α
  infer_instance

@[simp]

Depends on / 依赖: infer_instance, nonempty_fintype
-/
instance Set.instFinite [Finite α] : Finite (Set α) := by
  cases nonempty_fintype α
  infer_instance

@[simp]
/--
theorem `Fintype.card_set` / 定理 `Fintype.card_set`

English:
theorem Fintype.card_set
  given: [Fintype α]
  statement: Fintype.card (Set α) = 2 ^ Fintype.card α
  proof: (Finset.card_map _).trans (Finset.card_powerset _)

中文:
定理 Fintype.card_set
  条件: [Fintype α]
  结论: Fintype.card (Set α) = 2 ^ Fintype.card α
  证明: (Finset.card_map _).trans (Finset.card_powerset _)

Depends on / 依赖: Finset, Finset.card_map, Finset.card_powerset, card_map, card_powerset
-/
theorem Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α :=
  (Finset.card_map _).trans (Finset.card_powerset _)
