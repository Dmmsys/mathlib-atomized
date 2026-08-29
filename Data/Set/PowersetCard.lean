/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.

* `Set.powersetCard α n` is the set of all `Finset α` with cardinality `n`.
  The name is chosen in relation with `Finset.powersetCard` which corresponds to
  the analogous structure for subsets of given cardinality of a given `Finset`, as a `Finset`.

* `Set.powersetCard.card` proves that the `Nat.card`-cardinality
  of this set is equal to `(Nat.card α).choose n`.

-/

@[expose] public section

variable (α : Type*)

/--
Definition of `Set.powersetCard` / `Set.powersetCard` 的定义

English:
definition Set.powersetCard
  signature: (n : Nat)
  body: {s : Finset α | s.card = n}

中文:
定义 Set.powersetCard
  签名: (n : 自然数)
  定义体: {s : Finset α | s.card = n}

Depends on / 依赖: Finset, s.card
-/
def Set.powersetCard (n : Nat) := {s : Finset α | s.card = n}

variable {α} {n : Nat}

namespace Set.powersetCard

open Finset Set Function

@[simp]
/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {s : Finset α}
  proof: by
  rw [powersetCard]; rw [Set.mem_ofPred_eq]

中文:
定理 mem_iff
  条件: {s : Finset α}
  证明: by
  rw [powersetCard]; rw [Set.mem_ofPred_eq]

Depends on / 依赖: Set.mem_ofPred_eq, mem_ofPred_eq, powersetCard
-/
theorem mem_iff {s : Finset α} :
    s in powersetCard α n ↔ s.card = n := by
  rw [powersetCard]; rw [Set.mem_ofPred_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (powersetCard α n) α
  body: SetLike.instSubtype

中文:
实例 :
  签名: SetLike (powersetCard α n) α
  定义体: SetLike.instSubtype

Depends on / 依赖: SetLike, SetLike.instSubtype, instSubtype
-/
instance : SetLike (powersetCard α n) α := SetLike.instSubtype

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Set.powersetCard α n)
  body: .ofSetLike (Set.powersetCard α n) α

@[simp]

中文:
实例 :
  签名: PartialOrder (Set.powersetCard α n)
  定义体: .ofSetLike (Set.powersetCard α n) α

@[simp]

Depends on / 依赖: Set.powersetCard, ofSetLike, powersetCard
-/
instance : PartialOrder (Set.powersetCard α n) := .ofSetLike (Set.powersetCard α n) α

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: {s : powersetCard α n}
  proof: rfl

中文:
定理 coe_coe
  条件: {s : powersetCard α n}
  证明: rfl
-/
theorem coe_coe {s : powersetCard α n} :
    ((s : Finset α) : Set α) = s := rfl

/--
theorem `mem_coe_iff` / 定理 `mem_coe_iff`

English:
theorem mem_coe_iff
  given: {s : Set.powersetCard α n} {a : α}
  statement: a in (s : Finset α) ↔ a in s
  proof: .rfl

@[simp]

中文:
定理 mem_coe_iff
  条件: {s : Set.powersetCard α n} {a : α}
  结论: a in (s : Finset α) ↔ a in s
  证明: .rfl

@[simp]
-/
theorem mem_coe_iff {s : Set.powersetCard α n} {a : α} : a in (s : Finset α) ↔ a in s := .rfl

@[simp]
/--
theorem `card_eq` / 定理 `card_eq`

English:
theorem card_eq
  given: (s : Set.powersetCard α n)
  statement: (s : Finset α).card = n
  proof: s.prop

@[simp]

中文:
定理 card_eq
  条件: (s : Set.powersetCard α n)
  结论: (s : Finset α).card = n
  证明: s.prop

@[simp]

Depends on / 依赖: s.prop
-/
theorem card_eq (s : Set.powersetCard α n) : (s : Finset α).card = n := s.prop

@[simp]
/--
theorem `ncard_eq` / 定理 `ncard_eq`

English:
theorem ncard_eq
  given: (s : Set.powersetCard α n)
  statement: (s : Set α).ncard = n
  proof: by
  rw [← coe_coe]; rw [Set.ncard_coe_finset]; rw [s.prop]

中文:
定理 ncard_eq
  条件: (s : Set.powersetCard α n)
  结论: (s : Set α).ncard = n
  证明: by
  rw [← coe_coe]; rw [Set.ncard_coe_finset]; rw [s.prop]

Depends on / 依赖: Set.ncard_coe_finset, coe_coe, ncard_coe_finset, s.prop
-/
theorem ncard_eq (s : Set.powersetCard α n) : (s : Set α).ncard = n := by
  rw [← coe_coe]; rw [Set.ncard_coe_finset]; rw [s.prop]

/--
theorem `coe_nonempty_iff` / 定理 `coe_nonempty_iff`

English:
theorem coe_nonempty_iff
  given: {s : Set.powersetCard α n}
  proof: by
  rw [← Set.powersetCard.coe_coe]; rw [Finset.coe_nonempty]; rw [← one_le_card]; rw [s.prop]

中文:
定理 coe_nonempty_iff
  条件: {s : Set.powersetCard α n}
  证明: by
  rw [← Set.powersetCard.coe_coe]; rw [Finset.coe_nonempty]; rw [← one_le_card]; rw [s.prop]

Depends on / 依赖: Finset, Finset.coe_nonempty, Set.powersetCard.coe_coe, coe_coe, coe_nonempty, one_le_card, powersetCard, s.prop
-/
theorem coe_nonempty_iff {s : Set.powersetCard α n} :
    (s : Set α).Nonempty ↔ 1 <= n := by
  rw [← Set.powersetCard.coe_coe]; rw [Finset.coe_nonempty]; rw [← one_le_card]; rw [s.prop]

/--
theorem `coe_nontrivial_iff` / 定理 `coe_nontrivial_iff`

English:
theorem coe_nontrivial_iff
  given: {s : Set.powersetCard α n}
  proof: by
  rw [← coe_coe]; rw [Finset.nontrivial_coe]; rw [← one_lt_card_iff_nontrivial]; rw [card_eq]

中文:
定理 coe_nontrivial_iff
  条件: {s : Set.powersetCard α n}
  证明: by
  rw [← coe_coe]; rw [Finset.nontrivial_coe]; rw [← one_lt_card_iff_nontrivial]; rw [card_eq]

Depends on / 依赖: Finset, Finset.nontrivial_coe, card_eq, coe_coe, nontrivial_coe, one_lt_card_iff_nontrivial
-/
theorem coe_nontrivial_iff {s : Set.powersetCard α n} :
    (s : Set α).Nontrivial ↔ 1 < n := by
  rw [← coe_coe]; rw [Finset.nontrivial_coe]; rw [← one_lt_card_iff_nontrivial]; rw [card_eq]

/--
theorem `eq_iff_subset` / 定理 `eq_iff_subset`

English:
theorem eq_iff_subset
  given: {s t : Set.powersetCard α n}
  statement: s = t ↔ (s : Finset α) subseteq (t : Finset α)
  proof: by
  rw [Finset.subset_iff_eq_of_card_le (t.prop.trans_le s.prop.ge)]; rw [Subtype.ext_iff]

中文:
定理 eq_iff_subset
  条件: {s t : Set.powersetCard α n}
  结论: s = t ↔ (s : Finset α) subseteq (t : Finset α)
  证明: by
  rw [Finset.subset_iff_eq_of_card_le (t.prop.trans_le s.prop.ge)]; rw [Subtype.ext_iff]

Depends on / 依赖: Finset, Finset.subset_iff_eq_of_card_le, Subtype, Subtype.ext_iff, ext_iff, s.prop.ge, subset_iff_eq_of_card_le, t.prop.trans_le, trans_le
-/
theorem eq_iff_subset {s t : Set.powersetCard α n} : s = t ↔ (s : Finset α) subseteq (t : Finset α) := by
  rw [Finset.subset_iff_eq_of_card_le (t.prop.trans_le s.prop.ge)]; rw [Subtype.ext_iff]

/--
theorem `exists_mem_notMem` / 定理 `exists_mem_notMem`

English:
theorem exists_mem_notMem
  given: (hn : 1 <= n) (hα : n < ENat.card α) {a b : α} (hab : a != b)
  proof: by
  have ha' : n <= Set.encard {b}ᶜ := by
    rwa [← (Set.encard_add_encard_compl {b}).trans (Set.encard_univ α), Set.encard_singleton,
      add_comm, ENat.lt_add_one_iff' (ENat.natCast_ne_top n)] at hα
  obtain ⟨s, has, has', hs⟩ :=
    Set.exists_superset_subset_encard_eq (s := {a}) (by simp [Ne

中文:
定理 exists_mem_notMem
  条件: (hn : 1 <= n) (hα : n < E自然数.card α) {a b : α} (hab : a != b)
  证明: by
  have ha' : n <= Set.encard {b}ᶜ := by
    rwa [← (Set.encard_add_encard_compl {b}).trans (Set.encard_univ α), Set.encard_singleton,
      add_comm, ENat.lt_add_one_iff' (ENat.natCast_ne_top n)] at hα
  obtain ⟨s, has, has', hs⟩ :=
    Set.exists_superset_subset_encard_eq (s := {a}) (by simp [Ne

Depends on / 依赖: ENat.lt_add_one_iff, ENat.natCast_inj, ENat.natCast_ne_top, Finite, Ne.symm, Set.Finite, Set.Finite.toFinset, Set.encard, Set.encard_add_encard_compl, Set.encard_singleton, Set.encard_univ, Set.exists_superset_subset_encard_eq, Set.finite_of_encard_eq_coe, add_comm, encard, encard_add_encard_compl, encard_eq_coe_toFinset_card, encard_singleton, encard_univ, exists_superset_subset_encard_eq
-/
theorem exists_mem_notMem (hn : 1 <= n) (hα : n < ENat.card α) {a b : α} (hab : a != b) :
    exists s : powersetCard α n, a in s ∧ b ∉ s := by
  have ha' : n <= Set.encard {b}ᶜ := by
    rwa [← (Set.encard_add_encard_compl {b}).trans (Set.encard_univ α), Set.encard_singleton,
      add_comm, ENat.lt_add_one_iff' (ENat.natCast_ne_top n)] at hα
  obtain ⟨s, has, has', hs⟩ :=
    Set.exists_superset_subset_encard_eq (s := {a}) (by simp [Ne.symm hab]) (by simpa) ha'
  have : Set.Finite s := Set.finite_of_encard_eq_coe hs
  exact ⟨⟨Set.Finite.toFinset this, by
    rwa [mem_iff, ← ENat.natCast_inj, ← this.encard_eq_coe_toFinset_card]⟩,
      by simpa using has, by simpa using has'⟩

/--
theorem `exists_mem_notMem_iff_ne` / 定理 `exists_mem_notMem_iff_ne`

English:
theorem exists_mem_notMem_iff_ne
  given: (s t : Set.powersetCard α n)
  statement: s != t ↔ exists a in s, a ∉ t
  proof: by
  contrapose!
  rw [eq_iff_subset]
  rfl

中文:
定理 exists_mem_notMem_iff_ne
  条件: (s t : Set.powersetCard α n)
  结论: s != t ↔ 存在 a in s, a ∉ t
  证明: by
  contrapose!
  rw [eq_iff_subset]
  rfl

Depends on / 依赖: contrapose, eq_iff_subset
-/
theorem exists_mem_notMem_iff_ne (s t : Set.powersetCard α n) : s != t ↔ exists a in s, a ∉ t := by
  contrapose!
  rw [eq_iff_subset]
  rfl

section map

variable (n) {β : Type*}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α ↪ β) (s : powersetCard α n)
  body: ⟨Finset.map f s, by rw [mem_iff, card_map, s.prop]⟩

中文:
定义 map
  签名: (f : α ↪ β) (s : powersetCard α n)
  定义体: ⟨Finset.map f s, by rw [mem_iff, card_map, s.prop]⟩

Depends on / 依赖: Finset, Finset.map, card_map, mem_iff, s.prop
-/
def map (f : α ↪ β) (s : powersetCard α n) : powersetCard β n :=
    ⟨Finset.map f s, by rw [mem_iff, card_map, s.prop]⟩

/--
lemma `mem_map_iff_mem_range` / 引理 `mem_map_iff_mem_range`

English:
lemma mem_map_iff_mem_range
  given: (f : α ↪ β) (s : powersetCard α n) (b : β)
  proof: by
  simp [map]
  rfl

@[simp]

中文:
引理 mem_map_iff_mem_range
  条件: (f : α ↪ β) (s : powersetCard α n) (b : β)
  证明: by
  simp [map]
  rfl

@[simp]
-/
lemma mem_map_iff_mem_range (f : α ↪ β) (s : powersetCard α n) (b : β) :
    b in map n f s ↔ b in f '' s := by
  simp [map]
  rfl

@[simp]
/--
lemma `coe_map` / 引理 `coe_map`

English:
lemma coe_map
  given: (f : α ↪ β) (s : powersetCard α n)
  statement: SetLike.coe (map n f s) = f '' s
  proof: by
  ext
  simp [mem_map_iff_mem_range]

@[simp]

中文:
引理 coe_map
  条件: (f : α ↪ β) (s : powersetCard α n)
  结论: SetLike.coe (map n f s) = f '' s
  证明: by
  ext
  simp [mem_map_iff_mem_range]

@[simp]

Depends on / 依赖: mem_map_iff_mem_range
-/
lemma coe_map (f : α ↪ β) (s : powersetCard α n) : SetLike.coe (map n f s) = f '' s := by
  ext
  simp [mem_map_iff_mem_range]

@[simp]
/--
lemma `val_map` / 引理 `val_map`

English:
lemma val_map
  given: (f : α ↪ β) (s : powersetCard α n)
  statement: Subtype.val (map n f s) = s.val.map f
  proof: rfl

中文:
引理 val_map
  条件: (f : α ↪ β) (s : powersetCard α n)
  结论: Subtype.val (map n f s) = s.val.map f
  证明: rfl
-/
lemma val_map (f : α ↪ β) (s : powersetCard α n) : Subtype.val (map n f s) = s.val.map f := rfl

end map

section of

/--
Definition of `ofCard` / `ofCard` 的定义

English:
definition ofCard
  signature: {s : Finset α} (s_card : s.card = n)
  body: ⟨s, mem_iff.mpr s_card⟩

@[simp]

中文:
定义 ofCard
  签名: {s : Finset α} (s_card : s.card = n)
  定义体: ⟨s, mem_iff.mpr s_card⟩

@[simp]

Depends on / 依赖: mem_iff, mem_iff.mpr, s_card
-/
def ofCard {s : Finset α} (s_card : s.card = n) : powersetCard α n := ⟨s, mem_iff.mpr s_card⟩

@[simp]
/--
lemma `val_ofCard` / 引理 `val_ofCard`

English:
lemma val_ofCard
  given: {s : Finset α} (s_card : s.card = n)
  statement: Subtype.val (ofCard s_card) = s
  proof: rfl

@[simp]

中文:
引理 val_ofCard
  条件: {s : Finset α} (s_card : s.card = n)
  结论: Subtype.val (ofCard s_card) = s
  证明: rfl

@[simp]
-/
lemma val_ofCard {s : Finset α} (s_card : s.card = n) : Subtype.val (ofCard s_card) = s := rfl

@[simp]
/--
lemma `ofCard_coe` / 引理 `ofCard_coe`

English:
lemma ofCard_coe
  given: {s : powersetCard α n} (h)
  statement: ofCard (s := s.val) h = s
  proof: rfl

中文:
引理 ofCard_coe
  条件: {s : powersetCard α n} (h)
  结论: ofCard (s := s.val) h = s
  证明: rfl

Depends on / 依赖: s.val
-/
lemma ofCard_coe {s : powersetCard α n} (h) : ofCard (s := s.val) h = s := rfl

/--
Definition of `ofSingleton` / `ofSingleton` 的定义

English:
definition ofSingleton
  signature: : α ≃ powersetCard α 1 where
  body: ⟨{a}, Finset.card_singleton a⟩
  invFun s := (Finset.card_eq_one.mp s.prop).choose
  left_inv a := by simp
  right_inv s := by rw [← Subtype.val_inj, (Finset.card_eq_one.mp s.prop).choose_spec]

中文:
定义 ofSingleton
  签名: : α ≃ powersetCard α 1 where
  定义体: ⟨{a}, Finset.card_singleton a⟩
  invFun s := (Finset.card_eq_one.mp s.prop).choose
  left_inv a := by simp
  right_inv s := by rw [← Subtype.val_inj, (Finset.card_eq_one.mp s.prop).choose_spec]

Depends on / 依赖: Finset, Finset.card_singleton, card_singleton
-/
noncomputable def ofSingleton : α ≃ powersetCard α 1 where
  toFun a := ⟨{a}, Finset.card_singleton a⟩
  invFun s := (Finset.card_eq_one.mp s.prop).choose
  left_inv a := by simp
  right_inv s := by rw [← Subtype.val_inj, (Finset.card_eq_one.mp s.prop).choose_spec]

variable (n) (β : Type*)

/--
Definition of `ofFinEmb` / `ofFinEmb` 的定义

English:
definition ofFinEmb
  signature: (f : Fin n ↪ β)
  body: map n f ⟨Finset.univ, by rw [mem_iff, Finset.card_univ, Fintype.card_fin]⟩

@[simp]

中文:
定义 ofFinEmb
  签名: (f : Fin n ↪ β)
  定义体: map n f ⟨Finset.univ, by rw [mem_iff, Finset.card_univ, Fintype.card_fin]⟩

@[simp]

Depends on / 依赖: Finset, Finset.card_univ, Finset.univ, Fintype, Fintype.card_fin, card_fin, card_univ, mem_iff
-/
def ofFinEmb (f : Fin n ↪ β) : powersetCard β n :=
  map n f ⟨Finset.univ, by rw [mem_iff, Finset.card_univ, Fintype.card_fin]⟩

@[simp]
/--
lemma `mem_ofFinEmb_iff_mem_range` / 引理 `mem_ofFinEmb_iff_mem_range`

English:
lemma mem_ofFinEmb_iff_mem_range
  given: (f : Fin n ↪ β) (b : β)
  proof: by
  simp [ofFinEmb, mem_map_iff_mem_range]

@[simp]

中文:
引理 mem_ofFinEmb_iff_mem_range
  条件: (f : Fin n ↪ β) (b : β)
  证明: by
  simp [ofFinEmb, mem_map_iff_mem_range]

@[simp]

Depends on / 依赖: mem_map_iff_mem_range, ofFinEmb
-/
lemma mem_ofFinEmb_iff_mem_range (f : Fin n ↪ β) (b : β) :
    b in ofFinEmb n β f ↔ b in Set.range f := by
  simp [ofFinEmb, mem_map_iff_mem_range]

@[simp]
/--
lemma `coe_ofFinEmb` / 引理 `coe_ofFinEmb`

English:
lemma coe_ofFinEmb
  given: (f : Fin n ↪ β)
  statement: SetLike.coe (ofFinEmb n β f) = Set.range f
  proof: by
  ext
  simp [mem_ofFinEmb_iff_mem_range]

@[simp]

中文:
引理 coe_ofFinEmb
  条件: (f : Fin n ↪ β)
  结论: SetLike.coe (ofFinEmb n β f) = Set.range f
  证明: by
  ext
  simp [mem_ofFinEmb_iff_mem_range]

@[simp]

Depends on / 依赖: mem_ofFinEmb_iff_mem_range
-/
lemma coe_ofFinEmb (f : Fin n ↪ β) : SetLike.coe (ofFinEmb n β f) = Set.range f := by
  ext
  simp [mem_ofFinEmb_iff_mem_range]

@[simp]
/--
lemma `val_ofFinEmb` / 引理 `val_ofFinEmb`

English:
lemma val_ofFinEmb
  given: (f : Fin n ↪ β)
  proof: by
  simp [← coe_inj, coe_ofFinEmb]

中文:
引理 val_ofFinEmb
  条件: (f : Fin n ↪ β)
  证明: by
  simp [← coe_inj, coe_ofFinEmb]

Depends on / 依赖: coe_inj, coe_ofFinEmb
-/
lemma val_ofFinEmb (f : Fin n ↪ β) :
    Subtype.val (ofFinEmb n β f) = Finset.univ.map f := by
  simp [← coe_inj, coe_ofFinEmb]

/--
theorem `ofFinEmb_surjective` / 定理 `ofFinEmb_surjective`

English:
theorem ofFinEmb_surjective
  proof: by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ β, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

中文:
定理 ofFinEmb_surjective
  证明: by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ β, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

Depends on / 依赖: Embedding, Fintype, Fintype.card_fin, Function, Function.Embedding.exists_of_card_eq_finset, Subtype, Subtype.ext, card_fin, exists_of_card_eq_finset
-/
theorem ofFinEmb_surjective :
    Function.Surjective (ofFinEmb n β) := by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ β, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

end of

section compl

variable [DecidableEq α] [Fintype α] {m : Nat} (hm : m + n = Fintype.card α)

/--
Definition of `compl` / `compl` 的定义

English:
definition compl
  signature: : powersetCard α n ≃ powersetCard α m where
  body: ⟨(sᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp s.2]; omega⟩
  invFun t := ⟨(tᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp t.2]; omega⟩
  left_inv s := by simp
  right_inv t := by simp

中文:
定义 compl
  签名: : powersetCard α n ≃ powersetCard α m where
  定义体: ⟨(sᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp s.2]; omega⟩
  invFun t := ⟨(tᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp t.2]; omega⟩
  left_inv s := by simp
  right_inv t := by simp

Depends on / 依赖: Finset, Finset.card_compl, card_compl, mem_iff, mem_iff.mp
-/
def compl : powersetCard α n ≃ powersetCard α m where
  toFun s := ⟨(sᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp s.2]; omega⟩
  invFun t := ⟨(tᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp t.2]; omega⟩
  left_inv s := by simp
  right_inv t := by simp

variable {hm}

@[simp]
/--
theorem `coe_compl` / 定理 `coe_compl`

English:
theorem coe_compl
  given: {s : powersetCard α n}
  proof: rfl

@[simp]

中文:
定理 coe_compl
  条件: {s : powersetCard α n}
  证明: rfl

@[simp]
-/
theorem coe_compl {s : powersetCard α n} :
    (compl hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

@[simp]
/--
theorem `mem_compl` / 定理 `mem_compl`

English:
theorem mem_compl
  given: {s : powersetCard α n} {a : α}
  proof: Finset.mem_compl

中文:
定理 mem_compl
  条件: {s : powersetCard α n} {a : α}
  证明: Finset.mem_compl

Depends on / 依赖: Finset, Finset.mem_compl, mem_compl
-/
theorem mem_compl {s : powersetCard α n} {a : α} :
    a in compl hm s ↔ a ∉ s :=
  Finset.mem_compl

/--
theorem `compl_symm` / 定理 `compl_symm`

English:
theorem compl_symm
  statement: (compl hm).symm = compl ((n.add_comm m).trans hm)
  proof: rfl

中文:
定理 compl_symm
  结论: (compl hm).symm = compl ((n.add_comm m).trans hm)
  证明: rfl
-/
theorem compl_symm : (compl hm).symm = compl ((n.add_comm m).trans hm) := rfl

end compl

section disjUnion

variable {m : Nat} {s : powersetCard α m} {t : powersetCard α n} (hst : Disjoint s.val t.val)

/--
Definition of `disjUnion` / `disjUnion` 的定义

English:
definition disjUnion
  signature: : powersetCard α (m + n)
  body: ⟨s.val.disjUnion t hst, by rw [mem_iff, Finset.card_disjUnion, card_eq s, card_eq t]⟩

中文:
定义 disjUnion
  签名: : powersetCard α (m + n)
  定义体: ⟨s.val.disjUnion t hst, by rw [mem_iff, Finset.card_disjUnion, card_eq s, card_eq t]⟩

Depends on / 依赖: Finset, Finset.card_disjUnion, card_disjUnion, card_eq, disjUnion, mem_iff, s.val.disjUnion
-/
def disjUnion : powersetCard α (m + n) :=
  ⟨s.val.disjUnion t hst, by rw [mem_iff, Finset.card_disjUnion, card_eq s, card_eq t]⟩

variable {hst}

@[simp]
/--
theorem `coe_disjUnion` / 定理 `coe_disjUnion`

English:
theorem coe_disjUnion
  statement: (disjUnion hst : Finset α) = s.val.disjUnion t hst
  proof: rfl

@[simp]

中文:
定理 coe_disjUnion
  结论: (disjUnion hst : Finset α) = s.val.disjUnion t hst
  证明: rfl

@[simp]
-/
theorem coe_disjUnion : (disjUnion hst : Finset α) = s.val.disjUnion t hst := rfl

@[simp]
/--
theorem `mem_disjUnion` / 定理 `mem_disjUnion`

English:
theorem mem_disjUnion
  given: {a : α}
  statement: a in disjUnion hst ↔ a in s ∨ a in t
  proof: Finset.mem_disjUnion (h := hst)

中文:
定理 mem_disjUnion
  条件: {a : α}
  结论: a in disjUnion hst ↔ a in s ∨ a in t
  证明: Finset.mem_disjUnion (h := hst)

Depends on / 依赖: Finset, Finset.mem_disjUnion, mem_disjUnion
-/
theorem mem_disjUnion {a : α} : a in disjUnion hst ↔ a in s ∨ a in t :=
  Finset.mem_disjUnion (h := hst)

end disjUnion

variable (α n)

/--
theorem `coe_finset` / 定理 `coe_finset`

English:
theorem coe_finset
  given: [Fintype α]
  proof: by
  ext; simp

中文:
定理 coe_finset
  条件: [Fintype α]
  证明: by
  ext; simp
-/
theorem coe_finset [Fintype α] :
    powersetCard α n = Finset.powersetCard n (Finset.univ : Finset α) := by
  ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: α] : Fintype (powersetCard α n)
  body: by
  rw [coe_finset]
  infer_instance

中文:
实例 [Fintype
  签名: α] : Fintype (powersetCard α n)
  定义体: by
  rw [coe_finset]
  infer_instance

Depends on / 依赖: coe_finset, infer_instance
-/
instance [Fintype α] : Fintype (powersetCard α n) := by
  rw [coe_finset]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] : Finite (powersetCard α n)
  body: by
  have : Fintype α := Fintype.ofFinite α
  simpa [coe_finset] using Subtype.finite

中文:
实例 [Finite
  签名: α] : Finite (powersetCard α n)
  定义体: by
  have : Fintype α := Fintype.ofFinite α
  simpa [coe_finset] using Subtype.finite

Depends on / 依赖: Fintype, Fintype.ofFinite, Subtype, Subtype.finite, coe_finset, finite, ofFinite
-/
instance [Finite α] : Finite (powersetCard α n) := by
  have : Fintype α := Fintype.ofFinite α
  simpa [coe_finset] using Subtype.finite

/--
lemma `exist_mem_powersetCard_of_inf` / 引理 `exist_mem_powersetCard_of_inf`

English:
lemma exist_mem_powersetCard_of_inf
  given: (h : 0 < n) [Infinite α] (a : α)
  proof: by
  obtain ⟨s, a_mem, s_card⟩ := Infinite.exists_superset_card_eq ({a} : Finset α) n
    (by rw [Finset.card_singleton]; exact h)
  use ↑s
  exact ⟨mem_iff.mp s_card, by simpa using a_mem⟩

中文:
引理 exist_mem_powersetCard_of_inf
  条件: (h : 0 < n) [Infinite α] (a : α)
  证明: by
  obtain ⟨s, a_mem, s_card⟩ := Infinite.exists_superset_card_eq ({a} : Finset α) n
    (by rw [Finset.card_singleton]; exact h)
  use ↑s
  exact ⟨mem_iff.mp s_card, by simpa using a_mem⟩

Depends on / 依赖: Finset, Finset.card_singleton, Infinite, Infinite.exists_superset_card_eq, a_mem, card_singleton, exists_superset_card_eq, mem_iff, mem_iff.mp, s_card
-/
lemma exist_mem_powersetCard_of_inf (h : 0 < n) [Infinite α] (a : α) :
    exists s in powersetCard α n, a in s := by
  obtain ⟨s, a_mem, s_card⟩ := Infinite.exists_superset_card_eq ({a} : Finset α) n
    (by rw [Finset.card_singleton]; exact h)
  use ↑s
  exact ⟨mem_iff.mp s_card, by simpa using a_mem⟩

/--
Instance `instInfinite` / 实例 `instInfinite`

English:
instance instInfinite
  signature: [NeZero n] [Infinite α]
  body: by
  rw [← not_finite_iff_infinite]
  by_contra finite
  suffices ⋃₀ (SetLike.coe '' powersetCard α n) = Set.univ by
    apply Finite.false (α := α)
    rw [← Set.finite_univ_iff]; rw [← this]
    apply Set.Finite.sUnion (Finite.image SetLike.coe finite)
    aesop
  rw [sUnion_eq_univ_iff]
  intro a

中文:
实例 instInfinite
  签名: [NeZero n] [Infinite α]
  定义体: by
  rw [← not_finite_iff_infinite]
  by_contra finite
  suffices ⋃₀ (SetLike.coe '' powersetCard α n) = Set.univ by
    apply Finite.false (α := α)
    rw [← Set.finite_univ_iff]; rw [← this]
    apply Set.Finite.sUnion (Finite.image SetLike.coe finite)
    aesop
  rw [sUnion_eq_univ_iff]
  intro a

Depends on / 依赖: Finite, Finite.false, Finite.image, Nat.pos_of_neZero, Set.Finite.sUnion, Set.finite_univ_iff, Set.univ, SetLike, SetLike.coe, exist_mem_powersetCard_of_inf, finite, finite_univ_iff, mem_coe, mem_coe.mpr, mem_image_of_mem, mem_s, not_finite_iff_infinite, pos_of_neZero, powersetCard, sUnion
-/
instance instInfinite [NeZero n] [Infinite α] : Infinite (powersetCard α n) := by
  rw [← not_finite_iff_infinite]
  by_contra finite
  suffices ⋃₀ (SetLike.coe '' powersetCard α n) = Set.univ by
    apply Finite.false (α := α)
    rw [← Set.finite_univ_iff]; rw [← this]
    apply Set.Finite.sUnion (Finite.image SetLike.coe finite)
    aesop
  rw [sUnion_eq_univ_iff]
  intro a
  obtain ⟨s, s_mem, mem_s⟩ := exist_mem_powersetCard_of_inf α n (Nat.pos_of_neZero n) a
  exact ⟨↑s, mem_image_of_mem SetLike.coe s_mem, mem_coe.mpr mem_s⟩

/--
theorem `card` / 定理 `card`

English:
theorem card
  proof: by
  cases fintypeOrInfinite α
  · simp [coe_finset]
  · rcases n with _ | n
    · simp [powersetCard]
    · rw [Nat.card_eq_zero_of_infinite (α := α), Nat.choose_zero_succ]
      exact Nat.card_eq_zero_of_infinite

中文:
定理 card
  证明: by
  cases fintypeOrInfinite α
  · simp [coe_finset]
  · rcases n with _ | n
    · simp [powersetCard]
    · rw [Nat.card_eq_zero_of_infinite (α := α), Nat.choose_zero_succ]
      exact Nat.card_eq_zero_of_infinite
-/
protected theorem card :
    Nat.card (powersetCard α n) = (Nat.card α).choose n := by
  cases fintypeOrInfinite α
  · simp [coe_finset]
  · rcases n with _ | n
    · simp [powersetCard]
    · rw [Nat.card_eq_zero_of_infinite (α := α), Nat.choose_zero_succ]
      exact Nat.card_eq_zero_of_infinite

variable {α n}

/--
theorem `nontrivial` / 定理 `nontrivial`

English:
theorem nontrivial
  given: (h1 : 0 < n) (h2 : n < ENat.card α)
  proof: by
  cases fintypeOrInfinite α
  · rw [Set.nontrivial_coe_sort, ← Set.one_lt_ncard_iff_nontrivial, ← Nat.card_coe_set_eq,
      powersetCard.card]
    by_contra!
    rw [Nat.le_one_iff_eq_zero_or_eq_one] at this
    rw [ENat.card_eq_coe_natCard] at h2
    norm_cast at h2
    rcases this with h | h
 

中文:
定理 nontrivial
  条件: (h1 : 0 < n) (h2 : n < E自然数.card α)
  证明: by
  cases fintypeOrInfinite α
  · rw [Set.nontrivial_coe_sort, ← Set.one_lt_ncard_iff_nontrivial, ← Nat.card_coe_set_eq,
      powersetCard.card]
    by_contra!
    rw [Nat.le_one_iff_eq_zero_or_eq_one] at this
    rw [ENat.card_eq_coe_natCard] at h2
    norm_cast at h2
    rcases this with h | h
 

Depends on / 依赖: ENat.card_eq_coe_natCard, Nat.card_coe_set_eq, Nat.choose_eq_one_iff, Nat.choose_eq_zero_iff, Nat.le_one_iff_eq_zero_or_eq_one, NeZero, NeZero.of_pos, Set.nontrivial_coe_sort, Set.one_lt_ncard_iff_nontrivial, card_coe_set_eq, card_eq_coe_natCard, choose_eq_one_iff, choose_eq_zero_iff, fintypeOrInfinite, infer_instance, le_one_iff_eq_zero_or_eq_one, lt_self_iff_false, lt_trans, nontrivial_coe_sort, of_pos
-/
theorem nontrivial (h1 : 0 < n) (h2 : n < ENat.card α) :
    Nontrivial (powersetCard α n) := by
  cases fintypeOrInfinite α
  · rw [Set.nontrivial_coe_sort, ← Set.one_lt_ncard_iff_nontrivial, ← Nat.card_coe_set_eq,
      powersetCard.card]
    by_contra!
    rw [Nat.le_one_iff_eq_zero_or_eq_one] at this
    rw [ENat.card_eq_coe_natCard] at h2
    norm_cast at h2
    rcases this with h | h
    · rw [Nat.choose_eq_zero_iff] at h
      exact (lt_self_iff_false n).mp (lt_trans h2 h)
    · rw [Nat.choose_eq_one_iff] at h
      aesop
  · have : NeZero n := NeZero.of_pos h1
    infer_instance

/--
theorem `nontrivial'` / 定理 `nontrivial'`

English:
theorem nontrivial'
  given: (h1 : 0 < n) (h2 : n < Nat.card α)
  proof: by
  have : Finite α := Nat.finite_of_card_ne_zero (ne_zero_of_lt h2)
  apply nontrivial h1
  simp [ENat.card_eq_coe_natCard α, h2]

@[simp]

中文:
定理 nontrivial'
  条件: (h1 : 0 < n) (h2 : n < 自然数.card α)
  证明: by
  have : Finite α := Nat.finite_of_card_ne_zero (ne_zero_of_lt h2)
  apply nontrivial h1
  simp [ENat.card_eq_coe_natCard α, h2]

@[simp]

Depends on / 依赖: ENat.card_eq_coe_natCard, Finite, Nat.finite_of_card_ne_zero, card_eq_coe_natCard, finite_of_card_ne_zero, ne_zero_of_lt, nontrivial
-/
theorem nontrivial' (h1 : 0 < n) (h2 : n < Nat.card α) :
    Nontrivial (powersetCard α n) := by
  have : Finite α := Nat.finite_of_card_ne_zero (ne_zero_of_lt h2)
  apply nontrivial h1
  simp [ENat.card_eq_coe_natCard α, h2]

@[simp]
/--
theorem `eq_empty_iff` / 定理 `eq_empty_iff`

English:
theorem eq_empty_iff
  given: [Finite α]
  proof: by
  rw [← Set.ncard_eq_zero]; rw [← _root_.Nat.card_coe_set_eq]; rw [powersetCard.card]; rw [Nat.choose_eq_zero_iff]

中文:
定理 eq_empty_iff
  条件: [Finite α]
  证明: by
  rw [← Set.ncard_eq_zero]; rw [← _root_.Nat.card_coe_set_eq]; rw [powersetCard.card]; rw [Nat.choose_eq_zero_iff]

Depends on / 依赖: Nat.choose_eq_zero_iff, Set.ncard_eq_zero, _root_, _root_.Nat.card_coe_set_eq, card_coe_set_eq, choose_eq_zero_iff, ncard_eq_zero, powersetCard, powersetCard.card
-/
theorem eq_empty_iff [Finite α] :
    powersetCard α n = ∅ ↔ Nat.card α < n := by
  rw [← Set.ncard_eq_zero]; rw [← _root_.Nat.card_coe_set_eq]; rw [powersetCard.card]; rw [Nat.choose_eq_zero_iff]

/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  given: [Finite α]
  proof: by
  rw [← Finite.one_lt_card_iff_nontrivial]; rw [powersetCard.card]; rw [Nat.one_lt_iff_ne_zero_and_ne_one]; rw [ne_eq]; rw [Nat.choose_eq_zero_iff]; rw [ne_eq]; rw [Nat.choose_eq_one_iff]
  grind

中文:
定理 nontrivial_iff
  条件: [Finite α]
  证明: by
  rw [← Finite.one_lt_card_iff_nontrivial]; rw [powersetCard.card]; rw [Nat.one_lt_iff_ne_zero_and_ne_one]; rw [ne_eq]; rw [Nat.choose_eq_zero_iff]; rw [ne_eq]; rw [Nat.choose_eq_one_iff]
  grind

Depends on / 依赖: Finite, Finite.one_lt_card_iff_nontrivial, Nat.choose_eq_one_iff, Nat.choose_eq_zero_iff, Nat.one_lt_iff_ne_zero_and_ne_one, choose_eq_one_iff, choose_eq_zero_iff, ne_eq, one_lt_card_iff_nontrivial, one_lt_iff_ne_zero_and_ne_one, powersetCard, powersetCard.card
-/
theorem nontrivial_iff [Finite α] :
    Nontrivial (powersetCard α n) ↔ 0 < n ∧ n < Nat.card α := by
  rw [← Finite.one_lt_card_iff_nontrivial]; rw [powersetCard.card]; rw [Nat.one_lt_iff_ne_zero_and_ne_one]; rw [ne_eq]; rw [Nat.choose_eq_zero_iff]; rw [ne_eq]; rw [Nat.choose_eq_one_iff]
  grind

/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : (n : Nat) × (powersetCard α n) ≃ Finset α where
  body: x.2
  invFun x := ⟨x.card, ⟨x, rfl⟩⟩
  left_inv x := by ext <;> simp

@[simp]

中文:
定义 prodEquiv
  签名: : (n : 自然数) × (powersetCard α n) ≃ Finset α where
  定义体: x.2
  invFun x := ⟨x.card, ⟨x, rfl⟩⟩
  left_inv x := by ext <;> simp

@[simp]
-/
def prodEquiv : (n : Nat) × (powersetCard α n) ≃ Finset α where
  toFun x := x.2
  invFun x := ⟨x.card, ⟨x, rfl⟩⟩
  left_inv x := by ext <;> simp

@[simp]
/--
lemma `prodEquiv_apply` / 引理 `prodEquiv_apply`

English:
lemma prodEquiv_apply
  given: (x : (n : Nat) × (powersetCard α n))
  statement: prodEquiv x = x.2
  proof: rfl

@[simp]

中文:
引理 prodEquiv_apply
  条件: (x : (n : 自然数) × (powersetCard α n))
  结论: prodEquiv x = x.2
  证明: rfl

@[simp]
-/
lemma prodEquiv_apply (x : (n : Nat) × (powersetCard α n)) : prodEquiv x = x.2 := rfl

@[simp]
/--
lemma `prodEquiv_symm_apply` / 引理 `prodEquiv_symm_apply`

English:
lemma prodEquiv_symm_apply
  given: (s : Finset α)
  statement: prodEquiv.symm s = ⟨s.card, ofCard rfl⟩
  proof: rfl

中文:
引理 prodEquiv_symm_apply
  条件: (s : Finset α)
  结论: prodEquiv.symm s = ⟨s.card, ofCard rfl⟩
  证明: rfl
-/
lemma prodEquiv_symm_apply (s : Finset α) : prodEquiv.symm s = ⟨s.card, ofCard rfl⟩ := rfl

end Set.powersetCard
