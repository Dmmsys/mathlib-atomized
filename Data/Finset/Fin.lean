/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Kim Morrison, Johan Commelin
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Embedding

/-!
# Finsets in `Fin n`

A few constructions for Finsets in `Fin n`.

## Main declarations

* `Finset.attachFin`: Turns a Finset of naturals strictly less than `n` into a `Finset (Fin n)`.
-/

@[expose] public section


variable {n : Nat}

namespace Finset

/--
Definition of `attachFin` / `attachFin` 的定义

English:
definition attachFin
  signature: (s : Finset Nat) {n : Nat} (h : forall m in s, m < n)
  body: ⟨s.1.pmap (fun a ha => ⟨a, ha⟩) h, s.nodup.pmap fun _ _ _ _ => Fin.val_eq_of_eq⟩

@[simp]

中文:
定义 attachFin
  签名: (s : 有限集 自然数) {n : 自然数} (h : 对任意 m in s, m < n)
  定义体: ⟨s.1.pmap (fun a ha => ⟨a, ha⟩) h, s.nodup.pmap fun _ _ _ _ => Fin.val_eq_of_eq⟩

@[simp]

Depends on / 依赖: Fin.val_eq_of_eq, s.nodup.pmap, val_eq_of_eq
-/
def attachFin (s : Finset Nat) {n : Nat} (h : forall m in s, m < n) : Finset (Fin n) :=
  ⟨s.1.pmap (fun a ha => ⟨a, ha⟩) h, s.nodup.pmap fun _ _ _ _ => Fin.val_eq_of_eq⟩

@[simp]
/--
theorem `mem_attachFin` / 定理 `mem_attachFin`

English:
theorem mem_attachFin
  given: {s : Finset Nat} (h : forall m in s, m < n) {a : Fin n}
  proof: ⟨fun h =>
    let ⟨_, hb₁, hb₂⟩ := Multiset.mem_pmap.1 h
    hb₂ ▸ hb₁,
    fun h => Multiset.mem_pmap.2 ⟨a, h, Fin.eta _ _⟩⟩

@[simp]

中文:
定理 mem_attachFin
  条件: {s : 有限集 自然数} (h : 对任意 m in s, m < n) {a : 有限集 n}
  证明: ⟨fun h =>
    let ⟨_, hb₁, hb₂⟩ := Multiset.mem_pmap.1 h
    hb₂ ▸ hb₁,
    fun h => Multiset.mem_pmap.2 ⟨a, h, Fin.eta _ _⟩⟩

@[simp]

Depends on / 依赖: Fin.eta, Multiset, Multiset.mem_pmap, mem_pmap
-/
theorem mem_attachFin {s : Finset Nat} (h : forall m in s, m < n) {a : Fin n} :
    a in s.attachFin h ↔ (a : Nat) in s :=
  ⟨fun h =>
    let ⟨_, hb₁, hb₂⟩ := Multiset.mem_pmap.1 h
    hb₂ ▸ hb₁,
    fun h => Multiset.mem_pmap.2 ⟨a, h, Fin.eta _ _⟩⟩

@[simp]
/--
lemma `coe_attachFin` / 引理 `coe_attachFin`

English:
lemma coe_attachFin
  given: {s : Finset Nat} (h : forall m in s, m < n)
  proof: by
  ext; simp

@[simp]

中文:
引理 coe_attachFin
  条件: {s : 有限集 自然数} (h : 对任意 m in s, m < n)
  证明: by
  ext; simp

@[simp]
-/
lemma coe_attachFin {s : Finset Nat} (h : forall m in s, m < n) :
    (attachFin s h : Set (Fin n)) = Fin.val ⁻¹' s := by
  ext; simp

@[simp]
/--
theorem `card_attachFin` / 定理 `card_attachFin`

English:
theorem card_attachFin
  given: (s : Finset Nat) (h : forall m in s, m < n)
  proof: Multiset.card_pmap _ _ _

@[simp]

中文:
定理 card_attachFin
  条件: (s : 有限集 自然数) (h : 对任意 m in s, m < n)
  证明: Multiset.card_pmap _ _ _

@[simp]

Depends on / 依赖: Multiset, Multiset.card_pmap, card_pmap
-/
theorem card_attachFin (s : Finset Nat) (h : forall m in s, m < n) :
    (s.attachFin h).card = s.card :=
  Multiset.card_pmap _ _ _

@[simp]
/--
lemma `image_val_attachFin` / 引理 `image_val_attachFin`

English:
lemma image_val_attachFin
  given: {s : Finset Nat} (h : forall m in s, m < n)
  proof: by
  apply coe_injective
  rw [coe_image]; rw [coe_attachFin]; rw [Set.image_preimage_eq_iff]
  exact fun m hm => ⟨⟨m, h m hm⟩, rfl⟩

@[simp]

中文:
引理 image_val_attachFin
  条件: {s : 有限集 自然数} (h : 对任意 m in s, m < n)
  证明: by
  apply coe_injective
  rw [coe_image]; rw [coe_attachFin]; rw [Set.image_preimage_eq_iff]
  exact fun m hm => ⟨⟨m, h m hm⟩, rfl⟩

@[simp]

Depends on / 依赖: Set.image_preimage_eq_iff, coe_attachFin, coe_image, coe_injective, image_preimage_eq_iff
-/
lemma image_val_attachFin {s : Finset Nat} (h : forall m in s, m < n) :
    image Fin.val (s.attachFin h) = s := by
  apply coe_injective
  rw [coe_image]; rw [coe_attachFin]; rw [Set.image_preimage_eq_iff]
  exact fun m hm => ⟨⟨m, h m hm⟩, rfl⟩

@[simp]
/--
lemma `map_valEmbedding_attachFin` / 引理 `map_valEmbedding_attachFin`

English:
lemma map_valEmbedding_attachFin
  given: {s : Finset Nat} (h : forall m in s, m < n)
  proof: by
  simp [map_eq_image]

@[simp]

中文:
引理 map_valEmbedding_attachFin
  条件: {s : 有限集 自然数} (h : 对任意 m in s, m < n)
  证明: by
  simp [map_eq_image]

@[simp]

Depends on / 依赖: map_eq_image
-/
lemma map_valEmbedding_attachFin {s : Finset Nat} (h : forall m in s, m < n) :
    map Fin.valEmbedding (s.attachFin h) = s := by
  simp [map_eq_image]

@[simp]
/--
lemma `attachFin_subset_attachFin_iff` / 引理 `attachFin_subset_attachFin_iff`

English:
lemma attachFin_subset_attachFin_iff
  given: {s t : Finset Nat} (hs : forall m in s, m < n) (ht : forall m in t, m < n)
  proof: by
  simp [← map_subset_map (f := Fin.valEmbedding)]

@[mono, gcongr]

中文:
引理 attachFin_subset_attachFin_iff
  条件: {s t : 有限集 自然数} (hs : 对任意 m in s, m < n) (ht : 对任意 m in t, m < n)
  证明: by
  simp [← map_subset_map (f := Fin.valEmbedding)]

@[mono, gcongr]

Depends on / 依赖: Fin.valEmbedding, map_subset_map, valEmbedding
-/
lemma attachFin_subset_attachFin_iff {s t : Finset Nat} (hs : forall m in s, m < n) (ht : forall m in t, m < n) :
    s.attachFin hs subseteq t.attachFin ht ↔ s subseteq t := by
  simp [← map_subset_map (f := Fin.valEmbedding)]

@[mono, gcongr]
/--
lemma `attachFin_subset_attachFin` / 引理 `attachFin_subset_attachFin`

English:
lemma attachFin_subset_attachFin
  given: {s t : Finset Nat} (hst : s subseteq t) (ht : forall m in t, m < n)
  proof: by simpa

@[simp]

中文:
引理 attachFin_subset_attachFin
  条件: {s t : 有限集 自然数} (hst : s subseteq t) (ht : 对任意 m in t, m < n)
  证明: by simpa

@[simp]
-/
lemma attachFin_subset_attachFin {s t : Finset Nat} (hst : s subseteq t) (ht : forall m in t, m < n) :
    s.attachFin (fun m hm => ht m (hst hm)) subseteq t.attachFin ht := by simpa

@[simp]
/--
lemma `attachFin_ssubset_attachFin_iff` / 引理 `attachFin_ssubset_attachFin_iff`

English:
lemma attachFin_ssubset_attachFin_iff
  given: {s t : Finset Nat} (hs : forall m in s, m < n) (ht : forall m in t, m < n)
  proof: by
  simp [← map_ssubset_map (f := Fin.valEmbedding)]

@[mono, gcongr]

中文:
引理 attachFin_ssubset_attachFin_iff
  条件: {s t : 有限集 自然数} (hs : 对任意 m in s, m < n) (ht : 对任意 m in t, m < n)
  证明: by
  simp [← map_ssubset_map (f := Fin.valEmbedding)]

@[mono, gcongr]

Depends on / 依赖: Fin.valEmbedding, map_ssubset_map, valEmbedding
-/
lemma attachFin_ssubset_attachFin_iff {s t : Finset Nat} (hs : forall m in s, m < n) (ht : forall m in t, m < n) :
    s.attachFin hs ⊂ t.attachFin ht ↔ s ⊂ t := by
  simp [← map_ssubset_map (f := Fin.valEmbedding)]

@[mono, gcongr]
/--
lemma `attachFin_ssubset_attachFin` / 引理 `attachFin_ssubset_attachFin`

English:
lemma attachFin_ssubset_attachFin
  given: {s t : Finset Nat} (hst : s ⊂ t) (ht : forall m in t, m < n)
  proof: by simpa

中文:
引理 attachFin_ssubset_attachFin
  条件: {s t : 有限集 自然数} (hst : s ⊂ t) (ht : 对任意 m in t, m < n)
  证明: by simpa
-/
lemma attachFin_ssubset_attachFin {s t : Finset Nat} (hst : s ⊂ t) (ht : forall m in t, m < n) :
    s.attachFin (fun m hm => ht m (hst.subset hm)) ⊂ t.attachFin ht := by simpa

end Finset
