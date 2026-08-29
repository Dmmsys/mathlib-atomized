/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Union
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Data.Set.Pairwise.Lattice

/-!
# The powerset of a finset
-/

@[expose] public section


namespace Finset

open Function Multiset

variable {α : Type*} {s t : Finset α}

/-! ### powerset -/


section Powerset

/--
Definition of `powerset` / `powerset` 的定义

English:
definition powerset
  signature: (s : Finset α)
  body: ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩

@[simp, grind =]

中文:
定义 powerset
  签名: (s : 有限集 α)
  定义体: ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩

@[simp, grind =]

Depends on / 依赖: Finset, Finset.mk, Finset.val, congr_arg, mem_powerset, nodup_of_le, powerset, powerset.pmap, s.nodup, s.nodup.powerset.pmap
-/
def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩

@[simp, grind =]
/--
theorem `mem_powerset` / 定理 `mem_powerset`

English:
theorem mem_powerset
  given: {s t : Finset α}
  statement: s in powerset t ↔ s subseteq t
  proof: by
  cases s
  simp [powerset, mem_mk, mem_pmap, mk.injEq, exists_prop, exists_eq_right,
    ← val_le_iff]

@[simp, norm_cast]

中文:
定理 mem_powerset
  条件: {s t : 有限集 α}
  结论: s in powerset t ↔ s subseteq t
  证明: by
  cases s
  simp [powerset, mem_mk, mem_pmap, mk.injEq, exists_prop, exists_eq_right,
    ← val_le_iff]

@[simp, norm_cast]

Depends on / 依赖: exists_eq_right, exists_prop, mem_mk, mem_pmap, mk.injEq, powerset, val_le_iff
-/
theorem mem_powerset {s t : Finset α} : s in powerset t ↔ s subseteq t := by
  cases s
  simp [powerset, mem_mk, mem_pmap, mk.injEq, exists_prop, exists_eq_right,
    ← val_le_iff]

@[simp, norm_cast]
/--
theorem `coe_powerset` / 定理 `coe_powerset`

English:
theorem coe_powerset
  given: (s : Finset α)
  proof: by
  ext
  simp

中文:
定理 coe_powerset
  条件: (s : 有限集 α)
  证明: by
  ext
  simp
-/
theorem coe_powerset (s : Finset α) :
    (s.powerset : Set (Finset α)) = ((↑) : Finset α -> Set α) ⁻¹' (s : Set α).powerset := by
  ext
  simp

/--
theorem `empty_mem_powerset` / 定理 `empty_mem_powerset`

English:
theorem empty_mem_powerset
  given: (s : Finset α)
  statement: ∅ in powerset s
  proof: by simp

中文:
定理 empty_mem_powerset
  条件: (s : 有限集 α)
  结论: ∅ in powerset s
  证明: by simp
-/
theorem empty_mem_powerset (s : Finset α) : ∅ in powerset s := by simp

/--
theorem `mem_powerset_self` / 定理 `mem_powerset_self`

English:
theorem mem_powerset_self
  given: (s : Finset α)
  statement: s in powerset s
  proof: by simp

@[aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 mem_powerset_self
  条件: (s : 有限集 α)
  结论: s in powerset s
  证明: by simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
-/
theorem mem_powerset_self (s : Finset α) : s in powerset s := by simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `powerset_nonempty` / 定理 `powerset_nonempty`

English:
theorem powerset_nonempty
  given: (s : Finset α)
  statement: s.powerset.Nonempty
  proof: ⟨∅, empty_mem_powerset _⟩

@[simp]

中文:
定理 powerset_nonempty
  条件: (s : 有限集 α)
  结论: s.powerset.非空
  证明: ⟨∅, empty_mem_powerset _⟩

@[simp]

Depends on / 依赖: empty_mem_powerset
-/
theorem powerset_nonempty (s : Finset α) : s.powerset.Nonempty :=
  ⟨∅, empty_mem_powerset _⟩

@[simp]
/--
theorem `powerset_mono` / 定理 `powerset_mono`

English:
theorem powerset_mono
  given: {s t : Finset α}
  statement: powerset s subseteq powerset t ↔ s subseteq t
  proof: ⟨fun h => mem_powerset.1 h mem_powerset_self _, fun st _u h =>
mem_powerset.2 Subset.trans (mem_powerset.1 h) st⟩

中文:
定理 powerset_mono
  条件: {s t : 有限集 α}
  结论: powerset s subseteq powerset t ↔ s subseteq t
  证明: ⟨fun h => mem_powerset.1 h mem_powerset_self _, fun st _u h =>
mem_powerset.2 Subset.trans (mem_powerset.1 h) st⟩

Depends on / 依赖: Subset, Subset.trans, mem_powerset, mem_powerset_self
-/
theorem powerset_mono {s t : Finset α} : powerset s subseteq powerset t ↔ s subseteq t :=
⟨fun h => mem_powerset.1 h mem_powerset_self _, fun st _u h =>
mem_powerset.2 Subset.trans (mem_powerset.1 h) st⟩

/--
theorem `powerset_injective` / 定理 `powerset_injective`

English:
theorem powerset_injective
  statement: Injective (powerset : Finset α -> Finset (Finset α))
  proof: .of_eq_imp_le (powerset_mono.1 ·.le)

@[simp]

中文:
定理 powerset_injective
  结论: 单射 (powerset : 有限集 α -> 有限集 (有限集 α))
  证明: .of_eq_imp_le (powerset_mono.1 ·.le)

@[simp]

Depends on / 依赖: of_eq_imp_le, powerset_mono
-/
theorem powerset_injective : Injective (powerset : Finset α -> Finset (Finset α)) :=
  .of_eq_imp_le (powerset_mono.1 ·.le)

@[simp]
/--
theorem `powerset_inj` / 定理 `powerset_inj`

English:
theorem powerset_inj
  statement: powerset s = powerset t ↔ s = t
  proof: powerset_injective.eq_iff

@[simp]

中文:
定理 powerset_inj
  结论: powerset s = powerset t ↔ s = t
  证明: powerset_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, powerset_injective, powerset_injective.eq_iff
-/
theorem powerset_inj : powerset s = powerset t ↔ s = t :=
  powerset_injective.eq_iff

@[simp]
/--
theorem `powerset_empty` / 定理 `powerset_empty`

English:
theorem powerset_empty
  statement: (∅ : Finset α).powerset = {∅}
  proof: rfl

@[simp]

中文:
定理 powerset_empty
  结论: (∅ : 有限集 α).powerset = {∅}
  证明: rfl

@[simp]
-/
theorem powerset_empty : (∅ : Finset α).powerset = {∅} :=
  rfl

@[simp]
/--
theorem `powerset_eq_singleton_empty` / 定理 `powerset_eq_singleton_empty`

English:
theorem powerset_eq_singleton_empty
  statement: s.powerset = {∅} ↔ s = ∅
  proof: by
  rw [← powerset_empty]; rw [powerset_inj]

中文:
定理 powerset_eq_singleton_empty
  结论: s.powerset = {∅} ↔ s = ∅
  证明: by
  rw [← powerset_empty]; rw [powerset_inj]

Depends on / 依赖: powerset_empty, powerset_inj
-/
theorem powerset_eq_singleton_empty : s.powerset = {∅} ↔ s = ∅ := by
  rw [← powerset_empty]; rw [powerset_inj]

/--
theorem `image_injOn_powerset_of_injOn` / 定理 `image_injOn_powerset_of_injOn`

English:
theorem image_injOn_powerset_of_injOn
  given: {β : Type*} [DecidableEq β] {f : α -> β} (H : Set.InjOn f s)
  proof: by
  have {z a} (_ : z subseteq s) (_ : a in s) : a in z ↔ f a in z.image f := by grind [H.eq_iff]
  exact fun _ _ _ _ _ => by grind

中文:
定理 image_injOn_powerset_of_injOn
  条件: {β : 类型} [DecidableEq β] {f : α -> β} (H : 集合.单射限制 f s)
  证明: by
  have {z a} (_ : z subseteq s) (_ : a in s) : a in z ↔ f a in z.image f := by grind [H.eq_iff]
  exact fun _ _ _ _ _ => by grind

Depends on / 依赖: Finset, H.eq_iff, eq_iff, powerset, s.powerset, subseteq, z.image
-/
theorem image_injOn_powerset_of_injOn {β : Type*} [DecidableEq β] {f : α -> β} (H : Set.InjOn f s) :
    Set.InjOn (α := Finset α) (·.image f) s.powerset := by
  have {z a} (_ : z subseteq s) (_ : a in s) : a in z ↔ f a in z.image f := by grind [H.eq_iff]
  exact fun _ _ _ _ _ => by grind

/--
theorem `injOn_image_of_biUnion_injOn` / 定理 `injOn_image_of_biUnion_injOn`

English:
theorem injOn_image_of_biUnion_injOn
  statement: {β : Type*} [DecidableEq α] [DecidableEq β]
  proof: (image_injOn_powerset_of_injOn hf).mono (by aesop (add simp Set.subset_def))

中文:
定理 injOn_image_of_biUnion_injOn
  结论: {β : 类型} [DecidableEq α] [DecidableEq β]
  证明: (image_injOn_powerset_of_injOn hf).mono (by aesop (add simp Set.subset_def))

Depends on / 依赖: Set.subset_def, image_injOn_powerset_of_injOn, subset_def
-/
theorem injOn_image_of_biUnion_injOn {β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset (Finset α)} {f : α -> β} (hf : (S.biUnion id : Set α).InjOn f) :
    (S : Set (Finset α)).InjOn (·.image f) :=
  (image_injOn_powerset_of_injOn hf).mono (by aesop (add simp Set.subset_def))

/--
lemma `biUnion_id_subset_iff_subset_powerset` / 引理 `biUnion_id_subset_iff_subset_powerset`

English:
lemma biUnion_id_subset_iff_subset_powerset
  given: [DecidableEq α] {s : Finset (Finset α)}
  proof: by
  aesop (add simp subset_iff)

中文:
引理 biUnion_id_subset_iff_subset_powerset
  条件: [DecidableEq α] {s : 有限集 (有限集 α)}
  证明: by
  aesop (add simp subset_iff)

Depends on / 依赖: subset_iff
-/
lemma biUnion_id_subset_iff_subset_powerset [DecidableEq α] {s : Finset (Finset α)} :
    s.biUnion id subseteq t ↔ s subseteq t.powerset := by
  aesop (add simp subset_iff)

/--
theorem `image_surjOn_powerset` / 定理 `image_surjOn_powerset`

English:
theorem image_surjOn_powerset
  given: {β : Type*} [DecidableEq β] {f : α -> β}
  proof: fun t ht => ⟨{ x in s | f x in t}, by grind⟩

中文:
定理 image_surjOn_powerset
  条件: {β : 类型} [DecidableEq β] {f : α -> β}
  证明: fun t ht => ⟨{ x in s | f x in t}, by grind⟩

Depends on / 依赖: Finset, powerset, s.image, s.powerset
-/
theorem image_surjOn_powerset {β : Type*} [DecidableEq β] {f : α -> β} :
    Set.SurjOn (α := Finset α) (·.image f) s.powerset (s.image f).powerset :=
  fun t ht => ⟨{ x in s | f x in t}, by grind⟩

/--
theorem `powerset_image` / 定理 `powerset_image`

English:
theorem powerset_image
  given: {β : Type*} [DecidableEq β] {f : α -> β}
  proof: ext fun a => ⟨fun _ => mem_image.mpr ⟨{ x in s | f x in a}, by grind⟩, by grind⟩

中文:
定理 powerset_image
  条件: {β : 类型} [DecidableEq β] {f : α -> β}
  证明: ext fun a => ⟨fun _ => mem_image.mpr ⟨{ x in s | f x in a}, by grind⟩, by grind⟩

Depends on / 依赖: mem_image, mem_image.mpr
-/
theorem powerset_image {β : Type*} [DecidableEq β] {f : α -> β} :
    (s.image f).powerset = s.powerset.image (·.image f) :=
  ext fun a => ⟨fun _ => mem_image.mpr ⟨{ x in s | f x in a}, by grind⟩, by grind⟩

/-- **Number of Subsets of a Set** -/
@[simp]
/--
theorem `card_powerset` / 定理 `card_powerset`

English:
theorem card_powerset
  given: (s : Finset α)
  statement: card (powerset s) = 2 ^ card s
  proof: (card_pmap _ _ _).trans (Multiset.card_powerset s.1)

中文:
定理 card_powerset
  条件: (s : 有限集 α)
  结论: card (powerset s) = 2 ^ card s
  证明: (card_pmap _ _ _).trans (Multiset.card_powerset s.1)

Depends on / 依赖: Multiset, Multiset.card_powerset, card_pmap, card_powerset
-/
theorem card_powerset (s : Finset α) : card (powerset s) = 2 ^ card s :=
  (card_pmap _ _ _).trans (Multiset.card_powerset s.1)

/--
theorem `notMem_of_mem_powerset_of_notMem` / 定理 `notMem_of_mem_powerset_of_notMem`

English:
theorem notMem_of_mem_powerset_of_notMem
  statement: {s t : Finset α} {a : α} (ht : t in s.powerset)
  proof: by
  apply mt _ h
  apply mem_powerset.1 ht

中文:
定理 notMem_of_mem_powerset_of_notMem
  结论: {s t : 有限集 α} {a : α} (ht : t in s.powerset)
  证明: by
  apply mt _ h
  apply mem_powerset.1 ht

Depends on / 依赖: mem_powerset
-/
theorem notMem_of_mem_powerset_of_notMem {s t : Finset α} {a : α} (ht : t in s.powerset)
    (h : a ∉ s) : a ∉ t := by
  apply mt _ h
  apply mem_powerset.1 ht

/--
theorem `powerset_insert` / 定理 `powerset_insert`

English:
theorem powerset_insert
  given: [DecidableEq α] (s : Finset α) (a : α)
  proof: by
  ext t
  simp only [mem_powerset, mem_image, mem_union, subset_insert_iff]
  grind

中文:
定理 powerset_insert
  条件: [DecidableEq α] (s : 有限集 α) (a : α)
  证明: by
  ext t
  simp only [mem_powerset, mem_image, mem_union, subset_insert_iff]
  grind

Depends on / 依赖: mem_image, mem_powerset, mem_union, subset_insert_iff
-/
theorem powerset_insert [DecidableEq α] (s : Finset α) (a : α) :
    powerset (insert a s) = s.powerset union s.powerset.image (insert a) := by
  ext t
  simp only [mem_powerset, mem_image, mem_union, subset_insert_iff]
  grind

/--
lemma `pairwiseDisjoint_pair_insert` / 引理 `pairwiseDisjoint_pair_insert`

English:
lemma pairwiseDisjoint_pair_insert
  given: [DecidableEq α] {a : α} (ha : a ∉ s)
  proof: by
  simp_rw [Set.pairwiseDisjoint_iff, mem_coe, mem_powerset]
  rintro i hi j hj
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, or_imp, imp_self, true_and]
  refine ⟨?_, ?_, insert_erase_invOn.2.injOn (notMem_mono hi ha

中文:
引理 pairwiseDisjoint_pair_insert
  条件: [DecidableEq α] {a : α} (ha : a ∉ s)
  证明: by
  simp_rw [Set.pairwiseDisjoint_iff, mem_coe, mem_powerset]
  rintro i hi j hj
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, or_imp, imp_self, true_and]
  refine ⟨?_, ?_, insert_erase_invOn.2.injOn (notMem_mono hi ha

Depends on / 依赖: Finset, Finset.mem_insert_self, Finset.notMem_mono, Nonempty, Set.Nonempty, Set.mem_insert_iff, Set.mem_inter_iff, Set.mem_singleton_iff, Set.pairwiseDisjoint_iff, exists_eq_left, exists_eq_or_imp, imp_self, insert_erase_invOn, mem_coe, mem_insert_iff, mem_insert_self, mem_inter_iff, mem_powerset, mem_singleton_iff, notMem_mono
-/
lemma pairwiseDisjoint_pair_insert [DecidableEq α] {a : α} (ha : a ∉ s) :
    (s.powerset : Set (Finset α)).PairwiseDisjoint fun t => ({t, insert a t} : Set (Finset α)) := by
  simp_rw [Set.pairwiseDisjoint_iff, mem_coe, mem_powerset]
  rintro i hi j hj
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, or_imp, imp_self, true_and]
  refine ⟨?_, ?_, insert_erase_invOn.2.injOn (notMem_mono hi ha) (notMem_mono hj ha)⟩ <;>
    rintro rfl <;>
    cases Finset.notMem_mono ‹_› ha (Finset.mem_insert_self _ _)

/--
Instance `decidableExistsOfDecidableSubsets` / 实例 `decidableExistsOfDecidableSubsets`

English:
instance decidableExistsOfDecidableSubsets
  signature: {s : Finset α} {p : forall t subseteq s, Prop}
  body: decidable_of_iff (exists (t : _) (hs : t in s.powerset), p t (mem_powerset.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_powerset.2 hs, hp⟩⟩

中文:
实例 decidableExistsOfDecidableSubsets
  签名: {s : 有限集 α} {p : 对任意 t subseteq s, 命题}
  定义体: decidable_of_iff (exists (t : _) (hs : t in s.powerset), p t (mem_powerset.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_powerset.2 hs, hp⟩⟩

Depends on / 依赖: decidable_of_iff, mem_powerset, powerset, s.powerset
-/
instance decidableExistsOfDecidableSubsets {s : Finset α} {p : forall t subseteq s, Prop}
    [forall (t) (h : t subseteq s), Decidable (p t h)] : Decidable (exists (t : _) (h : t subseteq s), p t h) :=
  decidable_of_iff (exists (t : _) (hs : t in s.powerset), p t (mem_powerset.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_powerset.2 hs, hp⟩⟩

/--
Instance `decidableForallOfDecidableSubsets` / 实例 `decidableForallOfDecidableSubsets`

English:
instance decidableForallOfDecidableSubsets
  signature: {s : Finset α} {p : forall t subseteq s, Prop}
  body: decidable_of_iff (forall (t) (h : t in s.powerset), p t (mem_powerset.1 h))
    ⟨fun h t hs => h t (mem_powerset.2 hs), fun h _ _ => h _ _⟩

中文:
实例 decidableForallOfDecidableSubsets
  签名: {s : 有限集 α} {p : 对任意 t subseteq s, 命题}
  定义体: decidable_of_iff (forall (t) (h : t in s.powerset), p t (mem_powerset.1 h))
    ⟨fun h t hs => h t (mem_powerset.2 hs), fun h _ _ => h _ _⟩

Depends on / 依赖: decidable_of_iff, mem_powerset, powerset, s.powerset
-/
instance decidableForallOfDecidableSubsets {s : Finset α} {p : forall t subseteq s, Prop}
    [forall (t) (h : t subseteq s), Decidable (p t h)] : Decidable (forall (t) (h : t subseteq s), p t h) :=
  decidable_of_iff (forall (t) (h : t in s.powerset), p t (mem_powerset.1 h))
    ⟨fun h t hs => h t (mem_powerset.2 hs), fun h _ _ => h _ _⟩

/--
Instance `decidableExistsOfDecidableSubsets'` / 实例 `decidableExistsOfDecidableSubsets'`

English:
instance decidableExistsOfDecidableSubsets'
  signature: {s : Finset α} {p : Finset α -> Prop}
  body: decidable_of_iff (exists (t : _) (_h : t subseteq s), p t) by simp

中文:
实例 decidableExistsOfDecidableSubsets'
  签名: {s : 有限集 α} {p : 有限集 α -> 命题}
  定义体: decidable_of_iff (exists (t : _) (_h : t subseteq s), p t) by simp

Depends on / 依赖: decidable_of_iff, subseteq
-/
instance decidableExistsOfDecidableSubsets' {s : Finset α} {p : Finset α -> Prop}
    [forall t, Decidable (p t)] : Decidable (exists t subseteq s, p t) :=
decidable_of_iff (exists (t : _) (_h : t subseteq s), p t) by simp

/--
Instance `decidableForallOfDecidableSubsets'` / 实例 `decidableForallOfDecidableSubsets'`

English:
instance decidableForallOfDecidableSubsets'
  signature: {s : Finset α} {p : Finset α -> Prop}
  body: decidable_of_iff (forall (t : _) (_h : t subseteq s), p t) by simp

中文:
实例 decidableForallOfDecidableSubsets'
  签名: {s : 有限集 α} {p : 有限集 α -> 命题}
  定义体: decidable_of_iff (forall (t : _) (_h : t subseteq s), p t) by simp

Depends on / 依赖: decidable_of_iff, subseteq
-/
instance decidableForallOfDecidableSubsets' {s : Finset α} {p : Finset α -> Prop}
    [forall t, Decidable (p t)] : Decidable (forall t subseteq s, p t) :=
decidable_of_iff (forall (t : _) (_h : t subseteq s), p t) by simp

end Powerset

section SSubsets

variable [DecidableEq α]

/--
Definition of `ssubsets` / `ssubsets` 的定义

English:
definition ssubsets
  signature: (s : Finset α)
  body: erase (powerset s) s

@[simp, grind =]

中文:
定义 ssubsets
  签名: (s : 有限集 α)
  定义体: erase (powerset s) s

@[simp, grind =]

Depends on / 依赖: powerset
-/
def ssubsets (s : Finset α) : Finset (Finset α) :=
  erase (powerset s) s

@[simp, grind =]
/--
theorem `mem_ssubsets` / 定理 `mem_ssubsets`

English:
theorem mem_ssubsets
  given: {s t : Finset α}
  statement: t in s.ssubsets ↔ t ⊂ s
  proof: by
  rw [ssubsets]; rw [mem_erase]; rw [mem_powerset]; rw [ssubset_iff_subset_ne]; rw [and_comm]

中文:
定理 mem_ssubsets
  条件: {s t : 有限集 α}
  结论: t in s.ssubsets ↔ t ⊂ s
  证明: by
  rw [ssubsets]; rw [mem_erase]; rw [mem_powerset]; rw [ssubset_iff_subset_ne]; rw [and_comm]

Depends on / 依赖: and_comm, mem_erase, mem_powerset, ssubset_iff_subset_ne, ssubsets
-/
theorem mem_ssubsets {s t : Finset α} : t in s.ssubsets ↔ t ⊂ s := by
  rw [ssubsets]; rw [mem_erase]; rw [mem_powerset]; rw [ssubset_iff_subset_ne]; rw [and_comm]

/--
theorem `empty_mem_ssubsets` / 定理 `empty_mem_ssubsets`

English:
theorem empty_mem_ssubsets
  given: {s : Finset α} (h : s.Nonempty)
  statement: ∅ in s.ssubsets
  proof: by
  rw [mem_ssubsets]; rw [ssubset_iff_subset_ne]
  exact ⟨empty_subset s, h.ne_empty.symm⟩

中文:
定理 empty_mem_ssubsets
  条件: {s : 有限集 α} (h : s.非空)
  结论: ∅ in s.ssubsets
  证明: by
  rw [mem_ssubsets]; rw [ssubset_iff_subset_ne]
  exact ⟨empty_subset s, h.ne_empty.symm⟩

Depends on / 依赖: empty_subset, h.ne_empty.symm, mem_ssubsets, ne_empty, ssubset_iff_subset_ne
-/
theorem empty_mem_ssubsets {s : Finset α} (h : s.Nonempty) : ∅ in s.ssubsets := by
  rw [mem_ssubsets]; rw [ssubset_iff_subset_ne]
  exact ⟨empty_subset s, h.ne_empty.symm⟩

/--
Definition of `decidableExistsOfDecidableSSubsets` / `decidableExistsOfDecidableSSubsets` 的定义

English:
definition decidableExistsOfDecidableSSubsets
  signature: {s : Finset α} {p : forall t ⊂ s, Prop}
  body: decidable_of_iff (exists (t : _) (hs : t in s.ssubsets), p t (mem_ssubsets.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_ssubsets.2 hs, hp⟩⟩

中文:
定义 decidableExistsOfDecidableSSubsets
  签名: {s : 有限集 α} {p : 对任意 t ⊂ s, 命题}
  定义体: decidable_of_iff (exists (t : _) (hs : t in s.ssubsets), p t (mem_ssubsets.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_ssubsets.2 hs, hp⟩⟩

Depends on / 依赖: decidable_of_iff, mem_ssubsets, s.ssubsets, ssubsets
-/
def decidableExistsOfDecidableSSubsets {s : Finset α} {p : forall t ⊂ s, Prop}
    [forall t h, Decidable (p t h)] : Decidable (exists t h, p t h) :=
  decidable_of_iff (exists (t : _) (hs : t in s.ssubsets), p t (mem_ssubsets.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_ssubsets.2 hs, hp⟩⟩

/--
Definition of `decidableForallOfDecidableSSubsets` / `decidableForallOfDecidableSSubsets` 的定义

English:
definition decidableForallOfDecidableSSubsets
  signature: {s : Finset α} {p : forall t ⊂ s, Prop}
  body: decidable_of_iff (forall (t) (h : t in s.ssubsets), p t (mem_ssubsets.1 h))
    ⟨fun h t hs => h t (mem_ssubsets.2 hs), fun h _ _ => h _ _⟩

中文:
定义 decidableForallOfDecidableSSubsets
  签名: {s : 有限集 α} {p : 对任意 t ⊂ s, 命题}
  定义体: decidable_of_iff (forall (t) (h : t in s.ssubsets), p t (mem_ssubsets.1 h))
    ⟨fun h t hs => h t (mem_ssubsets.2 hs), fun h _ _ => h _ _⟩

Depends on / 依赖: decidable_of_iff, mem_ssubsets, s.ssubsets, ssubsets
-/
def decidableForallOfDecidableSSubsets {s : Finset α} {p : forall t ⊂ s, Prop}
    [forall t h, Decidable (p t h)] : Decidable (forall t h, p t h) :=
  decidable_of_iff (forall (t) (h : t in s.ssubsets), p t (mem_ssubsets.1 h))
    ⟨fun h t hs => h t (mem_ssubsets.2 hs), fun h _ _ => h _ _⟩

/--
Definition of `decidableExistsOfDecidableSSubsets'` / `decidableExistsOfDecidableSSubsets'` 的定义

English:
definition decidableExistsOfDecidableSSubsets'
  signature: {s : Finset α} {p : Finset α -> Prop}
  body: @Finset.decidableExistsOfDecidableSSubsets _ _ _ _ hu

中文:
定义 decidableExistsOfDecidableSSubsets'
  签名: {s : 有限集 α} {p : 有限集 α -> 命题}
  定义体: @Finset.decidableExistsOfDecidableSSubsets _ _ _ _ hu

Depends on / 依赖: Finset, Finset.decidableExistsOfDecidableSSubsets, decidableExistsOfDecidableSSubsets
-/
def decidableExistsOfDecidableSSubsets' {s : Finset α} {p : Finset α -> Prop}
    (hu : forall t ⊂ s, Decidable (p t)) : Decidable (exists (t : _) (_h : t ⊂ s), p t) :=
  @Finset.decidableExistsOfDecidableSSubsets _ _ _ _ hu

/--
Definition of `decidableForallOfDecidableSSubsets'` / `decidableForallOfDecidableSSubsets'` 的定义

English:
definition decidableForallOfDecidableSSubsets'
  signature: {s : Finset α} {p : Finset α -> Prop}
  body: @Finset.decidableForallOfDecidableSSubsets _ _ _ _ hu

中文:
定义 decidableForallOfDecidableSSubsets'
  签名: {s : 有限集 α} {p : 有限集 α -> 命题}
  定义体: @Finset.decidableForallOfDecidableSSubsets _ _ _ _ hu

Depends on / 依赖: Finset, Finset.decidableForallOfDecidableSSubsets, decidableForallOfDecidableSSubsets
-/
def decidableForallOfDecidableSSubsets' {s : Finset α} {p : Finset α -> Prop}
    (hu : forall t ⊂ s, Decidable (p t)) : Decidable (forall t ⊂ s, p t) :=
  @Finset.decidableForallOfDecidableSSubsets _ _ _ _ hu

end SSubsets

section powersetCard
variable {n} {s t : Finset α}

/--
Definition of `powersetCard` / `powersetCard` 的定义

English:
definition powersetCard
  signature: (n : Nat) (s : Finset α)
  body: ⟨((s.1.powersetCard n).pmap Finset.mk) fun _t h => nodup_of_le (mem_powersetCard.1 h).1 s.2,
    s.2.powersetCard.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩

中文:
定义 powersetCard
  签名: (n : 自然数) (s : 有限集 α)
  定义体: ⟨((s.1.powersetCard n).pmap Finset.mk) fun _t h => nodup_of_le (mem_powersetCard.1 h).1 s.2,
    s.2.powersetCard.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩

Depends on / 依赖: Finset, Finset.mk, Finset.val, congr_arg, mem_powersetCard, nodup_of_le, powersetCard, powersetCard.pmap
-/
def powersetCard (n : Nat) (s : Finset α) : Finset (Finset α) :=
  ⟨((s.1.powersetCard n).pmap Finset.mk) fun _t h => nodup_of_le (mem_powersetCard.1 h).1 s.2,
    s.2.powersetCard.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩

/--
lemma `mem_powersetCard` / 引理 `mem_powersetCard`

English:
lemma mem_powersetCard
  statement: s in powersetCard n t ↔ s subseteq t ∧ card s = n
  proof: by
  cases s; simp [powersetCard, val_le_iff.symm]

@[simp]

中文:
引理 mem_powersetCard
  结论: s in powersetCard n t ↔ s subseteq t ∧ card s = n
  证明: by
  cases s; simp [powersetCard, val_le_iff.symm]

@[simp]
-/
@[simp, grind =] lemma mem_powersetCard : s in powersetCard n t ↔ s subseteq t ∧ card s = n := by
  cases s; simp [powersetCard, val_le_iff.symm]

@[simp]
/--
theorem `powersetCard_mono` / 定理 `powersetCard_mono`

English:
theorem powersetCard_mono
  given: {n} {s t : Finset α} (h : s subseteq t)
  statement: powersetCard n s subseteq powersetCard n t
  proof: fun _u h' => mem_powersetCard.2
    And.imp (fun h₂ => Subset.trans h₂ h) id (mem_powersetCard.1 h')

中文:
定理 powersetCard_mono
  条件: {n} {s t : 有限集 α} (h : s subseteq t)
  结论: powersetCard n s subseteq powersetCard n t
  证明: fun _u h' => mem_powersetCard.2
    And.imp (fun h₂ => Subset.trans h₂ h) id (mem_powersetCard.1 h')

Depends on / 依赖: And.imp, Subset, Subset.trans, mem_powersetCard
-/
theorem powersetCard_mono {n} {s t : Finset α} (h : s subseteq t) : powersetCard n s subseteq powersetCard n t :=
fun _u h' => mem_powersetCard.2
    And.imp (fun h₂ => Subset.trans h₂ h) id (mem_powersetCard.1 h')

/-- **Formula for the Number of Combinations** -/
@[simp]
/--
theorem `card_powersetCard` / 定理 `card_powersetCard`

English:
theorem card_powersetCard
  given: (n : Nat) (s : Finset α)
  proof: (card_pmap _ _ _).trans (Multiset.card_powersetCard n s.1)

中文:
定理 card_powersetCard
  条件: (n : 自然数) (s : 有限集 α)
  证明: (card_pmap _ _ _).trans (Multiset.card_powersetCard n s.1)

Depends on / 依赖: Multiset, Multiset.card_powersetCard, card_pmap, card_powersetCard
-/
theorem card_powersetCard (n : Nat) (s : Finset α) :
    card (powersetCard n s) = Nat.choose (card s) n :=
  (card_pmap _ _ _).trans (Multiset.card_powersetCard n s.1)

/--
theorem `filter_powersetCard_subset` / 定理 `filter_powersetCard_subset`

English:
theorem filter_powersetCard_subset
  statement: [DecidableEq α] (s t : Finset α) (n : Nat)
  proof: by
  ext x
  simp only [mem_filter, mem_powersetCard, mem_image]
  constructor
  · intro ⟨⟨hxt, hxn⟩, hsx⟩
    exact ⟨x \ s, ⟨fun y hy => mem_sdiff.mpr ⟨hxt (mem_sdiff.mp hy).1, (mem_sdiff.mp hy).2⟩,
           by rw [card_sdiff_of_subset hsx, hxn]⟩, sdiff_union_of_subset hsx⟩
  · rintro ⟨y, ⟨hyt, h

中文:
定理 filter_powersetCard_subset
  结论: [DecidableEq α] (s t : 有限集 α) (n : 自然数)
  证明: by
  ext x
  simp only [mem_filter, mem_powersetCard, mem_image]
  constructor
  · intro ⟨⟨hxt, hxn⟩, hsx⟩
    exact ⟨x \ s, ⟨fun y hy => mem_sdiff.mpr ⟨hxt (mem_sdiff.mp hy).1, (mem_sdiff.mp hy).2⟩,
           by rw [card_sdiff_of_subset hsx, hxn]⟩, sdiff_union_of_subset hsx⟩
  · rintro ⟨y, ⟨hyt, h

Depends on / 依赖: card_sdiff_of_subset, card_union_of_disjoint, disjoint_of_subset_left, disjoint_sdiff_self_left, hyt.trans, mem_filter, mem_image, mem_powersetCard, mem_sdiff, mem_sdiff.mp, mem_sdiff.mpr, sdiff_subset, sdiff_union_of_subset, subset_union_right, union_subset
-/
theorem filter_powersetCard_subset [DecidableEq α] (s t : Finset α) (n : Nat)
    (hst : s subseteq t) (hsn : #s <= n) :
    (t.powersetCard n).filter (s subseteq ·) = ((t \ s).powersetCard (n - #s)).image (· union s) := by
  ext x
  simp only [mem_filter, mem_powersetCard, mem_image]
  constructor
  · intro ⟨⟨hxt, hxn⟩, hsx⟩
    exact ⟨x \ s, ⟨fun y hy => mem_sdiff.mpr ⟨hxt (mem_sdiff.mp hy).1, (mem_sdiff.mp hy).2⟩,
           by rw [card_sdiff_of_subset hsx, hxn]⟩, sdiff_union_of_subset hsx⟩
  · rintro ⟨y, ⟨hyt, hyn⟩, rfl⟩
    refine ⟨⟨union_subset (hyt.trans sdiff_subset) hst, ?_⟩, subset_union_right⟩
    rw [card_union_of_disjoint (disjoint_of_subset_left hyt disjoint_sdiff_self_left)]; rw [hyn]
    lia

/--
lemma `card_filter_powersetCard_subset` / 引理 `card_filter_powersetCard_subset`

English:
lemma card_filter_powersetCard_subset
  statement: [DecidableEq α] (s t : Finset α) (n : Nat)
  proof: by
  have hinj : Set.InjOn (· union s) ↑((t \ s).powersetCard (n - #s)) := fun a ha b hb hab =>
    (union_sdiff_cancel_right
      (disjoint_of_subset_left (mem_powersetCard.mp ha).1 disjoint_sdiff_self_left)).symm.trans
    ((congrArg (· \ s) hab).trans
      (union_sdiff_cancel_right
        (dis

中文:
引理 card_filter_powersetCard_subset
  结论: [DecidableEq α] (s t : 有限集 α) (n : 自然数)
  证明: by
  have hinj : Set.InjOn (· union s) ↑((t \ s).powersetCard (n - #s)) := fun a ha b hb hab =>
    (union_sdiff_cancel_right
      (disjoint_of_subset_left (mem_powersetCard.mp ha).1 disjoint_sdiff_self_left)).symm.trans
    ((congrArg (· \ s) hab).trans
      (union_sdiff_cancel_right
        (dis

Depends on / 依赖: Set.InjOn, card_image_of_injOn, card_powersetCard, card_sdiff_of_subset, disjoint_of_subset_left, disjoint_sdiff_self_left, filter_powersetCard_subset, mem_powersetCard, mem_powersetCard.mp, powersetCard, symm.trans, union_sdiff_cancel_right
-/
lemma card_filter_powersetCard_subset [DecidableEq α] (s t : Finset α) (n : Nat)
    (hst : s subseteq t) (hsn : #s <= n) :
    #((t.powersetCard n).filter (s subseteq ·)) = Nat.choose (#t - #s) (n - #s) := by
  have hinj : Set.InjOn (· union s) ↑((t \ s).powersetCard (n - #s)) := fun a ha b hb hab =>
    (union_sdiff_cancel_right
      (disjoint_of_subset_left (mem_powersetCard.mp ha).1 disjoint_sdiff_self_left)).symm.trans
    ((congrArg (· \ s) hab).trans
      (union_sdiff_cancel_right
        (disjoint_of_subset_left (mem_powersetCard.mp hb).1 disjoint_sdiff_self_left)))
  simp only [filter_powersetCard_subset s t n hst hsn, card_image_of_injOn hinj,
             card_powersetCard, card_sdiff_of_subset hst]

@[simp]
/--
theorem `powersetCard_zero` / 定理 `powersetCard_zero`

English:
theorem powersetCard_zero
  given: (s : Finset α)
  statement: s.powersetCard 0 = {∅}
  proof: by
  grind

中文:
定理 powersetCard_zero
  条件: (s : 有限集 α)
  结论: s.powersetCard 0 = {∅}
  证明: by
  grind
-/
theorem powersetCard_zero (s : Finset α) : s.powersetCard 0 = {∅} := by
  grind

/--
lemma `powersetCard_empty_subsingleton` / 引理 `powersetCard_empty_subsingleton`

English:
lemma powersetCard_empty_subsingleton
  given: (n : Nat)
  proof: by
  simp [Set.Subsingleton, subset_empty]

@[simp]

中文:
引理 powersetCard_empty_subsingleton
  条件: (n : 自然数)
  证明: by
  simp [Set.Subsingleton, subset_empty]

@[simp]

Depends on / 依赖: Set.Subsingleton, Subsingleton, subset_empty
-/
lemma powersetCard_empty_subsingleton (n : Nat) :
    (powersetCard n (∅ : Finset α) : Set <| Finset α).Subsingleton := by
  simp [Set.Subsingleton, subset_empty]

@[simp]
/--
theorem `map_val_val_powersetCard` / 定理 `map_val_val_powersetCard`

English:
theorem map_val_val_powersetCard
  given: (s : Finset α) (i : Nat)
  proof: by
  simp [Finset.powersetCard, map_pmap, pmap_eq_map, map_id']

中文:
定理 map_val_val_powersetCard
  条件: (s : 有限集 α) (i : 自然数)
  证明: by
  simp [Finset.powersetCard, map_pmap, pmap_eq_map, map_id']

Depends on / 依赖: Finset, Finset.powersetCard, map_id, map_pmap, pmap_eq_map, powersetCard
-/
theorem map_val_val_powersetCard (s : Finset α) (i : Nat) :
    (s.powersetCard i).val.map Finset.val = s.1.powersetCard i := by
  simp [Finset.powersetCard, map_pmap, pmap_eq_map, map_id']

/--
theorem `powersetCard_one` / 定理 `powersetCard_one`

English:
theorem powersetCard_one
  given: (s : Finset α)
  proof: eq_of_veq Multiset.map_injective val_injective by simp [Multiset.powersetCard_one]

@[simp]

中文:
定理 powersetCard_one
  条件: (s : 有限集 α)
  证明: eq_of_veq Multiset.map_injective val_injective by simp [Multiset.powersetCard_one]

@[simp]

Depends on / 依赖: Multiset, Multiset.map_injective, Multiset.powersetCard_one, eq_of_veq, map_injective, powersetCard_one, val_injective
-/
theorem powersetCard_one (s : Finset α) :
    s.powersetCard 1 = s.map ⟨_, Finset.singleton_injective⟩ :=
eq_of_veq Multiset.map_injective val_injective by simp [Multiset.powersetCard_one]

@[simp]
/--
lemma `powersetCard_eq_empty` / 引理 `powersetCard_eq_empty`

English:
lemma powersetCard_eq_empty
  statement: powersetCard n s = ∅ ↔ s.card < n
  proof: by
refine ⟨?_, fun h => card_eq_zero.1 by rw [card_powersetCard, Nat.choose_eq_zero_of_lt h]⟩
  contrapose!
exact fun h => (exists_subset_card_eq h).imp by simp

中文:
引理 powersetCard_eq_empty
  结论: powersetCard n s = ∅ ↔ s.card < n
  证明: by
refine ⟨?_, fun h => card_eq_zero.1 by rw [card_powersetCard, Nat.choose_eq_zero_of_lt h]⟩
  contrapose!
exact fun h => (exists_subset_card_eq h).imp by simp

Depends on / 依赖: Nat.choose_eq_zero_of_lt, card_eq_zero, card_powersetCard, choose_eq_zero_of_lt, contrapose, exists_subset_card_eq
-/
lemma powersetCard_eq_empty : powersetCard n s = ∅ ↔ s.card < n := by
refine ⟨?_, fun h => card_eq_zero.1 by rw [card_powersetCard, Nat.choose_eq_zero_of_lt h]⟩
  contrapose!
exact fun h => (exists_subset_card_eq h).imp by simp

/--
lemma `powersetCard_card_add` / 引理 `powersetCard_card_add`

English:
lemma powersetCard_card_add
  given: (s : Finset α) (hn : 0 < n)
  proof: by simpa

中文:
引理 powersetCard_card_add
  条件: (s : 有限集 α) (hn : 0 < n)
  证明: by simpa
-/
@[simp] lemma powersetCard_card_add (s : Finset α) (hn : 0 < n) :
    s.powersetCard (s.card + n) = ∅ := by simpa

/--
theorem `powersetCard_eq_filter` / 定理 `powersetCard_eq_filter`

English:
theorem powersetCard_eq_filter
  given: {n} {s : Finset α}
  proof: by
  ext
  simp [mem_powersetCard]

中文:
定理 powersetCard_eq_filter
  条件: {n} {s : 有限集 α}
  证明: by
  ext
  simp [mem_powersetCard]

Depends on / 依赖: mem_powersetCard
-/
theorem powersetCard_eq_filter {n} {s : Finset α} :
    powersetCard n s = (powerset s).filter fun x => x.card = n := by
  ext
  simp [mem_powersetCard]

/--
theorem `powersetCard_succ_insert` / 定理 `powersetCard_succ_insert`

English:
theorem powersetCard_succ_insert
  given: [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s) (n : Nat)
  proof: by
  rw [powersetCard_eq_filter]; rw [powerset_insert]; rw [filter_union]; rw [← powersetCard_eq_filter]
  grind

@[simp]

中文:
定理 powersetCard_succ_insert
  条件: [DecidableEq α] {x : α} {s : 有限集 α} (h : x ∉ s) (n : 自然数)
  证明: by
  rw [powersetCard_eq_filter]; rw [powerset_insert]; rw [filter_union]; rw [← powersetCard_eq_filter]
  grind

@[simp]

Depends on / 依赖: filter_union, powersetCard_eq_filter, powerset_insert
-/
theorem powersetCard_succ_insert [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s) (n : Nat) :
    powersetCard n.succ (insert x s) =
    powersetCard n.succ s union (powersetCard n s).image (insert x) := by
  rw [powersetCard_eq_filter]; rw [powerset_insert]; rw [filter_union]; rw [← powersetCard_eq_filter]
  grind

@[simp]
/--
lemma `powersetCard_nonempty` / 引理 `powersetCard_nonempty`

English:
lemma powersetCard_nonempty
  statement: (powersetCard n s).Nonempty ↔ n <= s.card
  proof: by
  aesop (add simp [Finset.Nonempty, exists_subset_card_eq, card_le_card])

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, powersetCard_nonempty_of_le⟩ := powersetCard_nonempty

@[simp]

中文:
引理 powersetCard_nonempty
  结论: (powersetCard n s).非空 ↔ n <= s.card
  证明: by
  aesop (add simp [Finset.Nonempty, exists_subset_card_eq, card_le_card])

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, powersetCard_nonempty_of_le⟩ := powersetCard_nonempty

@[simp]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, card_le_card, exists_subset_card_eq
-/
lemma powersetCard_nonempty : (powersetCard n s).Nonempty ↔ n <= s.card := by
  aesop (add simp [Finset.Nonempty, exists_subset_card_eq, card_le_card])

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, powersetCard_nonempty_of_le⟩ := powersetCard_nonempty

@[simp]
/--
theorem `powersetCard_self` / 定理 `powersetCard_self`

English:
theorem powersetCard_self
  given: (s : Finset α)
  statement: powersetCard s.card s = {s}
  proof: by
  ext
  rw [mem_powersetCard]; rw [mem_singleton]
  constructor
  · exact fun ⟨hs, hc⟩ => eq_of_subset_of_card_le hs hc.ge
  · rintro rfl
    simp

中文:
定理 powersetCard_self
  条件: (s : 有限集 α)
  结论: powersetCard s.card s = {s}
  证明: by
  ext
  rw [mem_powersetCard]; rw [mem_singleton]
  constructor
  · exact fun ⟨hs, hc⟩ => eq_of_subset_of_card_le hs hc.ge
  · rintro rfl
    simp

Depends on / 依赖: eq_of_subset_of_card_le, hc.ge, mem_powersetCard, mem_singleton
-/
theorem powersetCard_self (s : Finset α) : powersetCard s.card s = {s} := by
  ext
  rw [mem_powersetCard]; rw [mem_singleton]
  constructor
  · exact fun ⟨hs, hc⟩ => eq_of_subset_of_card_le hs hc.ge
  · rintro rfl
    simp

/--
theorem `pairwise_disjoint_powersetCard` / 定理 `pairwise_disjoint_powersetCard`

English:
theorem pairwise_disjoint_powersetCard
  given: (s : Finset α)
  proof: fun _i _j hij =>
  Finset.disjoint_left.mpr fun _x hi hj =>
hij (mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2

中文:
定理 pairwise_disjoint_powersetCard
  条件: (s : 有限集 α)
  证明: fun _i _j hij =>
  Finset.disjoint_left.mpr fun _x hi hj =>
hij (mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2

Depends on / 依赖: star_smul
-/
theorem pairwise_disjoint_powersetCard (s : Finset α) :
    Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j) := fun _i _j hij =>
  Finset.disjoint_left.mpr fun _x hi hj =>
hij (mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2

set_option backward.isDefEq.respectTransparency false in
/--
theorem `powerset_card_disjiUnion` / 定理 `powerset_card_disjiUnion`

English:
theorem powerset_card_disjiUnion
  given: (s : Finset α)
  proof: by
  refine ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [mem_disjiUnion]
    exact
      ⟨a.card, mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp ha))),
        mem_powersetCard.mpr ⟨mem_powerset.mp ha, rfl⟩⟩
  · rcases mem_disjiUnion.mp ha with ⟨i, _hi, ha⟩
    exact mem_powers

中文:
定理 powerset_card_disjiUnion
  条件: (s : 有限集 α)
  证明: by
  refine ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [mem_disjiUnion]
    exact
      ⟨a.card, mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp ha))),
        mem_powersetCard.mpr ⟨mem_powerset.mp ha, rfl⟩⟩
  · rcases mem_disjiUnion.mp ha with ⟨i, _hi, ha⟩
    exact mem_powers

Depends on / 依赖: Nat.lt_succ_of_le, PosNum, PosNum.one, a.card, card_le_card, lt_succ_of_le, mem_disjiUnion, mem_disjiUnion.mp, mem_powerset, mem_powerset.mp, mem_powerset.mpr, mem_powersetCard, mem_powersetCard.mp, mem_powersetCard.mpr, mem_range, mem_range.mpr
-/
theorem powerset_card_disjiUnion (s : Finset α) :
    Finset.powerset s =
      (range (s.card + 1)).disjiUnion (fun i => powersetCard i s)
        (s.pairwise_disjoint_powersetCard.set_pairwise _) := by
  refine ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [mem_disjiUnion]
    exact
      ⟨a.card, mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp ha))),
        mem_powersetCard.mpr ⟨mem_powerset.mp ha, rfl⟩⟩
  · rcases mem_disjiUnion.mp ha with ⟨i, _hi, ha⟩
    exact mem_powerset.mpr (mem_powersetCard.mp ha).1

set_option backward.isDefEq.respectTransparency false in
/--
theorem `powerset_card_biUnion` / 定理 `powerset_card_biUnion`

English:
theorem powerset_card_biUnion
  given: [DecidableEq (Finset α)] (s : Finset α)
  proof: by
  simpa only [disjiUnion_eq_biUnion] using powerset_card_disjiUnion s

中文:
定理 powerset_card_biUnion
  条件: [DecidableEq (有限集 α)] (s : 有限集 α)
  证明: by
  simpa only [disjiUnion_eq_biUnion] using powerset_card_disjiUnion s

Depends on / 依赖: disjiUnion_eq_biUnion, powerset_card_disjiUnion
-/
theorem powerset_card_biUnion [DecidableEq (Finset α)] (s : Finset α) :
    Finset.powerset s = (range (s.card + 1)).biUnion fun i => powersetCard i s := by
  simpa only [disjiUnion_eq_biUnion] using powerset_card_disjiUnion s

/--
theorem `powersetCard_sup` / 定理 `powersetCard_sup`

English:
theorem powersetCard_sup
  given: [DecidableEq α] (u : Finset α) (n : Nat) (hn : n < u.card)
  proof: by
  apply le_antisymm
  · simp_rw [Finset.sup_le_iff, mem_powersetCard]
    rintro x ⟨h, -⟩
    exact h
  · rw [sup_eq_biUnion, subset_iff]
    intro x hx
    simp only [mem_biUnion, id]
    obtain ⟨t, ht⟩ : exists t, t in powersetCard n (u.erase x) := powersetCard_nonempty.2
      (le_trans (Nat.l

中文:
定理 powersetCard_sup
  条件: [DecidableEq α] (u : 有限集 α) (n : 自然数) (hn : n < u.card)
  证明: by
  apply le_antisymm
  · simp_rw [Finset.sup_le_iff, mem_powersetCard]
    rintro x ⟨h, -⟩
    exact h
  · rw [sup_eq_biUnion, subset_iff]
    intro x hx
    simp only [mem_biUnion, id]
    obtain ⟨t, ht⟩ : exists t, t in powersetCard n (u.erase x) := powersetCard_nonempty.2
      (le_trans (Nat.l

Depends on / 依赖: Finset, Finset.sup_le_iff, Nat.le_sub_one_of_lt, Num.zero, insert, insert_erase, le_antisymm, le_sub_one_of_lt, le_trans, mem_biUnion, mem_image_of_mem, mem_insert_self, mem_powersetCard, mem_union_right, notMem_erase, powersetCard, powersetCard_nonempty, powersetCard_succ_insert, pred_card_le_card_erase, simp_rw
-/
theorem powersetCard_sup [DecidableEq α] (u : Finset α) (n : Nat) (hn : n < u.card) :
    (powersetCard n.succ u).sup id = u := by
  apply le_antisymm
  · simp_rw [Finset.sup_le_iff, mem_powersetCard]
    rintro x ⟨h, -⟩
    exact h
  · rw [sup_eq_biUnion, subset_iff]
    intro x hx
    simp only [mem_biUnion, id]
    obtain ⟨t, ht⟩ : exists t, t in powersetCard n (u.erase x) := powersetCard_nonempty.2
      (le_trans (Nat.le_sub_one_of_lt hn) pred_card_le_card_erase)
    refine ⟨insert x t, ?_, mem_insert_self _ _⟩
    rw [← insert_erase hx]; rw [powersetCard_succ_insert (notMem_erase _ _)]
    exact mem_union_right _ (mem_image_of_mem _ ht)

/--
lemma `powersetCard_biUnion` / 引理 `powersetCard_biUnion`

English:
lemma powersetCard_biUnion
  given: [DecidableEq α] {r : Nat} (hr : r != 0) (hrs : r <= #s)
  proof: by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [← sup_eq_biUnion]
  exact powersetCard_sup _ _ hrs

中文:
引理 powersetCard_biUnion
  条件: [DecidableEq α] {r : 自然数} (hr : r != 0) (hrs : r <= #s)
  证明: by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [← sup_eq_biUnion]
  exact powersetCard_sup _ _ hrs

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, exists_eq_succ_of_ne_zero, powersetCard_sup, sup_eq_biUnion
-/
lemma powersetCard_biUnion [DecidableEq α] {r : Nat} (hr : r != 0) (hrs : r <= #s) :
    (s.powersetCard r).biUnion id = s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [← sup_eq_biUnion]
  exact powersetCard_sup _ _ hrs

/--
lemma `eq_of_powersetCard_eq` / 引理 `eq_of_powersetCard_eq`

English:
lemma eq_of_powersetCard_eq
  statement: {a b : Finset α} {r : Nat}
  proof: by
  classical
  simpa [powersetCard_biUnion hr₀, ← hab, hra] using congr(($h).biUnion id)

中文:
引理 eq_of_powersetCard_eq
  结论: {a b : 有限集 α} {r : 自然数}
  证明: by
  classical
  simpa [powersetCard_biUnion hr₀, ← hab, hra] using congr(($h).biUnion id)

Depends on / 依赖: biUnion, classical, powersetCard_biUnion
-/
lemma eq_of_powersetCard_eq {a b : Finset α} {r : Nat}
    (hab : #a = #b) (hr₀ : r != 0) (hra : r <= #a)
    (h : a.powersetCard r = b.powersetCard r) : a = b := by
  classical
  simpa [powersetCard_biUnion hr₀, ← hab, hra] using congr(($h).biUnion id)

/--
lemma `powersetCard_injOn` / 引理 `powersetCard_injOn`

English:
lemma powersetCard_injOn
  given: {q r : Nat} (hr₀ : r != 0) (hrq : r <= q)

中文:
引理 powersetCard_injOn
  条件: {q r : 自然数} (hr₀ : r != 0) (hrq : r <= q)

Depends on / 依赖: ZNum.zero
-/
lemma powersetCard_injOn {q r : Nat} (hr₀ : r != 0) (hrq : r <= q) :
    Set.InjOn (fun a => a.powersetCard r) {a : Finset α | #a = q}
  | _, rfl, _, hbq, h => eq_of_powersetCard_eq hbq.symm hr₀ hrq h

/--
theorem `powersetCard_map` / 定理 `powersetCard_map`

English:
theorem powersetCard_map
  given: {β : Type*} (f : α ↪ β) (n : Nat) (s : Finset α)
  proof: ext fun t => by
    simp only [mem_powersetCard, mem_map]
    constructor
    · classical
      intro h
      have : map f (filter (fun x => (f x in t)) s) = t := by grind
      refine ⟨_, ?_, this⟩
      rw [← card_map f]; rw [this]; rw [h.2]; simp
    · rintro ⟨a, ⟨has, rfl⟩, rfl⟩
      simp [has]

中文:
定理 powersetCard_map
  条件: {β : 类型} (f : α ↪ β) (n : 自然数) (s : 有限集 α)
  证明: ext fun t => by
    simp only [mem_powersetCard, mem_map]
    constructor
    · classical
      intro h
      have : map f (filter (fun x => (f x in t)) s) = t := by grind
      refine ⟨_, ?_, this⟩
      rw [← card_map f]; rw [this]; rw [h.2]; simp
    · rintro ⟨a, ⟨has, rfl⟩, rfl⟩
      simp [has]

Depends on / 依赖: ZNum.pos, card_map, classical, filter, mem_map, mem_powersetCard
-/
theorem powersetCard_map {β : Type*} (f : α ↪ β) (n : Nat) (s : Finset α) :
    powersetCard n (s.map f) = (powersetCard n s).map (mapEmbedding f).toEmbedding :=
  ext fun t => by
    simp only [mem_powersetCard, mem_map]
    constructor
    · classical
      intro h
      have : map f (filter (fun x => (f x in t)) s) = t := by grind
      refine ⟨_, ?_, this⟩
      rw [← card_map f]; rw [this]; rw [h.2]; simp
    · rintro ⟨a, ⟨has, rfl⟩, rfl⟩
      simp [has]

end powersetCard

end Finset
