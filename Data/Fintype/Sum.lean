/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Embedding.Set

/-!
## Instances

We provide the `Fintype` instance for the sum of two fintypes.
-/

@[expose] public section


universe u v

variable {α β : Type*}

open Finset

instance (α : Type u) (β : Type v) [Fintype α] [Fintype β] : Fintype (α oplus β) where
  elems := univ.disjSum univ
  complete := by rintro (_ | _) <;> simp

namespace Finset
variable {α β : Type*} {u : Finset (α oplus β)} {s : Finset α} {t : Finset β}

section left
variable [Fintype α] {u : Finset (α oplus β)}

/--
lemma `toLeft_eq_univ` / 引理 `toLeft_eq_univ`

English:
lemma toLeft_eq_univ
  statement: u.toLeft = univ ↔ univ.map .inl subseteq u
  proof: by
  simp [map_inl_subset_iff_subset_toLeft]

中文:
引理 toLeft_eq_univ
  结论: u.toLeft = univ ↔ univ.map .inl subseteq u
  证明: by
  simp [map_inl_subset_iff_subset_toLeft]

Depends on / 依赖: map_inl_subset_iff_subset_toLeft
-/
lemma toLeft_eq_univ : u.toLeft = univ ↔ univ.map .inl subseteq u := by
  simp [map_inl_subset_iff_subset_toLeft]

/--
lemma `toRight_eq_empty` / 引理 `toRight_eq_empty`

English:
lemma toRight_eq_empty
  statement: u.toRight = ∅ ↔ u subseteq univ.map .inl
  proof: by simp [subset_map_inl]

中文:
引理 toRight_eq_empty
  结论: u.toRight = ∅ ↔ u subseteq univ.map .inl
  证明: by simp [subset_map_inl]

Depends on / 依赖: subset_map_inl
-/
lemma toRight_eq_empty : u.toRight = ∅ ↔ u subseteq univ.map .inl := by simp [subset_map_inl]

end left

section right
variable [Fintype β] {u : Finset (α oplus β)}

/--
lemma `toRight_eq_univ` / 引理 `toRight_eq_univ`

English:
lemma toRight_eq_univ
  statement: u.toRight = univ ↔ univ.map .inr subseteq u
  proof: by
  simp [map_inr_subset_iff_subset_toRight]

中文:
引理 toRight_eq_univ
  结论: u.toRight = univ ↔ univ.map .inr subseteq u
  证明: by
  simp [map_inr_subset_iff_subset_toRight]

Depends on / 依赖: map_inr_subset_iff_subset_toRight
-/
lemma toRight_eq_univ : u.toRight = univ ↔ univ.map .inr subseteq u := by
  simp [map_inr_subset_iff_subset_toRight]

/--
lemma `toLeft_eq_empty` / 引理 `toLeft_eq_empty`

English:
lemma toLeft_eq_empty
  statement: u.toLeft = ∅ ↔ u subseteq univ.map .inr
  proof: by simp [subset_map_inr]

中文:
引理 toLeft_eq_empty
  结论: u.toLeft = ∅ ↔ u subseteq univ.map .inr
  证明: by simp [subset_map_inr]

Depends on / 依赖: subset_map_inr
-/
lemma toLeft_eq_empty : u.toLeft = ∅ ↔ u subseteq univ.map .inr := by simp [subset_map_inr]

end right

variable [Fintype α] [Fintype β]

/--
lemma `univ_disjSum_univ` / 引理 `univ_disjSum_univ`

English:
lemma univ_disjSum_univ
  statement: univ.disjSum univ = (univ : Finset (α oplus β))
  proof: rfl

中文:
引理 univ_disjSum_univ
  结论: univ.disjSum univ = (univ : 有限集 (α oplus β))
  证明: rfl
-/
@[simp] lemma univ_disjSum_univ : univ.disjSum univ = (univ : Finset (α oplus β)) := rfl
/--
lemma `toLeft_univ` / 引理 `toLeft_univ`

English:
lemma toLeft_univ
  statement: (univ : Finset (α oplus β)).toLeft = univ
  proof: by ext; simp

中文:
引理 toLeft_univ
  结论: (univ : 有限集 (α oplus β)).toLeft = univ
  证明: by ext; simp
-/
@[simp] lemma toLeft_univ : (univ : Finset (α oplus β)).toLeft = univ := by ext; simp
/--
lemma `toRight_univ` / 引理 `toRight_univ`

English:
lemma toRight_univ
  statement: (univ : Finset (α oplus β)).toRight = univ
  proof: by ext; simp

中文:
引理 toRight_univ
  结论: (univ : 有限集 (α oplus β)).toRight = univ
  证明: by ext; simp
-/
@[simp] lemma toRight_univ : (univ : Finset (α oplus β)).toRight = univ := by ext; simp

end Finset

@[simp]
/--
theorem `Fintype.card_sum` / 定理 `Fintype.card_sum`

English:
theorem Fintype.card_sum
  given: [Fintype α] [Fintype β]
  proof: card_disjSum _ _

中文:
定理 有限类型.card_sum
  条件: [有限类型 α] [有限类型 β]
  证明: card_disjSum _ _

Depends on / 依赖: card_disjSum
-/
theorem Fintype.card_sum [Fintype α] [Fintype β] :
    Fintype.card (α oplus β) = Fintype.card α + Fintype.card β :=
  card_disjSum _ _

/-- If the subtype of all-but-one elements is a `Fintype` then the type itself is a `Fintype`. -/
@[instance_reducible]
/--
Definition of `fintypeOfFintypeNe` / `fintypeOfFintypeNe` 的定义

English:
definition fintypeOfFintypeNe
  signature: (a : α) (_ : Fintype { b // b != a })
  body: Fintype.ofBijective (Sum.elim ((↑) : { b // b = a } -> α) ((↑) : { b // b != a } -> α)) by
    classical exact (Equiv.sumCompl (· = a)).bijective

中文:
定义 fintypeOfFintypeNe
  签名: (a : α) (_ : 有限类型 { b // b != a })
  定义体: Fintype.ofBijective (Sum.elim ((↑) : { b // b = a } -> α) ((↑) : { b // b != a } -> α)) by
    classical exact (Equiv.sumCompl (· = a)).bijective

Depends on / 依赖: Equiv.sumCompl, Fintype, Fintype.ofBijective, Sum.elim, bijective, classical, ofBijective, sumCompl
-/
def fintypeOfFintypeNe (a : α) (_ : Fintype { b // b != a }) : Fintype α :=
Fintype.ofBijective (Sum.elim ((↑) : { b // b = a } -> α) ((↑) : { b // b != a } -> α)) by
    classical exact (Equiv.sumCompl (· = a)).bijective

/--
theorem `image_subtype_ne_univ_eq_image_erase` / 定理 `image_subtype_ne_univ_eq_image_erase`

English:
theorem image_subtype_ne_univ_eq_image_erase
  given: [Fintype α] [DecidableEq β] (k : β) (b : α -> β)
  proof: by
  apply subset_antisymm
  · rw [image_subset_iff]
    intro i _
    apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _))
  · intro i hi
    rw [mem_image]
    rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩
    subst ha
    exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩

中文:
定理 image_subtype_ne_univ_eq_image_erase
  条件: [有限类型 α] [DecidableEq β] (k : β) (b : α -> β)
  证明: by
  apply subset_antisymm
  · rw [image_subset_iff]
    intro i _
    apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _))
  · intro i hi
    rw [mem_image]
    rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩
    subst ha
    exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩

Depends on / 依赖: erase_subset, image_subset_iff, mem_erase_of_ne_of_mem, mem_image, mem_image_of_mem, mem_univ, ne_of_mem_erase, subset_antisymm
-/
theorem image_subtype_ne_univ_eq_image_erase [Fintype α] [DecidableEq β] (k : β) (b : α -> β) :
    image (fun i : { a // b a != k } => b ↑i) univ = (image b univ).erase k := by
  apply subset_antisymm
  · rw [image_subset_iff]
    intro i _
    apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _))
  · intro i hi
    rw [mem_image]
    rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩
    subst ha
    exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩

/--
theorem `image_subtype_univ_ssubset_image_univ` / 定理 `image_subtype_univ_ssubset_image_univ`

English:
theorem image_subtype_univ_ssubset_image_univ
  statement: [Fintype α] [DecidableEq β] (k : β) (b : α -> β)
  proof: by
  grind

中文:
定理 image_subtype_univ_ssubset_image_univ
  结论: [有限类型 α] [DecidableEq β] (k : β) (b : α -> β)
  证明: by
  grind
-/
theorem image_subtype_univ_ssubset_image_univ [Fintype α] [DecidableEq β] (k : β) (b : α -> β)
    (hk : k in Finset.image b univ) (p : β -> Prop) [DecidablePred p] (hp : ¬p k) :
    image (fun i : { a // p (b a) } => b ↑i) univ ⊂ image b univ := by
  grind

/--
theorem `Finset.exists_equiv_extend_of_card_eq` / 定理 `Finset.exists_equiv_extend_of_card_eq`

English:
theorem Finset.exists_equiv_extend_of_card_eq
  statement: [Fintype α] [DecidableEq β] {t : Finset β}
  proof: by
  classical
    induction s using Finset.induction generalizing f with
    | empty =>
      obtain ⟨e⟩ : Nonempty (α ≃ ↥t) := by rwa [← Fintype.card_eq, Fintype.card_coe]
      use e
      simp
    | insert a s has H => ?_
    have hfst' : Finset.image f s subseteq t := (Finset.image_mono _ (s.su

中文:
定理 有限集.存在_equiv_extend_of_card_eq
  结论: [有限类型 α] [DecidableEq β] {t : 有限集 β}
  证明: by
  classical
    induction s using Finset.induction generalizing f with
    | empty =>
      obtain ⟨e⟩ : Nonempty (α ≃ ↥t) := by rwa [← Fintype.card_eq, Fintype.card_coe]
      use e
      simp
    | insert a s has H => ?_
    have hfst' : Finset.image f s subseteq t := (Finset.image_mono _ (s.su

Depends on / 依赖: Equiv.swap, Finset, Finset.image, Finset.image_mono, Finset.induction, Fintype, Fintype.card_coe, Fintype.card_eq, Nonempty, Set.InjOn, card_coe, card_eq, classical, generalizing, hfs.mono, image_mono, insert, mem_image_of_mem, mem_insert_self, s.mem_insert_self
-/
theorem Finset.exists_equiv_extend_of_card_eq [Fintype α] [DecidableEq β] {t : Finset β}
    (hαt : Fintype.card α = #t) {s : Finset α} {f : α -> β} (hfst : Finset.image f s subseteq t)
    (hfs : Set.InjOn f s) : exists g : α ≃ t, forall i in s, (g i : β) = f i := by
  classical
    induction s using Finset.induction generalizing f with
    | empty =>
      obtain ⟨e⟩ : Nonempty (α ≃ ↥t) := by rwa [← Fintype.card_eq, Fintype.card_coe]
      use e
      simp
    | insert a s has H => ?_
    have hfst' : Finset.image f s subseteq t := (Finset.image_mono _ (s.subset_insert a)).trans hfst
    have hfs' : Set.InjOn f s := hfs.mono (s.subset_insert a)
    obtain ⟨g', hg'⟩ := H hfst' hfs'
    have hfat : f a in t := hfst (mem_image_of_mem _ (s.mem_insert_self a))
    use g'.trans (Equiv.swap (⟨f a, hfat⟩ : t) (g' a))
    simp_rw [mem_insert]
    rintro i (rfl | hi)
    · simp
    rw [Equiv.trans_apply]; rw [Equiv.swap_apply_of_ne_of_ne]; rw [hg' _ hi]
    · exact
        ne_of_apply_ne Subtype.val
          (ne_of_eq_of_ne (hg' _ hi) <|
hfs.ne (subset_insert _ _ hi) (mem_insert_self _ _) ne_of_mem_of_not_mem hi has)
    · exact g'.injective.ne (ne_of_mem_of_not_mem hi has)

/--
theorem `Set.MapsTo.exists_equiv_extend_of_card_eq` / 定理 `Set.MapsTo.exists_equiv_extend_of_card_eq`

English:
theorem Set.MapsTo.exists_equiv_extend_of_card_eq
  statement: [Fintype α] {t : Finset β}
  proof: by
  classical
    let s' : Finset α := s.toFinset
    have hfst' : s'.image f subseteq t := by simpa [s', ← Finset.coe_subset] using! hfst
    have hfs' : Set.InjOn f s' := by simpa [s'] using! hfs
    obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hαt hfst' hfs'
    refine ⟨g, fun i hi =>

中文:
定理 集合.映射到.存在_equiv_extend_of_card_eq
  结论: [有限类型 α] {t : 有限集 β}
  证明: by
  classical
    let s' : Finset α := s.toFinset
    have hfst' : s'.image f subseteq t := by simpa [s', ← Finset.coe_subset] using! hfst
    have hfs' : Set.InjOn f s' := by simpa [s'] using! hfs
    obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hαt hfst' hfs'
    refine ⟨g, fun i hi =>

Depends on / 依赖: Finset, Finset.coe_subset, Finset.exists_equiv_extend_of_card_eq, Set.InjOn, classical, coe_subset, exists_equiv_extend_of_card_eq, s.toFinset, subseteq, toFinset
-/
theorem Set.MapsTo.exists_equiv_extend_of_card_eq [Fintype α] {t : Finset β}
    (hαt : Fintype.card α = #t) {s : Set α} {f : α -> β} (hfst : s.MapsTo f t)
    (hfs : Set.InjOn f s) : exists g : α ≃ t, forall i in s, (g i : β) = f i := by
  classical
    let s' : Finset α := s.toFinset
    have hfst' : s'.image f subseteq t := by simpa [s', ← Finset.coe_subset] using! hfst
    have hfs' : Set.InjOn f s' := by simpa [s'] using! hfs
    obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hαt hfst' hfs'
    refine ⟨g, fun i hi => ?_⟩
    apply hg
    simpa [s'] using! hi

/--
theorem `Fintype.card_subtype_or` / 定理 `Fintype.card_subtype_or`

English:
theorem Fintype.card_subtype_or
  statement: (p q : α -> Prop) [Fintype { x // p x }] [Fintype { x // q x }]
  proof: by
  classical
    convert! Fintype.card_le_of_embedding (subtypeOrLeftEmbedding p q)
    rw [Fintype.card_sum]

中文:
定理 有限类型.card_subtype_or
  结论: (p q : α -> 命题) [有限类型 { x // p x }] [有限类型 { x // q x }]
  证明: by
  classical
    convert! Fintype.card_le_of_embedding (subtypeOrLeftEmbedding p q)
    rw [Fintype.card_sum]

Depends on / 依赖: Fintype, Fintype.card_le_of_embedding, Fintype.card_sum, card_le_of_embedding, card_sum, classical, convert, subtypeOrLeftEmbedding
-/
theorem Fintype.card_subtype_or (p q : α -> Prop) [Fintype { x // p x }] [Fintype { x // q x }]
    [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } <= Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert! Fintype.card_le_of_embedding (subtypeOrLeftEmbedding p q)
    rw [Fintype.card_sum]

/--
theorem `Fintype.card_subtype_or_disjoint` / 定理 `Fintype.card_subtype_or_disjoint`

English:
theorem Fintype.card_subtype_or_disjoint
  statement: (p q : α -> Prop) (h : Disjoint p q) [Fintype { x // p x }]
  proof: by
  classical
    convert! Fintype.card_congr (subtypeOrEquiv p q h)
    simp

中文:
定理 有限类型.card_subtype_or_disjoint
  结论: (p q : α -> 命题) (h : Disjoint p q) [有限类型 { x // p x }]
  证明: by
  classical
    convert! Fintype.card_congr (subtypeOrEquiv p q h)
    simp

Depends on / 依赖: Fintype, Fintype.card_congr, card_congr, classical, convert, subtypeOrEquiv
-/
theorem Fintype.card_subtype_or_disjoint (p q : α -> Prop) (h : Disjoint p q) [Fintype { x // p x }]
    [Fintype { x // q x }] [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } = Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert! Fintype.card_congr (subtypeOrEquiv p q h)
    simp

/--
theorem `Fintype.card_subtype_eq_or_eq_of_ne` / 定理 `Fintype.card_subtype_eq_or_eq_of_ne`

English:
theorem Fintype.card_subtype_eq_or_eq_of_ne
  statement: {α : Type*} [Fintype α] [DecidableEq α] {a b : α}
  proof: Fintype.card_subtype_or_disjoint _ _ fun _ ha hb _ hc => ha _ hc ▸ hb _ hc ▸ h rfl

中文:
定理 有限类型.card_subtype_eq_or_eq_of_ne
  结论: {α : 类型} [有限类型 α] [DecidableEq α] {a b : α}
  证明: Fintype.card_subtype_or_disjoint _ _ fun _ ha hb _ hc => ha _ hc ▸ hb _ hc ▸ h rfl

Depends on / 依赖: Fintype, Fintype.card_subtype_or_disjoint, card_subtype_or_disjoint
-/
theorem Fintype.card_subtype_eq_or_eq_of_ne {α : Type*} [Fintype α] [DecidableEq α] {a b : α}
    (h : a != b) : Fintype.card { c : α // c = a ∨ c = b } = 2 :=
Fintype.card_subtype_or_disjoint _ _ fun _ ha hb _ hc => ha _ hc ▸ hb _ hc ▸ h rfl

attribute [local instance] Fintype.ofFinite in
@[simp]
/--
theorem `infinite_sum` / 定理 `infinite_sum`

English:
theorem infinite_sum
  statement: Infinite (α oplus β) ↔ Infinite α ∨ Infinite β
  proof: by
  refine ⟨fun H => ?_, fun H => H.elim (@Sum.infinite_of_left α β) (@Sum.infinite_of_right α β)⟩
  contrapose! H; cases H
  infer_instance

中文:
定理 infinite_sum
  结论: 无限 (α oplus β) ↔ 无限 α ∨ 无限 β
  证明: by
  refine ⟨fun H => ?_, fun H => H.elim (@Sum.infinite_of_left α β) (@Sum.infinite_of_right α β)⟩
  contrapose! H; cases H
  infer_instance

Depends on / 依赖: H.elim, Sum.infinite_of_left, Sum.infinite_of_right, contrapose, infer_instance, infinite_of_left, infinite_of_right
-/
theorem infinite_sum : Infinite (α oplus β) ↔ Infinite α ∨ Infinite β := by
  refine ⟨fun H => ?_, fun H => H.elim (@Sum.infinite_of_left α β) (@Sum.infinite_of_right α β)⟩
  contrapose! H; cases H
  infer_instance
