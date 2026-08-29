/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Multiset.Sym
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Symmetric powers of a finset

This file defines the symmetric powers of a finset as `Finset (Sym α n)` and `Finset (Sym2 α)`.

## Main declarations

* `Finset.sym`: The symmetric power of a finset. `s.sym n` is all the multisets of cardinality `n`
  whose elements are in `s`.
* `Finset.sym2`: The symmetric square of a finset. `s.sym2` is all the pairs whose elements are in
  `s`.
* A `Fintype (Sym2 α)` instance that does not require `DecidableEq α`.

## TODO

`Finset.sym` forms a Galois connection between `Finset α` and `Finset (Sym α n)`. Similar for
`Finset.sym2`.
-/

@[expose] public section

namespace Finset

variable {α β : Type*}

/-- `s.sym2` is the finset of all unordered pairs of elements from `s`.
It is the image of `s ×ˢ s` under the quotient `α × α → Sym2 α`. -/
@[simps]
/--
Definition of `sym2` / `sym2` 的定义

English:
definition sym2
  signature: (s : Finset α)
  body: ⟨s.1.sym2, s.2.sym2⟩

中文:
定义 sym2
  签名: (s : 有限集 α)
  定义体: ⟨s.1.sym2, s.2.sym2⟩
-/
protected def sym2 (s : Finset α) : Finset (Sym2 α) := ⟨s.1.sym2, s.2.sym2⟩

section
variable {s t : Finset α} {a b : α}

/--
theorem `mk_mem_sym2_iff` / 定理 `mk_mem_sym2_iff`

English:
theorem mk_mem_sym2_iff
  statement: s(a, b) in s.sym2 ↔ a in s ∧ b in s
  proof: by
  rw [mem_mk]; rw [sym2_val]; rw [Multiset.mk_mem_sym2_iff]; rw [mem_mk]; rw [mem_mk]

@[simp, grind =]

中文:
定理 mk_mem_sym2_iff
  结论: s(a, b) in s.sym2 ↔ a in s ∧ b in s
  证明: by
  rw [mem_mk]; rw [sym2_val]; rw [Multiset.mk_mem_sym2_iff]; rw [mem_mk]; rw [mem_mk]

@[simp, grind =]

Depends on / 依赖: Multiset, Multiset.mk_mem_sym2_iff, mem_mk, mk_mem_sym2_iff, sym2_val
-/
theorem mk_mem_sym2_iff : s(a, b) in s.sym2 ↔ a in s ∧ b in s := by
  rw [mem_mk]; rw [sym2_val]; rw [Multiset.mk_mem_sym2_iff]; rw [mem_mk]; rw [mem_mk]

@[simp, grind =]
/--
theorem `mem_sym2_iff` / 定理 `mem_sym2_iff`

English:
theorem mem_sym2_iff
  given: {m : Sym2 α}
  statement: m in s.sym2 ↔ forall a in m, a in s
  proof: by
  rw [mem_mk]; rw [sym2_val]; rw [Multiset.mem_sym2_iff]
  simp only [mem_val]

中文:
定理 mem_sym2_iff
  条件: {m : Sym2 α}
  结论: m in s.sym2 ↔ 对任意 a in m, a in s
  证明: by
  rw [mem_mk]; rw [sym2_val]; rw [Multiset.mem_sym2_iff]
  simp only [mem_val]

Depends on / 依赖: Multiset, Multiset.mem_sym2_iff, mem_mk, mem_sym2_iff, mem_val, sym2_val
-/
theorem mem_sym2_iff {m : Sym2 α} : m in s.sym2 ↔ forall a in m, a in s := by
  rw [mem_mk]; rw [sym2_val]; rw [Multiset.mem_sym2_iff]
  simp only [mem_val]

/--
lemma `coe_sym2` / 引理 `coe_sym2`

English:
lemma coe_sym2
  given: {m : Finset α}
  statement: (m.sym2 : Set (Sym2 α)) = (m : Set α).sym2
  proof: Set.ext fun z => z.ind fun a b => by simp

中文:
引理 coe_sym2
  条件: {m : 有限集 α}
  结论: (m.sym2 : 集合 (Sym2 α)) = (m : 集合 α).sym2
  证明: Set.ext fun z => z.ind fun a b => by simp
-/
@[simp] lemma coe_sym2 {m : Finset α} : (m.sym2 : Set (Sym2 α)) = (m : Set α).sym2 :=
  Set.ext fun z => z.ind fun a b => by simp

/--
theorem `sym2_cons` / 定理 `sym2_cons`

English:
theorem sym2_cons
  given: (a : α) (s : Finset α) (ha : a ∉ s)
  proof: val_injective Multiset.sym2_cons _ _

中文:
定理 sym2_cons
  条件: (a : α) (s : 有限集 α) (ha : a ∉ s)
  证明: val_injective Multiset.sym2_cons _ _

Depends on / 依赖: Multiset, Multiset.sym2_cons, sym2_cons, val_injective
-/
theorem sym2_cons (a : α) (s : Finset α) (ha : a ∉ s) :
    (s.cons a ha).sym2 = ((s.cons a ha).map <| Sym2.mkEmbedding a).disjUnion s.sym2 (by
      simp [Finset.disjoint_left, ha]) :=
val_injective Multiset.sym2_cons _ _

/--
theorem `sym2_insert` / 定理 `sym2_insert`

English:
theorem sym2_insert
  given: [DecidableEq α] (a : α) (s : Finset α)
  proof: by
  obtain ha | ha := Decidable.em (a in s)
  · simp only [insert_eq_of_mem ha, right_eq_union, image_subset_iff]
    simp_all
  · simpa [map_eq_image] using! sym2_cons a s ha

中文:
定理 sym2_insert
  条件: [DecidableEq α] (a : α) (s : 有限集 α)
  证明: by
  obtain ha | ha := Decidable.em (a in s)
  · simp only [insert_eq_of_mem ha, right_eq_union, image_subset_iff]
    simp_all
  · simpa [map_eq_image] using! sym2_cons a s ha

Depends on / 依赖: Decidable, Decidable.em, image_subset_iff, insert_eq_of_mem, map_eq_image, right_eq_union, sym2_cons
-/
theorem sym2_insert [DecidableEq α] (a : α) (s : Finset α) :
    (insert a s).sym2 = ((insert a s).image fun b => s(a, b)) union s.sym2 := by
  obtain ha | ha := Decidable.em (a in s)
  · simp only [insert_eq_of_mem ha, right_eq_union, image_subset_iff]
    simp_all
  · simpa [map_eq_image] using! sym2_cons a s ha

/--
theorem `sym2_map` / 定理 `sym2_map`

English:
theorem sym2_map
  given: (f : α ↪ β) (s : Finset α)
  statement: (s.map f).sym2 = s.sym2.map (.sym2Map f)
  proof: val_injective s.val.sym2_map _

中文:
定理 sym2_map
  条件: (f : α ↪ β) (s : 有限集 α)
  结论: (s.map f).sym2 = s.sym2.map (.sym2Map f)
  证明: val_injective s.val.sym2_map _

Depends on / 依赖: s.val.sym2_map, sym2_map, val_injective
-/
theorem sym2_map (f : α ↪ β) (s : Finset α) : (s.map f).sym2 = s.sym2.map (.sym2Map f) :=
val_injective s.val.sym2_map _

/--
theorem `sym2_image` / 定理 `sym2_image`

English:
theorem sym2_image
  given: [DecidableEq β] (f : α -> β) (s : Finset α)
  proof: by
  apply val_injective
  dsimp [Finset.sym2]
  rw [← Multiset.dedup_sym2]; rw [Multiset.sym2_map]

中文:
定理 sym2_image
  条件: [DecidableEq β] (f : α -> β) (s : 有限集 α)
  证明: by
  apply val_injective
  dsimp [Finset.sym2]
  rw [← Multiset.dedup_sym2]; rw [Multiset.sym2_map]

Depends on / 依赖: Finset, Finset.sym2, Multiset, Multiset.dedup_sym2, Multiset.sym2_map, dedup_sym2, sym2_map, val_injective
-/
theorem sym2_image [DecidableEq β] (f : α -> β) (s : Finset α) :
    (s.image f).sym2 = s.sym2.image (Sym2.map f) := by
  apply val_injective
  dsimp [Finset.sym2]
  rw [← Multiset.dedup_sym2]; rw [Multiset.sym2_map]

/--
Instance `_root_.Sym2.instFintype` / 实例 `_root_.Sym2.instFintype`

English:
instance _root_.Sym2.instFintype
  signature: [Fintype α]
  body: Finset.univ.sym2
  complete := fun x => by rw [mem_sym2_iff]; exact (fun a _ => mem_univ a)

中文:
实例 _root_.Sym2.instFintype
  签名: [有限类型 α]
  定义体: Finset.univ.sym2
  complete := fun x => by rw [mem_sym2_iff]; exact (fun a _ => mem_univ a)

Depends on / 依赖: Finset, Finset.univ.sym2
-/
instance _root_.Sym2.instFintype [Fintype α] : Fintype (Sym2 α) where
  elems := Finset.univ.sym2
  complete := fun x => by rw [mem_sym2_iff]; exact (fun a _ => mem_univ a)

-- Note(kmill): Using a default argument to make this simp lemma more general.
@[simp]
/--
theorem `sym2_univ` / 定理 `sym2_univ`

English:
theorem sym2_univ
  given: [Fintype α] (inst : Fintype (Sym2 α) := Sym2.instFintype)
  proof: by
  ext
  simp only [mem_sym2_iff, mem_univ, implies_true]

@[simp, mono]

中文:
定理 sym2_univ
  条件: [有限类型 α] (inst : 有限类型 (Sym2 α) := Sym2.instFintype)
  证明: by
  ext
  simp only [mem_sym2_iff, mem_univ, implies_true]

@[simp, mono]

Depends on / 依赖: Sym2.instFintype, instFintype
-/
theorem sym2_univ [Fintype α] (inst : Fintype (Sym2 α) := Sym2.instFintype) :
    (univ : Finset α).sym2 = univ := by
  ext
  simp only [mem_sym2_iff, mem_univ, implies_true]

@[simp, mono]
/--
theorem `sym2_mono` / 定理 `sym2_mono`

English:
theorem sym2_mono
  given: (h : s subseteq t)
  statement: s.sym2 subseteq t.sym2
  proof: by
  grind

中文:
定理 sym2_mono
  条件: (h : s subseteq t)
  结论: s.sym2 subseteq t.sym2
  证明: by
  grind
-/
theorem sym2_mono (h : s subseteq t) : s.sym2 subseteq t.sym2 := by
  grind

/--
theorem `monotone_sym2` / 定理 `monotone_sym2`

English:
theorem monotone_sym2
  statement: Monotone (Finset.sym2 : Finset α -> _)
  proof: fun _ _ => sym2_mono

中文:
定理 monotone_sym2
  结论: 递增 (有限集.sym2 : 有限集 α -> _)
  证明: fun _ _ => sym2_mono

Depends on / 依赖: sym2_mono
-/
theorem monotone_sym2 : Monotone (Finset.sym2 : Finset α -> _) := fun _ _ => sym2_mono

/--
theorem `injective_sym2` / 定理 `injective_sym2`

English:
theorem injective_sym2
  statement: Function.Injective (Finset.sym2 : Finset α -> _)
  proof: by
  intro s t h
  ext x
  simpa using congr(s(x, x) in $h)

中文:
定理 injective_sym2
  结论: 函数.单射 (有限集.sym2 : 有限集 α -> _)
  证明: by
  intro s t h
  ext x
  simpa using congr(s(x, x) in $h)
-/
theorem injective_sym2 : Function.Injective (Finset.sym2 : Finset α -> _) := by
  intro s t h
  ext x
  simpa using congr(s(x, x) in $h)

/--
theorem `strictMono_sym2` / 定理 `strictMono_sym2`

English:
theorem strictMono_sym2
  statement: StrictMono (Finset.sym2 : Finset α -> _)
  proof: monotone_sym2.strictMono_of_injective injective_sym2

中文:
定理 strictMono_sym2
  结论: 严格递增 (有限集.sym2 : 有限集 α -> _)
  证明: monotone_sym2.strictMono_of_injective injective_sym2

Depends on / 依赖: injective_sym2, monotone_sym2, monotone_sym2.strictMono_of_injective, strictMono_of_injective
-/
theorem strictMono_sym2 : StrictMono (Finset.sym2 : Finset α -> _) :=
  monotone_sym2.strictMono_of_injective injective_sym2

/--
theorem `sym2_toFinset` / 定理 `sym2_toFinset`

English:
theorem sym2_toFinset
  given: [DecidableEq α] (m : Multiset α)
  proof: by
  ext z
  refine z.ind fun x y => ?_
  simp only [mk_mem_sym2_iff, Multiset.mem_toFinset, Multiset.mk_mem_sym2_iff]

@[simp]

中文:
定理 sym2_toFinset
  条件: [DecidableEq α] (m : Multiset α)
  证明: by
  ext z
  refine z.ind fun x y => ?_
  simp only [mk_mem_sym2_iff, Multiset.mem_toFinset, Multiset.mk_mem_sym2_iff]

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_toFinset, Multiset.mk_mem_sym2_iff, mem_toFinset, mk_mem_sym2_iff, z.ind
-/
theorem sym2_toFinset [DecidableEq α] (m : Multiset α) :
    m.toFinset.sym2 = m.sym2.toFinset := by
  ext z
  refine z.ind fun x y => ?_
  simp only [mk_mem_sym2_iff, Multiset.mem_toFinset, Multiset.mk_mem_sym2_iff]

@[simp]
/--
theorem `sym2_empty` / 定理 `sym2_empty`

English:
theorem sym2_empty
  statement: (∅ : Finset α).sym2 = ∅
  proof: rfl

@[simp]

中文:
定理 sym2_empty
  结论: (∅ : 有限集 α).sym2 = ∅
  证明: rfl

@[simp]
-/
theorem sym2_empty : (∅ : Finset α).sym2 = ∅ := rfl

@[simp]
/--
theorem `sym2_eq_empty` / 定理 `sym2_eq_empty`

English:
theorem sym2_eq_empty
  statement: s.sym2 = ∅ ↔ s = ∅
  proof: by
  rw [← val_eq_zero]; rw [sym2_val]; rw [Multiset.sym2_eq_zero_iff]; rw [val_eq_zero]

@[simp]

中文:
定理 sym2_eq_empty
  结论: s.sym2 = ∅ ↔ s = ∅
  证明: by
  rw [← val_eq_zero]; rw [sym2_val]; rw [Multiset.sym2_eq_zero_iff]; rw [val_eq_zero]

@[simp]

Depends on / 依赖: Multiset, Multiset.sym2_eq_zero_iff, sym2_eq_zero_iff, sym2_val, val_eq_zero
-/
theorem sym2_eq_empty : s.sym2 = ∅ ↔ s = ∅ := by
  rw [← val_eq_zero]; rw [sym2_val]; rw [Multiset.sym2_eq_zero_iff]; rw [val_eq_zero]

@[simp]
/--
theorem `sym2_nonempty` / 定理 `sym2_nonempty`

English:
theorem sym2_nonempty
  statement: s.sym2.Nonempty ↔ s.Nonempty
  proof: by
  contrapose!; exact sym2_eq_empty

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.sym2⟩ := sym2_nonempty

@[simp]

中文:
定理 sym2_nonempty
  结论: s.sym2.非空 ↔ s.非空
  证明: by
  contrapose!; exact sym2_eq_empty

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.sym2⟩ := sym2_nonempty

@[simp]

Depends on / 依赖: contrapose, sym2_eq_empty
-/
theorem sym2_nonempty : s.sym2.Nonempty ↔ s.Nonempty := by
  contrapose!; exact sym2_eq_empty

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.sym2⟩ := sym2_nonempty

@[simp]
/--
theorem `sym2_singleton` / 定理 `sym2_singleton`

English:
theorem sym2_singleton
  given: (a : α)
  statement: ({a} : Finset α).sym2 = {Sym2.diag a}
  proof: rfl

中文:
定理 sym2_singleton
  条件: (a : α)
  结论: ({a} : 有限集 α).sym2 = {Sym2.diag a}
  证明: rfl
-/
theorem sym2_singleton (a : α) : ({a} : Finset α).sym2 = {Sym2.diag a} := rfl

/--
theorem `card_sym2` / 定理 `card_sym2`

English:
theorem card_sym2
  given: (s : Finset α)
  statement: s.sym2.card = Nat.choose (s.card + 1) 2
  proof: by
  rw [card_def]; rw [sym2_val]; rw [Multiset.card_sym2]; rw [← card_def]

中文:
定理 card_sym2
  条件: (s : 有限集 α)
  结论: s.sym2.card = 自然数.choose (s.card + 1) 2
  证明: by
  rw [card_def]; rw [sym2_val]; rw [Multiset.card_sym2]; rw [← card_def]

Depends on / 依赖: Multiset, Multiset.card_sym2, card_def, card_sym2, sym2_val
-/
theorem card_sym2 (s : Finset α) : s.sym2.card = Nat.choose (s.card + 1) 2 := by
  rw [card_def]; rw [sym2_val]; rw [Multiset.card_sym2]; rw [← card_def]

end

variable {s t : Finset α} {a b : α}

/--
theorem `sym2_eq_image` / 定理 `sym2_eq_image`

English:
theorem sym2_eq_image
  given: [DecidableEq α]
  statement: s.sym2 = (s ×ˢ s).image Sym2.mk.uncurry
  proof: by
  ext ⟨a, b⟩; simp; grind

中文:
定理 sym2_eq_image
  条件: [DecidableEq α]
  结论: s.sym2 = (s ×ˢ s).像 Sym2.mk.uncurry
  证明: by
  ext ⟨a, b⟩; simp; grind
-/
theorem sym2_eq_image [DecidableEq α] : s.sym2 = (s ×ˢ s).image Sym2.mk.uncurry := by
  ext ⟨a, b⟩; simp; grind

/--
theorem `isDiag_mk_of_mem_diag` / 定理 `isDiag_mk_of_mem_diag`

English:
theorem isDiag_mk_of_mem_diag
  given: {a b : α} (h : (a, b) in s.diag)
  statement: s(a, b).IsDiag
  proof: by
  simp at *; grind

中文:
定理 isDiag_mk_of_mem_diag
  条件: {a b : α} (h : (a, b) in s.diag)
  结论: s(a, b).IsDiag
  证明: by
  simp at *; grind
-/
theorem isDiag_mk_of_mem_diag {a b : α} (h : (a, b) in s.diag) : s(a, b).IsDiag := by
  simp at *; grind

/--
theorem `not_isDiag_mk_of_mem_offDiag` / 定理 `not_isDiag_mk_of_mem_offDiag`

English:
theorem not_isDiag_mk_of_mem_offDiag
  given: {a b : α} (h : (a, b) in s.offDiag)
  statement: ¬ s(a, b).IsDiag
  proof: by
  simp at *; grind

中文:
定理 not_isDiag_mk_of_mem_offDiag
  条件: {a b : α} (h : (a, b) in s.offDiag)
  结论: ¬ s(a, b).IsDiag
  证明: by
  simp at *; grind
-/
theorem not_isDiag_mk_of_mem_offDiag {a b : α} (h : (a, b) in s.offDiag) : ¬ s(a, b).IsDiag := by
  simp at *; grind

section Sym2

variable {m : Sym2 α}

@[simp]
/--
theorem `diag_mem_sym2_mem_iff` / 定理 `diag_mem_sym2_mem_iff`

English:
theorem diag_mem_sym2_mem_iff
  statement: (forall b, b in Sym2.diag a -> b in s) ↔ a in s
  proof: by
  rw [← mem_sym2_iff]
exact mk_mem_sym2_iff.trans and_self_iff

中文:
定理 diag_mem_sym2_mem_iff
  结论: (对任意 b, b in Sym2.diag a -> b in s) ↔ a in s
  证明: by
  rw [← mem_sym2_iff]
exact mk_mem_sym2_iff.trans and_self_iff

Depends on / 依赖: and_self_iff, mem_sym2_iff, mk_mem_sym2_iff, mk_mem_sym2_iff.trans
-/
theorem diag_mem_sym2_mem_iff : (forall b, b in Sym2.diag a -> b in s) ↔ a in s := by
  rw [← mem_sym2_iff]
exact mk_mem_sym2_iff.trans and_self_iff

/--
theorem `diag_mem_sym2_iff` / 定理 `diag_mem_sym2_iff`

English:
theorem diag_mem_sym2_iff
  statement: Sym2.diag a in s.sym2 ↔ a in s
  proof: by simp [diag_mem_sym2_mem_iff]

中文:
定理 diag_mem_sym2_iff
  结论: Sym2.diag a in s.sym2 ↔ a in s
  证明: by simp [diag_mem_sym2_mem_iff]

Depends on / 依赖: diag_mem_sym2_mem_iff
-/
theorem diag_mem_sym2_iff : Sym2.diag a in s.sym2 ↔ a in s := by simp [diag_mem_sym2_mem_iff]

/--
theorem `image_diag_union_image_offDiag` / 定理 `image_diag_union_image_offDiag`

English:
theorem image_diag_union_image_offDiag
  given: [DecidableEq α]
  proof: by
  rw [← image_union]; rw [diag_union_offDiag]; rw [sym2_eq_image]

中文:
定理 image_diag_union_image_offDiag
  条件: [DecidableEq α]
  证明: by
  rw [← image_union]; rw [diag_union_offDiag]; rw [sym2_eq_image]

Depends on / 依赖: diag_union_offDiag, image_union, sym2_eq_image
-/
theorem image_diag_union_image_offDiag [DecidableEq α] :
    s.diag.image Sym2.mk.uncurry union s.offDiag.image Sym2.mk.uncurry = s.sym2 := by
  rw [← image_union]; rw [diag_union_offDiag]; rw [sym2_eq_image]

end Sym2

section Sym

variable [DecidableEq α] {n : Nat}

-- @[simp]
/--
theorem `sym_empty` / 定理 `sym_empty`

English:
theorem sym_empty
  given: (n : Nat)
  statement: (∅ : Finset α).sym (n + 1) = ∅
  proof: rfl

中文:
定理 sym_empty
  条件: (n : 自然数)
  结论: (∅ : 有限集 α).sym (n + 1) = ∅
  证明: rfl
-/
theorem sym_empty (n : Nat) : (∅ : Finset α).sym (n + 1) = ∅ := rfl

/--
theorem `replicate_mem_sym` / 定理 `replicate_mem_sym`

English:
theorem replicate_mem_sym
  given: (ha : a in s) (n : Nat)
  statement: Sym.replicate n a in s.sym n
  proof: mem_sym_iff.2 fun b hb => by rwa [(Sym.mem_replicate.1 hb).2]

中文:
定理 replicate_mem_sym
  条件: (ha : a in s) (n : 自然数)
  结论: Sym.replicate n a in s.sym n
  证明: mem_sym_iff.2 fun b hb => by rwa [(Sym.mem_replicate.1 hb).2]

Depends on / 依赖: Sym.mem_replicate, mem_replicate, mem_sym_iff
-/
theorem replicate_mem_sym (ha : a in s) (n : Nat) : Sym.replicate n a in s.sym n :=
  mem_sym_iff.2 fun b hb => by rwa [(Sym.mem_replicate.1 hb).2]

/--
theorem `Nonempty.sym` / 定理 `Nonempty.sym`

English:
theorem Nonempty.sym
  given: (h : s.Nonempty) (n : Nat)
  statement: (s.sym n).Nonempty
  proof: let ⟨_a, ha⟩ := h
  ⟨_, replicate_mem_sym ha n⟩

@[simp]

中文:
定理 非空.sym
  条件: (h : s.非空) (n : 自然数)
  结论: (s.sym n).非空
  证明: let ⟨_a, ha⟩ := h
  ⟨_, replicate_mem_sym ha n⟩

@[simp]
-/
protected theorem Nonempty.sym (h : s.Nonempty) (n : Nat) : (s.sym n).Nonempty :=
  let ⟨_a, ha⟩ := h
  ⟨_, replicate_mem_sym ha n⟩

@[simp]
/--
theorem `sym_singleton` / 定理 `sym_singleton`

English:
theorem sym_singleton
  given: (a : α) (n : Nat)
  statement: ({a} : Finset α).sym n = {Sym.replicate n a}
  proof: eq_singleton_iff_unique_mem.2
    ⟨replicate_mem_sym (mem_singleton.2 rfl) _, fun _s hs =>
Sym.eq_replicate_iff.2 fun _b hb => eq_of_mem_singleton mem_sym_iff.1 hs _ hb⟩

中文:
定理 sym_singleton
  条件: (a : α) (n : 自然数)
  结论: ({a} : 有限集 α).sym n = {Sym.replicate n a}
  证明: eq_singleton_iff_unique_mem.2
    ⟨replicate_mem_sym (mem_singleton.2 rfl) _, fun _s hs =>
Sym.eq_replicate_iff.2 fun _b hb => eq_of_mem_singleton mem_sym_iff.1 hs _ hb⟩

Depends on / 依赖: Sym.eq_replicate_iff, eq_of_mem_singleton, eq_replicate_iff, eq_singleton_iff_unique_mem, mem_singleton, mem_sym_iff, replicate_mem_sym
-/
theorem sym_singleton (a : α) (n : Nat) : ({a} : Finset α).sym n = {Sym.replicate n a} :=
  eq_singleton_iff_unique_mem.2
    ⟨replicate_mem_sym (mem_singleton.2 rfl) _, fun _s hs =>
Sym.eq_replicate_iff.2 fun _b hb => eq_of_mem_singleton mem_sym_iff.1 hs _ hb⟩

/--
theorem `eq_empty_of_sym_eq_empty` / 定理 `eq_empty_of_sym_eq_empty`

English:
theorem eq_empty_of_sym_eq_empty
  given: (h : s.sym n = ∅)
  statement: s = ∅
  proof: by
  contrapose! h; exact h.sym _

@[simp]

中文:
定理 eq_empty_of_sym_eq_empty
  条件: (h : s.sym n = ∅)
  结论: s = ∅
  证明: by
  contrapose! h; exact h.sym _

@[simp]

Depends on / 依赖: contrapose, h.sym
-/
theorem eq_empty_of_sym_eq_empty (h : s.sym n = ∅) : s = ∅ := by
  contrapose! h; exact h.sym _

@[simp]
/--
theorem `sym_eq_empty` / 定理 `sym_eq_empty`

English:
theorem sym_eq_empty
  statement: s.sym n = ∅ ↔ n != 0 ∧ s = ∅
  proof: by
  cases n
  · exact iff_of_false (singleton_ne_empty _) fun h => (h.1 rfl).elim
  · refine ⟨fun h => ⟨Nat.succ_ne_zero _, eq_empty_of_sym_eq_empty h⟩, ?_⟩
    rintro ⟨_, rfl⟩
    exact sym_empty _

@[simp]

中文:
定理 sym_eq_empty
  结论: s.sym n = ∅ ↔ n != 0 ∧ s = ∅
  证明: by
  cases n
  · exact iff_of_false (singleton_ne_empty _) fun h => (h.1 rfl).elim
  · refine ⟨fun h => ⟨Nat.succ_ne_zero _, eq_empty_of_sym_eq_empty h⟩, ?_⟩
    rintro ⟨_, rfl⟩
    exact sym_empty _

@[simp]

Depends on / 依赖: Nat.succ_ne_zero, eq_empty_of_sym_eq_empty, iff_of_false, singleton_ne_empty, succ_ne_zero, sym_empty
-/
theorem sym_eq_empty : s.sym n = ∅ ↔ n != 0 ∧ s = ∅ := by
  cases n
  · exact iff_of_false (singleton_ne_empty _) fun h => (h.1 rfl).elim
  · refine ⟨fun h => ⟨Nat.succ_ne_zero _, eq_empty_of_sym_eq_empty h⟩, ?_⟩
    rintro ⟨_, rfl⟩
    exact sym_empty _

@[simp]
/--
theorem `sym_nonempty` / 定理 `sym_nonempty`

English:
theorem sym_nonempty
  statement: (s.sym n).Nonempty ↔ n = 0 ∨ s.Nonempty
  proof: by
  contrapose!; exact sym_eq_empty

@[simp]

中文:
定理 sym_nonempty
  结论: (s.sym n).非空 ↔ n = 0 ∨ s.非空
  证明: by
  contrapose!; exact sym_eq_empty

@[simp]

Depends on / 依赖: contrapose, sym_eq_empty
-/
theorem sym_nonempty : (s.sym n).Nonempty ↔ n = 0 ∨ s.Nonempty := by
  contrapose!; exact sym_eq_empty

@[simp]
/--
theorem `sym_univ` / 定理 `sym_univ`

English:
theorem sym_univ
  given: [Fintype α] (n : Nat)
  statement: (univ : Finset α).sym n = univ
  proof: eq_univ_iff_forall.2 fun _s => mem_sym_iff.2 fun _a _ => mem_univ _

@[simp]

中文:
定理 sym_univ
  条件: [有限类型 α] (n : 自然数)
  结论: (univ : 有限集 α).sym n = univ
  证明: eq_univ_iff_forall.2 fun _s => mem_sym_iff.2 fun _a _ => mem_univ _

@[simp]

Depends on / 依赖: eq_univ_iff_forall, mem_sym_iff, mem_univ
-/
theorem sym_univ [Fintype α] (n : Nat) : (univ : Finset α).sym n = univ :=
  eq_univ_iff_forall.2 fun _s => mem_sym_iff.2 fun _a _ => mem_univ _

@[simp]
/--
theorem `sym_mono` / 定理 `sym_mono`

English:
theorem sym_mono
  given: (h : s subseteq t) (n : Nat)
  statement: s.sym n subseteq t.sym n
  proof: fun _m hm =>
mem_sym_iff.2 fun _a ha => h mem_sym_iff.1 hm _ ha

@[simp]

中文:
定理 sym_mono
  条件: (h : s subseteq t) (n : 自然数)
  结论: s.sym n subseteq t.sym n
  证明: fun _m hm =>
mem_sym_iff.2 fun _a ha => h mem_sym_iff.1 hm _ ha

@[simp]
-/
theorem sym_mono (h : s subseteq t) (n : Nat) : s.sym n subseteq t.sym n := fun _m hm =>
mem_sym_iff.2 fun _a ha => h mem_sym_iff.1 hm _ ha

@[simp]
/--
theorem `sym_inter` / 定理 `sym_inter`

English:
theorem sym_inter
  given: (s t : Finset α) (n : Nat)
  statement: (s inter t).sym n = s.sym n inter t.sym n
  proof: by
  ext m
  simp only [mem_inter, mem_sym_iff, imp_and, forall_and]

@[simp]

中文:
定理 sym_inter
  条件: (s t : 有限集 α) (n : 自然数)
  结论: (s inter t).sym n = s.sym n inter t.sym n
  证明: by
  ext m
  simp only [mem_inter, mem_sym_iff, imp_and, forall_and]

@[simp]

Depends on / 依赖: forall_and, imp_and, mem_inter, mem_sym_iff
-/
theorem sym_inter (s t : Finset α) (n : Nat) : (s inter t).sym n = s.sym n inter t.sym n := by
  ext m
  simp only [mem_inter, mem_sym_iff, imp_and, forall_and]

@[simp]
/--
theorem `sym_union` / 定理 `sym_union`

English:
theorem sym_union
  given: (s t : Finset α) (n : Nat)
  statement: s.sym n union t.sym n subseteq (s union t).sym n
  proof: union_subset (sym_mono subset_union_left n) (sym_mono subset_union_right n)

中文:
定理 sym_union
  条件: (s t : 有限集 α) (n : 自然数)
  结论: s.sym n union t.sym n subseteq (s union t).sym n
  证明: union_subset (sym_mono subset_union_left n) (sym_mono subset_union_right n)

Depends on / 依赖: subset_union_left, subset_union_right, sym_mono, union_subset
-/
theorem sym_union (s t : Finset α) (n : Nat) : s.sym n union t.sym n subseteq (s union t).sym n :=
  union_subset (sym_mono subset_union_left n) (sym_mono subset_union_right n)

/--
theorem `sym_fill_mem` / 定理 `sym_fill_mem`

English:
theorem sym_fill_mem
  given: (a : α) {i : Fin (n + 1)} {m : Sym α (n - i)} (h : m in s.sym (n - i))
  proof: mem_sym_iff.2 fun b hb =>
mem_insert.2 (Sym.mem_fill_iff.1 hb).imp And.right mem_sym_iff.1 h b

中文:
定理 sym_fill_mem
  条件: (a : α) {i : 有限集 (n + 1)} {m : Sym α (n - i)} (h : m in s.sym (n - i))
  证明: mem_sym_iff.2 fun b hb =>
mem_insert.2 (Sym.mem_fill_iff.1 hb).imp And.right mem_sym_iff.1 h b

Depends on / 依赖: And.right, Sym.mem_fill_iff, mem_fill_iff, mem_insert, mem_sym_iff
-/
theorem sym_fill_mem (a : α) {i : Fin (n + 1)} {m : Sym α (n - i)} (h : m in s.sym (n - i)) :
    m.fill a i in (insert a s).sym n :=
  mem_sym_iff.2 fun b hb =>
mem_insert.2 (Sym.mem_fill_iff.1 hb).imp And.right mem_sym_iff.1 h b

/--
theorem `sym_filterNe_mem` / 定理 `sym_filterNe_mem`

English:
theorem sym_filterNe_mem
  given: {m : Sym α n} (a : α) (h : m in s.sym n)
  proof: mem_sym_iff.2 fun b H =>
mem_erase.2 (Multiset.mem_filter.1 H).symm.imp Ne.symm mem_sym_iff.1 h b

中文:
定理 sym_filterNe_mem
  条件: {m : Sym α n} (a : α) (h : m in s.sym n)
  证明: mem_sym_iff.2 fun b H =>
mem_erase.2 (Multiset.mem_filter.1 H).symm.imp Ne.symm mem_sym_iff.1 h b

Depends on / 依赖: Multiset, Multiset.mem_filter, Ne.symm, mem_erase, mem_filter, mem_sym_iff, symm.imp
-/
theorem sym_filterNe_mem {m : Sym α n} (a : α) (h : m in s.sym n) :
    (m.filterNe a).2 in (Finset.erase s a).sym (n - (m.filterNe a).1) :=
  mem_sym_iff.2 fun b H =>
mem_erase.2 (Multiset.mem_filter.1 H).symm.imp Ne.symm mem_sym_iff.1 h b

/-- If `a` does not belong to the finset `s`, then the `n`th symmetric power of `{a} ∪ s` is
  in 1-1 correspondence with the disjoint union of the `n - i`th symmetric powers of `s`,
  for `0 ≤ i ≤ n`. -/
@[simps]
/--
Definition of `symInsertEquiv` / `symInsertEquiv` 的定义

English:
definition symInsertEquiv
  signature: (h : a ∉ s)
  body: ⟨_, (m.1.filterNe a).2, by convert! sym_filterNe_mem a m.2; rw [erase_insert h]⟩
  invFun m := ⟨m.2.1.fill a m.1, sym_fill_mem a m.2.2⟩
left_inv m := Subtype.ext m.1.fill_filterNe a
  right_inv := fun ⟨i, m, hm⟩ => by
    refine Function.Injective.sigma_map (β₂ := ?_) (f₂ := ?_)
        (Function.in

中文:
定义 symInsertEquiv
  签名: (h : a ∉ s)
  定义体: ⟨_, (m.1.filterNe a).2, by convert! sym_filterNe_mem a m.2; rw [erase_insert h]⟩
  invFun m := ⟨m.2.1.fill a m.1, sym_fill_mem a m.2.2⟩
left_inv m := Subtype.ext m.1.fill_filterNe a
  right_inv := fun ⟨i, m, hm⟩ => by
    refine Function.Injective.sigma_map (β₂ := ?_) (f₂ := ?_)
        (Function.in

Depends on / 依赖: M.corec, M.dest, appendFun, convert, erase_insert, filterNe, sym_filterNe_mem
-/
def symInsertEquiv (h : a ∉ s) : (insert a s).sym n ≃ Σ i : Fin (n + 1), s.sym (n - i) where
  toFun m := ⟨_, (m.1.filterNe a).2, by convert! sym_filterNe_mem a m.2; rw [erase_insert h]⟩
  invFun m := ⟨m.2.1.fill a m.1, sym_fill_mem a m.2.2⟩
left_inv m := Subtype.ext m.1.fill_filterNe a
  right_inv := fun ⟨i, m, hm⟩ => by
    refine Function.Injective.sigma_map (β₂ := ?_) (f₂ := ?_)
        (Function.injective_id) (fun i => ?_) ?_
    · exact fun i => Sym α (n - i)
    swap
    · exact Subtype.coe_injective
    refine Eq.trans ?_ (Sym.filter_ne_fill a _ ?_)
    exacts [rfl, h ∘ mem_sym_iff.1 hm a]

@[to_additive]
/--
theorem `val_prod_eq_prod_count_pow` / 定理 `val_prod_eq_prod_count_pow`

English:
theorem val_prod_eq_prod_count_pow
  statement: [CommMonoid α] {n : Nat} {k : Sym α n}
  proof: by
  rw [Finset.prod_multiset_count_of_subset _ s]
  · apply Finset.prod_congr rfl (by simp)
  intro x hx
  simp only [Sym.val_eq_coe, Multiset.mem_toFinset, Sym.mem_coe] at hx
  simp only [Finset.mem_sym_iff] at hk
  exact hk x hx

中文:
定理 val_prod_eq_prod_count_pow
  结论: [交换幺半群 α] {n : 自然数} {k : Sym α n}
  证明: by
  rw [Finset.prod_multiset_count_of_subset _ s]
  · apply Finset.prod_congr rfl (by simp)
  intro x hx
  simp only [Sym.val_eq_coe, Multiset.mem_toFinset, Sym.mem_coe] at hx
  simp only [Finset.mem_sym_iff] at hk
  exact hk x hx

Depends on / 依赖: Finset, Finset.mem_sym_iff, Finset.prod_congr, Finset.prod_multiset_count_of_subset, Multiset, Multiset.mem_toFinset, Sym.mem_coe, Sym.val_eq_coe, mem_coe, mem_sym_iff, mem_toFinset, prod_congr, prod_multiset_count_of_subset, symm.trans, val_eq_coe
-/
theorem val_prod_eq_prod_count_pow [CommMonoid α] {n : Nat} {k : Sym α n}
    {s : Finset α} (hk : k in s.sym n) :
    k.val.prod = ∏ d in s, d ^ Multiset.count d k := by
  rw [Finset.prod_multiset_count_of_subset _ s]
  · apply Finset.prod_congr rfl (by simp)
  intro x hx
  simp only [Sym.val_eq_coe, Multiset.mem_toFinset, Sym.mem_coe] at hx
  simp only [Finset.mem_sym_iff] at hk
  exact hk x hx

end Sym

end Finset
