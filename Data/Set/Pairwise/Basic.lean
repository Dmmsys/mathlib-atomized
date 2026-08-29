/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Pairwise
public import Mathlib.Logic.Relation

/-!
# Relations holding pairwise

This file develops pairwise relations and defines pairwise disjoint indexed sets.

We also prove many basic facts about `Pairwise`. It is possible that an intermediate file,
with more imports than `Logic.Pairwise` but not importing `Data.Set.Function` would be appropriate
to hold many of these basic facts.

## Main declarations

* `Set.PairwiseDisjoint`: `s.PairwiseDisjoint f` states that images under `f` of distinct elements
  of `s` are either equal or `Disjoint`.

## Notes

The spelling `s.PairwiseDisjoint id` is preferred over `s.Pairwise Disjoint` to permit dot notation
on `Set.PairwiseDisjoint`, even though the latter unfolds to something nicer.
-/

@[expose] public section


open Function Order Set

variable {α β γ ι ι' : Type*} {r p : α -> α -> Prop}

section Pairwise

variable {f g : ι -> α} {s t : Set α} {a b : α}

/--
theorem `pairwise_on_bool` / 定理 `pairwise_on_bool`

English:
theorem pairwise_on_bool
  given: [Std.Symm r] {a b : α}
  statement: Pairwise (r on fun c => cond c a b) ↔ r a b
  proof: by
  simpa [Pairwise, Function.onFun] using symm

中文:
定理 pairwise_on_bool
  条件: [Std.Symm r] {a b : α}
  结论: 两两 (r on fun c => cond c a b) ↔ r a b
  证明: by
  simpa [Pairwise, Function.onFun] using symm

Depends on / 依赖: Function, Function.onFun, Pairwise
-/
theorem pairwise_on_bool [Std.Symm r] {a b : α} : Pairwise (r on fun c => cond c a b) ↔ r a b := by
  simpa [Pairwise, Function.onFun] using symm

/--
theorem `pairwise_disjoint_on_bool` / 定理 `pairwise_disjoint_on_bool`

English:
theorem pairwise_disjoint_on_bool
  given: [PartialOrder α] [OrderBot α] {a b : α}
  proof: pairwise_on_bool

中文:
定理 pairwise_disjoint_on_bool
  条件: [偏序 α] [有底序 α] {a b : α}
  证明: pairwise_on_bool

Depends on / 依赖: pairwise_on_bool
-/
theorem pairwise_disjoint_on_bool [PartialOrder α] [OrderBot α] {a b : α} :
    Pairwise (Disjoint on fun c => cond c a b) ↔ Disjoint a b :=
  pairwise_on_bool

/--
theorem `Std.Symm.pairwise_on` / 定理 `Std.Symm.pairwise_on`

English:
theorem Std.Symm.pairwise_on
  given: [LinearOrder ι] [Std.Symm r] (f : ι -> α)
  proof: h hmn.ne
mpr h _m _n hmn := hmn.lt_or_gt.elim (@h _ _) fun h' => symm_of r h h'

@[deprecated (since := "2026-06-10")] alias Symmetric.pairwise_on := Std.Symm.pairwise_on

中文:
定理 Std.Symm.pairwise_on
  条件: [线性序 ι] [Std.Symm r] (f : ι -> α)
  证明: h hmn.ne
mpr h _m _n hmn := hmn.lt_or_gt.elim (@h _ _) fun h' => symm_of r h h'

@[deprecated (since := "2026-06-10")] alias Symmetric.pairwise_on := Std.Symm.pairwise_on

Depends on / 依赖: hmn.ne
-/
theorem Std.Symm.pairwise_on [LinearOrder ι] [Std.Symm r] (f : ι -> α) :
    Pairwise (r on f) ↔ forall ⦃m n⦄, m < n -> r (f m) (f n) where
  mp h _m _n hmn := h hmn.ne
mpr h _m _n hmn := hmn.lt_or_gt.elim (@h _ _) fun h' => symm_of r h h'

@[deprecated (since := "2026-06-10")] alias Symmetric.pairwise_on := Std.Symm.pairwise_on

/--
theorem `pairwise_disjoint_on` / 定理 `pairwise_disjoint_on`

English:
theorem pairwise_disjoint_on
  given: [PartialOrder α] [OrderBot α] [LinearOrder ι] (f : ι -> α)
  proof: Std.Symm.pairwise_on f

中文:
定理 pairwise_disjoint_on
  条件: [偏序 α] [有底序 α] [线性序 ι] (f : ι -> α)
  证明: Std.Symm.pairwise_on f

Depends on / 依赖: Std.Symm.pairwise_on, pairwise_on
-/
theorem pairwise_disjoint_on [PartialOrder α] [OrderBot α] [LinearOrder ι] (f : ι -> α) :
    Pairwise (Disjoint on f) ↔ forall ⦃m n⦄, m < n -> Disjoint (f m) (f n) :=
  Std.Symm.pairwise_on f

/--
theorem `pairwise_disjoint_mono` / 定理 `pairwise_disjoint_mono`

English:
theorem pairwise_disjoint_mono
  statement: [PartialOrder α] [OrderBot α] (hs : Pairwise (Disjoint on f))
  proof: hs.mono fun i j hij => Disjoint.mono (h i) (h j) hij

中文:
定理 pairwise_disjoint_mono
  结论: [偏序 α] [有底序 α] (hs : 两两 (Disjoint on f))
  证明: hs.mono fun i j hij => Disjoint.mono (h i) (h j) hij

Depends on / 依赖: Disjoint, Disjoint.mono, hs.mono
-/
theorem pairwise_disjoint_mono [PartialOrder α] [OrderBot α] (hs : Pairwise (Disjoint on f))
    (h : g <= f) : Pairwise (Disjoint on g) :=
  hs.mono fun i j hij => Disjoint.mono (h i) (h j) hij

/--
theorem `Pairwise.disjoint_extend_bot` / 定理 `Pairwise.disjoint_extend_bot`

English:
theorem Pairwise.disjoint_extend_bot
  statement: [PartialOrder γ] [OrderBot γ]
  proof: by
  intro b₁ b₂ hne
  rcases em (exists a₁, e a₁ = b₁) with ⟨a₁, rfl⟩ | hb₁
  · rcases em (exists a₂, e a₂ = b₂) with ⟨a₂, rfl⟩ | hb₂
    · simpa only [onFun, he.extend_apply] using! hf (ne_of_apply_ne e hne)
    · simpa only [onFun, extend_apply' _ _ _ hb₂] using! disjoint_bot_right
  · simpa only [onFun, extend_apply' _ _ _ hb₁] using! disjoint_bot_left

中文:
定理 两两.disjoint_extend_bot
  结论: [偏序 γ] [有底序 γ]
  证明: by
  intro b₁ b₂ hne
  rcases em (exists a₁, e a₁ = b₁) with ⟨a₁, rfl⟩ | hb₁
  · rcases em (exists a₂, e a₂ = b₂) with ⟨a₂, rfl⟩ | hb₂
    · simpa only [onFun, he.extend_apply] using! hf (ne_of_apply_ne e hne)
    · simpa only [onFun, extend_apply' _ _ _ hb₂] using! disjoint_bot_right
  · simpa only [onFun, extend_apply' _ _ _ hb₁] using! disjoint_bot_left

Depends on / 依赖: disjoint_bot_left, disjoint_bot_right, extend_apply, he.extend_apply, ne_of_apply_ne
-/
theorem Pairwise.disjoint_extend_bot [PartialOrder γ] [OrderBot γ]
    {e : α -> β} {f : α -> γ} (hf : Pairwise (Disjoint on f)) (he : FactorsThrough f e) :
    Pairwise (Disjoint on extend e f ⊥) := by
  intro b₁ b₂ hne
  rcases em (exists a₁, e a₁ = b₁) with ⟨a₁, rfl⟩ | hb₁
  · rcases em (exists a₂, e a₂ = b₂) with ⟨a₂, rfl⟩ | hb₂
    · simpa only [onFun, he.extend_apply] using! hf (ne_of_apply_ne e hne)
    · simpa only [onFun, extend_apply' _ _ _ hb₂] using! disjoint_bot_right
  · simpa only [onFun, extend_apply' _ _ _ hb₁] using! disjoint_bot_left

namespace Set

/--
theorem `Pairwise.mono` / 定理 `Pairwise.mono`

English:
theorem Pairwise.mono
  given: (h : t subseteq s) (hs : s.Pairwise r)
  statement: t.Pairwise r
  proof: fun _x xt _y yt => hs (h xt) (h yt)

中文:
定理 两两.mono
  条件: (h : t subseteq s) (hs : s.两两 r)
  结论: t.两两 r
  证明: fun _x xt _y yt => hs (h xt) (h yt)
-/
theorem Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.Pairwise r :=
  fun _x xt _y yt => hs (h xt) (h yt)

/--
theorem `Pairwise.mono'` / 定理 `Pairwise.mono'`

English:
theorem Pairwise.mono'
  given: (H : r <= p) (hr : s.Pairwise r)
  statement: s.Pairwise p
  proof: hr.imp H

中文:
定理 两两.mono'
  条件: (H : r <= p) (hr : s.两两 r)
  结论: s.两两 p
  证明: hr.imp H

Depends on / 依赖: hr.imp
-/
theorem Pairwise.mono' (H : r <= p) (hr : s.Pairwise r) : s.Pairwise p :=
  hr.imp H

/--
theorem `Pairwise.inter_left` / 定理 `Pairwise.inter_left`

English:
theorem Pairwise.inter_left
  given: (hs : s.Pairwise r) (t : Set α)
  statement: (s inter t).Pairwise r
  proof: hs.mono Set.inter_subset_left

中文:
定理 两两.inter_left
  条件: (hs : s.两两 r) (t : 集合 α)
  结论: (s inter t).两两 r
  证明: hs.mono Set.inter_subset_left

Depends on / 依赖: Set.inter_subset_left, hs.mono, inter_subset_left
-/
theorem Pairwise.inter_left (hs : s.Pairwise r) (t : Set α) : (s inter t).Pairwise r :=
  hs.mono Set.inter_subset_left

/--
theorem `Pairwise.inter_right` / 定理 `Pairwise.inter_right`

English:
theorem Pairwise.inter_right
  given: (hs : s.Pairwise r) (t : Set α)
  statement: (t inter s).Pairwise r
  proof: hs.mono Set.inter_subset_right

中文:
定理 两两.inter_right
  条件: (hs : s.两两 r) (t : 集合 α)
  结论: (t inter s).两两 r
  证明: hs.mono Set.inter_subset_right

Depends on / 依赖: Set.inter_subset_right, hs.mono, inter_subset_right
-/
theorem Pairwise.inter_right (hs : s.Pairwise r) (t : Set α) : (t inter s).Pairwise r :=
  hs.mono Set.inter_subset_right

/--
theorem `pairwise_top` / 定理 `pairwise_top`

English:
theorem pairwise_top
  given: (s : Set α)
  statement: s.Pairwise ⊤
  proof: pairwise_of_forall s _ fun _ _ => trivial

中文:
定理 pairwise_top
  条件: (s : 集合 α)
  结论: s.两两 ⊤
  证明: pairwise_of_forall s _ fun _ _ => trivial

Depends on / 依赖: pairwise_of_forall
-/
theorem pairwise_top (s : Set α) : s.Pairwise ⊤ :=
  pairwise_of_forall s _ fun _ _ => trivial

/--
theorem `Subsingleton.pairwise` / 定理 `Subsingleton.pairwise`

English:
theorem Subsingleton.pairwise
  given: (h : s.Subsingleton) (r : α -> α -> Prop)
  statement: s.Pairwise r
  proof: fun _x hx _y hy hne => (hne (h hx hy)).elim

@[simp]

中文:
定理 子单例.pairwise
  条件: (h : s.子单例) (r : α -> α -> 命题)
  结论: s.两两 r
  证明: fun _x hx _y hy hne => (hne (h hx hy)).elim

@[simp]
-/
protected theorem Subsingleton.pairwise (h : s.Subsingleton) (r : α -> α -> Prop) : s.Pairwise r :=
  fun _x hx _y hy hne => (hne (h hx hy)).elim

@[simp]
/--
theorem `pairwise_empty` / 定理 `pairwise_empty`

English:
theorem pairwise_empty
  given: (r : α -> α -> Prop)
  statement: (∅ : Set α).Pairwise r
  proof: subsingleton_empty.pairwise r

@[simp]

中文:
定理 pairwise_empty
  条件: (r : α -> α -> 命题)
  结论: (∅ : 集合 α).两两 r
  证明: subsingleton_empty.pairwise r

@[simp]

Depends on / 依赖: pairwise, subsingleton_empty, subsingleton_empty.pairwise
-/
theorem pairwise_empty (r : α -> α -> Prop) : (∅ : Set α).Pairwise r :=
  subsingleton_empty.pairwise r

@[simp]
/--
theorem `pairwise_singleton` / 定理 `pairwise_singleton`

English:
theorem pairwise_singleton
  given: (a : α) (r : α -> α -> Prop)
  statement: Set.Pairwise {a} r
  proof: subsingleton_singleton.pairwise r

中文:
定理 pairwise_singleton
  条件: (a : α) (r : α -> α -> 命题)
  结论: 集合.两两 {a} r
  证明: subsingleton_singleton.pairwise r

Depends on / 依赖: pairwise, subsingleton_singleton, subsingleton_singleton.pairwise
-/
theorem pairwise_singleton (a : α) (r : α -> α -> Prop) : Set.Pairwise {a} r :=
  subsingleton_singleton.pairwise r

/--
theorem `pairwise_iff_of_refl` / 定理 `pairwise_iff_of_refl`

English:
theorem pairwise_iff_of_refl
  given: [Std.Refl r]
  statement: s.Pairwise r ↔ forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> r a b
  proof: forall₄_congr fun _ _ _ _ => or_iff_not_imp_left.symm.trans or_iff_right_of_imp of_eq

alias ⟨Pairwise.of_refl, _⟩ := pairwise_iff_of_refl

中文:
定理 pairwise_iff_of_refl
  条件: [Std.Refl r]
  结论: s.两两 r ↔ 对任意 ⦃a⦄, a in s -> 对任意 ⦃b⦄, b in s -> r a b
  证明: forall₄_congr fun _ _ _ _ => or_iff_not_imp_left.symm.trans or_iff_right_of_imp of_eq

alias ⟨Pairwise.of_refl, _⟩ := pairwise_iff_of_refl

Depends on / 依赖: of_eq, or_iff_not_imp_left, or_iff_not_imp_left.symm.trans, or_iff_right_of_imp
-/
theorem pairwise_iff_of_refl [Std.Refl r] : s.Pairwise r ↔ forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> r a b :=
forall₄_congr fun _ _ _ _ => or_iff_not_imp_left.symm.trans or_iff_right_of_imp of_eq

alias ⟨Pairwise.of_refl, _⟩ := pairwise_iff_of_refl

/--
theorem `Nonempty.pairwise_iff_exists_forall` / 定理 `Nonempty.pairwise_iff_exists_forall`

English:
theorem Nonempty.pairwise_iff_exists_forall
  given: [IsEquiv α r] {s : Set ι} (hs : s.Nonempty)
  proof: by
  constructor
  · rcases hs with ⟨y, hy⟩
    refine fun H => ⟨f y, fun x hx => ?_⟩
    rcases eq_or_ne x y with (rfl | hne)
    · apply Std.Refl.refl
    · exact H hx hy hne
  · rintro ⟨z, hz⟩ x hx y hy _
    exact @IsTrans.trans α r _ (f x) z (f y) (hz _ hx) (symm <| hz _ hy)

中文:
定理 非空.pairwise_iff_存在_对任意
  条件: [Is等价 α r] {s : 集合 ι} (hs : s.非空)
  证明: by
  constructor
  · rcases hs with ⟨y, hy⟩
    refine fun H => ⟨f y, fun x hx => ?_⟩
    rcases eq_or_ne x y with (rfl | hne)
    · apply Std.Refl.refl
    · exact H hx hy hne
  · rintro ⟨z, hz⟩ x hx y hy _
    exact @IsTrans.trans α r _ (f x) z (f y) (hz _ hx) (symm <| hz _ hy)

Depends on / 依赖: IsTrans, IsTrans.trans, Std.Refl.refl, eq_or_ne
-/
theorem Nonempty.pairwise_iff_exists_forall [IsEquiv α r] {s : Set ι} (hs : s.Nonempty) :
    s.Pairwise (r on f) ↔ exists z, forall x in s, r (f x) z := by
  constructor
  · rcases hs with ⟨y, hy⟩
    refine fun H => ⟨f y, fun x hx => ?_⟩
    rcases eq_or_ne x y with (rfl | hne)
    · apply Std.Refl.refl
    · exact H hx hy hne
  · rintro ⟨z, hz⟩ x hx y hy _
    exact @IsTrans.trans α r _ (f x) z (f y) (hz _ hx) (symm <| hz _ hy)

/--
theorem `Nonempty.pairwise_eq_iff_exists_eq` / 定理 `Nonempty.pairwise_eq_iff_exists_eq`

English:
theorem Nonempty.pairwise_eq_iff_exists_eq
  given: {s : Set α} (hs : s.Nonempty) {f : α -> ι}
  proof: hs.pairwise_iff_exists_forall

中文:
定理 非空.pairwise_eq_iff_存在_eq
  条件: {s : 集合 α} (hs : s.非空) {f : α -> ι}
  证明: hs.pairwise_iff_exists_forall

Depends on / 依赖: X.carrier.str, carrier, hs.pairwise_iff_exists_forall, pairwise_iff_exists_forall
-/
theorem Nonempty.pairwise_eq_iff_exists_eq {s : Set α} (hs : s.Nonempty) {f : α -> ι} :
    (s.Pairwise fun x y => f x = f y) ↔ exists z, forall x in s, f x = z :=
  hs.pairwise_iff_exists_forall

/--
theorem `pairwise_iff_exists_forall` / 定理 `pairwise_iff_exists_forall`

English:
theorem pairwise_iff_exists_forall
  statement: [Nonempty ι] (s : Set α) (f : α -> ι) {r : ι -> ι -> Prop}
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  · exact hne.pairwise_iff_exists_forall

中文:
定理 pairwise_iff_存在_对任意
  结论: [非空 ι] (s : 集合 α) (f : α -> ι) {r : ι -> ι -> 命题}
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  · exact hne.pairwise_iff_exists_forall

Depends on / 依赖: eq_empty_or_nonempty, hne.pairwise_iff_exists_forall, pairwise_iff_exists_forall, s.eq_empty_or_nonempty
-/
theorem pairwise_iff_exists_forall [Nonempty ι] (s : Set α) (f : α -> ι) {r : ι -> ι -> Prop}
    [IsEquiv ι r] : s.Pairwise (r on f) ↔ exists z, forall x in s, r (f x) z := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  · exact hne.pairwise_iff_exists_forall

/--
theorem `pairwise_eq_iff_exists_eq` / 定理 `pairwise_eq_iff_exists_eq`

English:
theorem pairwise_eq_iff_exists_eq
  given: [Nonempty ι] (s : Set α) (f : α -> ι)
  proof: pairwise_iff_exists_forall s f

中文:
定理 pairwise_eq_iff_存在_eq
  条件: [非空 ι] (s : 集合 α) (f : α -> ι)
  证明: pairwise_iff_exists_forall s f

Depends on / 依赖: pairwise_iff_exists_forall
-/
theorem pairwise_eq_iff_exists_eq [Nonempty ι] (s : Set α) (f : α -> ι) :
    (s.Pairwise fun x y => f x = f y) ↔ exists z, forall x in s, f x = z :=
  pairwise_iff_exists_forall s f

/--
theorem `pairwise_union` / 定理 `pairwise_union`

English:
theorem pairwise_union
  proof: by
  grind [Set.Pairwise]

中文:
定理 pairwise_union
  证明: by
  grind [Set.Pairwise]

Depends on / 依赖: Pairwise, Set.Pairwise
-/
theorem pairwise_union :
    (s union t).Pairwise r ↔
    s.Pairwise r ∧ t.Pairwise r ∧ forall a in s, forall b in t, a != b -> r a b ∧ r b a := by
  grind [Set.Pairwise]

/--
theorem `pairwise_union_of_symm` / 定理 `pairwise_union_of_symm`

English:
theorem pairwise_union_of_symm
  given: [Std.Symm r]
  proof: pairwise_union.trans by simp only [Std.Symm.iff, and_self_iff]

@[deprecated (since := "2026-06-10")] alias pairwise_union_of_symmetric := pairwise_union_of_symm

中文:
定理 pairwise_union_of_symm
  条件: [Std.Symm r]
  证明: pairwise_union.trans by simp only [Std.Symm.iff, and_self_iff]

@[deprecated (since := "2026-06-10")] alias pairwise_union_of_symmetric := pairwise_union_of_symm

Depends on / 依赖: Std.Symm.iff, and_self_iff, pairwise_union, pairwise_union.trans
-/
theorem pairwise_union_of_symm [Std.Symm r] :
    (s union t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ forall a in s, forall b in t, a != b -> r a b :=
pairwise_union.trans by simp only [Std.Symm.iff, and_self_iff]

@[deprecated (since := "2026-06-10")] alias pairwise_union_of_symmetric := pairwise_union_of_symm

/--
theorem `pairwise_insert` / 定理 `pairwise_insert`

English:
theorem pairwise_insert
  proof: by
  simp only [insert_eq, pairwise_union, pairwise_singleton, true_and, mem_singleton_iff, forall_eq]

中文:
定理 pairwise_insert
  证明: by
  simp only [insert_eq, pairwise_union, pairwise_singleton, true_and, mem_singleton_iff, forall_eq]

Depends on / 依赖: forall_eq, insert_eq, mem_singleton_iff, pairwise_singleton, pairwise_union, true_and
-/
theorem pairwise_insert :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, a != b -> r a b ∧ r b a := by
  simp only [insert_eq, pairwise_union, pairwise_singleton, true_and, mem_singleton_iff, forall_eq]

/--
theorem `pairwise_insert_of_notMem` / 定理 `pairwise_insert_of_notMem`

English:
theorem pairwise_insert_of_notMem
  given: (ha : a ∉ s)
  proof: pairwise_insert.trans
and_congr_right' forall₂_congr fun b hb => by simp [(ne_of_mem_of_not_mem hb ha).symm]

中文:
定理 pairwise_insert_of_notMem
  条件: (ha : a ∉ s)
  证明: pairwise_insert.trans
and_congr_right' forall₂_congr fun b hb => by simp [(ne_of_mem_of_not_mem hb ha).symm]

Depends on / 依赖: and_congr_right, ne_of_mem_of_not_mem, pairwise_insert, pairwise_insert.trans
-/
theorem pairwise_insert_of_notMem (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, r a b ∧ r b a :=
pairwise_insert.trans
and_congr_right' forall₂_congr fun b hb => by simp [(ne_of_mem_of_not_mem hb ha).symm]

/--
theorem `Pairwise.insert` / 定理 `Pairwise.insert`

English:
theorem Pairwise.insert
  given: (hs : s.Pairwise r) (h : forall b in s, a != b -> r a b ∧ r b a)
  proof: pairwise_insert.2 ⟨hs, h⟩

中文:
定理 两两.insert
  条件: (hs : s.两两 r) (h : 对任意 b in s, a != b -> r a b ∧ r b a)
  证明: pairwise_insert.2 ⟨hs, h⟩
-/
protected theorem Pairwise.insert (hs : s.Pairwise r) (h : forall b in s, a != b -> r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  pairwise_insert.2 ⟨hs, h⟩

/--
theorem `Pairwise.insert_of_notMem` / 定理 `Pairwise.insert_of_notMem`

English:
theorem Pairwise.insert_of_notMem
  given: (ha : a ∉ s) (hs : s.Pairwise r) (h : forall b in s, r a b ∧ r b a)
  proof: (pairwise_insert_of_notMem ha).2 ⟨hs, h⟩

中文:
定理 两两.insert_of_notMem
  条件: (ha : a ∉ s) (hs : s.两两 r) (h : 对任意 b in s, r a b ∧ r b a)
  证明: (pairwise_insert_of_notMem ha).2 ⟨hs, h⟩

Depends on / 依赖: pairwise_insert_of_notMem
-/
theorem Pairwise.insert_of_notMem (ha : a ∉ s) (hs : s.Pairwise r) (h : forall b in s, r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  (pairwise_insert_of_notMem ha).2 ⟨hs, h⟩

/--
theorem `pairwise_insert_of_symm` / 定理 `pairwise_insert_of_symm`

English:
theorem pairwise_insert_of_symm
  given: [Std.Symm r]
  proof: by
  simp only [pairwise_insert, Std.Symm.iff a, and_self_iff]

@[deprecated (since := "2026-06-10")] alias pairwise_insert_of_symmetric := pairwise_insert_of_symm

中文:
定理 pairwise_insert_of_symm
  条件: [Std.Symm r]
  证明: by
  simp only [pairwise_insert, Std.Symm.iff a, and_self_iff]

@[deprecated (since := "2026-06-10")] alias pairwise_insert_of_symmetric := pairwise_insert_of_symm

Depends on / 依赖: Std.Symm.iff, and_self_iff, pairwise_insert
-/
theorem pairwise_insert_of_symm [Std.Symm r] :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, a != b -> r a b := by
  simp only [pairwise_insert, Std.Symm.iff a, and_self_iff]

@[deprecated (since := "2026-06-10")] alias pairwise_insert_of_symmetric := pairwise_insert_of_symm

/--
theorem `pairwise_insert_of_symm_of_notMem` / 定理 `pairwise_insert_of_symm_of_notMem`

English:
theorem pairwise_insert_of_symm_of_notMem
  given: [Std.Symm r] (ha : a ∉ s)
  proof: by
  simp only [pairwise_insert_of_notMem ha, Std.Symm.iff a, and_self_iff]

@[deprecated (since := "2026-06-10")]
alias pairwise_insert_of_symmetric_of_notMem := pairwise_insert_of_symm_of_notMem

中文:
定理 pairwise_insert_of_symm_of_notMem
  条件: [Std.Symm r] (ha : a ∉ s)
  证明: by
  simp only [pairwise_insert_of_notMem ha, Std.Symm.iff a, and_self_iff]

@[deprecated (since := "2026-06-10")]
alias pairwise_insert_of_symmetric_of_notMem := pairwise_insert_of_symm_of_notMem

Depends on / 依赖: Std.Symm.iff, and_self_iff, pairwise_insert_of_notMem
-/
theorem pairwise_insert_of_symm_of_notMem [Std.Symm r] (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, r a b := by
  simp only [pairwise_insert_of_notMem ha, Std.Symm.iff a, and_self_iff]

@[deprecated (since := "2026-06-10")]
alias pairwise_insert_of_symmetric_of_notMem := pairwise_insert_of_symm_of_notMem

/--
theorem `Pairwise.insert_of_symm` / 定理 `Pairwise.insert_of_symm`

English:
theorem Pairwise.insert_of_symm
  statement: [Std.Symm r] (hs : s.Pairwise r)
  proof: pairwise_insert_of_symm.mpr ⟨hs, h⟩

@[deprecated (since := "2026-06-10")] alias Pairwise.insert_of_symmetric := Pairwise.insert_of_symm

中文:
定理 两两.insert_of_symm
  结论: [Std.Symm r] (hs : s.两两 r)
  证明: pairwise_insert_of_symm.mpr ⟨hs, h⟩

@[deprecated (since := "2026-06-10")] alias Pairwise.insert_of_symmetric := Pairwise.insert_of_symm

Depends on / 依赖: pairwise_insert_of_symm, pairwise_insert_of_symm.mpr
-/
theorem Pairwise.insert_of_symm [Std.Symm r] (hs : s.Pairwise r)
    (h : forall b in s, a != b -> r a b) : (insert a s).Pairwise r :=
  pairwise_insert_of_symm.mpr ⟨hs, h⟩

@[deprecated (since := "2026-06-10")] alias Pairwise.insert_of_symmetric := Pairwise.insert_of_symm

/--
theorem `pairwise_pair` / 定理 `pairwise_pair`

English:
theorem pairwise_pair
  statement: Set.Pairwise {a, b} r ↔ a != b -> r a b ∧ r b a
  proof: by simp [pairwise_insert]

中文:
定理 pairwise_pair
  结论: 集合.两两 {a, b} r ↔ a != b -> r a b ∧ r b a
  证明: by simp [pairwise_insert]

Depends on / 依赖: pairwise_insert
-/
theorem pairwise_pair : Set.Pairwise {a, b} r ↔ a != b -> r a b ∧ r b a := by simp [pairwise_insert]

/--
theorem `pairwise_pair_of_symm` / 定理 `pairwise_pair_of_symm`

English:
theorem pairwise_pair_of_symm
  given: [Std.Symm r]
  statement: Set.Pairwise {a, b} r ↔ a != b -> r a b
  proof: by
  simp [pairwise_insert_of_symm]

@[deprecated (since := "2026-06-10")] alias pairwise_pair_of_symmetric := pairwise_pair_of_symm

中文:
定理 pairwise_pair_of_symm
  条件: [Std.Symm r]
  结论: 集合.两两 {a, b} r ↔ a != b -> r a b
  证明: by
  simp [pairwise_insert_of_symm]

@[deprecated (since := "2026-06-10")] alias pairwise_pair_of_symmetric := pairwise_pair_of_symm

Depends on / 依赖: pairwise_insert_of_symm
-/
theorem pairwise_pair_of_symm [Std.Symm r] : Set.Pairwise {a, b} r ↔ a != b -> r a b := by
  simp [pairwise_insert_of_symm]

@[deprecated (since := "2026-06-10")] alias pairwise_pair_of_symmetric := pairwise_pair_of_symm

/--
theorem `pairwise_univ` / 定理 `pairwise_univ`

English:
theorem pairwise_univ
  statement: (univ : Set α).Pairwise r ↔ Pairwise r
  proof: by
  simp only [Set.Pairwise, Pairwise, mem_univ, forall_const]

@[simp]

中文:
定理 pairwise_univ
  结论: (univ : 集合 α).两两 r ↔ 两两 r
  证明: by
  simp only [Set.Pairwise, Pairwise, mem_univ, forall_const]

@[simp]

Depends on / 依赖: Pairwise, Set.Pairwise, forall_const, mem_univ
-/
theorem pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise r := by
  simp only [Set.Pairwise, Pairwise, mem_univ, forall_const]

@[simp]
/--
theorem `pairwise_bot_iff` / 定理 `pairwise_bot_iff`

English:
theorem pairwise_bot_iff
  statement: s.Pairwise (⊥ : α -> α -> Prop) ↔ (s : Set α).Subsingleton
  proof: ⟨fun h _a ha _b hb => h.eq ha hb id, fun h => h.pairwise _⟩

alias ⟨Pairwise.subsingleton, _⟩ := pairwise_bot_iff

中文:
定理 pairwise_bot_iff
  结论: s.两两 (⊥ : α -> α -> 命题) ↔ (s : 集合 α).子单例
  证明: ⟨fun h _a ha _b hb => h.eq ha hb id, fun h => h.pairwise _⟩

alias ⟨Pairwise.subsingleton, _⟩ := pairwise_bot_iff

Depends on / 依赖: h.eq, h.pairwise, pairwise
-/
theorem pairwise_bot_iff : s.Pairwise (⊥ : α -> α -> Prop) ↔ (s : Set α).Subsingleton :=
  ⟨fun h _a ha _b hb => h.eq ha hb id, fun h => h.pairwise _⟩

alias ⟨Pairwise.subsingleton, _⟩ := pairwise_bot_iff

/--
lemma `injOn_iff_pairwise_ne` / 引理 `injOn_iff_pairwise_ne`

English:
lemma injOn_iff_pairwise_ne
  given: {s : Set ι}
  statement: InjOn f s ↔ s.Pairwise (f · != f ·)
  proof: by
  simp only [InjOn, Set.Pairwise, not_imp_not]

alias ⟨InjOn.pairwise_ne, _⟩ := injOn_iff_pairwise_ne

中文:
引理 injOn_iff_pairwise_ne
  条件: {s : 集合 ι}
  结论: 单射限制 f s ↔ s.两两 (f · != f ·)
  证明: by
  simp only [InjOn, Set.Pairwise, not_imp_not]

alias ⟨InjOn.pairwise_ne, _⟩ := injOn_iff_pairwise_ne

Depends on / 依赖: Pairwise, Set.Pairwise, not_imp_not
-/
lemma injOn_iff_pairwise_ne {s : Set ι} : InjOn f s ↔ s.Pairwise (f · != f ·) := by
  simp only [InjOn, Set.Pairwise, not_imp_not]

alias ⟨InjOn.pairwise_ne, _⟩ := injOn_iff_pairwise_ne

/--
theorem `Pairwise.image` / 定理 `Pairwise.image`

English:
theorem Pairwise.image
  given: {s : Set ι} (h : s.Pairwise (r on f))
  statement: (f '' s).Pairwise r
  proof: forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy hne => h hx hy ne_of_apply_ne _ hne

中文:
定理 两两.像
  条件: {s : 集合 ι} (h : s.两两 (r on f))
  结论: (f '' s).两两 r
  证明: forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy hne => h hx hy ne_of_apply_ne _ hne
-/
protected theorem Pairwise.image {s : Set ι} (h : s.Pairwise (r on f)) : (f '' s).Pairwise r :=
forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy hne => h hx hy ne_of_apply_ne _ hne

/--
theorem `InjOn.pairwise_image` / 定理 `InjOn.pairwise_image`

English:
theorem InjOn.pairwise_image
  given: {s : Set ι} (h : s.InjOn f)
  proof: by
  simp +contextual [h.eq_iff, Set.Pairwise]

中文:
定理 单射限制.pairwise_image
  条件: {s : 集合 ι} (h : s.单射限制 f)
  证明: by
  simp +contextual [h.eq_iff, Set.Pairwise]

Depends on / 依赖: Pairwise, Set.Pairwise, contextual, eq_iff, h.eq_iff
-/
theorem InjOn.pairwise_image {s : Set ι} (h : s.InjOn f) :
    (f '' s).Pairwise r ↔ s.Pairwise (r on f) := by
  simp +contextual [h.eq_iff, Set.Pairwise]

/--
lemma `_root_.Pairwise.range_pairwise` / 引理 `_root_.Pairwise.range_pairwise`

English:
lemma _root_.Pairwise.range_pairwise
  given: (hr : Pairwise (r on f))
  statement: (Set.range f).Pairwise r
  proof: image_univ ▸ (pairwise_univ.mpr hr).image

中文:
引理 _root_.两两.range_pairwise
  条件: (hr : 两两 (r on f))
  结论: (集合.range f).两两 r
  证明: image_univ ▸ (pairwise_univ.mpr hr).image

Depends on / 依赖: image_univ, pairwise_univ, pairwise_univ.mpr
-/
lemma _root_.Pairwise.range_pairwise (hr : Pairwise (r on f)) : (Set.range f).Pairwise r :=
  image_univ ▸ (pairwise_univ.mpr hr).image

end Set

end Pairwise

/--
theorem `pairwise_subtype_iff_pairwise_set` / 定理 `pairwise_subtype_iff_pairwise_set`

English:
theorem pairwise_subtype_iff_pairwise_set
  given: (s : Set α) (r : α -> α -> Prop)
  proof: by
  simp only [Pairwise, Set.Pairwise, SetCoe.forall, Ne, Subtype.ext_iff]

alias ⟨Pairwise.set_of_subtype, Set.Pairwise.subtype⟩ := pairwise_subtype_iff_pairwise_set

中文:
定理 pairwise_subtype_iff_pairwise_set
  条件: (s : 集合 α) (r : α -> α -> 命题)
  证明: by
  simp only [Pairwise, Set.Pairwise, SetCoe.forall, Ne, Subtype.ext_iff]

alias ⟨Pairwise.set_of_subtype, Set.Pairwise.subtype⟩ := pairwise_subtype_iff_pairwise_set

Depends on / 依赖: Pairwise, Set.Pairwise, SetCoe, SetCoe.forall, Subtype, Subtype.ext_iff, ext_iff
-/
theorem pairwise_subtype_iff_pairwise_set (s : Set α) (r : α -> α -> Prop) :
    (Pairwise fun (x : s) (y : s) => r x y) ↔ s.Pairwise r := by
  simp only [Pairwise, Set.Pairwise, SetCoe.forall, Ne, Subtype.ext_iff]

alias ⟨Pairwise.set_of_subtype, Set.Pairwise.subtype⟩ := pairwise_subtype_iff_pairwise_set

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s t : Set ι} {f g : ι -> α}

/--
Definition of `PairwiseDisjoint` / `PairwiseDisjoint` 的定义

English:
definition PairwiseDisjoint
  signature: (s : Set ι) (f : ι -> α)
  body: s.Pairwise (Disjoint on f)

中文:
定义 PairwiseDisjoint
  签名: (s : 集合 ι) (f : ι -> α)
  定义体: s.Pairwise (Disjoint on f)

Depends on / 依赖: Disjoint, Pairwise, s.Pairwise
-/
def PairwiseDisjoint (s : Set ι) (f : ι -> α) : Prop :=
  s.Pairwise (Disjoint on f)

/--
theorem `PairwiseDisjoint.subset` / 定理 `PairwiseDisjoint.subset`

English:
theorem PairwiseDisjoint.subset
  given: (ht : t.PairwiseDisjoint f) (h : s subseteq t)
  statement: s.PairwiseDisjoint f
  proof: Pairwise.mono h ht

中文:
定理 PairwiseDisjoint.subset
  条件: (ht : t.PairwiseDisjoint f) (h : s subseteq t)
  结论: s.PairwiseDisjoint f
  证明: Pairwise.mono h ht

Depends on / 依赖: Pairwise, Pairwise.mono
-/
theorem PairwiseDisjoint.subset (ht : t.PairwiseDisjoint f) (h : s subseteq t) : s.PairwiseDisjoint f :=
  Pairwise.mono h ht

/--
theorem `PairwiseDisjoint.mono_on` / 定理 `PairwiseDisjoint.mono_on`

English:
theorem PairwiseDisjoint.mono_on
  given: (hs : s.PairwiseDisjoint f) (h : forall ⦃i⦄, i in s -> g i <= f i)
  proof: fun _a ha _b hb hab => (hs ha hb hab).mono (h ha) (h hb)

中文:
定理 PairwiseDisjoint.mono_on
  条件: (hs : s.PairwiseDisjoint f) (h : 对任意 ⦃i⦄, i in s -> g i <= f i)
  证明: fun _a ha _b hb hab => (hs ha hb hab).mono (h ha) (h hb)
-/
theorem PairwiseDisjoint.mono_on (hs : s.PairwiseDisjoint f) (h : forall ⦃i⦄, i in s -> g i <= f i) :
    s.PairwiseDisjoint g := fun _a ha _b hb hab => (hs ha hb hab).mono (h ha) (h hb)

/--
theorem `PairwiseDisjoint.mono` / 定理 `PairwiseDisjoint.mono`

English:
theorem PairwiseDisjoint.mono
  given: (hs : s.PairwiseDisjoint f) (h : g <= f)
  statement: s.PairwiseDisjoint g
  proof: hs.mono_on fun i _ => h i

@[simp]

中文:
定理 PairwiseDisjoint.mono
  条件: (hs : s.PairwiseDisjoint f) (h : g <= f)
  结论: s.PairwiseDisjoint g
  证明: hs.mono_on fun i _ => h i

@[simp]

Depends on / 依赖: hs.mono_on, mono_on
-/
theorem PairwiseDisjoint.mono (hs : s.PairwiseDisjoint f) (h : g <= f) : s.PairwiseDisjoint g :=
  hs.mono_on fun i _ => h i

@[simp]
/--
theorem `pairwiseDisjoint_empty` / 定理 `pairwiseDisjoint_empty`

English:
theorem pairwiseDisjoint_empty
  statement: (∅ : Set ι).PairwiseDisjoint f
  proof: pairwise_empty _

@[simp]

中文:
定理 pairwiseDisjoint_empty
  结论: (∅ : 集合 ι).PairwiseDisjoint f
  证明: pairwise_empty _

@[simp]

Depends on / 依赖: pairwise_empty
-/
theorem pairwiseDisjoint_empty : (∅ : Set ι).PairwiseDisjoint f :=
  pairwise_empty _

@[simp]
/--
theorem `pairwiseDisjoint_singleton` / 定理 `pairwiseDisjoint_singleton`

English:
theorem pairwiseDisjoint_singleton
  given: (i : ι) (f : ι -> α)
  statement: PairwiseDisjoint {i} f
  proof: pairwise_singleton i _

@[simp]

中文:
定理 pairwiseDisjoint_singleton
  条件: (i : ι) (f : ι -> α)
  结论: PairwiseDisjoint {i} f
  证明: pairwise_singleton i _

@[simp]

Depends on / 依赖: pairwise_singleton
-/
theorem pairwiseDisjoint_singleton (i : ι) (f : ι -> α) : PairwiseDisjoint {i} f :=
  pairwise_singleton i _

@[simp]
/--
lemma `pairwiseDisjoint_singleton'` / 引理 `pairwiseDisjoint_singleton'`

English:
lemma pairwiseDisjoint_singleton'
  given: (s : Set ι)
  proof: by intro; grind

中文:
引理 pairwiseDisjoint_singleton'
  条件: (s : 集合 ι)
  证明: by intro; grind
-/
lemma pairwiseDisjoint_singleton' (s : Set ι) :
    s.PairwiseDisjoint (singleton : ι -> Set ι) := by intro; grind

/--
theorem `pairwiseDisjoint_insert` / 定理 `pairwiseDisjoint_insert`

English:
theorem pairwiseDisjoint_insert
  given: {i : ι}
  proof: pairwise_insert_of_symm

中文:
定理 pairwiseDisjoint_insert
  条件: {i : ι}
  证明: pairwise_insert_of_symm

Depends on / 依赖: pairwise_insert_of_symm
-/
theorem pairwiseDisjoint_insert {i : ι} :
    (insert i s).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧ forall j in s, i != j -> Disjoint (f i) (f j) :=
  pairwise_insert_of_symm

/--
theorem `pairwiseDisjoint_insert_of_notMem` / 定理 `pairwiseDisjoint_insert_of_notMem`

English:
theorem pairwiseDisjoint_insert_of_notMem
  given: {i : ι} (hi : i ∉ s)
  proof: pairwise_insert_of_symm_of_notMem hi

中文:
定理 pairwiseDisjoint_insert_of_notMem
  条件: {i : ι} (hi : i ∉ s)
  证明: pairwise_insert_of_symm_of_notMem hi

Depends on / 依赖: pairwise_insert_of_symm_of_notMem
-/
theorem pairwiseDisjoint_insert_of_notMem {i : ι} (hi : i ∉ s) :
    (insert i s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧ forall j in s, Disjoint (f i) (f j) :=
  pairwise_insert_of_symm_of_notMem hi

/--
theorem `PairwiseDisjoint.insert` / 定理 `PairwiseDisjoint.insert`

English:
theorem PairwiseDisjoint.insert
  statement: (hs : s.PairwiseDisjoint f) {i : ι}
  proof: pairwiseDisjoint_insert.2 ⟨hs, h⟩

中文:
定理 PairwiseDisjoint.insert
  结论: (hs : s.PairwiseDisjoint f) {i : ι}
  证明: pairwiseDisjoint_insert.2 ⟨hs, h⟩

Depends on / 依赖: K.obj, PresheafedSpace, PresheafedSpace.colimitCocone, PresheafedSpace.colimitCoconeIsColimit, Sheaf.pushforward_sheaf_of_sheaf, colimit, colimit.isoColimitCocone, colimitCocone, colimitCoconeIsColimit, createsColimitOfFullyFaithfulOfIso, forgetToPresheafedSpace, isoColimitCocone, limit_isSheaf, pushforward_sheaf_of_sheaf
-/
protected theorem PairwiseDisjoint.insert (hs : s.PairwiseDisjoint f) {i : ι}
    (h : forall j in s, i != j -> Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  pairwiseDisjoint_insert.2 ⟨hs, h⟩

/--
theorem `PairwiseDisjoint.insert_of_notMem` / 定理 `PairwiseDisjoint.insert_of_notMem`

English:
theorem PairwiseDisjoint.insert_of_notMem
  statement: (hs : s.PairwiseDisjoint f) {i : ι} (hi : i ∉ s)
  proof: (pairwiseDisjoint_insert_of_notMem hi).2 ⟨hs, h⟩

中文:
定理 PairwiseDisjoint.insert_of_notMem
  结论: (hs : s.PairwiseDisjoint f) {i : ι} (hi : i ∉ s)
  证明: (pairwiseDisjoint_insert_of_notMem hi).2 ⟨hs, h⟩

Depends on / 依赖: forgetToPresheafedSpace, hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape, pairwiseDisjoint_insert_of_notMem
-/
theorem PairwiseDisjoint.insert_of_notMem (hs : s.PairwiseDisjoint f) {i : ι} (hi : i ∉ s)
    (h : forall j in s, Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  (pairwiseDisjoint_insert_of_notMem hi).2 ⟨hs, h⟩

/--
theorem `PairwiseDisjoint.image_of_le` / 定理 `PairwiseDisjoint.image_of_le`

English:
theorem PairwiseDisjoint.image_of_le
  given: (hs : s.PairwiseDisjoint f) {g : ι -> ι} (hg : f ∘ g <= f)
  proof: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  exact (hs ha hb <| ne_of_apply_ne _ h).mono (hg a) (hg b)

中文:
定理 PairwiseDisjoint.image_of_le
  条件: (hs : s.PairwiseDisjoint f) {g : ι -> ι} (hg : f ∘ g <= f)
  证明: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  exact (hs ha hb <| ne_of_apply_ne _ h).mono (hg a) (hg b)

Depends on / 依赖: Limits, Limits.comp_preservesColimitsOfShape, PresheafedSpace, PresheafedSpace.forget, comp_preservesColimitsOfShape, forget, forgetToPresheafedSpace, ne_of_apply_ne
-/
theorem PairwiseDisjoint.image_of_le (hs : s.PairwiseDisjoint f) {g : ι -> ι} (hg : f ∘ g <= f) :
    (g '' s).PairwiseDisjoint f := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  exact (hs ha hb <| ne_of_apply_ne _ h).mono (hg a) (hg b)

/--
theorem `InjOn.pairwiseDisjoint_image` / 定理 `InjOn.pairwiseDisjoint_image`

English:
theorem InjOn.pairwiseDisjoint_image
  given: {g : ι' -> ι} {s : Set ι'} (h : s.InjOn g)
  proof: h.pairwise_image

中文:
定理 单射限制.pairwiseDisjoint_image
  条件: {g : ι' -> ι} {s : 集合 ι'} (h : s.单射限制 g)
  证明: h.pairwise_image

Depends on / 依赖: h.pairwise_image, pairwise_image
-/
theorem InjOn.pairwiseDisjoint_image {g : ι' -> ι} {s : Set ι'} (h : s.InjOn g) :
    (g '' s).PairwiseDisjoint f ↔ s.PairwiseDisjoint (f ∘ g) :=
  h.pairwise_image

/--
theorem `PairwiseDisjoint.range` / 定理 `PairwiseDisjoint.range`

English:
theorem PairwiseDisjoint.range
  statement: (g : s -> ι) (hg : forall i : s, f (g i) <= f i)
  proof: by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  exact ((ht x.2 y.2) fun h => hxy <| congr_arg g <| Subtype.ext h).mono (hg x) (hg y)

中文:
定理 PairwiseDisjoint.range
  结论: (g : s -> ι) (hg : 对任意 i : s, f (g i) <= f i)
  证明: by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  exact ((ht x.2 y.2) fun h => hxy <| congr_arg g <| Subtype.ext h).mono (hg x) (hg y)

Depends on / 依赖: Subtype, Subtype.ext, congr_arg
-/
theorem PairwiseDisjoint.range (g : s -> ι) (hg : forall i : s, f (g i) <= f i)
    (ht : s.PairwiseDisjoint f) : (range g).PairwiseDisjoint f := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  exact ((ht x.2 y.2) fun h => hxy <| congr_arg g <| Subtype.ext h).mono (hg x) (hg y)

/--
theorem `pairwiseDisjoint_union` / 定理 `pairwiseDisjoint_union`

English:
theorem pairwiseDisjoint_union
  proof: pairwise_union_of_symm

中文:
定理 pairwiseDisjoint_union
  证明: pairwise_union_of_symm

Depends on / 依赖: pairwise_union_of_symm
-/
theorem pairwiseDisjoint_union :
    (s union t).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧
        t.PairwiseDisjoint f ∧ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in t -> i != j -> Disjoint (f i) (f j) :=
  pairwise_union_of_symm

/--
theorem `PairwiseDisjoint.union` / 定理 `PairwiseDisjoint.union`

English:
theorem PairwiseDisjoint.union
  statement: (hs : s.PairwiseDisjoint f) (ht : t.PairwiseDisjoint f)
  proof: pairwiseDisjoint_union.2 ⟨hs, ht, h⟩

中文:
定理 PairwiseDisjoint.union
  结论: (hs : s.PairwiseDisjoint f) (ht : t.PairwiseDisjoint f)
  证明: pairwiseDisjoint_union.2 ⟨hs, ht, h⟩

Depends on / 依赖: X.presheaf.stalkPushforward, pairwiseDisjoint_union, presheaf, stalkFunctor, stalkPushforward
-/
theorem PairwiseDisjoint.union (hs : s.PairwiseDisjoint f) (ht : t.PairwiseDisjoint f)
    (h : forall ⦃i⦄, i in s -> forall ⦃j⦄, j in t -> i != j -> Disjoint (f i) (f j)) : (s union t).PairwiseDisjoint f :=
  pairwiseDisjoint_union.2 ⟨hs, ht, h⟩

-- classical
/--
theorem `PairwiseDisjoint.elim` / 定理 `PairwiseDisjoint.elim`

English:
theorem PairwiseDisjoint.elim
  statement: (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s)
  proof: hs.eq hi hj h

中文:
定理 PairwiseDisjoint.elim
  结论: (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s)
  证明: hs.eq hi hj h

Depends on / 依赖: hs.eq
-/
theorem PairwiseDisjoint.elim (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s)
    (h : ¬Disjoint (f i) (f j)) : i = j :=
  hs.eq hi hj h

/--
lemma `PairwiseDisjoint.eq_or_disjoint` / 引理 `PairwiseDisjoint.eq_or_disjoint`

English:
lemma PairwiseDisjoint.eq_or_disjoint
  proof: by
  rw [or_iff_not_imp_right]
  exact h.elim hi hj

中文:
引理 PairwiseDisjoint.eq_or_disjoint
  证明: by
  rw [or_iff_not_imp_right]
  exact h.elim hi hj

Depends on / 依赖: h.elim, or_iff_not_imp_right
-/
lemma PairwiseDisjoint.eq_or_disjoint
    (h : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s) :
    i = j ∨ Disjoint (f i) (f j) := by
  rw [or_iff_not_imp_right]
  exact h.elim hi hj

/--
lemma `pairwiseDisjoint_range_iff` / 引理 `pairwiseDisjoint_range_iff`

English:
lemma pairwiseDisjoint_range_iff
  given: {α β : Type*} {f : α -> (Set β)}
  proof: by
  aesop (add simp [PairwiseDisjoint, Set.Pairwise])

中文:
引理 pairwiseDisjoint_range_iff
  条件: {α β : 类型} {f : α -> (集合 β)}
  证明: by
  aesop (add simp [PairwiseDisjoint, Set.Pairwise])

Depends on / 依赖: Pairwise, PairwiseDisjoint, Set.Pairwise
-/
lemma pairwiseDisjoint_range_iff {α β : Type*} {f : α -> (Set β)} :
    (range f).PairwiseDisjoint id ↔ forall x y, f x != f y -> Disjoint (f x) (f y) := by
  aesop (add simp [PairwiseDisjoint, Set.Pairwise])

/--
lemma `_root_.Pairwise.pairwiseDisjoint` / 引理 `_root_.Pairwise.pairwiseDisjoint`

English:
lemma _root_.Pairwise.pairwiseDisjoint
  given: (h : Pairwise (Disjoint on f)) (s : Set ι)
  proof: h.set_pairwise s

中文:
引理 _root_.两两.pairwiseDisjoint
  条件: (h : 两两 (Disjoint on f)) (s : 集合 ι)
  证明: h.set_pairwise s

Depends on / 依赖: h.set_pairwise, set_pairwise
-/
lemma _root_.Pairwise.pairwiseDisjoint (h : Pairwise (Disjoint on f)) (s : Set ι) :
    s.PairwiseDisjoint f := h.set_pairwise s

end PartialOrderBot

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {s : Set ι} {f : ι -> α}

-- classical
/--
theorem `PairwiseDisjoint.elim'` / 定理 `PairwiseDisjoint.elim'`

English:
theorem PairwiseDisjoint.elim'
  statement: (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s)
  proof: (hs.elim hi hj) fun hij => h hij.eq_bot

中文:
定理 PairwiseDisjoint.elim'
  结论: (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s)
  证明: (hs.elim hi hj) fun hij => h hij.eq_bot

Depends on / 依赖: eq_bot, hij.eq_bot, hs.elim
-/
theorem PairwiseDisjoint.elim' (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s)
    (h : f i ⊓ f j != ⊥) : i = j :=
  (hs.elim hi hj) fun hij => h hij.eq_bot

/--
theorem `PairwiseDisjoint.eq_of_le` / 定理 `PairwiseDisjoint.eq_of_le`

English:
theorem PairwiseDisjoint.eq_of_le
  statement: (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s)
  proof: (hs.elim' hi hj) fun h => hf (inf_of_le_left hij).symm.trans h

中文:
定理 PairwiseDisjoint.eq_of_le
  结论: (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s)
  证明: (hs.elim' hi hj) fun h => hf (inf_of_le_left hij).symm.trans h

Depends on / 依赖: hs.elim, inf_of_le_left, symm.trans
-/
theorem PairwiseDisjoint.eq_of_le (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i in s) (hj : j in s)
    (hf : f i != ⊥) (hij : f i <= f j) : i = j :=
(hs.elim' hi hj) fun h => hf (inf_of_le_left hij).symm.trans h

end SemilatticeInfBot

/-! ### Pairwise disjoint set of sets -/

variable {s : Set ι} {t : Set ι'}

/--
theorem `pairwiseDisjoint_range_singleton` / 定理 `pairwiseDisjoint_range_singleton`

English:
theorem pairwiseDisjoint_range_singleton
  proof: Pairwise.range_pairwise fun _ _ => disjoint_singleton.2

中文:
定理 pairwiseDisjoint_range_singleton
  证明: Pairwise.range_pairwise fun _ _ => disjoint_singleton.2

Depends on / 依赖: Pairwise, Pairwise.range_pairwise, disjoint_singleton, range_pairwise
-/
theorem pairwiseDisjoint_range_singleton :
    (range (singleton : ι -> Set ι)).PairwiseDisjoint id :=
  Pairwise.range_pairwise fun _ _ => disjoint_singleton.2

/--
theorem `pairwiseDisjoint_fiber` / 定理 `pairwiseDisjoint_fiber`

English:
theorem pairwiseDisjoint_fiber
  given: (f : ι -> α) (s : Set α)
  statement: s.PairwiseDisjoint fun a => f ⁻¹' {a}
  proof: fun _a _ _b _ h => disjoint_iff_inf_le.mpr fun _i ⟨hia, hib⟩ => h (Eq.symm hia).trans hib

中文:
定理 pairwiseDisjoint_fiber
  条件: (f : ι -> α) (s : 集合 α)
  结论: s.PairwiseDisjoint fun a => f ⁻¹' {a}
  证明: fun _a _ _b _ h => disjoint_iff_inf_le.mpr fun _i ⟨hia, hib⟩ => h (Eq.symm hia).trans hib

Depends on / 依赖: Eq.symm, disjoint_iff_inf_le, disjoint_iff_inf_le.mpr
-/
theorem pairwiseDisjoint_fiber (f : ι -> α) (s : Set α) : s.PairwiseDisjoint fun a => f ⁻¹' {a} :=
fun _a _ _b _ h => disjoint_iff_inf_le.mpr fun _i ⟨hia, hib⟩ => h (Eq.symm hia).trans hib

-- classical
/--
theorem `PairwiseDisjoint.elim_set` / 定理 `PairwiseDisjoint.elim_set`

English:
theorem PairwiseDisjoint.elim_set
  statement: {s : Set ι} {f : ι -> Set α} (hs : s.PairwiseDisjoint f) {i j : ι}
  proof: hs.elim hi hj not_disjoint_iff.2 ⟨a, hai, haj⟩

中文:
定理 PairwiseDisjoint.elim_set
  结论: {s : 集合 ι} {f : ι -> 集合 α} (hs : s.PairwiseDisjoint f) {i j : ι}
  证明: hs.elim hi hj not_disjoint_iff.2 ⟨a, hai, haj⟩

Depends on / 依赖: hs.elim, not_disjoint_iff
-/
theorem PairwiseDisjoint.elim_set {s : Set ι} {f : ι -> Set α} (hs : s.PairwiseDisjoint f) {i j : ι}
    (hi : i in s) (hj : j in s) (a : α) (hai : a in f i) (haj : a in f j) : i = j :=
hs.elim hi hj not_disjoint_iff.2 ⟨a, hai, haj⟩

/--
theorem `PairwiseDisjoint.prod` / 定理 `PairwiseDisjoint.prod`

English:
theorem PairwiseDisjoint.prod
  statement: {f : ι -> Set α} {g : ι' -> Set β} (hs : s.PairwiseDisjoint f)
  proof: fun ⟨_, _⟩ ⟨hi, hi'⟩ ⟨_, _⟩ ⟨hj, hj'⟩ hij =>
  disjoint_left.2 fun ⟨_, _⟩ ⟨hai, hbi⟩ ⟨haj, hbj⟩ =>
hij Prod.ext (hs.elim_set hi hj _ hai haj) ht.elim_set hi' hj' _ hbi hbj

中文:
定理 PairwiseDisjoint.乘积
  结论: {f : ι -> 集合 α} {g : ι' -> 集合 β} (hs : s.PairwiseDisjoint f)
  证明: fun ⟨_, _⟩ ⟨hi, hi'⟩ ⟨_, _⟩ ⟨hj, hj'⟩ hij =>
  disjoint_left.2 fun ⟨_, _⟩ ⟨hai, hbi⟩ ⟨haj, hbj⟩ =>
hij Prod.ext (hs.elim_set hi hj _ hai haj) ht.elim_set hi' hj' _ hbi hbj

Depends on / 依赖: Prod.ext, disjoint_left, elim_set, hs.elim_set, ht.elim_set
-/
theorem PairwiseDisjoint.prod {f : ι -> Set α} {g : ι' -> Set β} (hs : s.PairwiseDisjoint f)
    (ht : t.PairwiseDisjoint g) :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint fun i => f i.1 ×ˢ g i.2 :=
  fun ⟨_, _⟩ ⟨hi, hi'⟩ ⟨_, _⟩ ⟨hj, hj'⟩ hij =>
  disjoint_left.2 fun ⟨_, _⟩ ⟨hai, hbi⟩ ⟨haj, hbj⟩ =>
hij Prod.ext (hs.elim_set hi hj _ hai haj) ht.elim_set hi' hj' _ hbi hbj

/--
theorem `pairwiseDisjoint_pi` / 定理 `pairwiseDisjoint_pi`

English:
theorem pairwiseDisjoint_pi
  statement: {ι' α : ι -> Type*} {s : forall i, Set (ι' i)} {f : forall i, ι' i -> Set (α i)}
  proof: fun _ hI _ hJ hIJ =>
  disjoint_left.2 fun a haI haJ =>
hIJ
      funext fun i =>
        (hs i).elim_set (hI i trivial) (hJ i trivial) (a i) (haI i trivial) (haJ i trivial)

中文:
定理 pairwiseDisjoint_pi
  结论: {ι' α : ι -> 类型} {s : 对任意 i, 集合 (ι' i)} {f : 对任意 i, ι' i -> 集合 (α i)}
  证明: fun _ hI _ hJ hIJ =>
  disjoint_left.2 fun a haI haJ =>
hIJ
      funext fun i =>
        (hs i).elim_set (hI i trivial) (hJ i trivial) (a i) (haI i trivial) (haJ i trivial)

Depends on / 依赖: disjoint_left, elim_set
-/
theorem pairwiseDisjoint_pi {ι' α : ι -> Type*} {s : forall i, Set (ι' i)} {f : forall i, ι' i -> Set (α i)}
    (hs : forall i, (s i).PairwiseDisjoint (f i)) :
    ((univ : Set ι).pi s).PairwiseDisjoint fun I => (univ : Set ι).pi fun i => f _ (I i) :=
  fun _ hI _ hJ hIJ =>
  disjoint_left.2 fun a haI haJ =>
hIJ
      funext fun i =>
        (hs i).elim_set (hI i trivial) (hJ i trivial) (a i) (haI i trivial) (haJ i trivial)

/--
theorem `pairwiseDisjoint_image_right_iff` / 定理 `pairwiseDisjoint_image_right_iff`

English:
theorem pairwiseDisjoint_image_right_iff
  statement: {f : α -> β -> γ} {s : Set α} {t : Set β}
  proof: by
  refine ⟨fun hs x hx y hy (h : f _ _ = _) => ?_, fun hs x hx y hy h => ?_⟩
  · suffices x.1 = y.1 by exact Prod.ext this (hf _ hx.1 <| h.trans <| by rw [this])
    refine hs.elim hx.1 hy.1 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.2, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.2
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.fst <| hs (mk_mem_prod hx ha) (mk_mem_prod hy hb) hab)

中文:
定理 pairwiseDisjoint_image_right_iff
  结论: {f : α -> β -> γ} {s : 集合 α} {t : 集合 β}
  证明: by
  refine ⟨fun hs x hx y hy (h : f _ _ = _) => ?_, fun hs x hx y hy h => ?_⟩
  · suffices x.1 = y.1 by exact Prod.ext this (hf _ hx.1 <| h.trans <| by rw [this])
    refine hs.elim hx.1 hy.1 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.2, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.2
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.fst <| hs (mk_mem_prod hx ha) (mk_mem_prod hy hb) hab)

Depends on / 依赖: Prod.ext, Prod.fst, congr_arg, disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, h.trans, hs.elim, mem_image_of_mem, mk_mem_prod, not_disjoint_iff
-/
theorem pairwiseDisjoint_image_right_iff {f : α -> β -> γ} {s : Set α} {t : Set β}
    (hf : forall a in s, Injective (f a)) :
    (s.PairwiseDisjoint fun a => f a '' t) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 := by
  refine ⟨fun hs x hx y hy (h : f _ _ = _) => ?_, fun hs x hx y hy h => ?_⟩
  · suffices x.1 = y.1 by exact Prod.ext this (hf _ hx.1 <| h.trans <| by rw [this])
    refine hs.elim hx.1 hy.1 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.2, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.2
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.fst <| hs (mk_mem_prod hx ha) (mk_mem_prod hy hb) hab)

/--
theorem `pairwiseDisjoint_image_left_iff` / 定理 `pairwiseDisjoint_image_left_iff`

English:
theorem pairwiseDisjoint_image_left_iff
  statement: {f : α -> β -> γ} {s : Set α} {t : Set β}
  proof: by
  refine ⟨fun ht x hx y hy (h : f _ _ = _) => ?_, fun ht x hx y hy h => ?_⟩
  · suffices x.2 = y.2 by exact Prod.ext (hf _ hx.2 <| h.trans <| by rw [this]) this
    refine ht.elim hx.2 hy.2 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.1, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.1
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.snd <| ht (mk_mem_prod ha hx) (mk_mem_prod hb hy) hab)

中文:
定理 pairwiseDisjoint_image_left_iff
  结论: {f : α -> β -> γ} {s : 集合 α} {t : 集合 β}
  证明: by
  refine ⟨fun ht x hx y hy (h : f _ _ = _) => ?_, fun ht x hx y hy h => ?_⟩
  · suffices x.2 = y.2 by exact Prod.ext (hf _ hx.2 <| h.trans <| by rw [this]) this
    refine ht.elim hx.2 hy.2 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.1, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.1
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.snd <| ht (mk_mem_prod ha hx) (mk_mem_prod hb hy) hab)

Depends on / 依赖: Prod.ext, Prod.snd, congr_arg, disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, h.trans, ht.elim, mem_image_of_mem, mk_mem_prod, not_disjoint_iff
-/
theorem pairwiseDisjoint_image_left_iff {f : α -> β -> γ} {s : Set α} {t : Set β}
    (hf : forall b in t, Injective fun a => f a b) :
    (t.PairwiseDisjoint fun b => (fun a => f a b) '' s) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 := by
  refine ⟨fun ht x hx y hy (h : f _ _ = _) => ?_, fun ht x hx y hy h => ?_⟩
  · suffices x.2 = y.2 by exact Prod.ext (hf _ hx.2 <| h.trans <| by rw [this]) this
    refine ht.elim hx.2 hy.2 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.1, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.1
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.snd <| ht (mk_mem_prod ha hx) (mk_mem_prod hb hy) hab)

/--
lemma `exists_ne_mem_inter_of_not_pairwiseDisjoint` / 引理 `exists_ne_mem_inter_of_not_pairwiseDisjoint`

English:
lemma exists_ne_mem_inter_of_not_pairwiseDisjoint
  proof: by
  change ¬ forall i, i in s -> forall j, j in s -> i != j -> forall t, t <= f i -> t <= f j -> t <= ⊥ at h
  simp only [not_forall] at h
  obtain ⟨i, hi, j, hj, h_ne, t, hfi, hfj, ht⟩ := h
  replace ht : t.Nonempty := by
    rwa [le_bot_iff, bot_eq_empty, ← Ne, ← nonempty_iff_ne_empty] at ht
  obtain ⟨x, hx⟩ := ht
  exact ⟨i, hi, j, hj, h_ne, x, hfi hx, hfj hx⟩

中文:
引理 存在_ne_mem_inter_of_not_pairwiseDisjoint
  证明: by
  change ¬ forall i, i in s -> forall j, j in s -> i != j -> forall t, t <= f i -> t <= f j -> t <= ⊥ at h
  simp only [not_forall] at h
  obtain ⟨i, hi, j, hj, h_ne, t, hfi, hfj, ht⟩ := h
  replace ht : t.Nonempty := by
    rwa [le_bot_iff, bot_eq_empty, ← Ne, ← nonempty_iff_ne_empty] at ht
  obtain ⟨x, hx⟩ := ht
  exact ⟨i, hi, j, hj, h_ne, x, hfi hx, hfj hx⟩

Depends on / 依赖: Nonempty, bot_eq_empty, h_ne, le_bot_iff, nonempty_iff_ne_empty, not_forall, replace, t.Nonempty
-/
lemma exists_ne_mem_inter_of_not_pairwiseDisjoint
    {f : ι -> Set α} (h : ¬ s.PairwiseDisjoint f) :
    exists i in s, exists j in s, i != j ∧ exists x : α, x in f i inter f j := by
  change ¬ forall i, i in s -> forall j, j in s -> i != j -> forall t, t <= f i -> t <= f j -> t <= ⊥ at h
  simp only [not_forall] at h
  obtain ⟨i, hi, j, hj, h_ne, t, hfi, hfj, ht⟩ := h
  replace ht : t.Nonempty := by
    rwa [le_bot_iff, bot_eq_empty, ← Ne, ← nonempty_iff_ne_empty] at ht
  obtain ⟨x, hx⟩ := ht
  exact ⟨i, hi, j, hj, h_ne, x, hfi hx, hfj hx⟩

/--
lemma `exists_lt_mem_inter_of_not_pairwiseDisjoint` / 引理 `exists_lt_mem_inter_of_not_pairwiseDisjoint`

English:
lemma exists_lt_mem_inter_of_not_pairwiseDisjoint
  statement: [LinearOrder ι]
  proof: by
  obtain ⟨i, hi, j, hj, hne, x, hx₁, hx₂⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  rcases lt_or_lt_iff_ne.mpr hne with h_lt | h_lt
  · exact ⟨i, hi, j, hj, h_lt, x, hx₁, hx₂⟩
  · exact ⟨j, hj, i, hi, h_lt, x, hx₂, hx₁⟩

中文:
引理 存在_lt_mem_inter_of_not_pairwiseDisjoint
  结论: [线性序 ι]
  证明: by
  obtain ⟨i, hi, j, hj, hne, x, hx₁, hx₂⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  rcases lt_or_lt_iff_ne.mpr hne with h_lt | h_lt
  · exact ⟨i, hi, j, hj, h_lt, x, hx₁, hx₂⟩
  · exact ⟨j, hj, i, hi, h_lt, x, hx₂, hx₁⟩

Depends on / 依赖: exists_ne_mem_inter_of_not_pairwiseDisjoint, h_lt, lt_or_lt_iff_ne, lt_or_lt_iff_ne.mpr
-/
lemma exists_lt_mem_inter_of_not_pairwiseDisjoint [LinearOrder ι]
    {f : ι -> Set α} (h : ¬ s.PairwiseDisjoint f) :
    exists i in s, exists j in s, i < j ∧ exists x, x in f i inter f j := by
  obtain ⟨i, hi, j, hj, hne, x, hx₁, hx₂⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  rcases lt_or_lt_iff_ne.mpr hne with h_lt | h_lt
  · exact ⟨i, hi, j, hj, h_lt, x, hx₁, hx₂⟩
  · exact ⟨j, hj, i, hi, h_lt, x, hx₂, hx₁⟩

/--
lemma `pairwiseDisjoint_singleton_iff_injOn` / 引理 `pairwiseDisjoint_singleton_iff_injOn`

English:
lemma pairwiseDisjoint_singleton_iff_injOn
  given: {f : ι -> α}
  proof: by
  simp [PairwiseDisjoint, InjOn, Set.Pairwise, not_imp_not]

中文:
引理 pairwiseDisjoint_singleton_iff_injOn
  条件: {f : ι -> α}
  证明: by
  simp [PairwiseDisjoint, InjOn, Set.Pairwise, not_imp_not]
-/
@[simp] lemma pairwiseDisjoint_singleton_iff_injOn {f : ι -> α} :
    s.PairwiseDisjoint (fun i => ({f i} : Set α)) ↔ s.InjOn f := by
  simp [PairwiseDisjoint, InjOn, Set.Pairwise, not_imp_not]

end Set

/--
lemma `exists_ne_mem_inter_of_not_pairwise_disjoint` / 引理 `exists_ne_mem_inter_of_not_pairwise_disjoint`

English:
lemma exists_ne_mem_inter_of_not_pairwise_disjoint
  proof: by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩

中文:
引理 存在_ne_mem_inter_of_not_pairwise_disjoint
  证明: by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩

Depends on / 依赖: exists_ne_mem_inter_of_not_pairwiseDisjoint, pairwise_univ
-/
lemma exists_ne_mem_inter_of_not_pairwise_disjoint
    {f : ι -> Set α} (h : ¬ Pairwise (Disjoint on f)) :
    exists i j : ι, i != j ∧ exists x, x in f i inter f j := by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩

/--
lemma `exists_lt_mem_inter_of_not_pairwise_disjoint` / 引理 `exists_lt_mem_inter_of_not_pairwise_disjoint`

English:
lemma exists_lt_mem_inter_of_not_pairwise_disjoint
  statement: [LinearOrder ι]
  proof: by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_lt_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩

中文:
引理 存在_lt_mem_inter_of_not_pairwise_disjoint
  结论: [线性序 ι]
  证明: by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_lt_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩

Depends on / 依赖: exists_lt_mem_inter_of_not_pairwiseDisjoint, pairwise_univ
-/
lemma exists_lt_mem_inter_of_not_pairwise_disjoint [LinearOrder ι]
    {f : ι -> Set α} (h : ¬ Pairwise (Disjoint on f)) :
    exists i j : ι, i < j ∧ exists x, x in f i inter f j := by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_lt_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩

/--
theorem `pairwise_disjoint_fiber` / 定理 `pairwise_disjoint_fiber`

English:
theorem pairwise_disjoint_fiber
  given: (f : ι -> α)
  statement: Pairwise (Disjoint on fun a : α => f ⁻¹' {a})
  proof: pairwise_univ.1 Set.pairwiseDisjoint_fiber f univ

中文:
定理 pairwise_disjoint_fiber
  条件: (f : ι -> α)
  结论: 两两 (Disjoint on fun a : α => f ⁻¹' {a})
  证明: pairwise_univ.1 Set.pairwiseDisjoint_fiber f univ

Depends on / 依赖: Set.pairwiseDisjoint_fiber, pairwiseDisjoint_fiber, pairwise_univ
-/
theorem pairwise_disjoint_fiber (f : ι -> α) : Pairwise (Disjoint on fun a : α => f ⁻¹' {a}) :=
pairwise_univ.1 Set.pairwiseDisjoint_fiber f univ

/--
lemma `subsingleton_setOfPred_mem_iff_pairwise_disjoint` / 引理 `subsingleton_setOfPred_mem_iff_pairwise_disjoint`

English:
lemma subsingleton_setOfPred_mem_iff_pairwise_disjoint
  given: {f : ι -> Set α}
  proof: ⟨fun h _ _ hij => disjoint_left.2 fun a hi hj => hij (h a hi hj),
   fun h _ _ hx _ hy => by_contra fun hne => disjoint_left.1 (h hne) hx hy⟩

@[deprecated (since := "2026-07-09")]
alias subsingleton_setOf_mem_iff_pairwise_disjoint :=
  subsingleton_setOfPred_mem_iff_pairwise_disjoint

中文:
引理 subsingleton_setOfPred_mem_iff_pairwise_disjoint
  条件: {f : ι -> 集合 α}
  证明: ⟨fun h _ _ hij => disjoint_left.2 fun a hi hj => hij (h a hi hj),
   fun h _ _ hx _ hy => by_contra fun hne => disjoint_left.1 (h hne) hx hy⟩

@[deprecated (since := "2026-07-09")]
alias subsingleton_setOf_mem_iff_pairwise_disjoint :=
  subsingleton_setOfPred_mem_iff_pairwise_disjoint

Depends on / 依赖: disjoint_left
-/
lemma subsingleton_setOfPred_mem_iff_pairwise_disjoint {f : ι -> Set α} :
    (forall a, {i | a in f i}.Subsingleton) ↔ Pairwise (Disjoint on f) :=
  ⟨fun h _ _ hij => disjoint_left.2 fun a hi hj => hij (h a hi hj),
   fun h _ _ hx _ hy => by_contra fun hne => disjoint_left.1 (h hne) hx hy⟩

@[deprecated (since := "2026-07-09")]
alias subsingleton_setOf_mem_iff_pairwise_disjoint :=
  subsingleton_setOfPred_mem_iff_pairwise_disjoint

/--
lemma `pairwise_not_eq_iff_injective` / 引理 `pairwise_not_eq_iff_injective`

English:
lemma pairwise_not_eq_iff_injective
  given: {f : ι -> α}
  proof: by
  simp [Pairwise, Function.Injective, not_imp_not]

中文:
引理 pairwise_not_eq_iff_injective
  条件: {f : ι -> α}
  证明: by
  simp [Pairwise, Function.Injective, not_imp_not]
-/
@[simp] lemma pairwise_not_eq_iff_injective {f : ι -> α} :
    Pairwise (fun i j => ¬ f i = f j) ↔ f.Injective := by
  simp [Pairwise, Function.Injective, not_imp_not]

/--
lemma `pairwise_ne_iff_injective` / 引理 `pairwise_ne_iff_injective`

English:
lemma pairwise_ne_iff_injective
  given: {f : ι -> α}
  statement: Pairwise (fun i j => f i != f j) ↔ f.Injective
  proof: by
  simp

中文:
引理 pairwise_ne_iff_injective
  条件: {f : ι -> α}
  结论: 两两 (fun i j => f i != f j) ↔ f.单射
  证明: by
  simp
-/
lemma pairwise_ne_iff_injective {f : ι -> α} : Pairwise (fun i j => f i != f j) ↔ f.Injective := by
  simp
