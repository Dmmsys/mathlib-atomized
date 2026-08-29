/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Data.List.Perm
public import Mathlib.Logic.Relation
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.InsertIdx

/-!
# List Permutations

This file develops theory about the `List.Perm` relation.

## Notation

The notation `~` is used for permutation equivalence.
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid Preorder

open Nat

namespace List
variable {α β : Type*} {l : List α}

open Perm (swap)

/--
lemma `perm_rfl` / 引理 `perm_rfl`

English:
lemma perm_rfl
  statement: l ~ l
  proof: Perm.refl _

中文:
引理 perm_rfl
  结论: l ~ l
  证明: Perm.refl _

Depends on / 依赖: Perm.refl
-/
lemma perm_rfl : l ~ l := Perm.refl _

attribute [symm] Perm.symm
attribute [trans] Perm.trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (α := List α) Perm
  body: ⟨fun _ _ => .symm⟩

中文:
实例 :
  签名: Std.Symm (α := 列表 α) 置换
  定义体: ⟨fun _ _ => .symm⟩
-/
instance : Std.Symm (α := List α) Perm := ⟨fun _ _ => .symm⟩

/--
theorem `Perm.subset_congr_left` / 定理 `Perm.subset_congr_left`

English:
theorem Perm.subset_congr_left
  given: {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂)
  statement: l₁ subseteq l₃ ↔ l₂ subseteq l₃
  proof: ⟨h.symm.subset.trans, h.subset.trans⟩

中文:
定理 置换.subset_congr_left
  条件: {l₁ l₂ l₃ : 列表 α} (h : l₁ ~ l₂)
  结论: l₁ subseteq l₃ ↔ l₂ subseteq l₃
  证明: ⟨h.symm.subset.trans, h.subset.trans⟩

Depends on / 依赖: h.subset.trans, h.symm.subset.trans, subset
-/
theorem Perm.subset_congr_left {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₁ subseteq l₃ ↔ l₂ subseteq l₃ :=
  ⟨h.symm.subset.trans, h.subset.trans⟩

/--
theorem `Perm.subset_congr_right` / 定理 `Perm.subset_congr_right`

English:
theorem Perm.subset_congr_right
  given: {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂)
  statement: l₃ subseteq l₁ ↔ l₃ subseteq l₂
  proof: ⟨fun h' => h'.trans h.subset, fun h' => h'.trans h.symm.subset⟩

中文:
定理 置换.subset_congr_right
  条件: {l₁ l₂ l₃ : 列表 α} (h : l₁ ~ l₂)
  结论: l₃ subseteq l₁ ↔ l₃ subseteq l₂
  证明: ⟨fun h' => h'.trans h.subset, fun h' => h'.trans h.symm.subset⟩

Depends on / 依赖: h.subset, h.symm.subset, subset
-/
theorem Perm.subset_congr_right {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₃ subseteq l₁ ↔ l₃ subseteq l₂ :=
  ⟨fun h' => h'.trans h.subset, fun h' => h'.trans h.symm.subset⟩

/--
theorem `set_perm_cons_eraseIdx` / 定理 `set_perm_cons_eraseIdx`

English:
theorem set_perm_cons_eraseIdx
  given: {n : Nat} (h : n < l.length) (a : α)
  proof: by
  rw [← insertIdx_eraseIdx_self (Nat.ne_of_lt h)]
  apply perm_insertIdx
  rw [length_eraseIdx_of_lt h]
  exact Nat.le_sub_one_of_lt h

中文:
定理 set_perm_cons_eraseIdx
  条件: {n : 自然数} (h : n < l.length) (a : α)
  证明: by
  rw [← insertIdx_eraseIdx_self (Nat.ne_of_lt h)]
  apply perm_insertIdx
  rw [length_eraseIdx_of_lt h]
  exact Nat.le_sub_one_of_lt h

Depends on / 依赖: Nat.le_sub_one_of_lt, Nat.ne_of_lt, insertIdx_eraseIdx_self, le_sub_one_of_lt, length_eraseIdx_of_lt, ne_of_lt, perm_insertIdx
-/
theorem set_perm_cons_eraseIdx {n : Nat} (h : n < l.length) (a : α) :
    l.set n a ~ a :: l.eraseIdx n := by
  rw [← insertIdx_eraseIdx_self (Nat.ne_of_lt h)]
  apply perm_insertIdx
  rw [length_eraseIdx_of_lt h]
  exact Nat.le_sub_one_of_lt h

/--
theorem `getElem_cons_eraseIdx_perm` / 定理 `getElem_cons_eraseIdx_perm`

English:
theorem getElem_cons_eraseIdx_perm
  given: {n : Nat} (h : n < l.length)
  proof: by
  simpa [h] using (set_perm_cons_eraseIdx h l[n]).symm

中文:
定理 getElem_cons_eraseIdx_perm
  条件: {n : 自然数} (h : n < l.length)
  证明: by
  simpa [h] using (set_perm_cons_eraseIdx h l[n]).symm

Depends on / 依赖: set_perm_cons_eraseIdx
-/
theorem getElem_cons_eraseIdx_perm {n : Nat} (h : n < l.length) :
    l[n] :: l.eraseIdx n ~ l := by
  simpa [h] using (set_perm_cons_eraseIdx h l[n]).symm

/--
theorem `perm_insertIdx_iff_of_le` / 定理 `perm_insertIdx_iff_of_le`

English:
theorem perm_insertIdx_iff_of_le
  statement: {l₁ l₂ : List α} {m n : Nat} (hm : m <= l₁.length)
  proof: by
  rw [rel_congr_left (perm_insertIdx _ _ hm)]; rw [rel_congr_right (perm_insertIdx _ _ hn)]; rw [perm_cons]

alias ⟨_, Perm.insertIdx_of_le⟩ := perm_insertIdx_iff_of_le

@[simp]

中文:
定理 perm_insertIdx_iff_of_le
  结论: {l₁ l₂ : 列表 α} {m n : 自然数} (hm : m <= l₁.length)
  证明: by
  rw [rel_congr_left (perm_insertIdx _ _ hm)]; rw [rel_congr_right (perm_insertIdx _ _ hn)]; rw [perm_cons]

alias ⟨_, Perm.insertIdx_of_le⟩ := perm_insertIdx_iff_of_le

@[simp]

Depends on / 依赖: perm_cons, perm_insertIdx, rel_congr_left, rel_congr_right
-/
theorem perm_insertIdx_iff_of_le {l₁ l₂ : List α} {m n : Nat} (hm : m <= l₁.length)
    (hn : n <= l₂.length) (a : α) : l₁.insertIdx m a ~ l₂.insertIdx n a ↔ l₁ ~ l₂ := by
  rw [rel_congr_left (perm_insertIdx _ _ hm)]; rw [rel_congr_right (perm_insertIdx _ _ hn)]; rw [perm_cons]

alias ⟨_, Perm.insertIdx_of_le⟩ := perm_insertIdx_iff_of_le

@[simp]
/--
theorem `perm_insertIdx_iff` / 定理 `perm_insertIdx_iff`

English:
theorem perm_insertIdx_iff
  given: {l₁ l₂ : List α} {n : Nat} {a : α}
  proof: by
  wlog hle : length l₁ <= length l₂ generalizing l₁ l₂
  · rw [perm_comm, this (Nat.le_of_not_ge hle), perm_comm]
  cases Nat.lt_or_ge (length l₁) n with
  | inl hn₁ =>
    rw [insertIdx_of_length_lt hn₁]
    cases Nat.lt_or_ge (length l₂) n with
    | inl hn₂ => rw [insertIdx_of_length_lt hn₂]
 

中文:
定理 perm_insertIdx_iff
  条件: {l₁ l₂ : 列表 α} {n : 自然数} {a : α}
  证明: by
  wlog hle : length l₁ <= length l₂ generalizing l₁ l₂
  · rw [perm_comm, this (Nat.le_of_not_ge hle), perm_comm]
  cases Nat.lt_or_ge (length l₁) n with
  | inl hn₁ =>
    rw [insertIdx_of_length_lt hn₁]
    cases Nat.lt_or_ge (length l₂) n with
    | inl hn₂ => rw [insertIdx_of_length_lt hn₂]
 

Depends on / 依赖: Nat.le_of_not_ge, Nat.le_trans, Nat.lt_or_ge, Perm.length_eq, generalizing, h.length_eq, iff_of_false, insertIdx_of_length_lt, le_of_not_ge, le_trans, length, length_eq, lt_or_ge, perm_comm, perm_insertIdx_iff_of_le
-/
theorem perm_insertIdx_iff {l₁ l₂ : List α} {n : Nat} {a : α} :
    l₁.insertIdx n a ~ l₂.insertIdx n a ↔ l₁ ~ l₂ := by
  wlog hle : length l₁ <= length l₂ generalizing l₁ l₂
  · rw [perm_comm, this (Nat.le_of_not_ge hle), perm_comm]
  cases Nat.lt_or_ge (length l₁) n with
  | inl hn₁ =>
    rw [insertIdx_of_length_lt hn₁]
    cases Nat.lt_or_ge (length l₂) n with
    | inl hn₂ => rw [insertIdx_of_length_lt hn₂]
    | inr hn₂ =>
      apply iff_of_false
      · intro h
        rw [h.length_eq] at hn₁
        grind
      · grind [Perm.length_eq]
  | inr hn₁ =>
    exact perm_insertIdx_iff_of_le hn₁ (Nat.le_trans hn₁ hle) _

@[gcongr]
/--
theorem `Perm.insertIdx` / 定理 `Perm.insertIdx`

English:
theorem Perm.insertIdx
  given: {l₁ l₂ : List α} (h : l₁ ~ l₂) (n : Nat) (a : α)
  proof: perm_insertIdx_iff.mpr h

中文:
定理 置换.insertIdx
  条件: {l₁ l₂ : 列表 α} (h : l₁ ~ l₂) (n : 自然数) (a : α)
  证明: perm_insertIdx_iff.mpr h
-/
protected theorem Perm.insertIdx {l₁ l₂ : List α} (h : l₁ ~ l₂) (n : Nat) (a : α) :
    l₁.insertIdx n a ~ l₂.insertIdx n a :=
  perm_insertIdx_iff.mpr h

/--
theorem `perm_eraseIdx_of_getElem?_eq` / 定理 `perm_eraseIdx_of_getElem?_eq`

English:
theorem perm_eraseIdx_of_getElem?_eq
  given: {l₁ l₂ : List α} {m n : Nat} (h : l₁[m]? = l₂[n]?)
  proof: by
  cases Nat.lt_or_ge m l₁.length with
  | inl hm =>
    rw [getElem?_eq_getElem hm]; rw [eq_comm]; rw [getElem?_eq_some_iff] at h
    cases h with
    | intro hn hnm =>
      rw [← perm_cons l₁[m], rel_congr_left (getElem_cons_eraseIdx_perm ..), ← hnm,
        rel_congr_right (getElem_cons_eraseI

中文:
定理 perm_eraseIdx_of_getElem?_eq
  条件: {l₁ l₂ : 列表 α} {m n : 自然数} (h : l₁[m]? = l₂[n]?)
  证明: by
  cases Nat.lt_or_ge m l₁.length with
  | inl hm =>
    rw [getElem?_eq_getElem hm]; rw [eq_comm]; rw [getElem?_eq_some_iff] at h
    cases h with
    | intro hn hnm =>
      rw [← perm_cons l₁[m], rel_congr_left (getElem_cons_eraseIdx_perm ..), ← hnm,
        rel_congr_right (getElem_cons_eraseI

Depends on / 依赖: Nat.lt_or_ge, _eq_getElem, _eq_none, _eq_none_iff, _eq_some_iff, eq_comm, eraseIdx_of_length_le, getElem, getElem_cons_eraseIdx_perm, length, lt_or_ge, perm_cons, rel_congr_left, rel_congr_right
-/
theorem perm_eraseIdx_of_getElem?_eq {l₁ l₂ : List α} {m n : Nat} (h : l₁[m]? = l₂[n]?) :
    eraseIdx l₁ m ~ eraseIdx l₂ n ↔ l₁ ~ l₂ := by
  cases Nat.lt_or_ge m l₁.length with
  | inl hm =>
    rw [getElem?_eq_getElem hm]; rw [eq_comm]; rw [getElem?_eq_some_iff] at h
    cases h with
    | intro hn hnm =>
      rw [← perm_cons l₁[m], rel_congr_left (getElem_cons_eraseIdx_perm ..), ← hnm,
        rel_congr_right (getElem_cons_eraseIdx_perm ..)]
  | inr hm =>
    rw [getElem?_eq_none hm]; rw [eq_comm]; rw [getElem?_eq_none_iff] at h
    rw [eraseIdx_of_length_le h]; rw [eraseIdx_of_length_le hm]

alias ⟨_, Perm.eraseIdx_of_getElem?_eq⟩ := perm_eraseIdx_of_getElem?_eq

section Rel

open Relator

variable {r : α -> β -> Prop}

local infixr:80 " ∘r " => Relation.Comp

/--
theorem `perm_comp_perm` / 定理 `perm_comp_perm`

English:
theorem perm_comp_perm
  statement: (Perm ∘r Perm : List α -> List α -> Prop) = Perm
  proof: by
  funext a c; apply propext
  constructor
  · exact fun ⟨b, hab, hba⟩ => Perm.trans hab hba
  · exact fun h => ⟨a, Perm.refl a, h⟩

中文:
定理 perm_comp_perm
  结论: (置换 ∘r 置换 : 列表 α -> 列表 α -> 命题) = 置换
  证明: by
  funext a c; apply propext
  constructor
  · exact fun ⟨b, hab, hba⟩ => Perm.trans hab hba
  · exact fun h => ⟨a, Perm.refl a, h⟩

Depends on / 依赖: Perm.refl, Perm.trans, propext
-/
theorem perm_comp_perm : (Perm ∘r Perm : List α -> List α -> Prop) = Perm := by
  funext a c; apply propext
  constructor
  · exact fun ⟨b, hab, hba⟩ => Perm.trans hab hba
  · exact fun h => ⟨a, Perm.refl a, h⟩

/--
theorem `perm_comp_forall₂` / 定理 `perm_comp_forall₂`

English:
theorem perm_comp_forall₂
  given: {l u v} (hlu : Perm l u) (huv : Forall₂ r u v)
  proof: by
  induction hlu generalizing v with
  | nil => cases huv; exact ⟨[], Forall₂.nil, Perm.nil⟩
  | cons u _hlu ih =>
    obtain - | ⟨hab, huv'⟩ := huv
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩
    exact ⟨_ :: l₂, Forall₂.cons hab h₁₂, h₂₃.cons _⟩
  | swap a₁ a₂ h₂₃ =>
    obtain - | ⟨h₁, hr₂₃⟩ := huv
 

中文:
定理 perm_comp_对任意₂
  条件: {l u v} (hlu : 置换 l u) (huv : Forall₂ r u v)
  证明: by
  induction hlu generalizing v with
  | nil => cases huv; exact ⟨[], Forall₂.nil, Perm.nil⟩
  | cons u _hlu ih =>
    obtain - | ⟨hab, huv'⟩ := huv
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩
    exact ⟨_ :: l₂, Forall₂.cons hab h₁₂, h₂₃.cons _⟩
  | swap a₁ a₂ h₂₃ =>
    obtain - | ⟨h₁, hr₂₃⟩ := huv
 

Depends on / 依赖: Perm.nil, Perm.swap, Perm.trans, _hlu, generalizing
-/
theorem perm_comp_forall₂ {l u v} (hlu : Perm l u) (huv : Forall₂ r u v) :
    (Forall₂ r ∘r Perm) l v := by
  induction hlu generalizing v with
  | nil => cases huv; exact ⟨[], Forall₂.nil, Perm.nil⟩
  | cons u _hlu ih =>
    obtain - | ⟨hab, huv'⟩ := huv
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩
    exact ⟨_ :: l₂, Forall₂.cons hab h₁₂, h₂₃.cons _⟩
  | swap a₁ a₂ h₂₃ =>
    obtain - | ⟨h₁, hr₂₃⟩ := huv
    obtain - | ⟨h₂, h₁₂⟩ := hr₂₃
    exact ⟨_, Forall₂.cons h₂ (Forall₂.cons h₁ h₁₂), Perm.swap _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
    rcases ih₂ huv with ⟨lb₂, hab₂, h₂₃⟩
    rcases ih₁ hab₂ with ⟨lb₁, hab₁, h₁₂⟩
    exact ⟨lb₁, hab₁, Perm.trans h₁₂ h₂₃⟩

/--
theorem `forall₂_comp_perm_eq_perm_comp_forall₂` / 定理 `forall₂_comp_perm_eq_perm_comp_forall₂`

English:
theorem forall₂_comp_perm_eq_perm_comp_forall₂
  statement: Forall₂ r ∘r Perm = Perm ∘r Forall₂ r
  proof: by
  funext l₁ l₃; apply propext
  constructor
  · intro h
    rcases h with ⟨l₂, h₁₂, h₂₃⟩
    have : Forall₂ (flip r) l₂ l₁ := h₁₂.flip
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩
    exact ⟨l', h₂.symm, h₁.flip⟩
  · exact fun ⟨l₂, h₁₂, h₂₃⟩ => perm_comp_forall₂ h₁₂ h₂₃

中文:
定理 对任意₂_comp_perm_eq_perm_comp_对任意₂
  结论: Forall₂ r ∘r 置换 = 置换 ∘r Forall₂ r
  证明: by
  funext l₁ l₃; apply propext
  constructor
  · intro h
    rcases h with ⟨l₂, h₁₂, h₂₃⟩
    have : Forall₂ (flip r) l₂ l₁ := h₁₂.flip
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩
    exact ⟨l', h₂.symm, h₁.flip⟩
  · exact fun ⟨l₂, h₁₂, h₂₃⟩ => perm_comp_forall₂ h₁₂ h₂₃

Depends on / 依赖: propext
-/
theorem forall₂_comp_perm_eq_perm_comp_forall₂ : Forall₂ r ∘r Perm = Perm ∘r Forall₂ r := by
  funext l₁ l₃; apply propext
  constructor
  · intro h
    rcases h with ⟨l₂, h₁₂, h₂₃⟩
    have : Forall₂ (flip r) l₂ l₁ := h₁₂.flip
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩
    exact ⟨l', h₂.symm, h₁.flip⟩
  · exact fun ⟨l₂, h₁₂, h₂₃⟩ => perm_comp_forall₂ h₁₂ h₂₃

/--
theorem `eq_map_comp_perm` / 定理 `eq_map_comp_perm`

English:
theorem eq_map_comp_perm
  given: (f : α -> β)
  statement: (· = map f ·) ∘r (· ~ ·) = (· ~ map f ·)
  proof: by
  conv_rhs => rw [← Relation.comp_eq_fun (map f)]
  simp only [← forall₂_eq_eq_eq, forall₂_map_right_iff, forall₂_comp_perm_eq_perm_comp_forall₂]

中文:
定理 eq_map_comp_perm
  条件: (f : α -> β)
  结论: (· = map f ·) ∘r (· ~ ·) = (· ~ map f ·)
  证明: by
  conv_rhs => rw [← Relation.comp_eq_fun (map f)]
  simp only [← forall₂_eq_eq_eq, forall₂_map_right_iff, forall₂_comp_perm_eq_perm_comp_forall₂]

Depends on / 依赖: Relation, Relation.comp_eq_fun, comp_eq_fun, conv_rhs
-/
theorem eq_map_comp_perm (f : α -> β) : (· = map f ·) ∘r (· ~ ·) = (· ~ map f ·) := by
  conv_rhs => rw [← Relation.comp_eq_fun (map f)]
  simp only [← forall₂_eq_eq_eq, forall₂_map_right_iff, forall₂_comp_perm_eq_perm_comp_forall₂]

/--
theorem `rel_perm_imp` / 定理 `rel_perm_imp`

English:
theorem rel_perm_imp
  given: (hr : RightUnique r)
  statement: (Forall₂ r ⇒ Forall₂ r ⇒ (· -> ·)) Perm Perm
  proof: fun a b h₁ c d h₂ h =>
  have : (flip (Forall₂ r) ∘r Perm ∘r Forall₂ r) b d := ⟨a, h₁, c, h, h₂⟩
  have : ((flip (Forall₂ r) ∘r Forall₂ r) ∘r Perm) b d := by
    rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← Relation.comp_assoc] at this
  let ⟨b', ⟨_, hbc, hcb⟩, hbd⟩ := this
  have : b' = b := ri

中文:
定理 rel_perm_imp
  条件: (hr : RightUnique r)
  结论: (Forall₂ r ⇒ Forall₂ r ⇒ (· -> ·)) 置换 置换
  证明: fun a b h₁ c d h₂ h =>
  have : (flip (Forall₂ r) ∘r Perm ∘r Forall₂ r) b d := ⟨a, h₁, c, h, h₂⟩
  have : ((flip (Forall₂ r) ∘r Forall₂ r) ∘r Perm) b d := by
    rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← Relation.comp_assoc] at this
  let ⟨b', ⟨_, hbc, hcb⟩, hbd⟩ := this
  have : b' = b := ri

Depends on / 依赖: Relation, Relation.comp_assoc, comp_assoc
-/
theorem rel_perm_imp (hr : RightUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· -> ·)) Perm Perm :=
  fun a b h₁ c d h₂ h =>
  have : (flip (Forall₂ r) ∘r Perm ∘r Forall₂ r) b d := ⟨a, h₁, c, h, h₂⟩
  have : ((flip (Forall₂ r) ∘r Forall₂ r) ∘r Perm) b d := by
    rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← Relation.comp_assoc] at this
  let ⟨b', ⟨_, hbc, hcb⟩, hbd⟩ := this
  have : b' = b := right_unique_forall₂' hr hcb hbc
  this ▸ hbd

/--
theorem `rel_perm` / 定理 `rel_perm`

English:
theorem rel_perm
  given: (hr : BiUnique r)
  statement: (Forall₂ r ⇒ Forall₂ r ⇒ (· ↔ ·)) Perm Perm
  proof: fun _a _b hab _c _d hcd =>
  Iff.intro (rel_perm_imp hr.2 hab hcd) (rel_perm_imp hr.left.flip hab.flip hcd.flip)

中文:
定理 rel_perm
  条件: (hr : BiUnique r)
  结论: (Forall₂ r ⇒ Forall₂ r ⇒ (· ↔ ·)) 置换 置换
  证明: fun _a _b hab _c _d hcd =>
  Iff.intro (rel_perm_imp hr.2 hab hcd) (rel_perm_imp hr.left.flip hab.flip hcd.flip)

Depends on / 依赖: Iff.intro, hab.flip, hcd.flip, hr.left.flip, rel_perm_imp
-/
theorem rel_perm (hr : BiUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· ↔ ·)) Perm Perm :=
  fun _a _b hab _c _d hcd =>
  Iff.intro (rel_perm_imp hr.2 hab hcd) (rel_perm_imp hr.left.flip hab.flip hcd.flip)

end Rel

/--
lemma `count_eq_count_filter_add` / 引理 `count_eq_count_filter_add`

English:
lemma count_eq_count_filter_add
  statement: [DecidableEq α] (P : α -> Prop) [DecidablePred P]
  proof: by
  unfold count
  convert countP_eq_countP_filter_add l _ P
  simp only [decide_not]

中文:
引理 count_eq_count_filter_add
  结论: [DecidableEq α] (P : α -> 命题) [DecidablePred P]
  证明: by
  unfold count
  convert countP_eq_countP_filter_add l _ P
  simp only [decide_not]

Depends on / 依赖: convert, countP_eq_countP_filter_add, decide_not
-/
lemma count_eq_count_filter_add [DecidableEq α] (P : α -> Prop) [DecidablePred P]
    (l : List α) (a : α) :
    count a l = count a (l.filter P) + count a (l.filter (¬ P ·)) := by
  unfold count
  convert countP_eq_countP_filter_add l _ P
  simp only [decide_not]

/--
theorem `Perm.foldl_eq` / 定理 `Perm.foldl_eq`

English:
theorem Perm.foldl_eq
  given: {f : β -> α -> β} {l₁ l₂ : List α} [rcomm : RightCommutative f] (p : l₁ ~ l₂)
  proof: p.foldl_eq' fun x _hx y _hy z => rcomm.right_comm z x y

中文:
定理 置换.foldl_eq
  条件: {f : β -> α -> β} {l₁ l₂ : 列表 α} [rcomm : 右交换 f] (p : l₁ ~ l₂)
  证明: p.foldl_eq' fun x _hx y _hy z => rcomm.right_comm z x y

Depends on / 依赖: foldl_eq, p.foldl_eq, rcomm.right_comm, right_comm
-/
theorem Perm.foldl_eq {f : β -> α -> β} {l₁ l₂ : List α} [rcomm : RightCommutative f] (p : l₁ ~ l₂) :
    forall b, foldl f b l₁ = foldl f b l₂ :=
  p.foldl_eq' fun x _hx y _hy z => rcomm.right_comm z x y

/--
theorem `Perm.foldr_eq` / 定理 `Perm.foldr_eq`

English:
theorem Perm.foldr_eq
  given: {f : α -> β -> β} {l₁ l₂ : List α} [lcomm : LeftCommutative f] (p : l₁ ~ l₂)
  proof: by
  intro b
  induction p using Perm.recOnSwap' generalizing b with
  | nil => rfl
  | cons _ _ r => simp [r b]
  | swap' _ _ _ r => simp only [foldr_cons]; rw [lcomm.left_comm, r b]
  | trans _ _ r₁ r₂ => exact Eq.trans (r₁ b) (r₂ b)

中文:
定理 置换.foldr_eq
  条件: {f : α -> β -> β} {l₁ l₂ : 列表 α} [lcomm : 左交换 f] (p : l₁ ~ l₂)
  证明: by
  intro b
  induction p using Perm.recOnSwap' generalizing b with
  | nil => rfl
  | cons _ _ r => simp [r b]
  | swap' _ _ _ r => simp only [foldr_cons]; rw [lcomm.left_comm, r b]
  | trans _ _ r₁ r₂ => exact Eq.trans (r₁ b) (r₂ b)

Depends on / 依赖: Eq.trans, Perm.recOnSwap, foldr_cons, generalizing, lcomm.left_comm, left_comm, recOnSwap
-/
theorem Perm.foldr_eq {f : α -> β -> β} {l₁ l₂ : List α} [lcomm : LeftCommutative f] (p : l₁ ~ l₂) :
    forall b, foldr f b l₁ = foldr f b l₂ := by
  intro b
  induction p using Perm.recOnSwap' generalizing b with
  | nil => rfl
  | cons _ _ r => simp [r b]
  | swap' _ _ _ r => simp only [foldr_cons]; rw [lcomm.left_comm, r b]
  | trans _ _ r₁ r₂ => exact Eq.trans (r₁ b) (r₂ b)

section

variable {op : α -> α -> α} [IA : Std.Associative op] [IC : Std.Commutative op]

local notation a " * " b => op a b

local notation l " <*> " a => foldl op a l

/--
theorem `Perm.foldl_op_eq` / 定理 `Perm.foldl_op_eq`

English:
theorem Perm.foldl_op_eq
  given: {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂)
  statement: (l₁ <*> a) = l₂ <*> a
  proof: h.foldl_eq _

中文:
定理 置换.foldl_op_eq
  条件: {l₁ l₂ : 列表 α} {a : α} (h : l₁ ~ l₂)
  结论: (l₁ <*> a) = l₂ <*> a
  证明: h.foldl_eq _

Depends on / 依赖: foldl_eq, h.foldl_eq
-/
theorem Perm.foldl_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : (l₁ <*> a) = l₂ <*> a :=
  h.foldl_eq _

/--
theorem `Perm.foldr_op_eq` / 定理 `Perm.foldr_op_eq`

English:
theorem Perm.foldr_op_eq
  given: {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂)
  statement: l₁.foldr op a = l₂.foldr op a
  proof: h.foldr_eq _

中文:
定理 置换.foldr_op_eq
  条件: {l₁ l₂ : 列表 α} {a : α} (h : l₁ ~ l₂)
  结论: l₁.foldr op a = l₂.foldr op a
  证明: h.foldr_eq _

Depends on / 依赖: foldr_eq, h.foldr_eq
-/
theorem Perm.foldr_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : l₁.foldr op a = l₂.foldr op a :=
  h.foldr_eq _

end

/--
theorem `perm_option_toList` / 定理 `perm_option_toList`

English:
theorem perm_option_toList
  given: {o₁ o₂ : Option α}
  statement: o₁.toList ~ o₂.toList ↔ o₁ = o₂
  proof: by
  refine ⟨fun p => ?_, fun e => e ▸ Perm.refl _⟩
  rcases o₁ with - | a <;> rcases o₂ with - | b; · rfl
  · cases p.length_eq
  · cases p.length_eq
  · exact Option.mem_toList.1 (p.symm.subset <| by simp)

中文:
定理 perm_option_toList
  条件: {o₁ o₂ : 选项类型 α}
  结论: o₁.toList ~ o₂.toList ↔ o₁ = o₂
  证明: by
  refine ⟨fun p => ?_, fun e => e ▸ Perm.refl _⟩
  rcases o₁ with - | a <;> rcases o₂ with - | b; · rfl
  · cases p.length_eq
  · cases p.length_eq
  · exact Option.mem_toList.1 (p.symm.subset <| by simp)

Depends on / 依赖: Option.mem_toList, Perm.refl, length_eq, mem_toList, p.length_eq, p.symm.subset, subset
-/
theorem perm_option_toList {o₁ o₂ : Option α} : o₁.toList ~ o₂.toList ↔ o₁ = o₂ := by
  refine ⟨fun p => ?_, fun e => e ▸ Perm.refl _⟩
  rcases o₁ with - | a <;> rcases o₂ with - | b; · rfl
  · cases p.length_eq
  · cases p.length_eq
  · exact Option.mem_toList.1 (p.symm.subset <| by simp)

/--
theorem `perm_replicate_append_replicate` / 定理 `perm_replicate_append_replicate`

English:
theorem perm_replicate_append_replicate
  proof: by
  rw [perm_iff_count]; rw [← Decidable.and_forall_ne a]; rw [← Decidable.and_forall_ne b]
  suffices l subseteq [a, b] ↔ forall c, c != b -> c != a -> c ∉ l by
    simp +contextual [count_replicate, h, this, count_eq_zero, Ne.symm]
  trans forall c, c in l -> c = b ∨ c = a
  · simp [subset_def, o

中文:
定理 perm_replicate_append_replicate
  证明: by
  rw [perm_iff_count]; rw [← Decidable.and_forall_ne a]; rw [← Decidable.and_forall_ne b]
  suffices l subseteq [a, b] ↔ forall c, c != b -> c != a -> c ∉ l by
    simp +contextual [count_replicate, h, this, count_eq_zero, Ne.symm]
  trans forall c, c in l -> c = b ∨ c = a
  · simp [subset_def, o

Depends on / 依赖: Decidable, Decidable.and_forall_ne, Ne.symm, and_forall_ne, and_imp, contextual, count_eq_zero, count_replicate, forall_congr, not_imp_not, not_or, or_comm, perm_iff_count, subset_def, subseteq
-/
theorem perm_replicate_append_replicate
    [DecidableEq α] {l : List α} {a b : α} {m n : Nat} (h : a != b) :
    l ~ replicate m a ++ replicate n b ↔ count a l = m ∧ count b l = n ∧ l subseteq [a, b] := by
  rw [perm_iff_count]; rw [← Decidable.and_forall_ne a]; rw [← Decidable.and_forall_ne b]
  suffices l subseteq [a, b] ↔ forall c, c != b -> c != a -> c ∉ l by
    simp +contextual [count_replicate, h, this, count_eq_zero, Ne.symm]
  trans forall c, c in l -> c = b ∨ c = a
  · simp [subset_def, or_comm]
  · exact forall_congr' fun _ => by rw [← and_imp, ← not_or, not_imp_not]

/--
theorem `map_perm_map_iff` / 定理 `map_perm_map_iff`

English:
theorem map_perm_map_iff
  given: {l' : List α} {f : α -> β} (hf : f.Injective)
  proof: calc
  map f l ~ map f l' ↔ Relation.Comp (· = map f ·) (· ~ ·) (map f l) l' := by rw [eq_map_comp_perm]
  _ ↔ l ~ l' := by simp [Relation.Comp, map_inj_right hf]

中文:
定理 map_perm_map_iff
  条件: {l' : 列表 α} {f : α -> β} (hf : f.单射)
  证明: calc
  map f l ~ map f l' ↔ Relation.Comp (· = map f ·) (· ~ ·) (map f l) l' := by rw [eq_map_comp_perm]
  _ ↔ l ~ l' := by simp [Relation.Comp, map_inj_right hf]
-/
theorem map_perm_map_iff {l' : List α} {f : α -> β} (hf : f.Injective) :
    map f l ~ map f l' ↔ l ~ l' := calc
  map f l ~ map f l' ↔ Relation.Comp (· = map f ·) (· ~ ·) (map f l) l' := by rw [eq_map_comp_perm]
  _ ↔ l ~ l' := by simp [Relation.Comp, map_inj_right hf]

/--
theorem `Perm.flatMap_left` / 定理 `Perm.flatMap_left`

English:
theorem Perm.flatMap_left
  given: (l : List α) {f g : α -> List β} (h : forall a in l, f a ~ g a)
  proof: Perm.flatten_congr by
    rwa [List.forall₂_map_right_iff, List.forall₂_map_left_iff, List.forall₂_same]

@[gcongr]

中文:
定理 置换.flatMap_left
  条件: (l : 列表 α) {f g : α -> 列表 β} (h : 对任意 a in l, f a ~ g a)
  证明: Perm.flatten_congr by
    rwa [List.forall₂_map_right_iff, List.forall₂_map_left_iff, List.forall₂_same]

@[gcongr]

Depends on / 依赖: List.forall, Perm.flatten_congr, flatten_congr
-/
theorem Perm.flatMap_left (l : List α) {f g : α -> List β} (h : forall a in l, f a ~ g a) :
    l.flatMap f ~ l.flatMap g :=
Perm.flatten_congr by
    rwa [List.forall₂_map_right_iff, List.forall₂_map_left_iff, List.forall₂_same]

@[gcongr]
/--
theorem `Perm.flatMap` / 定理 `Perm.flatMap`

English:
theorem Perm.flatMap
  statement: {l₁ l₂ : List α} {f g : α -> List β} (h : l₁ ~ l₂)
  proof: .trans (.flatMap_left _ hfg) (h.flatMap_right _)

中文:
定理 置换.flatMap
  结论: {l₁ l₂ : 列表 α} {f g : α -> 列表 β} (h : l₁ ~ l₂)
  证明: .trans (.flatMap_left _ hfg) (h.flatMap_right _)
-/
protected theorem Perm.flatMap {l₁ l₂ : List α} {f g : α -> List β} (h : l₁ ~ l₂)
    (hfg : forall a in l₁, f a ~ g a) : l₁.flatMap f ~ l₂.flatMap g :=
  .trans (.flatMap_left _ hfg) (h.flatMap_right _)

/--
theorem `flatMap_append_perm` / 定理 `flatMap_append_perm`

English:
theorem flatMap_append_perm
  given: (l : List α) (f g : α -> List β)
  proof: by
  induction l with | nil => simp | cons a l IH => ?_
  simp only [flatMap_cons, append_assoc]
  refine (Perm.trans ?_ (IH.append_left _)).append_left _
  rw [← append_assoc]; rw [← append_assoc]
  exact perm_append_comm.append_right _

中文:
定理 flatMap_append_perm
  条件: (l : 列表 α) (f g : α -> 列表 β)
  证明: by
  induction l with | nil => simp | cons a l IH => ?_
  simp only [flatMap_cons, append_assoc]
  refine (Perm.trans ?_ (IH.append_left _)).append_left _
  rw [← append_assoc]; rw [← append_assoc]
  exact perm_append_comm.append_right _

Depends on / 依赖: IH.append_left, Perm.trans, append_assoc, append_left, append_right, flatMap_cons, perm_append_comm, perm_append_comm.append_right
-/
theorem flatMap_append_perm (l : List α) (f g : α -> List β) :
    l.flatMap f ++ l.flatMap g ~ l.flatMap fun x => f x ++ g x := by
  induction l with | nil => simp | cons a l IH => ?_
  simp only [flatMap_cons, append_assoc]
  refine (Perm.trans ?_ (IH.append_left _)).append_left _
  rw [← append_assoc]; rw [← append_assoc]
  exact perm_append_comm.append_right _

/--
theorem `map_append_flatMap_perm` / 定理 `map_append_flatMap_perm`

English:
theorem map_append_flatMap_perm
  given: (l : List α) (f : α -> β) (g : α -> List β)
  proof: by
  simpa [← map_eq_flatMap] using flatMap_append_perm l (fun x => [f x]) g

中文:
定理 map_append_flatMap_perm
  条件: (l : 列表 α) (f : α -> β) (g : α -> 列表 β)
  证明: by
  simpa [← map_eq_flatMap] using flatMap_append_perm l (fun x => [f x]) g

Depends on / 依赖: flatMap_append_perm, map_eq_flatMap
-/
theorem map_append_flatMap_perm (l : List α) (f : α -> β) (g : α -> List β) :
    l.map f ++ l.flatMap g ~ l.flatMap fun x => f x :: g x := by
  simpa [← map_eq_flatMap] using flatMap_append_perm l (fun x => [f x]) g

/--
theorem `Perm.product_right` / 定理 `Perm.product_right`

English:
theorem Perm.product_right
  given: {l₁ l₂ : List α} (t₁ : List β) (p : l₁ ~ l₂)
  proof: p.flatMap_right _

中文:
定理 置换.product_right
  条件: {l₁ l₂ : 列表 α} (t₁ : 列表 β) (p : l₁ ~ l₂)
  证明: p.flatMap_right _

Depends on / 依赖: flatMap_right, p.flatMap_right
-/
theorem Perm.product_right {l₁ l₂ : List α} (t₁ : List β) (p : l₁ ~ l₂) :
    product l₁ t₁ ~ product l₂ t₁ :=
  p.flatMap_right _

/--
theorem `Perm.product_left` / 定理 `Perm.product_left`

English:
theorem Perm.product_left
  given: (l : List α) {t₁ t₂ : List β} (p : t₁ ~ t₂)
  proof: (Perm.flatMap_left _) fun _ _ => p.map _

@[gcongr]

中文:
定理 置换.product_left
  条件: (l : 列表 α) {t₁ t₂ : 列表 β} (p : t₁ ~ t₂)
  证明: (Perm.flatMap_left _) fun _ _ => p.map _

@[gcongr]

Depends on / 依赖: Perm.flatMap_left, flatMap_left, p.map
-/
theorem Perm.product_left (l : List α) {t₁ t₂ : List β} (p : t₁ ~ t₂) :
    product l t₁ ~ product l t₂ :=
  (Perm.flatMap_left _) fun _ _ => p.map _

@[gcongr]
/--
theorem `Perm.product` / 定理 `Perm.product`

English:
theorem Perm.product
  given: {l₁ l₂ : List α} {t₁ t₂ : List β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂)
  proof: (p₁.product_right t₁).trans (p₂.product_left l₂)

中文:
定理 置换.product
  条件: {l₁ l₂ : 列表 α} {t₁ t₂ : 列表 β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂)
  证明: (p₁.product_right t₁).trans (p₂.product_left l₂)

Depends on / 依赖: product_left, product_right
-/
theorem Perm.product {l₁ l₂ : List α} {t₁ t₂ : List β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) :
    product l₁ t₁ ~ product l₂ t₂ :=
  (p₁.product_right t₁).trans (p₂.product_left l₂)

end List
