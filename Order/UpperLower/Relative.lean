/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.SetNotation

/-!
# Properties of relative upper/lower sets

This file proves results on `IsRelUpperSet` and `IsRelLowerSet`.
-/

public section

open Set

variable {α : Type*} {ι : Sort*} {κ : ι -> Sort*} {s t : Set α} {a b : α} {P : α -> Prop}

section LE

variable [LE α]

/--
lemma `isRelUpperSet_true_iff_isUpperSet` / 引理 `isRelUpperSet_true_iff_isUpperSet`

English:
lemma isRelUpperSet_true_iff_isUpperSet
  proof: by
  grind [IsUpperSet, IsRelUpperSet]

中文:
引理 isRelUpperSet_true_iff_isUpperSet
  证明: by
  grind [IsUpperSet, IsRelUpperSet]
-/
@[simp] lemma isRelUpperSet_true_iff_isUpperSet :
    IsRelUpperSet s (fun _ => True) ↔ IsUpperSet s := by
  grind [IsUpperSet, IsRelUpperSet]

/--
lemma `isRelLowerSet_true_iff_isLowerSet` / 引理 `isRelLowerSet_true_iff_isLowerSet`

English:
lemma isRelLowerSet_true_iff_isLowerSet
  proof: by
  grind [IsLowerSet, IsRelLowerSet]

中文:
引理 isRelLowerSet_true_iff_isLowerSet
  证明: by
  grind [IsLowerSet, IsRelLowerSet]
-/
@[simp] lemma isRelLowerSet_true_iff_isLowerSet :
    IsRelLowerSet s (fun _ => True) ↔ IsLowerSet s := by
  grind [IsLowerSet, IsRelLowerSet]

variable (P) in
/--
lemma `IsUpperSet.isRelUpperSet_sep` / 引理 `IsUpperSet.isRelUpperSet_sep`

English:
lemma IsUpperSet.isRelUpperSet_sep
  given: (hs : IsUpperSet s)
  statement: IsRelUpperSet {x in s | P x} P
  proof: fun _ h => ⟨h.2, fun _ ht hp => ⟨hs ht h.1, hp⟩⟩

中文:
引理 是上集.isRelUpperSet_sep
  条件: (hs : 是上集 s)
  结论: IsRelUpperSet {x in s | P x} P
  证明: fun _ h => ⟨h.2, fun _ ht hp => ⟨hs ht h.1, hp⟩⟩

Depends on / 依赖: variable
-/
lemma IsUpperSet.isRelUpperSet_sep (hs : IsUpperSet s) : IsRelUpperSet {x in s | P x} P :=
  fun _ h => ⟨h.2, fun _ ht hp => ⟨hs ht h.1, hp⟩⟩
variable (P) in
/--
lemma `IsLowerSet.isRelLowerSet_sep` / 引理 `IsLowerSet.isRelLowerSet_sep`

English:
lemma IsLowerSet.isRelLowerSet_sep
  given: (hs : IsLowerSet s)
  statement: IsRelLowerSet {x in s | P x} P
  proof: fun _ h => ⟨h.2, fun _ ht hp => ⟨hs ht h.1, hp⟩⟩

中文:
引理 是下集.isRelLowerSet_sep
  条件: (hs : 是下集 s)
  结论: IsRelLowerSet {x in s | P x} P
  证明: fun _ h => ⟨h.2, fun _ ht hp => ⟨hs ht h.1, hp⟩⟩
-/
lemma IsLowerSet.isRelLowerSet_sep (hs : IsLowerSet s) : IsRelLowerSet {x in s | P x} P :=
  fun _ h => ⟨h.2, fun _ ht hp => ⟨hs ht h.1, hp⟩⟩

/--
lemma `IsRelLowerSet.mono_isLowerSet` / 引理 `IsRelLowerSet.mono_isLowerSet`

English:
lemma IsRelLowerSet.mono_isLowerSet
  given: (ht : IsRelLowerSet t P) (hs : IsLowerSet s) (hst : s subseteq t)
  proof: fun _ h => ⟨(ht (hst h)).1, fun _ ht _ => hs ht h⟩

中文:
引理 IsRelLowerSet.mono_isLowerSet
  条件: (ht : IsRelLowerSet t P) (hs : 是下集 s) (hst : s subseteq t)
  证明: fun _ h => ⟨(ht (hst h)).1, fun _ ht _ => hs ht h⟩
-/
lemma IsRelLowerSet.mono_isLowerSet (ht : IsRelLowerSet t P) (hs : IsLowerSet s) (hst : s subseteq t) :
    IsRelLowerSet s P :=
  fun _ h => ⟨(ht (hst h)).1, fun _ ht _ => hs ht h⟩

/--
lemma `IsRelUpperSet.mono_isUpperSet` / 引理 `IsRelUpperSet.mono_isUpperSet`

English:
lemma IsRelUpperSet.mono_isUpperSet
  given: (ht : IsRelUpperSet t P) (hs : IsUpperSet s) (hst : s subseteq t)
  proof: fun _ h => ⟨(ht (hst h)).1, fun _ ht _ => hs ht h⟩

中文:
引理 IsRelUpperSet.mono_isUpperSet
  条件: (ht : IsRelUpperSet t P) (hs : 是上集 s) (hst : s subseteq t)
  证明: fun _ h => ⟨(ht (hst h)).1, fun _ ht _ => hs ht h⟩
-/
lemma IsRelUpperSet.mono_isUpperSet (ht : IsRelUpperSet t P) (hs : IsUpperSet s) (hst : s subseteq t) :
    IsRelUpperSet s P :=
  fun _ h => ⟨(ht (hst h)).1, fun _ ht _ => hs ht h⟩

/--
lemma `IsRelUpperSet.prop_of_mem` / 引理 `IsRelUpperSet.prop_of_mem`

English:
lemma IsRelUpperSet.prop_of_mem
  given: (hs : IsRelUpperSet s P) (h : a in s)
  statement: P a
  proof: (hs h).1

中文:
引理 IsRelUpperSet.prop_of_mem
  条件: (hs : IsRelUpperSet s P) (h : a in s)
  结论: P a
  证明: (hs h).1
-/
lemma IsRelUpperSet.prop_of_mem (hs : IsRelUpperSet s P) (h : a in s) : P a := (hs h).1
/--
lemma `IsRelLowerSet.prop_of_mem` / 引理 `IsRelLowerSet.prop_of_mem`

English:
lemma IsRelLowerSet.prop_of_mem
  given: (hs : IsRelLowerSet s P) (h : a in s)
  statement: P a
  proof: (hs h).1

中文:
引理 IsRelLowerSet.prop_of_mem
  条件: (hs : IsRelLowerSet s P) (h : a in s)
  结论: P a
  证明: (hs h).1
-/
lemma IsRelLowerSet.prop_of_mem (hs : IsRelLowerSet s P) (h : a in s) : P a := (hs h).1

/--
lemma `IsRelUpperSet.mem_of_le` / 引理 `IsRelUpperSet.mem_of_le`

English:
lemma IsRelUpperSet.mem_of_le
  given: (hs : IsRelUpperSet s P) (h : a in s) (h₁ : a <= b) (h₂ : P b)
  proof: (hs h).2 h₁ h₂

中文:
引理 IsRelUpperSet.mem_of_le
  条件: (hs : IsRelUpperSet s P) (h : a in s) (h₁ : a <= b) (h₂ : P b)
  证明: (hs h).2 h₁ h₂
-/
lemma IsRelUpperSet.mem_of_le (hs : IsRelUpperSet s P) (h : a in s) (h₁ : a <= b) (h₂ : P b) :
    b in s := (hs h).2 h₁ h₂
/--
lemma `IsRelLowerSet.mem_of_le` / 引理 `IsRelLowerSet.mem_of_le`

English:
lemma IsRelLowerSet.mem_of_le
  given: (hs : IsRelLowerSet s P) (h : a in s) (h₁ : b <= a) (h₂ : P b)
  proof: (hs h).2 h₁ h₂

中文:
引理 IsRelLowerSet.mem_of_le
  条件: (hs : IsRelLowerSet s P) (h : a in s) (h₁ : b <= a) (h₂ : P b)
  证明: (hs h).2 h₁ h₂
-/
lemma IsRelLowerSet.mem_of_le (hs : IsRelLowerSet s P) (h : a in s) (h₁ : b <= a) (h₂ : P b) :
    b in s := (hs h).2 h₁ h₂

/--
lemma `isRelUpperSet_empty` / 引理 `isRelUpperSet_empty`

English:
lemma isRelUpperSet_empty
  statement: IsRelUpperSet (∅ : Set α) P
  proof: fun _ => False.elim

中文:
引理 isRelUpperSet_empty
  结论: IsRelUpperSet (∅ : 集合 α) P
  证明: fun _ => False.elim
-/
@[simp] lemma isRelUpperSet_empty : IsRelUpperSet (∅ : Set α) P := fun _ => False.elim
/--
lemma `isRelLowerSet_empty` / 引理 `isRelLowerSet_empty`

English:
lemma isRelLowerSet_empty
  statement: IsRelLowerSet (∅ : Set α) P
  proof: fun _ => False.elim

中文:
引理 isRelLowerSet_empty
  结论: IsRelLowerSet (∅ : 集合 α) P
  证明: fun _ => False.elim
-/
@[simp] lemma isRelLowerSet_empty : IsRelLowerSet (∅ : Set α) P := fun _ => False.elim

/--
lemma `isRelUpperSet_self` / 引理 `isRelUpperSet_self`

English:
lemma isRelUpperSet_self
  statement: IsRelUpperSet s (· in s)
  proof: fun _ b => ⟨b, fun _ _ => id⟩

中文:
引理 isRelUpperSet_self
  结论: IsRelUpperSet s (· in s)
  证明: fun _ b => ⟨b, fun _ _ => id⟩
-/
@[simp] lemma isRelUpperSet_self : IsRelUpperSet s (· in s) := fun _ b => ⟨b, fun _ _ => id⟩
/--
lemma `isRelLowerSet_self` / 引理 `isRelLowerSet_self`

English:
lemma isRelLowerSet_self
  statement: IsRelLowerSet s (· in s)
  proof: fun _ b => ⟨b, fun _ _ => id⟩

中文:
引理 isRelLowerSet_self
  结论: IsRelLowerSet s (· in s)
  证明: fun _ b => ⟨b, fun _ _ => id⟩
-/
@[simp] lemma isRelLowerSet_self : IsRelLowerSet s (· in s) := fun _ b => ⟨b, fun _ _ => id⟩

/--
lemma `IsRelUpperSet.union` / 引理 `IsRelUpperSet.union`

English:
lemma IsRelUpperSet.union
  given: (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P)
  proof: fun b mb => by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y => .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y => .inr ((ht h).2 x y)⟩

中文:
引理 IsRelUpperSet.union
  条件: (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P)
  证明: fun b mb => by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y => .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y => .inr ((ht h).2 x y)⟩
-/
lemma IsRelUpperSet.union (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P) :
    IsRelUpperSet (s union t) P := fun b mb => by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y => .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y => .inr ((ht h).2 x y)⟩

/--
lemma `IsRelLowerSet.union` / 引理 `IsRelLowerSet.union`

English:
lemma IsRelLowerSet.union
  given: (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P)
  proof: fun b mb => by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y => .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y => .inr ((ht h).2 x y)⟩

中文:
引理 IsRelLowerSet.union
  条件: (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P)
  证明: fun b mb => by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y => .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y => .inr ((ht h).2 x y)⟩
-/
lemma IsRelLowerSet.union (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P) :
    IsRelLowerSet (s union t) P := fun b mb => by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y => .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y => .inr ((ht h).2 x y)⟩

/--
lemma `IsRelUpperSet.inter` / 引理 `IsRelUpperSet.inter`

English:
lemma IsRelUpperSet.inter
  given: (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P)
  proof: fun b ⟨bs, bt⟩ => by
  simp_all only [IsRelUpperSet, true_and]
  exact fun _ x y => ⟨(hs bs).2 x y, (ht bt).2 x y⟩

中文:
引理 IsRelUpperSet.inter
  条件: (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P)
  证明: fun b ⟨bs, bt⟩ => by
  simp_all only [IsRelUpperSet, true_and]
  exact fun _ x y => ⟨(hs bs).2 x y, (ht bt).2 x y⟩

Depends on / 依赖: IsRelUpperSet, true_and
-/
lemma IsRelUpperSet.inter (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P) :
    IsRelUpperSet (s inter t) P := fun b ⟨bs, bt⟩ => by
  simp_all only [IsRelUpperSet, true_and]
  exact fun _ x y => ⟨(hs bs).2 x y, (ht bt).2 x y⟩

/--
lemma `IsRelLowerSet.inter` / 引理 `IsRelLowerSet.inter`

English:
lemma IsRelLowerSet.inter
  given: (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P)
  proof: fun b ⟨bs, bt⟩ => by
  simp_all only [IsRelLowerSet, true_and]
  exact fun _ x y => ⟨(hs bs).2 x y, (ht bt).2 x y⟩

中文:
引理 IsRelLowerSet.inter
  条件: (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P)
  证明: fun b ⟨bs, bt⟩ => by
  simp_all only [IsRelLowerSet, true_and]
  exact fun _ x y => ⟨(hs bs).2 x y, (ht bt).2 x y⟩

Depends on / 依赖: IsRelLowerSet, true_and
-/
lemma IsRelLowerSet.inter (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P) :
    IsRelLowerSet (s inter t) P := fun b ⟨bs, bt⟩ => by
  simp_all only [IsRelLowerSet, true_and]
  exact fun _ x y => ⟨(hs bs).2 x y, (ht bt).2 x y⟩

/--
lemma `IsRelUpperSet.sUnion` / 引理 `IsRelUpperSet.sUnion`

English:
lemma IsRelUpperSet.sUnion
  given: {S : Set (Set α)} (hS : forall s in S, IsRelUpperSet s P)
  proof: fun _ ⟨s, ms, mb⟩ =>
  ⟨(hS s ms mb).1, fun _ x y => ⟨s, ms, (hS s ms mb).2 x y⟩⟩

中文:
引理 IsRelUpperSet.集合并集
  条件: {S : 集合 (集合 α)} (hS : 对任意 s in S, IsRelUpperSet s P)
  证明: fun _ ⟨s, ms, mb⟩ =>
  ⟨(hS s ms mb).1, fun _ x y => ⟨s, ms, (hS s ms mb).2 x y⟩⟩
-/
protected lemma IsRelUpperSet.sUnion {S : Set (Set α)} (hS : forall s in S, IsRelUpperSet s P) :
    IsRelUpperSet (⋃₀ S) P := fun _ ⟨s, ms, mb⟩ =>
  ⟨(hS s ms mb).1, fun _ x y => ⟨s, ms, (hS s ms mb).2 x y⟩⟩

/--
lemma `IsRelLowerSet.sUnion` / 引理 `IsRelLowerSet.sUnion`

English:
lemma IsRelLowerSet.sUnion
  given: {S : Set (Set α)} (hS : forall s in S, IsRelLowerSet s P)
  proof: fun _ ⟨s, ms, mb⟩ =>
  ⟨(hS s ms mb).1, fun _ x y => ⟨s, ms, (hS s ms mb).2 x y⟩⟩

中文:
引理 IsRelLowerSet.集合并集
  条件: {S : 集合 (集合 α)} (hS : 对任意 s in S, IsRelLowerSet s P)
  证明: fun _ ⟨s, ms, mb⟩ =>
  ⟨(hS s ms mb).1, fun _ x y => ⟨s, ms, (hS s ms mb).2 x y⟩⟩
-/
protected lemma IsRelLowerSet.sUnion {S : Set (Set α)} (hS : forall s in S, IsRelLowerSet s P) :
    IsRelLowerSet (⋃₀ S) P := fun _ ⟨s, ms, mb⟩ =>
  ⟨(hS s ms mb).1, fun _ x y => ⟨s, ms, (hS s ms mb).2 x y⟩⟩

/--
lemma `IsRelUpperSet.iUnion` / 引理 `IsRelUpperSet.iUnion`

English:
lemma IsRelUpperSet.iUnion
  given: {f : ι -> Set α} (hf : forall i, IsRelUpperSet (f i) P)
  proof: .sUnion (forall_mem_range.2 hf)

中文:
引理 IsRelUpperSet.iUnion
  条件: {f : ι -> 集合 α} (hf : 对任意 i, IsRelUpperSet (f i) P)
  证明: .sUnion (forall_mem_range.2 hf)
-/
protected lemma IsRelUpperSet.iUnion {f : ι -> Set α} (hf : forall i, IsRelUpperSet (f i) P) :
    IsRelUpperSet (⋃ i, f i) P :=
  .sUnion (forall_mem_range.2 hf)

/--
lemma `IsRelLowerSet.iUnion` / 引理 `IsRelLowerSet.iUnion`

English:
lemma IsRelLowerSet.iUnion
  given: {f : ι -> Set α} (hf : forall i, IsRelLowerSet (f i) P)
  proof: .sUnion (forall_mem_range.2 hf)

中文:
引理 IsRelLowerSet.iUnion
  条件: {f : ι -> 集合 α} (hf : 对任意 i, IsRelLowerSet (f i) P)
  证明: .sUnion (forall_mem_range.2 hf)
-/
protected lemma IsRelLowerSet.iUnion {f : ι -> Set α} (hf : forall i, IsRelLowerSet (f i) P) :
    IsRelLowerSet (⋃ i, f i) P :=
  .sUnion (forall_mem_range.2 hf)

/--
lemma `IsRelUpperSet.iUnion₂` / 引理 `IsRelUpperSet.iUnion₂`

English:
lemma IsRelUpperSet.iUnion₂
  given: {f : forall i, κ i -> Set α} (hf : forall i j, IsRelUpperSet (f i j) P)
  proof: .iUnion fun i => .iUnion (hf i)

中文:
引理 IsRelUpperSet.iUnion₂
  条件: {f : 对任意 i, κ i -> 集合 α} (hf : 对任意 i j, IsRelUpperSet (f i j) P)
  证明: .iUnion fun i => .iUnion (hf i)
-/
protected lemma IsRelUpperSet.iUnion₂ {f : forall i, κ i -> Set α} (hf : forall i j, IsRelUpperSet (f i j) P) :
    IsRelUpperSet (⋃ (i) (j), f i j) P :=
  .iUnion fun i => .iUnion (hf i)

/--
lemma `IsRelLowerSet.iUnion₂` / 引理 `IsRelLowerSet.iUnion₂`

English:
lemma IsRelLowerSet.iUnion₂
  given: {f : forall i, κ i -> Set α} (hf : forall i j, IsRelLowerSet (f i j) P)
  proof: .iUnion fun i => .iUnion (hf i)

中文:
引理 IsRelLowerSet.iUnion₂
  条件: {f : 对任意 i, κ i -> 集合 α} (hf : 对任意 i j, IsRelLowerSet (f i j) P)
  证明: .iUnion fun i => .iUnion (hf i)
-/
protected lemma IsRelLowerSet.iUnion₂ {f : forall i, κ i -> Set α} (hf : forall i j, IsRelLowerSet (f i j) P) :
    IsRelLowerSet (⋃ (i) (j), f i j) P :=
  .iUnion fun i => .iUnion (hf i)

/--
lemma `IsRelUpperSet.sInter` / 引理 `IsRelUpperSet.sInter`

English:
lemma IsRelUpperSet.sInter
  proof: fun b mb => by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms => (hf s ms (mb s ms)).2 x y⟩

中文:
引理 IsRelUpperSet.集合交集
  证明: fun b mb => by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms => (hf s ms (mb s ms)).2 x y⟩
-/
protected lemma IsRelUpperSet.sInter
    {S : Set (Set α)} (hS : S.Nonempty) (hf : forall s in S, IsRelUpperSet s P) :
    IsRelUpperSet (⋂₀ S) P := fun b mb => by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms => (hf s ms (mb s ms)).2 x y⟩

/--
lemma `IsRelLowerSet.sInter` / 引理 `IsRelLowerSet.sInter`

English:
lemma IsRelLowerSet.sInter
  proof: fun b mb => by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms => (hf s ms (mb s ms)).2 x y⟩

中文:
引理 IsRelLowerSet.集合交集
  证明: fun b mb => by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms => (hf s ms (mb s ms)).2 x y⟩
-/
protected lemma IsRelLowerSet.sInter
    {S : Set (Set α)} (hS : S.Nonempty) (hf : forall s in S, IsRelLowerSet s P) :
    IsRelLowerSet (⋂₀ S) P := fun b mb => by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms => (hf s ms (mb s ms)).2 x y⟩

/--
lemma `IsRelUpperSet.iInter` / 引理 `IsRelUpperSet.iInter`

English:
lemma IsRelUpperSet.iInter
  proof: .sInter (range_nonempty f) (forall_mem_range.2 hf)

中文:
引理 IsRelUpperSet.i整数er
  证明: .sInter (range_nonempty f) (forall_mem_range.2 hf)
-/
protected lemma IsRelUpperSet.iInter
    [Nonempty ι] {f : ι -> Set α} (hf : forall i, IsRelUpperSet (f i) P) : IsRelUpperSet (⋂ i, f i) P :=
  .sInter (range_nonempty f) (forall_mem_range.2 hf)

/--
lemma `IsRelLowerSet.iInter` / 引理 `IsRelLowerSet.iInter`

English:
lemma IsRelLowerSet.iInter
  proof: .sInter (range_nonempty f) (forall_mem_range.2 hf)

中文:
引理 IsRelLowerSet.i整数er
  证明: .sInter (range_nonempty f) (forall_mem_range.2 hf)
-/
protected lemma IsRelLowerSet.iInter
    [Nonempty ι] {f : ι -> Set α} (hf : forall i, IsRelLowerSet (f i) P) : IsRelLowerSet (⋂ i, f i) P :=
  .sInter (range_nonempty f) (forall_mem_range.2 hf)

/--
lemma `IsRelUpperSet.iInter₂` / 引理 `IsRelUpperSet.iInter₂`

English:
lemma IsRelUpperSet.iInter₂
  statement: [Nonempty ι] [forall i, Nonempty (κ i)]
  proof: .iInter fun i => .iInter (hf i)

中文:
引理 IsRelUpperSet.i整数er₂
  结论: [非空 ι] [对任意 i, 非空 (κ i)]
  证明: .iInter fun i => .iInter (hf i)
-/
protected lemma IsRelUpperSet.iInter₂ [Nonempty ι] [forall i, Nonempty (κ i)]
    {f : forall i, κ i -> Set α} (hf : forall i j, IsRelUpperSet (f i j) P) :
    IsRelUpperSet (⋂ (i) (j), f i j) P :=
  .iInter fun i => .iInter (hf i)

/--
lemma `IsRelLowerSet.iInter₂` / 引理 `IsRelLowerSet.iInter₂`

English:
lemma IsRelLowerSet.iInter₂
  statement: [Nonempty ι] [forall i, Nonempty (κ i)]
  proof: .iInter fun i => .iInter (hf i)

中文:
引理 IsRelLowerSet.i整数er₂
  结论: [非空 ι] [对任意 i, 非空 (κ i)]
  证明: .iInter fun i => .iInter (hf i)
-/
protected lemma IsRelLowerSet.iInter₂ [Nonempty ι] [forall i, Nonempty (κ i)]
    {f : forall i, κ i -> Set α} (hf : forall i j, IsRelLowerSet (f i j) P) :
    IsRelLowerSet (⋂ (i) (j), f i j) P :=
  .iInter fun i => .iInter (hf i)

/--
lemma `isUpperSet_subtype_iff_isRelUpperSet` / 引理 `isUpperSet_subtype_iff_isRelUpperSet`

English:
lemma isUpperSet_subtype_iff_isRelUpperSet
  given: {s : Set { x // P x }}
  proof: by
  refine ⟨fun h a x => ?_, fun h a b x y => ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y => by simpa [h (show a <= ⟨b, y⟩ by exact x) ma]⟩
  · have ma : a.1 in Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, Subtype.coe_inj, exists_eq_right] using (h ma).2 x b.2

中文:
引理 isUpperSet_subtype_iff_isRelUpperSet
  条件: {s : 集合 { x // P x }}
  证明: by
  refine ⟨fun h a x => ?_, fun h a b x y => ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y => by simpa [h (show a <= ⟨b, y⟩ by exact x) ma]⟩
  · have ma : a.1 in Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, Subtype.coe_inj, exists_eq_right] using (h ma).2 x b.2

Depends on / 依赖: Subtype, Subtype.coe_inj, Subtype.val, coe_inj, exists_eq_right, mem_image
-/
lemma isUpperSet_subtype_iff_isRelUpperSet {s : Set { x // P x }} :
    IsUpperSet s ↔ IsRelUpperSet (Subtype.val '' s) P := by
  refine ⟨fun h a x => ?_, fun h a b x y => ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y => by simpa [h (show a <= ⟨b, y⟩ by exact x) ma]⟩
  · have ma : a.1 in Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, Subtype.coe_inj, exists_eq_right] using (h ma).2 x b.2

/--
lemma `isLowerSet_subtype_iff_isRelLowerSet` / 引理 `isLowerSet_subtype_iff_isRelLowerSet`

English:
lemma isLowerSet_subtype_iff_isRelLowerSet
  given: {s : Set { x // P x }}
  proof: by
  refine ⟨fun h a x => ?_, fun h a b x y => ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y => by simpa [h (show ⟨b, y⟩ <= a by exact x) ma]⟩
  · have ma : a.1 in Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, Subtype.coe_inj, exists_eq_right] using (h ma).2 x b.2

中文:
引理 isLowerSet_subtype_iff_isRelLowerSet
  条件: {s : 集合 { x // P x }}
  证明: by
  refine ⟨fun h a x => ?_, fun h a b x y => ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y => by simpa [h (show ⟨b, y⟩ <= a by exact x) ma]⟩
  · have ma : a.1 in Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, Subtype.coe_inj, exists_eq_right] using (h ma).2 x b.2

Depends on / 依赖: Subtype, Subtype.coe_inj, Subtype.val, coe_inj, exists_eq_right, mem_image
-/
lemma isLowerSet_subtype_iff_isRelLowerSet {s : Set { x // P x }} :
    IsLowerSet s ↔ IsRelLowerSet (Subtype.val '' s) P := by
  refine ⟨fun h a x => ?_, fun h a b x y => ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y => by simpa [h (show ⟨b, y⟩ <= a by exact x) ma]⟩
  · have ma : a.1 in Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, Subtype.coe_inj, exists_eq_right] using (h ma).2 x b.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (RelUpperSet P) α
  body: RelUpperSet.carrier
  coe_injective s t h := by cases s; cases t; congr

中文:
实例 :
  签名: 集合状 (关系上集 P) α
  定义体: RelUpperSet.carrier
  coe_injective s t h := by cases s; cases t; congr

Depends on / 依赖: RelUpperSet, RelUpperSet.carrier, carrier
-/
instance : SetLike (RelUpperSet P) α where
  coe := RelUpperSet.carrier
  coe_injective s t h := by cases s; cases t; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (RelUpperSet P)
  body: .ofSetLike (RelUpperSet P) α

中文:
实例 :
  签名: 偏序 (关系上集 P)
  定义体: .ofSetLike (RelUpperSet P) α

Depends on / 依赖: RelUpperSet, ofSetLike
-/
instance : PartialOrder (RelUpperSet P) := .ofSetLike (RelUpperSet P) α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (RelLowerSet P) α
  body: RelLowerSet.carrier
  coe_injective s t h := by cases s; cases t; congr

中文:
实例 :
  签名: 集合状 (关系下集 P) α
  定义体: RelLowerSet.carrier
  coe_injective s t h := by cases s; cases t; congr

Depends on / 依赖: RelLowerSet, RelLowerSet.carrier, carrier
-/
instance : SetLike (RelLowerSet P) α where
  coe := RelLowerSet.carrier
  coe_injective s t h := by cases s; cases t; congr

/--
lemma `RelUpperSet.isRelUpperSet` / 引理 `RelUpperSet.isRelUpperSet`

English:
lemma RelUpperSet.isRelUpperSet
  given: (u : RelUpperSet P)
  statement: IsRelUpperSet u P
  proof: u.isRelUpperSet'

中文:
引理 关系上集.isRelUpperSet
  条件: (u : 关系上集 P)
  结论: IsRelUpperSet u P
  证明: u.isRelUpperSet'

Depends on / 依赖: isRelUpperSet, u.isRelUpperSet
-/
lemma RelUpperSet.isRelUpperSet (u : RelUpperSet P) : IsRelUpperSet u P := u.isRelUpperSet'
/--
lemma `RelLowerSet.isRelLowerSet` / 引理 `RelLowerSet.isRelLowerSet`

English:
lemma RelLowerSet.isRelLowerSet
  given: (l : RelLowerSet P)
  statement: IsRelLowerSet l P
  proof: l.isRelLowerSet'

中文:
引理 关系下集.isRelLowerSet
  条件: (l : 关系下集 P)
  结论: IsRelLowerSet l P
  证明: l.isRelLowerSet'

Depends on / 依赖: isRelLowerSet, l.isRelLowerSet
-/
lemma RelLowerSet.isRelLowerSet (l : RelLowerSet P) : IsRelLowerSet l P := l.isRelLowerSet'

end LE

section Preorder

variable [Preorder α] {c : α}

/--
lemma `isRelUpperSet_Icc_le` / 引理 `isRelUpperSet_Icc_le`

English:
lemma isRelUpperSet_Icc_le
  statement: IsRelUpperSet (Icc a c) (· <= c)
  proof: fun _ b => by
  simp_all only [mem_Icc, and_true, true_and]
  exact fun _ x _ => b.1.trans x

中文:
引理 isRelUpperSet_Icc_le
  结论: IsRelUpperSet (闭区间 a c) (· <= c)
  证明: fun _ b => by
  simp_all only [mem_Icc, and_true, true_and]
  exact fun _ x _ => b.1.trans x

Depends on / 依赖: and_true, mem_Icc, true_and
-/
lemma isRelUpperSet_Icc_le : IsRelUpperSet (Icc a c) (· <= c) := fun _ b => by
  simp_all only [mem_Icc, and_true, true_and]
  exact fun _ x _ => b.1.trans x

/--
lemma `isRelLowerSet_Icc_ge` / 引理 `isRelLowerSet_Icc_ge`

English:
lemma isRelLowerSet_Icc_ge
  statement: IsRelLowerSet (Icc c a) (c <= ·)
  proof: fun _ b => by
  simp_all only [mem_Icc, true_and]
  exact fun _ x _ => x.trans b.2

中文:
引理 isRelLowerSet_Icc_ge
  结论: IsRelLowerSet (闭区间 c a) (c <= ·)
  证明: fun _ b => by
  simp_all only [mem_Icc, true_and]
  exact fun _ x _ => x.trans b.2

Depends on / 依赖: mem_Icc, true_and, x.trans
-/
lemma isRelLowerSet_Icc_ge : IsRelLowerSet (Icc c a) (c <= ·) := fun _ b => by
  simp_all only [mem_Icc, true_and]
  exact fun _ x _ => x.trans b.2

end Preorder
