/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.List.Basic

/-! # Some lemmas about lists involving sets

Split out from `Data.List.Basic` to reduce its dependencies.
-/

public section

variable {α β γ : Type*}

namespace List

@[simp]
/--
theorem `setOfPred_mem_eq_empty_iff` / 定理 `setOfPred_mem_eq_empty_iff`

English:
theorem setOfPred_mem_eq_empty_iff
  given: {l : List α}
  statement: { x | x in l } = ∅ ↔ l = []
  proof: Set.eq_empty_iff_forall_notMem.trans eq_nil_iff_forall_not_mem.symm

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq_empty_iff := setOfPred_mem_eq_empty_iff

中文:
定理 setOfPred_mem_eq_empty_iff
  条件: {l : 列表 α}
  结论: { x | x in l } = ∅ ↔ l = []
  证明: Set.eq_empty_iff_forall_notMem.trans eq_nil_iff_forall_not_mem.symm

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq_empty_iff := setOfPred_mem_eq_empty_iff

Depends on / 依赖: Set.eq_empty_iff_forall_notMem.trans, eq_empty_iff_forall_notMem, eq_nil_iff_forall_not_mem, eq_nil_iff_forall_not_mem.symm
-/
theorem setOfPred_mem_eq_empty_iff {l : List α} : { x | x in l } = ∅ ↔ l = [] :=
  Set.eq_empty_iff_forall_notMem.trans eq_nil_iff_forall_not_mem.symm

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq_empty_iff := setOfPred_mem_eq_empty_iff

/--
theorem `injOn_insertIdx_index_of_notMem` / 定理 `injOn_insertIdx_index_of_notMem`

English:
theorem injOn_insertIdx_index_of_notMem
  given: (l : List α) (x : α) (hx : x ∉ l)
  proof: by
  intro n hn m hm h
  induction l generalizing n m with
  | nil =>
    simp_all [Set.mem_singleton_iff, Set.ofPred_eq_eq_singleton, length]
  | cons hd tl IH =>
    simp only [length, Set.mem_ofPred_eq] at hn hm
    simp only [mem_cons, not_or] at hx
    cases n <;> cases m
    · rfl
    · simp [

中文:
定理 injOn_insertIdx_index_of_notMem
  条件: (l : 列表 α) (x : α) (hx : x ∉ l)
  证明: by
  intro n hn m hm h
  induction l generalizing n m with
  | nil =>
    simp_all [Set.mem_singleton_iff, Set.ofPred_eq_eq_singleton, length]
  | cons hd tl IH =>
    simp only [length, Set.mem_ofPred_eq] at hn hm
    simp only [mem_cons, not_or] at hx
    cases n <;> cases m
    · rfl
    · simp [

Depends on / 依赖: Nat.succ_inj, Nat.succ_le_succ_iff, Ne.symm, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.ofPred_eq_eq_singleton, cons.injEq, generalizing, hx.left, hx.right, insertIdx_succ_cons, length, mem_cons, mem_ofPred_eq, mem_singleton_iff, not_or, ofPred_eq_eq_singleton, succ_inj, succ_le_succ_iff, true_and
-/
theorem injOn_insertIdx_index_of_notMem (l : List α) (x : α) (hx : x ∉ l) :
    Set.InjOn (fun k => l.insertIdx k x) { n | n <= l.length } := by
  intro n hn m hm h
  induction l generalizing n m with
  | nil =>
    simp_all [Set.mem_singleton_iff, Set.ofPred_eq_eq_singleton, length]
  | cons hd tl IH =>
    simp only [length, Set.mem_ofPred_eq] at hn hm
    simp only [mem_cons, not_or] at hx
    cases n <;> cases m
    · rfl
    · simp [hx.left] at h
    · simp [Ne.symm hx.left] at h
    · simp only [insertIdx_succ_cons, cons.injEq, true_and] at h
      rw [Nat.succ_inj]
      refine IH hx.right ?_ ?_ h
      · simpa [Nat.succ_le_succ_iff] using hn
      · simpa [Nat.succ_le_succ_iff] using hm

/--
theorem `foldr_range_subset_of_range_subset` / 定理 `foldr_range_subset_of_range_subset`

English:
theorem foldr_range_subset_of_range_subset
  statement: {f : β -> α -> α} {g : γ -> α -> α}
  proof: by
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons b l H =>
    obtain ⟨c, hgf⟩ := hfg (Set.mem_range_self b)
    obtain ⟨m, hgf'⟩ := H
    rw [foldr_cons]; rw [← hgf]; rw [← hgf']
    exact ⟨c :: m, rfl⟩

中文:
定理 foldr_range_subset_of_range_subset
  结论: {f : β -> α -> α} {g : γ -> α -> α}
  证明: by
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons b l H =>
    obtain ⟨c, hgf⟩ := hfg (Set.mem_range_self b)
    obtain ⟨m, hgf'⟩ := H
    rw [foldr_cons]; rw [← hgf]; rw [← hgf']
    exact ⟨c :: m, rfl⟩

Depends on / 依赖: Set.mem_range_self, foldr_cons, mem_range_self
-/
theorem foldr_range_subset_of_range_subset {f : β -> α -> α} {g : γ -> α -> α}
    (hfg : Set.range f subseteq Set.range g) (a : α) : Set.range (foldr f a) subseteq Set.range (foldr g a) := by
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons b l H =>
    obtain ⟨c, hgf⟩ := hfg (Set.mem_range_self b)
    obtain ⟨m, hgf'⟩ := H
    rw [foldr_cons]; rw [← hgf]; rw [← hgf']
    exact ⟨c :: m, rfl⟩

/--
theorem `foldl_range_subset_of_range_subset` / 定理 `foldl_range_subset_of_range_subset`

English:
theorem foldl_range_subset_of_range_subset
  statement: {f : α -> β -> α} {g : α -> γ -> α}
  proof: by
  change (Set.range fun l => _) subseteq Set.range fun l => _
  -- Porting note: have to write `(foldr_reverse)` instead of `foldr_reverse`.
  simp_rw [← (foldr_reverse), Set.range_comp' _ reverse,
    reverse_involutive.bijective.surjective.range_eq, Set.image_univ]
  exact foldr_range_subset_of

中文:
定理 foldl_range_subset_of_range_subset
  结论: {f : α -> β -> α} {g : α -> γ -> α}
  证明: by
  change (Set.range fun l => _) subseteq Set.range fun l => _
  -- Porting note: have to write `(foldr_reverse)` instead of `foldr_reverse`.
  simp_rw [← (foldr_reverse), Set.range_comp' _ reverse,
    reverse_involutive.bijective.surjective.range_eq, Set.image_univ]
  exact foldr_range_subset_of

Depends on / 依赖: Set.range, subseteq
-/
theorem foldl_range_subset_of_range_subset {f : α -> β -> α} {g : α -> γ -> α}
    (hfg : (Set.range fun a c => f c a) subseteq Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) subseteq Set.range (foldl g a) := by
  change (Set.range fun l => _) subseteq Set.range fun l => _
  -- Porting note: have to write `(foldr_reverse)` instead of `foldr_reverse`.
  simp_rw [← (foldr_reverse), Set.range_comp' _ reverse,
    reverse_involutive.bijective.surjective.range_eq, Set.image_univ]
  exact foldr_range_subset_of_range_subset hfg a

/--
theorem `foldr_range_eq_of_range_eq` / 定理 `foldr_range_eq_of_range_eq`

English:
theorem foldr_range_eq_of_range_eq
  statement: {f : β -> α -> α} {g : γ -> α -> α} (hfg : Set.range f = Set.range g)
  proof: (foldr_range_subset_of_range_subset hfg.le a).antisymm
    (foldr_range_subset_of_range_subset hfg.ge a)

中文:
定理 foldr_range_eq_of_range_eq
  结论: {f : β -> α -> α} {g : γ -> α -> α} (hfg : 集合.range f = 集合.range g)
  证明: (foldr_range_subset_of_range_subset hfg.le a).antisymm
    (foldr_range_subset_of_range_subset hfg.ge a)

Depends on / 依赖: antisymm, foldr_range_subset_of_range_subset, hfg.ge, hfg.le
-/
theorem foldr_range_eq_of_range_eq {f : β -> α -> α} {g : γ -> α -> α} (hfg : Set.range f = Set.range g)
    (a : α) : Set.range (foldr f a) = Set.range (foldr g a) :=
  (foldr_range_subset_of_range_subset hfg.le a).antisymm
    (foldr_range_subset_of_range_subset hfg.ge a)

/--
theorem `foldl_range_eq_of_range_eq` / 定理 `foldl_range_eq_of_range_eq`

English:
theorem foldl_range_eq_of_range_eq
  statement: {f : α -> β -> α} {g : α -> γ -> α}
  proof: (foldl_range_subset_of_range_subset hfg.le a).antisymm
    (foldl_range_subset_of_range_subset hfg.ge a)

中文:
定理 foldl_range_eq_of_range_eq
  结论: {f : α -> β -> α} {g : α -> γ -> α}
  证明: (foldl_range_subset_of_range_subset hfg.le a).antisymm
    (foldl_range_subset_of_range_subset hfg.ge a)

Depends on / 依赖: antisymm, foldl_range_subset_of_range_subset, hfg.ge, hfg.le
-/
theorem foldl_range_eq_of_range_eq {f : α -> β -> α} {g : α -> γ -> α}
    (hfg : (Set.range fun a c => f c a) = Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) = Set.range (foldl g a) :=
  (foldl_range_subset_of_range_subset hfg.le a).antisymm
    (foldl_range_subset_of_range_subset hfg.ge a)



/-!
  ### MapAccumr and Foldr
  Some lemmas relation `mapAccumr` and `foldr`
-/
section MapAccumr

/--
theorem `mapAccumr_eq_foldr` / 定理 `mapAccumr_eq_foldr`

English:
theorem mapAccumr_eq_foldr
  given: {σ : Type*} (f : α -> σ -> σ × β)
  statement: forall (as : List α) (s : σ),

中文:
定理 mapAccumr_eq_foldr
  条件: {σ : 类型} (f : α -> σ -> σ × β)
  结论: 对任意 (as : 列表 α) (s : σ),
-/
theorem mapAccumr_eq_foldr {σ : Type*} (f : α -> σ -> σ × β) : forall (as : List α) (s : σ),
    mapAccumr f as s = List.foldr (fun a s =>
                                    let r := f a s.1
                                    (r.1, r.2 :: s.2)) (s, []) as
  | [], _ => rfl
  | a :: as, s => by
    simp only [mapAccumr, foldr, mapAccumr_eq_foldr f as]

/--
theorem `mapAccumr₂_eq_foldr` / 定理 `mapAccumr₂_eq_foldr`

English:
theorem mapAccumr₂_eq_foldr
  given: {σ φ : Type*} (f : α -> β -> σ -> σ × φ)

中文:
定理 mapAccumr₂_eq_foldr
  条件: {σ φ : 类型} (f : α -> β -> σ -> σ × φ)
-/
theorem mapAccumr₂_eq_foldr {σ φ : Type*} (f : α -> β -> σ -> σ × φ) :
    forall (as : List α) (bs : List β) (s : σ),
    mapAccumr₂ f as bs s = foldr (fun ab s =>
                              let r := f ab.1 ab.2 s.1
                              (r.1, r.2 :: s.2)) (s, []) (as.zip bs)
  | [], [], _ => rfl
  | _ :: _, [], _ => rfl
  | [], _ :: _, _ => rfl
  | a :: as, b :: bs, s => by
    simp only [mapAccumr₂, mapAccumr₂_eq_foldr f as]
    rfl

end MapAccumr

end List
