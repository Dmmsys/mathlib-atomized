/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Intervals `Ixx (f x) (f (Order.succ x))`

In this file we prove

* `Monotone.biUnion_Ico_Ioc_map_succ`: if `α` is a linear archimedean succ order and `β` is a linear
  order, then for any monotone function `f` and `m n : α`, the union of intervals
  `Set.Ioc (f i) (f (Order.succ i))`, `m ≤ i < n`, is equal to `Set.Ioc (f m) (f n)`;

* `Monotone.pairwise_disjoint_on_Ioc_succ`: if `α` is a linear succ order, `β` is a preorder, and
  `f : α → β` is a monotone function, then the intervals `Set.Ioc (f n) (f (Order.succ n))` are
  pairwise disjoint.

For the latter lemma, we also prove various order dual versions.
-/

public section


open Set Order

variable {α β : Type*} [LinearOrder α]

/--
theorem `biUnion_Ici_Ico_map_succ` / 定理 `biUnion_Ici_Ico_map_succ`

English:
theorem biUnion_Ici_Ico_map_succ
  statement: [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α -> β}
  proof: by
apply subset_antisymm
.trans Ico_subset_Ici_self iUnion₂_subset fun i hi => Ico_subset_Ico_left (hf i hi)
  intro b hb
  contrapose h2f
  use b
  simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact Succ.rec (P := fun i _ => f i <= b) hb (by simp_all)

中文:
定理 biUnion_Ici_Ico_map_succ
  结论: [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α -> β}
  证明: by
apply subset_antisymm
.trans Ico_subset_Ici_self iUnion₂_subset fun i hi => Ico_subset_Ico_left (hf i hi)
  intro b hb
  contrapose h2f
  use b
  simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact Succ.rec (P := fun i _ => f i <= b) hb (by simp_all)

Depends on / 依赖: Ico_subset_Ici_self, Ico_subset_Ico_left, Succ.rec, and_imp, contrapose, forall_exists_index, mem_image, subset_antisymm, upperBounds
-/
theorem biUnion_Ici_Ico_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α -> β}
    {a : α} (hf : forall i in Ici a, f a <= f i) (h2f : ¬BddAbove (f '' Ici a)) :
    ⋃ i in Ici a, Ico (f i) (f (succ i)) = Ici (f a) := by
apply subset_antisymm
.trans Ico_subset_Ici_self iUnion₂_subset fun i hi => Ico_subset_Ico_left (hf i hi)
  intro b hb
  contrapose h2f
  use b
  simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact Succ.rec (P := fun i _ => f i <= b) hb (by simp_all)

/--
theorem `biUnion_Ici_Ioc_map_succ` / 定理 `biUnion_Ici_Ioc_map_succ`

English:
theorem biUnion_Ici_Ioc_map_succ
  statement: [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α -> β}
  proof: by
apply subset_antisymm
.trans Ioc_subset_Ioi_self iUnion₂_subset fun i hi => Ioc_subset_Ioc_left (hf i hi)
  intro b hb
  contrapose h2f
  suffices forall i, a <= i -> f i < b from ⟨b, by aesop (add simp [upperBounds, le_of_lt])⟩
  exact Succ.rec (P := fun i _ => f i < b) hb (by simp_all)

中文:
定理 biUnion_Ici_Ioc_map_succ
  结论: [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α -> β}
  证明: by
apply subset_antisymm
.trans Ioc_subset_Ioi_self iUnion₂_subset fun i hi => Ioc_subset_Ioc_left (hf i hi)
  intro b hb
  contrapose h2f
  suffices forall i, a <= i -> f i < b from ⟨b, by aesop (add simp [upperBounds, le_of_lt])⟩
  exact Succ.rec (P := fun i _ => f i < b) hb (by simp_all)

Depends on / 依赖: Ioc_subset_Ioc_left, Ioc_subset_Ioi_self, Succ.rec, contrapose, le_of_lt, subset_antisymm, upperBounds
-/
theorem biUnion_Ici_Ioc_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α -> β}
    {a : α} (hf : forall i in Ici a, f a <= f i) (h2f : ¬BddAbove (f '' Ici a)) :
    ⋃ i in Ici a, Ioc (f i) (f (succ i)) = Ioi (f a) := by
apply subset_antisymm
.trans Ioc_subset_Ioi_self iUnion₂_subset fun i hi => Ioc_subset_Ioc_left (hf i hi)
  intro b hb
  contrapose h2f
  suffices forall i, a <= i -> f i < b from ⟨b, by aesop (add simp [upperBounds, le_of_lt])⟩
  exact Succ.rec (P := fun i _ => f i < b) hb (by simp_all)

/--
theorem `iUnion_Ico_map_succ_eq_Ici` / 定理 `iUnion_Ico_map_succ_eq_Ici`

English:
theorem iUnion_Ico_map_succ_eq_Ici
  statement: [OrderBot α] [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β]
  proof: by
  simpa using biUnion_Ici_Ico_map_succ (f := f) (a := ⊥) (by simpa) (by simpa)

中文:
定理 iUnion_Ico_map_succ_eq_Ici
  结论: [OrderBot α] [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β]
  证明: by
  simpa using biUnion_Ici_Ico_map_succ (f := f) (a := ⊥) (by simpa) (by simpa)

Depends on / 依赖: biUnion_Ici_Ico_map_succ
-/
theorem iUnion_Ico_map_succ_eq_Ici [OrderBot α] [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β]
    {f : α -> β} (hf : forall a, f ⊥ <= f a) (h2f : ¬BddAbove (range f)) :
    (⋃ a : α, Ico (f a) (f (succ a))) = Ici (f ⊥) := by
  simpa using biUnion_Ici_Ico_map_succ (f := f) (a := ⊥) (by simpa) (by simpa)

/--
theorem `iUnion_Ioc_map_succ_eq_Ioi` / 定理 `iUnion_Ioc_map_succ_eq_Ioi`

English:
theorem iUnion_Ioc_map_succ_eq_Ioi
  statement: [OrderBot α] [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β]
  proof: by
  simpa using biUnion_Ici_Ioc_map_succ (f := f) (a := ⊥) (by simpa) (by simpa)

中文:
定理 iUnion_Ioc_map_succ_eq_Ioi
  结论: [OrderBot α] [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β]
  证明: by
  simpa using biUnion_Ici_Ioc_map_succ (f := f) (a := ⊥) (by simpa) (by simpa)

Depends on / 依赖: biUnion_Ici_Ioc_map_succ
-/
theorem iUnion_Ioc_map_succ_eq_Ioi [OrderBot α] [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β]
    {f : α -> β} (hf : forall a, f ⊥ <= f a) (h2f : ¬BddAbove (range f)) :
    (⋃ a : α, Ioc (f a) (f (succ a))) = Ioi (f ⊥) := by
  simpa using biUnion_Ici_Ioc_map_succ (f := f) (a := ⊥) (by simpa) (by simpa)

namespace Monotone

/--
theorem `biUnion_Ico_Ioc_map_succ` / 定理 `biUnion_Ico_Ioc_map_succ`

English:
theorem biUnion_Ico_Ioc_map_succ
  statement: [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α -> β}
  proof: by
  rcases le_total n m with hnm | hmn
  · rw [Ico_eq_empty_of_le hnm, Ioc_eq_empty_of_le (hf hnm), biUnion_empty]
  · refine Succ.rec ?_ ?_ hmn
    · simp
    · intro k hmk ihk
      rw [← Ioc_union_Ioc_eq_Ioc (hf hmk) (hf <| le_succ _)]; rw [union_comm]; rw [← ihk]
      by_cases hk : IsMax k
   

中文:
定理 biUnion_Ico_Ioc_map_succ
  结论: [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α -> β}
  证明: by
  rcases le_total n m with hnm | hmn
  · rw [Ico_eq_empty_of_le hnm, Ioc_eq_empty_of_le (hf hnm), biUnion_empty]
  · refine Succ.rec ?_ ?_ hmn
    · simp
    · intro k hmk ihk
      rw [← Ioc_union_Ioc_eq_Ioc (hf hmk) (hf <| le_succ _)]; rw [union_comm]; rw [← ihk]
      by_cases hk : IsMax k
   

Depends on / 依赖: Ico_eq_empty_of_le, Ico_succ_right_eq_insert_of_not_isMax, Ioc_eq_empty_of_le, Ioc_self, Ioc_union_Ioc_eq_Ioc, Succ.rec, biUnion_empty, biUnion_insert, empty_union, hk.succ_eq, le_succ, le_total, succ_eq, union_comm
-/
theorem biUnion_Ico_Ioc_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α -> β}
    (hf : Monotone f) (m n : α) : ⋃ i in Ico m n, Ioc (f i) (f (succ i)) = Ioc (f m) (f n) := by
  rcases le_total n m with hnm | hmn
  · rw [Ico_eq_empty_of_le hnm, Ioc_eq_empty_of_le (hf hnm), biUnion_empty]
  · refine Succ.rec ?_ ?_ hmn
    · simp
    · intro k hmk ihk
      rw [← Ioc_union_Ioc_eq_Ioc (hf hmk) (hf <| le_succ _)]; rw [union_comm]; rw [← ihk]
      by_cases hk : IsMax k
      · rw [hk.succ_eq, Ioc_self, empty_union]
      · rw [Ico_succ_right_eq_insert_of_not_isMax hmk hk, biUnion_insert]

open scoped Function -- required for scoped `on` notation

/--
theorem `pairwise_disjoint_on_Ioc_succ` / 定理 `pairwise_disjoint_on_Ioc_succ`

English:
theorem pairwise_disjoint_on_Ioc_succ
  given: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  proof: (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
h₂.not_ge h₁.trans hf succ_le_of_lt hmn

中文:
定理 pairwise_disjoint_on_Ioc_succ
  条件: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  证明: (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
h₂.not_ge h₁.trans hf succ_le_of_lt hmn

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, not_ge, pairwise_disjoint_on, succ_le_of_lt
-/
theorem pairwise_disjoint_on_Ioc_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioc (f n) (f (succ n))) :=
  (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
h₂.not_ge h₁.trans hf succ_le_of_lt hmn

/--
theorem `pairwise_disjoint_on_Ico_succ` / 定理 `pairwise_disjoint_on_Ico_succ`

English:
theorem pairwise_disjoint_on_Ico_succ
  given: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  proof: (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
h₁.not_ge (hf <| succ_le_of_lt hmn).trans h₂

中文:
定理 pairwise_disjoint_on_Ico_succ
  条件: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  证明: (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
h₁.not_ge (hf <| succ_le_of_lt hmn).trans h₂

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, not_ge, pairwise_disjoint_on, succ_le_of_lt
-/
theorem pairwise_disjoint_on_Ico_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ico (f n) (f (succ n))) :=
  (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
h₁.not_ge (hf <| succ_le_of_lt hmn).trans h₂

/--
theorem `pairwise_disjoint_on_Ioo_succ` / 定理 `pairwise_disjoint_on_Ioo_succ`

English:
theorem pairwise_disjoint_on_Ioo_succ
  given: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  proof: hf.pairwise_disjoint_on_Ico_succ.mono fun _ _ h => h.mono Ioo_subset_Ico_self Ioo_subset_Ico_self

中文:
定理 pairwise_disjoint_on_Ioo_succ
  条件: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  证明: hf.pairwise_disjoint_on_Ico_succ.mono fun _ _ h => h.mono Ioo_subset_Ico_self Ioo_subset_Ico_self

Depends on / 依赖: Ioo_subset_Ico_self, h.mono, hf.pairwise_disjoint_on_Ico_succ.mono, pairwise_disjoint_on_Ico_succ
-/
theorem pairwise_disjoint_on_Ioo_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioo (f n) (f (succ n))) :=
  hf.pairwise_disjoint_on_Ico_succ.mono fun _ _ h => h.mono Ioo_subset_Ico_self Ioo_subset_Ico_self

/--
theorem `pairwise_disjoint_on_Ioc_pred` / 定理 `pairwise_disjoint_on_Ioc_pred`

English:
theorem pairwise_disjoint_on_Ioc_pred
  given: [PredOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  proof: by
  simpa using! hf.dual.pairwise_disjoint_on_Ico_succ

中文:
定理 pairwise_disjoint_on_Ioc_pred
  条件: [PredOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  证明: by
  simpa using! hf.dual.pairwise_disjoint_on_Ico_succ

Depends on / 依赖: hf.dual.pairwise_disjoint_on_Ico_succ, pairwise_disjoint_on_Ico_succ
-/
theorem pairwise_disjoint_on_Ioc_pred [PredOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioc (f (pred n)) (f n)) := by
  simpa using! hf.dual.pairwise_disjoint_on_Ico_succ

/--
theorem `pairwise_disjoint_on_Ico_pred` / 定理 `pairwise_disjoint_on_Ico_pred`

English:
theorem pairwise_disjoint_on_Ico_pred
  given: [PredOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  proof: by
  simpa using! hf.dual.pairwise_disjoint_on_Ioc_succ

中文:
定理 pairwise_disjoint_on_Ico_pred
  条件: [PredOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  证明: by
  simpa using! hf.dual.pairwise_disjoint_on_Ioc_succ

Depends on / 依赖: hf.dual.pairwise_disjoint_on_Ioc_succ, pairwise_disjoint_on_Ioc_succ
-/
theorem pairwise_disjoint_on_Ico_pred [PredOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ico (f (pred n)) (f n)) := by
  simpa using! hf.dual.pairwise_disjoint_on_Ioc_succ

/--
theorem `pairwise_disjoint_on_Ioo_pred` / 定理 `pairwise_disjoint_on_Ioo_pred`

English:
theorem pairwise_disjoint_on_Ioo_pred
  given: [PredOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  proof: by
  simpa using! hf.dual.pairwise_disjoint_on_Ioo_succ

中文:
定理 pairwise_disjoint_on_Ioo_pred
  条件: [PredOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  证明: by
  simpa using! hf.dual.pairwise_disjoint_on_Ioo_succ

Depends on / 依赖: hf.dual.pairwise_disjoint_on_Ioo_succ, pairwise_disjoint_on_Ioo_succ
-/
theorem pairwise_disjoint_on_Ioo_pred [PredOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioo (f (pred n)) (f n)) := by
  simpa using! hf.dual.pairwise_disjoint_on_Ioo_succ

end Monotone

namespace Antitone

open scoped Function -- required for scoped `on` notation

/--
theorem `pairwise_disjoint_on_Ioc_succ` / 定理 `pairwise_disjoint_on_Ioc_succ`

English:
theorem pairwise_disjoint_on_Ioc_succ
  given: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  proof: hf.dual_left.pairwise_disjoint_on_Ioc_pred

中文:
定理 pairwise_disjoint_on_Ioc_succ
  条件: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  证明: hf.dual_left.pairwise_disjoint_on_Ioc_pred

Depends on / 依赖: dual_left, hf.dual_left.pairwise_disjoint_on_Ioc_pred, pairwise_disjoint_on_Ioc_pred
-/
theorem pairwise_disjoint_on_Ioc_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioc (f (succ n)) (f n)) :=
  hf.dual_left.pairwise_disjoint_on_Ioc_pred

/--
theorem `pairwise_disjoint_on_Ico_succ` / 定理 `pairwise_disjoint_on_Ico_succ`

English:
theorem pairwise_disjoint_on_Ico_succ
  given: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  proof: hf.dual_left.pairwise_disjoint_on_Ico_pred

中文:
定理 pairwise_disjoint_on_Ico_succ
  条件: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  证明: hf.dual_left.pairwise_disjoint_on_Ico_pred

Depends on / 依赖: dual_left, hf.dual_left.pairwise_disjoint_on_Ico_pred, pairwise_disjoint_on_Ico_pred
-/
theorem pairwise_disjoint_on_Ico_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ico (f (succ n)) (f n)) :=
  hf.dual_left.pairwise_disjoint_on_Ico_pred

/--
theorem `pairwise_disjoint_on_Ioo_succ` / 定理 `pairwise_disjoint_on_Ioo_succ`

English:
theorem pairwise_disjoint_on_Ioo_succ
  given: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  proof: hf.dual_left.pairwise_disjoint_on_Ioo_pred

中文:
定理 pairwise_disjoint_on_Ioo_succ
  条件: [SuccOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  证明: hf.dual_left.pairwise_disjoint_on_Ioo_pred

Depends on / 依赖: dual_left, hf.dual_left.pairwise_disjoint_on_Ioo_pred, pairwise_disjoint_on_Ioo_pred
-/
theorem pairwise_disjoint_on_Ioo_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioo (f (succ n)) (f n)) :=
  hf.dual_left.pairwise_disjoint_on_Ioo_pred

/--
theorem `pairwise_disjoint_on_Ioc_pred` / 定理 `pairwise_disjoint_on_Ioc_pred`

English:
theorem pairwise_disjoint_on_Ioc_pred
  given: [PredOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  proof: hf.dual_left.pairwise_disjoint_on_Ioc_succ

中文:
定理 pairwise_disjoint_on_Ioc_pred
  条件: [PredOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  证明: hf.dual_left.pairwise_disjoint_on_Ioc_succ

Depends on / 依赖: dual_left, hf.dual_left.pairwise_disjoint_on_Ioc_succ, pairwise_disjoint_on_Ioc_succ
-/
theorem pairwise_disjoint_on_Ioc_pred [PredOrder α] [Preorder β] {f : α -> β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioc (f n) (f (pred n))) :=
  hf.dual_left.pairwise_disjoint_on_Ioc_succ

/--
theorem `pairwise_disjoint_on_Ico_pred` / 定理 `pairwise_disjoint_on_Ico_pred`

English:
theorem pairwise_disjoint_on_Ico_pred
  given: [PredOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  proof: hf.dual_left.pairwise_disjoint_on_Ico_succ

中文:
定理 pairwise_disjoint_on_Ico_pred
  条件: [PredOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  证明: hf.dual_left.pairwise_disjoint_on_Ico_succ

Depends on / 依赖: dual_left, hf.dual_left.pairwise_disjoint_on_Ico_succ, pairwise_disjoint_on_Ico_succ
-/
theorem pairwise_disjoint_on_Ico_pred [PredOrder α] [Preorder β] {f : α -> β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ico (f n) (f (pred n))) :=
  hf.dual_left.pairwise_disjoint_on_Ico_succ

/--
theorem `pairwise_disjoint_on_Ioo_pred` / 定理 `pairwise_disjoint_on_Ioo_pred`

English:
theorem pairwise_disjoint_on_Ioo_pred
  given: [PredOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  proof: hf.dual_left.pairwise_disjoint_on_Ioo_succ

中文:
定理 pairwise_disjoint_on_Ioo_pred
  条件: [PredOrder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  证明: hf.dual_left.pairwise_disjoint_on_Ioo_succ

Depends on / 依赖: dual_left, hf.dual_left.pairwise_disjoint_on_Ioo_succ, pairwise_disjoint_on_Ioo_succ
-/
theorem pairwise_disjoint_on_Ioo_pred [PredOrder α] [Preorder β] {f : α -> β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioo (f n) (f (pred n))) :=
  hf.dual_left.pairwise_disjoint_on_Ioo_succ

end Antitone
