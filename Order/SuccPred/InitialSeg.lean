/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.InitialSeg
public import Mathlib.Order.SuccPred.Limit

/-!
# Initial segments and successors

We establish some connections between initial segment embeddings and successors and predecessors.
-/

public section

variable {α β : Type*} {a b : α} [PartialOrder α] [PartialOrder β]

open Order

namespace InitialSeg

@[simp]
/--
theorem `apply_covBy_apply_iff` / 定理 `apply_covBy_apply_iff`

English:
theorem apply_covBy_apply_iff
  given: (f : α <=i β)
  statement: f a ⋖ f b ↔ a ⋖ b
  proof: (isLowerSet_range f).ordConnected.apply_covBy_apply_iff f.toOrderEmbedding

@[simp]

中文:
定理 apply_covBy_apply_iff
  条件: (f : α <=i β)
  结论: f a ⋖ f b ↔ a ⋖ b
  证明: (isLowerSet_range f).ordConnected.apply_covBy_apply_iff f.toOrderEmbedding

@[simp]

Depends on / 依赖: apply_covBy_apply_iff, f.toOrderEmbedding, isLowerSet_range, ordConnected, ordConnected.apply_covBy_apply_iff, toOrderEmbedding
-/
theorem apply_covBy_apply_iff (f : α <=i β) : f a ⋖ f b ↔ a ⋖ b :=
  (isLowerSet_range f).ordConnected.apply_covBy_apply_iff f.toOrderEmbedding

@[simp]
/--
theorem `apply_wCovBy_apply_iff` / 定理 `apply_wCovBy_apply_iff`

English:
theorem apply_wCovBy_apply_iff
  given: (f : α <=i β)
  statement: f a ⩿ f b ↔ a ⩿ b
  proof: by
  simp [wcovBy_iff_eq_or_covBy]

中文:
定理 apply_wCovBy_apply_iff
  条件: (f : α <=i β)
  结论: f a ⩿ f b ↔ a ⩿ b
  证明: by
  simp [wcovBy_iff_eq_or_covBy]

Depends on / 依赖: wcovBy_iff_eq_or_covBy
-/
theorem apply_wCovBy_apply_iff (f : α <=i β) : f a ⩿ f b ↔ a ⩿ b := by
  simp [wcovBy_iff_eq_or_covBy]

/--
theorem `map_succ` / 定理 `map_succ`

English:
theorem map_succ
  given: [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α <=i β) (a : α)
  proof: (f.apply_covBy_apply_iff.2 (covBy_succ a)).succ_eq.symm

中文:
定理 map_succ
  条件: [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α <=i β) (a : α)
  证明: (f.apply_covBy_apply_iff.2 (covBy_succ a)).succ_eq.symm

Depends on / 依赖: apply_covBy_apply_iff, covBy_succ, f.apply_covBy_apply_iff, succ_eq, succ_eq.symm
-/
theorem map_succ [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α <=i β) (a : α) :
    f (succ a) = succ (f a) :=
  (f.apply_covBy_apply_iff.2 (covBy_succ a)).succ_eq.symm

/--
theorem `map_pred` / 定理 `map_pred`

English:
theorem map_pred
  given: [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α <=i β) (a : α)
  proof: (f.apply_covBy_apply_iff.2 (pred_covBy a)).pred_eq.symm

@[simp]

中文:
定理 map_pred
  条件: [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α <=i β) (a : α)
  证明: (f.apply_covBy_apply_iff.2 (pred_covBy a)).pred_eq.symm

@[simp]

Depends on / 依赖: apply_covBy_apply_iff, f.apply_covBy_apply_iff, pred_covBy, pred_eq, pred_eq.symm
-/
theorem map_pred [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α <=i β) (a : α) :
    f (pred a) = pred (f a) :=
  (f.apply_covBy_apply_iff.2 (pred_covBy a)).pred_eq.symm

@[simp]
/--
theorem `isSuccPrelimit_apply_iff` / 定理 `isSuccPrelimit_apply_iff`

English:
theorem isSuccPrelimit_apply_iff
  given: (f : α <=i β)
  statement: IsSuccPrelimit (f a) ↔ IsSuccPrelimit a
  proof: by
  constructor <;> intro h b hb
  · rw [← f.apply_covBy_apply_iff] at hb
    exact h _ hb
  · obtain ⟨c, rfl⟩ := f.mem_range_of_rel hb.lt
    rw [f.apply_covBy_apply_iff] at hb
    exact h _ hb

@[simp]

中文:
定理 isSuccPrelimit_apply_iff
  条件: (f : α <=i β)
  结论: IsSuccPrelimit (f a) ↔ IsSuccPrelimit a
  证明: by
  constructor <;> intro h b hb
  · rw [← f.apply_covBy_apply_iff] at hb
    exact h _ hb
  · obtain ⟨c, rfl⟩ := f.mem_range_of_rel hb.lt
    rw [f.apply_covBy_apply_iff] at hb
    exact h _ hb

@[simp]

Depends on / 依赖: apply_covBy_apply_iff, f.apply_covBy_apply_iff, f.mem_range_of_rel, hb.lt, mem_range_of_rel
-/
theorem isSuccPrelimit_apply_iff (f : α <=i β) : IsSuccPrelimit (f a) ↔ IsSuccPrelimit a := by
  constructor <;> intro h b hb
  · rw [← f.apply_covBy_apply_iff] at hb
    exact h _ hb
  · obtain ⟨c, rfl⟩ := f.mem_range_of_rel hb.lt
    rw [f.apply_covBy_apply_iff] at hb
    exact h _ hb

@[simp]
/--
theorem `isSuccLimit_apply_iff` / 定理 `isSuccLimit_apply_iff`

English:
theorem isSuccLimit_apply_iff
  given: (f : α <=i β)
  statement: IsSuccLimit (f a) ↔ IsSuccLimit a
  proof: by
  simp [isSuccLimit_iff]

alias ⟨_, map_isSuccPrelimit⟩ := isSuccPrelimit_apply_iff
alias ⟨_, map_isSuccLimit⟩ := isSuccLimit_apply_iff

中文:
定理 isSuccLimit_apply_iff
  条件: (f : α <=i β)
  结论: IsSuccLimit (f a) ↔ IsSuccLimit a
  证明: by
  simp [isSuccLimit_iff]

alias ⟨_, map_isSuccPrelimit⟩ := isSuccPrelimit_apply_iff
alias ⟨_, map_isSuccLimit⟩ := isSuccLimit_apply_iff

Depends on / 依赖: isSuccLimit_iff
-/
theorem isSuccLimit_apply_iff (f : α <=i β) : IsSuccLimit (f a) ↔ IsSuccLimit a := by
  simp [isSuccLimit_iff]

alias ⟨_, map_isSuccPrelimit⟩ := isSuccPrelimit_apply_iff
alias ⟨_, map_isSuccLimit⟩ := isSuccLimit_apply_iff

end InitialSeg

namespace PrincipalSeg

@[simp]
/--
theorem `apply_covBy_apply_iff` / 定理 `apply_covBy_apply_iff`

English:
theorem apply_covBy_apply_iff
  given: (f : α <i β)
  statement: f a ⋖ f b ↔ a ⋖ b
  proof: (f : α <=i β).apply_covBy_apply_iff

@[simp]

中文:
定理 apply_covBy_apply_iff
  条件: (f : α <i β)
  结论: f a ⋖ f b ↔ a ⋖ b
  证明: (f : α <=i β).apply_covBy_apply_iff

@[simp]

Depends on / 依赖: apply_covBy_apply_iff
-/
theorem apply_covBy_apply_iff (f : α <i β) : f a ⋖ f b ↔ a ⋖ b :=
  (f : α <=i β).apply_covBy_apply_iff

@[simp]
/--
theorem `apply_wCovBy_apply_iff` / 定理 `apply_wCovBy_apply_iff`

English:
theorem apply_wCovBy_apply_iff
  given: (f : α <i β)
  statement: f a ⩿ f b ↔ a ⩿ b
  proof: (f : α <=i β).apply_wCovBy_apply_iff

中文:
定理 apply_wCovBy_apply_iff
  条件: (f : α <i β)
  结论: f a ⩿ f b ↔ a ⩿ b
  证明: (f : α <=i β).apply_wCovBy_apply_iff

Depends on / 依赖: apply_wCovBy_apply_iff
-/
theorem apply_wCovBy_apply_iff (f : α <i β) : f a ⩿ f b ↔ a ⩿ b :=
  (f : α <=i β).apply_wCovBy_apply_iff

/--
theorem `map_succ` / 定理 `map_succ`

English:
theorem map_succ
  given: [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α <i β) (a : α)
  proof: (f : α <=i β).map_succ a

中文:
定理 map_succ
  条件: [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α <i β) (a : α)
  证明: (f : α <=i β).map_succ a

Depends on / 依赖: map_succ
-/
theorem map_succ [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α <i β) (a : α) :
    f (succ a) = succ (f a) :=
  (f : α <=i β).map_succ a

/--
theorem `map_pred` / 定理 `map_pred`

English:
theorem map_pred
  given: [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α <=i β) (a : α)
  proof: (f : α <=i β).map_pred a

@[simp]

中文:
定理 map_pred
  条件: [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α <=i β) (a : α)
  证明: (f : α <=i β).map_pred a

@[simp]

Depends on / 依赖: map_pred
-/
theorem map_pred [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α <=i β) (a : α) :
    f (pred a) = pred (f a) :=
  (f : α <=i β).map_pred a

@[simp]
/--
theorem `isSuccPrelimit_apply_iff` / 定理 `isSuccPrelimit_apply_iff`

English:
theorem isSuccPrelimit_apply_iff
  given: (f : α <i β)
  statement: IsSuccPrelimit (f a) ↔ IsSuccPrelimit a
  proof: (f : α <=i β).isSuccPrelimit_apply_iff

@[simp]

中文:
定理 isSuccPrelimit_apply_iff
  条件: (f : α <i β)
  结论: IsSuccPrelimit (f a) ↔ IsSuccPrelimit a
  证明: (f : α <=i β).isSuccPrelimit_apply_iff

@[simp]

Depends on / 依赖: isSuccPrelimit_apply_iff
-/
theorem isSuccPrelimit_apply_iff (f : α <i β) : IsSuccPrelimit (f a) ↔ IsSuccPrelimit a :=
  (f : α <=i β).isSuccPrelimit_apply_iff

@[simp]
/--
theorem `isSuccLimit_apply_iff` / 定理 `isSuccLimit_apply_iff`

English:
theorem isSuccLimit_apply_iff
  given: (f : α <i β)
  statement: IsSuccLimit (f a) ↔ IsSuccLimit a
  proof: (f : α <=i β).isSuccLimit_apply_iff

alias ⟨_, map_isSuccPrelimit⟩ := isSuccPrelimit_apply_iff
alias ⟨_, map_isSuccLimit⟩ := isSuccLimit_apply_iff

中文:
定理 isSuccLimit_apply_iff
  条件: (f : α <i β)
  结论: IsSuccLimit (f a) ↔ IsSuccLimit a
  证明: (f : α <=i β).isSuccLimit_apply_iff

alias ⟨_, map_isSuccPrelimit⟩ := isSuccPrelimit_apply_iff
alias ⟨_, map_isSuccLimit⟩ := isSuccLimit_apply_iff

Depends on / 依赖: isSuccLimit_apply_iff
-/
theorem isSuccLimit_apply_iff (f : α <i β) : IsSuccLimit (f a) ↔ IsSuccLimit a :=
  (f : α <=i β).isSuccLimit_apply_iff

alias ⟨_, map_isSuccPrelimit⟩ := isSuccPrelimit_apply_iff
alias ⟨_, map_isSuccLimit⟩ := isSuccLimit_apply_iff

end PrincipalSeg
