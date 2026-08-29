/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Compare
public import Mathlib.Order.Max
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Contrapose

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Main theorems

* `monotone_nat_of_le_succ`, `monotone_int_of_le_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n ≤ f (n + 1)` for all `n`, then `f` is monotone.
* `antitone_nat_of_succ_le`, `antitone_int_of_succ_le`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) ≤ f n` for all `n`, then `f` is antitone.
* `strictMono_nat_of_lt_succ`, `strictMono_int_of_lt_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n < f (n + 1)` for all `n`, then `f` is strictly monotone.
* `strictAnti_nat_of_succ_lt`, `strictAnti_int_of_succ_lt`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) < f n` for all `n`, then `f` is strictly antitone.

## Implementation notes

Some of these definitions used to only require `LE α` or `LT α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `Preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## TODO

The above theorems are also true in `ℕ+`, `Fin n`... To make that work, we need `SuccOrder α`
and `IsSuccArchimedean α`.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/

public section

open Function OrderDual

universe u v

variable {ι : Type*} {α : Type u} {β : Type v}

/-! ### Monotonicity on the dual order

Strictly, many of the `*On.dual` lemmas in this section should use `ofDual ⁻¹' s` instead of `s`,
but right now this is not possible as `Set.preimage` is not defined yet, and importing it creates
an import cycle.

Often, you should not need the rewriting lemmas. Instead, you probably want to add `.dual`,
`.dual_left` or `.dual_right` to your `Monotone`/`Antitone` hypothesis.
-/


section OrderDual

variable [Preorder α] [Preorder β] {f : α -> β} {s : Set α}

@[simp]
/--
theorem `monotone_comp_ofDual_iff` / 定理 `monotone_comp_ofDual_iff`

English:
theorem monotone_comp_ofDual_iff
  statement: Monotone (f ∘ ofDual) ↔ Antitone f
  proof: forall_comm

@[simp]

中文:
定理 monotone_comp_ofDual_iff
  结论: 递增 (f ∘ ofDual) ↔ 递减 f
  证明: forall_comm

@[simp]

Depends on / 依赖: forall_comm
-/
theorem monotone_comp_ofDual_iff : Monotone (f ∘ ofDual) ↔ Antitone f :=
  forall_comm

@[simp]
/--
theorem `antitone_comp_ofDual_iff` / 定理 `antitone_comp_ofDual_iff`

English:
theorem antitone_comp_ofDual_iff
  statement: Antitone (f ∘ ofDual) ↔ Monotone f
  proof: forall_comm

@[simp]

中文:
定理 antitone_comp_ofDual_iff
  结论: 递减 (f ∘ ofDual) ↔ 递增 f
  证明: forall_comm

@[simp]

Depends on / 依赖: forall_comm
-/
theorem antitone_comp_ofDual_iff : Antitone (f ∘ ofDual) ↔ Monotone f :=
  forall_comm

@[simp]
/--
theorem `monotone_toDual_comp_iff` / 定理 `monotone_toDual_comp_iff`

English:
theorem monotone_toDual_comp_iff
  statement: Monotone (toDual ∘ f) ↔ Antitone f
  proof: Iff.rfl

@[simp]

中文:
定理 monotone_toDual_comp_iff
  结论: 递增 (toDual ∘ f) ↔ 递减 f
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem monotone_toDual_comp_iff : Monotone (toDual ∘ f) ↔ Antitone f :=
  Iff.rfl

@[simp]
/--
theorem `antitone_toDual_comp_iff` / 定理 `antitone_toDual_comp_iff`

English:
theorem antitone_toDual_comp_iff
  statement: Antitone (toDual ∘ f) ↔ Monotone f
  proof: Iff.rfl

@[simp]

中文:
定理 antitone_toDual_comp_iff
  结论: 递减 (toDual ∘ f) ↔ 递增 f
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem antitone_toDual_comp_iff : Antitone (toDual ∘ f) ↔ Monotone f :=
  Iff.rfl

@[simp]
/--
theorem `monotoneOn_comp_ofDual_iff` / 定理 `monotoneOn_comp_ofDual_iff`

English:
theorem monotoneOn_comp_ofDual_iff
  statement: MonotoneOn (f ∘ ofDual) s ↔ AntitoneOn f s
  proof: forall₂_comm

@[simp]

中文:
定理 monotoneOn_comp_ofDual_iff
  结论: MonotoneOn (f ∘ ofDual) s ↔ AntitoneOn f s
  证明: forall₂_comm

@[simp]
-/
theorem monotoneOn_comp_ofDual_iff : MonotoneOn (f ∘ ofDual) s ↔ AntitoneOn f s :=
  forall₂_comm

@[simp]
/--
theorem `antitoneOn_comp_ofDual_iff` / 定理 `antitoneOn_comp_ofDual_iff`

English:
theorem antitoneOn_comp_ofDual_iff
  statement: AntitoneOn (f ∘ ofDual) s ↔ MonotoneOn f s
  proof: forall₂_comm

@[simp]

中文:
定理 antitoneOn_comp_ofDual_iff
  结论: AntitoneOn (f ∘ ofDual) s ↔ MonotoneOn f s
  证明: forall₂_comm

@[simp]
-/
theorem antitoneOn_comp_ofDual_iff : AntitoneOn (f ∘ ofDual) s ↔ MonotoneOn f s :=
  forall₂_comm

@[simp]
/--
theorem `monotoneOn_toDual_comp_iff` / 定理 `monotoneOn_toDual_comp_iff`

English:
theorem monotoneOn_toDual_comp_iff
  statement: MonotoneOn (toDual ∘ f) s ↔ AntitoneOn f s
  proof: Iff.rfl

@[simp]

中文:
定理 monotoneOn_toDual_comp_iff
  结论: MonotoneOn (toDual ∘ f) s ↔ AntitoneOn f s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem monotoneOn_toDual_comp_iff : MonotoneOn (toDual ∘ f) s ↔ AntitoneOn f s :=
  Iff.rfl

@[simp]
/--
theorem `antitoneOn_toDual_comp_iff` / 定理 `antitoneOn_toDual_comp_iff`

English:
theorem antitoneOn_toDual_comp_iff
  statement: AntitoneOn (toDual ∘ f) s ↔ MonotoneOn f s
  proof: Iff.rfl

@[simp]

中文:
定理 antitoneOn_toDual_comp_iff
  结论: AntitoneOn (toDual ∘ f) s ↔ MonotoneOn f s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem antitoneOn_toDual_comp_iff : AntitoneOn (toDual ∘ f) s ↔ MonotoneOn f s :=
  Iff.rfl

@[simp]
/--
theorem `strictMono_comp_ofDual_iff` / 定理 `strictMono_comp_ofDual_iff`

English:
theorem strictMono_comp_ofDual_iff
  statement: StrictMono (f ∘ ofDual) ↔ StrictAnti f
  proof: forall_comm

@[simp]

中文:
定理 strictMono_comp_ofDual_iff
  结论: 严格递增 (f ∘ ofDual) ↔ 严格递减 f
  证明: forall_comm

@[simp]

Depends on / 依赖: forall_comm
-/
theorem strictMono_comp_ofDual_iff : StrictMono (f ∘ ofDual) ↔ StrictAnti f :=
  forall_comm

@[simp]
/--
theorem `strictAnti_comp_ofDual_iff` / 定理 `strictAnti_comp_ofDual_iff`

English:
theorem strictAnti_comp_ofDual_iff
  statement: StrictAnti (f ∘ ofDual) ↔ StrictMono f
  proof: forall_comm

@[simp]

中文:
定理 strictAnti_comp_ofDual_iff
  结论: 严格递减 (f ∘ ofDual) ↔ 严格递增 f
  证明: forall_comm

@[simp]

Depends on / 依赖: forall_comm
-/
theorem strictAnti_comp_ofDual_iff : StrictAnti (f ∘ ofDual) ↔ StrictMono f :=
  forall_comm

@[simp]
/--
theorem `strictMono_toDual_comp_iff` / 定理 `strictMono_toDual_comp_iff`

English:
theorem strictMono_toDual_comp_iff
  statement: StrictMono (toDual ∘ f : α -> βᵒᵈ) ↔ StrictAnti f
  proof: Iff.rfl

@[simp]

中文:
定理 strictMono_toDual_comp_iff
  结论: 严格递增 (toDual ∘ f : α -> βᵒᵈ) ↔ 严格递减 f
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem strictMono_toDual_comp_iff : StrictMono (toDual ∘ f : α -> βᵒᵈ) ↔ StrictAnti f :=
  Iff.rfl

@[simp]
/--
theorem `strictAnti_toDual_comp_iff` / 定理 `strictAnti_toDual_comp_iff`

English:
theorem strictAnti_toDual_comp_iff
  statement: StrictAnti (toDual ∘ f : α -> βᵒᵈ) ↔ StrictMono f
  proof: Iff.rfl

@[simp]

中文:
定理 strictAnti_toDual_comp_iff
  结论: 严格递减 (toDual ∘ f : α -> βᵒᵈ) ↔ 严格递增 f
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem strictAnti_toDual_comp_iff : StrictAnti (toDual ∘ f : α -> βᵒᵈ) ↔ StrictMono f :=
  Iff.rfl

@[simp]
/--
theorem `strictMonoOn_comp_ofDual_iff` / 定理 `strictMonoOn_comp_ofDual_iff`

English:
theorem strictMonoOn_comp_ofDual_iff
  statement: StrictMonoOn (f ∘ ofDual) s ↔ StrictAntiOn f s
  proof: forall₂_comm

@[simp]

中文:
定理 strictMonoOn_comp_ofDual_iff
  结论: StrictMonoOn (f ∘ ofDual) s ↔ StrictAntiOn f s
  证明: forall₂_comm

@[simp]
-/
theorem strictMonoOn_comp_ofDual_iff : StrictMonoOn (f ∘ ofDual) s ↔ StrictAntiOn f s :=
  forall₂_comm

@[simp]
/--
theorem `strictAntiOn_comp_ofDual_iff` / 定理 `strictAntiOn_comp_ofDual_iff`

English:
theorem strictAntiOn_comp_ofDual_iff
  statement: StrictAntiOn (f ∘ ofDual) s ↔ StrictMonoOn f s
  proof: forall₂_comm

@[simp]

中文:
定理 strictAntiOn_comp_ofDual_iff
  结论: StrictAntiOn (f ∘ ofDual) s ↔ StrictMonoOn f s
  证明: forall₂_comm

@[simp]
-/
theorem strictAntiOn_comp_ofDual_iff : StrictAntiOn (f ∘ ofDual) s ↔ StrictMonoOn f s :=
  forall₂_comm

@[simp]
/--
theorem `strictMonoOn_toDual_comp_iff` / 定理 `strictMonoOn_toDual_comp_iff`

English:
theorem strictMonoOn_toDual_comp_iff
  statement: StrictMonoOn (toDual ∘ f : α -> βᵒᵈ) s ↔ StrictAntiOn f s
  proof: Iff.rfl

@[simp]

中文:
定理 strictMonoOn_toDual_comp_iff
  结论: StrictMonoOn (toDual ∘ f : α -> βᵒᵈ) s ↔ StrictAntiOn f s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem strictMonoOn_toDual_comp_iff : StrictMonoOn (toDual ∘ f : α -> βᵒᵈ) s ↔ StrictAntiOn f s :=
  Iff.rfl

@[simp]
/--
theorem `strictAntiOn_toDual_comp_iff` / 定理 `strictAntiOn_toDual_comp_iff`

English:
theorem strictAntiOn_toDual_comp_iff
  statement: StrictAntiOn (toDual ∘ f : α -> βᵒᵈ) s ↔ StrictMonoOn f s
  proof: Iff.rfl

中文:
定理 strictAntiOn_toDual_comp_iff
  结论: StrictAntiOn (toDual ∘ f : α -> βᵒᵈ) s ↔ StrictMonoOn f s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem strictAntiOn_toDual_comp_iff : StrictAntiOn (toDual ∘ f : α -> βᵒᵈ) s ↔ StrictMonoOn f s :=
  Iff.rfl

/--
theorem `monotone_dual_iff` / 定理 `monotone_dual_iff`

English:
theorem monotone_dual_iff
  statement: Monotone (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ Monotone f
  proof: by
  rw [monotone_toDual_comp_iff]; rw [antitone_comp_ofDual_iff]

中文:
定理 monotone_dual_iff
  结论: 递增 (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ 递增 f
  证明: by
  rw [monotone_toDual_comp_iff]; rw [antitone_comp_ofDual_iff]

Depends on / 依赖: antitone_comp_ofDual_iff, monotone_toDual_comp_iff
-/
theorem monotone_dual_iff : Monotone (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ Monotone f := by
  rw [monotone_toDual_comp_iff]; rw [antitone_comp_ofDual_iff]

/--
theorem `antitone_dual_iff` / 定理 `antitone_dual_iff`

English:
theorem antitone_dual_iff
  statement: Antitone (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ Antitone f
  proof: by
  rw [antitone_toDual_comp_iff]; rw [monotone_comp_ofDual_iff]

中文:
定理 antitone_dual_iff
  结论: 递减 (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ 递减 f
  证明: by
  rw [antitone_toDual_comp_iff]; rw [monotone_comp_ofDual_iff]

Depends on / 依赖: antitone_toDual_comp_iff, monotone_comp_ofDual_iff
-/
theorem antitone_dual_iff : Antitone (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ Antitone f := by
  rw [antitone_toDual_comp_iff]; rw [monotone_comp_ofDual_iff]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `monotoneOn_dual_iff` / 定理 `monotoneOn_dual_iff`

English:
theorem monotoneOn_dual_iff
  statement: MonotoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ MonotoneOn f s
  proof: by
  rw [monotoneOn_toDual_comp_iff]; rw [antitoneOn_comp_ofDual_iff]

中文:
定理 monotoneOn_dual_iff
  结论: MonotoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ MonotoneOn f s
  证明: by
  rw [monotoneOn_toDual_comp_iff]; rw [antitoneOn_comp_ofDual_iff]

Depends on / 依赖: antitoneOn_comp_ofDual_iff, monotoneOn_toDual_comp_iff
-/
theorem monotoneOn_dual_iff : MonotoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ MonotoneOn f s := by
  rw [monotoneOn_toDual_comp_iff]; rw [antitoneOn_comp_ofDual_iff]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `antitoneOn_dual_iff` / 定理 `antitoneOn_dual_iff`

English:
theorem antitoneOn_dual_iff
  statement: AntitoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ AntitoneOn f s
  proof: by
  rw [antitoneOn_toDual_comp_iff]; rw [monotoneOn_comp_ofDual_iff]

中文:
定理 antitoneOn_dual_iff
  结论: AntitoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ AntitoneOn f s
  证明: by
  rw [antitoneOn_toDual_comp_iff]; rw [monotoneOn_comp_ofDual_iff]

Depends on / 依赖: antitoneOn_toDual_comp_iff, monotoneOn_comp_ofDual_iff
-/
theorem antitoneOn_dual_iff : AntitoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ AntitoneOn f s := by
  rw [antitoneOn_toDual_comp_iff]; rw [monotoneOn_comp_ofDual_iff]

/--
theorem `strictMono_dual_iff` / 定理 `strictMono_dual_iff`

English:
theorem strictMono_dual_iff
  statement: StrictMono (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ StrictMono f
  proof: by
  rw [strictMono_toDual_comp_iff]; rw [strictAnti_comp_ofDual_iff]

中文:
定理 strictMono_dual_iff
  结论: 严格递增 (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ 严格递增 f
  证明: by
  rw [strictMono_toDual_comp_iff]; rw [strictAnti_comp_ofDual_iff]

Depends on / 依赖: strictAnti_comp_ofDual_iff, strictMono_toDual_comp_iff
-/
theorem strictMono_dual_iff : StrictMono (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ StrictMono f := by
  rw [strictMono_toDual_comp_iff]; rw [strictAnti_comp_ofDual_iff]

/--
theorem `strictAnti_dual_iff` / 定理 `strictAnti_dual_iff`

English:
theorem strictAnti_dual_iff
  statement: StrictAnti (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ StrictAnti f
  proof: by
  rw [strictAnti_toDual_comp_iff]; rw [strictMono_comp_ofDual_iff]

中文:
定理 strictAnti_dual_iff
  结论: 严格递减 (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ 严格递减 f
  证明: by
  rw [strictAnti_toDual_comp_iff]; rw [strictMono_comp_ofDual_iff]

Depends on / 依赖: strictAnti_toDual_comp_iff, strictMono_comp_ofDual_iff
-/
theorem strictAnti_dual_iff : StrictAnti (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ StrictAnti f := by
  rw [strictAnti_toDual_comp_iff]; rw [strictMono_comp_ofDual_iff]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `strictMonoOn_dual_iff` / 定理 `strictMonoOn_dual_iff`

English:
theorem strictMonoOn_dual_iff
  proof: by
  rw [strictMonoOn_toDual_comp_iff]; rw [strictAntiOn_comp_ofDual_iff]

中文:
定理 strictMonoOn_dual_iff
  证明: by
  rw [strictMonoOn_toDual_comp_iff]; rw [strictAntiOn_comp_ofDual_iff]

Depends on / 依赖: strictAntiOn_comp_ofDual_iff, strictMonoOn_toDual_comp_iff
-/
theorem strictMonoOn_dual_iff :
    StrictMonoOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ StrictMonoOn f s := by
  rw [strictMonoOn_toDual_comp_iff]; rw [strictAntiOn_comp_ofDual_iff]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `strictAntiOn_dual_iff` / 定理 `strictAntiOn_dual_iff`

English:
theorem strictAntiOn_dual_iff
  proof: by
  rw [strictAntiOn_toDual_comp_iff]; rw [strictMonoOn_comp_ofDual_iff]

alias ⟨_, Monotone.dual_left⟩ := antitone_comp_ofDual_iff

alias ⟨_, Antitone.dual_left⟩ := monotone_comp_ofDual_iff

alias ⟨_, Monotone.dual_right⟩ := antitone_toDual_comp_iff

alias ⟨_, Antitone.dual_right⟩ := monotone_toDu

中文:
定理 strictAntiOn_dual_iff
  证明: by
  rw [strictAntiOn_toDual_comp_iff]; rw [strictMonoOn_comp_ofDual_iff]

alias ⟨_, Monotone.dual_left⟩ := antitone_comp_ofDual_iff

alias ⟨_, Antitone.dual_left⟩ := monotone_comp_ofDual_iff

alias ⟨_, Monotone.dual_right⟩ := antitone_toDual_comp_iff

alias ⟨_, Antitone.dual_right⟩ := monotone_toDu

Depends on / 依赖: strictAntiOn_toDual_comp_iff, strictMonoOn_comp_ofDual_iff
-/
theorem strictAntiOn_dual_iff :
    StrictAntiOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ StrictAntiOn f s := by
  rw [strictAntiOn_toDual_comp_iff]; rw [strictMonoOn_comp_ofDual_iff]

alias ⟨_, Monotone.dual_left⟩ := antitone_comp_ofDual_iff

alias ⟨_, Antitone.dual_left⟩ := monotone_comp_ofDual_iff

alias ⟨_, Monotone.dual_right⟩ := antitone_toDual_comp_iff

alias ⟨_, Antitone.dual_right⟩ := monotone_toDual_comp_iff

alias ⟨_, MonotoneOn.dual_left⟩ := antitoneOn_comp_ofDual_iff

alias ⟨_, AntitoneOn.dual_left⟩ := monotoneOn_comp_ofDual_iff

alias ⟨_, MonotoneOn.dual_right⟩ := antitoneOn_toDual_comp_iff

alias ⟨_, AntitoneOn.dual_right⟩ := monotoneOn_toDual_comp_iff

alias ⟨_, StrictMono.dual_left⟩ := strictAnti_comp_ofDual_iff

alias ⟨_, StrictAnti.dual_left⟩ := strictMono_comp_ofDual_iff

alias ⟨_, StrictMono.dual_right⟩ := strictAnti_toDual_comp_iff

alias ⟨_, StrictAnti.dual_right⟩ := strictMono_toDual_comp_iff

alias ⟨_, StrictMonoOn.dual_left⟩ := strictAntiOn_comp_ofDual_iff

alias ⟨_, StrictAntiOn.dual_left⟩ := strictMonoOn_comp_ofDual_iff

alias ⟨_, StrictMonoOn.dual_right⟩ := strictAntiOn_toDual_comp_iff

alias ⟨_, StrictAntiOn.dual_right⟩ := strictMonoOn_toDual_comp_iff

alias ⟨_, Monotone.dual⟩ := monotone_dual_iff

alias ⟨_, Antitone.dual⟩ := antitone_dual_iff

alias ⟨_, MonotoneOn.dual⟩ := monotoneOn_dual_iff

alias ⟨_, AntitoneOn.dual⟩ := antitoneOn_dual_iff

alias ⟨_, StrictMono.dual⟩ := strictMono_dual_iff

alias ⟨_, StrictAnti.dual⟩ := strictAnti_dual_iff

alias ⟨_, StrictMonoOn.dual⟩ := strictMonoOn_dual_iff

alias ⟨_, StrictAntiOn.dual⟩ := strictAntiOn_dual_iff

end OrderDual

section WellFounded

variable [Preorder α] [Preorder β] {f : α -> β}

@[to_dual]
/--
theorem `StrictMono.wellFoundedLT` / 定理 `StrictMono.wellFoundedLT`

English:
theorem StrictMono.wellFoundedLT
  given: [WellFoundedLT β] (hf : StrictMono f)
  statement: WellFoundedLT α
  proof: Subrelation.isWellFounded (InvImage (· < ·) f) hf.imp

@[to_dual]

中文:
定理 严格递增.wellFoundedLT
  条件: [WellFoundedLT β] (hf : 严格递增 f)
  结论: WellFoundedLT α
  证明: Subrelation.isWellFounded (InvImage (· < ·) f) hf.imp

@[to_dual]

Depends on / 依赖: InvImage, Subrelation, Subrelation.isWellFounded, hf.imp, isWellFounded
-/
theorem StrictMono.wellFoundedLT [WellFoundedLT β] (hf : StrictMono f) : WellFoundedLT α :=
  Subrelation.isWellFounded (InvImage (· < ·) f) hf.imp

@[to_dual]
/--
theorem `StrictAnti.wellFoundedLT` / 定理 `StrictAnti.wellFoundedLT`

English:
theorem StrictAnti.wellFoundedLT
  given: [WellFoundedGT β] (hf : StrictAnti f)
  statement: WellFoundedLT α
  proof: Subrelation.isWellFounded (InvImage (· > ·) f) hf.imp

中文:
定理 严格递减.wellFoundedLT
  条件: [WellFoundedGT β] (hf : 严格递减 f)
  结论: WellFoundedLT α
  证明: Subrelation.isWellFounded (InvImage (· > ·) f) hf.imp

Depends on / 依赖: InvImage, Subrelation, Subrelation.isWellFounded, hf.imp, isWellFounded
-/
theorem StrictAnti.wellFoundedLT [WellFoundedGT β] (hf : StrictAnti f) : WellFoundedLT α :=
  Subrelation.isWellFounded (InvImage (· > ·) f) hf.imp

end WellFounded

/-! ### Miscellaneous monotonicity results -/

section PreorderPartialOrder

variable [Preorder α] [PartialOrder β] {f : α -> β} {s : Set α}

/--
theorem `MonotoneOn.strictMonoOn_of_injOn` / 定理 `MonotoneOn.strictMonoOn_of_injOn`

English:
theorem MonotoneOn.strictMonoOn_of_injOn
  given: (hmono : MonotoneOn f s) (hinj : s.InjOn f)
  proof: .lt_of_ne mt (hinj hx hy) h.ne fun _ hx _ hy h => hmono hx hy h.le

中文:
定理 MonotoneOn.strictMonoOn_of_injOn
  条件: (hmono : MonotoneOn f s) (hinj : s.单射限制 f)
  证明: .lt_of_ne mt (hinj hx hy) h.ne fun _ hx _ hy h => hmono hx hy h.le

Depends on / 依赖: h.le, h.ne, lt_of_ne
-/
theorem MonotoneOn.strictMonoOn_of_injOn (hmono : MonotoneOn f s) (hinj : s.InjOn f) :
    StrictMonoOn f s :=
.lt_of_ne mt (hinj hx hy) h.ne fun _ hx _ hy h => hmono hx hy h.le

/--
theorem `AntitoneOn.strictAntiOn_of_injOn` / 定理 `AntitoneOn.strictAntiOn_of_injOn`

English:
theorem AntitoneOn.strictAntiOn_of_injOn
  given: (hanti : AntitoneOn f s) (hinj : s.InjOn f)
  proof: .lt_of_ne' mt (hinj hx hy) h.ne fun _ hx _ hy h => hanti hx hy h.le

中文:
定理 AntitoneOn.strictAntiOn_of_injOn
  条件: (hanti : AntitoneOn f s) (hinj : s.单射限制 f)
  证明: .lt_of_ne' mt (hinj hx hy) h.ne fun _ hx _ hy h => hanti hx hy h.le

Depends on / 依赖: h.le, h.ne, lt_of_ne
-/
theorem AntitoneOn.strictAntiOn_of_injOn (hanti : AntitoneOn f s) (hinj : s.InjOn f) :
    StrictAntiOn f s :=
.lt_of_ne' mt (hinj hx hy) h.ne fun _ hx _ hy h => hanti hx hy h.le

end PreorderPartialOrder

section Preorder

variable [Preorder α] [Preorder β] {f g : α -> β} {a : α}

@[to_dual]
/--
theorem `StrictMono.isMax_of_apply` / 定理 `StrictMono.isMax_of_apply`

English:
theorem StrictMono.isMax_of_apply
  given: (hf : StrictMono f) (ha : IsMax (f a))
  statement: IsMax a
  proof: of_not_not fun h =>
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMax ha

@[to_dual]

中文:
定理 严格递增.isMax_of_apply
  条件: (hf : 严格递增 f) (ha : IsMax (f a))
  结论: IsMax a
  证明: of_not_not fun h =>
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMax ha

@[to_dual]

Depends on / 依赖: not_isMax, not_isMax_iff, of_not_not
-/
theorem StrictMono.isMax_of_apply (hf : StrictMono f) (ha : IsMax (f a)) : IsMax a :=
  of_not_not fun h =>
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMax ha

@[to_dual]
/--
theorem `StrictAnti.isMax_of_apply` / 定理 `StrictAnti.isMax_of_apply`

English:
theorem StrictAnti.isMax_of_apply
  given: (hf : StrictAnti f) (ha : IsMin (f a))
  statement: IsMax a
  proof: of_not_not fun h =>
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMin ha

中文:
定理 严格递减.isMax_of_apply
  条件: (hf : 严格递减 f) (ha : IsMin (f a))
  结论: IsMax a
  证明: of_not_not fun h =>
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMin ha

Depends on / 依赖: not_isMax_iff, not_isMin, of_not_not
-/
theorem StrictAnti.isMax_of_apply (hf : StrictAnti f) (ha : IsMin (f a)) : IsMax a :=
  of_not_not fun h =>
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMin ha

/--
lemma `StrictMono.add_le_nat` / 引理 `StrictMono.add_le_nat`

English:
lemma StrictMono.add_le_nat
  given: {f : Nat -> Nat} (hf : StrictMono f) (m n : Nat)
  statement: m + f n <= f (m + n)
  proof: by
  rw [Nat.add_comm m]; rw [Nat.add_comm m]
  induction m with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ m ih =>
    rw [← Nat.add_assoc]; rw [← Nat.add_assoc]; rw [Nat.succ_le_iff]
    exact ih.trans_lt (hf (n + m).lt_succ_self)

中文:
引理 严格递增.add_le_nat
  条件: {f : 自然数 -> 自然数} (hf : 严格递增 f) (m n : 自然数)
  结论: m + f n <= f (m + n)
  证明: by
  rw [Nat.add_comm m]; rw [Nat.add_comm m]
  induction m with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ m ih =>
    rw [← Nat.add_assoc]; rw [← Nat.add_assoc]; rw [Nat.succ_le_iff]
    exact ih.trans_lt (hf (n + m).lt_succ_self)

Depends on / 依赖: Nat.add_assoc, Nat.add_comm, Nat.add_zero, Nat.succ_le_iff, add_assoc, add_comm, add_zero, ih.trans_lt, lt_succ_self, succ_le_iff, trans_lt
-/
lemma StrictMono.add_le_nat {f : Nat -> Nat} (hf : StrictMono f) (m n : Nat) : m + f n <= f (m + n) := by
  rw [Nat.add_comm m]; rw [Nat.add_comm m]
  induction m with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ m ih =>
    rw [← Nat.add_assoc]; rw [← Nat.add_assoc]; rw [Nat.succ_le_iff]
    exact ih.trans_lt (hf (n + m).lt_succ_self)

/--
theorem `StrictMono.ite'` / 定理 `StrictMono.ite'`

English:
theorem StrictMono.ite'
  statement: (hf : StrictMono f) (hg : StrictMono g) {p : α -> Prop}
  proof: by
  intro x y h
  by_cases hy : p y
  · have hx : p x := hp h hy
    simpa [hx, hy] using hf h
  by_cases hx : p x
  · simpa [hx, hy] using hfg hx hy h
  · simpa [hx, hy] using hg h

中文:
定理 严格递增.ite'
  结论: (hf : 严格递增 f) (hg : 严格递增 g) {p : α -> 命题}
  证明: by
  intro x y h
  by_cases hy : p y
  · have hx : p x := hp h hy
    simpa [hx, hy] using hf h
  by_cases hx : p x
  · simpa [hx, hy] using hfg hx hy h
  · simpa [hx, hy] using hg h
-/
protected theorem StrictMono.ite' (hf : StrictMono f) (hg : StrictMono g) {p : α -> Prop}
    [DecidablePred p]
    (hp : forall ⦃x y⦄, x < y -> p y -> p x) (hfg : forall ⦃x y⦄, p x -> ¬p y -> x < y -> f x < g y) :
    StrictMono fun x => if p x then f x else g x := by
  intro x y h
  by_cases hy : p y
  · have hx : p x := hp h hy
    simpa [hx, hy] using hf h
  by_cases hx : p x
  · simpa [hx, hy] using hfg hx hy h
  · simpa [hx, hy] using hg h

/--
theorem `StrictMono.ite` / 定理 `StrictMono.ite`

English:
theorem StrictMono.ite
  statement: (hf : StrictMono f) (hg : StrictMono g) {p : α -> Prop}
  proof: (hf.ite' hg hp) fun _ y _ _ h => (hf h).trans_le (hfg y)

中文:
定理 严格递增.ite
  结论: (hf : 严格递增 f) (hg : 严格递增 g) {p : α -> 命题}
  证明: (hf.ite' hg hp) fun _ y _ _ h => (hf h).trans_le (hfg y)
-/
protected theorem StrictMono.ite (hf : StrictMono f) (hg : StrictMono g) {p : α -> Prop}
    [DecidablePred p] (hp : forall ⦃x y⦄, x < y -> p y -> p x) (hfg : forall x, f x <= g x) :
    StrictMono fun x => if p x then f x else g x :=
  (hf.ite' hg hp) fun _ y _ _ h => (hf h).trans_le (hfg y)

/--
theorem `StrictAnti.ite'` / 定理 `StrictAnti.ite'`

English:
theorem StrictAnti.ite'
  statement: (hf : StrictAnti f) (hg : StrictAnti g) {p : α -> Prop}
  proof: StrictMono.ite' hf.dual_right hg.dual_right hp hfg

中文:
定理 严格递减.ite'
  结论: (hf : 严格递减 f) (hg : 严格递减 g) {p : α -> 命题}
  证明: StrictMono.ite' hf.dual_right hg.dual_right hp hfg
-/
protected theorem StrictAnti.ite' (hf : StrictAnti f) (hg : StrictAnti g) {p : α -> Prop}
    [DecidablePred p]
    (hp : forall ⦃x y⦄, x < y -> p y -> p x) (hfg : forall ⦃x y⦄, p x -> ¬p y -> x < y -> g y < f x) :
    StrictAnti fun x => if p x then f x else g x :=
  StrictMono.ite' hf.dual_right hg.dual_right hp hfg

/--
theorem `StrictAnti.ite` / 定理 `StrictAnti.ite`

English:
theorem StrictAnti.ite
  statement: (hf : StrictAnti f) (hg : StrictAnti g) {p : α -> Prop}
  proof: (hf.ite' hg hp) fun _ y _ _ h => (hfg y).trans_lt (hf h)

中文:
定理 严格递减.ite
  结论: (hf : 严格递减 f) (hg : 严格递减 g) {p : α -> 命题}
  证明: (hf.ite' hg hp) fun _ y _ _ h => (hfg y).trans_lt (hf h)
-/
protected theorem StrictAnti.ite (hf : StrictAnti f) (hg : StrictAnti g) {p : α -> Prop}
    [DecidablePred p] (hp : forall ⦃x y⦄, x < y -> p y -> p x) (hfg : forall x, g x <= f x) :
    StrictAnti fun x => if p x then f x else g x :=
  (hf.ite' hg hp) fun _ y _ _ h => (hfg y).trans_lt (hf h)

end Preorder

namespace List

section Fold

/--
theorem `foldl_monotone` / 定理 `foldl_monotone`

English:
theorem foldl_monotone
  statement: [Preorder α] {f : α -> β -> α} (H : forall b, Monotone fun a => f a b)
  proof: List.recOn l (fun _ _ => id) fun _ _ hl _ _ h => hl (H _ h)

中文:
定理 foldl_monotone
  结论: [预序 α] {f : α -> β -> α} (H : 对任意 b, 递增 fun a => f a b)
  证明: List.recOn l (fun _ _ => id) fun _ _ hl _ _ h => hl (H _ h)

Depends on / 依赖: List.recOn
-/
theorem foldl_monotone [Preorder α] {f : α -> β -> α} (H : forall b, Monotone fun a => f a b)
    (l : List β) : Monotone fun a => l.foldl f a :=
  List.recOn l (fun _ _ => id) fun _ _ hl _ _ h => hl (H _ h)

/--
theorem `foldr_monotone` / 定理 `foldr_monotone`

English:
theorem foldr_monotone
  given: [Preorder β] {f : α -> β -> β} (H : forall a, Monotone (f a)) (l : List α)
  proof: fun _ _ h => List.recOn l h fun i _ hl => H i hl

中文:
定理 foldr_monotone
  条件: [预序 β] {f : α -> β -> β} (H : 对任意 a, 递增 (f a)) (l : 列表 α)
  证明: fun _ _ h => List.recOn l h fun i _ hl => H i hl

Depends on / 依赖: List.recOn
-/
theorem foldr_monotone [Preorder β] {f : α -> β -> β} (H : forall a, Monotone (f a)) (l : List α) :
    Monotone fun b => l.foldr f b := fun _ _ h => List.recOn l h fun i _ hl => H i hl

/--
theorem `foldl_strictMono` / 定理 `foldl_strictMono`

English:
theorem foldl_strictMono
  statement: [Preorder α] {f : α -> β -> α} (H : forall b, StrictMono fun a => f a b)
  proof: List.recOn l (fun _ _ => id) fun _ _ hl _ _ h => hl (H _ h)

中文:
定理 foldl_strictMono
  结论: [预序 α] {f : α -> β -> α} (H : 对任意 b, 严格递增 fun a => f a b)
  证明: List.recOn l (fun _ _ => id) fun _ _ hl _ _ h => hl (H _ h)

Depends on / 依赖: List.recOn
-/
theorem foldl_strictMono [Preorder α] {f : α -> β -> α} (H : forall b, StrictMono fun a => f a b)
    (l : List β) : StrictMono fun a => l.foldl f a :=
  List.recOn l (fun _ _ => id) fun _ _ hl _ _ h => hl (H _ h)

/--
theorem `foldr_strictMono` / 定理 `foldr_strictMono`

English:
theorem foldr_strictMono
  given: [Preorder β] {f : α -> β -> β} (H : forall a, StrictMono (f a)) (l : List α)
  proof: fun _ _ h => List.recOn l h fun i _ hl => H i hl

中文:
定理 foldr_strictMono
  条件: [预序 β] {f : α -> β -> β} (H : 对任意 a, 严格递增 (f a)) (l : 列表 α)
  证明: fun _ _ h => List.recOn l h fun i _ hl => H i hl

Depends on / 依赖: List.recOn
-/
theorem foldr_strictMono [Preorder β] {f : α -> β -> β} (H : forall a, StrictMono (f a)) (l : List α) :
    StrictMono fun b => l.foldr f b := fun _ _ h => List.recOn l h fun i _ hl => H i hl

end Fold

end List

/-! ### Monotonicity in linear orders -/


section LinearOrder

variable [LinearOrder α]

section Preorder

variable [Preorder β] {f : α -> β} {s : Set α}

open Ordering

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `StrictMonoOn.le_iff_le` / 定理 `StrictMonoOn.le_iff_le`

English:
theorem StrictMonoOn.le_iff_le
  given: (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb : b in s)
  proof: ⟨fun h => le_of_not_gt fun h' => (hf hb ha h').not_ge h, fun h =>
    h.lt_or_eq_dec.elim (fun h' => (hf ha hb h').le) fun h' => h' ▸ le_rfl⟩

@[to_dual self (reorder := a b, ha hb)]

中文:
定理 StrictMonoOn.le_iff_le
  条件: (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb : b in s)
  证明: ⟨fun h => le_of_not_gt fun h' => (hf hb ha h').not_ge h, fun h =>
    h.lt_or_eq_dec.elim (fun h' => (hf ha hb h').le) fun h' => h' ▸ le_rfl⟩

@[to_dual self (reorder := a b, ha hb)]

Depends on / 依赖: h.lt_or_eq_dec.elim, le_of_not_gt, le_rfl, lt_or_eq_dec, not_ge
-/
theorem StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb : b in s) :
    f a <= f b ↔ a <= b :=
  ⟨fun h => le_of_not_gt fun h' => (hf hb ha h').not_ge h, fun h =>
    h.lt_or_eq_dec.elim (fun h' => (hf ha hb h').le) fun h' => h' ▸ le_rfl⟩

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `StrictAntiOn.le_iff_ge` / 定理 `StrictAntiOn.le_iff_ge`

English:
theorem StrictAntiOn.le_iff_ge
  given: (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb : b in s)
  proof: hf.dual_right.le_iff_le hb ha

中文:
定理 StrictAntiOn.le_iff_ge
  条件: (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb : b in s)
  证明: hf.dual_right.le_iff_le hb ha

Depends on / 依赖: dual_right, hf.dual_right.le_iff_le, le_iff_le
-/
theorem StrictAntiOn.le_iff_ge (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb : b in s) :
    f a <= f b ↔ b <= a :=
  hf.dual_right.le_iff_le hb ha

/--
theorem `StrictMonoOn.eq_iff_eq` / 定理 `StrictMonoOn.eq_iff_eq`

English:
theorem StrictMonoOn.eq_iff_eq
  given: (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb : b in s)
  proof: ⟨fun h => le_antisymm ((hf.le_iff_le ha hb).mp h.le) ((hf.le_iff_le hb ha).mp h.ge), by
    rintro rfl
    rfl⟩

中文:
定理 StrictMonoOn.eq_iff_eq
  条件: (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb : b in s)
  证明: ⟨fun h => le_antisymm ((hf.le_iff_le ha hb).mp h.le) ((hf.le_iff_le hb ha).mp h.ge), by
    rintro rfl
    rfl⟩

Depends on / 依赖: h.ge, h.le, hf.le_iff_le, le_antisymm, le_iff_le
-/
theorem StrictMonoOn.eq_iff_eq (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb : b in s) :
    f a = f b ↔ a = b :=
  ⟨fun h => le_antisymm ((hf.le_iff_le ha hb).mp h.le) ((hf.le_iff_le hb ha).mp h.ge), by
    rintro rfl
    rfl⟩

/--
theorem `StrictAntiOn.eq_iff_eq` / 定理 `StrictAntiOn.eq_iff_eq`

English:
theorem StrictAntiOn.eq_iff_eq
  given: (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb : b in s)
  proof: (hf.dual_right.eq_iff_eq ha hb).trans eq_comm

@[to_dual self (reorder := a b, ha hb)]

中文:
定理 StrictAntiOn.eq_iff_eq
  条件: (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb : b in s)
  证明: (hf.dual_right.eq_iff_eq ha hb).trans eq_comm

@[to_dual self (reorder := a b, ha hb)]

Depends on / 依赖: dual_right, eq_comm, eq_iff_eq, hf.dual_right.eq_iff_eq
-/
theorem StrictAntiOn.eq_iff_eq (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb : b in s) :
    f a = f b ↔ b = a :=
  (hf.dual_right.eq_iff_eq ha hb).trans eq_comm

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `StrictMonoOn.lt_iff_lt` / 定理 `StrictMonoOn.lt_iff_lt`

English:
theorem StrictMonoOn.lt_iff_lt
  given: (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb : b in s)
  proof: by
  rw [lt_iff_le_not_ge]; rw [lt_iff_le_not_ge]; rw [hf.le_iff_le ha hb]; rw [hf.le_iff_le hb ha]

@[to_dual self (reorder := a b, ha hb)]

中文:
定理 StrictMonoOn.lt_iff_lt
  条件: (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb : b in s)
  证明: by
  rw [lt_iff_le_not_ge]; rw [lt_iff_le_not_ge]; rw [hf.le_iff_le ha hb]; rw [hf.le_iff_le hb ha]

@[to_dual self (reorder := a b, ha hb)]

Depends on / 依赖: hf.le_iff_le, le_iff_le, lt_iff_le_not_ge
-/
theorem StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb : b in s) :
    f a < f b ↔ a < b := by
  rw [lt_iff_le_not_ge]; rw [lt_iff_le_not_ge]; rw [hf.le_iff_le ha hb]; rw [hf.le_iff_le hb ha]

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `StrictAntiOn.lt_iff_gt` / 定理 `StrictAntiOn.lt_iff_gt`

English:
theorem StrictAntiOn.lt_iff_gt
  given: (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb : b in s)
  proof: hf.dual_right.lt_iff_lt hb ha

@[to_dual self]

中文:
定理 StrictAntiOn.lt_iff_gt
  条件: (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb : b in s)
  证明: hf.dual_right.lt_iff_lt hb ha

@[to_dual self]

Depends on / 依赖: dual_right, hf.dual_right.lt_iff_lt, lt_iff_lt
-/
theorem StrictAntiOn.lt_iff_gt (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb : b in s) :
    f a < f b ↔ b < a :=
  hf.dual_right.lt_iff_lt hb ha

@[to_dual self]
/--
theorem `StrictMono.le_iff_le` / 定理 `StrictMono.le_iff_le`

English:
theorem StrictMono.le_iff_le
  given: (hf : StrictMono f) {a b : α}
  statement: f a <= f b ↔ a <= b
  proof: (hf.strictMonoOn Set.univ).le_iff_le trivial trivial

@[to_dual self]

中文:
定理 严格递增.le_iff_le
  条件: (hf : 严格递增 f) {a b : α}
  结论: f a <= f b ↔ a <= b
  证明: (hf.strictMonoOn Set.univ).le_iff_le trivial trivial

@[to_dual self]

Depends on / 依赖: Set.univ, hf.strictMonoOn, le_iff_le, strictMonoOn
-/
theorem StrictMono.le_iff_le (hf : StrictMono f) {a b : α} : f a <= f b ↔ a <= b :=
  (hf.strictMonoOn Set.univ).le_iff_le trivial trivial

@[to_dual self]
/--
theorem `StrictAnti.le_iff_ge` / 定理 `StrictAnti.le_iff_ge`

English:
theorem StrictAnti.le_iff_ge
  given: (hf : StrictAnti f) {a b : α}
  statement: f a <= f b ↔ b <= a
  proof: (hf.strictAntiOn Set.univ).le_iff_ge trivial trivial

@[to_dual self]

中文:
定理 严格递减.le_iff_ge
  条件: (hf : 严格递减 f) {a b : α}
  结论: f a <= f b ↔ b <= a
  证明: (hf.strictAntiOn Set.univ).le_iff_ge trivial trivial

@[to_dual self]

Depends on / 依赖: Set.univ, hf.strictAntiOn, le_iff_ge, strictAntiOn
-/
theorem StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α} : f a <= f b ↔ b <= a :=
  (hf.strictAntiOn Set.univ).le_iff_ge trivial trivial

@[to_dual self]
/--
theorem `StrictMono.lt_iff_lt` / 定理 `StrictMono.lt_iff_lt`

English:
theorem StrictMono.lt_iff_lt
  given: (hf : StrictMono f) {a b : α}
  statement: f a < f b ↔ a < b
  proof: (hf.strictMonoOn Set.univ).lt_iff_lt trivial trivial

@[to_dual self]

中文:
定理 严格递增.lt_iff_lt
  条件: (hf : 严格递增 f) {a b : α}
  结论: f a < f b ↔ a < b
  证明: (hf.strictMonoOn Set.univ).lt_iff_lt trivial trivial

@[to_dual self]

Depends on / 依赖: Set.univ, hf.strictMonoOn, lt_iff_lt, strictMonoOn
-/
theorem StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α} : f a < f b ↔ a < b :=
  (hf.strictMonoOn Set.univ).lt_iff_lt trivial trivial

@[to_dual self]
/--
theorem `StrictAnti.lt_iff_gt` / 定理 `StrictAnti.lt_iff_gt`

English:
theorem StrictAnti.lt_iff_gt
  given: (hf : StrictAnti f) {a b : α}
  statement: f a < f b ↔ b < a
  proof: (hf.strictAntiOn Set.univ).lt_iff_gt trivial trivial

中文:
定理 严格递减.lt_iff_gt
  条件: (hf : 严格递减 f) {a b : α}
  结论: f a < f b ↔ b < a
  证明: (hf.strictAntiOn Set.univ).lt_iff_gt trivial trivial

Depends on / 依赖: Set.univ, hf.strictAntiOn, lt_iff_gt, strictAntiOn
-/
theorem StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α} : f a < f b ↔ b < a :=
  (hf.strictAntiOn Set.univ).lt_iff_gt trivial trivial

/--
theorem `StrictMonoOn.compares` / 定理 `StrictMonoOn.compares`

English:
theorem StrictMonoOn.compares
  statement: (hf : StrictMonoOn f s) {a b : α} (ha : a in s)

中文:
定理 StrictMonoOn.compares
  结论: (hf : StrictMonoOn f s) {a b : α} (ha : a in s)
-/
protected theorem StrictMonoOn.compares (hf : StrictMonoOn f s) {a b : α} (ha : a in s)
    (hb : b in s) : forall {o : Ordering}, o.Compares (f a) (f b) ↔ o.Compares a b
  | Ordering.lt => hf.lt_iff_lt ha hb
  | Ordering.eq => ⟨fun h => ((hf.le_iff_le ha hb).1 h.le).antisymm
                      ((hf.le_iff_le hb ha).1 h.symm.le), congr_arg _⟩
  | Ordering.gt => hf.lt_iff_lt hb ha

/--
theorem `StrictAntiOn.compares` / 定理 `StrictAntiOn.compares`

English:
theorem StrictAntiOn.compares
  statement: (hf : StrictAntiOn f s) {a b : α} (ha : a in s)
  proof: toDual_compares_toDual.trans hf.dual_right.compares hb ha

中文:
定理 StrictAntiOn.compares
  结论: (hf : StrictAntiOn f s) {a b : α} (ha : a in s)
  证明: toDual_compares_toDual.trans hf.dual_right.compares hb ha
-/
protected theorem StrictAntiOn.compares (hf : StrictAntiOn f s) {a b : α} (ha : a in s)
    (hb : b in s) {o : Ordering} : o.Compares (f a) (f b) ↔ o.Compares b a :=
toDual_compares_toDual.trans hf.dual_right.compares hb ha

/--
theorem `StrictMono.compares` / 定理 `StrictMono.compares`

English:
theorem StrictMono.compares
  given: (hf : StrictMono f) {a b : α} {o : Ordering}
  proof: (hf.strictMonoOn Set.univ).compares trivial trivial

中文:
定理 严格递增.compares
  条件: (hf : 严格递增 f) {a b : α} {o : Ordering}
  证明: (hf.strictMonoOn Set.univ).compares trivial trivial
-/
protected theorem StrictMono.compares (hf : StrictMono f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares a b :=
  (hf.strictMonoOn Set.univ).compares trivial trivial

/--
theorem `StrictAnti.compares` / 定理 `StrictAnti.compares`

English:
theorem StrictAnti.compares
  given: (hf : StrictAnti f) {a b : α} {o : Ordering}
  proof: (hf.strictAntiOn Set.univ).compares trivial trivial

中文:
定理 严格递减.compares
  条件: (hf : 严格递减 f) {a b : α} {o : Ordering}
  证明: (hf.strictAntiOn Set.univ).compares trivial trivial
-/
protected theorem StrictAnti.compares (hf : StrictAnti f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares b a :=
  (hf.strictAntiOn Set.univ).compares trivial trivial

/--
theorem `StrictMono.injective` / 定理 `StrictMono.injective`

English:
theorem StrictMono.injective
  given: (hf : StrictMono f)
  statement: Injective f
  proof: fun x y h => show Compares eq x y from hf.compares.1 h

中文:
定理 严格递增.injective
  条件: (hf : 严格递增 f)
  结论: 单射 f
  证明: fun x y h => show Compares eq x y from hf.compares.1 h

Depends on / 依赖: Compares, compares, hf.compares
-/
theorem StrictMono.injective (hf : StrictMono f) : Injective f :=
  fun x y h => show Compares eq x y from hf.compares.1 h

/--
theorem `StrictAnti.injective` / 定理 `StrictAnti.injective`

English:
theorem StrictAnti.injective
  given: (hf : StrictAnti f)
  statement: Injective f
  proof: fun x y h => show Compares eq x y from hf.compares.1 h.symm

中文:
定理 严格递减.injective
  条件: (hf : 严格递减 f)
  结论: 单射 f
  证明: fun x y h => show Compares eq x y from hf.compares.1 h.symm

Depends on / 依赖: CommRing, Compares, I.IsTwoSided, IsTwoSided, compares, h.symm, hf.compares, quotientAlgebra
-/
theorem StrictAnti.injective (hf : StrictAnti f) : Injective f :=
  fun x y h => show Compares eq x y from hf.compares.1 h.symm

/--
lemma `StrictMonoOn.injOn` / 引理 `StrictMonoOn.injOn`

English:
lemma StrictMonoOn.injOn
  given: (hf : StrictMonoOn f s)
  statement: s.InjOn f
  proof: fun x hx y hy hxy =>
  show Ordering.eq.Compares x y from (hf.compares hx hy).1 hxy

中文:
引理 StrictMonoOn.injOn
  条件: (hf : StrictMonoOn f s)
  结论: s.单射限制 f
  证明: fun x hx y hy hxy =>
  show Ordering.eq.Compares x y from (hf.compares hx hy).1 hxy
-/
lemma StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn f := fun x hx y hy hxy =>
  show Ordering.eq.Compares x y from (hf.compares hx hy).1 hxy

/--
lemma `StrictAntiOn.injOn` / 引理 `StrictAntiOn.injOn`

English:
lemma StrictAntiOn.injOn
  given: (hf : StrictAntiOn f s)
  statement: s.InjOn f
  proof: hf.dual_left.injOn

@[to_dual]

中文:
引理 StrictAntiOn.injOn
  条件: (hf : StrictAntiOn f s)
  结论: s.单射限制 f
  证明: hf.dual_left.injOn

@[to_dual]

Depends on / 依赖: dual_left, hf.dual_left.injOn
-/
lemma StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn f := hf.dual_left.injOn

@[to_dual]
/--
theorem `StrictMono.maximal_of_maximal_image` / 定理 `StrictMono.maximal_of_maximal_image`

English:
theorem StrictMono.maximal_of_maximal_image
  given: (hf : StrictMono f) {a} (hmax : forall p, p <= f a) (x : α)
  proof: hf.le_iff_le.mp (hmax (f x))

@[to_dual]

中文:
定理 严格递增.maximal_of_maximal_image
  条件: (hf : 严格递增 f) {a} (hmax : 对任意 p, p <= f a) (x : α)
  证明: hf.le_iff_le.mp (hmax (f x))

@[to_dual]

Depends on / 依赖: hf.le_iff_le.mp, le_iff_le
-/
theorem StrictMono.maximal_of_maximal_image (hf : StrictMono f) {a} (hmax : forall p, p <= f a) (x : α) :
    x <= a :=
  hf.le_iff_le.mp (hmax (f x))

@[to_dual]
/--
theorem `StrictAnti.minimal_of_maximal_image` / 定理 `StrictAnti.minimal_of_maximal_image`

English:
theorem StrictAnti.minimal_of_maximal_image
  given: (hf : StrictAnti f) {a} (hmax : forall p, p <= f a) (x : α)
  proof: hf.le_iff_ge.mp (hmax (f x))

中文:
定理 严格递减.minimal_of_maximal_image
  条件: (hf : 严格递减 f) {a} (hmax : 对任意 p, p <= f a) (x : α)
  证明: hf.le_iff_ge.mp (hmax (f x))

Depends on / 依赖: hf.le_iff_ge.mp, le_iff_ge
-/
theorem StrictAnti.minimal_of_maximal_image (hf : StrictAnti f) {a} (hmax : forall p, p <= f a) (x : α) :
    a <= x :=
  hf.le_iff_ge.mp (hmax (f x))

end Preorder

section PartialOrder

variable [PartialOrder β] {f : α -> β} {s : Set α}

/--
theorem `Monotone.strictMono_iff_injective` / 定理 `Monotone.strictMono_iff_injective`

English:
theorem Monotone.strictMono_iff_injective
  given: (hf : Monotone f)
  statement: StrictMono f ↔ Injective f
  proof: ⟨fun h => h.injective, hf.strictMono_of_injective⟩

中文:
定理 递增.strictMono_iff_injective
  条件: (hf : 递增 f)
  结论: 严格递增 f ↔ 单射 f
  证明: ⟨fun h => h.injective, hf.strictMono_of_injective⟩

Depends on / 依赖: h.injective, hf.strictMono_of_injective, injective, strictMono_of_injective
-/
theorem Monotone.strictMono_iff_injective (hf : Monotone f) : StrictMono f ↔ Injective f :=
  ⟨fun h => h.injective, hf.strictMono_of_injective⟩

/--
theorem `Antitone.strictAnti_iff_injective` / 定理 `Antitone.strictAnti_iff_injective`

English:
theorem Antitone.strictAnti_iff_injective
  given: (hf : Antitone f)
  statement: StrictAnti f ↔ Injective f
  proof: ⟨fun h => h.injective, hf.strictAnti_of_injective⟩

中文:
定理 递减.strictAnti_iff_injective
  条件: (hf : 递减 f)
  结论: 严格递减 f ↔ 单射 f
  证明: ⟨fun h => h.injective, hf.strictAnti_of_injective⟩

Depends on / 依赖: h.injective, hf.strictAnti_of_injective, injective, strictAnti_of_injective
-/
theorem Antitone.strictAnti_iff_injective (hf : Antitone f) : StrictAnti f ↔ Injective f :=
  ⟨fun h => h.injective, hf.strictAnti_of_injective⟩

/--
theorem `MonotoneOn.strictMonoOn_iff_injOn` / 定理 `MonotoneOn.strictMonoOn_iff_injOn`

English:
theorem MonotoneOn.strictMonoOn_iff_injOn
  given: (hf : MonotoneOn f s)
  statement: StrictMonoOn f s ↔ s.InjOn f
  proof: ⟨StrictMonoOn.injOn, hf.strictMonoOn_of_injOn⟩

中文:
定理 MonotoneOn.strictMonoOn_iff_injOn
  条件: (hf : MonotoneOn f s)
  结论: StrictMonoOn f s ↔ s.单射限制 f
  证明: ⟨StrictMonoOn.injOn, hf.strictMonoOn_of_injOn⟩

Depends on / 依赖: StrictMonoOn, StrictMonoOn.injOn, hf.strictMonoOn_of_injOn, strictMonoOn_of_injOn
-/
theorem MonotoneOn.strictMonoOn_iff_injOn (hf : MonotoneOn f s) : StrictMonoOn f s ↔ s.InjOn f :=
  ⟨StrictMonoOn.injOn, hf.strictMonoOn_of_injOn⟩

/--
theorem `AntitoneOn.strictAnti_iff_injOn` / 定理 `AntitoneOn.strictAnti_iff_injOn`

English:
theorem AntitoneOn.strictAnti_iff_injOn
  given: (hf : AntitoneOn f s)
  statement: StrictAntiOn f s ↔ s.InjOn f
  proof: ⟨StrictAntiOn.injOn, hf.strictAntiOn_of_injOn⟩

中文:
定理 AntitoneOn.strictAnti_iff_injOn
  条件: (hf : AntitoneOn f s)
  结论: StrictAntiOn f s ↔ s.单射限制 f
  证明: ⟨StrictAntiOn.injOn, hf.strictAntiOn_of_injOn⟩

Depends on / 依赖: StrictAntiOn, StrictAntiOn.injOn, hf.strictAntiOn_of_injOn, strictAntiOn_of_injOn
-/
theorem AntitoneOn.strictAnti_iff_injOn (hf : AntitoneOn f s) : StrictAntiOn f s ↔ s.InjOn f :=
  ⟨StrictAntiOn.injOn, hf.strictAntiOn_of_injOn⟩

/--
theorem `Monotone.eq_of_ge_of_le` / 定理 `Monotone.eq_of_ge_of_le`

English:
theorem Monotone.eq_of_ge_of_le
  statement: {a₁ a₂ : α} (h_mon : Monotone f) (h_fa : f a₁ = f a₂) {i : α}
  proof: by
  apply le_antisymm
  · rw [h_fa]; exact h_mon h₂
  · exact h_mon h₁

中文:
定理 递增.eq_of_ge_of_le
  结论: {a₁ a₂ : α} (h_mon : 递增 f) (h_fa : f a₁ = f a₂) {i : α}
  证明: by
  apply le_antisymm
  · rw [h_fa]; exact h_mon h₂
  · exact h_mon h₁

Depends on / 依赖: h_fa, h_mon, le_antisymm
-/
theorem Monotone.eq_of_ge_of_le {a₁ a₂ : α} (h_mon : Monotone f) (h_fa : f a₁ = f a₂) {i : α}
    (h₁ : a₁ <= i) (h₂ : i <= a₂) : f i = f a₁ := by
  apply le_antisymm
  · rw [h_fa]; exact h_mon h₂
  · exact h_mon h₁

/--
theorem `Antitone.eq_of_ge_of_le` / 定理 `Antitone.eq_of_ge_of_le`

English:
theorem Antitone.eq_of_ge_of_le
  statement: {a₁ a₂ : α} (h_anti : Antitone f) (h_fa : f a₁ = f a₂) {i : α}
  proof: by
  apply le_antisymm
  · exact h_anti h₁
  · rw [h_fa]; exact h_anti h₂

中文:
定理 递减.eq_of_ge_of_le
  结论: {a₁ a₂ : α} (h_anti : 递减 f) (h_fa : f a₁ = f a₂) {i : α}
  证明: by
  apply le_antisymm
  · exact h_anti h₁
  · rw [h_fa]; exact h_anti h₂

Depends on / 依赖: h_anti, h_fa, le_antisymm
-/
theorem Antitone.eq_of_ge_of_le {a₁ a₂ : α} (h_anti : Antitone f) (h_fa : f a₁ = f a₂) {i : α}
    (h₁ : a₁ <= i) (h₂ : i <= a₂) : f i = f a₁ := by
  apply le_antisymm
  · exact h_anti h₁
  · rw [h_fa]; exact h_anti h₂

end PartialOrder

variable [LinearOrder β] {f : α -> β} {s : Set α} {x y : α}

/--
lemma `not_monotone_not_antitone_iff_exists_le_le` / 引理 `not_monotone_not_antitone_iff_exists_le_le`

English:
lemma not_monotone_not_antitone_iff_exists_le_le
  proof: by
  simp only [Monotone, Antitone]
  grind [not_le]

中文:
引理 not_monotone_not_antitone_iff_存在_le_le
  证明: by
  simp only [Monotone, Antitone]
  grind [not_le]

Depends on / 依赖: Antitone, Monotone, not_le
-/
lemma not_monotone_not_antitone_iff_exists_le_le :
    ¬ Monotone f ∧ ¬ Antitone f ↔
      exists a b c, a <= b ∧ b <= c ∧ ((f a < f b ∧ f c < f b) ∨ (f b < f a ∧ f b < f c)) := by
  simp only [Monotone, Antitone]
  grind [not_le]

/--
lemma `not_monotone_not_antitone_iff_exists_lt_lt` / 引理 `not_monotone_not_antitone_iff_exists_lt_lt`

English:
lemma not_monotone_not_antitone_iff_exists_lt_lt
  proof: by
  simp_rw [not_monotone_not_antitone_iff_exists_le_le, ← and_assoc]
  refine exists₃_congr (fun a b c => and_congr_left <|
fun h => (Ne.le_iff_lt ?_).and Ne.le_iff_lt ?_) <;>
  (rintro rfl; simp at h)

中文:
引理 not_monotone_not_antitone_iff_存在_lt_lt
  证明: by
  simp_rw [not_monotone_not_antitone_iff_exists_le_le, ← and_assoc]
  refine exists₃_congr (fun a b c => and_congr_left <|
fun h => (Ne.le_iff_lt ?_).and Ne.le_iff_lt ?_) <;>
  (rintro rfl; simp at h)

Depends on / 依赖: Ne.le_iff_lt, and_assoc, and_congr_left, le_iff_lt, not_monotone_not_antitone_iff_exists_le_le, simp_rw
-/
lemma not_monotone_not_antitone_iff_exists_lt_lt :
    ¬ Monotone f ∧ ¬ Antitone f ↔ exists a b c, a < b ∧ b < c ∧
    (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp_rw [not_monotone_not_antitone_iff_exists_le_le, ← and_assoc]
  refine exists₃_congr (fun a b c => and_congr_left <|
fun h => (Ne.le_iff_lt ?_).and Ne.le_iff_lt ?_) <;>
  (rintro rfl; simp at h)



/--
theorem `StrictMonoOn.cmp_map_eq` / 定理 `StrictMonoOn.cmp_map_eq`

English:
theorem StrictMonoOn.cmp_map_eq
  given: (hf : StrictMonoOn f s) (hx : x in s) (hy : y in s)
  proof: ((hf.compares hx hy).2 (cmp_compares x y)).cmp_eq

中文:
定理 StrictMonoOn.cmp_map_eq
  条件: (hf : StrictMonoOn f s) (hx : x in s) (hy : y in s)
  证明: ((hf.compares hx hy).2 (cmp_compares x y)).cmp_eq

Depends on / 依赖: cmp_compares, cmp_eq, compares, hf.compares
-/
theorem StrictMonoOn.cmp_map_eq (hf : StrictMonoOn f s) (hx : x in s) (hy : y in s) :
    cmp (f x) (f y) = cmp x y :=
  ((hf.compares hx hy).2 (cmp_compares x y)).cmp_eq

/--
theorem `StrictMono.cmp_map_eq` / 定理 `StrictMono.cmp_map_eq`

English:
theorem StrictMono.cmp_map_eq
  given: (hf : StrictMono f) (x y : α)
  statement: cmp (f x) (f y) = cmp x y
  proof: (hf.strictMonoOn Set.univ).cmp_map_eq trivial trivial

中文:
定理 严格递增.cmp_map_eq
  条件: (hf : 严格递增 f) (x y : α)
  结论: cmp (f x) (f y) = cmp x y
  证明: (hf.strictMonoOn Set.univ).cmp_map_eq trivial trivial

Depends on / 依赖: Set.univ, cmp_map_eq, hf.strictMonoOn, strictMonoOn
-/
theorem StrictMono.cmp_map_eq (hf : StrictMono f) (x y : α) : cmp (f x) (f y) = cmp x y :=
  (hf.strictMonoOn Set.univ).cmp_map_eq trivial trivial

/--
theorem `StrictAntiOn.cmp_map_eq` / 定理 `StrictAntiOn.cmp_map_eq`

English:
theorem StrictAntiOn.cmp_map_eq
  given: (hf : StrictAntiOn f s) (hx : x in s) (hy : y in s)
  proof: hf.dual_right.cmp_map_eq hy hx

中文:
定理 StrictAntiOn.cmp_map_eq
  条件: (hf : StrictAntiOn f s) (hx : x in s) (hy : y in s)
  证明: hf.dual_right.cmp_map_eq hy hx

Depends on / 依赖: cmp_map_eq, dual_right, hf.dual_right.cmp_map_eq
-/
theorem StrictAntiOn.cmp_map_eq (hf : StrictAntiOn f s) (hx : x in s) (hy : y in s) :
    cmp (f x) (f y) = cmp y x :=
  hf.dual_right.cmp_map_eq hy hx

/--
theorem `StrictAnti.cmp_map_eq` / 定理 `StrictAnti.cmp_map_eq`

English:
theorem StrictAnti.cmp_map_eq
  given: (hf : StrictAnti f) (x y : α)
  statement: cmp (f x) (f y) = cmp y x
  proof: (hf.strictAntiOn Set.univ).cmp_map_eq trivial trivial

中文:
定理 严格递减.cmp_map_eq
  条件: (hf : 严格递减 f) (x y : α)
  结论: cmp (f x) (f y) = cmp y x
  证明: (hf.strictAntiOn Set.univ).cmp_map_eq trivial trivial

Depends on / 依赖: Set.univ, cmp_map_eq, hf.strictAntiOn, strictAntiOn
-/
theorem StrictAnti.cmp_map_eq (hf : StrictAnti f) (x y : α) : cmp (f x) (f y) = cmp y x :=
  (hf.strictAntiOn Set.univ).cmp_map_eq trivial trivial

end LinearOrder

/-! ### Monotonicity in `ℕ` and `ℤ` -/


section Preorder

variable [Preorder α]

/--
theorem `Nat.rel_of_forall_rel_succ_of_le_of_lt` / 定理 `Nat.rel_of_forall_rel_succ_of_le_of_lt`

English:
theorem Nat.rel_of_forall_rel_succ_of_le_of_lt
  statement: (r : β -> β -> Prop) [IsTrans β r] {f : Nat -> β} {a : Nat}
  proof: by
  induction hbc with
  | refl => exact h _ hab
  | step b_lt_k r_b_k => exact _root_.trans r_b_k (h _ (hab.trans_lt b_lt_k).le)

中文:
定理 自然数.rel_of_对任意_rel_succ_of_le_of_lt
  结论: (r : β -> β -> 命题) [是Trans β r] {f : 自然数 -> β} {a : 自然数}
  证明: by
  induction hbc with
  | refl => exact h _ hab
  | step b_lt_k r_b_k => exact _root_.trans r_b_k (h _ (hab.trans_lt b_lt_k).le)

Depends on / 依赖: _root_, _root_.trans, b_lt_k, hab.trans_lt, r_b_k, trans_lt
-/
theorem Nat.rel_of_forall_rel_succ_of_le_of_lt (r : β -> β -> Prop) [IsTrans β r] {f : Nat -> β} {a : Nat}
    (h : forall n, a <= n -> r (f n) (f (n + 1))) ⦃b c : Nat⦄ (hab : a <= b) (hbc : b < c) :
    r (f b) (f c) := by
  induction hbc with
  | refl => exact h _ hab
  | step b_lt_k r_b_k => exact _root_.trans r_b_k (h _ (hab.trans_lt b_lt_k).le)

/--
theorem `Nat.rel_of_forall_rel_succ_of_le_of_le` / 定理 `Nat.rel_of_forall_rel_succ_of_le_of_le`

English:
theorem Nat.rel_of_forall_rel_succ_of_le_of_le
  statement: (r : β -> β -> Prop) [Std.Refl r] [IsTrans β r]
  proof: hbc.eq_or_lt.elim (fun h => h ▸ refl _) (Nat.rel_of_forall_rel_succ_of_le_of_lt r h hab)

中文:
定理 自然数.rel_of_对任意_rel_succ_of_le_of_le
  结论: (r : β -> β -> 命题) [Std.Refl r] [是Trans β r]
  证明: hbc.eq_or_lt.elim (fun h => h ▸ refl _) (Nat.rel_of_forall_rel_succ_of_le_of_lt r h hab)

Depends on / 依赖: Nat.rel_of_forall_rel_succ_of_le_of_lt, eq_or_lt, hbc.eq_or_lt.elim, rel_of_forall_rel_succ_of_le_of_lt
-/
theorem Nat.rel_of_forall_rel_succ_of_le_of_le (r : β -> β -> Prop) [Std.Refl r] [IsTrans β r]
    {f : Nat -> β} {a : Nat} (h : forall n, a <= n -> r (f n) (f (n + 1)))
    ⦃b c : Nat⦄ (hab : a <= b) (hbc : b <= c) : r (f b) (f c) :=
  hbc.eq_or_lt.elim (fun h => h ▸ refl _) (Nat.rel_of_forall_rel_succ_of_le_of_lt r h hab)

/--
theorem `Nat.rel_of_forall_rel_succ_of_lt` / 定理 `Nat.rel_of_forall_rel_succ_of_lt`

English:
theorem Nat.rel_of_forall_rel_succ_of_lt
  statement: (r : β -> β -> Prop) [IsTrans β r] {f : Nat -> β}
  proof: Nat.rel_of_forall_rel_succ_of_le_of_lt r (fun n _ => h n) le_rfl hab

中文:
定理 自然数.rel_of_对任意_rel_succ_of_lt
  结论: (r : β -> β -> 命题) [是Trans β r] {f : 自然数 -> β}
  证明: Nat.rel_of_forall_rel_succ_of_le_of_lt r (fun n _ => h n) le_rfl hab

Depends on / 依赖: Nat.rel_of_forall_rel_succ_of_le_of_lt, le_rfl, rel_of_forall_rel_succ_of_le_of_lt
-/
theorem Nat.rel_of_forall_rel_succ_of_lt (r : β -> β -> Prop) [IsTrans β r] {f : Nat -> β}
    (h : forall n, r (f n) (f (n + 1))) ⦃a b : Nat⦄ (hab : a < b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_lt r (fun n _ => h n) le_rfl hab

/--
theorem `Nat.rel_of_forall_rel_succ_of_le` / 定理 `Nat.rel_of_forall_rel_succ_of_le`

English:
theorem Nat.rel_of_forall_rel_succ_of_le
  statement: (r : β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Nat -> β}
  proof: Nat.rel_of_forall_rel_succ_of_le_of_le r (fun n _ => h n) le_rfl hab

中文:
定理 自然数.rel_of_对任意_rel_succ_of_le
  结论: (r : β -> β -> 命题) [Std.Refl r] [是Trans β r] {f : 自然数 -> β}
  证明: Nat.rel_of_forall_rel_succ_of_le_of_le r (fun n _ => h n) le_rfl hab

Depends on / 依赖: Nat.rel_of_forall_rel_succ_of_le_of_le, le_rfl, rel_of_forall_rel_succ_of_le_of_le
-/
theorem Nat.rel_of_forall_rel_succ_of_le (r : β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Nat -> β}
    (h : forall n, r (f n) (f (n + 1))) ⦃a b : Nat⦄ (hab : a <= b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_le r (fun n _ => h n) le_rfl hab

/--
theorem `monotone_nat_of_le_succ` / 定理 `monotone_nat_of_le_succ`

English:
theorem monotone_nat_of_le_succ
  given: {f : Nat -> α} (hf : forall n, f n <= f (n + 1))
  statement: Monotone f
  proof: Nat.rel_of_forall_rel_succ_of_le (· <= ·) hf

中文:
定理 monotone_nat_of_le_succ
  条件: {f : 自然数 -> α} (hf : 对任意 n, f n <= f (n + 1))
  结论: 递增 f
  证明: Nat.rel_of_forall_rel_succ_of_le (· <= ·) hf

Depends on / 依赖: Nat.rel_of_forall_rel_succ_of_le, rel_of_forall_rel_succ_of_le
-/
theorem monotone_nat_of_le_succ {f : Nat -> α} (hf : forall n, f n <= f (n + 1)) : Monotone f :=
  Nat.rel_of_forall_rel_succ_of_le (· <= ·) hf

/--
theorem `monotone_add_nat_of_le_succ` / 定理 `monotone_add_nat_of_le_succ`

English:
theorem monotone_add_nat_of_le_succ
  given: {f : Nat -> α} {k : Nat} (hf : forall n >= k, f n <= f (n + 1))
  proof: fun _ _ hle => Nat.rel_of_forall_rel_succ_of_le_of_le (· <= ·) hf
    (Nat.le_add_left k _) (Nat.add_le_add_iff_right.mpr hle)

中文:
定理 monotone_add_nat_of_le_succ
  条件: {f : 自然数 -> α} {k : 自然数} (hf : 对任意 n >= k, f n <= f (n + 1))
  证明: fun _ _ hle => Nat.rel_of_forall_rel_succ_of_le_of_le (· <= ·) hf
    (Nat.le_add_left k _) (Nat.add_le_add_iff_right.mpr hle)

Depends on / 依赖: Nat.add_le_add_iff_right.mpr, Nat.le_add_left, Nat.rel_of_forall_rel_succ_of_le_of_le, add_le_add_iff_right, le_add_left, rel_of_forall_rel_succ_of_le_of_le
-/
theorem monotone_add_nat_of_le_succ {f : Nat -> α} {k : Nat} (hf : forall n >= k, f n <= f (n + 1)) :
    Monotone (fun n => f (n + k)) :=
  fun _ _ hle => Nat.rel_of_forall_rel_succ_of_le_of_le (· <= ·) hf
    (Nat.le_add_left k _) (Nat.add_le_add_iff_right.mpr hle)

-- TODO replace `{ x | k ≤ x }` with `Set.Ici k`
/--
theorem `monotoneOn_nat_Ici_of_le_succ` / 定理 `monotoneOn_nat_Ici_of_le_succ`

English:
theorem monotoneOn_nat_Ici_of_le_succ
  given: {f : Nat -> α} {k : Nat} (hf : forall n >= k, f n <= f (n + 1))
  proof: fun _ hab _ _ hle => Nat.rel_of_forall_rel_succ_of_le_of_le (· <= ·) hf hab hle

中文:
定理 monotoneOn_nat_Ici_of_le_succ
  条件: {f : 自然数 -> α} {k : 自然数} (hf : 对任意 n >= k, f n <= f (n + 1))
  证明: fun _ hab _ _ hle => Nat.rel_of_forall_rel_succ_of_le_of_le (· <= ·) hf hab hle

Depends on / 依赖: Nat.rel_of_forall_rel_succ_of_le_of_le, rel_of_forall_rel_succ_of_le_of_le
-/
theorem monotoneOn_nat_Ici_of_le_succ {f : Nat -> α} {k : Nat} (hf : forall n >= k, f n <= f (n + 1)) :
    MonotoneOn f { x | k <= x } :=
  fun _ hab _ _ hle => Nat.rel_of_forall_rel_succ_of_le_of_le (· <= ·) hf hab hle

-- TODO replace `{ x | k ≤ x }` with `Set.Ici k`
/--
theorem `monotone_add_nat_iff_monotoneOn_nat_Ici` / 定理 `monotone_add_nat_iff_monotoneOn_nat_Ici`

English:
theorem monotone_add_nat_iff_monotoneOn_nat_Ici
  given: {f : Nat -> α} {k : Nat}
  proof: by
  refine ⟨fun h x hx y hy hle => ?_, fun h x y hle => ?_⟩
  · rw [← Nat.sub_add_cancel hx, ← Nat.sub_add_cancel hy]
    rw [← Nat.sub_le_sub_iff_right hy] at hle
    exact h hle
  · rw [← Nat.add_le_add_iff_right] at hle
    exact h (Nat.le_add_left k x) (Nat.le_add_left k y) hle

中文:
定理 monotone_add_nat_iff_monotoneOn_nat_Ici
  条件: {f : 自然数 -> α} {k : 自然数}
  证明: by
  refine ⟨fun h x hx y hy hle => ?_, fun h x y hle => ?_⟩
  · rw [← Nat.sub_add_cancel hx, ← Nat.sub_add_cancel hy]
    rw [← Nat.sub_le_sub_iff_right hy] at hle
    exact h hle
  · rw [← Nat.add_le_add_iff_right] at hle
    exact h (Nat.le_add_left k x) (Nat.le_add_left k y) hle

Depends on / 依赖: Nat.add_le_add_iff_right, Nat.le_add_left, Nat.sub_add_cancel, Nat.sub_le_sub_iff_right, add_le_add_iff_right, le_add_left, sub_add_cancel, sub_le_sub_iff_right
-/
theorem monotone_add_nat_iff_monotoneOn_nat_Ici {f : Nat -> α} {k : Nat} :
    Monotone (fun n => f (n + k)) ↔ MonotoneOn f { x | k <= x } := by
  refine ⟨fun h x hx y hy hle => ?_, fun h x y hle => ?_⟩
  · rw [← Nat.sub_add_cancel hx, ← Nat.sub_add_cancel hy]
    rw [← Nat.sub_le_sub_iff_right hy] at hle
    exact h hle
  · rw [← Nat.add_le_add_iff_right] at hle
    exact h (Nat.le_add_left k x) (Nat.le_add_left k y) hle

/--
theorem `antitone_nat_of_succ_le` / 定理 `antitone_nat_of_succ_le`

English:
theorem antitone_nat_of_succ_le
  given: {f : Nat -> α} (hf : forall n, f (n + 1) <= f n)
  statement: Antitone f
  proof: @monotone_nat_of_le_succ αᵒᵈ _ _ hf

中文:
定理 antitone_nat_of_succ_le
  条件: {f : 自然数 -> α} (hf : 对任意 n, f (n + 1) <= f n)
  结论: 递减 f
  证明: @monotone_nat_of_le_succ αᵒᵈ _ _ hf

Depends on / 依赖: monotone_nat_of_le_succ
-/
theorem antitone_nat_of_succ_le {f : Nat -> α} (hf : forall n, f (n + 1) <= f n) : Antitone f :=
  @monotone_nat_of_le_succ αᵒᵈ _ _ hf

/--
theorem `antitone_add_nat_of_succ_le` / 定理 `antitone_add_nat_of_succ_le`

English:
theorem antitone_add_nat_of_succ_le
  given: {f : Nat -> α} {k : Nat} (hf : forall n >= k, f (n + 1) <= f n)
  proof: @monotone_add_nat_of_le_succ αᵒᵈ _ f k hf

中文:
定理 antitone_add_nat_of_succ_le
  条件: {f : 自然数 -> α} {k : 自然数} (hf : 对任意 n >= k, f (n + 1) <= f n)
  证明: @monotone_add_nat_of_le_succ αᵒᵈ _ f k hf

Depends on / 依赖: monotone_add_nat_of_le_succ
-/
theorem antitone_add_nat_of_succ_le {f : Nat -> α} {k : Nat} (hf : forall n >= k, f (n + 1) <= f n) :
    Antitone (fun n => f (n + k)) :=
  @monotone_add_nat_of_le_succ αᵒᵈ _ f k hf

-- TODO replace `{ x | k ≤ x }` with `Set.Ici k`
/--
theorem `antitoneOn_nat_Ici_of_succ_le` / 定理 `antitoneOn_nat_Ici_of_succ_le`

English:
theorem antitoneOn_nat_Ici_of_succ_le
  given: {f : Nat -> α} {k : Nat} (hf : forall n >= k, f (n + 1) <= f n)
  proof: @monotoneOn_nat_Ici_of_le_succ αᵒᵈ _ f k hf

中文:
定理 antitoneOn_nat_Ici_of_succ_le
  条件: {f : 自然数 -> α} {k : 自然数} (hf : 对任意 n >= k, f (n + 1) <= f n)
  证明: @monotoneOn_nat_Ici_of_le_succ αᵒᵈ _ f k hf

Depends on / 依赖: monotoneOn_nat_Ici_of_le_succ
-/
theorem antitoneOn_nat_Ici_of_succ_le {f : Nat -> α} {k : Nat} (hf : forall n >= k, f (n + 1) <= f n) :
    AntitoneOn f { x | k <= x } :=
  @monotoneOn_nat_Ici_of_le_succ αᵒᵈ _ f k hf

-- TODO replace `{ x | k ≤ x }` with `Set.Ici k`
/--
theorem `antitone_add_nat_iff_antitoneOn_nat_Ici` / 定理 `antitone_add_nat_iff_antitoneOn_nat_Ici`

English:
theorem antitone_add_nat_iff_antitoneOn_nat_Ici
  given: {f : Nat -> α} {k : Nat}
  proof: @monotone_add_nat_iff_monotoneOn_nat_Ici αᵒᵈ _ f k

中文:
定理 antitone_add_nat_iff_antitoneOn_nat_Ici
  条件: {f : 自然数 -> α} {k : 自然数}
  证明: @monotone_add_nat_iff_monotoneOn_nat_Ici αᵒᵈ _ f k

Depends on / 依赖: monotone_add_nat_iff_monotoneOn_nat_Ici
-/
theorem antitone_add_nat_iff_antitoneOn_nat_Ici {f : Nat -> α} {k : Nat} :
    Antitone (fun n => f (n + k)) ↔ AntitoneOn f { x | k <= x } :=
  @monotone_add_nat_iff_monotoneOn_nat_Ici αᵒᵈ _ f k

/--
theorem `strictMono_nat_of_lt_succ` / 定理 `strictMono_nat_of_lt_succ`

English:
theorem strictMono_nat_of_lt_succ
  given: {f : Nat -> α} (hf : forall n, f n < f (n + 1))
  statement: StrictMono f
  proof: Nat.rel_of_forall_rel_succ_of_lt (· < ·) hf

中文:
定理 strictMono_nat_of_lt_succ
  条件: {f : 自然数 -> α} (hf : 对任意 n, f n < f (n + 1))
  结论: 严格递增 f
  证明: Nat.rel_of_forall_rel_succ_of_lt (· < ·) hf

Depends on / 依赖: Nat.rel_of_forall_rel_succ_of_lt, rel_of_forall_rel_succ_of_lt
-/
theorem strictMono_nat_of_lt_succ {f : Nat -> α} (hf : forall n, f n < f (n + 1)) : StrictMono f :=
  Nat.rel_of_forall_rel_succ_of_lt (· < ·) hf

/--
theorem `strictAnti_nat_of_succ_lt` / 定理 `strictAnti_nat_of_succ_lt`

English:
theorem strictAnti_nat_of_succ_lt
  given: {f : Nat -> α} (hf : forall n, f (n + 1) < f n)
  statement: StrictAnti f
  proof: @strictMono_nat_of_lt_succ αᵒᵈ _ f hf

中文:
定理 strictAnti_nat_of_succ_lt
  条件: {f : 自然数 -> α} (hf : 对任意 n, f (n + 1) < f n)
  结论: 严格递减 f
  证明: @strictMono_nat_of_lt_succ αᵒᵈ _ f hf

Depends on / 依赖: strictMono_nat_of_lt_succ
-/
theorem strictAnti_nat_of_succ_lt {f : Nat -> α} (hf : forall n, f (n + 1) < f n) : StrictAnti f :=
  @strictMono_nat_of_lt_succ αᵒᵈ _ f hf

namespace Nat

/--
theorem `exists_strictMono'` / 定理 `exists_strictMono'`

English:
theorem exists_strictMono'
  given: [NoMaxOrder α] (a : α)
  statement: exists f : Nat -> α, StrictMono f ∧ f 0 = a
  proof: by
  choose g hg using fun x : α => exists_gt x
  exact ⟨fun n => Nat.recOn n a fun _ => g, strictMono_nat_of_lt_succ fun n => hg _, rfl⟩

中文:
定理 存在_strictMono'
  条件: [NoMax序 α] (a : α)
  结论: 存在 f : 自然数 -> α, 严格递增 f ∧ f 0 = a
  证明: by
  choose g hg using fun x : α => exists_gt x
  exact ⟨fun n => Nat.recOn n a fun _ => g, strictMono_nat_of_lt_succ fun n => hg _, rfl⟩

Depends on / 依赖: Nat.recOn, exists_gt, strictMono_nat_of_lt_succ
-/
theorem exists_strictMono' [NoMaxOrder α] (a : α) : exists f : Nat -> α, StrictMono f ∧ f 0 = a := by
  choose g hg using fun x : α => exists_gt x
  exact ⟨fun n => Nat.recOn n a fun _ => g, strictMono_nat_of_lt_succ fun n => hg _, rfl⟩

/--
theorem `exists_strictAnti'` / 定理 `exists_strictAnti'`

English:
theorem exists_strictAnti'
  given: [NoMinOrder α] (a : α)
  statement: exists f : Nat -> α, StrictAnti f ∧ f 0 = a
  proof: exists_strictMono' (OrderDual.toDual a)

中文:
定理 存在_strictAnti'
  条件: [NoMin序 α] (a : α)
  结论: 存在 f : 自然数 -> α, 严格递减 f ∧ f 0 = a
  证明: exists_strictMono' (OrderDual.toDual a)

Depends on / 依赖: OrderDual, OrderDual.toDual, exists_strictMono, toDual
-/
theorem exists_strictAnti' [NoMinOrder α] (a : α) : exists f : Nat -> α, StrictAnti f ∧ f 0 = a :=
  exists_strictMono' (OrderDual.toDual a)

/--
theorem `exists_strictMono_subsequence` / 定理 `exists_strictMono_subsequence`

English:
theorem exists_strictMono_subsequence
  given: {P : Nat -> Prop} (h : forall N, exists n > N, P n)
  proof: by
  have : NoMaxOrder {n // P n} :=
    ⟨fun n => Exists.intro ⟨(h n.1).choose, (h n.1).choose_spec.2⟩ (h n.1).choose_spec.1⟩
  obtain ⟨f, hf, _⟩ := Nat.exists_strictMono' (⟨(h 0).choose, (h 0).choose_spec.2⟩ : {n // P n})
  exact Exists.intro (fun n => (f n).1) ⟨hf, fun n => (f n).2⟩

中文:
定理 存在_strictMono_subsequence
  条件: {P : 自然数 -> 命题} (h : 对任意 N, 存在 n > N, P n)
  证明: by
  have : NoMaxOrder {n // P n} :=
    ⟨fun n => Exists.intro ⟨(h n.1).choose, (h n.1).choose_spec.2⟩ (h n.1).choose_spec.1⟩
  obtain ⟨f, hf, _⟩ := Nat.exists_strictMono' (⟨(h 0).choose, (h 0).choose_spec.2⟩ : {n // P n})
  exact Exists.intro (fun n => (f n).1) ⟨hf, fun n => (f n).2⟩

Depends on / 依赖: Exists, Exists.intro, Nat.exists_strictMono, NoMaxOrder, choose_spec, exists_strictMono
-/
theorem exists_strictMono_subsequence {P : Nat -> Prop} (h : forall N, exists n > N, P n) :
    exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P (φ n) := by
  have : NoMaxOrder {n // P n} :=
    ⟨fun n => Exists.intro ⟨(h n.1).choose, (h n.1).choose_spec.2⟩ (h n.1).choose_spec.1⟩
  obtain ⟨f, hf, _⟩ := Nat.exists_strictMono' (⟨(h 0).choose, (h 0).choose_spec.2⟩ : {n // P n})
  exact Exists.intro (fun n => (f n).1) ⟨hf, fun n => (f n).2⟩

variable (α)

/--
theorem `exists_strictMono` / 定理 `exists_strictMono`

English:
theorem exists_strictMono
  given: [Nonempty α] [NoMaxOrder α]
  statement: exists f : Nat -> α, StrictMono f
  proof: let ⟨a⟩ := ‹Nonempty α›
  let ⟨f, hf, _⟩ := exists_strictMono' a
  ⟨f, hf⟩

中文:
定理 存在_strictMono
  条件: [非空 α] [NoMax序 α]
  结论: 存在 f : 自然数 -> α, 严格递增 f
  证明: let ⟨a⟩ := ‹Nonempty α›
  let ⟨f, hf, _⟩ := exists_strictMono' a
  ⟨f, hf⟩

Depends on / 依赖: Nonempty, exists_strictMono
-/
theorem exists_strictMono [Nonempty α] [NoMaxOrder α] : exists f : Nat -> α, StrictMono f :=
  let ⟨a⟩ := ‹Nonempty α›
  let ⟨f, hf, _⟩ := exists_strictMono' a
  ⟨f, hf⟩

/--
theorem `exists_strictAnti` / 定理 `exists_strictAnti`

English:
theorem exists_strictAnti
  given: [Nonempty α] [NoMinOrder α]
  statement: exists f : Nat -> α, StrictAnti f
  proof: exists_strictMono αᵒᵈ

中文:
定理 存在_strictAnti
  条件: [非空 α] [NoMin序 α]
  结论: 存在 f : 自然数 -> α, 严格递减 f
  证明: exists_strictMono αᵒᵈ

Depends on / 依赖: exists_strictMono
-/
theorem exists_strictAnti [Nonempty α] [NoMinOrder α] : exists f : Nat -> α, StrictAnti f :=
  exists_strictMono αᵒᵈ

/--
lemma `pow_self_mono` / 引理 `pow_self_mono`

English:
lemma pow_self_mono
  statement: Monotone fun n : Nat => n ^ n
  proof: by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [Nat.pow_succ]
  exact (Nat.pow_le_pow_left n.le_succ _).trans (Nat.le_mul_of_pos_right _ n.succ_pos)

中文:
引理 pow_self_mono
  结论: 递增 fun n : 自然数 => n ^ n
  证明: by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [Nat.pow_succ]
  exact (Nat.pow_le_pow_left n.le_succ _).trans (Nat.le_mul_of_pos_right _ n.succ_pos)

Depends on / 依赖: Nat.le_mul_of_pos_right, Nat.pow_le_pow_left, Nat.pow_succ, le_mul_of_pos_right, le_succ, monotone_nat_of_le_succ, n.le_succ, n.succ_pos, pow_le_pow_left, pow_succ, succ_pos
-/
lemma pow_self_mono : Monotone fun n : Nat => n ^ n := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [Nat.pow_succ]
  exact (Nat.pow_le_pow_left n.le_succ _).trans (Nat.le_mul_of_pos_right _ n.succ_pos)

/--
lemma `pow_monotoneOn` / 引理 `pow_monotoneOn`

English:
lemma pow_monotoneOn
  statement: MonotoneOn (fun p : Nat × Nat => p.1 ^ p.2) {p | p.1 != 0}
  proof: fun _p _ _q hq hpq =>
  (Nat.pow_le_pow_left hpq.1 _).trans (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hq) hpq.2)

中文:
引理 pow_monotoneOn
  结论: MonotoneOn (fun p : 自然数 × 自然数 => p.1 ^ p.2) {p | p.1 != 0}
  证明: fun _p _ _q hq hpq =>
  (Nat.pow_le_pow_left hpq.1 _).trans (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hq) hpq.2)
-/
lemma pow_monotoneOn : MonotoneOn (fun p : Nat × Nat => p.1 ^ p.2) {p | p.1 != 0} := fun _p _ _q hq hpq =>
  (Nat.pow_le_pow_left hpq.1 _).trans (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hq) hpq.2)

/--
lemma `pow_self_strictMonoOn` / 引理 `pow_self_strictMonoOn`

English:
lemma pow_self_strictMonoOn
  statement: StrictMonoOn (fun n : Nat => n ^ n) {n : Nat | n != 0}
  proof: fun _m hm _n hn hmn =>
    (Nat.pow_lt_pow_left hmn hm).trans_le (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hn) hmn.le)

中文:
引理 pow_self_strictMonoOn
  结论: StrictMonoOn (fun n : 自然数 => n ^ n) {n : 自然数 | n != 0}
  证明: fun _m hm _n hn hmn =>
    (Nat.pow_lt_pow_left hmn hm).trans_le (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hn) hmn.le)

Depends on / 依赖: Nat.pos_iff_ne_zero, Nat.pow_le_pow_right, Nat.pow_lt_pow_left, hmn.le, pos_iff_ne_zero, pow_le_pow_right, pow_lt_pow_left, trans_le
-/
lemma pow_self_strictMonoOn : StrictMonoOn (fun n : Nat => n ^ n) {n : Nat | n != 0} :=
  fun _m hm _n hn hmn =>
    (Nat.pow_lt_pow_left hmn hm).trans_le (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hn) hmn.le)

end Nat

/--
theorem `Int.rel_of_forall_rel_succ_of_lt` / 定理 `Int.rel_of_forall_rel_succ_of_lt`

English:
theorem Int.rel_of_forall_rel_succ_of_lt
  statement: (r : β -> β -> Prop) [IsTrans β r] {f : Int -> β}
  proof: by
  rcases lt.dest hab with ⟨n, rfl⟩
  clear hab
  induction n with
  | zero => rw [Int.ofNat_one]; apply h
  | succ n ihn => rw [Int.natCast_succ, ← Int.add_assoc]; exact _root_.trans ihn (h _)

中文:
定理 整数.rel_of_对任意_rel_succ_of_lt
  结论: (r : β -> β -> 命题) [是Trans β r] {f : 整数 -> β}
  证明: by
  rcases lt.dest hab with ⟨n, rfl⟩
  clear hab
  induction n with
  | zero => rw [Int.ofNat_one]; apply h
  | succ n ihn => rw [Int.natCast_succ, ← Int.add_assoc]; exact _root_.trans ihn (h _)

Depends on / 依赖: Int.add_assoc, Int.natCast_succ, Int.ofNat_one, _root_, _root_.trans, add_assoc, lt.dest, natCast_succ, ofNat_one
-/
theorem Int.rel_of_forall_rel_succ_of_lt (r : β -> β -> Prop) [IsTrans β r] {f : Int -> β}
    (h : forall n, r (f n) (f (n + 1))) ⦃a b : Int⦄ (hab : a < b) : r (f a) (f b) := by
  rcases lt.dest hab with ⟨n, rfl⟩
  clear hab
  induction n with
  | zero => rw [Int.ofNat_one]; apply h
  | succ n ihn => rw [Int.natCast_succ, ← Int.add_assoc]; exact _root_.trans ihn (h _)

/--
theorem `Int.rel_of_forall_rel_succ_of_le` / 定理 `Int.rel_of_forall_rel_succ_of_le`

English:
theorem Int.rel_of_forall_rel_succ_of_le
  statement: (r : β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Int -> β}
  proof: hab.eq_or_lt.elim (fun h => h ▸ refl _) fun h' => Int.rel_of_forall_rel_succ_of_lt r h h'

中文:
定理 整数.rel_of_对任意_rel_succ_of_le
  结论: (r : β -> β -> 命题) [Std.Refl r] [是Trans β r] {f : 整数 -> β}
  证明: hab.eq_or_lt.elim (fun h => h ▸ refl _) fun h' => Int.rel_of_forall_rel_succ_of_lt r h h'

Depends on / 依赖: Int.rel_of_forall_rel_succ_of_lt, eq_or_lt, hab.eq_or_lt.elim, rel_of_forall_rel_succ_of_lt
-/
theorem Int.rel_of_forall_rel_succ_of_le (r : β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Int -> β}
    (h : forall n, r (f n) (f (n + 1))) ⦃a b : Int⦄ (hab : a <= b) : r (f a) (f b) :=
  hab.eq_or_lt.elim (fun h => h ▸ refl _) fun h' => Int.rel_of_forall_rel_succ_of_lt r h h'

/--
theorem `monotone_int_of_le_succ` / 定理 `monotone_int_of_le_succ`

English:
theorem monotone_int_of_le_succ
  given: {f : Int -> α} (hf : forall n, f n <= f (n + 1))
  statement: Monotone f
  proof: Int.rel_of_forall_rel_succ_of_le (· <= ·) hf

中文:
定理 monotone_int_of_le_succ
  条件: {f : 整数 -> α} (hf : 对任意 n, f n <= f (n + 1))
  结论: 递增 f
  证明: Int.rel_of_forall_rel_succ_of_le (· <= ·) hf

Depends on / 依赖: Int.rel_of_forall_rel_succ_of_le, rel_of_forall_rel_succ_of_le
-/
theorem monotone_int_of_le_succ {f : Int -> α} (hf : forall n, f n <= f (n + 1)) : Monotone f :=
  Int.rel_of_forall_rel_succ_of_le (· <= ·) hf

/--
theorem `antitone_int_of_succ_le` / 定理 `antitone_int_of_succ_le`

English:
theorem antitone_int_of_succ_le
  given: {f : Int -> α} (hf : forall n, f (n + 1) <= f n)
  statement: Antitone f
  proof: Int.rel_of_forall_rel_succ_of_le (· >= ·) hf

中文:
定理 antitone_int_of_succ_le
  条件: {f : 整数 -> α} (hf : 对任意 n, f (n + 1) <= f n)
  结论: 递减 f
  证明: Int.rel_of_forall_rel_succ_of_le (· >= ·) hf

Depends on / 依赖: Int.rel_of_forall_rel_succ_of_le, rel_of_forall_rel_succ_of_le
-/
theorem antitone_int_of_succ_le {f : Int -> α} (hf : forall n, f (n + 1) <= f n) : Antitone f :=
  Int.rel_of_forall_rel_succ_of_le (· >= ·) hf

/--
theorem `strictMono_int_of_lt_succ` / 定理 `strictMono_int_of_lt_succ`

English:
theorem strictMono_int_of_lt_succ
  given: {f : Int -> α} (hf : forall n, f n < f (n + 1))
  statement: StrictMono f
  proof: Int.rel_of_forall_rel_succ_of_lt (· < ·) hf

中文:
定理 strictMono_int_of_lt_succ
  条件: {f : 整数 -> α} (hf : 对任意 n, f n < f (n + 1))
  结论: 严格递增 f
  证明: Int.rel_of_forall_rel_succ_of_lt (· < ·) hf

Depends on / 依赖: Int.rel_of_forall_rel_succ_of_lt, rel_of_forall_rel_succ_of_lt
-/
theorem strictMono_int_of_lt_succ {f : Int -> α} (hf : forall n, f n < f (n + 1)) : StrictMono f :=
  Int.rel_of_forall_rel_succ_of_lt (· < ·) hf

/--
theorem `strictAnti_int_of_succ_lt` / 定理 `strictAnti_int_of_succ_lt`

English:
theorem strictAnti_int_of_succ_lt
  given: {f : Int -> α} (hf : forall n, f (n + 1) < f n)
  statement: StrictAnti f
  proof: Int.rel_of_forall_rel_succ_of_lt (· > ·) hf

中文:
定理 strictAnti_int_of_succ_lt
  条件: {f : 整数 -> α} (hf : 对任意 n, f (n + 1) < f n)
  结论: 严格递减 f
  证明: Int.rel_of_forall_rel_succ_of_lt (· > ·) hf

Depends on / 依赖: Int.rel_of_forall_rel_succ_of_lt, rel_of_forall_rel_succ_of_lt
-/
theorem strictAnti_int_of_succ_lt {f : Int -> α} (hf : forall n, f (n + 1) < f n) : StrictAnti f :=
  Int.rel_of_forall_rel_succ_of_lt (· > ·) hf

namespace Int

variable (α)
variable [Nonempty α] [NoMinOrder α] [NoMaxOrder α]

/--
theorem `exists_strictMono` / 定理 `exists_strictMono`

English:
theorem exists_strictMono
  statement: exists f : Int -> α, StrictMono f
  proof: by
  inhabit α
  rcases Nat.exists_strictMono' (default : α) with ⟨f, hf, hf₀⟩
  rcases Nat.exists_strictAnti' (default : α) with ⟨g, hg, hg₀⟩
  refine ⟨fun n => Int.casesOn n f fun n => g (n + 1), strictMono_int_of_lt_succ ?_⟩
  rintro (n | _ | n)
  · exact hf n.lt_succ_self
  · change g 1 < f 0
  

中文:
定理 存在_strictMono
  结论: 存在 f : 整数 -> α, 严格递增 f
  证明: by
  inhabit α
  rcases Nat.exists_strictMono' (default : α) with ⟨f, hf, hf₀⟩
  rcases Nat.exists_strictAnti' (default : α) with ⟨g, hg, hg₀⟩
  refine ⟨fun n => Int.casesOn n f fun n => g (n + 1), strictMono_int_of_lt_succ ?_⟩
  rintro (n | _ | n)
  · exact hf n.lt_succ_self
  · change g 1 < f 0
  

Depends on / 依赖: Int.casesOn, Nat.exists_strictAnti, Nat.exists_strictMono, Nat.lt_succ_self, Nat.zero_lt_one, casesOn, exists_strictAnti, exists_strictMono, inhabit, lt_succ_self, n.lt_succ_self, strictMono_int_of_lt_succ, zero_lt_one
-/
theorem exists_strictMono : exists f : Int -> α, StrictMono f := by
  inhabit α
  rcases Nat.exists_strictMono' (default : α) with ⟨f, hf, hf₀⟩
  rcases Nat.exists_strictAnti' (default : α) with ⟨g, hg, hg₀⟩
  refine ⟨fun n => Int.casesOn n f fun n => g (n + 1), strictMono_int_of_lt_succ ?_⟩
  rintro (n | _ | n)
  · exact hf n.lt_succ_self
  · change g 1 < f 0
    rw [hf₀]; rw [← hg₀]
    exact hg Nat.zero_lt_one
  · exact hg (Nat.lt_succ_self _)

/--
theorem `exists_strictAnti` / 定理 `exists_strictAnti`

English:
theorem exists_strictAnti
  statement: exists f : Int -> α, StrictAnti f
  proof: exists_strictMono αᵒᵈ

中文:
定理 存在_strictAnti
  结论: 存在 f : 整数 -> α, 严格递减 f
  证明: exists_strictMono αᵒᵈ

Depends on / 依赖: exists_strictMono
-/
theorem exists_strictAnti : exists f : Int -> α, StrictAnti f :=
  exists_strictMono αᵒᵈ

end Int

-- TODO@Yael: Generalize the following four to succ orders
/--
theorem `Monotone.ne_of_lt_of_lt_nat` / 定理 `Monotone.ne_of_lt_of_lt_nat`

English:
theorem Monotone.ne_of_lt_of_lt_nat
  statement: {f : Nat -> α} (hf : Monotone f) (n : Nat) {x : α} (h1 : f n < x)
  proof: by
  rintro rfl
  exact (hf.reflect_lt h1).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h2)

中文:
定理 递增.ne_of_lt_of_lt_nat
  结论: {f : 自然数 -> α} (hf : 递增 f) (n : 自然数) {x : α} (h1 : f n < x)
  证明: by
  rintro rfl
  exact (hf.reflect_lt h1).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h2)

Depends on / 依赖: Nat.le_of_lt_succ, hf.reflect_lt, le_of_lt_succ, not_ge, reflect_lt
-/
theorem Monotone.ne_of_lt_of_lt_nat {f : Nat -> α} (hf : Monotone f) (n : Nat) {x : α} (h1 : f n < x)
    (h2 : x < f (n + 1)) (a : Nat) : f a != x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h2)

/--
theorem `Antitone.ne_of_lt_of_lt_nat` / 定理 `Antitone.ne_of_lt_of_lt_nat`

English:
theorem Antitone.ne_of_lt_of_lt_nat
  statement: {f : Nat -> α} (hf : Antitone f) (n : Nat) {x : α}
  proof: by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h1)

中文:
定理 递减.ne_of_lt_of_lt_nat
  结论: {f : 自然数 -> α} (hf : 递减 f) (n : 自然数) {x : α}
  证明: by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h1)

Depends on / 依赖: Nat.le_of_lt_succ, hf.reflect_lt, le_of_lt_succ, not_ge, reflect_lt
-/
theorem Antitone.ne_of_lt_of_lt_nat {f : Nat -> α} (hf : Antitone f) (n : Nat) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : Nat) : f a != x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h1)

/--
theorem `Monotone.ne_of_lt_of_lt_int` / 定理 `Monotone.ne_of_lt_of_lt_int`

English:
theorem Monotone.ne_of_lt_of_lt_int
  statement: {f : Int -> α} (hf : Monotone f) (n : Int) {x : α} (h1 : f n < x)
  proof: by
  rintro rfl
  exact (hf.reflect_lt h1).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h2)

中文:
定理 递增.ne_of_lt_of_lt_int
  结论: {f : 整数 -> α} (hf : 递增 f) (n : 整数) {x : α} (h1 : f n < x)
  证明: by
  rintro rfl
  exact (hf.reflect_lt h1).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h2)

Depends on / 依赖: Int.le_of_lt_add_one, hf.reflect_lt, le_of_lt_add_one, not_ge, reflect_lt
-/
theorem Monotone.ne_of_lt_of_lt_int {f : Int -> α} (hf : Monotone f) (n : Int) {x : α} (h1 : f n < x)
    (h2 : x < f (n + 1)) (a : Int) : f a != x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h2)

/--
theorem `Antitone.ne_of_lt_of_lt_int` / 定理 `Antitone.ne_of_lt_of_lt_int`

English:
theorem Antitone.ne_of_lt_of_lt_int
  statement: {f : Int -> α} (hf : Antitone f) (n : Int) {x : α}
  proof: by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h1)

中文:
定理 递减.ne_of_lt_of_lt_int
  结论: {f : 整数 -> α} (hf : 递减 f) (n : 整数) {x : α}
  证明: by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h1)

Depends on / 依赖: Int.le_of_lt_add_one, hf.reflect_lt, le_of_lt_add_one, not_ge, reflect_lt
-/
theorem Antitone.ne_of_lt_of_lt_int {f : Int -> α} (hf : Antitone f) (n : Int) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : Int) : f a != x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h1)

end Preorder

/--
lemma `Nat.stabilises_of_monotone` / 引理 `Nat.stabilises_of_monotone`

English:
lemma Nat.stabilises_of_monotone
  statement: {f : Nat -> Nat} {b n : Nat} (hfmono : Monotone f) (hfb : forall m, f m <= b)
  proof: by
  obtain ⟨m, hmb, hm⟩ : exists m <= b, f m = f (m + 1) := by
    contrapose! hfb
    let rec strictMono : forall m <= b + 1, m <= f m
    | 0, _ => Nat.zero_le _
| m + 1, hmb => (strictMono _ <| m.le_succ.trans hmb).trans_lt (hfmono m.le_succ).lt_of_ne
hfb _ Nat.le_of_succ_le_succ hmb
    exact ⟨

中文:
引理 自然数.stabilises_of_monotone
  结论: {f : 自然数 -> 自然数} {b n : 自然数} (hfmono : 递增 f) (hfb : 对任意 m, f m <= b)
  证明: by
  obtain ⟨m, hmb, hm⟩ : exists m <= b, f m = f (m + 1) := by
    contrapose! hfb
    let rec strictMono : forall m <= b + 1, m <= f m
    | 0, _ => Nat.zero_le _
| m + 1, hmb => (strictMono _ <| m.le_succ.trans hmb).trans_lt (hfmono m.le_succ).lt_of_ne
hfb _ Nat.le_of_succ_le_succ hmb
    exact ⟨

Depends on / 依赖: Nat.le_of_succ_le_succ, Nat.rec, Nat.zero_le, contrapose, hfmono, hfstab, le_of_succ_le_succ, le_rfl, le_succ, lt_of_ne, m.le_succ, m.le_succ.trans, replace, strictMono, symm.trans, trans_lt, zero_le
-/
lemma Nat.stabilises_of_monotone {f : Nat -> Nat} {b n : Nat} (hfmono : Monotone f) (hfb : forall m, f m <= b)
    (hfstab : forall m, f m = f (m + 1) -> f (m + 1) = f (m + 2)) (hbn : b <= n) : f n = f b := by
  obtain ⟨m, hmb, hm⟩ : exists m <= b, f m = f (m + 1) := by
    contrapose! hfb
    let rec strictMono : forall m <= b + 1, m <= f m
    | 0, _ => Nat.zero_le _
| m + 1, hmb => (strictMono _ <| m.le_succ.trans hmb).trans_lt (hfmono m.le_succ).lt_of_ne
hfb _ Nat.le_of_succ_le_succ hmb
    exact ⟨b + 1, strictMono _ le_rfl⟩
  replace key : forall k : Nat, f (m + k) = f (m + k + 1) ∧ f (m + k) = f m := fun k =>
    Nat.rec ⟨hm, rfl⟩ (fun k ih => ⟨hfstab _ ih.1, ih.1.symm.trans ih.2⟩) k
  replace key : forall k >= m, f k = f m := fun k hk =>
    (congr_arg f (Nat.add_sub_of_le hk)).symm.trans (key (k - m)).2
  exact (key n (hmb.trans hbn)).trans (key b hmb).symm

/--
lemma `Nat.stabilises_of_antitone` / 引理 `Nat.stabilises_of_antitone`

English:
lemma Nat.stabilises_of_antitone
  statement: {f : Nat -> Nat} (hfmono : Antitone f)
  proof: by
  induction h : f 0 using Nat.strongRecOn generalizing f with
  | ind n ih =>
    by_cases heq : f 0 = f 1
    · have flat (j : Nat) : f j = f (j + 1) := by induction j with grind
      exact ⟨0, Nat.zero_le _, fun m _ => by induction m with grind⟩
    · have hlt : f 1 < f 0 := (hfmono (Nat.le_su

中文:
引理 自然数.stabilises_of_antitone
  结论: {f : 自然数 -> 自然数} (hfmono : 递减 f)
  证明: by
  induction h : f 0 using Nat.strongRecOn generalizing f with
  | ind n ih =>
    by_cases heq : f 0 = f 1
    · have flat (j : Nat) : f j = f (j + 1) := by induction j with grind
      exact ⟨0, Nat.zero_le _, fun m _ => by induction m with grind⟩
    · have hlt : f 1 < f 0 := (hfmono (Nat.le_su

Depends on / 依赖: Antitone, Nat.le_succ, Nat.strongRecOn, Nat.zero_le, generalizing, hfmono, hg_anti, le_succ, lt_of_ne, specialize, strongRecOn, zero_le
-/
lemma Nat.stabilises_of_antitone {f : Nat -> Nat} (hfmono : Antitone f)
    (hfstab : forall m, f m = f (m + 1) -> f (m + 1) = f (m + 2)) :
    exists n <= f 0, forall m, n <= m -> f m = f n := by
  induction h : f 0 using Nat.strongRecOn generalizing f with
  | ind n ih =>
    by_cases heq : f 0 = f 1
    · have flat (j : Nat) : f j = f (j + 1) := by induction j with grind
      exact ⟨0, Nat.zero_le _, fun m _ => by induction m with grind⟩
    · have hlt : f 1 < f 0 := (hfmono (Nat.le_succ 0)).lt_of_ne' heq
      let g (i : Nat) := f (i + 1)
      have hg_anti : Antitone g := by grind [Antitone]
      obtain ⟨p, hp, hp'⟩ := ih (f 1) (by grind) hg_anti (by grind) rfl
      refine ⟨p + 1, by omega, fun m hm => ?_⟩
      specialize hp' (m - 1) (by lia)
      grind

/--
lemma `converges_of_monotone_of_bounded` / 引理 `converges_of_monotone_of_bounded`

English:
lemma converges_of_monotone_of_bounded
  statement: {f : Nat -> Nat} (mono_f : Monotone f)
  proof: by
  induction c with
  | zero => use 0, 0, fun n _ => Nat.eq_zero_of_le_zero (hc n)
  | succ c ih =>
    by_cases! h : forall n, f n <= c
    · exact ih h
    · obtain ⟨N, hN⟩ := h
      replace hN : f N = c + 1 := by specialize hc N; lia
      use c + 1, N; intro n hn
      specialize mono_f hn; s

中文:
引理 converges_of_monotone_of_bounded
  结论: {f : 自然数 -> 自然数} (mono_f : 递增 f)
  证明: by
  induction c with
  | zero => use 0, 0, fun n _ => Nat.eq_zero_of_le_zero (hc n)
  | succ c ih =>
    by_cases! h : forall n, f n <= c
    · exact ih h
    · obtain ⟨N, hN⟩ := h
      replace hN : f N = c + 1 := by specialize hc N; lia
      use c + 1, N; intro n hn
      specialize mono_f hn; s

Depends on / 依赖: Nat.eq_zero_of_le_zero, eq_zero_of_le_zero, mono_f, replace, specialize
-/
lemma converges_of_monotone_of_bounded {f : Nat -> Nat} (mono_f : Monotone f)
    {c : Nat} (hc : forall n, f n <= c) : exists b N, forall n >= N, f n = b := by
  induction c with
  | zero => use 0, 0, fun n _ => Nat.eq_zero_of_le_zero (hc n)
  | succ c ih =>
    by_cases! h : forall n, f n <= c
    · exact ih h
    · obtain ⟨N, hN⟩ := h
      replace hN : f N = c + 1 := by specialize hc N; lia
      use c + 1, N; intro n hn
      specialize mono_f hn; specialize hc n; lia
