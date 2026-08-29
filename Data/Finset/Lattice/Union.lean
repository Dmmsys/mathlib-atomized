/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union

/-!
# Relating `Finset.biUnion` with lattice operations

This file shows `Finset.biUnion` could alternatively be defined in terms of `Finset.sup`.

## TODO

Remove `Finset.biUnion` in favour of `Finset.sup`.
-/

public section

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}
variable {s s₁ s₂ : Finset β} {f g : β -> α} {a : α}

namespace Finset

section Sup

variable [SemilatticeSup α] [OrderBot α]

@[simp, grind =]
/--
theorem `sup_biUnion` / 定理 `sup_biUnion`

English:
theorem sup_biUnion
  given: [DecidableEq β] (s : Finset γ) (t : γ -> Finset β)
  proof: eq_of_forall_ge_iff fun c => by simp [@forall_comm _ β]

中文:
定理 sup_biUnion
  条件: [DecidableEq β] (s : Finset γ) (t : γ -> Finset β)
  证明: eq_of_forall_ge_iff fun c => by simp [@forall_comm _ β]

Depends on / 依赖: eq_of_forall_ge_iff, forall_comm
-/
theorem sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ -> Finset β) :
    (s.biUnion t).sup f = s.sup fun x => (t x).sup f :=
  eq_of_forall_ge_iff fun c => by simp [@forall_comm _ β]

end Sup

section Inf

variable [SemilatticeInf α] [OrderTop α]

/--
theorem `inf_biUnion` / 定理 `inf_biUnion`

English:
theorem inf_biUnion
  given: [DecidableEq β] (s : Finset γ) (t : γ -> Finset β)
  proof: @sup_biUnion αᵒᵈ _ _ _ _ _ _ _ _

中文:
定理 inf_biUnion
  条件: [DecidableEq β] (s : Finset γ) (t : γ -> Finset β)
  证明: @sup_biUnion αᵒᵈ _ _ _ _ _ _ _ _
-/
@[simp, grind =] theorem inf_biUnion [DecidableEq β] (s : Finset γ) (t : γ -> Finset β) :
    (s.biUnion t).inf f = s.inf fun x => (t x).inf f :=
  @sup_biUnion αᵒᵈ _ _ _ _ _ _ _ _

end Inf

section Sup'

variable [SemilatticeSup α]

variable {s : Finset β} (H : s.Nonempty) (f : β -> α)

/--
theorem `sup'_biUnion` / 定理 `sup'_biUnion`

English:
theorem sup'_biUnion
  statement: [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ -> Finset β}
  proof: eq_of_forall_ge_iff fun c => by simp [@forall_comm _ β]

中文:
定理 sup'_biUnion
  结论: [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ -> Finset β}
  证明: eq_of_forall_ge_iff fun c => by simp [@forall_comm _ β]
-/
theorem sup'_biUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ -> Finset β}
    (Ht : forall b, (t b).Nonempty) :
    (s.biUnion t).sup' (Hs.biUnion fun b _ => Ht b) f = s.sup' Hs (fun b => (t b).sup' (Ht b) f) :=
  eq_of_forall_ge_iff fun c => by simp [@forall_comm _ β]

end Sup'

section Inf'

variable [SemilatticeInf α]

variable {s : Finset β} (H : s.Nonempty) (f : β -> α)

/--
theorem `inf'_biUnion` / 定理 `inf'_biUnion`

English:
theorem inf'_biUnion
  statement: [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ -> Finset β}
  proof: sup'_biUnion (α := αᵒᵈ) _ Hs Ht

中文:
定理 inf'_biUnion
  结论: [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ -> Finset β}
  证明: sup'_biUnion (α := αᵒᵈ) _ Hs Ht
-/
theorem inf'_biUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ -> Finset β}
    (Ht : forall b, (t b).Nonempty) :
    (s.biUnion t).inf' (Hs.biUnion fun b _ => Ht b) f = s.inf' Hs (fun b => (t b).inf' (Ht b) f) :=
  sup'_biUnion (α := αᵒᵈ) _ Hs Ht

end Inf'

variable [DecidableEq α] {s : Finset ι} {f : ι -> Finset α} {a : α}

/--
theorem `sup_eq_biUnion` / 定理 `sup_eq_biUnion`

English:
theorem sup_eq_biUnion
  given: {α β} [DecidableEq β] (s : Finset α) (t : α -> Finset β)
  proof: by
  ext
  rw [mem_sup]; rw [mem_biUnion]

中文:
定理 sup_eq_biUnion
  条件: {α β} [DecidableEq β] (s : Finset α) (t : α -> Finset β)
  证明: by
  ext
  rw [mem_sup]; rw [mem_biUnion]

Depends on / 依赖: mem_biUnion, mem_sup
-/
theorem sup_eq_biUnion {α β} [DecidableEq β] (s : Finset α) (t : α -> Finset β) :
    s.sup t = s.biUnion t := by
  ext
  rw [mem_sup]; rw [mem_biUnion]

end Finset
