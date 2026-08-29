/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Extension of a monotone function from a set to the whole space

In this file we prove that if a function is monotone and is bounded on a set `s`, then it admits a
monotone extension to the whole space.
-/

public section


open Set

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] {f : α -> β} {s : Set α}

/--
theorem `MonotoneOn.exists_monotone_extension` / 定理 `MonotoneOn.exists_monotone_extension`

English:
theorem MonotoneOn.exists_monotone_extension
  statement: (h : MonotoneOn f s) (hl : BddBelow (f '' s))
  proof: by
  classical
    /- The extension is defined by `f x = f a` for `x ≤ a`, and `f x` is the supremum of the values
      of `f` to the left of `x` for `x ≥ a`. -/
    rcases hl with ⟨a, ha⟩
    have hu' : forall x, BddAbove (f '' (Iic x inter s)) := fun x =>
      hu.mono (image_mono inter_subset_ri

中文:
定理 MonotoneOn.exists_monotone_extension
  结论: (h : MonotoneOn f s) (hl : BddBelow (f '' s))
  证明: by
  classical
    /- The extension is defined by `f x = f a` for `x ≤ a`, and `f x` is the supremum of the values
      of `f` to the left of `x` for `x ≥ a`. -/
    rcases hl with ⟨a, ha⟩
    have hu' : forall x, BddAbove (f '' (Iic x inter s)) := fun x =>
      hu.mono (image_mono inter_subset_ri

Depends on / 依赖: classical
-/
theorem MonotoneOn.exists_monotone_extension (h : MonotoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : exists g : α -> β, Monotone g ∧ EqOn f g s := by
  classical
    /- The extension is defined by `f x = f a` for `x ≤ a`, and `f x` is the supremum of the values
      of `f` to the left of `x` for `x ≥ a`. -/
    rcases hl with ⟨a, ha⟩
    have hu' : forall x, BddAbove (f '' (Iic x inter s)) := fun x =>
      hu.mono (image_mono inter_subset_right)
    let g : α -> β := fun x => if Disjoint (Iic x) s then a else sSup (f '' (Iic x inter s))
    have hgs : EqOn f g s := by
      intro x hx
      simp only [g]
      have : IsGreatest (Iic x inter s) x := ⟨⟨self_mem_Iic, hx⟩, fun y hy => hy.1⟩
      rw [if_neg this.nonempty.not_disjoint]; rw [((h.mono inter_subset_right).map_isGreatest this).csSup_eq]
    refine ⟨g, fun x y hxy => ?_, hgs⟩
    by_cases hx : Disjoint (Iic x) s <;> by_cases hy : Disjoint (Iic y) s <;>
      simp only [g, if_pos, if_neg, not_false_iff, *, refl]
    · rcases not_disjoint_iff_nonempty_inter.1 hy with ⟨z, hz⟩
      exact le_csSup_of_le (hu' _) (mem_image_of_mem _ hz) (ha <| mem_image_of_mem _ hz.2)
    · exact (hx <| hy.mono_left <| Iic_subset_Iic.2 hxy).elim
    · rw [not_disjoint_iff_nonempty_inter] at hx
      gcongr; exacts [hu' _, hx.image _]

/--
theorem `AntitoneOn.exists_antitone_extension` / 定理 `AntitoneOn.exists_antitone_extension`

English:
theorem AntitoneOn.exists_antitone_extension
  statement: (h : AntitoneOn f s) (hl : BddBelow (f '' s))
  proof: h.dual_right.exists_monotone_extension hu hl

中文:
定理 AntitoneOn.exists_antitone_extension
  结论: (h : AntitoneOn f s) (hl : BddBelow (f '' s))
  证明: h.dual_right.exists_monotone_extension hu hl

Depends on / 依赖: dual_right, exists_monotone_extension, h.dual_right.exists_monotone_extension
-/
theorem AntitoneOn.exists_antitone_extension (h : AntitoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : exists g : α -> β, Antitone g ∧ EqOn f g s :=
  h.dual_right.exists_monotone_extension hu hl
