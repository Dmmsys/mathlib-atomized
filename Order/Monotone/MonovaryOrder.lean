/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Monotone.Monovary
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Interpreting monovarying functions as monotone functions

This file proves that monovarying functions to linear orders can be made simultaneously monotone by
setting the correct order on their shared indexing type.
-/

@[expose] public section

open Function Set

variable {ι ι' α β γ : Type*}

section
variable [LinearOrder α] [LinearOrder β] (f : ι -> α) (g : ι -> β) {s : Set ι}

/--
Definition of `MonovaryOrder` / `MonovaryOrder` 的定义

English:
definition MonovaryOrder
  signature: (i j : ι)
  body: Prod.Lex (· < ·) (Prod.Lex (· < ·) WellOrderingRel) (f i, g i, i) (f j, g j, j)

中文:
定义 MonovaryOrder
  签名: (i j : ι)
  定义体: Prod.Lex (· < ·) (Prod.Lex (· < ·) WellOrderingRel) (f i, g i, i) (f j, g j, j)

Depends on / 依赖: Prod.Lex, WellOrderingRel
-/
def MonovaryOrder (i j : ι) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) WellOrderingRel) (f i, g i, i) (f j, g j, j)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStrictTotalOrder ι (MonovaryOrder f g)
  body: Std.trichotomous_of_rel_or_eq_or_rel_swap fun {a b} => by
    convert! trichotomous_of (Prod.Lex (· < ·) <| Prod.Lex (· < ·) WellOrderingRel) _ _
    · simp only [Prod.ext_iff, ← and_assoc, imp_and, iff_and_self]
      exact ⟨congr_arg _, congr_arg _⟩
    · infer_instance
  irrefl i := by rw [Monova

中文:
实例 :
  签名: IsStrictTotalOrder ι (MonovaryOrder f g)
  定义体: Std.trichotomous_of_rel_or_eq_or_rel_swap fun {a b} => by
    convert! trichotomous_of (Prod.Lex (· < ·) <| Prod.Lex (· < ·) WellOrderingRel) _ _
    · simp only [Prod.ext_iff, ← and_assoc, imp_and, iff_and_self]
      exact ⟨congr_arg _, congr_arg _⟩
    · infer_instance
  irrefl i := by rw [Monova

Depends on / 依赖: MonovaryOrder, Prod.Lex, Prod.ext_iff, Std.trichotomous_of_rel_or_eq_or_rel_swap, WellOrderingRel, _root_, _root_.trans, and_assoc, congr_arg, convert, ext_iff, iff_and_self, imp_and, infer_instance, irrefl, trichotomous_of, trichotomous_of_rel_or_eq_or_rel_swap
-/
instance : IsStrictTotalOrder ι (MonovaryOrder f g) where
  toTrichotomous := Std.trichotomous_of_rel_or_eq_or_rel_swap fun {a b} => by
    convert! trichotomous_of (Prod.Lex (· < ·) <| Prod.Lex (· < ·) WellOrderingRel) _ _
    · simp only [Prod.ext_iff, ← and_assoc, imp_and, iff_and_self]
      exact ⟨congr_arg _, congr_arg _⟩
    · infer_instance
  irrefl i := by rw [MonovaryOrder]; exact irrefl _
  trans i j k := by rw [MonovaryOrder]; exact _root_.trans

variable {f g}

/--
lemma `monovaryOn_iff_exists_monotoneOn` / 引理 `monovaryOn_iff_exists_monotoneOn`

English:
lemma monovaryOn_iff_exists_monotoneOn
  proof: by
  classical
  let := linearOrderOfSTO (MonovaryOrder f g)
  refine ⟨fun hfg => ⟨‹_›, monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_,
    monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_⟩, ?_⟩
  · obtain h | ⟨h, -⟩ := Prod.lex_iff.1 hij <;> exact h.le
  · obtain h | ⟨-, h⟩ := Prod.lex_iff.1 

中文:
引理 monovaryOn_iff_exists_monotoneOn
  证明: by
  classical
  let := linearOrderOfSTO (MonovaryOrder f g)
  refine ⟨fun hfg => ⟨‹_›, monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_,
    monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_⟩, ?_⟩
  · obtain h | ⟨h, -⟩ := Prod.lex_iff.1 hij <;> exact h.le
  · obtain h | ⟨-, h⟩ := Prod.lex_iff.1 

Depends on / 依赖: MonovaryOrder, Prod.lex_iff, classical, h.le, hf.monovaryOn, hfg.symm, lex_iff, linearOrderOfSTO, monotoneOn_iff_forall_lt, monovaryOn
-/
lemma monovaryOn_iff_exists_monotoneOn :
    MonovaryOn f g s ↔ exists (_ : LinearOrder ι), MonotoneOn f s ∧ MonotoneOn g s := by
  classical
  let := linearOrderOfSTO (MonovaryOrder f g)
  refine ⟨fun hfg => ⟨‹_›, monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_,
    monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_⟩, ?_⟩
  · obtain h | ⟨h, -⟩ := Prod.lex_iff.1 hij <;> exact h.le
  · obtain h | ⟨-, h⟩ := Prod.lex_iff.1 hij
    · exact hfg.symm hi hj h
    obtain h | ⟨h, -⟩ := Prod.lex_iff.1 h <;> exact h.le
  · rintro ⟨_, hf, hg⟩
    exact hf.monovaryOn hg

/--
lemma `antivaryOn_iff_exists_monotoneOn_antitoneOn` / 引理 `antivaryOn_iff_exists_monotoneOn_antitoneOn`

English:
lemma antivaryOn_iff_exists_monotoneOn_antitoneOn
  proof: by
  simp_rw [← monovaryOn_toDual_right, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

中文:
引理 antivaryOn_iff_exists_monotoneOn_antitoneOn
  证明: by
  simp_rw [← monovaryOn_toDual_right, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

Depends on / 依赖: monotoneOn_toDual_comp_iff, monovaryOn_iff_exists_monotoneOn, monovaryOn_toDual_right, simp_rw
-/
lemma antivaryOn_iff_exists_monotoneOn_antitoneOn :
    AntivaryOn f g s ↔ exists (_ : LinearOrder ι), MonotoneOn f s ∧ AntitoneOn g s := by
  simp_rw [← monovaryOn_toDual_right, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

/--
lemma `monovaryOn_iff_exists_antitoneOn` / 引理 `monovaryOn_iff_exists_antitoneOn`

English:
lemma monovaryOn_iff_exists_antitoneOn
  proof: by
  simp_rw [← antivaryOn_toDual_left, antivaryOn_iff_exists_monotoneOn_antitoneOn,
    monotoneOn_toDual_comp_iff]

中文:
引理 monovaryOn_iff_exists_antitoneOn
  证明: by
  simp_rw [← antivaryOn_toDual_left, antivaryOn_iff_exists_monotoneOn_antitoneOn,
    monotoneOn_toDual_comp_iff]

Depends on / 依赖: antivaryOn_iff_exists_monotoneOn_antitoneOn, antivaryOn_toDual_left, monotoneOn_toDual_comp_iff, simp_rw
-/
lemma monovaryOn_iff_exists_antitoneOn :
    MonovaryOn f g s ↔ exists (_ : LinearOrder ι), AntitoneOn f s ∧ AntitoneOn g s := by
  simp_rw [← antivaryOn_toDual_left, antivaryOn_iff_exists_monotoneOn_antitoneOn,
    monotoneOn_toDual_comp_iff]

/--
lemma `antivaryOn_iff_exists_antitoneOn_monotoneOn` / 引理 `antivaryOn_iff_exists_antitoneOn_monotoneOn`

English:
lemma antivaryOn_iff_exists_antitoneOn_monotoneOn
  proof: by
  simp_rw [← monovaryOn_toDual_left, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

中文:
引理 antivaryOn_iff_exists_antitoneOn_monotoneOn
  证明: by
  simp_rw [← monovaryOn_toDual_left, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

Depends on / 依赖: monotoneOn_toDual_comp_iff, monovaryOn_iff_exists_monotoneOn, monovaryOn_toDual_left, simp_rw
-/
lemma antivaryOn_iff_exists_antitoneOn_monotoneOn :
    AntivaryOn f g s ↔ exists (_ : LinearOrder ι), AntitoneOn f s ∧ MonotoneOn g s := by
  simp_rw [← monovaryOn_toDual_left, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

/--
lemma `monovary_iff_exists_monotone` / 引理 `monovary_iff_exists_monotone`

English:
lemma monovary_iff_exists_monotone
  proof: by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_monotoneOn]

中文:
引理 monovary_iff_exists_monotone
  证明: by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_monotoneOn]

Depends on / 依赖: monovaryOn_iff_exists_monotoneOn, monovaryOn_univ
-/
lemma monovary_iff_exists_monotone :
    Monovary f g ↔ exists (_ : LinearOrder ι), Monotone f ∧ Monotone g := by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_monotoneOn]

/--
lemma `monovary_iff_exists_antitone` / 引理 `monovary_iff_exists_antitone`

English:
lemma monovary_iff_exists_antitone
  proof: by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_antitoneOn]

中文:
引理 monovary_iff_exists_antitone
  证明: by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_antitoneOn]

Depends on / 依赖: monovaryOn_iff_exists_antitoneOn, monovaryOn_univ
-/
lemma monovary_iff_exists_antitone :
    Monovary f g ↔ exists (_ : LinearOrder ι), Antitone f ∧ Antitone g := by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_antitoneOn]

/--
lemma `antivary_iff_exists_monotone_antitone` / 引理 `antivary_iff_exists_monotone_antitone`

English:
lemma antivary_iff_exists_monotone_antitone
  proof: by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_monotoneOn_antitoneOn]

中文:
引理 antivary_iff_exists_monotone_antitone
  证明: by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_monotoneOn_antitoneOn]

Depends on / 依赖: antivaryOn_iff_exists_monotoneOn_antitoneOn, antivaryOn_univ
-/
lemma antivary_iff_exists_monotone_antitone :
    Antivary f g ↔ exists (_ : LinearOrder ι), Monotone f ∧ Antitone g := by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_monotoneOn_antitoneOn]

/--
lemma `antivary_iff_exists_antitone_monotone` / 引理 `antivary_iff_exists_antitone_monotone`

English:
lemma antivary_iff_exists_antitone_monotone
  proof: by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_antitoneOn_monotoneOn]

alias ⟨MonovaryOn.exists_monotoneOn, _⟩ := monovaryOn_iff_exists_monotoneOn
alias ⟨MonovaryOn.exists_antitoneOn, _⟩ := monovaryOn_iff_exists_antitoneOn
alias ⟨AntivaryOn.exists_monotoneOn_antitoneOn, _⟩ := antivaryOn_iff_exi

中文:
引理 antivary_iff_exists_antitone_monotone
  证明: by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_antitoneOn_monotoneOn]

alias ⟨MonovaryOn.exists_monotoneOn, _⟩ := monovaryOn_iff_exists_monotoneOn
alias ⟨MonovaryOn.exists_antitoneOn, _⟩ := monovaryOn_iff_exists_antitoneOn
alias ⟨AntivaryOn.exists_monotoneOn_antitoneOn, _⟩ := antivaryOn_iff_exi

Depends on / 依赖: antivaryOn_iff_exists_antitoneOn_monotoneOn, antivaryOn_univ
-/
lemma antivary_iff_exists_antitone_monotone :
    Antivary f g ↔ exists (_ : LinearOrder ι), Antitone f ∧ Monotone g := by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_antitoneOn_monotoneOn]

alias ⟨MonovaryOn.exists_monotoneOn, _⟩ := monovaryOn_iff_exists_monotoneOn
alias ⟨MonovaryOn.exists_antitoneOn, _⟩ := monovaryOn_iff_exists_antitoneOn
alias ⟨AntivaryOn.exists_monotoneOn_antitoneOn, _⟩ := antivaryOn_iff_exists_monotoneOn_antitoneOn
alias ⟨AntivaryOn.exists_antitoneOn_monotoneOn, _⟩ := antivaryOn_iff_exists_antitoneOn_monotoneOn
alias ⟨Monovary.exists_monotone, _⟩ := monovary_iff_exists_monotone
alias ⟨Monovary.exists_antitone, _⟩ := monovary_iff_exists_antitone
alias ⟨Antivary.exists_monotone_antitone, _⟩ := antivary_iff_exists_monotone_antitone
alias ⟨Antivary.exists_antitone_monotone, _⟩ := antivary_iff_exists_antitone_monotone

end
