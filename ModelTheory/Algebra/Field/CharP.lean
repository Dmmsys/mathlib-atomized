/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing
public import Mathlib.ModelTheory.Algebra.Field.Basic

/-!
# First-order theory of fields

This file defines the first-order theory of fields of characteristic `p` as a theory over the
language of rings

## Main definitions

- `FirstOrder.Language.Theory.fieldOfChar` : the first-order theory of fields of characteristic `p`
  as a theory over the language of rings
-/

@[expose] public section

variable {p : Nat} {K : Type*}

namespace FirstOrder

namespace Field

open Language FirstOrder.Ring

/--
Definition of `eqZero` / `eqZero` 的定义

English:
definition eqZero
  signature: (n : Nat)
  body: Term.equal (termOfFreeCommRing n) 0

中文:
定义 eqZero
  签名: (n : 自然数)
  定义体: Term.equal (termOfFreeCommRing n) 0

Depends on / 依赖: Term.equal, termOfFreeCommRing
-/
noncomputable def eqZero (n : Nat) : Language.ring.Sentence :=
  Term.equal (termOfFreeCommRing n) 0

/--
theorem `realize_eqZero` / 定理 `realize_eqZero`

English:
theorem realize_eqZero
  statement: [CommRing K] [CompatibleRing K] (n : Nat)
  proof: by
  simp [eqZero]

中文:
定理 realize_eqZero
  结论: [CommRing K] [CompatibleRing K] (n : 自然数)
  证明: by
  simp [eqZero]
-/
@[simp] theorem realize_eqZero [CommRing K] [CompatibleRing K] (n : Nat)
    (v : Empty -> K) : (Formula.Realize (eqZero n) v) ↔ ((n : K) = 0) := by
  simp [eqZero]

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `_root_.FirstOrder.Language.Theory.fieldOfChar` / `_root_.FirstOrder.Language.Theory.fieldOfChar` 的定义

English:
definition _root_.FirstOrder.Language.Theory.fieldOfChar
  signature: (p : Nat)
  body: Theory.field union
  if p = 0
  then (fun q => ∼(eqZero q)) '' {q : Nat | q.Prime}
  else if p.Prime then {eqZero p}
  else {⊥}

中文:
定义 _root_.FirstOrder.Language.Theory.fieldOfChar
  签名: (p : 自然数)
  定义体: Theory.field union
  if p = 0
  then (fun q => ∼(eqZero q)) '' {q : Nat | q.Prime}
  else if p.Prime then {eqZero p}
  else {⊥}

Depends on / 依赖: Theory, Theory.field, eqZero, p.Prime, q.Prime
-/
noncomputable def _root_.FirstOrder.Language.Theory.fieldOfChar (p : Nat) : Language.ring.Theory :=
  Theory.field union
  if p = 0
  then (fun q => ∼(eqZero q)) '' {q : Nat | q.Prime}
  else if p.Prime then {eqZero p}
  else {⊥}

/--
Instance `model_hasChar_of_charP` / 实例 `model_hasChar_of_charP`

English:
instance model_hasChar_of_charP
  signature: [Field K] [CompatibleRing K] [CharP K p]
  body: by
  refine Language.Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  cases CharP.char_is_prime_or_zero K p with
  | inl hp =>
    simp [hp.ne_zero, hp, Sentence.Realize]
  | inr hp =>
    subst hp
    simp only [ite_true, Theory.model_iff, Set.mem_image, Set.mem_ofPred_eq,
      Sentence.Realize, for

中文:
实例 model_hasChar_of_charP
  签名: [Field K] [CompatibleRing K] [CharP K p]
  定义体: by
  refine Language.Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  cases CharP.char_is_prime_or_zero K p with
  | inl hp =>
    simp [hp.ne_zero, hp, Sentence.Realize]
  | inr hp =>
    subst hp
    simp only [ite_true, Theory.model_iff, Set.mem_image, Set.mem_ofPred_eq,
      Sentence.Realize, for

Depends on / 依赖: CharP.charP_to_charZero, CharP.char_is_prime_or_zero, CharZero, CharZero.charZero_iff_forall_prime_ne_zero, Formula, Formula.realize_not, Language, Language.Theory.model_union_iff, Realize, Sentence, Sentence.Realize, Set.mem_image, Set.mem_ofPred_eq, Theory, Theory.model_iff, and_imp, charP_to_charZero, charZero_iff_forall_prime_ne_zero, char_is_prime_or_zero, forall_exists_index
-/
instance model_hasChar_of_charP [Field K] [CompatibleRing K] [CharP K p] :
    (Theory.fieldOfChar p).Model K := by
  refine Language.Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  cases CharP.char_is_prime_or_zero K p with
  | inl hp =>
    simp [hp.ne_zero, hp, Sentence.Realize]
  | inr hp =>
    subst hp
    simp only [ite_true, Theory.model_iff, Set.mem_image, Set.mem_ofPred_eq,
      Sentence.Realize, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Formula.realize_not, realize_eqZero, ← CharZero.charZero_iff_forall_prime_ne_zero]
    exact CharP.charP_to_charZero K

/--
theorem `charP_iff_model_fieldOfChar` / 定理 `charP_iff_model_fieldOfChar`

English:
theorem charP_iff_model_fieldOfChar
  given: [Field K] [CompatibleRing K]
  proof: by
  simp only [Theory.fieldOfChar, Theory.model_union_iff,
    (show (Theory.field.Model K) by infer_instance), true_and]
  split_ifs with hp0 hp
  · subst hp0
    simp only [Theory.model_iff, Set.mem_image, Set.mem_ofPred_eq, Sentence.Realize,
      forall_exists_index, and_imp, forall_apply_eq_im

中文:
定理 charP_iff_model_fieldOfChar
  条件: [Field K] [CompatibleRing K]
  证明: by
  simp only [Theory.fieldOfChar, Theory.model_union_iff,
    (show (Theory.field.Model K) by infer_instance), true_and]
  split_ifs with hp0 hp
  · subst hp0
    simp only [Theory.model_iff, Set.mem_image, Set.mem_ofPred_eq, Sentence.Realize,
      forall_exists_index, and_imp, forall_apply_eq_im

Depends on / 依赖: CharP.charP_to_charZero, CharP.ofCharZero, CharZero, CharZero.charZero_iff_forall_prime_ne_zero, Formula, Formula.realize_not, Realize, Sentence, Sentence.Realize, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff, Theory, Theory.field.Model, Theory.fieldOfChar, Theory.model_iff, Theory.model_union_iff, and_imp, charP_to_charZero, charZero_iff_forall_prime_ne_zero
-/
theorem charP_iff_model_fieldOfChar [Field K] [CompatibleRing K] :
    (Theory.fieldOfChar p).Model K ↔ CharP K p := by
  simp only [Theory.fieldOfChar, Theory.model_union_iff,
    (show (Theory.field.Model K) by infer_instance), true_and]
  split_ifs with hp0 hp
  · subst hp0
    simp only [Theory.model_iff, Set.mem_image, Set.mem_ofPred_eq, Sentence.Realize,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Formula.realize_not,
      realize_eqZero, ← CharZero.charZero_iff_forall_prime_ne_zero]
    exact ⟨fun _ => CharP.ofCharZero _, fun _ => CharP.charP_to_charZero K⟩
  · simp only [Theory.model_iff, Set.mem_singleton_iff, Sentence.Realize, forall_eq,
      realize_eqZero, ← CharP.charP_iff_prime_eq_zero hp]
  · simp only [Theory.model_iff, Set.mem_singleton_iff, Sentence.Realize,
      forall_eq, Formula.realize_bot, false_iff]
    intro H
    cases (CharP.char_is_prime_or_zero K p) <;> simp_all

/--
Instance `model_fieldOfChar_of_charP` / 实例 `model_fieldOfChar_of_charP`

English:
instance model_fieldOfChar_of_charP
  signature: [Field K] [CompatibleRing K]
  body: charP_iff_model_fieldOfChar.2 inferInstance

中文:
实例 model_fieldOfChar_of_charP
  签名: [Field K] [CompatibleRing K]
  定义体: charP_iff_model_fieldOfChar.2 inferInstance

Depends on / 依赖: charP_iff_model_fieldOfChar
-/
instance model_fieldOfChar_of_charP [Field K] [CompatibleRing K]
    [CharP K p] : (Theory.fieldOfChar p).Model K :=
  charP_iff_model_fieldOfChar.2 inferInstance

variable (p) (K)
/--
theorem `charP_of_model_fieldOfChar` / 定理 `charP_of_model_fieldOfChar`

English:
theorem charP_of_model_fieldOfChar
  statement: [Field K] [CompatibleRing K]
  proof: charP_iff_model_fieldOfChar.1 h

中文:
定理 charP_of_model_fieldOfChar
  结论: [Field K] [CompatibleRing K]
  证明: charP_iff_model_fieldOfChar.1 h

Depends on / 依赖: charP_iff_model_fieldOfChar
-/
theorem charP_of_model_fieldOfChar [Field K] [CompatibleRing K]
    [h : (Theory.fieldOfChar p).Model K] : CharP K p :=
  charP_iff_model_fieldOfChar.1 h

end Field

end FirstOrder
