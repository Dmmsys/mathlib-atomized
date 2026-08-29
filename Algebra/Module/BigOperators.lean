/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.Module.End

/-!
# Finite sums over modules over a ring
-/

public section

variable {ι κ α β R M : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
theorem `List.sum_smul` / 定理 `List.sum_smul`

English:
theorem List.sum_smul
  given: {l : List R} {x : M}
  statement: l.sum • x = (l.map fun r => r • x).sum
  proof: map_list_sum ((smulAddHom R M).flip x) l

中文:
定理 List.sum_smul
  条件: {l : List R} {x : M}
  结论: l.sum • x = (l.map fun r => r • x).sum
  证明: map_list_sum ((smulAddHom R M).flip x) l

Depends on / 依赖: map_list_sum, smulAddHom
-/
theorem List.sum_smul {l : List R} {x : M} : l.sum • x = (l.map fun r => r • x).sum :=
  map_list_sum ((smulAddHom R M).flip x) l

/--
theorem `Multiset.sum_smul` / 定理 `Multiset.sum_smul`

English:
theorem Multiset.sum_smul
  given: {l : Multiset R} {x : M}
  statement: l.sum • x = (l.map fun r => r • x).sum
  proof: ((smulAddHom R M).flip x).map_multiset_sum l

中文:
定理 Multiset.sum_smul
  条件: {l : Multiset R} {x : M}
  结论: l.sum • x = (l.map fun r => r • x).sum
  证明: ((smulAddHom R M).flip x).map_multiset_sum l

Depends on / 依赖: map_multiset_sum, smulAddHom
-/
theorem Multiset.sum_smul {l : Multiset R} {x : M} : l.sum • x = (l.map fun r => r • x).sum :=
  ((smulAddHom R M).flip x).map_multiset_sum l

/--
theorem `Multiset.sum_smul_sum` / 定理 `Multiset.sum_smul_sum`

English:
theorem Multiset.sum_smul_sum
  given: {s : Multiset R} {t : Multiset M}
  proof: by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [add_smul, ih, ← Multiset.smul_sum]

中文:
定理 Multiset.sum_smul_sum
  条件: {s : Multiset R} {t : Multiset M}
  证明: by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [add_smul, ih, ← Multiset.smul_sum]

Depends on / 依赖: Multiset, Multiset.induction, Multiset.smul_sum, add_smul, smul_sum
-/
theorem Multiset.sum_smul_sum {s : Multiset R} {t : Multiset M} :
    s.sum • t.sum = ((s ×ˢ t).map fun p : R × M => p.fst • p.snd).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [add_smul, ih, ← Multiset.smul_sum]

/--
theorem `Finset.sum_smul` / 定理 `Finset.sum_smul`

English:
theorem Finset.sum_smul
  given: {f : ι -> R} {s : Finset ι} {x : M}
  proof: map_sum ((smulAddHom R M).flip x) f s

中文:
定理 Finset.sum_smul
  条件: {f : ι -> R} {s : Finset ι} {x : M}
  证明: map_sum ((smulAddHom R M).flip x) f s

Depends on / 依赖: map_sum, smulAddHom
-/
theorem Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} :
    (∑ i in s, f i) • x = ∑ i in s, f i • x := map_sum ((smulAddHom R M).flip x) f s

/--
lemma `Finset.sum_smul_sum` / 引理 `Finset.sum_smul_sum`

English:
lemma Finset.sum_smul_sum
  given: (s : Finset α) (t : Finset β) {f : α -> R} {g : β -> M}
  proof: by
  simp_rw [sum_smul, ← smul_sum]

中文:
引理 Finset.sum_smul_sum
  条件: (s : Finset α) (t : Finset β) {f : α -> R} {g : β -> M}
  证明: by
  simp_rw [sum_smul, ← smul_sum]

Depends on / 依赖: simp_rw, smul_sum, sum_smul
-/
lemma Finset.sum_smul_sum (s : Finset α) (t : Finset β) {f : α -> R} {g : β -> M} :
    (∑ i in s, f i) • ∑ j in t, g j = ∑ i in s, ∑ j in t, f i • g j := by
  simp_rw [sum_smul, ← smul_sum]

/--
lemma `Fintype.sum_smul_sum` / 引理 `Fintype.sum_smul_sum`

English:
lemma Fintype.sum_smul_sum
  given: [Fintype α] [Fintype β] (f : α -> R) (g : β -> M)
  proof: Finset.sum_smul_sum _ _

中文:
引理 Fintype.sum_smul_sum
  条件: [Fintype α] [Fintype β] (f : α -> R) (g : β -> M)
  证明: Finset.sum_smul_sum _ _

Depends on / 依赖: Finset, Finset.sum_smul_sum, sum_smul_sum
-/
lemma Fintype.sum_smul_sum [Fintype α] [Fintype β] (f : α -> R) (g : β -> M) :
    (∑ i, f i) • ∑ j, g j = ∑ i, ∑ j, f i • g j := Finset.sum_smul_sum _ _

end AddCommMonoid

open Finset

/--
theorem `Finset.cast_card` / 定理 `Finset.cast_card`

English:
theorem Finset.cast_card
  given: [NonAssocSemiring R] (s : Finset α)
  statement: (#s : R) = ∑ _ in s, 1
  proof: by
  rw [Finset.sum_const]; rw [Nat.smul_one_eq_cast]

中文:
定理 Finset.cast_card
  条件: [NonAssocSemiring R] (s : Finset α)
  结论: (#s : R) = ∑ _ in s, 1
  证明: by
  rw [Finset.sum_const]; rw [Nat.smul_one_eq_cast]

Depends on / 依赖: Finset, Finset.sum_const, Nat.smul_one_eq_cast, smul_one_eq_cast, sum_const
-/
theorem Finset.cast_card [NonAssocSemiring R] (s : Finset α) : (#s : R) = ∑ _ in s, 1 := by
  rw [Finset.sum_const]; rw [Nat.smul_one_eq_cast]

namespace Fintype
variable [DecidableEq ι] [Fintype ι] [AddCommMonoid α]

/--
lemma `sum_piFinset_apply` / 引理 `sum_piFinset_apply`

English:
lemma sum_piFinset_apply
  given: (f : κ -> α) (s : Finset κ) (i : ι)
  proof: by
  classical
  rw [Finset.sum_comp]
  simp only [eval_image_piFinset_const, card_filter_piFinset_const s, ite_smul, zero_smul, smul_sum,
    Finset.sum_ite_mem, inter_self]

@[simp]

中文:
引理 sum_piFinset_apply
  条件: (f : κ -> α) (s : Finset κ) (i : ι)
  证明: by
  classical
  rw [Finset.sum_comp]
  simp only [eval_image_piFinset_const, card_filter_piFinset_const s, ite_smul, zero_smul, smul_sum,
    Finset.sum_ite_mem, inter_self]

@[simp]

Depends on / 依赖: Finset, Finset.sum_comp, Finset.sum_ite_mem, card_filter_piFinset_const, classical, eval_image_piFinset_const, inter_self, ite_smul, smul_sum, sum_comp, sum_ite_mem, zero_smul
-/
lemma sum_piFinset_apply (f : κ -> α) (s : Finset κ) (i : ι) :
    ∑ g in piFinset fun _ : ι => s, f (g i) = #s ^ (card ι - 1) • ∑ b in s, f b := by
  classical
  rw [Finset.sum_comp]
  simp only [eval_image_piFinset_const, card_filter_piFinset_const s, ite_smul, zero_smul, smul_sum,
    Finset.sum_ite_mem, inter_self]

@[simp]
/--
lemma `sum_single_smul` / 引理 `sum_single_smul`

English:
lemma sum_single_smul
  proof: by
  rw [Finset.sum_eq_single i₀]; rw [Pi.single_eq_same] <;> aesop

中文:
引理 sum_single_smul
  证明: by
  rw [Finset.sum_eq_single i₀]; rw [Pi.single_eq_same] <;> aesop

Depends on / 依赖: Finset, Finset.sum_eq_single, Pi.single_eq_same, single_eq_same, sum_eq_single
-/
lemma sum_single_smul
    {R : Type*} [Semiring R] [Module R α] (f : ι -> α) (r : R) (i₀ : ι) :
    ∑ i, (Pi.single (M := fun _ => R) i₀ r i) • f i = r • f i₀ := by
  rw [Finset.sum_eq_single i₀]; rw [Pi.single_eq_same] <;> aesop

end Fintype
