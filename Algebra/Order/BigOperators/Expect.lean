/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Algebra.Order.Module.Rat
public import Mathlib.Tactic.GCongr

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Order properties of the average over a finset
-/

public section

open Function
open Fintype (card)
open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

local notation a " /Rat " q => (q : Rat>=0)⁻¹ • a

namespace Finset
section OrderedAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module Rat>=0 α]
  {s : Finset ι} {f g : ι -> α}

/--
lemma `expect_eq_zero_iff_of_nonneg` / 引理 `expect_eq_zero_iff_of_nonneg`

English:
lemma expect_eq_zero_iff_of_nonneg
  given: (hf : forall i in s, 0 <= f i)
  proof: by
  simp +contextual [expect, sum_eq_zero_iff_of_nonneg hf]

中文:
引理 expect_eq_zero_iff_of_nonneg
  条件: (hf : 对任意 i in s, 0 <= f i)
  证明: by
  simp +contextual [expect, sum_eq_zero_iff_of_nonneg hf]

Depends on / 依赖: contextual, expect, sum_eq_zero_iff_of_nonneg
-/
lemma expect_eq_zero_iff_of_nonneg (hf : forall i in s, 0 <= f i) :
    𝔼 i in s, f i = 0 ↔ forall i in s, f i = 0 := by
  simp +contextual [expect, sum_eq_zero_iff_of_nonneg hf]

/--
lemma `expect_eq_zero_iff_of_nonpos` / 引理 `expect_eq_zero_iff_of_nonpos`

English:
lemma expect_eq_zero_iff_of_nonpos
  given: (hf : forall i in s, f i <= 0)
  proof: by
  simp +contextual [expect, sum_eq_zero_iff_of_nonpos hf]

中文:
引理 expect_eq_zero_iff_of_nonpos
  条件: (hf : 对任意 i in s, f i <= 0)
  证明: by
  simp +contextual [expect, sum_eq_zero_iff_of_nonpos hf]

Depends on / 依赖: contextual, expect, sum_eq_zero_iff_of_nonpos
-/
lemma expect_eq_zero_iff_of_nonpos (hf : forall i in s, f i <= 0) :
    𝔼 i in s, f i = 0 ↔ forall i in s, f i = 0 := by
  simp +contextual [expect, sum_eq_zero_iff_of_nonpos hf]

section PosSMulMono
variable [PosSMulMono Rat>=0 α] {a : α}

@[gcongr]
/--
lemma `expect_le_expect` / 引理 `expect_le_expect`

English:
lemma expect_le_expect
  given: (hfg : forall i in s, f i <= g i)
  statement: 𝔼 i in s, f i <= 𝔼 i in s, g i
  proof: smul_le_smul_of_nonneg_left (sum_le_sum hfg) by positivity

中文:
引理 expect_le_expect
  条件: (hfg : 对任意 i in s, f i <= g i)
  结论: 𝔼 i in s, f i <= 𝔼 i in s, g i
  证明: smul_le_smul_of_nonneg_left (sum_le_sum hfg) by positivity

Depends on / 依赖: smul_le_smul_of_nonneg_left, sum_le_sum
-/
lemma expect_le_expect (hfg : forall i in s, f i <= g i) : 𝔼 i in s, f i <= 𝔼 i in s, g i :=
smul_le_smul_of_nonneg_left (sum_le_sum hfg) by positivity

/--
lemma `expect_le` / 引理 `expect_le`

English:
lemma expect_le
  given: (hs : s.Nonempty) (h : forall x in s, f x <= a)
  statement: 𝔼 i in s, f i <= a
  proof: (inv_smul_le_iff_of_pos <| mod_cast hs.card_pos).2 by
    rw [Nat.cast_smul_eq_nsmul]; exact sum_le_card_nsmul _ _ _ h

中文:
引理 expect_le
  条件: (hs : s.Nonempty) (h : 对任意 x in s, f x <= a)
  结论: 𝔼 i in s, f i <= a
  证明: (inv_smul_le_iff_of_pos <| mod_cast hs.card_pos).2 by
    rw [Nat.cast_smul_eq_nsmul]; exact sum_le_card_nsmul _ _ _ h

Depends on / 依赖: Nat.cast_smul_eq_nsmul, card_pos, cast_smul_eq_nsmul, hs.card_pos, inv_smul_le_iff_of_pos, mod_cast, sum_le_card_nsmul
-/
lemma expect_le (hs : s.Nonempty) (h : forall x in s, f x <= a) : 𝔼 i in s, f i <= a :=
(inv_smul_le_iff_of_pos <| mod_cast hs.card_pos).2 by
    rw [Nat.cast_smul_eq_nsmul]; exact sum_le_card_nsmul _ _ _ h

/--
lemma `le_expect` / 引理 `le_expect`

English:
lemma le_expect
  given: (hs : s.Nonempty) (h : forall x in s, a <= f x)
  statement: a <= 𝔼 i in s, f i
  proof: (le_inv_smul_iff_of_pos <| mod_cast hs.card_pos).2 by
    rw [Nat.cast_smul_eq_nsmul]; exact card_nsmul_le_sum _ _ _ h

中文:
引理 le_expect
  条件: (hs : s.Nonempty) (h : 对任意 x in s, a <= f x)
  结论: a <= 𝔼 i in s, f i
  证明: (le_inv_smul_iff_of_pos <| mod_cast hs.card_pos).2 by
    rw [Nat.cast_smul_eq_nsmul]; exact card_nsmul_le_sum _ _ _ h

Depends on / 依赖: Nat.cast_smul_eq_nsmul, card_nsmul_le_sum, card_pos, cast_smul_eq_nsmul, hs.card_pos, le_inv_smul_iff_of_pos, mod_cast
-/
lemma le_expect (hs : s.Nonempty) (h : forall x in s, a <= f x) : a <= 𝔼 i in s, f i :=
(le_inv_smul_iff_of_pos <| mod_cast hs.card_pos).2 by
    rw [Nat.cast_smul_eq_nsmul]; exact card_nsmul_le_sum _ _ _ h

/--
lemma `expect_nonneg` / 引理 `expect_nonneg`

English:
lemma expect_nonneg
  given: (hf : forall i in s, 0 <= f i)
  statement: 0 <= 𝔼 i in s, f i
  proof: smul_nonneg (by positivity) sum_nonneg hf

中文:
引理 expect_nonneg
  条件: (hf : 对任意 i in s, 0 <= f i)
  结论: 0 <= 𝔼 i in s, f i
  证明: smul_nonneg (by positivity) sum_nonneg hf

Depends on / 依赖: smul_nonneg, sum_nonneg
-/
lemma expect_nonneg (hf : forall i in s, 0 <= f i) : 0 <= 𝔼 i in s, f i :=
smul_nonneg (by positivity) sum_nonneg hf

end PosSMulMono

section PosSMulMono
variable {M N : Type*} [AddCommMonoid M] [Module Rat>=0 M]
  [AddCommMonoid N] [PartialOrder N] [IsOrderedAddMonoid N] [Module Rat>=0 N]
  [PosSMulMono Rat>=0 N] {m : M -> N} {p : M -> Prop} {f : ι -> M} {s : Finset ι}

/--
lemma `le_expect_nonempty_of_subadditive_on_pred` / 引理 `le_expect_nonempty_of_subadditive_on_pred`

English:
lemma le_expect_nonempty_of_subadditive_on_pred
  statement: (h_add : forall a b, p a -> p b -> m (a + b) <= m a + m b)
  proof: by
  simp only [expect, h_div _ _ (sum_induction_nonempty _ _ hp_add hs_nonempty hs)]
  exact smul_le_smul_of_nonneg_left
(le_sum_nonempty_of_subadditive_on_pred _ _ h_add hp_add _ _ hs_nonempty hs) by positivity

中文:
引理 le_expect_nonempty_of_subadditive_on_pred
  结论: (h_add : 对任意 a b, p a -> p b -> m (a + b) <= m a + m b)
  证明: by
  simp only [expect, h_div _ _ (sum_induction_nonempty _ _ hp_add hs_nonempty hs)]
  exact smul_le_smul_of_nonneg_left
(le_sum_nonempty_of_subadditive_on_pred _ _ h_add hp_add _ _ hs_nonempty hs) by positivity

Depends on / 依赖: expect, h_add, h_div, hp_add, hs_nonempty, le_sum_nonempty_of_subadditive_on_pred, smul_le_smul_of_nonneg_left, sum_induction_nonempty
-/
lemma le_expect_nonempty_of_subadditive_on_pred (h_add : forall a b, p a -> p b -> m (a + b) <= m a + m b)
    (hp_add : forall a b, p a -> p b -> p (a + b)) (h_div : forall (n : Nat) a, p a -> m (a /Rat n) = m a /Rat n)
    (hs_nonempty : s.Nonempty) (hs : forall i in s, p (f i)) :
    m (𝔼 i in s, f i) <= 𝔼 i in s, m (f i) := by
  simp only [expect, h_div _ _ (sum_induction_nonempty _ _ hp_add hs_nonempty hs)]
  exact smul_le_smul_of_nonneg_left
(le_sum_nonempty_of_subadditive_on_pred _ _ h_add hp_add _ _ hs_nonempty hs) by positivity

/--
lemma `le_expect_nonempty_of_subadditive` / 引理 `le_expect_nonempty_of_subadditive`

English:
lemma le_expect_nonempty_of_subadditive
  statement: (m : M -> N) (h_mul : forall a b, m (a + b) <= m a + m b)
  proof: le_expect_nonempty_of_subadditive_on_pred (p := fun _ => True) (by simpa) (by simp) (by simpa) hs
    (by simp)

中文:
引理 le_expect_nonempty_of_subadditive
  结论: (m : M -> N) (h_mul : 对任意 a b, m (a + b) <= m a + m b)
  证明: le_expect_nonempty_of_subadditive_on_pred (p := fun _ => True) (by simpa) (by simp) (by simpa) hs
    (by simp)

Depends on / 依赖: le_expect_nonempty_of_subadditive_on_pred
-/
lemma le_expect_nonempty_of_subadditive (m : M -> N) (h_mul : forall a b, m (a + b) <= m a + m b)
    (h_div : forall (n : Nat) a, m (a /Rat n) = m a /Rat n) (hs : s.Nonempty) :
    m (𝔼 i in s, f i) <= 𝔼 i in s, m (f i) :=
  le_expect_nonempty_of_subadditive_on_pred (p := fun _ => True) (by simpa) (by simp) (by simpa) hs
    (by simp)

/--
lemma `le_expect_of_subadditive_on_pred` / 引理 `le_expect_of_subadditive_on_pred`

English:
lemma le_expect_of_subadditive_on_pred
  statement: (h_zero : m 0 = 0)
  proof: by
  obtain rfl | hs_nonempty := s.eq_empty_or_nonempty
  · simp [h_zero]
  · exact le_expect_nonempty_of_subadditive_on_pred h_add hp_add h_div hs_nonempty hs

中文:
引理 le_expect_of_subadditive_on_pred
  结论: (h_zero : m 0 = 0)
  证明: by
  obtain rfl | hs_nonempty := s.eq_empty_or_nonempty
  · simp [h_zero]
  · exact le_expect_nonempty_of_subadditive_on_pred h_add hp_add h_div hs_nonempty hs

Depends on / 依赖: eq_empty_or_nonempty, h_add, h_div, h_zero, hp_add, hs_nonempty, le_expect_nonempty_of_subadditive_on_pred, s.eq_empty_or_nonempty
-/
lemma le_expect_of_subadditive_on_pred (h_zero : m 0 = 0)
    (h_add : forall a b, p a -> p b -> m (a + b) <= m a + m b) (hp_add : forall a b, p a -> p b -> p (a + b))
    (h_div : forall (n : Nat) a, p a -> m (a /Rat n) = m a /Rat n)
    (hs : forall i in s, p (f i)) : m (𝔼 i in s, f i) <= 𝔼 i in s, m (f i) := by
  obtain rfl | hs_nonempty := s.eq_empty_or_nonempty
  · simp [h_zero]
  · exact le_expect_nonempty_of_subadditive_on_pred h_add hp_add h_div hs_nonempty hs

-- TODO: Contribute back better docstring to `le_prod_of_submultiplicative`
/--
lemma `le_expect_of_subadditive` / 引理 `le_expect_of_subadditive`

English:
lemma le_expect_of_subadditive
  statement: (h_zero : m 0 = 0) (h_add : forall a b, m (a + b) <= m a + m b)
  proof: le_expect_of_subadditive_on_pred (p := fun _ => True) h_zero (by simpa) (by simp) (by simpa)
    (by simp)

中文:
引理 le_expect_of_subadditive
  结论: (h_zero : m 0 = 0) (h_add : 对任意 a b, m (a + b) <= m a + m b)
  证明: le_expect_of_subadditive_on_pred (p := fun _ => True) h_zero (by simpa) (by simp) (by simpa)
    (by simp)

Depends on / 依赖: h_zero, le_expect_of_subadditive_on_pred
-/
lemma le_expect_of_subadditive (h_zero : m 0 = 0) (h_add : forall a b, m (a + b) <= m a + m b)
    (h_div : forall (n : Nat) a, m (a /Rat n) = m a /Rat n) : m (𝔼 i in s, f i) <= 𝔼 i in s, m (f i) :=
  le_expect_of_subadditive_on_pred (p := fun _ => True) h_zero (by simpa) (by simp) (by simpa)
    (by simp)

end PosSMulMono
end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] [Module Rat>=0 α]
  [PosSMulStrictMono Rat>=0 α] {s : Finset ι} {f g : ι -> α} {a : α}

/--
lemma `expect_lt_expect` / 引理 `expect_lt_expect`

English:
lemma expect_lt_expect
  given: (hfg : forall i in s, f i <= g i) (hfg' : exists i in s, f i < g i)
  proof: smul_lt_smul_of_pos_left (sum_lt_sum hfg hfg')
    (by obtain ⟨i, hi, -⟩ := hfg'; have : s.Nonempty := ⟨i, hi⟩; simpa)

中文:
引理 expect_lt_expect
  条件: (hfg : 对任意 i in s, f i <= g i) (hfg' : 存在 i in s, f i < g i)
  证明: smul_lt_smul_of_pos_left (sum_lt_sum hfg hfg')
    (by obtain ⟨i, hi, -⟩ := hfg'; have : s.Nonempty := ⟨i, hi⟩; simpa)

Depends on / 依赖: Nonempty, s.Nonempty, smul_lt_smul_of_pos_left, sum_lt_sum
-/
lemma expect_lt_expect (hfg : forall i in s, f i <= g i) (hfg' : exists i in s, f i < g i) :
    𝔼 i in s, f i < 𝔼 i in s, g i :=
  smul_lt_smul_of_pos_left (sum_lt_sum hfg hfg')
    (by obtain ⟨i, hi, -⟩ := hfg'; have : s.Nonempty := ⟨i, hi⟩; simpa)

/--
lemma `expect_lt` / 引理 `expect_lt`

English:
lemma expect_lt
  given: (hle : forall x in s, f x <= a) (hlt : exists x in s, f x < a)
  proof: by
  rw [← expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt

中文:
引理 expect_lt
  条件: (hle : 对任意 x in s, f x <= a) (hlt : 存在 x in s, f x < a)
  证明: by
  rw [← expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt

Depends on / 依赖: And.left, expect_const, expect_lt_expect, hlt.imp
-/
lemma expect_lt (hle : forall x in s, f x <= a) (hlt : exists x in s, f x < a) :
    𝔼 i in s, f i < a := by
  rw [← expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt

/--
lemma `lt_expect` / 引理 `lt_expect`

English:
lemma lt_expect
  given: (hle : forall x in s, a <= f x) (hlt : exists x in s, a < f x)
  proof: by
  rw [← expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt

中文:
引理 lt_expect
  条件: (hle : 对任意 x in s, a <= f x) (hlt : 存在 x in s, a < f x)
  证明: by
  rw [← expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt

Depends on / 依赖: And.left, expect_const, expect_lt_expect, hlt.imp
-/
lemma lt_expect (hle : forall x in s, a <= f x) (hlt : exists x in s, a < f x) :
    a < 𝔼 i in s, f i := by
  rw [← expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt

/--
lemma `expect_pos'` / 引理 `expect_pos'`

English:
lemma expect_pos'
  given: (h : forall i in s, 0 <= f i) (hs : exists i in s, 0 < f i)
  statement: 0 < 𝔼 i in s, f i
  proof: (expect_const_zero _).symm.trans_lt expect_lt_expect h hs

中文:
引理 expect_pos'
  条件: (h : 对任意 i in s, 0 <= f i) (hs : 存在 i in s, 0 < f i)
  结论: 0 < 𝔼 i in s, f i
  证明: (expect_const_zero _).symm.trans_lt expect_lt_expect h hs

Depends on / 依赖: expect_const_zero, expect_lt_expect, symm.trans_lt, trans_lt
-/
lemma expect_pos' (h : forall i in s, 0 <= f i) (hs : exists i in s, 0 < f i) : 0 < 𝔼 i in s, f i :=
(expect_const_zero _).symm.trans_lt expect_lt_expect h hs

/--
lemma `expect_pos` / 引理 `expect_pos`

English:
lemma expect_pos
  given: (hf : forall i in s, 0 < f i) (hs : s.Nonempty)
  statement: 0 < 𝔼 i in s, f i
  proof: smul_pos (inv_pos.2 <| mod_cast hs.card_pos) sum_pos hf hs

中文:
引理 expect_pos
  条件: (hf : 对任意 i in s, 0 < f i) (hs : s.Nonempty)
  结论: 0 < 𝔼 i in s, f i
  证明: smul_pos (inv_pos.2 <| mod_cast hs.card_pos) sum_pos hf hs

Depends on / 依赖: card_pos, hs.card_pos, inv_pos, mod_cast, smul_pos, sum_pos
-/
lemma expect_pos (hf : forall i in s, 0 < f i) (hs : s.Nonempty) : 0 < 𝔼 i in s, f i :=
smul_pos (inv_pos.2 <| mod_cast hs.card_pos) sum_pos hf hs

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α] [Module Rat>=0 α]
  [PosSMulMono Rat>=0 α] {s : Finset ι}
  {f g : ι -> α} {a : α}

/--
lemma `exists_lt_of_expect_lt_expect` / 引理 `exists_lt_of_expect_lt_expect`

English:
lemma exists_lt_of_expect_lt_expect
  given: (h : 𝔼 i in s, g i < 𝔼 i in s, f i)
  proof: by
  contrapose! h; exact expect_le_expect h

中文:
引理 exists_lt_of_expect_lt_expect
  条件: (h : 𝔼 i in s, g i < 𝔼 i in s, f i)
  证明: by
  contrapose! h; exact expect_le_expect h

Depends on / 依赖: contrapose, expect_le_expect
-/
lemma exists_lt_of_expect_lt_expect (h : 𝔼 i in s, g i < 𝔼 i in s, f i) :
    exists x in s, g x < f x := by
  contrapose! h; exact expect_le_expect h

/--
lemma `exists_lt_of_lt_expect` / 引理 `exists_lt_of_lt_expect`

English:
lemma exists_lt_of_lt_expect
  given: (hs : s.Nonempty) (h : a < 𝔼 i in s, f i)
  statement: exists x in s, a < f x
  proof: by
  contrapose! h; exact expect_le hs h

中文:
引理 exists_lt_of_lt_expect
  条件: (hs : s.Nonempty) (h : a < 𝔼 i in s, f i)
  结论: 存在 x in s, a < f x
  证明: by
  contrapose! h; exact expect_le hs h

Depends on / 依赖: contrapose, expect_le
-/
lemma exists_lt_of_lt_expect (hs : s.Nonempty) (h : a < 𝔼 i in s, f i) : exists x in s, a < f x := by
  contrapose! h; exact expect_le hs h

/--
lemma `exists_lt_of_expect_lt` / 引理 `exists_lt_of_expect_lt`

English:
lemma exists_lt_of_expect_lt
  given: (hs : s.Nonempty) (h : 𝔼 i in s, f i < a)
  statement: exists x in s, f x < a
  proof: by
  contrapose! h; exact le_expect hs h

中文:
引理 exists_lt_of_expect_lt
  条件: (hs : s.Nonempty) (h : 𝔼 i in s, f i < a)
  结论: 存在 x in s, f x < a
  证明: by
  contrapose! h; exact le_expect hs h

Depends on / 依赖: contrapose, le_expect
-/
lemma exists_lt_of_expect_lt (hs : s.Nonempty) (h : 𝔼 i in s, f i < a) : exists x in s, f x < a := by
  contrapose! h; exact le_expect hs h

end LinearOrderedAddCommMonoid

section LinearOrderedCancelAddMonoid
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α] [Module Rat>=0 α]
  [PosSMulStrictMono Rat>=0 α] {a : α} {s : Finset ι} {f g : ι -> α}

/--
lemma `exists_le_of_expect_le_expect` / 引理 `exists_le_of_expect_le_expect`

English:
lemma exists_le_of_expect_le_expect
  given: (hs : s.Nonempty) (h : 𝔼 i in s, g i <= 𝔼 i in s, f i)
  proof: by
  obtain ⟨_, hx⟩ := hs
  contrapose! h
  exact expect_lt_expect (fun _ hx => le_of_lt (h _ hx)) ⟨_, ⟨hx, h _ hx⟩⟩

中文:
引理 exists_le_of_expect_le_expect
  条件: (hs : s.Nonempty) (h : 𝔼 i in s, g i <= 𝔼 i in s, f i)
  证明: by
  obtain ⟨_, hx⟩ := hs
  contrapose! h
  exact expect_lt_expect (fun _ hx => le_of_lt (h _ hx)) ⟨_, ⟨hx, h _ hx⟩⟩

Depends on / 依赖: contrapose, expect_lt_expect, le_of_lt
-/
lemma exists_le_of_expect_le_expect (hs : s.Nonempty) (h : 𝔼 i in s, g i <= 𝔼 i in s, f i) :
    exists x in s, g x <= f x := by
  obtain ⟨_, hx⟩ := hs
  contrapose! h
  exact expect_lt_expect (fun _ hx => le_of_lt (h _ hx)) ⟨_, ⟨hx, h _ hx⟩⟩

/--
lemma `exists_le_of_le_expect` / 引理 `exists_le_of_le_expect`

English:
lemma exists_le_of_le_expect
  given: (hs : s.Nonempty) (h : a <= 𝔼 i in s, f i)
  statement: exists x in s, a <= f x
  proof: exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])

中文:
引理 exists_le_of_le_expect
  条件: (hs : s.Nonempty) (h : a <= 𝔼 i in s, f i)
  结论: 存在 x in s, a <= f x
  证明: exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])

Depends on / 依赖: exists_le_of_expect_le_expect, expect_const
-/
lemma exists_le_of_le_expect (hs : s.Nonempty) (h : a <= 𝔼 i in s, f i) : exists x in s, a <= f x :=
  exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])

/--
lemma `exists_le_of_expect_le` / 引理 `exists_le_of_expect_le`

English:
lemma exists_le_of_expect_le
  given: (hs : s.Nonempty) (h : 𝔼 i in s, f i <= a)
  statement: exists x in s, f x <= a
  proof: exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])

中文:
引理 exists_le_of_expect_le
  条件: (hs : s.Nonempty) (h : 𝔼 i in s, f i <= a)
  结论: 存在 x in s, f x <= a
  证明: exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])

Depends on / 依赖: exists_le_of_expect_le_expect, expect_const
-/
lemma exists_le_of_expect_le (hs : s.Nonempty) (h : 𝔼 i in s, f i <= a) : exists x in s, f x <= a :=
  exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])

end LinearOrderedCancelAddMonoid

section LinearOrderedAddCommGroup
variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Module Rat>=0 α] [PosSMulMono Rat>=0 α]

/--
lemma `abs_expect_le` / 引理 `abs_expect_le`

English:
lemma abs_expect_le
  given: (s : Finset ι) (f : ι -> α)
  statement: |𝔼 i in s, f i| <= 𝔼 i in s, |f i|
  proof: le_expect_of_subadditive abs_zero abs_add_le (fun _ => abs_nnqsmul _)

中文:
引理 abs_expect_le
  条件: (s : Finset ι) (f : ι -> α)
  结论: |𝔼 i in s, f i| <= 𝔼 i in s, |f i|
  证明: le_expect_of_subadditive abs_zero abs_add_le (fun _ => abs_nnqsmul _)

Depends on / 依赖: abs_add_le, abs_nnqsmul, abs_zero, le_expect_of_subadditive
-/
lemma abs_expect_le (s : Finset ι) (f : ι -> α) : |𝔼 i in s, f i| <= 𝔼 i in s, |f i| :=
  le_expect_of_subadditive abs_zero abs_add_le (fun _ => abs_nnqsmul _)

end LinearOrderedAddCommGroup

section LinearOrderedCommSemiring
variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] [Module Rat>=0 R]
  [PosSMulMono Rat>=0 R]

/--
lemma `expect_mul_sq_le_sq_mul_sq` / 引理 `expect_mul_sq_le_sq_mul_sq`

English:
lemma expect_mul_sq_le_sq_mul_sq
  given: (s : Finset ι) (f g : ι -> R)
  proof: by
  simp only [expect, smul_pow, inv_pow, smul_mul_smul_comm, ← sq]
  gcongr
  exact sum_mul_sq_le_sq_mul_sq ..

中文:
引理 expect_mul_sq_le_sq_mul_sq
  条件: (s : Finset ι) (f g : ι -> R)
  证明: by
  simp only [expect, smul_pow, inv_pow, smul_mul_smul_comm, ← sq]
  gcongr
  exact sum_mul_sq_le_sq_mul_sq ..

Depends on / 依赖: expect, inv_pow, smul_mul_smul_comm, smul_pow, sum_mul_sq_le_sq_mul_sq
-/
lemma expect_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι -> R) :
    (𝔼 i in s, f i * g i) ^ 2 <= (𝔼 i in s, f i ^ 2) * 𝔼 i in s, g i ^ 2 := by
  simp only [expect, smul_pow, inv_pow, smul_mul_smul_comm, ← sq]
  gcongr
  exact sum_mul_sq_le_sq_mul_sq ..

end LinearOrderedCommSemiring
end Finset

open Finset

namespace Fintype
variable [Fintype ι]

section OrderedAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module Rat>=0 α] {f : ι -> α}

/--
lemma `expect_eq_zero_iff_of_nonneg` / 引理 `expect_eq_zero_iff_of_nonneg`

English:
lemma expect_eq_zero_iff_of_nonneg
  given: (hf : 0 <= f)
  statement: 𝔼 i, f i = 0 ↔ f = 0
  proof: by
  rw [Finset.expect_eq_zero_iff_of_nonneg (by aesop)]
  aesop

中文:
引理 expect_eq_zero_iff_of_nonneg
  条件: (hf : 0 <= f)
  结论: 𝔼 i, f i = 0 ↔ f = 0
  证明: by
  rw [Finset.expect_eq_zero_iff_of_nonneg (by aesop)]
  aesop

Depends on / 依赖: Finset, Finset.expect_eq_zero_iff_of_nonneg, expect_eq_zero_iff_of_nonneg
-/
lemma expect_eq_zero_iff_of_nonneg (hf : 0 <= f) : 𝔼 i, f i = 0 ↔ f = 0 := by
  rw [Finset.expect_eq_zero_iff_of_nonneg (by aesop)]
  aesop

/--
lemma `expect_eq_zero_iff_of_nonpos` / 引理 `expect_eq_zero_iff_of_nonpos`

English:
lemma expect_eq_zero_iff_of_nonpos
  given: (hf : f <= 0)
  statement: 𝔼 i, f i = 0 ↔ f = 0
  proof: by
  rw [Finset.expect_eq_zero_iff_of_nonpos (by aesop)]
  aesop

中文:
引理 expect_eq_zero_iff_of_nonpos
  条件: (hf : f <= 0)
  结论: 𝔼 i, f i = 0 ↔ f = 0
  证明: by
  rw [Finset.expect_eq_zero_iff_of_nonpos (by aesop)]
  aesop

Depends on / 依赖: Finset, Finset.expect_eq_zero_iff_of_nonpos, expect_eq_zero_iff_of_nonpos
-/
lemma expect_eq_zero_iff_of_nonpos (hf : f <= 0) : 𝔼 i, f i = 0 ↔ f = 0 := by
  rw [Finset.expect_eq_zero_iff_of_nonpos (by aesop)]
  aesop

end OrderedAddCommMonoid
end Fintype

open Finset

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset
open scoped BigOperators

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for `Finset.expect`. -/
@[positivity Finset.expect _ _]
meta def evalFinsetExpect : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match e with
  | ~q(@Finset.expect $ι _ $instα $instmod $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := .betaRev f #[i]
    let rbody ← core zα pα body
    let p_pos : Option Q(0 < $e) ← do
      let .positive pbody := rbody | pure none -- Fail if the body is not provably positive
      let some ps ← proveFinsetNonempty s | pure none
      let .some pα' ← trySynthInstanceQ q(IsOrderedCancelAddMonoid $α) | pure none
      let .some instαordsmul ← trySynthInstanceQ q(PosSMulStrictMono Rat>=0 $α) | pure none
      assumeInstancesCommute
      let pr : Q(forall i, 0 < $f i) ← mkLambdaFVars #[i] pbody
pure some
        q(@expect_pos $ι $α $instα $pα $pα' $instmod $instαordsmul $s $f (fun i _ => $pr i) $ps)
    -- Try to show that the sum is positive
    if let some p_pos := p_pos then
      return .positive p_pos
    -- Fall back to showing that the sum is nonnegative
    else
      let pbody ← rbody.toNonneg
      let pr : Q(forall i, 0 <= $f i) ← mkLambdaFVars #[i] pbody
      let instαordmon ← synthInstanceQ q(IsOrderedAddMonoid $α)
      let instαordsmul ← synthInstanceQ q(PosSMulMono Rat>=0 $α)
      assumeInstancesCommute
      return .nonnegative
        q(@expect_nonneg $ι $α $instα $pα $instαordmon $instmod $s $f $instαordsmul fun i _ => $pr i)
  | _ => throwError "not Finset.expect"

example (n : Nat) (a : Nat -> Rat) : 0 <= 𝔼 j in range n, a j ^ 2 := by positivity
example (a : ULift.{2} Nat -> Rat) (s : Finset (ULift.{2} Nat)) : 0 <= 𝔼 j in s, a j ^ 2 := by positivity
example (n : Nat) (a : Nat -> Rat) : 0 <= 𝔼 j : Fin 8, 𝔼 i in range n, (a j ^ 2 + i ^ 2) := by positivity
example (n : Nat) (a : Nat -> Rat) : 0 < 𝔼 j : Fin (n + 1), (a j ^ 2 + 1) := by positivity
example (a : Nat -> Rat) : 0 < 𝔼 j in ({1} : Finset Nat), (a j ^ 2 + 1) := by positivity

end Mathlib.Meta.Positivity
