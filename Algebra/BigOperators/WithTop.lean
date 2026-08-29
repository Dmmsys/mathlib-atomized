/-
Copyright (c) 2024 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Sums in `WithTop`

This file proves results about finite sums over monoids extended by a bottom or top element.
-/

public section

open Finset

variable {ι M M₀ : Type*}

namespace WithTop
section AddCommMonoid
variable [AddCommMonoid M] {s : Finset ι} {f : ι -> WithTop M}

/--
lemma `coe_sum` / 引理 `coe_sum`

English:
lemma coe_sum
  given: (s : Finset ι) (f : ι -> M)
  proof: map_sum addHom f s

中文:
引理 coe_sum
  条件: (s : Finset ι) (f : ι -> M)
  证明: map_sum addHom f s
-/
@[simp, norm_cast] lemma coe_sum (s : Finset ι) (f : ι -> M) :
    ∑ i in s, f i = ∑ i in s, (f i : WithTop M) := map_sum addHom f s

/--
lemma `sum_eq_top` / 引理 `sum_eq_top`

English:
lemma sum_eq_top
  statement: ∑ i in s, f i = ⊤ ↔ exists i in s, f i = ⊤
  proof: by
  induction s using Finset.cons_induction <;> simp [*]

中文:
引理 sum_eq_top
  结论: ∑ i in s, f i = ⊤ ↔ 存在 i in s, f i = ⊤
  证明: by
  induction s using Finset.cons_induction <;> simp [*]
-/
@[simp] lemma sum_eq_top : ∑ i in s, f i = ⊤ ↔ exists i in s, f i = ⊤ := by
  induction s using Finset.cons_induction <;> simp [*]

/--
lemma `sum_ne_top` / 引理 `sum_ne_top`

English:
lemma sum_ne_top
  statement: ∑ i in s, f i != ⊤ ↔ forall i in s, f i != ⊤
  proof: by simp

中文:
引理 sum_ne_top
  结论: ∑ i in s, f i != ⊤ ↔ 对任意 i in s, f i != ⊤
  证明: by simp
-/
lemma sum_ne_top : ∑ i in s, f i != ⊤ ↔ forall i in s, f i != ⊤ := by simp

variable [LT M]

/--
lemma `sum_lt_top` / 引理 `sum_lt_top`

English:
lemma sum_lt_top
  statement: ∑ i in s, f i < ⊤ ↔ forall i in s, f i < ⊤
  proof: by
  simp [WithTop.lt_top_iff_ne_top]

中文:
引理 sum_lt_top
  结论: ∑ i in s, f i < ⊤ ↔ 对任意 i in s, f i < ⊤
  证明: by
  simp [WithTop.lt_top_iff_ne_top]
-/
@[simp] lemma sum_lt_top : ∑ i in s, f i < ⊤ ↔ forall i in s, f i < ⊤ := by
  simp [WithTop.lt_top_iff_ne_top]

end AddCommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι -> WithTop M₀} {i : ι}

/--
lemma `prod_ne_top` / 引理 `prod_ne_top`

English:
lemma prod_ne_top
  given: (h : forall i in s, f i != ⊤)
  statement: ∏ i in s, f i != ⊤
  proof: prod_induction f (· != ⊤) (fun _ _ => mul_ne_top) coe_ne_top h

中文:
引理 prod_ne_top
  条件: (h : 对任意 i in s, f i != ⊤)
  结论: ∏ i in s, f i != ⊤
  证明: prod_induction f (· != ⊤) (fun _ _ => mul_ne_top) coe_ne_top h

Depends on / 依赖: coe_ne_top, mul_ne_top, prod_induction
-/
lemma prod_ne_top (h : forall i in s, f i != ⊤) : ∏ i in s, f i != ⊤ :=
  prod_induction f (· != ⊤) (fun _ _ => mul_ne_top) coe_ne_top h

/--
lemma `prod_lt_top` / 引理 `prod_lt_top`

English:
lemma prod_lt_top
  given: [LT M₀] (h : forall i in s, f i < ⊤)
  statement: ∏ i in s, f i < ⊤
  proof: prod_induction f (· < ⊤) (fun _ _ => mul_lt_top) (coe_lt_top _) h

中文:
引理 prod_lt_top
  条件: [LT M₀] (h : 对任意 i in s, f i < ⊤)
  结论: ∏ i in s, f i < ⊤
  证明: prod_induction f (· < ⊤) (fun _ _ => mul_lt_top) (coe_lt_top _) h

Depends on / 依赖: coe_lt_top, mul_lt_top, prod_induction
-/
lemma prod_lt_top [LT M₀] (h : forall i in s, f i < ⊤) : ∏ i in s, f i < ⊤ :=
  prod_induction f (· < ⊤) (fun _ _ => mul_lt_top) (coe_lt_top _) h

/--
lemma `prod_eq_top` / 引理 `prod_eq_top`

English:
lemma prod_eq_top
  given: (hi : i in s) (hi' : f i = ⊤) (h : forall j in s, f j != 0)
  proof: by
  classical rw [← prod_erase_mul _ _ hi]
  refine WithTop.mul_eq_top_iff.mpr (Or.inl ⟨?_, hi'⟩)
  refine prod_ne_zero_iff.mpr ?_
  intros
  simp_all only [ne_eq, mem_erase, not_false_eq_true]

中文:
引理 prod_eq_top
  条件: (hi : i in s) (hi' : f i = ⊤) (h : 对任意 j in s, f j != 0)
  证明: by
  classical rw [← prod_erase_mul _ _ hi]
  refine WithTop.mul_eq_top_iff.mpr (Or.inl ⟨?_, hi'⟩)
  refine prod_ne_zero_iff.mpr ?_
  intros
  simp_all only [ne_eq, mem_erase, not_false_eq_true]

Depends on / 依赖: Or.inl, WithTop, WithTop.mul_eq_top_iff.mpr, classical, intros, mem_erase, mul_eq_top_iff, ne_eq, not_false_eq_true, prod_erase_mul, prod_ne_zero_iff, prod_ne_zero_iff.mpr
-/
lemma prod_eq_top (hi : i in s) (hi' : f i = ⊤) (h : forall j in s, f j != 0) :
    ∏ j in s, f j = ⊤ := by
  classical rw [← prod_erase_mul _ _ hi]
  refine WithTop.mul_eq_top_iff.mpr (Or.inl ⟨?_, hi'⟩)
  refine prod_ne_zero_iff.mpr ?_
  intros
  simp_all only [ne_eq, mem_erase, not_false_eq_true]

/--
lemma `prod_eq_top_ne_zero` / 引理 `prod_eq_top_ne_zero`

English:
lemma prod_eq_top_ne_zero
  given: (hi : i in s) (h : ∏ j in s, f j = ⊤)
  statement: f i != 0
  proof: by
  by_contra! h0
  apply WithTop.top_ne_zero (α := M₀)
  calc
    ⊤ = ∏ j in s, f j := Eq.symm h
    _ = 0 := prod_eq_zero hi h0

中文:
引理 prod_eq_top_ne_zero
  条件: (hi : i in s) (h : ∏ j in s, f j = ⊤)
  结论: f i != 0
  证明: by
  by_contra! h0
  apply WithTop.top_ne_zero (α := M₀)
  calc
    ⊤ = ∏ j in s, f j := Eq.symm h
    _ = 0 := prod_eq_zero hi h0

Depends on / 依赖: Eq.symm, WithTop, WithTop.top_ne_zero, prod_eq_zero, top_ne_zero
-/
lemma prod_eq_top_ne_zero (hi : i in s) (h : ∏ j in s, f j = ⊤) : f i != 0 := by
  by_contra! h0
  apply WithTop.top_ne_zero (α := M₀)
  calc
    ⊤ = ∏ j in s, f j := Eq.symm h
    _ = 0 := prod_eq_zero hi h0

/--
lemma `prod_eq_top_ex_top` / 引理 `prod_eq_top_ex_top`

English:
lemma prod_eq_top_ex_top
  given: (h : ∏ j in s, f j = ⊤)
  statement: exists i in s, f i = ⊤
  proof: by
  contrapose! h
  exact WithTop.prod_ne_top h

中文:
引理 prod_eq_top_ex_top
  条件: (h : ∏ j in s, f j = ⊤)
  结论: 存在 i in s, f i = ⊤
  证明: by
  contrapose! h
  exact WithTop.prod_ne_top h

Depends on / 依赖: WithTop, WithTop.prod_ne_top, contrapose, prod_ne_top
-/
lemma prod_eq_top_ex_top (h : ∏ j in s, f j = ⊤) : exists i in s, f i = ⊤ := by
  contrapose! h
  exact WithTop.prod_ne_top h

/--
lemma `prod_eq_top_iff` / 引理 `prod_eq_top_iff`

English:
lemma prod_eq_top_iff
  statement: ∏ j in s, f j = ⊤ ↔ (exists i in s, f i = ⊤) ∧ (forall i in s, f i != 0)
  proof: by
  constructor
  · exact fun h => ⟨prod_eq_top_ex_top h, fun _ ih => prod_eq_top_ne_zero ih h⟩
  · exact fun ⟨h, h'⟩ => prod_eq_top (Exists.choose_spec h).1 (Exists.choose_spec h).2 h'

中文:
引理 prod_eq_top_iff
  结论: ∏ j in s, f j = ⊤ ↔ (存在 i in s, f i = ⊤) ∧ (对任意 i in s, f i != 0)
  证明: by
  constructor
  · exact fun h => ⟨prod_eq_top_ex_top h, fun _ ih => prod_eq_top_ne_zero ih h⟩
  · exact fun ⟨h, h'⟩ => prod_eq_top (Exists.choose_spec h).1 (Exists.choose_spec h).2 h'

Depends on / 依赖: Exists, Exists.choose_spec, choose_spec, prod_eq_top, prod_eq_top_ex_top, prod_eq_top_ne_zero
-/
lemma prod_eq_top_iff : ∏ j in s, f j = ⊤ ↔ (exists i in s, f i = ⊤) ∧ (forall i in s, f i != 0) := by
  constructor
  · exact fun h => ⟨prod_eq_top_ex_top h, fun _ ih => prod_eq_top_ne_zero ih h⟩
  · exact fun ⟨h, h'⟩ => prod_eq_top (Exists.choose_spec h).1 (Exists.choose_spec h).2 h'

end CommMonoidWithZero
end WithTop

namespace WithBot
section AddCommMonoid
variable [AddCommMonoid M] {s : Finset ι} {f : ι -> WithBot M}

/--
lemma `coe_sum` / 引理 `coe_sum`

English:
lemma coe_sum
  given: (s : Finset ι) (f : ι -> M)
  proof: map_sum addHom f s

中文:
引理 coe_sum
  条件: (s : Finset ι) (f : ι -> M)
  证明: map_sum addHom f s
-/
@[simp, norm_cast] lemma coe_sum (s : Finset ι) (f : ι -> M) :
    ∑ i in s, f i = ∑ i in s, (f i : WithBot M) := map_sum addHom f s

/--
lemma `sum_eq_bot_iff` / 引理 `sum_eq_bot_iff`

English:
lemma sum_eq_bot_iff
  statement: ∑ i in s, f i = ⊥ ↔ exists i in s, f i = ⊥
  proof: by
  induction s using Finset.cons_induction <;> simp [*]

中文:
引理 sum_eq_bot_iff
  结论: ∑ i in s, f i = ⊥ ↔ 存在 i in s, f i = ⊥
  证明: by
  induction s using Finset.cons_induction <;> simp [*]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
lemma sum_eq_bot_iff : ∑ i in s, f i = ⊥ ↔ exists i in s, f i = ⊥ := by
  induction s using Finset.cons_induction <;> simp [*]

variable [LT M]

/--
lemma `bot_lt_sum_iff` / 引理 `bot_lt_sum_iff`

English:
lemma bot_lt_sum_iff
  statement: ⊥ < ∑ i in s, f i ↔ forall i in s, ⊥ < f i
  proof: by
  simp only [WithBot.bot_lt_iff_ne_bot, ne_eq, sum_eq_bot_iff, not_exists, not_and]

中文:
引理 bot_lt_sum_iff
  结论: ⊥ < ∑ i in s, f i ↔ 对任意 i in s, ⊥ < f i
  证明: by
  simp only [WithBot.bot_lt_iff_ne_bot, ne_eq, sum_eq_bot_iff, not_exists, not_and]

Depends on / 依赖: WithBot, WithBot.bot_lt_iff_ne_bot, bot_lt_iff_ne_bot, ne_eq, not_and, not_exists, sum_eq_bot_iff
-/
lemma bot_lt_sum_iff : ⊥ < ∑ i in s, f i ↔ forall i in s, ⊥ < f i := by
  simp only [WithBot.bot_lt_iff_ne_bot, ne_eq, sum_eq_bot_iff, not_exists, not_and]

/--
lemma `sum_lt_bot` / 引理 `sum_lt_bot`

English:
lemma sum_lt_bot
  given: (h : forall i in s, f i != ⊥)
  statement: ⊥ < ∑ i in s, f i
  proof: bot_lt_sum_iff.2 fun i hi => WithBot.bot_lt_iff_ne_bot.2 (h i hi)

中文:
引理 sum_lt_bot
  条件: (h : 对任意 i in s, f i != ⊥)
  结论: ⊥ < ∑ i in s, f i
  证明: bot_lt_sum_iff.2 fun i hi => WithBot.bot_lt_iff_ne_bot.2 (h i hi)

Depends on / 依赖: WithBot, WithBot.bot_lt_iff_ne_bot, bot_lt_iff_ne_bot, bot_lt_sum_iff
-/
lemma sum_lt_bot (h : forall i in s, f i != ⊥) : ⊥ < ∑ i in s, f i :=
  bot_lt_sum_iff.2 fun i hi => WithBot.bot_lt_iff_ne_bot.2 (h i hi)

end AddCommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι -> WithBot M₀}

/--
lemma `prod_ne_bot` / 引理 `prod_ne_bot`

English:
lemma prod_ne_bot
  given: (h : forall i in s, f i != ⊥)
  statement: ∏ i in s, f i != ⊥
  proof: prod_induction f (· != ⊥) (fun _ _ => mul_ne_bot) coe_ne_bot h

中文:
引理 prod_ne_bot
  条件: (h : 对任意 i in s, f i != ⊥)
  结论: ∏ i in s, f i != ⊥
  证明: prod_induction f (· != ⊥) (fun _ _ => mul_ne_bot) coe_ne_bot h

Depends on / 依赖: coe_ne_bot, mul_ne_bot, prod_induction
-/
lemma prod_ne_bot (h : forall i in s, f i != ⊥) : ∏ i in s, f i != ⊥ :=
  prod_induction f (· != ⊥) (fun _ _ => mul_ne_bot) coe_ne_bot h

/--
lemma `bot_lt_prod` / 引理 `bot_lt_prod`

English:
lemma bot_lt_prod
  given: [LT M₀] (h : forall i in s, ⊥ < f i)
  statement: ⊥ < ∏ i in s, f i
  proof: prod_induction f (⊥ < ·) (fun _ _ => bot_lt_mul) (bot_lt_coe _) h

中文:
引理 bot_lt_prod
  条件: [LT M₀] (h : 对任意 i in s, ⊥ < f i)
  结论: ⊥ < ∏ i in s, f i
  证明: prod_induction f (⊥ < ·) (fun _ _ => bot_lt_mul) (bot_lt_coe _) h

Depends on / 依赖: bot_lt_coe, bot_lt_mul, prod_induction
-/
lemma bot_lt_prod [LT M₀] (h : forall i in s, ⊥ < f i) : ⊥ < ∏ i in s, f i :=
  prod_induction f (⊥ < ·) (fun _ _ => bot_lt_mul) (bot_lt_coe _) h

end CommMonoidWithZero

end WithBot
