/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.SuccPred.InitialSeg
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Ordinal arithmetic

Ordinals have an addition (corresponding to the disjoint union) that turns them into an additive
monoid, and a multiplication (corresponding to the lexicographic order on the product) that turns
them into a monoid. One can also define (truncated) subtraction and division operators.

Ordinal powers and logarithms are defined in `Mathlib.SetTheory.Ordinal.Exponential`.

## Main definitions and results

* `a + b` is the order type of the lexicographic sum `a ⊕ₗ b`.
* `a - b` is the unique ordinal `c` such that `b + c = a`, when `b ≤ a`.
* `a * b` is the order type of the lexicographic product `b ×ₗ a`.
* `a / b` is the ordinal `q` such that `a = b * q + r` with `r < b`. We also define the
  divisibility predicate, and a modulo operation.
* `limitRecOn` is limit recursion on ordinals, i.e. well-founded recursion separating out the zero,
  successor, and limit cases.

We discuss the properties of casts of natural numbers of and of `ω` with respect to these
operations.

Note that some basic functions and properties of ordinals have been generalized to other orders, and
exist on other files:

* `Order.succ o = o + 1` is the successor of `o`.
* `Order.IsSuccLimit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `Order.IsNormal`: a function `f : Ordinal → Ordinal` is normal if it is strictly increasing and
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the supremum of `f a`
  for `a < o`.

Various other basic arithmetic results are given in `Principal.lean` instead.
-/

@[expose] public noncomputable section

assert_not_exists Field Module

open Function Cardinal Set Equiv Order

universe u v w

namespace Ordinal

variable {α β γ : Type*} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop}

/-! ### Further properties of addition on ordinals -/

@[simp]
/--
theorem `lift_add` / 定理 `lift_add`

English:
theorem lift_add
  given: (a b : Ordinal.{v})
  statement: lift.{u} (a + b) = lift.{u} a + lift.{u} b
  proof: Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.sumLexCongr (RelIso.preimage Equiv.ulift _) (RelIso.preimage Equiv.ulift _)).symm⟩

中文:
定理 lift_add
  条件: (a b : 序数.{v})
  结论: lift.{u} (a + b) = lift.{u} a + lift.{u} b
  证明: Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.sumLexCongr (RelIso.preimage Equiv.ulift _) (RelIso.preimage Equiv.ulift _)).symm⟩

Depends on / 依赖: Equiv.ulift, Quotient, Quotient.inductionOn, Quotient.sound, RelIso, RelIso.preimage, RelIso.sumLexCongr, preimage, sumLexCongr
-/
theorem lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift.{u} a + lift.{u} b :=
  Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.sumLexCongr (RelIso.preimage Equiv.ulift _) (RelIso.preimage Equiv.ulift _)).symm⟩

/--
theorem `lift_add_one` / 定理 `lift_add_one`

English:
theorem lift_add_one
  given: (a : Ordinal.{v})
  statement: lift.{u} (a + 1) = lift.{u} a + 1
  proof: by
  simp

中文:
定理 lift_add_one
  条件: (a : 序数.{v})
  结论: lift.{u} (a + 1) = lift.{u} a + 1
  证明: by
  simp
-/
theorem lift_add_one (a : Ordinal.{v}) : lift.{u} (a + 1) = lift.{u} a + 1 := by
  simp

-- TODO: deprecate
/--
theorem `lift_succ` / 定理 `lift_succ`

English:
theorem lift_succ
  given: (a : Ordinal.{v})
  statement: lift.{u} (succ a) = succ (lift.{u} a)
  proof: lift_add_one a

中文:
定理 lift_succ
  条件: (a : 序数.{v})
  结论: lift.{u} (succ a) = succ (lift.{u} a)
  证明: lift_add_one a

Depends on / 依赖: lift_add_one
-/
theorem lift_succ (a : Ordinal.{v}) : lift.{u} (succ a) = succ (lift.{u} a) :=
  lift_add_one a

/--
Instance `instAddLeftReflectLE` / 实例 `instAddLeftReflectLE`

English:
instance instAddLeftReflectLE
  signature: : AddLeftReflectLE Ordinal.{u} where
  body: by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ => ?_
    have H₁ a : f (Sum.inl a) = Sum.inl a := by
      simpa using ((InitialSeg.leAdd t r).trans f).eq (InitialSeg.leAdd t s) a
    have H₂ a : exists b, f (Sum.inr a) = Sum.inr b := by
      generalize hx : f (Sum.inr a) = x
      obtain x | x := x
      · rw [← H₁, f.inj] at hx
        contradiction
      · exact ⟨x, rfl⟩
    choose g hg using H₂
    refine (RelEmbedding.ofMonotone g fun _ _ h => ?_).ordinal_type_le
    rwa [← @Sum.lex_inr_inr _ t _ s, ← hg, ← hg, f.map_rel_iff, Sum.lex_inr_inr]

中文:
实例 instAddLeftReflectLE
  签名: : 加法LeftReflectLE 序数.{u} where
  定义体: by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ => ?_
    have H₁ a : f (Sum.inl a) = Sum.inl a := by
      simpa using ((InitialSeg.leAdd t r).trans f).eq (InitialSeg.leAdd t s) a
    have H₂ a : exists b, f (Sum.inr a) = Sum.inr b := by
      generalize hx : f (Sum.inr a) = x
      obtain x | x := x
      · rw [← H₁, f.inj] at hx
        contradiction
      · exact ⟨x, rfl⟩
    choose g hg using H₂
    refine (RelEmbedding.ofMonotone g fun _ _ h => ?_).ordinal_type_le
    rwa [← @Sum.lex_inr_inr _ t _ s, ← hg, ← hg, f.map_rel_iff, Sum.lex_inr_inr]

Depends on / 依赖: InitialSeg, InitialSeg.leAdd, RelEmbedding, RelEmbedding.ofMonotone, Sum.inl, Sum.inr, Sum.lex_inr_, Sum.lex_inr_inr, f.inj, f.map_rel_iff, generalize, lex_inr_, lex_inr_inr, map_rel_iff, ofMonotone, ordinal_type_le
-/
instance instAddLeftReflectLE : AddLeftReflectLE Ordinal.{u} where
  le_of_add_le_add_left {c a b} := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ => ?_
    have H₁ a : f (Sum.inl a) = Sum.inl a := by
      simpa using ((InitialSeg.leAdd t r).trans f).eq (InitialSeg.leAdd t s) a
    have H₂ a : exists b, f (Sum.inr a) = Sum.inr b := by
      generalize hx : f (Sum.inr a) = x
      obtain x | x := x
      · rw [← H₁, f.inj] at hx
        contradiction
      · exact ⟨x, rfl⟩
    choose g hg using H₂
    refine (RelEmbedding.ofMonotone g fun _ _ h => ?_).ordinal_type_le
    rwa [← @Sum.lex_inr_inr _ t _ s, ← hg, ← hg, f.map_rel_iff, Sum.lex_inr_inr]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLeftCancelAdd Ordinal
  body: by simpa only [le_antisymm_iff, add_le_add_iff_left] using h

中文:
实例 :
  签名: 是左消去加法 序数
  定义体: by simpa only [le_antisymm_iff, add_le_add_iff_left] using h

Depends on / 依赖: add_le_add_iff_left, le_antisymm_iff
-/
instance : IsLeftCancelAdd Ordinal where
  add_left_cancel a b c h := by simpa only [le_antisymm_iff, add_le_add_iff_left] using h

/--
theorem `add_lt_add_iff_left'` / 定理 `add_lt_add_iff_left'`

English:
theorem add_lt_add_iff_left'
  given: (a) {b c : Ordinal}
  statement: a + b < a + c ↔ b < c
  proof: by
  rw [← not_le]; rw [← not_le]; rw [add_le_add_iff_left]

中文:
定理 add_lt_add_iff_left'
  条件: (a) {b c : 序数}
  结论: a + b < a + c ↔ b < c
  证明: by
  rw [← not_le]; rw [← not_le]; rw [add_le_add_iff_left]
-/
private theorem add_lt_add_iff_left' (a) {b c : Ordinal} : a + b < a + c ↔ b < c := by
  rw [← not_le]; rw [← not_le]; rw [add_le_add_iff_left]

/--
Instance `instAddLeftStrictMono` / 实例 `instAddLeftStrictMono`

English:
instance instAddLeftStrictMono
  signature: : AddLeftStrictMono Ordinal.{u}
  body: ⟨fun a _b _c => (add_lt_add_iff_left' a).2⟩

中文:
实例 instAddLeftStrictMono
  签名: : AddLeftStrictMono 序数.{u}
  定义体: ⟨fun a _b _c => (add_lt_add_iff_left' a).2⟩

Depends on / 依赖: add_lt_add_iff_left
-/
instance instAddLeftStrictMono : AddLeftStrictMono Ordinal.{u} :=
  ⟨fun a _b _c => (add_lt_add_iff_left' a).2⟩

/--
Instance `instAddLeftReflectLT` / 实例 `instAddLeftReflectLT`

English:
instance instAddLeftReflectLT
  signature: : AddLeftReflectLT Ordinal.{u}
  body: ⟨fun a _b _c => (add_lt_add_iff_left' a).1⟩

中文:
实例 instAddLeftReflectLT
  签名: : AddLeftReflectLT 序数.{u}
  定义体: ⟨fun a _b _c => (add_lt_add_iff_left' a).1⟩

Depends on / 依赖: add_lt_add_iff_left
-/
instance instAddLeftReflectLT : AddLeftReflectLT Ordinal.{u} :=
  ⟨fun a _b _c => (add_lt_add_iff_left' a).1⟩

/--
Instance `instAddRightReflectLT` / 实例 `instAddRightReflectLT`

English:
instance instAddRightReflectLT
  signature: : AddRightReflectLT Ordinal.{u}
  body: ⟨fun _a _b _c => lt_imp_lt_of_le_imp_le fun h => add_le_add_left h _⟩

中文:
实例 instAddRightReflectLT
  签名: : AddRightReflectLT 序数.{u}
  定义体: ⟨fun _a _b _c => lt_imp_lt_of_le_imp_le fun h => add_le_add_left h _⟩

Depends on / 依赖: add_le_add_left, lt_imp_lt_of_le_imp_le
-/
instance instAddRightReflectLT : AddRightReflectLT Ordinal.{u} :=
  ⟨fun _a _b _c => lt_imp_lt_of_le_imp_le fun h => add_le_add_left h _⟩

/--
theorem `add_le_add_iff_right` / 定理 `add_le_add_iff_right`

English:
theorem add_le_add_iff_right
  given: {a b : Ordinal}
  statement: forall n : Nat, a + n <= b + n ↔ a <= b

中文:
定理 add_le_add_iff_right
  条件: {a b : 序数}
  结论: 对任意 n : 自然数, a + n <= b + n ↔ a <= b
-/
theorem add_le_add_iff_right {a b : Ordinal} : forall n : Nat, a + n <= b + n ↔ a <= b
  | 0 => by simp
  | n + 1 => by simpa [← add_assoc] using add_le_add_iff_right n

/--
theorem `add_right_cancel` / 定理 `add_right_cancel`

English:
theorem add_right_cancel
  given: {a b : Ordinal} (n : Nat)
  statement: a + n = b + n ↔ a = b
  proof: by
  simp only [le_antisymm_iff, add_le_add_iff_right]

@[simp]

中文:
定理 add_right_cancel
  条件: {a b : 序数} (n : 自然数)
  结论: a + n = b + n ↔ a = b
  证明: by
  simp only [le_antisymm_iff, add_le_add_iff_right]

@[simp]

Depends on / 依赖: add_le_add_iff_right, le_antisymm_iff
-/
theorem add_right_cancel {a b : Ordinal} (n : Nat) : a + n = b + n ↔ a = b := by
  simp only [le_antisymm_iff, add_le_add_iff_right]

@[simp]
/--
theorem `add_eq_zero_iff` / 定理 `add_eq_zero_iff`

English:
theorem add_eq_zero_iff
  given: {a b : Ordinal}
  statement: a + b = 0 ↔ a = 0 ∧ b = 0
  proof: inductionOn₂ a b fun α r _ β s _ => by
    simp_rw [← type_sum_lex, type_eq_zero_iff_isEmpty]
    exact isEmpty_sum

中文:
定理 add_eq_zero_iff
  条件: {a b : 序数}
  结论: a + b = 0 ↔ a = 0 ∧ b = 0
  证明: inductionOn₂ a b fun α r _ β s _ => by
    simp_rw [← type_sum_lex, type_eq_zero_iff_isEmpty]
    exact isEmpty_sum

Depends on / 依赖: isEmpty_sum, simp_rw, type_eq_zero_iff_isEmpty, type_sum_lex
-/
theorem add_eq_zero_iff {a b : Ordinal} : a + b = 0 ↔ a = 0 ∧ b = 0 :=
  inductionOn₂ a b fun α r _ β s _ => by
    simp_rw [← type_sum_lex, type_eq_zero_iff_isEmpty]
    exact isEmpty_sum

/--
theorem `left_eq_zero_of_add_eq_zero` / 定理 `left_eq_zero_of_add_eq_zero`

English:
theorem left_eq_zero_of_add_eq_zero
  given: {a b : Ordinal} (h : a + b = 0)
  statement: a = 0
  proof: (add_eq_zero_iff.1 h).1

中文:
定理 left_eq_zero_of_add_eq_zero
  条件: {a b : 序数} (h : a + b = 0)
  结论: a = 0
  证明: (add_eq_zero_iff.1 h).1

Depends on / 依赖: add_eq_zero_iff
-/
theorem left_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : a = 0 :=
  (add_eq_zero_iff.1 h).1

/--
theorem `right_eq_zero_of_add_eq_zero` / 定理 `right_eq_zero_of_add_eq_zero`

English:
theorem right_eq_zero_of_add_eq_zero
  given: {a b : Ordinal} (h : a + b = 0)
  statement: b = 0
  proof: (add_eq_zero_iff.1 h).2

中文:
定理 right_eq_zero_of_add_eq_zero
  条件: {a b : 序数} (h : a + b = 0)
  结论: b = 0
  证明: (add_eq_zero_iff.1 h).2

Depends on / 依赖: add_eq_zero_iff
-/
theorem right_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : b = 0 :=
  (add_eq_zero_iff.1 h).2


/--
theorem `isSuccLimit_iff` / 定理 `isSuccLimit_iff`

English:
theorem isSuccLimit_iff
  given: {o : Ordinal}
  statement: IsSuccLimit o ↔ o != 0 ∧ IsSuccPrelimit o
  proof: isSuccLimit_iff_of_orderBot

@[simp]

中文:
定理 isSuccLimit_iff
  条件: {o : 序数}
  结论: 是SuccLimit o ↔ o != 0 ∧ IsSuccPrelimit o
  证明: isSuccLimit_iff_of_orderBot

@[simp]

Depends on / 依赖: isSuccLimit_iff_of_orderBot
-/
theorem isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔ o != 0 ∧ IsSuccPrelimit o :=
  isSuccLimit_iff_of_orderBot

@[simp]
/--
theorem `isSuccPrelimit_zero` / 定理 `isSuccPrelimit_zero`

English:
theorem isSuccPrelimit_zero
  statement: IsSuccPrelimit (0 : Ordinal)
  proof: isSuccPrelimit_bot

@[simp]

中文:
定理 isSuccPrelimit_zero
  结论: IsSuccPrelimit (0 : 序数)
  证明: isSuccPrelimit_bot

@[simp]

Depends on / 依赖: isSuccPrelimit_bot
-/
theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Ordinal) := isSuccPrelimit_bot

@[simp]
/--
theorem `not_isSuccLimit_zero` / 定理 `not_isSuccLimit_zero`

English:
theorem not_isSuccLimit_zero
  statement: ¬ IsSuccLimit (0 : Ordinal)
  proof: not_isSuccLimit_bot

@[simp]

中文:
定理 not_isSuccLimit_zero
  结论: ¬ 是SuccLimit (0 : 序数)
  证明: not_isSuccLimit_bot

@[simp]

Depends on / 依赖: not_isSuccLimit_bot
-/
theorem not_isSuccLimit_zero : ¬ IsSuccLimit (0 : Ordinal) := not_isSuccLimit_bot

@[simp]
/--
theorem `isSuccPrelimit_lift` / 定理 `isSuccPrelimit_lift`

English:
theorem isSuccPrelimit_lift
  given: {o : Ordinal}
  statement: IsSuccPrelimit (lift.{u, v} o) ↔ IsSuccPrelimit o
  proof: liftInitialSeg.isSuccPrelimit_apply_iff

@[simp]

中文:
定理 isSuccPrelimit_lift
  条件: {o : 序数}
  结论: IsSuccPrelimit (lift.{u, v} o) ↔ IsSuccPrelimit o
  证明: liftInitialSeg.isSuccPrelimit_apply_iff

@[simp]

Depends on / 依赖: isSuccPrelimit_apply_iff, liftInitialSeg, liftInitialSeg.isSuccPrelimit_apply_iff
-/
theorem isSuccPrelimit_lift {o : Ordinal} : IsSuccPrelimit (lift.{u, v} o) ↔ IsSuccPrelimit o :=
  liftInitialSeg.isSuccPrelimit_apply_iff

@[simp]
/--
theorem `isSuccLimit_lift` / 定理 `isSuccLimit_lift`

English:
theorem isSuccLimit_lift
  given: {o : Ordinal}
  statement: IsSuccLimit (lift.{u, v} o) ↔ IsSuccLimit o
  proof: liftInitialSeg.isSuccLimit_apply_iff

中文:
定理 isSuccLimit_lift
  条件: {o : 序数}
  结论: 是SuccLimit (lift.{u, v} o) ↔ 是SuccLimit o
  证明: liftInitialSeg.isSuccLimit_apply_iff

Depends on / 依赖: isSuccLimit_apply_iff, liftInitialSeg, liftInitialSeg.isSuccLimit_apply_iff
-/
theorem isSuccLimit_lift {o : Ordinal} : IsSuccLimit (lift.{u, v} o) ↔ IsSuccLimit o :=
  liftInitialSeg.isSuccLimit_apply_iff

/--
theorem `natCast_lt_of_isSuccLimit` / 定理 `natCast_lt_of_isSuccLimit`

English:
theorem natCast_lt_of_isSuccLimit
  given: {o : Ordinal} (h : IsSuccLimit o) (n : Nat)
  statement: n < o
  proof: by
  simpa using h.add_natCast_lt h.bot_lt n

中文:
定理 natCast_lt_of_isSuccLimit
  条件: {o : 序数} (h : 是SuccLimit o) (n : 自然数)
  结论: n < o
  证明: by
  simpa using h.add_natCast_lt h.bot_lt n

Depends on / 依赖: add_natCast_lt, bot_lt, h.add_natCast_lt, h.bot_lt
-/
theorem natCast_lt_of_isSuccLimit {o : Ordinal} (h : IsSuccLimit o) (n : Nat) : n < o := by
  simpa using h.add_natCast_lt h.bot_lt n

/--
theorem `one_lt_of_isSuccLimit` / 定理 `one_lt_of_isSuccLimit`

English:
theorem one_lt_of_isSuccLimit
  given: {o : Ordinal} (h : IsSuccLimit o)
  statement: 1 < o
  proof: mod_cast natCast_lt_of_isSuccLimit h 1

中文:
定理 one_lt_of_isSuccLimit
  条件: {o : 序数} (h : 是SuccLimit o)
  结论: 1 < o
  证明: mod_cast natCast_lt_of_isSuccLimit h 1

Depends on / 依赖: mod_cast, natCast_lt_of_isSuccLimit
-/
theorem one_lt_of_isSuccLimit {o : Ordinal} (h : IsSuccLimit o) : 1 < o :=
  mod_cast natCast_lt_of_isSuccLimit h 1

/--
theorem `zero_or_succ_or_isSuccLimit` / 定理 `zero_or_succ_or_isSuccLimit`

English:
theorem zero_or_succ_or_isSuccLimit
  given: (o : Ordinal)
  statement: o = 0 ∨ o in range succ ∨ IsSuccLimit o
  proof: by
  simpa using isMin_or_mem_range_succ_or_isSuccLimit o

中文:
定理 zero_or_succ_or_isSuccLimit
  条件: (o : 序数)
  结论: o = 0 ∨ o in range succ ∨ 是SuccLimit o
  证明: by
  simpa using isMin_or_mem_range_succ_or_isSuccLimit o

Depends on / 依赖: isMin_or_mem_range_succ_or_isSuccLimit
-/
theorem zero_or_succ_or_isSuccLimit (o : Ordinal) : o = 0 ∨ o in range succ ∨ IsSuccLimit o := by
  simpa using isMin_or_mem_range_succ_or_isSuccLimit o

/-- Limit induction on ordinals: if one can prove a property by induction at successor ordinals and
at limit ordinals, then it holds for all ordinals.

Note that this is just a special (though sometimes convenient) case of the more general
well-founded recursion `WellFoundedLT.fix`. -/
@[elab_as_elim]
/--
Definition of `limitRecOn` / `limitRecOn` 的定义

English:
definition limitRecOn
  signature: {motive : Ordinal -> Sort*} (o : Ordinal)
  body: SuccOrder.limitRecOn o (fun _a ha => ha.eq_bot ▸ zero) (fun a _ => add_one a) limit

@[simp]

中文:
定义 limitRecOn
  签名: {motive : 序数 -> 类型层*} (o : 序数)
  定义体: SuccOrder.limitRecOn o (fun _a ha => ha.eq_bot ▸ zero) (fun a _ => add_one a) limit

@[simp]

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn, add_one, eq_bot, ha.eq_bot, limitRecOn
-/
def limitRecOn {motive : Ordinal -> Sort*} (o : Ordinal)
    (zero : motive 0) (add_one : forall o, motive o -> motive (o + 1))
    (limit : forall o, IsSuccLimit o -> (forall o' < o, motive o') -> motive o) : motive o :=
  SuccOrder.limitRecOn o (fun _a ha => ha.eq_bot ▸ zero) (fun a _ => add_one a) limit

@[simp]
/--
theorem `limitRecOn_zero` / 定理 `limitRecOn_zero`

English:
theorem limitRecOn_zero
  given: {motive} (H₁ H₂ H₃)
  statement: @limitRecOn motive 0 H₁ H₂ H₃ = H₁
  proof: SuccOrder.limitRecOn_isMin _ _ _ isMin_bot

@[simp]

中文:
定理 limitRecOn_zero
  条件: {motive} (H₁ H₂ H₃)
  结论: @limitRecOn motive 0 H₁ H₂ H₃ = H₁
  证明: SuccOrder.limitRecOn_isMin _ _ _ isMin_bot

@[simp]

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn_isMin, isMin_bot, limitRecOn_isMin
-/
theorem limitRecOn_zero {motive} (H₁ H₂ H₃) : @limitRecOn motive 0 H₁ H₂ H₃ = H₁ :=
  SuccOrder.limitRecOn_isMin _ _ _ isMin_bot

@[simp]
/--
theorem `limitRecOn_add_one` / 定理 `limitRecOn_add_one`

English:
theorem limitRecOn_add_one
  given: {motive} (o H₁ H₂ H₃)
  proof: SuccOrder.limitRecOn_succ ..

@[deprecated limitRecOn_add_one (since := "2026-05-21")]

中文:
定理 limitRecOn_add_one
  条件: {motive} (o H₁ H₂ H₃)
  证明: SuccOrder.limitRecOn_succ ..

@[deprecated limitRecOn_add_one (since := "2026-05-21")]

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn_succ, limitRecOn_succ
-/
theorem limitRecOn_add_one {motive} (o H₁ H₂ H₃) :
    @limitRecOn motive (o + 1) H₁ H₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃) :=
  SuccOrder.limitRecOn_succ ..

@[deprecated limitRecOn_add_one (since := "2026-05-21")]
/--
theorem `limitRecOn_succ` / 定理 `limitRecOn_succ`

English:
theorem limitRecOn_succ
  given: {motive} (o H₁ H₂ H₃)
  proof: limitRecOn_add_one ..

@[simp]

中文:
定理 limitRecOn_succ
  条件: {motive} (o H₁ H₂ H₃)
  证明: limitRecOn_add_one ..

@[simp]

Depends on / 依赖: limitRecOn_add_one
-/
theorem limitRecOn_succ {motive} (o H₁ H₂ H₃) :
    @limitRecOn motive (succ o) H₁ H₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃) :=
  limitRecOn_add_one ..

@[simp]
/--
theorem `limitRecOn_limit` / 定理 `limitRecOn_limit`

English:
theorem limitRecOn_limit
  given: {motive} (o H₁ H₂ H₃ h)
  proof: SuccOrder.limitRecOn_of_isSuccLimit ..

中文:
定理 limitRecOn_limit
  条件: {motive} (o H₁ H₂ H₃ h)
  证明: SuccOrder.limitRecOn_of_isSuccLimit ..

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn_of_isSuccLimit, limitRecOn_of_isSuccLimit
-/
theorem limitRecOn_limit {motive} (o H₁ H₂ H₃ h) :
    @limitRecOn motive o H₁ H₂ H₃ = H₃ o h fun x _h => @limitRecOn motive x H₁ H₂ H₃ :=
  SuccOrder.limitRecOn_of_isSuccLimit ..

/--
Instance `orderTopToTypeSucc` / 实例 `orderTopToTypeSucc`

English:
instance orderTopToTypeSucc
  signature: (o : Ordinal)
  body: @OrderTop.mk _ _ (Top.mk _) le_enum_succ

中文:
实例 orderTopToTypeSucc
  签名: (o : 序数)
  定义体: @OrderTop.mk _ _ (Top.mk _) le_enum_succ

Depends on / 依赖: OrderTop, OrderTop.mk, Top.mk, le_enum_succ
-/
instance orderTopToTypeSucc (o : Ordinal) : OrderTop (succ o).ToType :=
  @OrderTop.mk _ _ (Top.mk _) le_enum_succ

/--
theorem `enum_succ_eq_top` / 定理 `enum_succ_eq_top`

English:
theorem enum_succ_eq_top
  given: {o : Ordinal}
  proof: rfl

中文:
定理 enum_succ_eq_top
  条件: {o : 序数}
  证明: rfl

Depends on / 依赖: ToType, lt_succ, type_toType
-/
theorem enum_succ_eq_top {o : Ordinal} :
    enum (α := (succ o).ToType) (· < ·) ⟨o, type_toType _ ▸ lt_succ o⟩ = ⊤ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[deprecated isSuccPrelimit_type_lt_iff (since := "2026-04-12")]
/--
theorem `has_succ_of_type_succ_lt` / 定理 `has_succ_of_type_succ_lt`

English:
theorem has_succ_of_type_succ_lt
  statement: {α} {r : α -> α -> Prop} [wo : IsWellOrder α r]
  proof: by
  use enum r ⟨succ (typein r x), h _ (typein_lt_type r x)⟩
  convert! enum_lt_enum.mpr _
  · rw [enum_typein]
  · rw [Subtype.mk_lt_mk, lt_succ_iff]

@[deprecated isSuccPrelimit_type_lt_iff (since := "2026-04-12")]

中文:
定理 has_succ_of_type_succ_lt
  结论: {α} {r : α -> α -> 命题} [wo : 是良序 α r]
  证明: by
  use enum r ⟨succ (typein r x), h _ (typein_lt_type r x)⟩
  convert! enum_lt_enum.mpr _
  · rw [enum_typein]
  · rw [Subtype.mk_lt_mk, lt_succ_iff]

@[deprecated isSuccPrelimit_type_lt_iff (since := "2026-04-12")]

Depends on / 依赖: Subtype, Subtype.mk_lt_mk, convert, enum_lt_enum, enum_lt_enum.mpr, enum_typein, lt_succ_iff, mk_lt_mk, typein, typein_lt_type
-/
theorem has_succ_of_type_succ_lt {α} {r : α -> α -> Prop} [wo : IsWellOrder α r]
    (h : forall a < type r, succ a < type r) (x : α) : exists y, r x y := by
  use enum r ⟨succ (typein r x), h _ (typein_lt_type r x)⟩
  convert! enum_lt_enum.mpr _
  · rw [enum_typein]
  · rw [Subtype.mk_lt_mk, lt_succ_iff]

@[deprecated isSuccPrelimit_type_lt_iff (since := "2026-04-12")]
/--
theorem `toType_noMax_of_succ_lt` / 定理 `toType_noMax_of_succ_lt`

English:
theorem toType_noMax_of_succ_lt
  given: {o : Ordinal} (ho : forall a < o, succ a < o)
  statement: NoMaxOrder o.ToType
  proof: ⟨has_succ_of_type_succ_lt (type_toType _ ▸ ho)⟩

中文:
定理 toType_noMax_of_succ_lt
  条件: {o : 序数} (ho : 对任意 a < o, succ a < o)
  结论: NoMax序 o.ToType
  证明: ⟨has_succ_of_type_succ_lt (type_toType _ ▸ ho)⟩

Depends on / 依赖: has_succ_of_type_succ_lt, type_toType
-/
theorem toType_noMax_of_succ_lt {o : Ordinal} (ho : forall a < o, succ a < o) : NoMaxOrder o.ToType :=
  ⟨has_succ_of_type_succ_lt (type_toType _ ▸ ho)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `bounded_singleton` / 定理 `bounded_singleton`

English:
theorem bounded_singleton
  given: {r : α -> α -> Prop} [IsWellOrder α r] (hr : IsSuccLimit (type r)) (x)
  proof: by
  refine ⟨enum r ⟨succ (typein r x), hr.succ_lt (typein_lt_type r x)⟩, ?_⟩
  intro b hb
  rw [mem_singleton_iff.1 hb]
  nth_rw 1 [← enum_typein r x]
  rw [@enum_lt_enum _ r]; rw [Subtype.mk_lt_mk]
  apply lt_succ

中文:
定理 bounded_singleton
  条件: {r : α -> α -> 命题} [是良序 α r] (hr : 是SuccLimit (type r)) (x)
  证明: by
  refine ⟨enum r ⟨succ (typein r x), hr.succ_lt (typein_lt_type r x)⟩, ?_⟩
  intro b hb
  rw [mem_singleton_iff.1 hb]
  nth_rw 1 [← enum_typein r x]
  rw [@enum_lt_enum _ r]; rw [Subtype.mk_lt_mk]
  apply lt_succ

Depends on / 依赖: Subtype, Subtype.mk_lt_mk, enum_lt_enum, enum_typein, hr.succ_lt, lt_succ, mem_singleton_iff, mk_lt_mk, nth_rw, succ_lt, typein, typein_lt_type
-/
theorem bounded_singleton {r : α -> α -> Prop} [IsWellOrder α r] (hr : IsSuccLimit (type r)) (x) :
    Bounded r {x} := by
  refine ⟨enum r ⟨succ (typein r x), hr.succ_lt (typein_lt_type r x)⟩, ?_⟩
  intro b hb
  rw [mem_singleton_iff.1 hb]
  nth_rw 1 [← enum_typein r x]
  rw [@enum_lt_enum _ r]; rw [Subtype.mk_lt_mk]
  apply lt_succ

/-! ### The predecessor of an ordinal -/

/--
Definition of `pred` / `pred` 的定义

English:
definition pred
  signature: (o : Ordinal)
  body: isSuccPrelimitRecOn o (fun a _ => a) (fun a _ => a)

@[simp]

中文:
定义 pred
  签名: (o : 序数)
  定义体: isSuccPrelimitRecOn o (fun a _ => a) (fun a _ => a)

@[simp]

Depends on / 依赖: Completion, Completion.dist_eq, coe_smul, coe_zero, dist_eq, dist_pair_smul, dist_smul_pair, fun_prop, induction_on, isClosed_le, isSuccPrelimitRecOn
-/
def pred (o : Ordinal) : Ordinal :=
  isSuccPrelimitRecOn o (fun a _ => a) (fun a _ => a)

@[simp]
/--
theorem `pred_add_one` / 定理 `pred_add_one`

English:
theorem pred_add_one
  given: (o)
  statement: pred (o + 1) = o
  proof: isSuccPrelimitRecOn_succ ..

@[deprecated pred_add_one (since := "2026-05-25")]

中文:
定理 pred_add_one
  条件: (o)
  结论: pred (o + 1) = o
  证明: isSuccPrelimitRecOn_succ ..

@[deprecated pred_add_one (since := "2026-05-25")]

Depends on / 依赖: isSuccPrelimitRecOn_succ
-/
theorem pred_add_one (o) : pred (o + 1) = o :=
  isSuccPrelimitRecOn_succ ..

@[deprecated pred_add_one (since := "2026-05-25")]
/--
theorem `pred_succ` / 定理 `pred_succ`

English:
theorem pred_succ
  given: (o)
  statement: pred (succ o) = o
  proof: pred_add_one o

中文:
定理 pred_succ
  条件: (o)
  结论: pred (succ o) = o
  证明: pred_add_one o

Depends on / 依赖: pred_add_one
-/
theorem pred_succ (o) : pred (succ o) = o :=
  pred_add_one o

/--
theorem `pred_eq_of_isSuccPrelimit` / 定理 `pred_eq_of_isSuccPrelimit`

English:
theorem pred_eq_of_isSuccPrelimit
  given: {o}
  statement: IsSuccPrelimit o -> pred o = o
  proof: isSuccPrelimitRecOn_of_isSuccPrelimit _ _

alias _root_.Order.IsSuccPrelimit.ordinalPred_eq := pred_eq_of_isSuccPrelimit

中文:
定理 pred_eq_of_isSuccPrelimit
  条件: {o}
  结论: IsSuccPrelimit o -> pred o = o
  证明: isSuccPrelimitRecOn_of_isSuccPrelimit _ _

alias _root_.Order.IsSuccPrelimit.ordinalPred_eq := pred_eq_of_isSuccPrelimit

Depends on / 依赖: isSuccPrelimitRecOn_of_isSuccPrelimit
-/
theorem pred_eq_of_isSuccPrelimit {o} : IsSuccPrelimit o -> pred o = o :=
  isSuccPrelimitRecOn_of_isSuccPrelimit _ _

alias _root_.Order.IsSuccPrelimit.ordinalPred_eq := pred_eq_of_isSuccPrelimit

/--
theorem `_root_.Order.IsSuccLimit.ordinalPred_eq` / 定理 `_root_.Order.IsSuccLimit.ordinalPred_eq`

English:
theorem _root_.Order.IsSuccLimit.ordinalPred_eq
  given: {o} (ho : IsSuccLimit o)
  statement: pred o = o
  proof: ho.isSuccPrelimit.ordinalPred_eq

@[simp]

中文:
定理 _root_.Order.是SuccLimit.ordinalPred_eq
  条件: {o} (ho : 是SuccLimit o)
  结论: pred o = o
  证明: ho.isSuccPrelimit.ordinalPred_eq

@[simp]

Depends on / 依赖: ho.isSuccPrelimit.ordinalPred_eq, isSuccPrelimit, ordinalPred_eq
-/
theorem _root_.Order.IsSuccLimit.ordinalPred_eq {o} (ho : IsSuccLimit o) : pred o = o :=
  ho.isSuccPrelimit.ordinalPred_eq

@[simp]
/--
theorem `pred_zero` / 定理 `pred_zero`

English:
theorem pred_zero
  statement: pred 0 = 0
  proof: isSuccPrelimit_zero.ordinalPred_eq

@[simp]

中文:
定理 pred_zero
  结论: pred 0 = 0
  证明: isSuccPrelimit_zero.ordinalPred_eq

@[simp]

Depends on / 依赖: isSuccPrelimit_zero, isSuccPrelimit_zero.ordinalPred_eq, ordinalPred_eq
-/
theorem pred_zero : pred 0 = 0 :=
  isSuccPrelimit_zero.ordinalPred_eq

@[simp]
/--
theorem `pred_le_iff_le_succ` / 定理 `pred_le_iff_le_succ`

English:
theorem pred_le_iff_le_succ
  given: {a b}
  statement: pred a <= b ↔ a <= succ b
  proof: by
  obtain ⟨a, rfl⟩ | ha := mem_range_succ_or_isSuccPrelimit a
  · simp
  · rw [ha.ordinalPred_eq, ha.le_succ_iff]

@[simp]

中文:
定理 pred_le_iff_le_succ
  条件: {a b}
  结论: pred a <= b ↔ a <= succ b
  证明: by
  obtain ⟨a, rfl⟩ | ha := mem_range_succ_or_isSuccPrelimit a
  · simp
  · rw [ha.ordinalPred_eq, ha.le_succ_iff]

@[simp]

Depends on / 依赖: ha.le_succ_iff, ha.ordinalPred_eq, le_succ_iff, mem_range_succ_or_isSuccPrelimit, ordinalPred_eq
-/
theorem pred_le_iff_le_succ {a b} : pred a <= b ↔ a <= succ b := by
  obtain ⟨a, rfl⟩ | ha := mem_range_succ_or_isSuccPrelimit a
  · simp
  · rw [ha.ordinalPred_eq, ha.le_succ_iff]

@[simp]
/--
theorem `lt_pred_iff_succ_lt` / 定理 `lt_pred_iff_succ_lt`

English:
theorem lt_pred_iff_succ_lt
  given: {a b}
  statement: a < pred b ↔ succ a < b
  proof: le_iff_le_iff_lt_iff_lt.1 pred_le_iff_le_succ

中文:
定理 lt_pred_iff_succ_lt
  条件: {a b}
  结论: a < pred b ↔ succ a < b
  证明: le_iff_le_iff_lt_iff_lt.1 pred_le_iff_le_succ

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, pred_le_iff_le_succ
-/
theorem lt_pred_iff_succ_lt {a b} : a < pred b ↔ succ a < b :=
  le_iff_le_iff_lt_iff_lt.1 pred_le_iff_le_succ

/--
theorem `pred_le_self` / 定理 `pred_le_self`

English:
theorem pred_le_self
  given: (o)
  statement: pred o <= o
  proof: by
  simp

中文:
定理 pred_le_self
  条件: (o)
  结论: pred o <= o
  证明: by
  simp
-/
theorem pred_le_self (o) : pred o <= o := by
  simp

/--
Definition of `pred_succ_gi` / `pred_succ_gi` 的定义

English:
definition pred_succ_gi
  signature: : GaloisInsertion pred succ
  body: GaloisConnection.toGaloisInsertion @pred_le_iff_le_succ (by simp)

中文:
定义 pred_succ_gi
  签名: : Galois嵌入 pred succ
  定义体: GaloisConnection.toGaloisInsertion @pred_le_iff_le_succ (by simp)

Depends on / 依赖: GaloisConnection, GaloisConnection.toGaloisInsertion, pred_le_iff_le_succ, toGaloisInsertion
-/
def pred_succ_gi : GaloisInsertion pred succ :=
  GaloisConnection.toGaloisInsertion @pred_le_iff_le_succ (by simp)

/--
theorem `pred_surjective` / 定理 `pred_surjective`

English:
theorem pred_surjective
  statement: Function.Surjective pred
  proof: pred_succ_gi.l_surjective

中文:
定理 pred_surjective
  结论: 函数.满射 pred
  证明: pred_succ_gi.l_surjective

Depends on / 依赖: l_surjective, pred_succ_gi, pred_succ_gi.l_surjective
-/
theorem pred_surjective : Function.Surjective pred :=
  pred_succ_gi.l_surjective

/--
theorem `self_le_succ_pred` / 定理 `self_le_succ_pred`

English:
theorem self_le_succ_pred
  given: (o)
  statement: o <= succ (pred o)
  proof: pred_succ_gi.gc.le_u_l o

中文:
定理 self_le_succ_pred
  条件: (o)
  结论: o <= succ (pred o)
  证明: pred_succ_gi.gc.le_u_l o

Depends on / 依赖: le_u_l, pred_succ_gi, pred_succ_gi.gc.le_u_l
-/
theorem self_le_succ_pred (o) : o <= succ (pred o) :=
  pred_succ_gi.gc.le_u_l o

/--
theorem `pred_eq_iff_isSuccPrelimit` / 定理 `pred_eq_iff_isSuccPrelimit`

English:
theorem pred_eq_iff_isSuccPrelimit
  given: {o}
  statement: pred o = o ↔ IsSuccPrelimit o
  proof: by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simp
  · simp_rw [ho.ordinalPred_eq, ho]

中文:
定理 pred_eq_iff_isSuccPrelimit
  条件: {o}
  结论: pred o = o ↔ IsSuccPrelimit o
  证明: by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simp
  · simp_rw [ho.ordinalPred_eq, ho]

Depends on / 依赖: ho.ordinalPred_eq, mem_range_succ_or_isSuccPrelimit, ordinalPred_eq, simp_rw
-/
theorem pred_eq_iff_isSuccPrelimit {o} : pred o = o ↔ IsSuccPrelimit o := by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simp
  · simp_rw [ho.ordinalPred_eq, ho]

/--
theorem `pred_lt_iff_not_isSuccPrelimit` / 定理 `pred_lt_iff_not_isSuccPrelimit`

English:
theorem pred_lt_iff_not_isSuccPrelimit
  given: {o}
  statement: pred o < o ↔ ¬ IsSuccPrelimit o
  proof: by
  rw [(pred_le_self o).lt_iff_ne]
  exact pred_eq_iff_isSuccPrelimit.not

中文:
定理 pred_lt_iff_not_isSuccPrelimit
  条件: {o}
  结论: pred o < o ↔ ¬ IsSuccPrelimit o
  证明: by
  rw [(pred_le_self o).lt_iff_ne]
  exact pred_eq_iff_isSuccPrelimit.not

Depends on / 依赖: lt_iff_ne, pred_eq_iff_isSuccPrelimit, pred_eq_iff_isSuccPrelimit.not, pred_le_self
-/
theorem pred_lt_iff_not_isSuccPrelimit {o} : pred o < o ↔ ¬ IsSuccPrelimit o := by
  rw [(pred_le_self o).lt_iff_ne]
  exact pred_eq_iff_isSuccPrelimit.not

/--
theorem `succ_pred_eq_iff_not_isSuccPrelimit` / 定理 `succ_pred_eq_iff_not_isSuccPrelimit`

English:
theorem succ_pred_eq_iff_not_isSuccPrelimit
  given: {o}
  statement: succ (pred o) = o ↔ ¬ IsSuccPrelimit o
  proof: by
  rw [← (self_le_succ_pred o).ge_iff_eq']; rw [succ_le_iff]; rw [pred_lt_iff_not_isSuccPrelimit]

@[simp]

中文:
定理 succ_pred_eq_iff_not_isSuccPrelimit
  条件: {o}
  结论: succ (pred o) = o ↔ ¬ IsSuccPrelimit o
  证明: by
  rw [← (self_le_succ_pred o).ge_iff_eq']; rw [succ_le_iff]; rw [pred_lt_iff_not_isSuccPrelimit]

@[simp]

Depends on / 依赖: ge_iff_eq, pred_lt_iff_not_isSuccPrelimit, self_le_succ_pred, succ_le_iff
-/
theorem succ_pred_eq_iff_not_isSuccPrelimit {o} : succ (pred o) = o ↔ ¬ IsSuccPrelimit o := by
  rw [← (self_le_succ_pred o).ge_iff_eq']; rw [succ_le_iff]; rw [pred_lt_iff_not_isSuccPrelimit]

@[simp]
/--
theorem `lift_pred` / 定理 `lift_pred`

English:
theorem lift_pred
  given: (o : Ordinal.{v})
  statement: lift.{u} (pred o) = pred (lift.{u} o)
  proof: by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simp
  · rwa [ho.ordinalPred_eq, eq_comm, pred_eq_iff_isSuccPrelimit, isSuccPrelimit_lift]

中文:
定理 lift_pred
  条件: (o : 序数.{v})
  结论: lift.{u} (pred o) = pred (lift.{u} o)
  证明: by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simp
  · rwa [ho.ordinalPred_eq, eq_comm, pred_eq_iff_isSuccPrelimit, isSuccPrelimit_lift]

Depends on / 依赖: eq_comm, ho.ordinalPred_eq, isSuccPrelimit_lift, mem_range_succ_or_isSuccPrelimit, ordinalPred_eq, pred_eq_iff_isSuccPrelimit
-/
theorem lift_pred (o : Ordinal.{v}) : lift.{u} (pred o) = pred (lift.{u} o) := by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simp
  · rwa [ho.ordinalPred_eq, eq_comm, pred_eq_iff_isSuccPrelimit, isSuccPrelimit_lift]

/-! ### Subtraction on ordinals -/

/--
Instance `sub` / 实例 `sub`

English:
instance sub
  signature: : Sub Ordinal where
  body: if h : b <= a then Classical.choose (exists_add_of_le h) else 0

中文:
实例 sub
  签名: : 减法 序数 where
  定义体: if h : b <= a then Classical.choose (exists_add_of_le h) else 0

Depends on / 依赖: Classical, Classical.choose, exists_add_of_le
-/
instance sub : Sub Ordinal where
  sub a b := if h : b <= a then Classical.choose (exists_add_of_le h) else 0

/--
theorem `sub_eq_zero_of_lt` / 定理 `sub_eq_zero_of_lt`

English:
theorem sub_eq_zero_of_lt
  given: {a b : Ordinal} (h : a < b)
  statement: a - b = 0
  proof: dif_neg h.not_ge

中文:
定理 sub_eq_zero_of_lt
  条件: {a b : 序数} (h : a < b)
  结论: a - b = 0
  证明: dif_neg h.not_ge
-/
private theorem sub_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a - b = 0 :=
  dif_neg h.not_ge

/--
theorem `add_sub_cancel_of_le` / 定理 `add_sub_cancel_of_le`

English:
theorem add_sub_cancel_of_le
  given: {a b : Ordinal} (h : b <= a)
  statement: b + (a - b) = a
  proof: by
  change b + dite _ _ _ = a
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_add_of_le h)).symm

@[simp]

中文:
定理 add_sub_cancel_of_le
  条件: {a b : 序数} (h : b <= a)
  结论: b + (a - b) = a
  证明: by
  change b + dite _ _ _ = a
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_add_of_le h)).symm

@[simp]
-/
protected theorem add_sub_cancel_of_le {a b : Ordinal} (h : b <= a) : b + (a - b) = a := by
  change b + dite _ _ _ = a
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_add_of_le h)).symm

@[simp]
/--
theorem `add_sub_cancel` / 定理 `add_sub_cancel`

English:
theorem add_sub_cancel
  given: (a b : Ordinal)
  statement: a + b - a = b
  proof: by
  simpa using Ordinal.add_sub_cancel_of_le le_self_add

中文:
定理 add_sub_cancel
  条件: (a b : 序数)
  结论: a + b - a = b
  证明: by
  simpa using Ordinal.add_sub_cancel_of_le le_self_add

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_sub_cancel_of_le, le_self_add
-/
theorem add_sub_cancel (a b : Ordinal) : a + b - a = b := by
  simpa using Ordinal.add_sub_cancel_of_le le_self_add

/--
theorem `le_add_sub` / 定理 `le_add_sub`

English:
theorem le_add_sub
  given: (a b : Ordinal)
  statement: a <= b + (a - b)
  proof: by
  obtain h | h := le_or_gt b a
  · exact (Ordinal.add_sub_cancel_of_le h).ge
  · simpa [sub_eq_zero_of_lt h] using h.le

中文:
定理 le_add_sub
  条件: (a b : 序数)
  结论: a <= b + (a - b)
  证明: by
  obtain h | h := le_or_gt b a
  · exact (Ordinal.add_sub_cancel_of_le h).ge
  · simpa [sub_eq_zero_of_lt h] using h.le

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_sub_cancel_of_le, h.le, le_or_gt, sub_eq_zero_of_lt
-/
theorem le_add_sub (a b : Ordinal) : a <= b + (a - b) := by
  obtain h | h := le_or_gt b a
  · exact (Ordinal.add_sub_cancel_of_le h).ge
  · simpa [sub_eq_zero_of_lt h] using h.le

/--
theorem `sub_le` / 定理 `sub_le`

English:
theorem sub_le
  given: {a b c : Ordinal}
  statement: a - b <= c ↔ a <= b + c
  proof: by
  refine ⟨fun h => (le_add_sub a b).trans (by gcongr), fun h => ?_⟩
  obtain h' | h' := le_or_gt b a
  · rwa [← add_le_add_iff_left b, Ordinal.add_sub_cancel_of_le h']
  · simp [sub_eq_zero_of_lt h']

中文:
定理 sub_le
  条件: {a b c : 序数}
  结论: a - b <= c ↔ a <= b + c
  证明: by
  refine ⟨fun h => (le_add_sub a b).trans (by gcongr), fun h => ?_⟩
  obtain h' | h' := le_or_gt b a
  · rwa [← add_le_add_iff_left b, Ordinal.add_sub_cancel_of_le h']
  · simp [sub_eq_zero_of_lt h']

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_le_add_iff_left, add_sub_cancel_of_le, le_add_sub, le_or_gt, sub_eq_zero_of_lt
-/
theorem sub_le {a b c : Ordinal} : a - b <= c ↔ a <= b + c := by
  refine ⟨fun h => (le_add_sub a b).trans (by gcongr), fun h => ?_⟩
  obtain h' | h' := le_or_gt b a
  · rwa [← add_le_add_iff_left b, Ordinal.add_sub_cancel_of_le h']
  · simp [sub_eq_zero_of_lt h']

/--
theorem `lt_sub` / 定理 `lt_sub`

English:
theorem lt_sub
  given: {a b c : Ordinal}
  statement: a < b - c ↔ c + a < b
  proof: lt_iff_lt_of_le_iff_le sub_le

中文:
定理 lt_sub
  条件: {a b c : 序数}
  结论: a < b - c ↔ c + a < b
  证明: lt_iff_lt_of_le_iff_le sub_le

Depends on / 依赖: lt_iff_lt_of_le_iff_le, sub_le
-/
theorem lt_sub {a b c : Ordinal} : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le sub_le

/--
theorem `sub_eq_of_add_eq` / 定理 `sub_eq_of_add_eq`

English:
theorem sub_eq_of_add_eq
  given: {a b c : Ordinal} (h : a + b = c)
  statement: c - a = b
  proof: h ▸ add_sub_cancel _ _

中文:
定理 sub_eq_of_add_eq
  条件: {a b c : 序数} (h : a + b = c)
  结论: c - a = b
  证明: h ▸ add_sub_cancel _ _

Depends on / 依赖: add_sub_cancel
-/
theorem sub_eq_of_add_eq {a b c : Ordinal} (h : a + b = c) : c - a = b :=
  h ▸ add_sub_cancel _ _

/--
theorem `sub_le_self` / 定理 `sub_le_self`

English:
theorem sub_le_self
  given: (a b : Ordinal)
  statement: a - b <= a
  proof: sub_le.2 le_add_self

中文:
定理 sub_le_self
  条件: (a b : 序数)
  结论: a - b <= a
  证明: sub_le.2 le_add_self

Depends on / 依赖: le_add_self, sub_le
-/
theorem sub_le_self (a b : Ordinal) : a - b <= a := sub_le.2 le_add_self

/--
theorem `le_sub_of_le` / 定理 `le_sub_of_le`

English:
theorem le_sub_of_le
  given: {a b c : Ordinal} (h : b <= a)
  statement: c <= a - b ↔ b + c <= a
  proof: by
  rw [← add_le_add_iff_left b]; rw [Ordinal.add_sub_cancel_of_le h]

中文:
定理 le_sub_of_le
  条件: {a b c : 序数} (h : b <= a)
  结论: c <= a - b ↔ b + c <= a
  证明: by
  rw [← add_le_add_iff_left b]; rw [Ordinal.add_sub_cancel_of_le h]

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_le_add_iff_left, add_sub_cancel_of_le
-/
theorem le_sub_of_le {a b c : Ordinal} (h : b <= a) : c <= a - b ↔ b + c <= a := by
  rw [← add_le_add_iff_left b]; rw [Ordinal.add_sub_cancel_of_le h]

/--
theorem `sub_lt_of_le` / 定理 `sub_lt_of_le`

English:
theorem sub_lt_of_le
  given: {a b c : Ordinal} (h : b <= a)
  statement: a - b < c ↔ a < b + c
  proof: lt_iff_lt_of_le_iff_le (le_sub_of_le h)

@[simp]

中文:
定理 sub_lt_of_le
  条件: {a b c : 序数} (h : b <= a)
  结论: a - b < c ↔ a < b + c
  证明: lt_iff_lt_of_le_iff_le (le_sub_of_le h)

@[simp]

Depends on / 依赖: le_sub_of_le, lt_iff_lt_of_le_iff_le
-/
theorem sub_lt_of_le {a b c : Ordinal} (h : b <= a) : a - b < c ↔ a < b + c :=
  lt_iff_lt_of_le_iff_le (le_sub_of_le h)

@[simp]
/--
theorem `sub_zero` / 定理 `sub_zero`

English:
theorem sub_zero
  given: (a : Ordinal)
  statement: a - 0 = a
  proof: by simpa only [zero_add] using add_sub_cancel 0 a

@[simp]

中文:
定理 sub_zero
  条件: (a : 序数)
  结论: a - 0 = a
  证明: by simpa only [zero_add] using add_sub_cancel 0 a

@[simp]

Depends on / 依赖: add_sub_cancel, zero_add
-/
theorem sub_zero (a : Ordinal) : a - 0 = a := by simpa only [zero_add] using add_sub_cancel 0 a

@[simp]
/--
theorem `zero_sub` / 定理 `zero_sub`

English:
theorem zero_sub
  given: (a : Ordinal)
  statement: 0 - a = 0
  proof: by simpa using sub_le_self 0 _

@[simp]

中文:
定理 zero_sub
  条件: (a : 序数)
  结论: 0 - a = 0
  证明: by simpa using sub_le_self 0 _

@[simp]

Depends on / 依赖: sub_le_self
-/
theorem zero_sub (a : Ordinal) : 0 - a = 0 := by simpa using sub_le_self 0 _

@[simp]
/--
theorem `sub_self` / 定理 `sub_self`

English:
theorem sub_self
  given: (a : Ordinal)
  statement: a - a = 0
  proof: by simpa only [add_zero] using add_sub_cancel a 0

中文:
定理 sub_self
  条件: (a : 序数)
  结论: a - a = 0
  证明: by simpa only [add_zero] using add_sub_cancel a 0

Depends on / 依赖: add_sub_cancel, add_zero
-/
theorem sub_self (a : Ordinal) : a - a = 0 := by simpa only [add_zero] using add_sub_cancel a 0

/--
theorem `sub_eq_zero_iff_le` / 定理 `sub_eq_zero_iff_le`

English:
theorem sub_eq_zero_iff_le
  given: {a b : Ordinal}
  statement: a - b = 0 ↔ a <= b
  proof: by
  simp [← nonpos_iff_eq_zero, sub_le]

中文:
定理 sub_eq_zero_iff_le
  条件: {a b : 序数}
  结论: a - b = 0 ↔ a <= b
  证明: by
  simp [← nonpos_iff_eq_zero, sub_le]
-/
protected theorem sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a <= b := by
  simp [← nonpos_iff_eq_zero, sub_le]

/--
theorem `sub_ne_zero_iff_lt` / 定理 `sub_ne_zero_iff_lt`

English:
theorem sub_ne_zero_iff_lt
  given: {a b : Ordinal}
  statement: a - b != 0 ↔ b < a
  proof: by
  simpa using Ordinal.sub_eq_zero_iff_le.not

中文:
定理 sub_ne_zero_iff_lt
  条件: {a b : 序数}
  结论: a - b != 0 ↔ b < a
  证明: by
  simpa using Ordinal.sub_eq_zero_iff_le.not
-/
protected theorem sub_ne_zero_iff_lt {a b : Ordinal} : a - b != 0 ↔ b < a := by
  simpa using Ordinal.sub_eq_zero_iff_le.not

/--
theorem `sub_sub` / 定理 `sub_sub`

English:
theorem sub_sub
  given: (a b c : Ordinal)
  statement: a - b - c = a - (b + c)
  proof: eq_of_forall_ge_iff fun d => by rw [sub_le, sub_le, sub_le, add_assoc]

@[simp]

中文:
定理 sub_sub
  条件: (a b c : 序数)
  结论: a - b - c = a - (b + c)
  证明: eq_of_forall_ge_iff fun d => by rw [sub_le, sub_le, sub_le, add_assoc]

@[simp]

Depends on / 依赖: add_assoc, eq_of_forall_ge_iff, sub_le
-/
theorem sub_sub (a b c : Ordinal) : a - b - c = a - (b + c) :=
  eq_of_forall_ge_iff fun d => by rw [sub_le, sub_le, sub_le, add_assoc]

@[simp]
/--
theorem `add_sub_add_cancel` / 定理 `add_sub_add_cancel`

English:
theorem add_sub_add_cancel
  given: (a b c : Ordinal)
  statement: a + b - (a + c) = b - c
  proof: by
  rw [← sub_sub]; rw [add_sub_cancel]

中文:
定理 add_sub_add_cancel
  条件: (a b c : 序数)
  结论: a + b - (a + c) = b - c
  证明: by
  rw [← sub_sub]; rw [add_sub_cancel]

Depends on / 依赖: add_sub_cancel, sub_sub
-/
theorem add_sub_add_cancel (a b c : Ordinal) : a + b - (a + c) = b - c := by
  rw [← sub_sub]; rw [add_sub_cancel]

/--
theorem `le_sub_of_add_le` / 定理 `le_sub_of_add_le`

English:
theorem le_sub_of_add_le
  given: {a b c : Ordinal} (h : b + c <= a)
  statement: c <= a - b
  proof: by
  rw [← add_le_add_iff_left b]
  exact h.trans (le_add_sub a b)

中文:
定理 le_sub_of_add_le
  条件: {a b c : 序数} (h : b + c <= a)
  结论: c <= a - b
  证明: by
  rw [← add_le_add_iff_left b]
  exact h.trans (le_add_sub a b)

Depends on / 依赖: add_le_add_iff_left, h.trans, le_add_sub
-/
theorem le_sub_of_add_le {a b c : Ordinal} (h : b + c <= a) : c <= a - b := by
  rw [← add_le_add_iff_left b]
  exact h.trans (le_add_sub a b)

/--
theorem `sub_lt_of_lt_add` / 定理 `sub_lt_of_lt_add`

English:
theorem sub_lt_of_lt_add
  given: {a b c : Ordinal} (h : a < b + c) (hc : 0 < c)
  statement: a - b < c
  proof: by
  obtain hab | hba := lt_or_ge a b
  · rwa [Ordinal.sub_eq_zero_iff_le.2 hab.le]
  · rwa [sub_lt_of_le hba]

中文:
定理 sub_lt_of_lt_add
  条件: {a b c : 序数} (h : a < b + c) (hc : 0 < c)
  结论: a - b < c
  证明: by
  obtain hab | hba := lt_or_ge a b
  · rwa [Ordinal.sub_eq_zero_iff_le.2 hab.le]
  · rwa [sub_lt_of_le hba]

Depends on / 依赖: Ordinal, Ordinal.sub_eq_zero_iff_le, hab.le, lt_or_ge, sub_eq_zero_iff_le, sub_lt_of_le
-/
theorem sub_lt_of_lt_add {a b c : Ordinal} (h : a < b + c) (hc : 0 < c) : a - b < c := by
  obtain hab | hba := lt_or_ge a b
  · rwa [Ordinal.sub_eq_zero_iff_le.2 hab.le]
  · rwa [sub_lt_of_le hba]

/--
theorem `lt_add_iff` / 定理 `lt_add_iff`

English:
theorem lt_add_iff
  given: {a b c : Ordinal} (hc : c != 0)
  statement: a < b + c ↔ exists d < c, a <= b + d
  proof: by
  use fun h => ⟨_, sub_lt_of_lt_add h hc.bot_lt, le_add_sub a b⟩
  rintro ⟨d, hd, ha⟩
  exact ha.trans_lt (by gcongr)

中文:
定理 lt_add_iff
  条件: {a b c : 序数} (hc : c != 0)
  结论: a < b + c ↔ 存在 d < c, a <= b + d
  证明: by
  use fun h => ⟨_, sub_lt_of_lt_add h hc.bot_lt, le_add_sub a b⟩
  rintro ⟨d, hd, ha⟩
  exact ha.trans_lt (by gcongr)

Depends on / 依赖: bot_lt, ha.trans_lt, hc.bot_lt, le_add_sub, sub_lt_of_lt_add, trans_lt
-/
theorem lt_add_iff {a b c : Ordinal} (hc : c != 0) : a < b + c ↔ exists d < c, a <= b + d := by
  use fun h => ⟨_, sub_lt_of_lt_add h hc.bot_lt, le_add_sub a b⟩
  rintro ⟨d, hd, ha⟩
  exact ha.trans_lt (by gcongr)

/--
theorem `add_le_iff` / 定理 `add_le_iff`

English:
theorem add_le_iff
  given: {a b c : Ordinal} (hb : b != 0)
  statement: a + b <= c ↔ forall d < b, a + d < c
  proof: by
  simpa using (lt_add_iff hb).not

中文:
定理 add_le_iff
  条件: {a b c : 序数} (hb : b != 0)
  结论: a + b <= c ↔ 对任意 d < b, a + d < c
  证明: by
  simpa using (lt_add_iff hb).not

Depends on / 依赖: lt_add_iff
-/
theorem add_le_iff {a b c : Ordinal} (hb : b != 0) : a + b <= c ↔ forall d < b, a + d < c := by
  simpa using (lt_add_iff hb).not

/--
theorem `lt_add_iff_of_isSuccLimit` / 定理 `lt_add_iff_of_isSuccLimit`

English:
theorem lt_add_iff_of_isSuccLimit
  given: {a b c : Ordinal} (hc : IsSuccLimit c)
  proof: by
  rw [lt_add_iff hc.ne_bot]
  constructor <;> rintro ⟨d, hd, ha⟩
  · refine ⟨_, hc.succ_lt hd, ?_⟩
    rwa [succ_eq_add_one, ← add_assoc, lt_add_one_iff]
  · exact ⟨d, hd, ha.le⟩

中文:
定理 lt_add_iff_of_isSuccLimit
  条件: {a b c : 序数} (hc : 是SuccLimit c)
  证明: by
  rw [lt_add_iff hc.ne_bot]
  constructor <;> rintro ⟨d, hd, ha⟩
  · refine ⟨_, hc.succ_lt hd, ?_⟩
    rwa [succ_eq_add_one, ← add_assoc, lt_add_one_iff]
  · exact ⟨d, hd, ha.le⟩

Depends on / 依赖: add_assoc, ha.le, hc.ne_bot, hc.succ_lt, lt_add_iff, lt_add_one_iff, ne_bot, succ_eq_add_one, succ_lt
-/
theorem lt_add_iff_of_isSuccLimit {a b c : Ordinal} (hc : IsSuccLimit c) :
    a < b + c ↔ exists d < c, a < b + d := by
  rw [lt_add_iff hc.ne_bot]
  constructor <;> rintro ⟨d, hd, ha⟩
  · refine ⟨_, hc.succ_lt hd, ?_⟩
    rwa [succ_eq_add_one, ← add_assoc, lt_add_one_iff]
  · exact ⟨d, hd, ha.le⟩

/--
theorem `add_le_iff_of_isSuccLimit` / 定理 `add_le_iff_of_isSuccLimit`

English:
theorem add_le_iff_of_isSuccLimit
  given: {a b c : Ordinal} (hb : IsSuccLimit b)
  proof: by
  simpa using (lt_add_iff_of_isSuccLimit hb).not

中文:
定理 add_le_iff_of_isSuccLimit
  条件: {a b c : 序数} (hb : 是SuccLimit b)
  证明: by
  simpa using (lt_add_iff_of_isSuccLimit hb).not

Depends on / 依赖: lt_add_iff_of_isSuccLimit
-/
theorem add_le_iff_of_isSuccLimit {a b c : Ordinal} (hb : IsSuccLimit b) :
    a + b <= c ↔ forall d < b, a + d <= c := by
  simpa using (lt_add_iff_of_isSuccLimit hb).not

/--
theorem `isNormal_add_right` / 定理 `isNormal_add_right`

English:
theorem isNormal_add_right
  given: (a : Ordinal)
  statement: IsNormal (a + ·)
  proof: by
  rw [isNormal_iff]
  exact ⟨add_right_strictMono, fun _ l _ => (add_le_iff_of_isSuccLimit l).2⟩

中文:
定理 isNormal_add_right
  条件: (a : 序数)
  结论: 是正规 (a + ·)
  证明: by
  rw [isNormal_iff]
  exact ⟨add_right_strictMono, fun _ l _ => (add_le_iff_of_isSuccLimit l).2⟩

Depends on / 依赖: add_le_iff_of_isSuccLimit, add_right_strictMono, isNormal_iff
-/
theorem isNormal_add_right (a : Ordinal) : IsNormal (a + ·) := by
  rw [isNormal_iff]
  exact ⟨add_right_strictMono, fun _ l _ => (add_le_iff_of_isSuccLimit l).2⟩

/--
theorem `isSuccLimit_add` / 定理 `isSuccLimit_add`

English:
theorem isSuccLimit_add
  given: (a : Ordinal) {b : Ordinal}
  statement: IsSuccLimit b -> IsSuccLimit (a + b)
  proof: (isNormal_add_right a).map_isSuccLimit

中文:
定理 isSuccLimit_add
  条件: (a : 序数) {b : 序数}
  结论: 是SuccLimit b -> 是SuccLimit (a + b)
  证明: (isNormal_add_right a).map_isSuccLimit

Depends on / 依赖: isNormal_add_right, map_isSuccLimit
-/
theorem isSuccLimit_add (a : Ordinal) {b : Ordinal} : IsSuccLimit b -> IsSuccLimit (a + b) :=
  (isNormal_add_right a).map_isSuccLimit

/--
theorem `isSuccLimit_sub` / 定理 `isSuccLimit_sub`

English:
theorem isSuccLimit_sub
  given: {a b : Ordinal} (ha : IsSuccPrelimit a) (h : b < a)
  proof: by
  rw [isSuccLimit_iff]; rw [Ordinal.sub_ne_zero_iff_lt]; rw [isSuccPrelimit_iff_succ_lt]
  refine ⟨h, fun c hc => ?_⟩
  rw [lt_sub] at hc ⊢
  rw [succ_eq_add_one]; rw [← add_assoc]
  exact ha.succ_lt hc

中文:
定理 isSuccLimit_sub
  条件: {a b : 序数} (ha : IsSuccPrelimit a) (h : b < a)
  证明: by
  rw [isSuccLimit_iff]; rw [Ordinal.sub_ne_zero_iff_lt]; rw [isSuccPrelimit_iff_succ_lt]
  refine ⟨h, fun c hc => ?_⟩
  rw [lt_sub] at hc ⊢
  rw [succ_eq_add_one]; rw [← add_assoc]
  exact ha.succ_lt hc

Depends on / 依赖: Ordinal, Ordinal.sub_ne_zero_iff_lt, add_assoc, ha.succ_lt, isSuccLimit_iff, isSuccPrelimit_iff_succ_lt, lt_sub, sub_ne_zero_iff_lt, succ_eq_add_one, succ_lt
-/
theorem isSuccLimit_sub {a b : Ordinal} (ha : IsSuccPrelimit a) (h : b < a) :
    IsSuccLimit (a - b) := by
  rw [isSuccLimit_iff]; rw [Ordinal.sub_ne_zero_iff_lt]; rw [isSuccPrelimit_iff_succ_lt]
  refine ⟨h, fun c hc => ?_⟩
  rw [lt_sub] at hc ⊢
  rw [succ_eq_add_one]; rw [← add_assoc]
  exact ha.succ_lt hc

/-! ### Multiplication of ordinals -/

/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: : Monoid Ordinal.{u} where
  body: Quotient.liftOn₂ a b (fun ⟨α, r, _⟩ ⟨β, s, _⟩ => ⟦⟨β × α, Prod.Lex s r, inferInstance⟩⟧)
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => Quot.sound ⟨RelIso.prodLexCongr g f⟩
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun _ _ _ =>
.symm Quotient.sound ⟨⟨prodAssoc .., by grind [Prod.mk.injEq]⟩⟩
  mul_one a := inductionOn a fun α _ _ => Quotient.sound ⟨⟨punitProd α, by simp [Prod.lex_def]⟩⟩
  one_mul a := inductionOn a fun α _ _ => Quotient.sound ⟨⟨prodPUnit α, by simp [Prod.lex_def]⟩⟩

@[simp]

中文:
实例 monoid
  签名: : 幺半群 序数.{u} where
  定义体: Quotient.liftOn₂ a b (fun ⟨α, r, _⟩ ⟨β, s, _⟩ => ⟦⟨β × α, Prod.Lex s r, inferInstance⟩⟧)
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => Quot.sound ⟨RelIso.prodLexCongr g f⟩
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun _ _ _ =>
.symm Quotient.sound ⟨⟨prodAssoc .., by grind [Prod.mk.injEq]⟩⟩
  mul_one a := inductionOn a fun α _ _ => Quotient.sound ⟨⟨punitProd α, by simp [Prod.lex_def]⟩⟩
  one_mul a := inductionOn a fun α _ _ => Quotient.sound ⟨⟨prodPUnit α, by simp [Prod.lex_def]⟩⟩

@[simp]

Depends on / 依赖: Prod.Lex, Prod.lex_def, Prod.mk.injEq, Quot.sound, Quotient, Quotient.inductionOn, Quotient.liftOn, Quotient.sound, RelIso, RelIso.prodLexCongr, inductionOn, lex_def, mul_assoc, mul_one, one_mul, prodAssoc, prodLexCongr, prodPUnit, punitProd
-/
instance monoid : Monoid Ordinal.{u} where
  mul a b :=
    Quotient.liftOn₂ a b (fun ⟨α, r, _⟩ ⟨β, s, _⟩ => ⟦⟨β × α, Prod.Lex s r, inferInstance⟩⟧)
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => Quot.sound ⟨RelIso.prodLexCongr g f⟩
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun _ _ _ =>
.symm Quotient.sound ⟨⟨prodAssoc .., by grind [Prod.mk.injEq]⟩⟩
  mul_one a := inductionOn a fun α _ _ => Quotient.sound ⟨⟨punitProd α, by simp [Prod.lex_def]⟩⟩
  one_mul a := inductionOn a fun α _ _ => Quotient.sound ⟨⟨prodPUnit α, by simp [Prod.lex_def]⟩⟩

@[simp]
/--
theorem `type_prod_lex` / 定理 `type_prod_lex`

English:
theorem type_prod_lex
  statement: {α β : Type u} (r : α -> α -> Prop) (s : β -> β -> Prop) [IsWellOrder α r]
  proof: rfl

中文:
定理 type_prod_lex
  结论: {α β : 类型u} (r : α -> α -> 命题) (s : β -> β -> 命题) [是良序 α r]
  证明: rfl
-/
theorem type_prod_lex {α β : Type u} (r : α -> α -> Prop) (s : β -> β -> Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Prod.Lex s r) = type r * type s :=
  rfl

/--
theorem `mul_eq_zero'` / 定理 `mul_eq_zero'`

English:
theorem mul_eq_zero'
  given: {a b : Ordinal}
  statement: a * b = 0 ↔ a = 0 ∨ b = 0
  proof: by
  induction a, b using inductionOn₂ with | _ α _ β _
  simp_rw [← type_prod_lex, type_eq_zero_iff_isEmpty, isEmpty_prod, iff_true_intro or_comm]

中文:
定理 mul_eq_zero'
  条件: {a b : 序数}
  结论: a * b = 0 ↔ a = 0 ∨ b = 0
  证明: by
  induction a, b using inductionOn₂ with | _ α _ β _
  simp_rw [← type_prod_lex, type_eq_zero_iff_isEmpty, isEmpty_prod, iff_true_intro or_comm]
-/
private theorem mul_eq_zero' {a b : Ordinal} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  induction a, b using inductionOn₂ with | _ α _ β _
  simp_rw [← type_prod_lex, type_eq_zero_iff_isEmpty, isEmpty_prod, iff_true_intro or_comm]

/--
Instance `monoidWithZero` / 实例 `monoidWithZero`

English:
instance monoidWithZero
  signature: : MonoidWithZero Ordinal where
  body: by exact mul_eq_zero'.2 (.inr rfl)
  zero_mul _ := by exact mul_eq_zero'.2 (.inl rfl)

中文:
实例 monoidWithZero
  签名: : 带零幺半群 序数 where
  定义体: by exact mul_eq_zero'.2 (.inr rfl)
  zero_mul _ := by exact mul_eq_zero'.2 (.inl rfl)

Depends on / 依赖: mul_eq_zero, zero_mul
-/
instance monoidWithZero : MonoidWithZero Ordinal where
  mul_zero _ := by exact mul_eq_zero'.2 (.inr rfl)
  zero_mul _ := by exact mul_eq_zero'.2 (.inl rfl)

/--
Instance `noZeroDivisors` / 实例 `noZeroDivisors`

English:
instance noZeroDivisors
  signature: : NoZeroDivisors Ordinal where
  body: mul_eq_zero'.1

@[simp]

中文:
实例 noZeroDivisors
  签名: : 无零因子 序数 where
  定义体: mul_eq_zero'.1

@[simp]

Depends on / 依赖: mul_eq_zero
-/
instance noZeroDivisors : NoZeroDivisors Ordinal where
  eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_zero'.1

@[simp]
/--
theorem `lift_mul` / 定理 `lift_mul`

English:
theorem lift_mul
  given: (a b : Ordinal.{v})
  statement: lift.{u} (a * b) = lift.{u} a * lift.{u} b
  proof: Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.prodLexCongr (RelIso.preimage Equiv.ulift _)
              (RelIso.preimage Equiv.ulift _)).symm⟩

@[simp]

中文:
定理 lift_mul
  条件: (a b : 序数.{v})
  结论: lift.{u} (a * b) = lift.{u} a * lift.{u} b
  证明: Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.prodLexCongr (RelIso.preimage Equiv.ulift _)
              (RelIso.preimage Equiv.ulift _)).symm⟩

@[simp]

Depends on / 依赖: Equiv.ulift, Quotient, Quotient.inductionOn, Quotient.sound, RelIso, RelIso.preimage, RelIso.prodLexCongr, preimage, prodLexCongr
-/
theorem lift_mul (a b : Ordinal.{v}) : lift.{u} (a * b) = lift.{u} a * lift.{u} b :=
  Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.prodLexCongr (RelIso.preimage Equiv.ulift _)
              (RelIso.preimage Equiv.ulift _)).symm⟩

@[simp]
/--
theorem `card_mul` / 定理 `card_mul`

English:
theorem card_mul
  given: (a b)
  statement: card (a * b) = card a * card b
  proof: Quotient.inductionOn₂ a b fun ⟨α, _r, _⟩ ⟨β, _s, _⟩ => mul_comm #β #α

中文:
定理 card_mul
  条件: (a b)
  结论: card (a * b) = card a * card b
  证明: Quotient.inductionOn₂ a b fun ⟨α, _r, _⟩ ⟨β, _s, _⟩ => mul_comm #β #α

Depends on / 依赖: Quotient, Quotient.inductionOn, mul_comm
-/
theorem card_mul (a b) : card (a * b) = card a * card b :=
  Quotient.inductionOn₂ a b fun ⟨α, _r, _⟩ ⟨β, _s, _⟩ => mul_comm #β #α

/--
Instance `leftDistribClass` / 实例 `leftDistribClass`

English:
instance leftDistribClass
  signature: : LeftDistribClass Ordinal where
  body: Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
    Quotient.sound ⟨⟨sumProdDistrib .., by simp [Prod.lex_def]⟩⟩

中文:
实例 leftDistribClass
  签名: : LeftDistrib类 序数 where
  定义体: Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
    Quotient.sound ⟨⟨sumProdDistrib .., by simp [Prod.lex_def]⟩⟩

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
instance leftDistribClass : LeftDistribClass Ordinal where
  left_distrib a b c := Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
    Quotient.sound ⟨⟨sumProdDistrib .., by simp [Prod.lex_def]⟩⟩

/--
theorem `mul_succ` / 定理 `mul_succ`

English:
theorem mul_succ
  given: (a b : Ordinal)
  statement: a * succ b = a * b + a
  proof: mul_add_one a b

中文:
定理 mul_succ
  条件: (a b : 序数)
  结论: a * succ b = a * b + a
  证明: mul_add_one a b

Depends on / 依赖: mul_add_one
-/
theorem mul_succ (a b : Ordinal) : a * succ b = a * b + a :=
  mul_add_one a b

/--
Instance `mulLeftMono` / 实例 `mulLeftMono`

English:
instance mulLeftMono
  signature: : MulLeftMono Ordinal.{u}
  body: ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : α × γ => (f a.1, a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ (f.toRelEmbedding.map_rel_iff.2 h')
      · exact Prod.Lex.right _ h'⟩

中文:
实例 mulLeftMono
  签名: : MulLeftMono 序数.{u}
  定义体: ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : α × γ => (f a.1, a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ (f.toRelEmbedding.map_rel_iff.2 h')
      · exact Prod.Lex.right _ h'⟩

Depends on / 依赖: Prod.Lex.left, Prod.Lex.right, Quotient, Quotient.inductionOn, RelEmbedding, RelEmbedding.ofMonotone, f.toRelEmbedding.map_rel_iff, map_rel_iff, ofMonotone, ordinal_type_le, toRelEmbedding
-/
instance mulLeftMono : MulLeftMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : α × γ => (f a.1, a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ (f.toRelEmbedding.map_rel_iff.2 h')
      · exact Prod.Lex.right _ h'⟩

/--
Instance `mulRightMono` / 实例 `mulRightMono`

English:
instance mulRightMono
  signature: : MulRightMono Ordinal.{u}
  body: ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : γ × α => (a.1, f a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ h'
      · exact Prod.Lex.right _ (f.toRelEmbedding.map_rel_iff.2 h')⟩

中文:
实例 mulRightMono
  签名: : MulRightMono 序数.{u}
  定义体: ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : γ × α => (a.1, f a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ h'
      · exact Prod.Lex.right _ (f.toRelEmbedding.map_rel_iff.2 h')⟩

Depends on / 依赖: Prod.Lex.left, Prod.Lex.right, Quotient, Quotient.inductionOn, RelEmbedding, RelEmbedding.ofMonotone, f.toRelEmbedding.map_rel_iff, map_rel_iff, ofMonotone, ordinal_type_le, toRelEmbedding
-/
instance mulRightMono : MulRightMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : γ × α => (a.1, f a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ h'
      · exact Prod.Lex.right _ (f.toRelEmbedding.map_rel_iff.2 h')⟩

/--
theorem `le_mul_left` / 定理 `le_mul_left`

English:
theorem le_mul_left
  given: (a : Ordinal) {b : Ordinal} (hb : 0 < b)
  statement: a <= a * b
  proof: by
  convert! mul_le_mul_right (one_le_iff_pos.2 hb) a
  rw [mul_one a]

中文:
定理 le_mul_left
  条件: (a : 序数) {b : 序数} (hb : 0 < b)
  结论: a <= a * b
  证明: by
  convert! mul_le_mul_right (one_le_iff_pos.2 hb) a
  rw [mul_one a]

Depends on / 依赖: convert, mul_le_mul_right, mul_one, one_le_iff_pos
-/
theorem le_mul_left (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a <= a * b := by
  convert! mul_le_mul_right (one_le_iff_pos.2 hb) a
  rw [mul_one a]

/--
theorem `le_mul_right` / 定理 `le_mul_right`

English:
theorem le_mul_right
  given: (a : Ordinal) {b : Ordinal} (hb : 0 < b)
  statement: a <= b * a
  proof: by
  convert! mul_le_mul_left (one_le_iff_pos.2 hb) a
  rw [one_mul a]

中文:
定理 le_mul_right
  条件: (a : 序数) {b : 序数} (hb : 0 < b)
  结论: a <= b * a
  证明: by
  convert! mul_le_mul_left (one_le_iff_pos.2 hb) a
  rw [one_mul a]

Depends on / 依赖: convert, mul_le_mul_left, one_le_iff_pos, one_mul
-/
theorem le_mul_right (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a <= b * a := by
  convert! mul_le_mul_left (one_le_iff_pos.2 hb) a
  rw [one_mul a]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_le_of_limit_aux` / 定理 `mul_le_of_limit_aux`

English:
theorem mul_le_of_limit_aux
  statement: {α β r s} [IsWellOrder α r] [IsWellOrder β s] {c}
  proof: by
  suffices forall a b, Prod.Lex s r (b, a) (enum _ ⟨_, l⟩) from irrefl _ (this _ _)
  intro a b
  rw [← typein_lt_typein (Prod.Lex s r)]; rw [typein_enum]
  have := H _ (h.succ_lt (typein_lt_type s b))
  rw [mul_succ] at this
  have := ((add_lt_add_iff_left _).2 (typein_lt_type _ a)).trans_le this
  refine (RelEmbedding.ofMonotone (fun a => ?_) fun a b => ?_).ordinal_type_le.trans_lt this
  · rcases a with ⟨⟨b', a'⟩, h⟩
    by_cases e : b = b'
    · exact .inr ⟨a', by grind [asymm_of s]⟩
    · exact .inl (⟨b', by grind⟩, a')
  · grind [subrel_val, Sum.Lex.sep, asymm_of s]

中文:
定理 mul_le_of_limit_aux
  结论: {α β r s} [是良序 α r] [是良序 β s] {c}
  证明: by
  suffices forall a b, Prod.Lex s r (b, a) (enum _ ⟨_, l⟩) from irrefl _ (this _ _)
  intro a b
  rw [← typein_lt_typein (Prod.Lex s r)]; rw [typein_enum]
  have := H _ (h.succ_lt (typein_lt_type s b))
  rw [mul_succ] at this
  have := ((add_lt_add_iff_left _).2 (typein_lt_type _ a)).trans_le this
  refine (RelEmbedding.ofMonotone (fun a => ?_) fun a b => ?_).ordinal_type_le.trans_lt this
  · rcases a with ⟨⟨b', a'⟩, h⟩
    by_cases e : b = b'
    · exact .inr ⟨a', by grind [asymm_of s]⟩
    · exact .inl (⟨b', by grind⟩, a')
  · grind [subrel_val, Sum.Lex.sep, asymm_of s]
-/
private theorem mul_le_of_limit_aux {α β r s} [IsWellOrder α r] [IsWellOrder β s] {c}
    (h : IsSuccLimit (type s)) (H : forall b' < type s, type r * b' <= c) (l : c < type r * type s) :
    False := by
  suffices forall a b, Prod.Lex s r (b, a) (enum _ ⟨_, l⟩) from irrefl _ (this _ _)
  intro a b
  rw [← typein_lt_typein (Prod.Lex s r)]; rw [typein_enum]
  have := H _ (h.succ_lt (typein_lt_type s b))
  rw [mul_succ] at this
  have := ((add_lt_add_iff_left _).2 (typein_lt_type _ a)).trans_le this
  refine (RelEmbedding.ofMonotone (fun a => ?_) fun a b => ?_).ordinal_type_le.trans_lt this
  · rcases a with ⟨⟨b', a'⟩, h⟩
    by_cases e : b = b'
    · exact .inr ⟨a', by grind [asymm_of s]⟩
    · exact .inl (⟨b', by grind⟩, a')
  · grind [subrel_val, Sum.Lex.sep, asymm_of s]

/--
theorem `mul_le_iff_of_isSuccLimit` / 定理 `mul_le_iff_of_isSuccLimit`

English:
theorem mul_le_iff_of_isSuccLimit
  given: {a b c : Ordinal} (h : IsSuccLimit b)
  proof: by
  refine ⟨fun h _ l => (mul_le_mul_right l.le _).trans h, fun H => le_of_not_gt ?_⟩
  induction a, b using inductionOn₂ with | type α r β s
  exact mul_le_of_limit_aux h H

中文:
定理 mul_le_iff_of_isSuccLimit
  条件: {a b c : 序数} (h : 是SuccLimit b)
  证明: by
  refine ⟨fun h _ l => (mul_le_mul_right l.le _).trans h, fun H => le_of_not_gt ?_⟩
  induction a, b using inductionOn₂ with | type α r β s
  exact mul_le_of_limit_aux h H

Depends on / 依赖: l.le, le_of_not_gt, mul_le_mul_right, mul_le_of_limit_aux
-/
theorem mul_le_iff_of_isSuccLimit {a b c : Ordinal} (h : IsSuccLimit b) :
    a * b <= c ↔ forall b' < b, a * b' <= c := by
  refine ⟨fun h _ l => (mul_le_mul_right l.le _).trans h, fun H => le_of_not_gt ?_⟩
  induction a, b using inductionOn₂ with | type α r β s
  exact mul_le_of_limit_aux h H

/--
theorem `isNormal_mul_right` / 定理 `isNormal_mul_right`

English:
theorem isNormal_mul_right
  given: {a : Ordinal} (h : 0 < a)
  statement: IsNormal (a * ·)
  proof: by
  refine .of_succ_lt (fun b => ?_) fun hb => ?_
  · simpa [mul_add_one] using (add_lt_add_iff_left (a * b)).2 h
  · simpa [IsLUB, IsLeast, upperBounds, lowerBounds, mul_le_iff_of_isSuccLimit hb] using
      fun c hc => mul_le_mul_right hc.le a

中文:
定理 isNormal_mul_right
  条件: {a : 序数} (h : 0 < a)
  结论: 是正规 (a * ·)
  证明: by
  refine .of_succ_lt (fun b => ?_) fun hb => ?_
  · simpa [mul_add_one] using (add_lt_add_iff_left (a * b)).2 h
  · simpa [IsLUB, IsLeast, upperBounds, lowerBounds, mul_le_iff_of_isSuccLimit hb] using
      fun c hc => mul_le_mul_right hc.le a

Depends on / 依赖: IsLeast, add_lt_add_iff_left, hc.le, lowerBounds, mul_add_one, mul_le_iff_of_isSuccLimit, mul_le_mul_right, of_succ_lt, upperBounds
-/
theorem isNormal_mul_right {a : Ordinal} (h : 0 < a) : IsNormal (a * ·) := by
  refine .of_succ_lt (fun b => ?_) fun hb => ?_
  · simpa [mul_add_one] using (add_lt_add_iff_left (a * b)).2 h
  · simpa [IsLUB, IsLeast, upperBounds, lowerBounds, mul_le_iff_of_isSuccLimit hb] using
      fun c hc => mul_le_mul_right hc.le a

/--
theorem `lt_mul_iff_of_isSuccLimit` / 定理 `lt_mul_iff_of_isSuccLimit`

English:
theorem lt_mul_iff_of_isSuccLimit
  given: {a b c : Ordinal} (h : IsSuccLimit c)
  proof: by
  simpa using (mul_le_iff_of_isSuccLimit h).not

中文:
定理 lt_mul_iff_of_isSuccLimit
  条件: {a b c : 序数} (h : 是SuccLimit c)
  证明: by
  simpa using (mul_le_iff_of_isSuccLimit h).not

Depends on / 依赖: mul_le_iff_of_isSuccLimit
-/
theorem lt_mul_iff_of_isSuccLimit {a b c : Ordinal} (h : IsSuccLimit c) :
    a < b * c ↔ exists c' < c, a < b * c' := by
  simpa using (mul_le_iff_of_isSuccLimit h).not

/--
theorem `lt_mul_add_one_iff` / 定理 `lt_mul_add_one_iff`

English:
theorem lt_mul_add_one_iff
  given: {a b c : Ordinal}
  statement: a < b * (c + 1) ↔ exists d < b, a <= b * c + d
  proof: by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · rw [mul_add_one, lt_add_iff hb]

中文:
定理 lt_mul_add_one_iff
  条件: {a b c : 序数}
  结论: a < b * (c + 1) ↔ 存在 d < b, a <= b * c + d
  证明: by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · rw [mul_add_one, lt_add_iff hb]

Depends on / 依赖: eq_or_ne, lt_add_iff, mul_add_one
-/
theorem lt_mul_add_one_iff {a b c : Ordinal} : a < b * (c + 1) ↔ exists d < b, a <= b * c + d := by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · rw [mul_add_one, lt_add_iff hb]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PosMulStrictMono Ordinal
  body: (isNormal_mul_right ha).strictMono

中文:
实例 :
  签名: 正乘严格递增 序数
  定义体: (isNormal_mul_right ha).strictMono

Depends on / 依赖: isNormal_mul_right, strictMono
-/
instance : PosMulStrictMono Ordinal where
  mul_lt_mul_of_pos_left _a ha := (isNormal_mul_right ha).strictMono

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLeftCancelMulZero Ordinal
  body: mul_left_cancel_iff_of_pos h0.pos

中文:
实例 :
  签名: 是左消去MulZero 序数
  定义体: mul_left_cancel_iff_of_pos h0.pos

Depends on / 依赖: h0.pos, mul_left_cancel_iff_of_pos
-/
instance : IsLeftCancelMulZero Ordinal where
.mp mul_left_cancel_of_ne_zero h0 _ _ := mul_left_cancel_iff_of_pos h0.pos

/--
theorem `isSuccLimit_mul_right` / 定理 `isSuccLimit_mul_right`

English:
theorem isSuccLimit_mul_right
  given: {a b : Ordinal} (a0 : 0 < a) (l : IsSuccLimit b)
  proof: (isNormal_mul_right a0).map_isSuccLimit l

@[deprecated (since := "2026-02-01")]
alias isSuccLimit_mul := isSuccLimit_mul_right

中文:
定理 isSuccLimit_mul_right
  条件: {a b : 序数} (a0 : 0 < a) (l : 是SuccLimit b)
  证明: (isNormal_mul_right a0).map_isSuccLimit l

@[deprecated (since := "2026-02-01")]
alias isSuccLimit_mul := isSuccLimit_mul_right

Depends on / 依赖: isNormal_mul_right, map_isSuccLimit
-/
theorem isSuccLimit_mul_right {a b : Ordinal} (a0 : 0 < a) (l : IsSuccLimit b) :
    IsSuccLimit (a * b) :=
  (isNormal_mul_right a0).map_isSuccLimit l

@[deprecated (since := "2026-02-01")]
alias isSuccLimit_mul := isSuccLimit_mul_right

/--
theorem `isSuccPrelimit_mul_right` / 定理 `isSuccPrelimit_mul_right`

English:
theorem isSuccPrelimit_mul_right
  given: {a b : Ordinal} (hb : IsSuccLimit b)
  statement: IsSuccPrelimit (a * b)
  proof: by
  obtain rfl | ha := eq_zero_or_pos a
  · rw [zero_mul]
    exact isSuccPrelimit_zero
  · exact (isSuccLimit_mul_right ha hb).isSuccPrelimit

中文:
定理 isSuccPrelimit_mul_right
  条件: {a b : 序数} (hb : 是SuccLimit b)
  结论: IsSuccPrelimit (a * b)
  证明: by
  obtain rfl | ha := eq_zero_or_pos a
  · rw [zero_mul]
    exact isSuccPrelimit_zero
  · exact (isSuccLimit_mul_right ha hb).isSuccPrelimit

Depends on / 依赖: eq_zero_or_pos, isSuccLimit_mul_right, isSuccPrelimit, isSuccPrelimit_zero, zero_mul
-/
theorem isSuccPrelimit_mul_right {a b : Ordinal} (hb : IsSuccLimit b) : IsSuccPrelimit (a * b) := by
  obtain rfl | ha := eq_zero_or_pos a
  · rw [zero_mul]
    exact isSuccPrelimit_zero
  · exact (isSuccLimit_mul_right ha hb).isSuccPrelimit

/--
theorem `isSuccLimit_mul_left` / 定理 `isSuccLimit_mul_left`

English:
theorem isSuccLimit_mul_left
  given: {a b : Ordinal} (l : IsSuccLimit a) (b0 : 0 < b)
  proof: by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨b, rfl⟩ | lb)
  · exact b0.false.elim
  · rw [mul_succ]
    exact isSuccLimit_add _ l
  · exact isSuccLimit_mul_right l.bot_lt lb

中文:
定理 isSuccLimit_mul_left
  条件: {a b : 序数} (l : 是SuccLimit a) (b0 : 0 < b)
  证明: by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨b, rfl⟩ | lb)
  · exact b0.false.elim
  · rw [mul_succ]
    exact isSuccLimit_add _ l
  · exact isSuccLimit_mul_right l.bot_lt lb

Depends on / 依赖: b0.false.elim, bot_lt, isSuccLimit_add, isSuccLimit_mul_right, l.bot_lt, mul_succ, zero_or_succ_or_isSuccLimit
-/
theorem isSuccLimit_mul_left {a b : Ordinal} (l : IsSuccLimit a) (b0 : 0 < b) :
    IsSuccLimit (a * b) := by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨b, rfl⟩ | lb)
  · exact b0.false.elim
  · rw [mul_succ]
    exact isSuccLimit_add _ l
  · exact isSuccLimit_mul_right l.bot_lt lb

/--
theorem `isSuccPrelimit_mul_left` / 定理 `isSuccPrelimit_mul_left`

English:
theorem isSuccPrelimit_mul_left
  given: {a b : Ordinal} (ha : IsSuccLimit a)
  statement: IsSuccPrelimit (a * b)
  proof: by
  obtain rfl | hb := eq_zero_or_pos b
  · rw [mul_zero]
    exact isSuccPrelimit_zero
  · exact (isSuccLimit_mul_left ha hb).isSuccPrelimit

@[simp]

中文:
定理 isSuccPrelimit_mul_left
  条件: {a b : 序数} (ha : 是SuccLimit a)
  结论: IsSuccPrelimit (a * b)
  证明: by
  obtain rfl | hb := eq_zero_or_pos b
  · rw [mul_zero]
    exact isSuccPrelimit_zero
  · exact (isSuccLimit_mul_left ha hb).isSuccPrelimit

@[simp]

Depends on / 依赖: eq_zero_or_pos, isSuccLimit_mul_left, isSuccPrelimit, isSuccPrelimit_zero, mul_zero
-/
theorem isSuccPrelimit_mul_left {a b : Ordinal} (ha : IsSuccLimit a) : IsSuccPrelimit (a * b) := by
  obtain rfl | hb := eq_zero_or_pos b
  · rw [mul_zero]
    exact isSuccPrelimit_zero
  · exact (isSuccLimit_mul_left ha hb).isSuccPrelimit

@[simp]
/--
theorem `nsmul_eq_mul` / 定理 `nsmul_eq_mul`

English:
theorem nsmul_eq_mul
  statement: forall (n : Nat) (a : Ordinal), n • a = a * n
  proof: nsmul_eq_mul

中文:
定理 nsmul_eq_mul
  结论: 对任意 (n : 自然数) (a : 序数), n • a = a * n
  证明: nsmul_eq_mul
-/
theorem nsmul_eq_mul : forall (n : Nat) (a : Ordinal), n • a = a * n
  | 0, a => by rw [zero_nsmul, Nat.cast_zero, mul_zero]
  | n + 1, a => by rw [succ_nsmul, nsmul_eq_mul, Nat.cast_add_one, mul_add_one]

@[deprecated (since := "2026-03-14")] alias smul_eq_mul := nsmul_eq_mul

/--
theorem `add_mul_limit_aux` / 定理 `add_mul_limit_aux`

English:
theorem add_mul_limit_aux
  statement: {a b c : Ordinal} (ba : b + a = a) (l : IsSuccLimit c)
  proof: le_antisymm
    ((mul_le_iff_of_isSuccLimit l).2 fun c' h => by
      grw [le_succ c', IH _ h, le_self_add (a := b), ba, ← mul_succ, succ_le_of_lt <| l.succ_lt h])
    (by grw [← le_self_add])

中文:
定理 add_mul_limit_aux
  结论: {a b c : 序数} (ba : b + a = a) (l : 是SuccLimit c)
  证明: le_antisymm
    ((mul_le_iff_of_isSuccLimit l).2 fun c' h => by
      grw [le_succ c', IH _ h, le_self_add (a := b), ba, ← mul_succ, succ_le_of_lt <| l.succ_lt h])
    (by grw [← le_self_add])
-/
private theorem add_mul_limit_aux {a b c : Ordinal} (ba : b + a = a) (l : IsSuccLimit c)
    (IH : forall c' < c, (a + b) * succ c' = a * succ c' + b) : (a + b) * c = a * c :=
  le_antisymm
    ((mul_le_iff_of_isSuccLimit l).2 fun c' h => by
      grw [le_succ c', IH _ h, le_self_add (a := b), ba, ← mul_succ, succ_le_of_lt <| l.succ_lt h])
    (by grw [← le_self_add])

/--
theorem `add_mul_add_one` / 定理 `add_mul_add_one`

English:
theorem add_mul_add_one
  given: {a b : Ordinal} (c) (ba : b + a = a)
  proof: by
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [mul_add_one, IH, ← add_assoc, add_assoc _ b, ba, ← mul_add_one]
  | limit c l IH => rw [mul_add_one, add_mul_limit_aux ba l IH, mul_add_one, add_assoc]

中文:
定理 add_mul_add_one
  条件: {a b : 序数} (c) (ba : b + a = a)
  证明: by
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [mul_add_one, IH, ← add_assoc, add_assoc _ b, ba, ← mul_add_one]
  | limit c l IH => rw [mul_add_one, add_mul_limit_aux ba l IH, mul_add_one, add_assoc]

Depends on / 依赖: add_assoc, add_mul_limit_aux, add_one, limitRecOn, mul_add_one
-/
theorem add_mul_add_one {a b : Ordinal} (c) (ba : b + a = a) :
    (a + b) * (c + 1) = a * (c + 1) + b := by
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [mul_add_one, IH, ← add_assoc, add_assoc _ b, ba, ← mul_add_one]
  | limit c l IH => rw [mul_add_one, add_mul_limit_aux ba l IH, mul_add_one, add_assoc]

-- TODO: deprecate
/--
theorem `add_mul_succ` / 定理 `add_mul_succ`

English:
theorem add_mul_succ
  given: {a b : Ordinal} (c) (ba : b + a = a)
  statement: (a + b) * succ c = a * succ c + b
  proof: add_mul_add_one c ba

中文:
定理 add_mul_succ
  条件: {a b : 序数} (c) (ba : b + a = a)
  结论: (a + b) * succ c = a * succ c + b
  证明: add_mul_add_one c ba

Depends on / 依赖: add_mul_add_one
-/
theorem add_mul_succ {a b : Ordinal} (c) (ba : b + a = a) : (a + b) * succ c = a * succ c + b :=
  add_mul_add_one c ba

/--
theorem `add_mul_of_isSuccLimit` / 定理 `add_mul_of_isSuccLimit`

English:
theorem add_mul_of_isSuccLimit
  given: {a b c : Ordinal} (ba : b + a = a) (l : IsSuccLimit c)
  proof: add_mul_limit_aux ba l fun c' _ => add_mul_succ c' ba

中文:
定理 add_mul_of_isSuccLimit
  条件: {a b c : 序数} (ba : b + a = a) (l : 是SuccLimit c)
  证明: add_mul_limit_aux ba l fun c' _ => add_mul_succ c' ba

Depends on / 依赖: add_mul_limit_aux, add_mul_succ
-/
theorem add_mul_of_isSuccLimit {a b c : Ordinal} (ba : b + a = a) (l : IsSuccLimit c) :
    (a + b) * c = a * c :=
  add_mul_limit_aux ba l fun c' _ => add_mul_succ c' ba

/--
theorem `mul_two` / 定理 `mul_two`

English:
theorem mul_two
  given: (o : Ordinal)
  statement: o * 2 = o + o
  proof: by
  rw [← one_add_one_eq_two]; rw [mul_add]; rw [mul_one]

中文:
定理 mul_two
  条件: (o : 序数)
  结论: o * 2 = o + o
  证明: by
  rw [← one_add_one_eq_two]; rw [mul_add]; rw [mul_one]
-/
protected theorem mul_two (o : Ordinal) : o * 2 = o + o := by
  rw [← one_add_one_eq_two]; rw [mul_add]; rw [mul_one]

/-! ### Division on ordinals -/

/-- `a / b` is the unique ordinal `q` satisfying `a = b * q + r` with `r < b`. -/
@[no_expose]
/--
Instance `div` / 实例 `div`

English:
instance div
  signature: : Div Ordinal where
  body: sSup ((b * ·) ⁻¹' Iic a)

@[simp]

中文:
实例 div
  签名: : 除法 序数 where
  定义体: sSup ((b * ·) ⁻¹' Iic a)

@[simp]
-/
instance div : Div Ordinal where
  div a b := sSup ((b * ·) ⁻¹' Iic a)

@[simp]
/--
theorem `div_zero` / 定理 `div_zero`

English:
theorem div_zero
  given: (a : Ordinal)
  statement: a / 0 = 0
  proof: by
  change sSup _ = _
  simp

中文:
定理 div_zero
  条件: (a : 序数)
  结论: a / 0 = 0
  证明: by
  change sSup _ = _
  simp
-/
theorem div_zero (a : Ordinal) : a / 0 = 0 := by
  change sSup _ = _
  simp

/--
theorem `mul_div_gc` / 定理 `mul_div_gc`

English:
theorem mul_div_gc
  given: {a : Ordinal} (ha : a != 0)
  statement: GaloisConnection (a * ·) (· / a)
  proof: fun b c => (isNormal_mul_right ha.pos).le_iff_le_sSup' ⟨0, by simp⟩

中文:
定理 mul_div_gc
  条件: {a : 序数} (ha : a != 0)
  结论: GaloisConnection (a * ·) (· / a)
  证明: fun b c => (isNormal_mul_right ha.pos).le_iff_le_sSup' ⟨0, by simp⟩

Depends on / 依赖: ha.pos, isNormal_mul_right, le_iff_le_sSup
-/
theorem mul_div_gc {a : Ordinal} (ha : a != 0) : GaloisConnection (a * ·) (· / a) :=
  fun b c => (isNormal_mul_right ha.pos).le_iff_le_sSup' ⟨0, by simp⟩

/--
theorem `mul_le_iff_le_div` / 定理 `mul_le_iff_le_div`

English:
theorem mul_le_iff_le_div
  given: {a b c : Ordinal} (ha : a != 0)
  statement: a * b <= c ↔ b <= c / a
  proof: (mul_div_gc ha).le_iff_le

中文:
定理 mul_le_iff_le_div
  条件: {a b c : 序数} (ha : a != 0)
  结论: a * b <= c ↔ b <= c / a
  证明: (mul_div_gc ha).le_iff_le

Depends on / 依赖: le_iff_le, mul_div_gc
-/
theorem mul_le_iff_le_div {a b c : Ordinal} (ha : a != 0) : a * b <= c ↔ b <= c / a :=
  (mul_div_gc ha).le_iff_le

/--
theorem `lt_mul_iff_div_lt` / 定理 `lt_mul_iff_div_lt`

English:
theorem lt_mul_iff_div_lt
  given: {a b c : Ordinal} (ha : a != 0)
  statement: c < a * b ↔ c / a < b
  proof: (mul_div_gc ha).lt_iff_lt

中文:
定理 lt_mul_iff_div_lt
  条件: {a b c : 序数} (ha : a != 0)
  结论: c < a * b ↔ c / a < b
  证明: (mul_div_gc ha).lt_iff_lt

Depends on / 依赖: lt_iff_lt, mul_div_gc
-/
theorem lt_mul_iff_div_lt {a b c : Ordinal} (ha : a != 0) : c < a * b ↔ c / a < b :=
  (mul_div_gc ha).lt_iff_lt

/--
theorem `lt_mul_succ_div` / 定理 `lt_mul_succ_div`

English:
theorem lt_mul_succ_div
  given: (a) {b : Ordinal} (h : b != 0)
  statement: a < b * succ (a / b)
  proof: by
  rw [lt_mul_iff_div_lt h]; rw [lt_succ_iff]

中文:
定理 lt_mul_succ_div
  条件: (a) {b : 序数} (h : b != 0)
  结论: a < b * succ (a / b)
  证明: by
  rw [lt_mul_iff_div_lt h]; rw [lt_succ_iff]

Depends on / 依赖: lt_mul_iff_div_lt, lt_succ_iff
-/
theorem lt_mul_succ_div (a) {b : Ordinal} (h : b != 0) : a < b * succ (a / b) := by
  rw [lt_mul_iff_div_lt h]; rw [lt_succ_iff]

/--
theorem `lt_mul_div_add` / 定理 `lt_mul_div_add`

English:
theorem lt_mul_div_add
  given: (a) {b : Ordinal} (h : b != 0)
  statement: a < b * (a / b) + b
  proof: by
  simpa only [mul_succ] using lt_mul_succ_div a h

中文:
定理 lt_mul_div_add
  条件: (a) {b : 序数} (h : b != 0)
  结论: a < b * (a / b) + b
  证明: by
  simpa only [mul_succ] using lt_mul_succ_div a h

Depends on / 依赖: lt_mul_succ_div, mul_succ
-/
theorem lt_mul_div_add (a) {b : Ordinal} (h : b != 0) : a < b * (a / b) + b := by
  simpa only [mul_succ] using lt_mul_succ_div a h

/--
theorem `div_le` / 定理 `div_le`

English:
theorem div_le
  given: {a b c : Ordinal} (b0 : b != 0)
  statement: a / b <= c ↔ a < b * succ c
  proof: by
  rw [← lt_succ_iff]; rw [← lt_mul_iff_div_lt b0]

中文:
定理 div_le
  条件: {a b c : 序数} (b0 : b != 0)
  结论: a / b <= c ↔ a < b * succ c
  证明: by
  rw [← lt_succ_iff]; rw [← lt_mul_iff_div_lt b0]

Depends on / 依赖: lt_mul_iff_div_lt, lt_succ_iff
-/
theorem div_le {a b c : Ordinal} (b0 : b != 0) : a / b <= c ↔ a < b * succ c := by
  rw [← lt_succ_iff]; rw [← lt_mul_iff_div_lt b0]

/--
theorem `lt_div` / 定理 `lt_div`

English:
theorem lt_div
  given: {a b c : Ordinal} (h : c != 0)
  statement: a < b / c ↔ c * succ a <= b
  proof: by
  rw [← not_le]; rw [div_le h]; rw [not_lt]

中文:
定理 lt_div
  条件: {a b c : 序数} (h : c != 0)
  结论: a < b / c ↔ c * succ a <= b
  证明: by
  rw [← not_le]; rw [div_le h]; rw [not_lt]

Depends on / 依赖: div_le, not_le, not_lt
-/
theorem lt_div {a b c : Ordinal} (h : c != 0) : a < b / c ↔ c * succ a <= b := by
  rw [← not_le]; rw [div_le h]; rw [not_lt]

/--
theorem `div_pos` / 定理 `div_pos`

English:
theorem div_pos
  given: {b c : Ordinal} (h : c != 0)
  statement: 0 < b / c ↔ c <= b
  proof: by simp [lt_div h]

@[deprecated mul_le_iff_le_div (since := "2026-02-27")]

中文:
定理 div_pos
  条件: {b c : 序数} (h : c != 0)
  结论: 0 < b / c ↔ c <= b
  证明: by simp [lt_div h]

@[deprecated mul_le_iff_le_div (since := "2026-02-27")]

Depends on / 依赖: lt_div
-/
theorem div_pos {b c : Ordinal} (h : c != 0) : 0 < b / c ↔ c <= b := by simp [lt_div h]

@[deprecated mul_le_iff_le_div (since := "2026-02-27")]
/--
theorem `le_div` / 定理 `le_div`

English:
theorem le_div
  given: {a b c : Ordinal} (c0 : c != 0)
  statement: a <= b / c ↔ c * a <= b
  proof: (mul_le_iff_le_div c0).symm

@[deprecated lt_mul_iff_div_lt (since := "2026-02-27")]

中文:
定理 le_div
  条件: {a b c : 序数} (c0 : c != 0)
  结论: a <= b / c ↔ c * a <= b
  证明: (mul_le_iff_le_div c0).symm

@[deprecated lt_mul_iff_div_lt (since := "2026-02-27")]

Depends on / 依赖: mul_le_iff_le_div
-/
theorem le_div {a b c : Ordinal} (c0 : c != 0) : a <= b / c ↔ c * a <= b :=
  (mul_le_iff_le_div c0).symm

@[deprecated lt_mul_iff_div_lt (since := "2026-02-27")]
/--
theorem `div_lt` / 定理 `div_lt`

English:
theorem div_lt
  given: {a b c : Ordinal} (b0 : b != 0)
  statement: a / b < c ↔ a < b * c
  proof: (lt_mul_iff_div_lt b0).symm

中文:
定理 div_lt
  条件: {a b c : 序数} (b0 : b != 0)
  结论: a / b < c ↔ a < b * c
  证明: (lt_mul_iff_div_lt b0).symm

Depends on / 依赖: lt_mul_iff_div_lt
-/
theorem div_lt {a b c : Ordinal} (b0 : b != 0) : a / b < c ↔ a < b * c :=
  (lt_mul_iff_div_lt b0).symm

/--
theorem `div_le_of_le_mul` / 定理 `div_le_of_le_mul`

English:
theorem div_le_of_le_mul
  given: {a b c : Ordinal} (h : a <= b * c)
  statement: a / b <= c
  proof: by
  obtain rfl | b0 := eq_or_ne b 0
  · simp
· exact (div_le b0).2 h.trans_lt mul_lt_mul_of_pos_left (lt_succ c) (pos_iff_ne_zero.2 b0)

中文:
定理 div_le_of_le_mul
  条件: {a b c : 序数} (h : a <= b * c)
  结论: a / b <= c
  证明: by
  obtain rfl | b0 := eq_or_ne b 0
  · simp
· exact (div_le b0).2 h.trans_lt mul_lt_mul_of_pos_left (lt_succ c) (pos_iff_ne_zero.2 b0)

Depends on / 依赖: div_le, eq_or_ne, h.trans_lt, lt_succ, mul_lt_mul_of_pos_left, pos_iff_ne_zero, trans_lt
-/
theorem div_le_of_le_mul {a b c : Ordinal} (h : a <= b * c) : a / b <= c := by
  obtain rfl | b0 := eq_or_ne b 0
  · simp
· exact (div_le b0).2 h.trans_lt mul_lt_mul_of_pos_left (lt_succ c) (pos_iff_ne_zero.2 b0)

/--
theorem `mul_lt_of_lt_div` / 定理 `mul_lt_of_lt_div`

English:
theorem mul_lt_of_lt_div
  given: {a b c : Ordinal}
  statement: a < b / c -> c * a < b
  proof: lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp]

中文:
定理 mul_lt_of_lt_div
  条件: {a b c : 序数}
  结论: a < b / c -> c * a < b
  证明: lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp]

Depends on / 依赖: div_le_of_le_mul, lt_imp_lt_of_le_imp_le
-/
theorem mul_lt_of_lt_div {a b c : Ordinal} : a < b / c -> c * a < b :=
  lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp]
/--
theorem `zero_div` / 定理 `zero_div`

English:
theorem zero_div
  given: (a : Ordinal)
  statement: 0 / a = 0
  proof: nonpos_iff_eq_zero.1 div_le_of_le_mul zero_le

中文:
定理 zero_div
  条件: (a : 序数)
  结论: 0 / a = 0
  证明: nonpos_iff_eq_zero.1 div_le_of_le_mul zero_le

Depends on / 依赖: div_le_of_le_mul, nonpos_iff_eq_zero, zero_le
-/
theorem zero_div (a : Ordinal) : 0 / a = 0 := nonpos_iff_eq_zero.1 div_le_of_le_mul zero_le

/--
theorem `mul_div_le` / 定理 `mul_div_le`

English:
theorem mul_div_le
  given: (a b : Ordinal)
  statement: b * (a / b) <= a
  proof: if b0 : b = 0 then by simp [b0] else (mul_le_iff_le_div b0).2 le_rfl

中文:
定理 mul_div_le
  条件: (a b : 序数)
  结论: b * (a / b) <= a
  证明: if b0 : b = 0 then by simp [b0] else (mul_le_iff_le_div b0).2 le_rfl

Depends on / 依赖: le_rfl, mul_le_iff_le_div
-/
theorem mul_div_le (a b : Ordinal) : b * (a / b) <= a :=
  if b0 : b = 0 then by simp [b0] else (mul_le_iff_le_div b0).2 le_rfl

/--
theorem `div_le_left` / 定理 `div_le_left`

English:
theorem div_le_left
  given: {a b : Ordinal} (h : a <= b) (c : Ordinal)
  statement: a / c <= b / c
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · rw [div_zero, div_zero]
  · rw [← mul_le_iff_le_div hc]
    exact (mul_div_le a c).trans h

中文:
定理 div_le_left
  条件: {a b : 序数} (h : a <= b) (c : 序数)
  结论: a / c <= b / c
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · rw [div_zero, div_zero]
  · rw [← mul_le_iff_le_div hc]
    exact (mul_div_le a c).trans h

Depends on / 依赖: div_zero, eq_or_ne, mul_div_le, mul_le_iff_le_div
-/
theorem div_le_left {a b : Ordinal} (h : a <= b) (c : Ordinal) : a / c <= b / c := by
  obtain rfl | hc := eq_or_ne c 0
  · rw [div_zero, div_zero]
  · rw [← mul_le_iff_le_div hc]
    exact (mul_div_le a c).trans h

/--
theorem `mul_add_div` / 定理 `mul_add_div`

English:
theorem mul_add_div
  given: (a) {b : Ordinal} (b0 : b != 0) (c)
  statement: (b * a + c) / b = a + c / b
  proof: by
  apply le_antisymm
  · apply (div_le b0).2
    rw [mul_succ]; rw [mul_add]; rw [add_assoc]; rw [add_lt_add_iff_left]
    apply lt_mul_div_add _ b0
  · rw [← mul_le_iff_le_div b0, mul_add, add_le_add_iff_left]
    apply mul_div_le

中文:
定理 mul_add_div
  条件: (a) {b : 序数} (b0 : b != 0) (c)
  结论: (b * a + c) / b = a + c / b
  证明: by
  apply le_antisymm
  · apply (div_le b0).2
    rw [mul_succ]; rw [mul_add]; rw [add_assoc]; rw [add_lt_add_iff_left]
    apply lt_mul_div_add _ b0
  · rw [← mul_le_iff_le_div b0, mul_add, add_le_add_iff_left]
    apply mul_div_le

Depends on / 依赖: add_assoc, add_le_add_iff_left, add_lt_add_iff_left, div_le, le_antisymm, lt_mul_div_add, mul_add, mul_div_le, mul_le_iff_le_div, mul_succ
-/
theorem mul_add_div (a) {b : Ordinal} (b0 : b != 0) (c) : (b * a + c) / b = a + c / b := by
  apply le_antisymm
  · apply (div_le b0).2
    rw [mul_succ]; rw [mul_add]; rw [add_assoc]; rw [add_lt_add_iff_left]
    apply lt_mul_div_add _ b0
  · rw [← mul_le_iff_le_div b0, mul_add, add_le_add_iff_left]
    apply mul_div_le

/--
theorem `div_eq_zero_of_lt` / 定理 `div_eq_zero_of_lt`

English:
theorem div_eq_zero_of_lt
  given: {a b : Ordinal} (h : a < b)
  statement: a / b = 0
  proof: by
  rw [← nonpos_iff_eq_zero]; rw [div_le h.ne_bot]
  simpa

@[simp]

中文:
定理 div_eq_zero_of_lt
  条件: {a b : 序数} (h : a < b)
  结论: a / b = 0
  证明: by
  rw [← nonpos_iff_eq_zero]; rw [div_le h.ne_bot]
  simpa

@[simp]

Depends on / 依赖: div_le, h.ne_bot, ne_bot, nonpos_iff_eq_zero
-/
theorem div_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a / b = 0 := by
  rw [← nonpos_iff_eq_zero]; rw [div_le h.ne_bot]
  simpa

@[simp]
/--
theorem `mul_div_cancel` / 定理 `mul_div_cancel`

English:
theorem mul_div_cancel
  given: (a) {b : Ordinal} (b0 : b != 0)
  statement: b * a / b = a
  proof: by
  simpa using mul_add_div a b0 0

中文:
定理 mul_div_cancel
  条件: (a) {b : 序数} (b0 : b != 0)
  结论: b * a / b = a
  证明: by
  simpa using mul_add_div a b0 0

Depends on / 依赖: mul_add_div
-/
theorem mul_div_cancel (a) {b : Ordinal} (b0 : b != 0) : b * a / b = a := by
  simpa using mul_add_div a b0 0

/--
theorem `mul_add_div_mul` / 定理 `mul_add_div_mul`

English:
theorem mul_add_div_mul
  given: {a c : Ordinal} (hc : c < a) (b d : Ordinal)
  proof: by
  obtain rfl | hd := eq_or_ne d 0
  · rw [mul_zero, div_zero, div_zero]
  · have H := mul_ne_zero hc.ne_zero hd
    apply le_antisymm
    · rw [← lt_succ_iff, ← lt_mul_iff_div_lt H, mul_assoc]
      · grw [hc, ← mul_succ]
        gcongr
        rw [succ_le_iff]
        exact lt_mul_succ_div b hd
    · grw [← mul_le_iff_le_div H, mul_assoc, mul_div_le b d, ← le_self_add]

中文:
定理 mul_add_div_mul
  条件: {a c : 序数} (hc : c < a) (b d : 序数)
  证明: by
  obtain rfl | hd := eq_or_ne d 0
  · rw [mul_zero, div_zero, div_zero]
  · have H := mul_ne_zero hc.ne_zero hd
    apply le_antisymm
    · rw [← lt_succ_iff, ← lt_mul_iff_div_lt H, mul_assoc]
      · grw [hc, ← mul_succ]
        gcongr
        rw [succ_le_iff]
        exact lt_mul_succ_div b hd
    · grw [← mul_le_iff_le_div H, mul_assoc, mul_div_le b d, ← le_self_add]

Depends on / 依赖: div_zero, eq_or_ne, hc.ne_zero, le_antisymm, le_self_add, lt_mul_iff_div_lt, lt_mul_succ_div, lt_succ_iff, mul_assoc, mul_div_le, mul_le_iff_le_div, mul_ne_zero, mul_succ, mul_zero, ne_zero, succ_le_iff
-/
theorem mul_add_div_mul {a c : Ordinal} (hc : c < a) (b d : Ordinal) :
    (a * b + c) / (a * d) = b / d := by
  obtain rfl | hd := eq_or_ne d 0
  · rw [mul_zero, div_zero, div_zero]
  · have H := mul_ne_zero hc.ne_zero hd
    apply le_antisymm
    · rw [← lt_succ_iff, ← lt_mul_iff_div_lt H, mul_assoc]
      · grw [hc, ← mul_succ]
        gcongr
        rw [succ_le_iff]
        exact lt_mul_succ_div b hd
    · grw [← mul_le_iff_le_div H, mul_assoc, mul_div_le b d, ← le_self_add]

/--
theorem `mul_div_mul_cancel` / 定理 `mul_div_mul_cancel`

English:
theorem mul_div_mul_cancel
  given: {a : Ordinal} (ha : a != 0) (b c)
  statement: a * b / (a * c) = b / c
  proof: by
  convert! mul_add_div_mul (pos_iff_ne_zero.2 ha) b c using 1
  rw [add_zero]

中文:
定理 mul_div_mul_cancel
  条件: {a : 序数} (ha : a != 0) (b c)
  结论: a * b / (a * c) = b / c
  证明: by
  convert! mul_add_div_mul (pos_iff_ne_zero.2 ha) b c using 1
  rw [add_zero]

Depends on / 依赖: add_zero, convert, mul_add_div_mul, pos_iff_ne_zero
-/
theorem mul_div_mul_cancel {a : Ordinal} (ha : a != 0) (b c) : a * b / (a * c) = b / c := by
  convert! mul_add_div_mul (pos_iff_ne_zero.2 ha) b c using 1
  rw [add_zero]

/--
theorem `div_eq` / 定理 `div_eq`

English:
theorem div_eq
  given: {a b c : Ordinal} (hle : b * c <= a) (hlt : a < b * (c + 1))
  statement: a / b = c
  proof: by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp at hlt
  exact le_antisymm (div_le hb |>.mpr hlt) (mul_le_iff_le_div hb |>.mp hle)

中文:
定理 div_eq
  条件: {a b c : 序数} (hle : b * c <= a) (hlt : a < b * (c + 1))
  结论: a / b = c
  证明: by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp at hlt
  exact le_antisymm (div_le hb |>.mpr hlt) (mul_le_iff_le_div hb |>.mp hle)

Depends on / 依赖: div_le, eq_or_ne, le_antisymm, mul_le_iff_le_div
-/
theorem div_eq {a b c : Ordinal} (hle : b * c <= a) (hlt : a < b * (c + 1)) : a / b = c := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp at hlt
  exact le_antisymm (div_le hb |>.mpr hlt) (mul_le_iff_le_div hb |>.mp hle)

/--
theorem `div_eq_iff` / 定理 `div_eq_iff`

English:
theorem div_eq_iff
  given: {a b c : Ordinal} (hb : b != 0)
  statement: a / b = c ↔ b * c <= a ∧ a < b * (c + 1)
  proof: ⟨fun h => h ▸ ⟨mul_div_le a b, lt_mul_succ_div a hb⟩, fun ⟨hle, hlt⟩ => div_eq hle hlt⟩

中文:
定理 div_eq_iff
  条件: {a b c : 序数} (hb : b != 0)
  结论: a / b = c ↔ b * c <= a ∧ a < b * (c + 1)
  证明: ⟨fun h => h ▸ ⟨mul_div_le a b, lt_mul_succ_div a hb⟩, fun ⟨hle, hlt⟩ => div_eq hle hlt⟩

Depends on / 依赖: div_eq, lt_mul_succ_div, mul_div_le
-/
theorem div_eq_iff {a b c : Ordinal} (hb : b != 0) : a / b = c ↔ b * c <= a ∧ a < b * (c + 1) :=
  ⟨fun h => h ▸ ⟨mul_div_le a b, lt_mul_succ_div a hb⟩, fun ⟨hle, hlt⟩ => div_eq hle hlt⟩

/--
theorem `div_eq_iff'` / 定理 `div_eq_iff'`

English:
theorem div_eq_iff'
  given: {a b c : Ordinal} (hc : c != 0)
  statement: a / b = c ↔ b * c <= a ∧ a < b * (c + 1)
  proof: by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp [hc.symm]
  exact div_eq_iff hb

中文:
定理 div_eq_iff'
  条件: {a b c : 序数} (hc : c != 0)
  结论: a / b = c ↔ b * c <= a ∧ a < b * (c + 1)
  证明: by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp [hc.symm]
  exact div_eq_iff hb

Depends on / 依赖: div_eq_iff, eq_or_ne, hc.symm
-/
theorem div_eq_iff' {a b c : Ordinal} (hc : c != 0) : a / b = c ↔ b * c <= a ∧ a < b * (c + 1) := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp [hc.symm]
  exact div_eq_iff hb

/--
theorem `div_eq_one_iff` / 定理 `div_eq_one_iff`

English:
theorem div_eq_one_iff
  given: {a b : Ordinal}
  statement: a / b = 1 ↔ b <= a ∧ a < b * 2
  proof: by
  rw [div_eq_iff' one_ne_zero]; rw [mul_one]; rw [one_add_one_eq_two]

@[simp]

中文:
定理 div_eq_one_iff
  条件: {a b : 序数}
  结论: a / b = 1 ↔ b <= a ∧ a < b * 2
  证明: by
  rw [div_eq_iff' one_ne_zero]; rw [mul_one]; rw [one_add_one_eq_two]

@[simp]

Depends on / 依赖: div_eq_iff, mul_one, one_add_one_eq_two, one_ne_zero
-/
theorem div_eq_one_iff {a b : Ordinal} : a / b = 1 ↔ b <= a ∧ a < b * 2 := by
  rw [div_eq_iff' one_ne_zero]; rw [mul_one]; rw [one_add_one_eq_two]

@[simp]
/--
theorem `div_one` / 定理 `div_one`

English:
theorem div_one
  given: (a : Ordinal)
  statement: a / 1 = a
  proof: by
  simpa only [one_mul] using mul_div_cancel a one_ne_zero

@[simp]

中文:
定理 div_one
  条件: (a : 序数)
  结论: a / 1 = a
  证明: by
  simpa only [one_mul] using mul_div_cancel a one_ne_zero

@[simp]

Depends on / 依赖: mul_div_cancel, one_mul, one_ne_zero
-/
theorem div_one (a : Ordinal) : a / 1 = a := by
  simpa only [one_mul] using mul_div_cancel a one_ne_zero

@[simp]
/--
theorem `div_self` / 定理 `div_self`

English:
theorem div_self
  given: {a : Ordinal} (h : a != 0)
  statement: a / a = 1
  proof: by
  simpa only [mul_one] using mul_div_cancel 1 h

中文:
定理 div_self
  条件: {a : 序数} (h : a != 0)
  结论: a / a = 1
  证明: by
  simpa only [mul_one] using mul_div_cancel 1 h

Depends on / 依赖: mul_div_cancel, mul_one
-/
theorem div_self {a : Ordinal} (h : a != 0) : a / a = 1 := by
  simpa only [mul_one] using mul_div_cancel 1 h

/--
theorem `mul_sub` / 定理 `mul_sub`

English:
theorem mul_sub
  given: (a b c : Ordinal)
  statement: a * (b - c) = a * b - a * c
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · refine eq_of_forall_ge_iff fun d => ?_
    rw [sub_le]; rw [mul_le_iff_le_div ha]; rw [sub_le]; rw [mul_le_iff_le_div ha]; rw [mul_add_div _ ha]

中文:
定理 mul_sub
  条件: (a b c : 序数)
  结论: a * (b - c) = a * b - a * c
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · refine eq_of_forall_ge_iff fun d => ?_
    rw [sub_le]; rw [mul_le_iff_le_div ha]; rw [sub_le]; rw [mul_le_iff_le_div ha]; rw [mul_add_div _ ha]

Depends on / 依赖: eq_of_forall_ge_iff, eq_or_ne, mul_add_div, mul_le_iff_le_div, sub_le
-/
theorem mul_sub (a b c : Ordinal) : a * (b - c) = a * b - a * c := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · refine eq_of_forall_ge_iff fun d => ?_
    rw [sub_le]; rw [mul_le_iff_le_div ha]; rw [sub_le]; rw [mul_le_iff_le_div ha]; rw [mul_add_div _ ha]

/--
theorem `isSuccLimit_add_iff` / 定理 `isSuccLimit_add_iff`

English:
theorem isSuccLimit_add_iff
  given: {a b : Ordinal}
  proof: by
  refine ⟨fun h => ?_, by grind [isSuccLimit_add]⟩
  rcases eq_or_ne b 0 with (rfl | h')
  · grind
  rw [← add_sub_cancel a b]
exact .inl isSuccLimit_sub h.isSuccPrelimit lt_add_of_pos_right a h'.pos

中文:
定理 isSuccLimit_add_iff
  条件: {a b : 序数}
  证明: by
  refine ⟨fun h => ?_, by grind [isSuccLimit_add]⟩
  rcases eq_or_ne b 0 with (rfl | h')
  · grind
  rw [← add_sub_cancel a b]
exact .inl isSuccLimit_sub h.isSuccPrelimit lt_add_of_pos_right a h'.pos

Depends on / 依赖: add_sub_cancel, eq_or_ne, h.isSuccPrelimit, isSuccLimit_add, isSuccLimit_sub, isSuccPrelimit, lt_add_of_pos_right
-/
theorem isSuccLimit_add_iff {a b : Ordinal} :
    IsSuccLimit (a + b) ↔ IsSuccLimit b ∨ b = 0 ∧ IsSuccLimit a := by
  refine ⟨fun h => ?_, by grind [isSuccLimit_add]⟩
  rcases eq_or_ne b 0 with (rfl | h')
  · grind
  rw [← add_sub_cancel a b]
exact .inl isSuccLimit_sub h.isSuccPrelimit lt_add_of_pos_right a h'.pos

/--
theorem `isSuccLimit_add_iff_of_isSuccLimit` / 定理 `isSuccLimit_add_iff_of_isSuccLimit`

English:
theorem isSuccLimit_add_iff_of_isSuccLimit
  given: {a b : Ordinal} (h : IsSuccLimit a)
  proof: by
  rw [isSuccLimit_add_iff]
  obtain rfl | hb := eq_or_ne b 0
  · simpa
  · simp [hb, isSuccLimit_iff]

中文:
定理 isSuccLimit_add_iff_of_isSuccLimit
  条件: {a b : 序数} (h : 是SuccLimit a)
  证明: by
  rw [isSuccLimit_add_iff]
  obtain rfl | hb := eq_or_ne b 0
  · simpa
  · simp [hb, isSuccLimit_iff]

Depends on / 依赖: eq_or_ne, isSuccLimit_add_iff, isSuccLimit_iff
-/
theorem isSuccLimit_add_iff_of_isSuccLimit {a b : Ordinal} (h : IsSuccLimit a) :
    IsSuccLimit (a + b) ↔ IsSuccPrelimit b := by
  rw [isSuccLimit_add_iff]
  obtain rfl | hb := eq_or_ne b 0
  · simpa
  · simp [hb, isSuccLimit_iff]

/--
theorem `dvd_add_iff` / 定理 `dvd_add_iff`

English:
theorem dvd_add_iff
  statement: forall {a b c : Ordinal}, a ∣ b -> (a ∣ b + c ↔ a ∣ c)

中文:
定理 dvd_add_iff
  结论: 对任意 {a b c : 序数}, a ∣ b -> (a ∣ b + c ↔ a ∣ c)
-/
theorem dvd_add_iff : forall {a b c : Ordinal}, a ∣ b -> (a ∣ b + c ↔ a ∣ c)
  | a, _, c, ⟨b, rfl⟩ =>
    ⟨fun ⟨d, e⟩ => ⟨d - b, by rw [mul_sub, ← e, add_sub_cancel]⟩, fun ⟨d, e⟩ => by
      rw [e]; rw [← mul_add]
      apply dvd_mul_right⟩

/--
theorem `div_mul_cancel` / 定理 `div_mul_cancel`

English:
theorem div_mul_cancel
  statement: forall {a b : Ordinal}, a != 0 -> a ∣ b -> a * (b / a) = b

中文:
定理 div_mul_cancel
  结论: 对任意 {a b : 序数}, a != 0 -> a ∣ b -> a * (b / a) = b
-/
theorem div_mul_cancel : forall {a b : Ordinal}, a != 0 -> a ∣ b -> a * (b / a) = b
  | a, _, a0, ⟨b, rfl⟩ => by rw [mul_div_cancel _ a0]

/--
theorem `le_of_dvd` / 定理 `le_of_dvd`

English:
theorem le_of_dvd
  given: {a b : Ordinal} (b0 : b != 0) (h : a ∣ b)
  statement: a <= b
  proof: by
  rcases h with ⟨b, rfl⟩
  simpa using mul_le_mul_right (one_le_iff_ne_zero.mpr fun h => by simp [h] at b0) a

中文:
定理 le_of_dvd
  条件: {a b : 序数} (b0 : b != 0) (h : a ∣ b)
  结论: a <= b
  证明: by
  rcases h with ⟨b, rfl⟩
  simpa using mul_le_mul_right (one_le_iff_ne_zero.mpr fun h => by simp [h] at b0) a

Depends on / 依赖: mul_le_mul_right, one_le_iff_ne_zero, one_le_iff_ne_zero.mpr
-/
theorem le_of_dvd {a b : Ordinal} (b0 : b != 0) (h : a ∣ b) : a <= b := by
  rcases h with ⟨b, rfl⟩
  simpa using mul_le_mul_right (one_le_iff_ne_zero.mpr fun h => by simp [h] at b0) a

/--
theorem `dvd_antisymm` / 定理 `dvd_antisymm`

English:
theorem dvd_antisymm
  given: {a b : Ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a)
  statement: a = b
  proof: if a0 : a = 0 then by subst a; exact (eq_zero_of_zero_dvd h₁).symm
  else
    if b0 : b = 0 then by subst b; exact eq_zero_of_zero_dvd h₂
    else (le_of_dvd b0 h₁).antisymm (le_of_dvd a0 h₂)

中文:
定理 dvd_antisymm
  条件: {a b : 序数} (h₁ : a ∣ b) (h₂ : b ∣ a)
  结论: a = b
  证明: if a0 : a = 0 then by subst a; exact (eq_zero_of_zero_dvd h₁).symm
  else
    if b0 : b = 0 then by subst b; exact eq_zero_of_zero_dvd h₂
    else (le_of_dvd b0 h₁).antisymm (le_of_dvd a0 h₂)

Depends on / 依赖: antisymm, eq_zero_of_zero_dvd, le_of_dvd
-/
theorem dvd_antisymm {a b : Ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
  if a0 : a = 0 then by subst a; exact (eq_zero_of_zero_dvd h₁).symm
  else
    if b0 : b = 0 then by subst b; exact eq_zero_of_zero_dvd h₂
    else (le_of_dvd b0 h₁).antisymm (le_of_dvd a0 h₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPartialOrder Ordinal (· ∣ ·)
  body: dvd_refl
  trans _ _ _ := dvd_trans
  antisymm := @dvd_antisymm

中文:
实例 :
  签名: 是偏序 序数 (· ∣ ·)
  定义体: dvd_refl
  trans _ _ _ := dvd_trans
  antisymm := @dvd_antisymm

Depends on / 依赖: dvd_refl
-/
instance : IsPartialOrder Ordinal (· ∣ ·) where
  refl := dvd_refl
  trans _ _ _ := dvd_trans
  antisymm := @dvd_antisymm

/--
Instance `mod` / 实例 `mod`

English:
instance mod
  signature: : Mod Ordinal where
  body: a - b * (a / b)

中文:
实例 mod
  签名: : 取模 序数 where
  定义体: a - b * (a / b)
-/
instance mod : Mod Ordinal where
  mod a b := a - b * (a / b)

/--
theorem `mod_def` / 定理 `mod_def`

English:
theorem mod_def
  given: (a b : Ordinal)
  statement: a % b = a - b * (a / b)
  proof: rfl

中文:
定理 mod_def
  条件: (a b : 序数)
  结论: a % b = a - b * (a / b)
  证明: rfl
-/
theorem mod_def (a b : Ordinal) : a % b = a - b * (a / b) :=
  rfl

/--
theorem `mod_le` / 定理 `mod_le`

English:
theorem mod_le
  given: (a b : Ordinal)
  statement: a % b <= a
  proof: sub_le_self a _

@[simp]

中文:
定理 mod_le
  条件: (a b : 序数)
  结论: a % b <= a
  证明: sub_le_self a _

@[simp]

Depends on / 依赖: sub_le_self
-/
theorem mod_le (a b : Ordinal) : a % b <= a :=
  sub_le_self a _

@[simp]
/--
theorem `mod_zero` / 定理 `mod_zero`

English:
theorem mod_zero
  given: (a : Ordinal)
  statement: a % 0 = a
  proof: by simp [mod_def]

中文:
定理 mod_zero
  条件: (a : 序数)
  结论: a % 0 = a
  证明: by simp [mod_def]

Depends on / 依赖: mod_def
-/
theorem mod_zero (a : Ordinal) : a % 0 = a := by simp [mod_def]

/--
theorem `mod_eq_of_lt` / 定理 `mod_eq_of_lt`

English:
theorem mod_eq_of_lt
  given: {a b : Ordinal} (h : a < b)
  statement: a % b = a
  proof: by
  simp [mod_def, div_eq_zero_of_lt h]

@[simp]

中文:
定理 mod_eq_of_lt
  条件: {a b : 序数} (h : a < b)
  结论: a % b = a
  证明: by
  simp [mod_def, div_eq_zero_of_lt h]

@[simp]

Depends on / 依赖: div_eq_zero_of_lt, mod_def
-/
theorem mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b = a := by
  simp [mod_def, div_eq_zero_of_lt h]

@[simp]
/--
theorem `zero_mod` / 定理 `zero_mod`

English:
theorem zero_mod
  given: (b : Ordinal)
  statement: 0 % b = 0
  proof: by simp [mod_def]

中文:
定理 zero_mod
  条件: (b : 序数)
  结论: 0 % b = 0
  证明: by simp [mod_def]

Depends on / 依赖: mod_def
-/
theorem zero_mod (b : Ordinal) : 0 % b = 0 := by simp [mod_def]

/--
theorem `div_add_mod` / 定理 `div_add_mod`

English:
theorem div_add_mod
  given: (a b : Ordinal)
  statement: b * (a / b) + a % b = a
  proof: Ordinal.add_sub_cancel_of_le mul_div_le _ _

中文:
定理 div_add_mod
  条件: (a b : 序数)
  结论: b * (a / b) + a % b = a
  证明: Ordinal.add_sub_cancel_of_le mul_div_le _ _

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_sub_cancel_of_le, mul_div_le
-/
theorem div_add_mod (a b : Ordinal) : b * (a / b) + a % b = a :=
Ordinal.add_sub_cancel_of_le mul_div_le _ _

/--
theorem `mod_lt` / 定理 `mod_lt`

English:
theorem mod_lt
  given: (a) {b : Ordinal} (h : b != 0)
  statement: a % b < b
  proof: by
  rw [← add_lt_add_iff_left]; rw [div_add_mod]
  exact lt_mul_div_add a h

@[simp]

中文:
定理 mod_lt
  条件: (a) {b : 序数} (h : b != 0)
  结论: a % b < b
  证明: by
  rw [← add_lt_add_iff_left]; rw [div_add_mod]
  exact lt_mul_div_add a h

@[simp]

Depends on / 依赖: add_lt_add_iff_left, div_add_mod, lt_mul_div_add
-/
theorem mod_lt (a) {b : Ordinal} (h : b != 0) : a % b < b := by
  rw [← add_lt_add_iff_left]; rw [div_add_mod]
  exact lt_mul_div_add a h

@[simp]
/--
theorem `mod_self` / 定理 `mod_self`

English:
theorem mod_self
  given: (a : Ordinal)
  statement: a % a = 0
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · simp [mod_def, ha]

@[simp]

中文:
定理 mod_self
  条件: (a : 序数)
  结论: a % a = 0
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · simp [mod_def, ha]

@[simp]

Depends on / 依赖: eq_or_ne, mod_def
-/
theorem mod_self (a : Ordinal) : a % a = 0 := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · simp [mod_def, ha]

@[simp]
/--
theorem `mod_one` / 定理 `mod_one`

English:
theorem mod_one
  given: (a : Ordinal)
  statement: a % 1 = 0
  proof: by simp [mod_def]

中文:
定理 mod_one
  条件: (a : 序数)
  结论: a % 1 = 0
  证明: by simp [mod_def]

Depends on / 依赖: mod_def
-/
theorem mod_one (a : Ordinal) : a % 1 = 0 := by simp [mod_def]

/--
theorem `dvd_of_mod_eq_zero` / 定理 `dvd_of_mod_eq_zero`

English:
theorem dvd_of_mod_eq_zero
  given: {a b : Ordinal} (H : a % b = 0)
  statement: b ∣ a
  proof: ⟨a / b, by simpa [H] using (div_add_mod a b).symm⟩

中文:
定理 dvd_of_mod_eq_zero
  条件: {a b : 序数} (H : a % b = 0)
  结论: b ∣ a
  证明: ⟨a / b, by simpa [H] using (div_add_mod a b).symm⟩

Depends on / 依赖: div_add_mod
-/
theorem dvd_of_mod_eq_zero {a b : Ordinal} (H : a % b = 0) : b ∣ a :=
  ⟨a / b, by simpa [H] using (div_add_mod a b).symm⟩

/--
theorem `mod_eq_zero_of_dvd` / 定理 `mod_eq_zero_of_dvd`

English:
theorem mod_eq_zero_of_dvd
  given: {a b : Ordinal} (H : b ∣ a)
  statement: a % b = 0
  proof: by
  rcases H with ⟨c, rfl⟩
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  · simp [mod_def, hb]

中文:
定理 mod_eq_zero_of_dvd
  条件: {a b : 序数} (H : b ∣ a)
  结论: a % b = 0
  证明: by
  rcases H with ⟨c, rfl⟩
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  · simp [mod_def, hb]

Depends on / 依赖: eq_or_ne, mod_def
-/
theorem mod_eq_zero_of_dvd {a b : Ordinal} (H : b ∣ a) : a % b = 0 := by
  rcases H with ⟨c, rfl⟩
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  · simp [mod_def, hb]

/--
theorem `dvd_iff_mod_eq_zero` / 定理 `dvd_iff_mod_eq_zero`

English:
theorem dvd_iff_mod_eq_zero
  given: {a b : Ordinal}
  statement: b ∣ a ↔ a % b = 0
  proof: ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

@[simp]

中文:
定理 dvd_iff_mod_eq_zero
  条件: {a b : 序数}
  结论: b ∣ a ↔ a % b = 0
  证明: ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

@[simp]

Depends on / 依赖: dvd_of_mod_eq_zero, mod_eq_zero_of_dvd
-/
theorem dvd_iff_mod_eq_zero {a b : Ordinal} : b ∣ a ↔ a % b = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

@[simp]
/--
theorem `mul_add_mod_self` / 定理 `mul_add_mod_self`

English:
theorem mul_add_mod_self
  given: (x y z : Ordinal)
  statement: (x * y + z) % x = z % x
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rwa [mod_def, mul_add_div, mul_add, ← sub_sub, add_sub_cancel, mod_def]

@[simp]

中文:
定理 mul_add_mod_self
  条件: (x y z : 序数)
  结论: (x * y + z) % x = z % x
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rwa [mod_def, mul_add_div, mul_add, ← sub_sub, add_sub_cancel, mod_def]

@[simp]

Depends on / 依赖: add_sub_cancel, eq_or_ne, mod_def, mul_add, mul_add_div, sub_sub
-/
theorem mul_add_mod_self (x y z : Ordinal) : (x * y + z) % x = z % x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rwa [mod_def, mul_add_div, mul_add, ← sub_sub, add_sub_cancel, mod_def]

@[simp]
/--
theorem `mul_mod` / 定理 `mul_mod`

English:
theorem mul_mod
  given: (x y : Ordinal)
  statement: x * y % x = 0
  proof: by
  simpa using mul_add_mod_self x y 0

中文:
定理 mul_mod
  条件: (x y : 序数)
  结论: x * y % x = 0
  证明: by
  simpa using mul_add_mod_self x y 0

Depends on / 依赖: mul_add_mod_self
-/
theorem mul_mod (x y : Ordinal) : x * y % x = 0 := by
  simpa using mul_add_mod_self x y 0

/--
theorem `mul_add_mod_mul` / 定理 `mul_add_mod_mul`

English:
theorem mul_add_mod_mul
  given: {w x : Ordinal} (hw : w < x) (y z : Ordinal)
  proof: by
  rw [mod_def]; rw [mul_add_div_mul hw]
  apply sub_eq_of_add_eq
  rw [← add_assoc]; rw [mul_assoc]; rw [← mul_add]; rw [div_add_mod]

中文:
定理 mul_add_mod_mul
  条件: {w x : 序数} (hw : w < x) (y z : 序数)
  证明: by
  rw [mod_def]; rw [mul_add_div_mul hw]
  apply sub_eq_of_add_eq
  rw [← add_assoc]; rw [mul_assoc]; rw [← mul_add]; rw [div_add_mod]

Depends on / 依赖: add_assoc, div_add_mod, mod_def, mul_add, mul_add_div_mul, mul_assoc, sub_eq_of_add_eq
-/
theorem mul_add_mod_mul {w x : Ordinal} (hw : w < x) (y z : Ordinal) :
    (x * y + w) % (x * z) = x * (y % z) + w := by
  rw [mod_def]; rw [mul_add_div_mul hw]
  apply sub_eq_of_add_eq
  rw [← add_assoc]; rw [mul_assoc]; rw [← mul_add]; rw [div_add_mod]

/--
theorem `mul_mod_mul` / 定理 `mul_mod_mul`

English:
theorem mul_mod_mul
  given: (x y z : Ordinal)
  statement: (x * y) % (x * z) = x * (y % z)
  proof: by
  obtain rfl | hx := eq_zero_or_pos x
  · simp
  · convert! mul_add_mod_mul hx y z using 1 <;>
    rw [add_zero]

中文:
定理 mul_mod_mul
  条件: (x y z : 序数)
  结论: (x * y) % (x * z) = x * (y % z)
  证明: by
  obtain rfl | hx := eq_zero_or_pos x
  · simp
  · convert! mul_add_mod_mul hx y z using 1 <;>
    rw [add_zero]

Depends on / 依赖: add_zero, convert, eq_zero_or_pos, mul_add_mod_mul
-/
theorem mul_mod_mul (x y z : Ordinal) : (x * y) % (x * z) = x * (y % z) := by
  obtain rfl | hx := eq_zero_or_pos x
  · simp
  · convert! mul_add_mod_mul hx y z using 1 <;>
    rw [add_zero]

/--
theorem `mod_mod_of_dvd` / 定理 `mod_mod_of_dvd`

English:
theorem mod_mod_of_dvd
  given: (a : Ordinal) {b c : Ordinal} (h : c ∣ b)
  statement: a % b % c = a % c
  proof: by
  nth_rw 2 [← div_add_mod a b]
  rcases h with ⟨d, rfl⟩
  rw [mul_assoc]; rw [mul_add_mod_self]

@[simp]

中文:
定理 mod_mod_of_dvd
  条件: (a : 序数) {b c : 序数} (h : c ∣ b)
  结论: a % b % c = a % c
  证明: by
  nth_rw 2 [← div_add_mod a b]
  rcases h with ⟨d, rfl⟩
  rw [mul_assoc]; rw [mul_add_mod_self]

@[simp]

Depends on / 依赖: div_add_mod, mul_add_mod_self, mul_assoc, nth_rw
-/
theorem mod_mod_of_dvd (a : Ordinal) {b c : Ordinal} (h : c ∣ b) : a % b % c = a % c := by
  nth_rw 2 [← div_add_mod a b]
  rcases h with ⟨d, rfl⟩
  rw [mul_assoc]; rw [mul_add_mod_self]

@[simp]
/--
theorem `mod_mod` / 定理 `mod_mod`

English:
theorem mod_mod
  given: (a b : Ordinal)
  statement: a % b % b = a % b
  proof: mod_mod_of_dvd a dvd_rfl

中文:
定理 mod_mod
  条件: (a b : 序数)
  结论: a % b % b = a % b
  证明: mod_mod_of_dvd a dvd_rfl

Depends on / 依赖: dvd_rfl, mod_mod_of_dvd
-/
theorem mod_mod (a b : Ordinal) : a % b % b = a % b :=
  mod_mod_of_dvd a dvd_rfl

/--
theorem `lt_mul_iff` / 定理 `lt_mul_iff`

English:
theorem lt_mul_iff
  given: {a b c : Ordinal}
  statement: a < b * c ↔ exists q < c, exists r < b, a = b * q + r
  proof: by
  obtain rfl | hb₀ := eq_or_ne b 0; · simp
  refine ⟨fun h => ⟨_, (lt_mul_iff_div_lt hb₀).1 h, _, mod_lt a hb₀, (div_add_mod ..).symm⟩, ?_⟩
  rintro ⟨q, hq, r, hr, rfl⟩
  grw [hr, ← mul_add_one, add_one_le_iff.2 hq]

中文:
定理 lt_mul_iff
  条件: {a b c : 序数}
  结论: a < b * c ↔ 存在 q < c, 存在 r < b, a = b * q + r
  证明: by
  obtain rfl | hb₀ := eq_or_ne b 0; · simp
  refine ⟨fun h => ⟨_, (lt_mul_iff_div_lt hb₀).1 h, _, mod_lt a hb₀, (div_add_mod ..).symm⟩, ?_⟩
  rintro ⟨q, hq, r, hr, rfl⟩
  grw [hr, ← mul_add_one, add_one_le_iff.2 hq]

Depends on / 依赖: add_one_le_iff, div_add_mod, eq_or_ne, lt_mul_iff_div_lt, mod_lt, mul_add_one
-/
theorem lt_mul_iff {a b c : Ordinal} : a < b * c ↔ exists q < c, exists r < b, a = b * q + r := by
  obtain rfl | hb₀ := eq_or_ne b 0; · simp
  refine ⟨fun h => ⟨_, (lt_mul_iff_div_lt hb₀).1 h, _, mod_lt a hb₀, (div_add_mod ..).symm⟩, ?_⟩
  rintro ⟨q, hq, r, hr, rfl⟩
  grw [hr, ← mul_add_one, add_one_le_iff.2 hq]

/--
theorem `forall_lt_mul` / 定理 `forall_lt_mul`

English:
theorem forall_lt_mul
  given: {b c : Ordinal} {P : Ordinal -> Prop}
  proof: by
  grind [lt_mul_iff]

中文:
定理 对任意_lt_mul
  条件: {b c : 序数} {P : 序数 -> 命题}
  证明: by
  grind [lt_mul_iff]

Depends on / 依赖: lt_mul_iff
-/
theorem forall_lt_mul {b c : Ordinal} {P : Ordinal -> Prop} :
    (forall a < b * c, P a) ↔ forall q < c, forall r < b, P (b * q + r) := by
  grind [lt_mul_iff]

/--
theorem `exists_lt_mul` / 定理 `exists_lt_mul`

English:
theorem exists_lt_mul
  given: {b c : Ordinal} {P : Ordinal -> Prop}
  proof: by
  grind [lt_mul_iff]

中文:
定理 存在_lt_mul
  条件: {b c : 序数} {P : 序数 -> 命题}
  证明: by
  grind [lt_mul_iff]

Depends on / 依赖: lt_mul_iff
-/
theorem exists_lt_mul {b c : Ordinal} {P : Ordinal -> Prop} :
    (exists a < b * c, P a) ↔ exists q < c, exists r < b, P (b * q + r) := by
  grind [lt_mul_iff]


/--
Instance `instCharZero` / 实例 `instCharZero`

English:
instance instCharZero
  signature: : CharZero Ordinal
  body: by
  refine ⟨fun a b h => ?_⟩
  rwa [← Cardinal.ord_natCast, ← Cardinal.ord_natCast, Cardinal.ord_inj, Nat.cast_inj] at h

@[deprecated Nat.cast_add_one_comm (since := "2026-05-10")]

中文:
实例 instCharZero
  签名: : 特征零 序数
  定义体: by
  refine ⟨fun a b h => ?_⟩
  rwa [← Cardinal.ord_natCast, ← Cardinal.ord_natCast, Cardinal.ord_inj, Nat.cast_inj] at h

@[deprecated Nat.cast_add_one_comm (since := "2026-05-10")]

Depends on / 依赖: Cardinal, Cardinal.ord_inj, Cardinal.ord_natCast, Nat.cast_inj, cast_inj, ord_inj, ord_natCast
-/
instance instCharZero : CharZero Ordinal := by
  refine ⟨fun a b h => ?_⟩
  rwa [← Cardinal.ord_natCast, ← Cardinal.ord_natCast, Cardinal.ord_inj, Nat.cast_inj] at h

@[deprecated Nat.cast_add_one_comm (since := "2026-05-10")]
/--
theorem `one_add_natCast` / 定理 `one_add_natCast`

English:
theorem one_add_natCast
  given: (m : Nat)
  statement: 1 + (m : Ordinal) = succ m
  proof: m.cast_add_one_comm.symm

@[deprecated Nat.cast_add_one_comm (since := "2026-05-10")]

中文:
定理 one_add_natCast
  条件: (m : 自然数)
  结论: 1 + (m : 序数) = succ m
  证明: m.cast_add_one_comm.symm

@[deprecated Nat.cast_add_one_comm (since := "2026-05-10")]

Depends on / 依赖: cast_add_one_comm, m.cast_add_one_comm.symm
-/
theorem one_add_natCast (m : Nat) : 1 + (m : Ordinal) = succ m :=
  m.cast_add_one_comm.symm

@[deprecated Nat.cast_add_one_comm (since := "2026-05-10")]
/--
theorem `one_add_ofNat` / 定理 `one_add_ofNat`

English:
theorem one_add_ofNat
  given: (m : Nat) [m.AtLeastTwo]
  proof: m.cast_add_one_comm.symm

@[simp, norm_cast]

中文:
定理 one_add_of自然数
  条件: (m : 自然数) [m.AtLeastTwo]
  证明: m.cast_add_one_comm.symm

@[simp, norm_cast]

Depends on / 依赖: cast_add_one_comm, m.cast_add_one_comm.symm
-/
theorem one_add_ofNat (m : Nat) [m.AtLeastTwo] :
    1 + (ofNat(m) : Ordinal) = Order.succ (OfNat.ofNat m : Ordinal) :=
  m.cast_add_one_comm.symm

@[simp, norm_cast]
/--
theorem `natCast_mul` / 定理 `natCast_mul`

English:
theorem natCast_mul
  given: (m : Nat)
  statement: forall n : Nat, ((m * n : Nat) : Ordinal) = m * n

中文:
定理 natCast_mul
  条件: (m : 自然数)
  结论: 对任意 n : 自然数, ((m * n : 自然数) : 序数) = m * n
-/
theorem natCast_mul (m : Nat) : forall n : Nat, ((m * n : Nat) : Ordinal) = m * n
  | 0 => by simp
  | n + 1 => by rw [Nat.mul_succ, Nat.cast_add, natCast_mul m n, Nat.cast_succ, mul_add_one]

@[simp, norm_cast]
/--
theorem `natCast_sub` / 定理 `natCast_sub`

English:
theorem natCast_sub
  given: (m n : Nat)
  statement: ((m - n : Nat) : Ordinal) = m - n
  proof: by
  rcases le_total m n with h | h
  · rw [tsub_eq_zero_iff_le.2 h, Ordinal.sub_eq_zero_iff_le.2 (Nat.cast_le.2 h), Nat.cast_zero]
  · rw [← add_left_cancel_iff (a := ↑n), ← Nat.cast_add, add_tsub_cancel_of_le h,
      Ordinal.add_sub_cancel_of_le (Nat.cast_le.2 h)]

@[simp, norm_cast]

中文:
定理 natCast_sub
  条件: (m n : 自然数)
  结论: ((m - n : 自然数) : 序数) = m - n
  证明: by
  rcases le_total m n with h | h
  · rw [tsub_eq_zero_iff_le.2 h, Ordinal.sub_eq_zero_iff_le.2 (Nat.cast_le.2 h), Nat.cast_zero]
  · rw [← add_left_cancel_iff (a := ↑n), ← Nat.cast_add, add_tsub_cancel_of_le h,
      Ordinal.add_sub_cancel_of_le (Nat.cast_le.2 h)]

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_add, Nat.cast_le, Nat.cast_zero, Ordinal, Ordinal.add_sub_cancel_of_le, Ordinal.sub_eq_zero_iff_le, add_left_cancel_iff, add_sub_cancel_of_le, add_tsub_cancel_of_le, cast_add, cast_le, cast_zero, le_total, sub_eq_zero_iff_le, tsub_eq_zero_iff_le
-/
theorem natCast_sub (m n : Nat) : ((m - n : Nat) : Ordinal) = m - n := by
  rcases le_total m n with h | h
  · rw [tsub_eq_zero_iff_le.2 h, Ordinal.sub_eq_zero_iff_le.2 (Nat.cast_le.2 h), Nat.cast_zero]
  · rw [← add_left_cancel_iff (a := ↑n), ← Nat.cast_add, add_tsub_cancel_of_le h,
      Ordinal.add_sub_cancel_of_le (Nat.cast_le.2 h)]

@[simp, norm_cast]
/--
theorem `natCast_div` / 定理 `natCast_div`

English:
theorem natCast_div
  given: (m n : Nat)
  statement: ((m / n : Nat) : Ordinal) = m / n
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  · have hn' : (n : Ordinal) != 0 := Nat.cast_ne_zero.2 hn
    apply le_antisymm
    · rw [← mul_le_iff_le_div hn', ← natCast_mul, Nat.cast_le, mul_comm]
      apply Nat.div_mul_le_self
    · rw [div_le hn', succ_eq_add_one, ← Nat.cast_succ, ← natCast_mul, Nat.cast_lt, mul_comm,
        ← Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hn)]
      apply Nat.lt_succ_self

@[simp, norm_cast]

中文:
定理 natCast_div
  条件: (m n : 自然数)
  结论: ((m / n : 自然数) : 序数) = m / n
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  · have hn' : (n : Ordinal) != 0 := Nat.cast_ne_zero.2 hn
    apply le_antisymm
    · rw [← mul_le_iff_le_div hn', ← natCast_mul, Nat.cast_le, mul_comm]
      apply Nat.div_mul_le_self
    · rw [div_le hn', succ_eq_add_one, ← Nat.cast_succ, ← natCast_mul, Nat.cast_lt, mul_comm,
        ← Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hn)]
      apply Nat.lt_succ_self

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_le, Nat.cast_lt, Nat.cast_ne_zero, Nat.cast_succ, Nat.div_lt_iff_lt_mul, Nat.div_mul_le_self, Nat.lt_succ_self, Nat.pos_of_ne_zero, Ordinal, cast_le, cast_lt, cast_ne_zero, cast_succ, div_le, div_lt_iff_lt_mul, div_mul_le_self, eq_or_ne, le_antisymm, lt_succ_self, mul_comm
-/
theorem natCast_div (m n : Nat) : ((m / n : Nat) : Ordinal) = m / n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  · have hn' : (n : Ordinal) != 0 := Nat.cast_ne_zero.2 hn
    apply le_antisymm
    · rw [← mul_le_iff_le_div hn', ← natCast_mul, Nat.cast_le, mul_comm]
      apply Nat.div_mul_le_self
    · rw [div_le hn', succ_eq_add_one, ← Nat.cast_succ, ← natCast_mul, Nat.cast_lt, mul_comm,
        ← Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hn)]
      apply Nat.lt_succ_self

@[simp, norm_cast]
/--
theorem `natCast_mod` / 定理 `natCast_mod`

English:
theorem natCast_mod
  given: (m n : Nat)
  statement: ((m % n : Nat) : Ordinal) = m % n
  proof: by
  rw [← add_left_cancel_iff]; rw [div_add_mod]; rw [← natCast_div]; rw [← natCast_mul]; rw [← Nat.cast_add]; rw [Nat.div_add_mod]

@[simp]

中文:
定理 natCast_mod
  条件: (m n : 自然数)
  结论: ((m % n : 自然数) : 序数) = m % n
  证明: by
  rw [← add_left_cancel_iff]; rw [div_add_mod]; rw [← natCast_div]; rw [← natCast_mul]; rw [← Nat.cast_add]; rw [Nat.div_add_mod]

@[simp]

Depends on / 依赖: Nat.cast_add, Nat.div_add_mod, add_left_cancel_iff, cast_add, div_add_mod, natCast_div, natCast_mul
-/
theorem natCast_mod (m n : Nat) : ((m % n : Nat) : Ordinal) = m % n := by
  rw [← add_left_cancel_iff]; rw [div_add_mod]; rw [← natCast_div]; rw [← natCast_mul]; rw [← Nat.cast_add]; rw [Nat.div_add_mod]

@[simp]
/--
theorem `lift_natCast` / 定理 `lift_natCast`

English:
theorem lift_natCast
  statement: forall n : Nat, lift.{u, v} n = n

中文:
定理 lift_natCast
  结论: 对任意 n : 自然数, lift.{u, v} n = n
-/
theorem lift_natCast : forall n : Nat, lift.{u, v} n = n
  | 0 => by simp
  | n + 1 => by simp [lift_natCast n]

@[simp]
/--
theorem `lift_ofNat` / 定理 `lift_ofNat`

English:
theorem lift_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: lift_natCast n

@[simp]

中文:
定理 lift_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: lift_natCast n

@[simp]

Depends on / 依赖: lift_natCast
-/
theorem lift_ofNat (n : Nat) [n.AtLeastTwo] :
    lift.{u, v} ofNat(n) = OfNat.ofNat n :=
  lift_natCast n

@[simp]
/--
theorem `typein_lt_nat` / 定理 `typein_lt_nat`

English:
theorem typein_lt_nat
  given: (x : Nat)
  statement: typein LT.lt x = x
  proof: by
have : Fintype Iio x := Nat.fintypeIio x
  rw [← type_Iio_lt]; rw [type_fintype]; rw [Nat.cast_inj]
  nth_rw 2 [← Fintype.card_fin x]
  exact Fintype.card_congr Fin.equivSubtype.symm

@[simp]

中文:
定理 typein_lt_nat
  条件: (x : 自然数)
  结论: typein LT.lt x = x
  证明: by
have : Fintype Iio x := Nat.fintypeIio x
  rw [← type_Iio_lt]; rw [type_fintype]; rw [Nat.cast_inj]
  nth_rw 2 [← Fintype.card_fin x]
  exact Fintype.card_congr Fin.equivSubtype.symm

@[simp]

Depends on / 依赖: Fin.equivSubtype.symm, Fintype, Fintype.card_congr, Fintype.card_fin, Nat.cast_inj, Nat.fintypeIio, card_congr, card_fin, cast_inj, equivSubtype, fintypeIio, nth_rw, type_Iio_lt, type_fintype
-/
theorem typein_lt_nat (x : Nat) : typein LT.lt x = x := by
have : Fintype Iio x := Nat.fintypeIio x
  rw [← type_Iio_lt]; rw [type_fintype]; rw [Nat.cast_inj]
  nth_rw 2 [← Fintype.card_fin x]
  exact Fintype.card_congr Fin.equivSubtype.symm

@[simp]
/--
theorem `typein_lt_fin` / 定理 `typein_lt_fin`

English:
theorem typein_lt_fin
  given: {n : Nat} (x : Fin n)
  statement: typein LT.lt x = x
  proof: by
  rw [← type_Iio_lt]; rw [type_fintype]; rw [Nat.cast_inj]
  exact Fintype.card_fin_lt_of_le x.is_le'

中文:
定理 typein_lt_fin
  条件: {n : 自然数} (x : 有限集 n)
  结论: typein LT.lt x = x
  证明: by
  rw [← type_Iio_lt]; rw [type_fintype]; rw [Nat.cast_inj]
  exact Fintype.card_fin_lt_of_le x.is_le'

Depends on / 依赖: Fintype, Fintype.card_fin_lt_of_le, Nat.cast_inj, card_fin_lt_of_le, cast_inj, is_le, type_Iio_lt, type_fintype, x.is_le
-/
theorem typein_lt_fin {n : Nat} (x : Fin n) : typein LT.lt x = x := by
  rw [← type_Iio_lt]; rw [type_fintype]; rw [Nat.cast_inj]
  exact Fintype.card_fin_lt_of_le x.is_le'

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `enum_lt_fin` / 定理 `enum_lt_fin`

English:
theorem enum_lt_fin
  given: {n : Nat} (x : Fin n)
  statement: enum LT.lt ⟨x, by simp⟩ = x
  proof: by
  simp [← typein_inj LT.lt]

中文:
定理 enum_lt_fin
  条件: {n : 自然数} (x : 有限集 n)
  结论: enum LT.lt ⟨x, by simp⟩ = x
  证明: by
  simp [← typein_inj LT.lt]

Depends on / 依赖: LT.lt, typein_inj
-/
theorem enum_lt_fin {n : Nat} (x : Fin n) : enum LT.lt ⟨x, by simp⟩ = x := by
  simp [← typein_inj LT.lt]


/--
theorem `lt_omega0` / 定理 `lt_omega0`

English:
theorem lt_omega0
  given: {o : Ordinal}
  statement: o < ω ↔ exists n : Nat, o = n
  proof: by
  simp_rw [← Cardinal.ord_aleph0, Cardinal.lt_ord, lt_aleph0, card_eq_nat]

@[simp]

中文:
定理 lt_omega0
  条件: {o : 序数}
  结论: o < ω ↔ 存在 n : 自然数, o = n
  证明: by
  simp_rw [← Cardinal.ord_aleph0, Cardinal.lt_ord, lt_aleph0, card_eq_nat]

@[simp]

Depends on / 依赖: Cardinal, Cardinal.lt_ord, Cardinal.ord_aleph0, card_eq_nat, lt_aleph0, lt_ord, ord_aleph0, simp_rw
-/
theorem lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o = n := by
  simp_rw [← Cardinal.ord_aleph0, Cardinal.lt_ord, lt_aleph0, card_eq_nat]

@[simp]
/--
theorem `natCast_lt_omega0` / 定理 `natCast_lt_omega0`

English:
theorem natCast_lt_omega0
  given: (n : Nat)
  statement: ↑n < ω
  proof: lt_omega0.2 ⟨_, rfl⟩

@[deprecated (since := "2026-03-08")] alias nat_lt_omega0 := natCast_lt_omega0

中文:
定理 natCast_lt_omega0
  条件: (n : 自然数)
  结论: ↑n < ω
  证明: lt_omega0.2 ⟨_, rfl⟩

@[deprecated (since := "2026-03-08")] alias nat_lt_omega0 := natCast_lt_omega0

Depends on / 依赖: lt_omega0
-/
theorem natCast_lt_omega0 (n : Nat) : ↑n < ω :=
  lt_omega0.2 ⟨_, rfl⟩

@[deprecated (since := "2026-03-08")] alias nat_lt_omega0 := natCast_lt_omega0

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `enum_lt_nat` / 定理 `enum_lt_nat`

English:
theorem enum_lt_nat
  given: (x : Nat)
  statement: enum LT.lt ⟨x, by simp⟩ = x
  proof: by
  simp [← typein_inj LT.lt]

中文:
定理 enum_lt_nat
  条件: (x : 自然数)
  结论: enum LT.lt ⟨x, by simp⟩ = x
  证明: by
  simp [← typein_inj LT.lt]

Depends on / 依赖: LT.lt, typein_inj
-/
theorem enum_lt_nat (x : Nat) : enum LT.lt ⟨x, by simp⟩ = x := by
  simp [← typein_inj LT.lt]

/--
theorem `eq_natCast_of_le_natCast` / 定理 `eq_natCast_of_le_natCast`

English:
theorem eq_natCast_of_le_natCast
  given: {a : Ordinal} {b : Nat} (h : a <= b)
  statement: exists c : Nat, a = c
  proof: lt_omega0.1 (h.trans_lt (natCast_lt_omega0 b))

中文:
定理 eq_natCast_of_le_natCast
  条件: {a : 序数} {b : 自然数} (h : a <= b)
  结论: 存在 c : 自然数, a = c
  证明: lt_omega0.1 (h.trans_lt (natCast_lt_omega0 b))

Depends on / 依赖: h.trans_lt, lt_omega0, natCast_lt_omega0, trans_lt
-/
theorem eq_natCast_of_le_natCast {a : Ordinal} {b : Nat} (h : a <= b) : exists c : Nat, a = c :=
  lt_omega0.1 (h.trans_lt (natCast_lt_omega0 b))

/--
theorem `eq_natCast_or_omega0_le` / 定理 `eq_natCast_or_omega0_le`

English:
theorem eq_natCast_or_omega0_le
  given: (o : Ordinal)
  statement: (exists n : Nat, o = n) ∨ ω <= o
  proof: by
  obtain ho | ho := lt_or_ge o ω
· exact Or.inl lt_omega0.1 ho
  · exact Or.inr ho

@[deprecated (since := "2026-03-12")] alias eq_nat_or_omega0_le := eq_natCast_or_omega0_le

@[simp]

中文:
定理 eq_natCast_or_omega0_le
  条件: (o : 序数)
  结论: (存在 n : 自然数, o = n) ∨ ω <= o
  证明: by
  obtain ho | ho := lt_or_ge o ω
· exact Or.inl lt_omega0.1 ho
  · exact Or.inr ho

@[deprecated (since := "2026-03-12")] alias eq_nat_or_omega0_le := eq_natCast_or_omega0_le

@[simp]

Depends on / 依赖: Or.inl, Or.inr, lt_omega0, lt_or_ge
-/
theorem eq_natCast_or_omega0_le (o : Ordinal) : (exists n : Nat, o = n) ∨ ω <= o := by
  obtain ho | ho := lt_or_ge o ω
· exact Or.inl lt_omega0.1 ho
  · exact Or.inr ho

@[deprecated (since := "2026-03-12")] alias eq_nat_or_omega0_le := eq_natCast_or_omega0_le

@[simp]
/--
theorem `natCast_image_Iio` / 定理 `natCast_image_Iio`

English:
theorem natCast_image_Iio
  given: (n : Nat)
  statement: Nat.cast '' Set.Iio n = Set.Iio (n : Ordinal)
  proof: by
  ext o
  have := @eq_natCast_of_le_natCast o
  grind [Nat.cast_lt]

@[simp]

中文:
定理 natCast_image_Iio
  条件: (n : 自然数)
  结论: 自然数.cast '' 集合.左无界右开区间 n = 集合.左无界右开区间 (n : 序数)
  证明: by
  ext o
  have := @eq_natCast_of_le_natCast o
  grind [Nat.cast_lt]

@[simp]

Depends on / 依赖: Nat.cast_lt, cast_lt, eq_natCast_of_le_natCast
-/
theorem natCast_image_Iio (n : Nat) : Nat.cast '' Set.Iio n = Set.Iio (n : Ordinal) := by
  ext o
  have := @eq_natCast_of_le_natCast o
  grind [Nat.cast_lt]

@[simp]
/--
theorem `omega0_pos` / 定理 `omega0_pos`

English:
theorem omega0_pos
  statement: 0 < ω
  proof: natCast_lt_omega0 0

@[simp]

中文:
定理 omega0_pos
  结论: 0 < ω
  证明: natCast_lt_omega0 0

@[simp]

Depends on / 依赖: natCast_lt_omega0
-/
theorem omega0_pos : 0 < ω :=
  natCast_lt_omega0 0

@[simp]
/--
theorem `omega0_ne_zero` / 定理 `omega0_ne_zero`

English:
theorem omega0_ne_zero
  statement: ω != 0
  proof: omega0_pos.ne'

@[simp]

中文:
定理 omega0_ne_zero
  结论: ω != 0
  证明: omega0_pos.ne'

@[simp]

Depends on / 依赖: omega0_pos, omega0_pos.ne
-/
theorem omega0_ne_zero : ω != 0 :=
  omega0_pos.ne'

@[simp]
/--
theorem `one_lt_omega0` / 定理 `one_lt_omega0`

English:
theorem one_lt_omega0
  statement: 1 < ω
  proof: by simpa only [Nat.cast_one] using natCast_lt_omega0 1

@[simp]

中文:
定理 one_lt_omega0
  结论: 1 < ω
  证明: by simpa only [Nat.cast_one] using natCast_lt_omega0 1

@[simp]

Depends on / 依赖: Nat.cast_one, cast_one, natCast_lt_omega0
-/
theorem one_lt_omega0 : 1 < ω := by simpa only [Nat.cast_one] using natCast_lt_omega0 1

@[simp]
/--
theorem `isSuccLimit_omega0` / 定理 `isSuccLimit_omega0`

English:
theorem isSuccLimit_omega0
  statement: IsSuccLimit ω
  proof: by
  rw [isSuccLimit_iff]; rw [isSuccPrelimit_iff_succ_lt]
  refine ⟨omega0_ne_zero, fun o h => ?_⟩
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact natCast_lt_omega0 (n + 1)

中文:
定理 isSuccLimit_omega0
  结论: 是SuccLimit ω
  证明: by
  rw [isSuccLimit_iff]; rw [isSuccPrelimit_iff_succ_lt]
  refine ⟨omega0_ne_zero, fun o h => ?_⟩
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact natCast_lt_omega0 (n + 1)

Depends on / 依赖: isSuccLimit_iff, isSuccPrelimit_iff_succ_lt, lt_omega0, natCast_lt_omega0, omega0_ne_zero
-/
theorem isSuccLimit_omega0 : IsSuccLimit ω := by
  rw [isSuccLimit_iff]; rw [isSuccPrelimit_iff_succ_lt]
  refine ⟨omega0_ne_zero, fun o h => ?_⟩
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact natCast_lt_omega0 (n + 1)

/--
theorem `omega0_le` / 定理 `omega0_le`

English:
theorem omega0_le
  given: {o : Ordinal}
  statement: ω <= o ↔ forall n : Nat, ↑n <= o
  proof: ⟨fun h n => (natCast_lt_omega0 _).le.trans h, fun H =>
    le_of_forall_lt fun a h => by
      let ⟨n, e⟩ := lt_omega0.1 h
      rw [e]; rw [← succ_le_iff]; exact H (n + 1)⟩

中文:
定理 omega0_le
  条件: {o : 序数}
  结论: ω <= o ↔ 对任意 n : 自然数, ↑n <= o
  证明: ⟨fun h n => (natCast_lt_omega0 _).le.trans h, fun H =>
    le_of_forall_lt fun a h => by
      let ⟨n, e⟩ := lt_omega0.1 h
      rw [e]; rw [← succ_le_iff]; exact H (n + 1)⟩

Depends on / 依赖: le.trans, le_of_forall_lt, lt_omega0, natCast_lt_omega0, succ_le_iff
-/
theorem omega0_le {o : Ordinal} : ω <= o ↔ forall n : Nat, ↑n <= o :=
  ⟨fun h n => (natCast_lt_omega0 _).le.trans h, fun H =>
    le_of_forall_lt fun a h => by
      let ⟨n, e⟩ := lt_omega0.1 h
      rw [e]; rw [← succ_le_iff]; exact H (n + 1)⟩

/--
theorem `omega0_le_of_isSuccLimit` / 定理 `omega0_le_of_isSuccLimit`

English:
theorem omega0_le_of_isSuccLimit
  given: {o} (h : IsSuccLimit o)
  statement: ω <= o
  proof: omega0_le.2 fun n => le_of_lt natCast_lt_of_isSuccLimit h n

中文:
定理 omega0_le_of_isSuccLimit
  条件: {o} (h : 是SuccLimit o)
  结论: ω <= o
  证明: omega0_le.2 fun n => le_of_lt natCast_lt_of_isSuccLimit h n

Depends on / 依赖: le_of_lt, natCast_lt_of_isSuccLimit, omega0_le
-/
theorem omega0_le_of_isSuccLimit {o} (h : IsSuccLimit o) : ω <= o :=
omega0_le.2 fun n => le_of_lt natCast_lt_of_isSuccLimit h n

/--
theorem `natCast_add_omega0` / 定理 `natCast_add_omega0`

English:
theorem natCast_add_omega0
  given: (n : Nat)
  statement: n + ω = ω
  proof: by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) le_add_self
  obtain ⟨b, hb', hb⟩ := (lt_add_iff omega0_ne_zero).1 ha
  obtain ⟨m, rfl⟩ := lt_omega0.1 hb'
  apply hb.trans_lt
  exact_mod_cast natCast_lt_omega0 (n + m)

中文:
定理 natCast_add_omega0
  条件: (n : 自然数)
  结论: n + ω = ω
  证明: by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) le_add_self
  obtain ⟨b, hb', hb⟩ := (lt_add_iff omega0_ne_zero).1 ha
  obtain ⟨m, rfl⟩ := lt_omega0.1 hb'
  apply hb.trans_lt
  exact_mod_cast natCast_lt_omega0 (n + m)

Depends on / 依赖: hb.trans_lt, le_add_self, le_antisymm, le_of_forall_lt, lt_add_iff, lt_omega0, natCast_lt_omega0, omega0_ne_zero, trans_lt
-/
theorem natCast_add_omega0 (n : Nat) : n + ω = ω := by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) le_add_self
  obtain ⟨b, hb', hb⟩ := (lt_add_iff omega0_ne_zero).1 ha
  obtain ⟨m, rfl⟩ := lt_omega0.1 hb'
  apply hb.trans_lt
  exact_mod_cast natCast_lt_omega0 (n + m)

/--
theorem `one_add_omega0` / 定理 `one_add_omega0`

English:
theorem one_add_omega0
  statement: 1 + ω = ω
  proof: mod_cast natCast_add_omega0 1

中文:
定理 one_add_omega0
  结论: 1 + ω = ω
  证明: mod_cast natCast_add_omega0 1

Depends on / 依赖: mod_cast, natCast_add_omega0
-/
theorem one_add_omega0 : 1 + ω = ω :=
  mod_cast natCast_add_omega0 1

/--
theorem `add_omega0` / 定理 `add_omega0`

English:
theorem add_omega0
  given: {a : Ordinal} (h : a < ω)
  statement: a + ω = ω
  proof: by
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact natCast_add_omega0 n

@[simp]

中文:
定理 add_omega0
  条件: {a : 序数} (h : a < ω)
  结论: a + ω = ω
  证明: by
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact natCast_add_omega0 n

@[simp]

Depends on / 依赖: lt_omega0, natCast_add_omega0
-/
theorem add_omega0 {a : Ordinal} (h : a < ω) : a + ω = ω := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact natCast_add_omega0 n

@[simp]
/--
theorem `natCast_add_of_omega0_le` / 定理 `natCast_add_of_omega0_le`

English:
theorem natCast_add_of_omega0_le
  given: {o} (h : ω <= o) (n : Nat)
  statement: n + o = o
  proof: by
  rw [← Ordinal.add_sub_cancel_of_le h]; rw [← add_assoc]; rw [natCast_add_omega0]

@[simp]

中文:
定理 natCast_add_of_omega0_le
  条件: {o} (h : ω <= o) (n : 自然数)
  结论: n + o = o
  证明: by
  rw [← Ordinal.add_sub_cancel_of_le h]; rw [← add_assoc]; rw [natCast_add_omega0]

@[simp]

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_assoc, add_sub_cancel_of_le, natCast_add_omega0
-/
theorem natCast_add_of_omega0_le {o} (h : ω <= o) (n : Nat) : n + o = o := by
  rw [← Ordinal.add_sub_cancel_of_le h]; rw [← add_assoc]; rw [natCast_add_omega0]

@[simp]
/--
theorem `one_add_of_omega0_le` / 定理 `one_add_of_omega0_le`

English:
theorem one_add_of_omega0_le
  given: {o} (h : ω <= o)
  statement: 1 + o = o
  proof: mod_cast natCast_add_of_omega0_le h 1

中文:
定理 one_add_of_omega0_le
  条件: {o} (h : ω <= o)
  结论: 1 + o = o
  证明: mod_cast natCast_add_of_omega0_le h 1

Depends on / 依赖: mod_cast, natCast_add_of_omega0_le
-/
theorem one_add_of_omega0_le {o} (h : ω <= o) : 1 + o = o :=
  mod_cast natCast_add_of_omega0_le h 1

open Ordinal

/--
theorem `isSuccPrelimit_iff_omega0_dvd` / 定理 `isSuccPrelimit_iff_omega0_dvd`

English:
theorem isSuccPrelimit_iff_omega0_dvd
  given: {a : Ordinal}
  statement: IsSuccPrelimit a ↔ ω ∣ a
  proof: by
  refine ⟨fun l => ⟨a / ω, le_antisymm ?_ (mul_div_le _ _)⟩, fun h => ?_⟩
  · refine l.le_iff_forall_le.2 fun x hx => le_of_lt ?_
    rw [lt_mul_iff_div_lt omega0_ne_zero]; rw [← succ_le_iff]; rw [← mul_le_iff_le_div omega0_ne_zero]; rw [mul_succ]; rw [add_le_iff_of_isSuccLimit isSuccLimit_omega0]
    intro b hb
    rcases lt_omega0.1 hb with ⟨n, rfl⟩
    grw [mul_div_le]
    exact (lt_sub.1 <| natCast_lt_of_isSuccLimit (isSuccLimit_sub l hx) _).le
  · rcases h with ⟨a0, b, rfl⟩
    exact isSuccPrelimit_mul_left isSuccLimit_omega0

@[deprecated isSuccPrelimit_iff_omega0_dvd (since := "2026-02-01")]

中文:
定理 isSuccPrelimit_iff_omega0_dvd
  条件: {a : 序数}
  结论: IsSuccPrelimit a ↔ ω ∣ a
  证明: by
  refine ⟨fun l => ⟨a / ω, le_antisymm ?_ (mul_div_le _ _)⟩, fun h => ?_⟩
  · refine l.le_iff_forall_le.2 fun x hx => le_of_lt ?_
    rw [lt_mul_iff_div_lt omega0_ne_zero]; rw [← succ_le_iff]; rw [← mul_le_iff_le_div omega0_ne_zero]; rw [mul_succ]; rw [add_le_iff_of_isSuccLimit isSuccLimit_omega0]
    intro b hb
    rcases lt_omega0.1 hb with ⟨n, rfl⟩
    grw [mul_div_le]
    exact (lt_sub.1 <| natCast_lt_of_isSuccLimit (isSuccLimit_sub l hx) _).le
  · rcases h with ⟨a0, b, rfl⟩
    exact isSuccPrelimit_mul_left isSuccLimit_omega0

@[deprecated isSuccPrelimit_iff_omega0_dvd (since := "2026-02-01")]

Depends on / 依赖: MetricSpace, add_le_iff_of_isSuccLimit, isSuccLim, isSuccLimit_omega0, isSuccLimit_sub, isSuccPrelimit_mul_left, l.le_iff_forall_le, le_antisymm, le_iff_forall_le, le_of_lt, lt_mul_iff_div_lt, lt_omega0, lt_sub, mul_div_le, mul_le_iff_le_div, mul_succ, natCast_lt_of_isSuccLimit, omega0_ne_zero, succ_le_iff
-/
theorem isSuccPrelimit_iff_omega0_dvd {a : Ordinal} : IsSuccPrelimit a ↔ ω ∣ a := by
  refine ⟨fun l => ⟨a / ω, le_antisymm ?_ (mul_div_le _ _)⟩, fun h => ?_⟩
  · refine l.le_iff_forall_le.2 fun x hx => le_of_lt ?_
    rw [lt_mul_iff_div_lt omega0_ne_zero]; rw [← succ_le_iff]; rw [← mul_le_iff_le_div omega0_ne_zero]; rw [mul_succ]; rw [add_le_iff_of_isSuccLimit isSuccLimit_omega0]
    intro b hb
    rcases lt_omega0.1 hb with ⟨n, rfl⟩
    grw [mul_div_le]
    exact (lt_sub.1 <| natCast_lt_of_isSuccLimit (isSuccLimit_sub l hx) _).le
  · rcases h with ⟨a0, b, rfl⟩
    exact isSuccPrelimit_mul_left isSuccLimit_omega0

@[deprecated isSuccPrelimit_iff_omega0_dvd (since := "2026-02-01")]
/--
theorem `isSuccLimit_iff_omega0_dvd` / 定理 `isSuccLimit_iff_omega0_dvd`

English:
theorem isSuccLimit_iff_omega0_dvd
  given: {a : Ordinal}
  statement: IsSuccLimit a ↔ a != 0 ∧ ω ∣ a
  proof: by
  rw [isSuccLimit_iff]; rw [isSuccPrelimit_iff_omega0_dvd]

@[simp]

中文:
定理 isSuccLimit_iff_omega0_dvd
  条件: {a : 序数}
  结论: 是SuccLimit a ↔ a != 0 ∧ ω ∣ a
  证明: by
  rw [isSuccLimit_iff]; rw [isSuccPrelimit_iff_omega0_dvd]

@[simp]

Depends on / 依赖: isSuccLimit_iff, isSuccPrelimit_iff_omega0_dvd
-/
theorem isSuccLimit_iff_omega0_dvd {a : Ordinal} : IsSuccLimit a ↔ a != 0 ∧ ω ∣ a := by
  rw [isSuccLimit_iff]; rw [isSuccPrelimit_iff_omega0_dvd]

@[simp]
/--
theorem `natCast_mod_omega0` / 定理 `natCast_mod_omega0`

English:
theorem natCast_mod_omega0
  given: (n : Nat)
  statement: n % ω = n
  proof: mod_eq_of_lt (natCast_lt_omega0 n)

中文:
定理 natCast_mod_omega0
  条件: (n : 自然数)
  结论: n % ω = n
  证明: mod_eq_of_lt (natCast_lt_omega0 n)

Depends on / 依赖: mod_eq_of_lt, natCast_lt_omega0
-/
theorem natCast_mod_omega0 (n : Nat) : n % ω = n :=
  mod_eq_of_lt (natCast_lt_omega0 n)

end Ordinal

namespace Cardinal

open Ordinal

@[simp]
/--
theorem `add_one_of_aleph0_le` / 定理 `add_one_of_aleph0_le`

English:
theorem add_one_of_aleph0_le
  given: {c} (h : ℵ₀ <= c)
  statement: c + 1 = c
  proof: by
  rw [add_comm]; rw [← card_ord c]; rw [← card_one]; rw [← card_add]; rw [one_add_of_omega0_le]
  rwa [← ord_aleph0, ord_le_ord]

中文:
定理 add_one_of_aleph0_le
  条件: {c} (h : ℵ₀ <= c)
  结论: c + 1 = c
  证明: by
  rw [add_comm]; rw [← card_ord c]; rw [← card_one]; rw [← card_add]; rw [one_add_of_omega0_le]
  rwa [← ord_aleph0, ord_le_ord]

Depends on / 依赖: add_comm, card_add, card_one, card_ord, one_add_of_omega0_le, ord_aleph0, ord_le_ord
-/
theorem add_one_of_aleph0_le {c} (h : ℵ₀ <= c) : c + 1 = c := by
  rw [add_comm]; rw [← card_ord c]; rw [← card_one]; rw [← card_add]; rw [one_add_of_omega0_le]
  rwa [← ord_aleph0, ord_le_ord]

/--
theorem `isSuccLimit_ord` / 定理 `isSuccLimit_ord`

English:
theorem isSuccLimit_ord
  given: {c} (hc : ℵ₀ <= c)
  statement: IsSuccLimit (ord c)
  proof: by
  constructor
  · simpa using (aleph0_pos.trans_le hc).ne'
  · simp_rw [isSuccPrelimit_iff_succ_lt, succ_eq_add_one, lt_ord, card_add_one]
    refine fun a ha => ?_
    contrapose! ha
    rwa [add_one_of_aleph0_le] at ha
    rw [← ord_le]; rw [← IsSuccLimit.le_succ_iff]; rw [succ_eq_add_one]; rw [ord_le]; rw [card_add_one]
    · exact hc.trans ha
    · simp

中文:
定理 isSuccLimit_ord
  条件: {c} (hc : ℵ₀ <= c)
  结论: 是SuccLimit (ord c)
  证明: by
  constructor
  · simpa using (aleph0_pos.trans_le hc).ne'
  · simp_rw [isSuccPrelimit_iff_succ_lt, succ_eq_add_one, lt_ord, card_add_one]
    refine fun a ha => ?_
    contrapose! ha
    rwa [add_one_of_aleph0_le] at ha
    rw [← ord_le]; rw [← IsSuccLimit.le_succ_iff]; rw [succ_eq_add_one]; rw [ord_le]; rw [card_add_one]
    · exact hc.trans ha
    · simp

Depends on / 依赖: IsSuccLimit, IsSuccLimit.le_succ_iff, add_one_of_aleph0_le, aleph0_pos, aleph0_pos.trans_le, card_add_one, contrapose, hc.trans, isSuccPrelimit_iff_succ_lt, le_succ_iff, lt_ord, ord_le, simp_rw, succ_eq_add_one, trans_le
-/
theorem isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLimit (ord c) := by
  constructor
  · simpa using (aleph0_pos.trans_le hc).ne'
  · simp_rw [isSuccPrelimit_iff_succ_lt, succ_eq_add_one, lt_ord, card_add_one]
    refine fun a ha => ?_
    contrapose! ha
    rwa [add_one_of_aleph0_le] at ha
    rw [← ord_le]; rw [← IsSuccLimit.le_succ_iff]; rw [succ_eq_add_one]; rw [ord_le]; rw [card_add_one]
    · exact hc.trans ha
    · simp

-- TODO: deprecate in favor of `isSuccPrelimit_type_lt_iff`
/--
theorem `noMaxOrder` / 定理 `noMaxOrder`

English:
theorem noMaxOrder
  given: {c} (h : ℵ₀ <= c)
  statement: NoMaxOrder c.ord.ToType
  proof: by
  rw [← isSuccPrelimit_type_lt_iff]; rw [type_toType]
  exact (isSuccLimit_ord h).isSuccPrelimit

中文:
定理 noMaxOrder
  条件: {c} (h : ℵ₀ <= c)
  结论: NoMax序 c.ord.ToType
  证明: by
  rw [← isSuccPrelimit_type_lt_iff]; rw [type_toType]
  exact (isSuccLimit_ord h).isSuccPrelimit

Depends on / 依赖: isSuccLimit_ord, isSuccPrelimit, isSuccPrelimit_type_lt_iff, type_toType
-/
theorem noMaxOrder {c} (h : ℵ₀ <= c) : NoMaxOrder c.ord.ToType := by
  rw [← isSuccPrelimit_type_lt_iff]; rw [type_toType]
  exact (isSuccLimit_ord h).isSuccPrelimit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (ℵ₀ : Cardinal.{u}).ord.ToType
  body: by simp

中文:
实例 :
  签名: 非空 (ℵ₀ : 基数.{u}).ord.ToType
  定义体: by simp
-/
instance : Nonempty (ℵ₀ : Cardinal.{u}).ord.ToType := by simp

/--
Definition of `orderBotAleph0OrdToType` / `orderBotAleph0OrdToType` 的定义

English:
abbreviation orderBotAleph0OrdToType
  signature: : OrderBot Cardinal.aleph0.{u}.ord.ToType
  body: WellFoundedLT.toOrderBot _

中文:
缩写 orderBotAleph0OrdToType
  签名: : 有底序 基数.aleph0.{u}.ord.ToType
  定义体: WellFoundedLT.toOrderBot _

Depends on / 依赖: WellFoundedLT, WellFoundedLT.toOrderBot, toOrderBot
-/
abbrev orderBotAleph0OrdToType : OrderBot Cardinal.aleph0.{u}.ord.ToType :=
  WellFoundedLT.toOrderBot _

end Cardinal
