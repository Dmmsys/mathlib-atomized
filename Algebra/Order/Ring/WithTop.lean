/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Synonym
public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop

/-! # Structures involving `*` and `0` on `WithTop` and `WithBot`
The main results of this section are `WithTop.instOrderedCommSemiring` and
`WithBot.instOrderedCommSemiring`.
-/

@[expose] public section

variable {α : Type*}

namespace WithTop

variable [DecidableEq α]

section MulZeroClass
variable [MulZeroClass α] {a b : WithTop α}

/--
Instance `instMulZeroClass` / 实例 `instMulZeroClass`

English:
instance instMulZeroClass
  signature: : MulZeroClass (WithTop α) where

中文:
实例 instMulZeroClass
  签名: : 乘零类 (WithTop α) where
-/
instance instMulZeroClass : MulZeroClass (WithTop α) where
  mul
    | (a : α), (b : α) => ↑(a * b)
    | (a : α), ⊤ => if a = 0 then 0 else ⊤
    | ⊤, (b : α) => if b = 0 then 0 else ⊤
    | ⊤, ⊤ => ⊤
  mul_zero
| (a : α) => congr_arg some mul_zero _
    | ⊤ => if_pos rfl
  zero_mul
| (b : α) => congr_arg some zero_mul _
    | ⊤ => if_pos rfl

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (a b : α)
  statement: (↑(a * b) : WithTop α) = a * b
  proof: rfl

中文:
引理 coe_mul
  条件: (a b : α)
  结论: (↑(a * b) : WithTop α) = a * b
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithTop α) = a * b := rfl

/--
lemma `mul_top'` / 引理 `mul_top'`

English:
lemma mul_top'
  statement: forall (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤

中文:
引理 mul_top'
  结论: 对任意 (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤
-/
lemma mul_top' : forall (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm

/--
lemma `mul_top` / 引理 `mul_top`

English:
lemma mul_top
  given: (h : a != 0)
  statement: a * ⊤ = ⊤
  proof: by rw [mul_top', if_neg h]

中文:
引理 mul_top
  条件: (h : a != 0)
  结论: a * ⊤ = ⊤
  证明: by rw [mul_top', if_neg h]
-/
@[simp] lemma mul_top (h : a != 0) : a * ⊤ = ⊤ := by rw [mul_top', if_neg h]

/--
lemma `top_mul'` / 引理 `top_mul'`

English:
lemma top_mul'
  statement: forall (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤

中文:
引理 top_mul'
  结论: 对任意 (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤
-/
lemma top_mul' : forall (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm

/--
lemma `top_mul` / 引理 `top_mul`

English:
lemma top_mul
  given: (hb : b != 0)
  statement: ⊤ * b = ⊤
  proof: by rw [top_mul', if_neg hb]

中文:
引理 top_mul
  条件: (hb : b != 0)
  结论: ⊤ * b = ⊤
  证明: by rw [top_mul', if_neg hb]
-/
@[simp] lemma top_mul (hb : b != 0) : ⊤ * b = ⊤ := by rw [top_mul', if_neg hb]

/--
lemma `top_mul_top` / 引理 `top_mul_top`

English:
lemma top_mul_top
  statement: (⊤ * ⊤ : WithTop α) = ⊤
  proof: rfl

中文:
引理 top_mul_top
  结论: (⊤ * ⊤ : WithTop α) = ⊤
  证明: rfl
-/
@[simp] lemma top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ := rfl

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (a b : WithTop α)
  proof: by
  cases a <;> cases b <;> aesop

中文:
引理 mul_def
  条件: (a b : WithTop α)
  证明: by
  cases a <;> cases b <;> aesop
-/
lemma mul_def (a b : WithTop α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithTop.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop

/--
lemma `mul_eq_top_iff` / 引理 `mul_eq_top_iff`

English:
lemma mul_eq_top_iff
  statement: a * b = ⊤ ↔ a != 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b != 0
  proof: by rw [mul_def]; aesop

中文:
引理 mul_eq_top_iff
  结论: a * b = ⊤ ↔ a != 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b != 0
  证明: by rw [mul_def]; aesop

Depends on / 依赖: mul_def
-/
lemma mul_eq_top_iff : a * b = ⊤ ↔ a != 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b != 0 := by rw [mul_def]; aesop

/--
lemma `mul_coe_eq_bind` / 引理 `mul_coe_eq_bind`

English:
lemma mul_coe_eq_bind
  given: {b : α} (hb : b != 0)
  statement: forall a, (a * b : WithTop α) = a.bind fun a => ↑(a * b)

中文:
引理 mul_coe_eq_bind
  条件: {b : α} (hb : b != 0)
  结论: 对任意 a, (a * b : WithTop α) = a.bind fun a => ↑(a * b)
-/
lemma mul_coe_eq_bind {b : α} (hb : b != 0) : forall a, (a * b : WithTop α) = a.bind fun a => ↑(a * b)
  | ⊤ => by simp [top_mul, hb]; rfl
  | (a : α) => rfl

/--
lemma `coe_mul_eq_bind` / 引理 `coe_mul_eq_bind`

English:
lemma coe_mul_eq_bind
  given: {a : α} (ha : a != 0)
  statement: forall b, (a * b : WithTop α) = b.bind fun b => ↑(a * b)

中文:
引理 coe_mul_eq_bind
  条件: {a : α} (ha : a != 0)
  结论: 对任意 b, (a * b : WithTop α) = b.bind fun b => ↑(a * b)
-/
lemma coe_mul_eq_bind {a : α} (ha : a != 0) : forall b, (a * b : WithTop α) = b.bind fun b => ↑(a * b)
  | ⊤ => by simp [ha]; rfl
  | (b : α) => rfl

@[simp]
/--
lemma `untopD_zero_mul` / 引理 `untopD_zero_mul`

English:
lemma untopD_zero_mul
  given: (a b : WithTop α)
  statement: (a * b).untopD 0 = a.untopD 0 * b.untopD 0
  proof: by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untopD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untopD_coe, mul_zero]
  cases a; · rw [top_mul hb, untopD_top, zero_mul]
  cases b; · rw [mul_top ha, untopD_top, mul_zero]
  rw [← coe_mul]; rw [untopD_coe]; rw [untopD_coe]; rw [untopD_coe]

中文:
引理 untopD_zero_mul
  条件: (a b : WithTop α)
  结论: (a * b).untopD 0 = a.untopD 0 * b.untopD 0
  证明: by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untopD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untopD_coe, mul_zero]
  cases a; · rw [top_mul hb, untopD_top, zero_mul]
  cases b; · rw [mul_top ha, untopD_top, mul_zero]
  rw [← coe_mul]; rw [untopD_coe]; rw [untopD_coe]; rw [untopD_coe]

Depends on / 依赖: coe_mul, coe_zero, mul_top, mul_zero, top_mul, untopD_coe, untopD_top, zero_mul
-/
lemma untopD_zero_mul (a b : WithTop α) : (a * b).untopD 0 = a.untopD 0 * b.untopD 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untopD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untopD_coe, mul_zero]
  cases a; · rw [top_mul hb, untopD_top, zero_mul]
  cases b; · rw [mul_top ha, untopD_top, mul_zero]
  rw [← coe_mul]; rw [untopD_coe]; rw [untopD_coe]; rw [untopD_coe]

/--
theorem `mul_ne_top` / 定理 `mul_ne_top`

English:
theorem mul_ne_top
  given: {a b : WithTop α} (ha : a != ⊤) (hb : b != ⊤)
  statement: a * b != ⊤
  proof: by
  simp [mul_eq_top_iff, *]

中文:
定理 mul_ne_top
  条件: {a b : WithTop α} (ha : a != ⊤) (hb : b != ⊤)
  结论: a * b != ⊤
  证明: by
  simp [mul_eq_top_iff, *]

Depends on / 依赖: mul_eq_top_iff
-/
theorem mul_ne_top {a b : WithTop α} (ha : a != ⊤) (hb : b != ⊤) : a * b != ⊤ := by
  simp [mul_eq_top_iff, *]

/--
theorem `mul_lt_top` / 定理 `mul_lt_top`

English:
theorem mul_lt_top
  given: [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤)
  statement: a * b < ⊤
  proof: by
  rw [WithTop.lt_top_iff_ne_top] at *
  exact mul_ne_top ha hb

中文:
定理 mul_lt_top
  条件: [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤)
  结论: a * b < ⊤
  证明: by
  rw [WithTop.lt_top_iff_ne_top] at *
  exact mul_ne_top ha hb

Depends on / 依赖: WithTop, WithTop.lt_top_iff_ne_top, lt_top_iff_ne_top, mul_ne_top
-/
theorem mul_lt_top [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top] at *
  exact mul_ne_top ha hb

/--
Instance `instNoZeroDivisors` / 实例 `instNoZeroDivisors`

English:
instance instNoZeroDivisors
  signature: [NoZeroDivisors α]
  body: by
  refine ⟨fun h₁ => Decidable.byContradiction fun h₂ => ?_⟩
  rw [mul_def]; rw [if_neg h₂] at h₁
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, (rfl : _ = _), (rfl : _ = _), hab⟩
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))

中文:
实例 instNoZeroDivisors
  签名: [无零因子 α]
  定义体: by
  refine ⟨fun h₁ => Decidable.byContradiction fun h₂ => ?_⟩
  rw [mul_def]; rw [if_neg h₂] at h₁
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, (rfl : _ = _), (rfl : _ = _), hab⟩
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))

Depends on / 依赖: Decidable, Decidable.byContradiction, Option.mem_map, byContradiction, congr_arg, eq_zero_or_eq_zero_of_mul_eq_zero, if_neg, mul_def
-/
instance instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithTop α) := by
  refine ⟨fun h₁ => Decidable.byContradiction fun h₂ => ?_⟩
  rw [mul_def]; rw [if_neg h₂] at h₁
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, (rfl : _ = _), (rfl : _ = _), hab⟩
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))

variable [Preorder α]

/--
lemma `mul_right_strictMono` / 引理 `mul_right_strictMono`

English:
lemma mul_right_strictMono
  given: [PosMulStrictMono α] (h₀ : 0 < a) (hinf : a != ⊤)
  proof: by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, mul_top h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  exact mul_lt_mul_of_pos_left hbc h₀

中文:
引理 mul_right_strictMono
  条件: [正乘严格递增 α] (h₀ : 0 < a) (hinf : a != ⊤)
  证明: by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, mul_top h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  exact mul_lt_mul_of_pos_left hbc h₀
-/
protected lemma mul_right_strictMono [PosMulStrictMono α] (h₀ : 0 < a) (hinf : a != ⊤) :
    StrictMono (a * ·) := by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, mul_top h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  exact mul_lt_mul_of_pos_left hbc h₀

/--
lemma `mul_left_strictMono` / 引理 `mul_left_strictMono`

English:
lemma mul_left_strictMono
  given: [MulPosStrictMono α] (h₀ : 0 < a) (hinf : a != ⊤)
  proof: by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, top_mul h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  gcongr

中文:
引理 mul_left_strictMono
  条件: [乘正严格递增 α] (h₀ : 0 < a) (hinf : a != ⊤)
  证明: by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, top_mul h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  gcongr
-/
protected lemma mul_left_strictMono [MulPosStrictMono α] (h₀ : 0 < a) (hinf : a != ⊤) :
    StrictMono (· * a) := by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, top_mul h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  gcongr

end MulZeroClass

/--
Instance `instMulZeroOneClass` / 实例 `instMulZeroOneClass`

English:
instance instMulZeroOneClass
  signature: [MulZeroOneClass α] [Nontrivial α]
  body: instMulZeroClass
  one_mul
    | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, one_mul]
  mul_one
    | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, mul_one]

中文:
实例 instMulZeroOneClass
  签名: [乘零幺类 α] [非平凡 α]
  定义体: instMulZeroClass
  one_mul
    | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, one_mul]
  mul_one
    | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, mul_one]

Depends on / 依赖: instMulZeroClass
-/
instance instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithTop α) where
  __ := instMulZeroClass
  one_mul
    | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, one_mul]
  mul_one
    | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, mul_one]

/-- A version of `WithTop.map` for `MonoidWithZeroHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.MonoidWithZeroHom.withTopMap` / `_root_.MonoidWithZeroHom.withTopMap` 的定义

English:
definition _root_.MonoidWithZeroHom.withTopMap
  signature: {R S : Type*} [MulZeroOneClass R] [DecidableEq R]
  body: { f.toZeroHom.withTopMap, f.toMonoidHom.toOneHom.withTopMap with
    toFun := WithTop.map f
    map_mul' := fun x y => by
      have : forall z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.toZeroHom.withTopMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      cases x with | top => simp [hy, this] | coe x => ?_
      cases y with
      | top =>
        have : (f x : WithTop S) != 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [mul_top hx, mul_top this]
      | coe y => simp [← coe_mul] }

中文:
定义 _root_.带零幺半群态射.withTopMap
  签名: {R S : 类型} [乘零幺类 R] [DecidableEq R]
  定义体: { f.toZeroHom.withTopMap, f.toMonoidHom.toOneHom.withTopMap with
    toFun := WithTop.map f
    map_mul' := fun x y => by
      have : forall z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.toZeroHom.withTopMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      cases x with | top => simp [hy, this] | coe x => ?_
      cases y with
      | top =>
        have : (f x : WithTop S) != 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [mul_top hx, mul_top this]
      | coe y => simp [← coe_mul] }
-/
protected def _root_.MonoidWithZeroHom.withTopMap {R S : Type*} [MulZeroOneClass R] [DecidableEq R]
    [Nontrivial R] [MulZeroOneClass S] [DecidableEq S] [Nontrivial S] (f : R ->*₀ S)
    (hf : Function.Injective f) : WithTop R ->*₀ WithTop S :=
  { f.toZeroHom.withTopMap, f.toMonoidHom.toOneHom.withTopMap with
    toFun := WithTop.map f
    map_mul' := fun x y => by
      have : forall z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.toZeroHom.withTopMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      cases x with | top => simp [hy, this] | coe x => ?_
      cases y with
      | top =>
        have : (f x : WithTop S) != 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [mul_top hx, mul_top this]
      | coe y => simp [← coe_mul] }

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: [SemigroupWithZero α] [NoZeroDivisors α]
  body: instMulZeroClass
  mul_assoc a b c := by
    rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
    rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
    rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
    cases a with | top => simp [hb, hc] | coe a => ?_
    cases b with | top => simp [mul_top ha, top_mul hc] | coe b => ?_
    cases c with
    | top =>
      rw [mul_top hb]; rw [mul_top ha]
      rw [← coe_zero]; rw [ne_eq]; rw [coe_eq_coe] at ha hb
      simp [ha, hb]
    | coe c => simp only [← coe_mul, mul_assoc]

中文:
实例 instSemigroupWithZero
  签名: [带零半群 α] [无零因子 α]
  定义体: instMulZeroClass
  mul_assoc a b c := by
    rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
    rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
    rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
    cases a with | top => simp [hb, hc] | coe a => ?_
    cases b with | top => simp [mul_top ha, top_mul hc] | coe b => ?_
    cases c with
    | top =>
      rw [mul_top hb]; rw [mul_top ha]
      rw [← coe_zero]; rw [ne_eq]; rw [coe_eq_coe] at ha hb
      simp [ha, hb]
    | coe c => simp only [← coe_mul, mul_assoc]

Depends on / 依赖: instMulZeroClass
-/
instance instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] :
    SemigroupWithZero (WithTop α) where
  __ := instMulZeroClass
  mul_assoc a b c := by
    rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
    rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
    rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
    cases a with | top => simp [hb, hc] | coe a => ?_
    cases b with | top => simp [mul_top ha, top_mul hc] | coe b => ?_
    cases c with
    | top =>
      rw [mul_top hb]; rw [mul_top ha]
      rw [← coe_zero]; rw [ne_eq]; rw [coe_eq_coe] at ha hb
      simp [ha, hb]
    | coe c => simp only [← coe_mul, mul_assoc]

section MonoidWithZero
variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] {x : WithTop α} {n : Nat}

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: : MonoidWithZero (WithTop α) where
  body: instMulZeroOneClass
  __ := instSemigroupWithZero
  npow n a := match a, n with
    | (a : α), n => ↑(a ^ n)
    | ⊤, 0 => 1
    | ⊤, _n + 1 => ⊤
  npow_zero a := by simp_rw [HPow.hPow, Pow.pow]; cases a <;> simp
  npow_succ n a := by simp_rw [HPow.hPow, Pow.pow]; cases n <;> cases a <;> simp [pow_succ]

中文:
实例 instMonoidWithZero
  签名: : 带零幺半群 (WithTop α) where
  定义体: instMulZeroOneClass
  __ := instSemigroupWithZero
  npow n a := match a, n with
    | (a : α), n => ↑(a ^ n)
    | ⊤, 0 => 1
    | ⊤, _n + 1 => ⊤
  npow_zero a := by simp_rw [HPow.hPow, Pow.pow]; cases a <;> simp
  npow_succ n a := by simp_rw [HPow.hPow, Pow.pow]; cases n <;> cases a <;> simp [pow_succ]

Depends on / 依赖: instMulZeroOneClass
-/
instance instMonoidWithZero : MonoidWithZero (WithTop α) where
  __ := instMulZeroOneClass
  __ := instSemigroupWithZero
  npow n a := match a, n with
    | (a : α), n => ↑(a ^ n)
    | ⊤, 0 => 1
    | ⊤, _n + 1 => ⊤
  npow_zero a := by simp_rw [HPow.hPow, Pow.pow]; cases a <;> simp
  npow_succ n a := by simp_rw [HPow.hPow, Pow.pow]; cases n <;> cases a <;> simp [pow_succ]

/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (a : α) (n : Nat)
  statement: (↑(a ^ n) : WithTop α) = a ^ n
  proof: rfl

中文:
引理 coe_pow
  条件: (a : α) (n : 自然数)
  结论: (↑(a ^ n) : WithTop α) = a ^ n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_pow (a : α) (n : Nat) : (↑(a ^ n) : WithTop α) = a ^ n := rfl

/--
lemma `top_pow` / 引理 `top_pow`

English:
lemma top_pow
  statement: forall {n : Nat}, n != 0 -> (⊤ : WithTop α) ^ n = ⊤ | _ + 1, _ => rfl

中文:
引理 top_pow
  结论: 对任意 {n : 自然数}, n != 0 -> (⊤ : WithTop α) ^ n = ⊤ | _ + 1, _ => rfl
-/
@[simp] lemma top_pow : forall {n : Nat}, n != 0 -> (⊤ : WithTop α) ^ n = ⊤ | _ + 1, _ => rfl

/--
lemma `pow_eq_top_iff` / 引理 `pow_eq_top_iff`

English:
lemma pow_eq_top_iff
  statement: x ^ n = ⊤ ↔ x = ⊤ ∧ n != 0
  proof: by
  cases x <;> cases n <;> simp [← coe_pow]

中文:
引理 pow_eq_top_iff
  结论: x ^ n = ⊤ ↔ x = ⊤ ∧ n != 0
  证明: by
  cases x <;> cases n <;> simp [← coe_pow]
-/
@[simp] lemma pow_eq_top_iff : x ^ n = ⊤ ↔ x = ⊤ ∧ n != 0 := by
  cases x <;> cases n <;> simp [← coe_pow]

/--
lemma `pow_ne_top_iff` / 引理 `pow_ne_top_iff`

English:
lemma pow_ne_top_iff
  statement: x ^ n != ⊤ ↔ x != ⊤ ∨ n = 0
  proof: by simp [pow_eq_top_iff, or_iff_not_imp_left]

中文:
引理 pow_ne_top_iff
  结论: x ^ n != ⊤ ↔ x != ⊤ ∨ n = 0
  证明: by simp [pow_eq_top_iff, or_iff_not_imp_left]

Depends on / 依赖: or_iff_not_imp_left, pow_eq_top_iff
-/
lemma pow_ne_top_iff : x ^ n != ⊤ ↔ x != ⊤ ∨ n = 0 := by simp [pow_eq_top_iff, or_iff_not_imp_left]

/--
lemma `pow_lt_top_iff` / 引理 `pow_lt_top_iff`

English:
lemma pow_lt_top_iff
  given: [Preorder α]
  statement: x ^ n < ⊤ ↔ x < ⊤ ∨ n = 0
  proof: by
  simp_rw [WithTop.lt_top_iff_ne_top, pow_ne_top_iff]

中文:
引理 pow_lt_top_iff
  条件: [预序 α]
  结论: x ^ n < ⊤ ↔ x < ⊤ ∨ n = 0
  证明: by
  simp_rw [WithTop.lt_top_iff_ne_top, pow_ne_top_iff]
-/
@[simp] lemma pow_lt_top_iff [Preorder α] : x ^ n < ⊤ ↔ x < ⊤ ∨ n = 0 := by
  simp_rw [WithTop.lt_top_iff_ne_top, pow_ne_top_iff]

/--
lemma `eq_top_of_pow` / 引理 `eq_top_of_pow`

English:
lemma eq_top_of_pow
  given: (n : Nat) (hx : x ^ n = ⊤)
  statement: x = ⊤
  proof: (pow_eq_top_iff.1 hx).1

中文:
引理 eq_top_of_pow
  条件: (n : 自然数) (hx : x ^ n = ⊤)
  结论: x = ⊤
  证明: (pow_eq_top_iff.1 hx).1

Depends on / 依赖: pow_eq_top_iff
-/
lemma eq_top_of_pow (n : Nat) (hx : x ^ n = ⊤) : x = ⊤ := (pow_eq_top_iff.1 hx).1
/--
lemma `pow_ne_top` / 引理 `pow_ne_top`

English:
lemma pow_ne_top
  given: (hx : x != ⊤)
  statement: x ^ n != ⊤
  proof: pow_ne_top_iff.2 .inl hx

中文:
引理 pow_ne_top
  条件: (hx : x != ⊤)
  结论: x ^ n != ⊤
  证明: pow_ne_top_iff.2 .inl hx

Depends on / 依赖: pow_ne_top_iff
-/
lemma pow_ne_top (hx : x != ⊤) : x ^ n != ⊤ := pow_ne_top_iff.2 .inl hx
/--
lemma `pow_lt_top` / 引理 `pow_lt_top`

English:
lemma pow_lt_top
  given: [Preorder α] (hx : x < ⊤)
  statement: x ^ n < ⊤
  proof: pow_lt_top_iff.2 .inl hx

中文:
引理 pow_lt_top
  条件: [预序 α] (hx : x < ⊤)
  结论: x ^ n < ⊤
  证明: pow_lt_top_iff.2 .inl hx

Depends on / 依赖: pow_lt_top_iff
-/
lemma pow_lt_top [Preorder α] (hx : x < ⊤) : x ^ n < ⊤ := pow_lt_top_iff.2 .inl hx

end MonoidWithZero

/--
Instance `instCommMonoidWithZero` / 实例 `instCommMonoidWithZero`

English:
instance instCommMonoidWithZero
  signature: [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α]
  body: instMonoidWithZero
  mul_comm a b := by simp_rw [mul_def]; exact if_congr or_comm rfl (Option.map₂_comm mul_comm)

中文:
实例 instCommMonoidWithZero
  签名: [带零交换幺半群 α] [无零因子 α] [非平凡 α]
  定义体: instMonoidWithZero
  mul_comm a b := by simp_rw [mul_def]; exact if_congr or_comm rfl (Option.map₂_comm mul_comm)

Depends on / 依赖: instMonoidWithZero
-/
instance instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) where
  __ := instMonoidWithZero
  mul_comm a b := by simp_rw [mul_def]; exact if_congr or_comm rfl (Option.map₂_comm mul_comm)

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring α] [PartialOrder α]
  body: WithTop.addCommMonoid
  __ := WithTop.instMulZeroClass
  right_distrib a b c := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [mul_coe_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (add_mul _ _ _)
  left_distrib c a b := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [coe_mul_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (mul_add _ _ _)

中文:
实例 instNonUnitalNonAssocSemiring
  签名: [非幺非结合半环 α] [偏序 α]
  定义体: WithTop.addCommMonoid
  __ := WithTop.instMulZeroClass
  right_distrib a b c := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [mul_coe_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (add_mul _ _ _)
  left_distrib c a b := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [coe_mul_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (mul_add _ _ _)

Depends on / 依赖: WithTop, WithTop.addCommMonoid, addCommMonoid
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α] : NonUnitalNonAssocSemiring (WithTop α) where
  toAddCommMonoid := WithTop.addCommMonoid
  __ := WithTop.instMulZeroClass
  right_distrib a b c := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [mul_coe_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (add_mul _ _ _)
  left_distrib c a b := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [coe_mul_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (mul_add _ _ _)

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: [NonAssocSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
  body: instNonUnitalNonAssocSemiring
  __ := WithTop.instMulZeroOneClass
  __ := WithTop.addCommMonoidWithOne

中文:
实例 instNonAssocSemiring
  签名: [非结合半环 α] [偏序 α] [典范有序加法 α]
  定义体: instNonUnitalNonAssocSemiring
  __ := WithTop.instMulZeroOneClass
  __ := WithTop.addCommMonoidWithOne

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonAssocSemiring [NonAssocSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [Nontrivial α] : NonAssocSemiring (WithTop α) where
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := WithTop.instMulZeroOneClass
  __ := WithTop.addCommMonoidWithOne

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: [NonUnitalSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
  body: WithTop.instNonUnitalNonAssocSemiring
  __ := WithTop.instSemigroupWithZero

中文:
实例 instNonUnitalSemiring
  签名: [非幺半环 α] [偏序 α] [典范有序加法 α]
  定义体: WithTop.instNonUnitalNonAssocSemiring
  __ := WithTop.instSemigroupWithZero

Depends on / 依赖: WithTop, WithTop.instNonUnitalNonAssocSemiring, instNonUnitalNonAssocSemiring
-/
instance instNonUnitalSemiring [NonUnitalSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] : NonUnitalSemiring (WithTop α) where
  toNonUnitalNonAssocSemiring := WithTop.instNonUnitalNonAssocSemiring
  __ := WithTop.instSemigroupWithZero

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [Semiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
  body: WithTop.instNonUnitalSemiring
  __ := WithTop.instMonoidWithZero
  __ := WithTop.addCommMonoidWithOne

中文:
实例 instSemiring
  签名: [半环 α] [偏序 α] [典范有序加法 α]
  定义体: WithTop.instNonUnitalSemiring
  __ := WithTop.instMonoidWithZero
  __ := WithTop.addCommMonoidWithOne

Depends on / 依赖: WithTop, WithTop.instNonUnitalSemiring, instNonUnitalSemiring
-/
instance instSemiring [Semiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] : Semiring (WithTop α) where
  toNonUnitalSemiring := WithTop.instNonUnitalSemiring
  __ := WithTop.instMonoidWithZero
  __ := WithTop.addCommMonoidWithOne

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
  body: WithTop.instSemiring
  __ := WithTop.instCommMonoidWithZero

中文:
实例 instCommSemiring
  签名: [交换半环 α] [偏序 α] [典范有序加法 α]
  定义体: WithTop.instSemiring
  __ := WithTop.instCommMonoidWithZero

Depends on / 依赖: WithTop, WithTop.instSemiring, instSemiring
-/
instance instCommSemiring [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] : CommSemiring (WithTop α) where
  toSemiring := WithTop.instSemiring
  __ := WithTop.instCommMonoidWithZero

/--
Instance `instIsOrderedRing` / 实例 `instIsOrderedRing`

English:
instance instIsOrderedRing
  signature: [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
  body: CanonicallyOrderedAdd.toIsOrderedRing

中文:
实例 instIsOrderedRing
  签名: [交换半环 α] [偏序 α] [典范有序加法 α]
  定义体: CanonicallyOrderedAdd.toIsOrderedRing

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.toIsOrderedRing, toIsOrderedRing
-/
instance instIsOrderedRing [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] : IsOrderedRing (WithTop α) :=
  CanonicallyOrderedAdd.toIsOrderedRing

/-- A version of `WithTop.map` for `RingHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.RingHom.withTopMap` / `_root_.RingHom.withTopMap` 的定义

English:
definition _root_.RingHom.withTopMap
  signature: {R S : Type*}
  body: { MonoidWithZeroHom.withTopMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.withTopMap with }

中文:
定义 _root_.环态射.withTopMap
  签名: {R S : 类型}
  定义体: { MonoidWithZeroHom.withTopMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.withTopMap with }
-/
protected def _root_.RingHom.withTopMap {R S : Type*}
    [NonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
    [DecidableEq R] [Nontrivial R]
    [NonAssocSemiring S] [PartialOrder S] [CanonicallyOrderedAdd S]
    [DecidableEq S] [Nontrivial S]
    (f : R ->+* S) (hf : Function.Injective f) : WithTop R ->+* WithTop S :=
  { MonoidWithZeroHom.withTopMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.withTopMap with }

variable [CommSemiring α] [PartialOrder α] [OrderBot α]
  [CanonicallyOrderedAdd α] [PosMulStrictMono α]
  {a a₁ a₂ b₁ b₂ : WithTop α}

@[gcongr]
/--
lemma `mul_lt_mul` / 引理 `mul_lt_mul`

English:
lemma mul_lt_mul
  given: (ha : a₁ < a₂) (hb : b₁ < b₂)
  statement: a₁ * b₁ < a₂ * b₂
  proof: by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  lift a₁ to α using ha.lt_top.ne
  lift b₁ to α using hb.lt_top.ne
  obtain rfl | ha₂ := eq_or_ne a₂ ⊤
  · rw [top_mul (by simpa [bot_eq_zero] using hb.bot_lt.ne')]
    exact coe_lt_top _
  obtain rfl | hb₂ := eq_or_ne b₂ ⊤
  · rw [mul_top (by simpa [bot_eq_zero] using ha.bot_lt.ne')]
    exact coe_lt_top _
  lift a₂ to α using ha₂
  lift b₂ to α using hb₂
  norm_cast at *
  exact CanonicallyOrderedAdd.mul_lt_mul_of_lt_of_lt ha hb

中文:
引理 mul_lt_mul
  条件: (ha : a₁ < a₂) (hb : b₁ < b₂)
  结论: a₁ * b₁ < a₂ * b₂
  证明: by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  lift a₁ to α using ha.lt_top.ne
  lift b₁ to α using hb.lt_top.ne
  obtain rfl | ha₂ := eq_or_ne a₂ ⊤
  · rw [top_mul (by simpa [bot_eq_zero] using hb.bot_lt.ne')]
    exact coe_lt_top _
  obtain rfl | hb₂ := eq_or_ne b₂ ⊤
  · rw [mul_top (by simpa [bot_eq_zero] using ha.bot_lt.ne')]
    exact coe_lt_top _
  lift a₂ to α using ha₂
  lift b₂ to α using hb₂
  norm_cast at *
  exact CanonicallyOrderedAdd.mul_lt_mul_of_lt_of_lt ha hb
-/
protected lemma mul_lt_mul (ha : a₁ < a₂) (hb : b₁ < b₂) : a₁ * b₁ < a₂ * b₂ := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  lift a₁ to α using ha.lt_top.ne
  lift b₁ to α using hb.lt_top.ne
  obtain rfl | ha₂ := eq_or_ne a₂ ⊤
  · rw [top_mul (by simpa [bot_eq_zero] using hb.bot_lt.ne')]
    exact coe_lt_top _
  obtain rfl | hb₂ := eq_or_ne b₂ ⊤
  · rw [mul_top (by simpa [bot_eq_zero] using ha.bot_lt.ne')]
    exact coe_lt_top _
  lift a₂ to α using ha₂
  lift b₂ to α using hb₂
  norm_cast at *
  exact CanonicallyOrderedAdd.mul_lt_mul_of_lt_of_lt ha hb

variable [NoZeroDivisors α] [Nontrivial α] {a b : WithTop α}

/--
lemma `pow_right_strictMono` / 引理 `pow_right_strictMono`

English:
lemma pow_right_strictMono
  statement: forall {n : Nat}, n != 0 -> StrictMono fun a : WithTop α => a ^ n

中文:
引理 pow_right_strictMono
  结论: 对任意 {n : 自然数}, n != 0 -> 严格递增 fun a : WithTop α => a ^ n
-/
protected lemma pow_right_strictMono : forall {n : Nat}, n != 0 -> StrictMono fun a : WithTop α => a ^ n
  | 0, h => absurd rfl h
  | 1, _ => by simpa only [pow_one] using! strictMono_id
  | n + 2, _ => fun x y h => by
    simp_rw [pow_succ _ (n + 1)]
    exact WithTop.mul_lt_mul (WithTop.pow_right_strictMono n.succ_ne_zero h) h

/--
lemma `pow_lt_pow_left` / 引理 `pow_lt_pow_left`

English:
lemma pow_lt_pow_left
  given: (hab : a < b) {n : Nat} (hn : n != 0)
  statement: a ^ n < b ^ n
  proof: WithTop.pow_right_strictMono hn hab

中文:
引理 pow_lt_pow_left
  条件: (hab : a < b) {n : 自然数} (hn : n != 0)
  结论: a ^ n < b ^ n
  证明: WithTop.pow_right_strictMono hn hab
-/
@[gcongr] protected lemma pow_lt_pow_left (hab : a < b) {n : Nat} (hn : n != 0) : a ^ n < b ^ n :=
  WithTop.pow_right_strictMono hn hab

end WithTop

namespace WithBot

variable [DecidableEq α]

section MulZeroClass
variable [MulZeroClass α] {a b : WithBot α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulZeroClass (WithBot α)
  body: inferInstanceAs MulZeroClass (WithTop α)

中文:
实例 :
  签名: 乘零类 (WithBot α)
  定义体: inferInstanceAs MulZeroClass (WithTop α)

Depends on / 依赖: MulZeroClass, WithTop
-/
instance : MulZeroClass (WithBot α) := inferInstanceAs MulZeroClass (WithTop α)

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (a b : α)
  statement: (↑(a * b) : WithBot α) = a * b
  proof: rfl

中文:
引理 coe_mul
  条件: (a b : α)
  结论: (↑(a * b) : WithBot α) = a * b
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithBot α) = a * b := rfl

/--
lemma `mul_bot'` / 引理 `mul_bot'`

English:
lemma mul_bot'
  statement: forall (a : WithBot α), a * ⊥ = if a = 0 then 0 else ⊥

中文:
引理 mul_bot'
  结论: 对任意 (a : WithBot α), a * ⊥ = if a = 0 then 0 else ⊥
-/
lemma mul_bot' : forall (a : WithBot α), a * ⊥ = if a = 0 then 0 else ⊥
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm

/--
lemma `mul_bot` / 引理 `mul_bot`

English:
lemma mul_bot
  given: (h : a != 0)
  statement: a * ⊥ = ⊥
  proof: by rw [mul_bot', if_neg h]

中文:
引理 mul_bot
  条件: (h : a != 0)
  结论: a * ⊥ = ⊥
  证明: by rw [mul_bot', if_neg h]
-/
@[simp] lemma mul_bot (h : a != 0) : a * ⊥ = ⊥ := by rw [mul_bot', if_neg h]

/--
lemma `bot_mul'` / 引理 `bot_mul'`

English:
lemma bot_mul'
  statement: forall (b : WithBot α), ⊥ * b = if b = 0 then 0 else ⊥

中文:
引理 bot_mul'
  结论: 对任意 (b : WithBot α), ⊥ * b = if b = 0 then 0 else ⊥
-/
lemma bot_mul' : forall (b : WithBot α), ⊥ * b = if b = 0 then 0 else ⊥
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm

/--
lemma `bot_mul` / 引理 `bot_mul`

English:
lemma bot_mul
  given: (hb : b != 0)
  statement: ⊥ * b = ⊥
  proof: by rw [bot_mul', if_neg hb]

中文:
引理 bot_mul
  条件: (hb : b != 0)
  结论: ⊥ * b = ⊥
  证明: by rw [bot_mul', if_neg hb]
-/
@[simp] lemma bot_mul (hb : b != 0) : ⊥ * b = ⊥ := by rw [bot_mul', if_neg hb]

/--
lemma `bot_mul_bot` / 引理 `bot_mul_bot`

English:
lemma bot_mul_bot
  statement: (⊥ * ⊥ : WithBot α) = ⊥
  proof: rfl

中文:
引理 bot_mul_bot
  结论: (⊥ * ⊥ : WithBot α) = ⊥
  证明: rfl
-/
@[simp] lemma bot_mul_bot : (⊥ * ⊥ : WithBot α) = ⊥ := rfl

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (a b : WithBot α)
  proof: by
  cases a <;> cases b <;> aesop

中文:
引理 mul_def
  条件: (a b : WithBot α)
  证明: by
  cases a <;> cases b <;> aesop
-/
lemma mul_def (a b : WithBot α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithBot.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop

/--
lemma `mul_eq_bot_iff` / 引理 `mul_eq_bot_iff`

English:
lemma mul_eq_bot_iff
  statement: a * b = ⊥ ↔ a != 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b != 0
  proof: by rw [mul_def]; aesop

中文:
引理 mul_eq_bot_iff
  结论: a * b = ⊥ ↔ a != 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b != 0
  证明: by rw [mul_def]; aesop

Depends on / 依赖: mul_def
-/
lemma mul_eq_bot_iff : a * b = ⊥ ↔ a != 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b != 0 := by rw [mul_def]; aesop

/--
lemma `mul_coe_eq_bind` / 引理 `mul_coe_eq_bind`

English:
lemma mul_coe_eq_bind
  given: {b : α} (hb : b != 0)
  statement: forall a, (a * b : WithBot α) = a.bind fun a => ↑(a * b)

中文:
引理 mul_coe_eq_bind
  条件: {b : α} (hb : b != 0)
  结论: 对任意 a, (a * b : WithBot α) = a.bind fun a => ↑(a * b)
-/
lemma mul_coe_eq_bind {b : α} (hb : b != 0) : forall a, (a * b : WithBot α) = a.bind fun a => ↑(a * b)
  | ⊥ => by simp only [ne_eq, coe_eq_zero, hb, not_false_eq_true, bot_mul]; rfl
  | (a : α) => rfl

/--
lemma `coe_mul_eq_bind` / 引理 `coe_mul_eq_bind`

English:
lemma coe_mul_eq_bind
  given: {a : α} (ha : a != 0)
  statement: forall b, (a * b : WithBot α) = b.bind fun b => ↑(a * b)

中文:
引理 coe_mul_eq_bind
  条件: {a : α} (ha : a != 0)
  结论: 对任意 b, (a * b : WithBot α) = b.bind fun b => ↑(a * b)
-/
lemma coe_mul_eq_bind {a : α} (ha : a != 0) : forall b, (a * b : WithBot α) = b.bind fun b => ↑(a * b)
  | ⊥ => by simp only [ne_eq, coe_eq_zero, ha, not_false_eq_true, mul_bot]; rfl
  | (b : α) => rfl

@[simp]
/--
lemma `unbotD_zero_mul` / 引理 `unbotD_zero_mul`

English:
lemma unbotD_zero_mul
  given: (a b : WithBot α)
  statement: (a * b).unbotD 0 = a.unbotD 0 * b.unbotD 0
  proof: by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, unbotD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, unbotD_coe, mul_zero]
  cases a; · rw [bot_mul hb, unbotD_bot, zero_mul]
  cases b; · rw [mul_bot ha, unbotD_bot, mul_zero]
  rw [← coe_mul]; rw [unbotD_coe]; rw [unbotD_coe]; rw [unbotD_coe]

中文:
引理 unbotD_zero_mul
  条件: (a b : WithBot α)
  结论: (a * b).unbotD 0 = a.unbotD 0 * b.unbotD 0
  证明: by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, unbotD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, unbotD_coe, mul_zero]
  cases a; · rw [bot_mul hb, unbotD_bot, zero_mul]
  cases b; · rw [mul_bot ha, unbotD_bot, mul_zero]
  rw [← coe_mul]; rw [unbotD_coe]; rw [unbotD_coe]; rw [unbotD_coe]

Depends on / 依赖: bot_mul, coe_mul, coe_zero, mul_bot, mul_zero, unbotD_bot, unbotD_coe, zero_mul
-/
lemma unbotD_zero_mul (a b : WithBot α) : (a * b).unbotD 0 = a.unbotD 0 * b.unbotD 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, unbotD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, unbotD_coe, mul_zero]
  cases a; · rw [bot_mul hb, unbotD_bot, zero_mul]
  cases b; · rw [mul_bot ha, unbotD_bot, mul_zero]
  rw [← coe_mul]; rw [unbotD_coe]; rw [unbotD_coe]; rw [unbotD_coe]

/--
theorem `mul_ne_bot` / 定理 `mul_ne_bot`

English:
theorem mul_ne_bot
  given: {a b : WithBot α} (ha : a != ⊥) (hb : b != ⊥)
  statement: a * b != ⊥
  proof: WithTop.mul_ne_top (α := αᵒᵈ) ha hb

中文:
定理 mul_ne_bot
  条件: {a b : WithBot α} (ha : a != ⊥) (hb : b != ⊥)
  结论: a * b != ⊥
  证明: WithTop.mul_ne_top (α := αᵒᵈ) ha hb

Depends on / 依赖: WithTop, WithTop.mul_ne_top, mul_ne_top
-/
theorem mul_ne_bot {a b : WithBot α} (ha : a != ⊥) (hb : b != ⊥) : a * b != ⊥ :=
  WithTop.mul_ne_top (α := αᵒᵈ) ha hb

/--
theorem `bot_lt_mul` / 定理 `bot_lt_mul`

English:
theorem bot_lt_mul
  given: [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b)
  statement: ⊥ < a * b
  proof: WithTop.mul_lt_top (α := αᵒᵈ) ha hb

中文:
定理 bot_lt_mul
  条件: [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b)
  结论: ⊥ < a * b
  证明: WithTop.mul_lt_top (α := αᵒᵈ) ha hb

Depends on / 依赖: WithTop, WithTop.mul_lt_top, mul_lt_top
-/
theorem bot_lt_mul [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
  WithTop.mul_lt_top (α := αᵒᵈ) ha hb

/--
Instance `instNoZeroDivisors` / 实例 `instNoZeroDivisors`

English:
instance instNoZeroDivisors
  signature: [NoZeroDivisors α]
  body: inferInstanceAs NoZeroDivisors (WithTop α)

中文:
实例 instNoZeroDivisors
  签名: [无零因子 α]
  定义体: inferInstanceAs NoZeroDivisors (WithTop α)

Depends on / 依赖: NoZeroDivisors, WithTop
-/
instance instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithBot α) :=
inferInstanceAs NoZeroDivisors (WithTop α)

end MulZeroClass

/--
Instance `instMulZeroOneClass` / 实例 `instMulZeroOneClass`

English:
instance instMulZeroOneClass
  signature: [MulZeroOneClass α] [Nontrivial α]
  body: inferInstanceAs MulZeroOneClass (WithTop α)

中文:
实例 instMulZeroOneClass
  签名: [乘零幺类 α] [非平凡 α]
  定义体: inferInstanceAs MulZeroOneClass (WithTop α)

Depends on / 依赖: MulZeroOneClass, WithTop
-/
instance instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithBot α) :=
inferInstanceAs MulZeroOneClass (WithTop α)

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: [SemigroupWithZero α] [NoZeroDivisors α]
  body: inferInstanceAs SemigroupWithZero (WithTop α)

中文:
实例 instSemigroupWithZero
  签名: [带零半群 α] [无零因子 α]
  定义体: inferInstanceAs SemigroupWithZero (WithTop α)

Depends on / 依赖: SemigroupWithZero, WithTop
-/
instance instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] :
    SemigroupWithZero (WithBot α) :=
inferInstanceAs SemigroupWithZero (WithTop α)

section MonoidWithZero
variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α]

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: : MonoidWithZero (WithBot α)
  body: inferInstanceAs MonoidWithZero (WithTop α)

中文:
实例 instMonoidWithZero
  签名: : 带零幺半群 (WithBot α)
  定义体: inferInstanceAs MonoidWithZero (WithTop α)

Depends on / 依赖: MonoidWithZero, WithTop
-/
instance instMonoidWithZero : MonoidWithZero (WithBot α) :=
inferInstanceAs MonoidWithZero (WithTop α)

/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (a : α) (n : Nat)
  statement: (↑(a ^ n) : WithBot α) = a ^ n
  proof: rfl

中文:
引理 coe_pow
  条件: (a : α) (n : 自然数)
  结论: (↑(a ^ n) : WithBot α) = a ^ n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_pow (a : α) (n : Nat) : (↑(a ^ n) : WithBot α) = a ^ n := rfl

end MonoidWithZero

/--
Instance `instCommMonoidWithZero` / 实例 `instCommMonoidWithZero`

English:
instance instCommMonoidWithZero
  signature: [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α]
  body: inferInstanceAs CommMonoidWithZero (WithTop α)

中文:
实例 instCommMonoidWithZero
  签名: [带零交换幺半群 α] [无零因子 α] [非平凡 α]
  定义体: inferInstanceAs CommMonoidWithZero (WithTop α)

Depends on / 依赖: CommMonoidWithZero, WithTop
-/
instance instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithBot α) :=
inferInstanceAs CommMonoidWithZero (WithTop α)

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
  body: inferInstanceAs CommSemiring (WithTop α)

中文:
实例 instCommSemiring
  签名: [交换半环 α] [偏序 α] [典范有序加法 α]
  定义体: inferInstanceAs CommSemiring (WithTop α)

Depends on / 依赖: CommSemiring, WithTop
-/
instance instCommSemiring [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] :
    CommSemiring (WithBot α) :=
inferInstanceAs CommSemiring (WithTop α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] [Preorder α] [PosMulMono α] : PosMulMono (WithBot α) where
  body: by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [mul_bot x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_left h x0

中文:
实例 [乘零类
  签名: α] [预序 α] [正乘递增 α] : 正乘递增 (WithBot α) where
  定义体: by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [mul_bot x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_left h x0

Depends on / 依赖: WithBot, WithBot.bot_lt_coe, absurd, bot_le, bot_lt_coe, coe_le_coe, coe_mul, eq_or_ne, mul_bot, mul_le_mul_of_nonneg_left, not_ge, simp_rw
-/
instance [MulZeroClass α] [Preorder α] [PosMulMono α] : PosMulMono (WithBot α) where
  mul_le_mul_of_nonneg_left x x0 a b h := by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [mul_bot x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_left h x0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] [Preorder α] [MulPosMono α] : MulPosMono (WithBot α) where
  body: by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [bot_mul x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_right h x0

中文:
实例 [乘零类
  签名: α] [预序 α] [乘正递增 α] : 乘正递增 (WithBot α) where
  定义体: by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [bot_mul x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_right h x0

Depends on / 依赖: WithBot, WithBot.bot_lt_coe, absurd, bot_le, bot_lt_coe, bot_mul, coe_le_coe, coe_mul, eq_or_ne, mul_le_mul_of_nonneg_right, not_ge, simp_rw
-/
instance [MulZeroClass α] [Preorder α] [MulPosMono α] : MulPosMono (WithBot α) where
  mul_le_mul_of_nonneg_right x x0 a b h := by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [bot_mul x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_right h x0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] [Preorder α] [PosMulStrictMono α] : PosMulStrictMono (WithBot α) where
  body: by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact mul_lt_mul_of_pos_left h x0

中文:
实例 [乘零类
  签名: α] [预序 α] [正乘严格递增 α] : 正乘严格递增 (WithBot α) where
  定义体: by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact mul_lt_mul_of_pos_left h x0

Depends on / 依赖: absurd, bot_lt_coe, coe_lt_coe, coe_mul, mul_bot, mul_lt_mul_of_pos_left, ne_bot, not_lt_bot, simp_rw, x0.ne.symm, x0.ne_bot
-/
instance [MulZeroClass α] [Preorder α] [PosMulStrictMono α] : PosMulStrictMono (WithBot α) where
  mul_lt_mul_of_pos_left x x0 a b h := by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact mul_lt_mul_of_pos_left h x0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] [Preorder α] [MulPosStrictMono α] : MulPosStrictMono (WithBot α) where
  body: by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    gcongr

中文:
实例 [乘零类
  签名: α] [预序 α] [乘正严格递增 α] : 乘正严格递增 (WithBot α) where
  定义体: by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    gcongr

Depends on / 依赖: absurd, bot_lt_coe, bot_mul, coe_lt_coe, coe_mul, ne_bot, not_lt_bot, simp_rw, x0.ne.symm, x0.ne_bot
-/
instance [MulZeroClass α] [Preorder α] [MulPosStrictMono α] : MulPosStrictMono (WithBot α) where
  mul_lt_mul_of_pos_right x x0 a b h := by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    gcongr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] [Preorder α] [PosMulReflectLT α] : PosMulReflectLT (WithBot α) where
  body: by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [mul_bot x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_left h x0

中文:
实例 [乘零类
  签名: α] [预序 α] [正乘反映严格偏序 α] : 正乘反映严格偏序 (WithBot α) where
  定义体: by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [mul_bot x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_left h x0

Depends on / 依赖: WithBot, WithBot.bot_lt_coe, absurd, bot_le, bot_le.not_gt, bot_lt_coe, coe_lt_coe, coe_mul, eq_or_ne, lt_of_mul_lt_mul_left, mul_bot, not_ge, not_gt
-/
instance [MulZeroClass α] [Preorder α] [PosMulReflectLT α] : PosMulReflectLT (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [mul_bot x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_left h x0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] [Preorder α] [MulPosReflectLT α] : MulPosReflectLT (WithBot α) where
  body: by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [bot_mul x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_right h x0

中文:
实例 [乘零类
  签名: α] [预序 α] [乘正反映严格偏序 α] : 乘正反映严格偏序 (WithBot α) where
  定义体: by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [bot_mul x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_right h x0

Depends on / 依赖: WithBot, WithBot.bot_lt_coe, absurd, bot_le, bot_le.not_gt, bot_lt_coe, bot_mul, coe_lt_coe, coe_mul, eq_or_ne, lt_of_mul_lt_mul_right, not_ge, not_gt
-/
instance [MulZeroClass α] [Preorder α] [MulPosReflectLT α] : MulPosReflectLT (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [bot_mul x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_right h x0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] [Preorder α] [PosMulReflectLE α] : PosMulReflectLE (WithBot α) where
  body: by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [mul_bot x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_left h x0

中文:
实例 [乘零类
  签名: α] [预序 α] [正乘反映偏序 α] : 正乘反映偏序 (WithBot α) where
  定义体: by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [mul_bot x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_left h x0

Depends on / 依赖: absurd, bot_le, bot_lt_coe, coe_le_coe, coe_mul, le_of_mul_le_mul_left, mul_bot, ne_bot, not_ge, x0.ne.symm, x0.ne_bot
-/
instance [MulZeroClass α] [Preorder α] [PosMulReflectLE α] : PosMulReflectLE (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [mul_bot x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_left h x0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] [Preorder α] [MulPosReflectLE α] : MulPosReflectLE (WithBot α) where
  body: by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [bot_mul x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_right h x0

中文:
实例 [乘零类
  签名: α] [预序 α] [乘正反映偏序 α] : 乘正反映偏序 (WithBot α) where
  定义体: by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [bot_mul x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_right h x0

Depends on / 依赖: absurd, bot_le, bot_lt_coe, bot_mul, coe_le_coe, coe_mul, le_of_mul_le_mul_right, ne_bot, not_ge, x0.ne.symm, x0.ne_bot
-/
instance [MulZeroClass α] [Preorder α] [MulPosReflectLE α] : MulPosReflectLE (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [bot_mul x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_right h x0

/--
Instance `instIsOrderedRing` / 实例 `instIsOrderedRing`

English:
instance instIsOrderedRing
  signature: [CommSemiring α] [PartialOrder α] [IsOrderedRing α]

中文:
实例 instIsOrderedRing
  签名: [交换半环 α] [偏序 α] [是Ordered环 α]
-/
instance instIsOrderedRing [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    [CanonicallyOrderedAdd α] [NoZeroDivisors α] [Nontrivial α] :
    IsOrderedRing (WithBot α) where

end WithBot
