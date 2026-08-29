/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Field.Defs -- shake: keep (Qq dependency)
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Int.Parity -- shake: keep (Qq dependency)
public meta import Mathlib.Util.Qq

/-! # Lemmas for the `field_simp` tactic

-/

public section

open List

namespace Mathlib.Tactic.FieldSimp
@[expose] public section

section zpow'

variable {α : Type*}

section
variable [GroupWithZero α]

open scoped Classical in
/--
Definition of `zpow'` / `zpow'` 的定义

English:
definition zpow'
  signature: (a : α) (n : Int)
  body: if a = 0 ∧ n = 0 then 0 else a ^ n

中文:
定义 zpow'
  签名: (a : α) (n : 整数)
  定义体: if a = 0 ∧ n = 0 then 0 else a ^ n
-/
noncomputable def zpow' (a : α) (n : Int) : α :=
  if a = 0 ∧ n = 0 then 0 else a ^ n

/--
theorem `zpow'_add` / 定理 `zpow'_add`

English:
theorem zpow'_add
  given: (a : α) (m n : Int)
  proof: by
  by_cases ha : a = 0
  · simp [zpow', ha]
    by_cases hn : n = 0
    · simp +contextual [hn, zero_zpow]
    · simp +contextual [hn, zero_zpow]
  · simp [zpow', ha, zpow_add₀]

中文:
定理 zpow'_add
  条件: (a : α) (m n : 整数)
  证明: by
  by_cases ha : a = 0
  · simp [zpow', ha]
    by_cases hn : n = 0
    · simp +contextual [hn, zero_zpow]
    · simp +contextual [hn, zero_zpow]
  · simp [zpow', ha, zpow_add₀]
-/
theorem zpow'_add (a : α) (m n : Int) :
    zpow' a (m + n) = zpow' a m * zpow' a n := by
  by_cases ha : a = 0
  · simp [zpow', ha]
    by_cases hn : n = 0
    · simp +contextual [hn, zero_zpow]
    · simp +contextual [hn, zero_zpow]
  · simp [zpow', ha, zpow_add₀]

/--
theorem `zpow'_of_ne_zero_right` / 定理 `zpow'_of_ne_zero_right`

English:
theorem zpow'_of_ne_zero_right
  given: (a : α) (n : Int) (hn : n != 0)
  statement: zpow' a n = a ^ n
  proof: by
  simp [zpow', hn]

中文:
定理 zpow'_of_ne_zero_right
  条件: (a : α) (n : 整数) (hn : n != 0)
  结论: zpow' a n = a ^ n
  证明: by
  simp [zpow', hn]
-/
theorem zpow'_of_ne_zero_right (a : α) (n : Int) (hn : n != 0) : zpow' a n = a ^ n := by
  simp [zpow', hn]

/--
theorem `zpow'_of_ne_zero_left` / 定理 `zpow'_of_ne_zero_left`

English:
theorem zpow'_of_ne_zero_left
  given: (a : α) (n : Int) (ha : a != 0)
  statement: zpow' a n = a ^ n
  proof: by
  simp [zpow', ha]

@[simp]

中文:
定理 zpow'_of_ne_zero_left
  条件: (a : α) (n : 整数) (ha : a != 0)
  结论: zpow' a n = a ^ n
  证明: by
  simp [zpow', ha]

@[simp]
-/
theorem zpow'_of_ne_zero_left (a : α) (n : Int) (ha : a != 0) : zpow' a n = a ^ n := by
  simp [zpow', ha]

@[simp]
/--
lemma `zero_zpow'` / 引理 `zero_zpow'`

English:
lemma zero_zpow'
  given: (n : Int)
  statement: zpow' (0 : α) n = 0
  proof: by
  simp +contextual only [zpow', true_and, ite_eq_left_iff]
  intro hn
  exact zero_zpow n hn

中文:
引理 zero_zpow'
  条件: (n : 整数)
  结论: zpow' (0 : α) n = 0
  证明: by
  simp +contextual only [zpow', true_and, ite_eq_left_iff]
  intro hn
  exact zero_zpow n hn

Depends on / 依赖: contextual, ite_eq_left_iff, true_and, zero_zpow
-/
lemma zero_zpow' (n : Int) : zpow' (0 : α) n = 0 := by
  simp +contextual only [zpow', true_and, ite_eq_left_iff]
  intro hn
  exact zero_zpow n hn

/--
lemma `zpow'_eq_zero_iff` / 引理 `zpow'_eq_zero_iff`

English:
lemma zpow'_eq_zero_iff
  given: (a : α) (n : Int)
  statement: zpow' a n = 0 ↔ a = 0
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simp [zpow']
  · simp [zpow', zpow_eq_zero_iff hn]
    tauto

@[simp]

中文:
引理 zpow'_eq_zero_iff
  条件: (a : α) (n : 整数)
  结论: zpow' a n = 0 ↔ a = 0
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simp [zpow']
  · simp [zpow', zpow_eq_zero_iff hn]
    tauto

@[simp]
-/
lemma zpow'_eq_zero_iff (a : α) (n : Int) : zpow' a n = 0 ↔ a = 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [zpow']
  · simp [zpow', zpow_eq_zero_iff hn]
    tauto

@[simp]
/--
lemma `one_zpow'` / 引理 `one_zpow'`

English:
lemma one_zpow'
  given: (n : Int)
  statement: zpow' (1 : α) n = 1
  proof: by
  simp [zpow']

@[simp]

中文:
引理 one_zpow'
  条件: (n : 整数)
  结论: zpow' (1 : α) n = 1
  证明: by
  simp [zpow']

@[simp]
-/
lemma one_zpow' (n : Int) : zpow' (1 : α) n = 1 := by
  simp [zpow']

@[simp]
/--
lemma `zpow'_one` / 引理 `zpow'_one`

English:
lemma zpow'_one
  given: (a : α)
  statement: zpow' a 1 = a
  proof: by
  simp [zpow']

中文:
引理 zpow'_one
  条件: (a : α)
  结论: zpow' a 1 = a
  证明: by
  simp [zpow']
-/
lemma zpow'_one (a : α) : zpow' a 1 = a := by
  simp [zpow']

/--
lemma `zpow'_zero_eq_div` / 引理 `zpow'_zero_eq_div`

English:
lemma zpow'_zero_eq_div
  given: (a : α)
  statement: zpow' a 0 = a / a
  proof: by
  simp [zpow']
  by_cases h : a = 0
  · simp [h]
  · simp [h]

中文:
引理 zpow'_zero_eq_div
  条件: (a : α)
  结论: zpow' a 0 = a / a
  证明: by
  simp [zpow']
  by_cases h : a = 0
  · simp [h]
  · simp [h]
-/
lemma zpow'_zero_eq_div (a : α) : zpow' a 0 = a / a := by
  simp [zpow']
  by_cases h : a = 0
  · simp [h]
  · simp [h]

/--
lemma `zpow'_zero_of_ne_zero` / 引理 `zpow'_zero_of_ne_zero`

English:
lemma zpow'_zero_of_ne_zero
  given: {a : α} (ha : a != 0)
  statement: zpow' a 0 = 1
  proof: by simp [zpow', ha]

中文:
引理 zpow'_zero_of_ne_zero
  条件: {a : α} (ha : a != 0)
  结论: zpow' a 0 = 1
  证明: by simp [zpow', ha]
-/
lemma zpow'_zero_of_ne_zero {a : α} (ha : a != 0) : zpow' a 0 = 1 := by simp [zpow', ha]

/--
lemma `zpow'_neg` / 引理 `zpow'_neg`

English:
lemma zpow'_neg
  given: (a : α) (n : Int)
  statement: zpow' a (-n) = (zpow' a n)⁻¹
  proof: by
  simp +contextual [zpow', apply_ite]
  split_ifs with h
  · tauto
  · tauto

中文:
引理 zpow'_neg
  条件: (a : α) (n : 整数)
  结论: zpow' a (-n) = (zpow' a n)⁻¹
  证明: by
  simp +contextual [zpow', apply_ite]
  split_ifs with h
  · tauto
  · tauto
-/
lemma zpow'_neg (a : α) (n : Int) : zpow' a (-n) = (zpow' a n)⁻¹ := by
  simp +contextual [zpow', apply_ite]
  split_ifs with h
  · tauto
  · tauto

/--
lemma `zpow'_mul` / 引理 `zpow'_mul`

English:
lemma zpow'_mul
  given: (a : α) (m n : Int)
  statement: zpow' a (m * n) = zpow' (zpow' a m) n
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hn : n = 0
  · rw [hn]
    simp [zpow', ha, zpow_ne_zero ]
  by_cases hm : m = 0
  · rw [hm]
    simp [zpow', ha]
  simpa [zpow', ha, hm, hn] using zpow_mul a m n

中文:
引理 zpow'_mul
  条件: (a : α) (m n : 整数)
  结论: zpow' a (m * n) = zpow' (zpow' a m) n
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hn : n = 0
  · rw [hn]
    simp [zpow', ha, zpow_ne_zero ]
  by_cases hm : m = 0
  · rw [hm]
    simp [zpow', ha]
  simpa [zpow', ha, hm, hn] using zpow_mul a m n
-/
lemma zpow'_mul (a : α) (m n : Int) : zpow' a (m * n) = zpow' (zpow' a m) n := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hn : n = 0
  · rw [hn]
    simp [zpow', ha, zpow_ne_zero ]
  by_cases hm : m = 0
  · rw [hm]
    simp [zpow', ha]
  simpa [zpow', ha, hm, hn] using zpow_mul a m n

/--
lemma `zpow'_ofNat` / 引理 `zpow'_ofNat`

English:
lemma zpow'_ofNat
  given: (a : α) {n : Nat} (hn : n != 0)
  statement: zpow' a n = a ^ n
  proof: by
  rw [zpow'_of_ne_zero_right]
  · simp
  exact_mod_cast hn

中文:
引理 zpow'_ofNat
  条件: (a : α) {n : 自然数} (hn : n != 0)
  结论: zpow' a n = a ^ n
  证明: by
  rw [zpow'_of_ne_zero_right]
  · simp
  exact_mod_cast hn
-/
lemma zpow'_ofNat (a : α) {n : Nat} (hn : n != 0) : zpow' a n = a ^ n := by
  rw [zpow'_of_ne_zero_right]
  · simp
  exact_mod_cast hn

end

/--
lemma `mul_zpow'` / 引理 `mul_zpow'`

English:
lemma mul_zpow'
  given: [CommGroupWithZero α] (n : Int) (a b : α)
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simpa [zpow', ha, hb] using mul_zpow a b n

中文:
引理 mul_zpow'
  条件: [CommGroupWithZero α] (n : 整数) (a b : α)
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simpa [zpow', ha, hb] using mul_zpow a b n

Depends on / 依赖: mul_zpow
-/
lemma mul_zpow' [CommGroupWithZero α] (n : Int) (a b : α) :
    zpow' (a * b) n = zpow' a n * zpow' b n := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simpa [zpow', ha, hb] using mul_zpow a b n

/--
theorem `list_prod_zpow'` / 定理 `list_prod_zpow'`

English:
theorem list_prod_zpow'
  given: [CommGroupWithZero α] {r : Int} {l : List α}
  proof: let fr : α ->* α := ⟨⟨fun b => zpow' b r, one_zpow' r⟩, (mul_zpow' r)⟩
  map_list_prod fr l

中文:
定理 list_prod_zpow'
  条件: [CommGroupWithZero α] {r : 整数} {l : List α}
  证明: let fr : α ->* α := ⟨⟨fun b => zpow' b r, one_zpow' r⟩, (mul_zpow' r)⟩
  map_list_prod fr l

Depends on / 依赖: map_list_prod, mul_zpow, one_zpow
-/
theorem list_prod_zpow' [CommGroupWithZero α] {r : Int} {l : List α} :
    zpow' (prod l) r = prod (map (fun x => zpow' x r) l) :=
  let fr : α ->* α := ⟨⟨fun b => zpow' b r, one_zpow' r⟩, (mul_zpow' r)⟩
  map_list_prod fr l

end zpow'

/--
theorem `subst_add` / 定理 `subst_add`

English:
theorem subst_add
  statement: {M : Type*} [Semiring M] {x₁ x₂ X₁ X₂ Y y a : M}
  proof: by
  subst h₁ h₂ H_atom hy
  simp [mul_add]

中文:
定理 subst_add
  结论: {M : 类型} [Semiring M] {x₁ x₂ X₁ X₂ Y y a : M}
  证明: by
  subst h₁ h₂ H_atom hy
  simp [mul_add]

Depends on / 依赖: H_atom, mul_add
-/
theorem subst_add {M : Type*} [Semiring M] {x₁ x₂ X₁ X₂ Y y a : M}
    (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ = Y) (hy : a * Y = y) :
    x₁ + x₂ = y := by
  subst h₁ h₂ H_atom hy
  simp [mul_add]

/--
theorem `subst_sub` / 定理 `subst_sub`

English:
theorem subst_sub
  statement: {M : Type*} [Ring M] {x₁ x₂ X₁ X₂ Y y a : M}
  proof: by
  subst h₁ h₂ H_atom hy
  simp [mul_sub]

中文:
定理 subst_sub
  结论: {M : 类型} [Ring M] {x₁ x₂ X₁ X₂ Y y a : M}
  证明: by
  subst h₁ h₂ H_atom hy
  simp [mul_sub]

Depends on / 依赖: H_atom, mul_sub
-/
theorem subst_sub {M : Type*} [Ring M] {x₁ x₂ X₁ X₂ Y y a : M}
    (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) (hy : a * Y = y) :
    x₁ - x₂ = y := by
  subst h₁ h₂ H_atom hy
  simp [mul_sub]

/--
theorem `eq_div_of_eq_one_of_subst` / 定理 `eq_div_of_eq_one_of_subst`

English:
theorem eq_div_of_eq_one_of_subst
  statement: {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1)
  proof: by
  rw [h]; rw [hn]; rw [div_one]

中文:
定理 eq_div_of_eq_one_of_subst
  结论: {M : 类型} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1)
  证明: by
  rw [h]; rw [hn]; rw [div_one]

Depends on / 依赖: div_one
-/
theorem eq_div_of_eq_one_of_subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1)
    (hn : l_n = n) :
    l = n := by
  rw [h]; rw [hn]; rw [div_one]

/--
theorem `eq_div_of_eq_one_of_subst'` / 定理 `eq_div_of_eq_one_of_subst'`

English:
theorem eq_div_of_eq_one_of_subst'
  statement: {M : Type*} [DivInvOneMonoid M] {l l_d d : M} (h : l = 1 / l_d)
  proof: by
  rw [h]; rw [hn]; rw [one_div]

中文:
定理 eq_div_of_eq_one_of_subst'
  结论: {M : 类型} [DivInvOneMonoid M] {l l_d d : M} (h : l = 1 / l_d)
  证明: by
  rw [h]; rw [hn]; rw [one_div]

Depends on / 依赖: one_div
-/
theorem eq_div_of_eq_one_of_subst' {M : Type*} [DivInvOneMonoid M] {l l_d d : M} (h : l = 1 / l_d)
    (hn : l_d = d) :
    l = d⁻¹ := by
  rw [h]; rw [hn]; rw [one_div]

/--
theorem `eq_div_of_subst` / 定理 `eq_div_of_subst`

English:
theorem eq_div_of_subst
  statement: {M : Type*} [Div M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n)
  proof: by
  rw [h]; rw [hn]; rw [hd]

中文:
定理 eq_div_of_subst
  结论: {M : 类型} [Div M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n)
  证明: by
  rw [h]; rw [hn]; rw [hd]
-/
theorem eq_div_of_subst {M : Type*} [Div M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n)
    (hd : l_d = d) :
    l = n / d := by
  rw [h]; rw [hn]; rw [hd]

/--
theorem `eq_mul_of_eq_eq_eq_mul` / 定理 `eq_mul_of_eq_eq_eq_mul`

English:
theorem eq_mul_of_eq_eq_eq_mul
  statement: {M : Type*} [Mul M] {a b c D e f : M}
  proof: by
  rw [h₁]; rw [h₂]; rw [h₃]; rw [h₄]

中文:
定理 eq_mul_of_eq_eq_eq_mul
  结论: {M : 类型} [Mul M] {a b c D e f : M}
  证明: by
  rw [h₁]; rw [h₂]; rw [h₃]; rw [h₄]
-/
theorem eq_mul_of_eq_eq_eq_mul {M : Type*} [Mul M] {a b c D e f : M}
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e) (h₄ : e = f) :
    a = D * f := by
  rw [h₁]; rw [h₂]; rw [h₃]; rw [h₄]

/--
theorem `eq_eq_cancel_eq` / 定理 `eq_eq_cancel_eq`

English:
theorem eq_eq_cancel_eq
  statement: {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M}
  proof: by
  subst H₁ H₂
  rw [mul_right_inj' HL]

中文:
定理 eq_eq_cancel_eq
  结论: {M : 类型} [MonoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M}
  证明: by
  subst H₁ H₂
  rw [mul_right_inj' HL]

Depends on / 依赖: mul_right_inj
-/
theorem eq_eq_cancel_eq {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M}
    (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : L != 0) :
    (e₁ = e₂) = (f₁ = f₂) := by
  subst H₁ H₂
  rw [mul_right_inj' HL]

/--
theorem `le_eq_cancel_le` / 定理 `le_eq_cancel_le`

English:
theorem le_eq_cancel_le
  statement: {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulMono M]
  proof: by
  subst H₁ H₂
  apply Iff.eq
  exact mul_le_mul_iff_right₀ HL

中文:
定理 le_eq_cancel_le
  结论: {M : 类型} [MonoidWithZero M] [PartialOrder M] [PosMulMono M]
  证明: by
  subst H₁ H₂
  apply Iff.eq
  exact mul_le_mul_iff_right₀ HL

Depends on / 依赖: Iff.eq
-/
theorem le_eq_cancel_le {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulMono M]
    [PosMulReflectLE M] {e₁ e₂ f₁ f₂ L : M}
    (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : 0 < L) :
    (e₁ <= e₂) = (f₁ <= f₂) := by
  subst H₁ H₂
  apply Iff.eq
  exact mul_le_mul_iff_right₀ HL

/--
theorem `lt_eq_cancel_lt` / 定理 `lt_eq_cancel_lt`

English:
theorem lt_eq_cancel_lt
  statement: {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulStrictMono M]
  proof: by
  subst H₁ H₂
  apply Iff.eq
  exact mul_lt_mul_iff_of_pos_left HL

中文:
定理 lt_eq_cancel_lt
  结论: {M : 类型} [MonoidWithZero M] [PartialOrder M] [PosMulStrictMono M]
  证明: by
  subst H₁ H₂
  apply Iff.eq
  exact mul_lt_mul_iff_of_pos_left HL

Depends on / 依赖: Iff.eq, mul_lt_mul_iff_of_pos_left
-/
theorem lt_eq_cancel_lt {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulStrictMono M]
    [PosMulReflectLT M] {e₁ e₂ f₁ f₂ L : M}
    (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : 0 < L) :
    (e₁ < e₂) = (f₁ < f₂) := by
  subst H₁ H₂
  apply Iff.eq
  exact mul_lt_mul_iff_of_pos_left HL

/-! ### Theory of lists of pairs (exponent, atom)

This section contains the lemmas which are orchestrated by the `field_simp` tactic
to prove goals in fields. The basic object which these lemmas concern is `NF M`, a type synonym
for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.
-/

/--
Definition of `NF` / `NF` 的定义

English:
definition NF
  signature: (M : Type*)
  body: List (Int × M)

中文:
定义 NF
  签名: (M : 类型)
  定义体: List (Int × M)
-/
def NF (M : Type*) := List (Int × M)

namespace NF
variable {M : Type*}

/-- Augment a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, by prepending another
pair `p : ℤ × M`. -/
@[match_pattern]
/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (p : Int × M) (l : NF M)
  body: p :: l

@[inherit_doc cons] infixl:100 " ::ᵣ " => cons

中文:
定义 cons
  签名: (p : 整数 × M) (l : NF M)
  定义体: p :: l

@[inherit_doc cons] infixl:100 " ::ᵣ " => cons
-/
def cons (p : Int × M) (l : NF M) : NF M := p :: l

@[inherit_doc cons] infixl:100 " ::ᵣ " => cons

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: [GroupWithZero M] (l : NF M)
  body: (l.map (fun (⟨r, x⟩ : Int × M) => zpow' x r)).prod

中文:
定义 eval
  签名: [GroupWithZero M] (l : NF M)
  定义体: (l.map (fun (⟨r, x⟩ : Int × M) => zpow' x r)).prod

Depends on / 依赖: l.map
-/
noncomputable def eval [GroupWithZero M] (l : NF M) : M :=
  (l.map (fun (⟨r, x⟩ : Int × M) => zpow' x r)).prod

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eval_cons` / 定理 `eval_cons`

English:
theorem eval_cons
  given: [CommGroupWithZero M] (p : Int × M) (l : NF M)
  proof: by
  unfold eval cons
  simp [mul_comm]

中文:
定理 eval_cons
  条件: [CommGroupWithZero M] (p : 整数 × M) (l : NF M)
  证明: by
  unfold eval cons
  simp [mul_comm]
-/
@[simp] theorem eval_cons [CommGroupWithZero M] (p : Int × M) (l : NF M) :
    (p ::ᵣ l).eval = l.eval * zpow' p.2 p.1 := by
  unfold eval cons
  simp [mul_comm]

/--
theorem `cons_ne_zero` / 定理 `cons_ne_zero`

English:
theorem cons_ne_zero
  given: [GroupWithZero M] (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0)
  proof: by
  unfold eval cons
  apply mul_ne_zero ?_ hl
  simp [zpow'_eq_zero_iff, hx]

中文:
定理 cons_ne_zero
  条件: [GroupWithZero M] (r : 整数) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0)
  证明: by
  unfold eval cons
  apply mul_ne_zero ?_ hl
  simp [zpow'_eq_zero_iff, hx]

Depends on / 依赖: _eq_zero_iff, mul_ne_zero
-/
theorem cons_ne_zero [GroupWithZero M] (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) :
    ((r, x) ::ᵣ l).eval != 0 := by
  unfold eval cons
  apply mul_ne_zero ?_ hl
  simp [zpow'_eq_zero_iff, hx]

/--
theorem `cons_pos` / 定理 `cons_pos`

English:
theorem cons_pos
  statement: [GroupWithZero M] [PartialOrder M] [PosMulStrictMono M] [PosMulReflectLT M]
  proof: by
  unfold eval cons
  apply mul_pos ?_ hl
  simp only
  rw [zpow'_of_ne_zero_left _ _ hx.ne']
  apply zpow_pos hx

中文:
定理 cons_pos
  结论: [GroupWithZero M] [PartialOrder M] [PosMulStrictMono M] [PosMulReflectLT M]
  证明: by
  unfold eval cons
  apply mul_pos ?_ hl
  simp only
  rw [zpow'_of_ne_zero_left _ _ hx.ne']
  apply zpow_pos hx

Depends on / 依赖: _of_ne_zero_left, hx.ne, mul_pos, zpow_pos
-/
theorem cons_pos [GroupWithZero M] [PartialOrder M] [PosMulStrictMono M] [PosMulReflectLT M]
    [ZeroLEOneClass M] (r : Int) {x : M} (hx : 0 < x) {l : NF M} (hl : 0 < l.eval) :
    0 < ((r, x) ::ᵣ l).eval := by
  unfold eval cons
  apply mul_pos ?_ hl
  simp only
  rw [zpow'_of_ne_zero_left _ _ hx.ne']
  apply zpow_pos hx

/--
theorem `atom_eq_eval` / 定理 `atom_eq_eval`

English:
theorem atom_eq_eval
  given: [GroupWithZero M] (x : M)
  statement: x = NF.eval [(1, x)]
  proof: by simp [eval]

中文:
定理 atom_eq_eval
  条件: [GroupWithZero M] (x : M)
  结论: x = NF.eval [(1, x)]
  证明: by simp [eval]
-/
theorem atom_eq_eval [GroupWithZero M] (x : M) : x = NF.eval [(1, x)] := by simp [eval]

variable (M) in
/--
theorem `one_eq_eval` / 定理 `one_eq_eval`

English:
theorem one_eq_eval
  given: [GroupWithZero M]
  statement: (1:M) = NF.eval (M := M) []
  proof: (rfl)

中文:
定理 one_eq_eval
  条件: [GroupWithZero M]
  结论: (1:M) = NF.eval (M := M) []
  证明: (rfl)
-/
theorem one_eq_eval [GroupWithZero M] : (1:M) = NF.eval (M := M) [] := (rfl)

/--
theorem `mul_eq_eval₁` / 定理 `mul_eq_eval₁`

English:
theorem mul_eq_eval₁
  statement: [CommGroupWithZero M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M}
  proof: by
  simp only [eval_cons, ← h]
  ac_rfl

中文:
定理 mul_eq_eval₁
  结论: [CommGroupWithZero M] (a₁ : 整数 × M) {a₂ : 整数 × M} {l₁ l₂ l : NF M}
  证明: by
  simp only [eval_cons, ← h]
  ac_rfl

Depends on / 依赖: eval_cons
-/
theorem mul_eq_eval₁ [CommGroupWithZero M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M}
    (h : l₁.eval * (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  ac_rfl

/--
theorem `mul_eq_eval₂` / 定理 `mul_eq_eval₂`

English:
theorem mul_eq_eval₂
  statement: [CommGroupWithZero M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M}
  proof: by
  simp only [eval_cons, ← h, zpow'_add]
  ac_rfl

中文:
定理 mul_eq_eval₂
  结论: [CommGroupWithZero M] (r₁ r₂ : 整数) (x : M) {l₁ l₂ l : NF M}
  证明: by
  simp only [eval_cons, ← h, zpow'_add]
  ac_rfl

Depends on / 依赖: _add, eval_cons
-/
theorem mul_eq_eval₂ [CommGroupWithZero M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M}
    (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  simp only [eval_cons, ← h, zpow'_add]
  ac_rfl

/--
theorem `mul_eq_eval₃` / 定理 `mul_eq_eval₃`

English:
theorem mul_eq_eval₃
  statement: [CommGroupWithZero M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M}
  proof: by
  simp only [eval_cons, ← h]
  ac_rfl

中文:
定理 mul_eq_eval₃
  结论: [CommGroupWithZero M] {a₁ : 整数 × M} (a₂ : 整数 × M) {l₁ l₂ l : NF M}
  证明: by
  simp only [eval_cons, ← h]
  ac_rfl

Depends on / 依赖: eval_cons
-/
theorem mul_eq_eval₃ [CommGroupWithZero M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval * l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  ac_rfl

/--
theorem `mul_eq_eval` / 定理 `mul_eq_eval`

English:
theorem mul_eq_eval
  statement: [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
  proof: by
  rw [hx₁]; rw [hx₂]; rw [h]

中文:
定理 mul_eq_eval
  结论: [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
  证明: by
  rw [hx₁]; rw [hx₂]; rw [h]
-/
theorem mul_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = l.eval := by
  rw [hx₁]; rw [hx₂]; rw [h]

/--
theorem `div_eq_eval₁` / 定理 `div_eq_eval₁`

English:
theorem div_eq_eval₁
  statement: [CommGroupWithZero M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M}
  proof: by
  simp only [eval_cons, ← h, div_eq_mul_inv]
  ac_rfl

中文:
定理 div_eq_eval₁
  结论: [CommGroupWithZero M] (a₁ : 整数 × M) {a₂ : 整数 × M} {l₁ l₂ l : NF M}
  证明: by
  simp only [eval_cons, ← h, div_eq_mul_inv]
  ac_rfl

Depends on / 依赖: div_eq_mul_inv, eval_cons
-/
theorem div_eq_eval₁ [CommGroupWithZero M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M}
    (h : l₁.eval / (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, div_eq_mul_inv]
  ac_rfl

/--
theorem `div_eq_eval₂` / 定理 `div_eq_eval₂`

English:
theorem div_eq_eval₂
  statement: [CommGroupWithZero M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M}
  proof: by
  simp only [← h, eval_cons, div_eq_mul_inv, mul_inv, ← zpow'_neg, sub_eq_add_neg, zpow'_add]
  ac_rfl

中文:
定理 div_eq_eval₂
  结论: [CommGroupWithZero M] (r₁ r₂ : 整数) (x : M) {l₁ l₂ l : NF M}
  证明: by
  simp only [← h, eval_cons, div_eq_mul_inv, mul_inv, ← zpow'_neg, sub_eq_add_neg, zpow'_add]
  ac_rfl

Depends on / 依赖: _add, _neg, div_eq_mul_inv, eval_cons, mul_inv, sub_eq_add_neg
-/
theorem div_eq_eval₂ [CommGroupWithZero M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M}
    (h : l₁.eval / l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval / ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, div_eq_mul_inv, mul_inv, ← zpow'_neg, sub_eq_add_neg, zpow'_add]
  ac_rfl

/--
theorem `div_eq_eval₃` / 定理 `div_eq_eval₃`

English:
theorem div_eq_eval₃
  statement: [CommGroupWithZero M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M}
  proof: by
  simp only [eval_cons, ← h, zpow'_neg, div_eq_mul_inv, mul_inv, mul_assoc]

中文:
定理 div_eq_eval₃
  结论: [CommGroupWithZero M] {a₁ : 整数 × M} (a₂ : 整数 × M) {l₁ l₂ l : NF M}
  证明: by
  simp only [eval_cons, ← h, zpow'_neg, div_eq_mul_inv, mul_inv, mul_assoc]

Depends on / 依赖: _neg, div_eq_mul_inv, eval_cons, mul_assoc, mul_inv
-/
theorem div_eq_eval₃ [CommGroupWithZero M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval / l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  simp only [eval_cons, ← h, zpow'_neg, div_eq_mul_inv, mul_inv, mul_assoc]

/--
theorem `div_eq_eval` / 定理 `div_eq_eval`

English:
theorem div_eq_eval
  statement: [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
  proof: by
  rw [hx₁]; rw [hx₂]; rw [h]

中文:
定理 div_eq_eval
  结论: [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
  证明: by
  rw [hx₁]; rw [hx₂]; rw [h]
-/
theorem div_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = l.eval := by
  rw [hx₁]; rw [hx₂]; rw [h]

/--
theorem `eval_mul_eval_cons` / 定理 `eval_mul_eval_cons`

English:
theorem eval_mul_eval_cons
  statement: [CommGroupWithZero M] (n : Int) (e : M) {L l l' : NF M}
  proof: by
  rw [eval_cons]; rw [eval_cons]; rw [← h]; rw [mul_assoc]

中文:
定理 eval_mul_eval_cons
  结论: [CommGroupWithZero M] (n : 整数) (e : M) {L l l' : NF M}
  证明: by
  rw [eval_cons]; rw [eval_cons]; rw [← h]; rw [mul_assoc]

Depends on / 依赖: eval_cons, mul_assoc
-/
theorem eval_mul_eval_cons [CommGroupWithZero M] (n : Int) (e : M) {L l l' : NF M}
    (h : L.eval * l.eval = l'.eval) :
    L.eval * ((n, e) ::ᵣ l).eval = ((n, e) ::ᵣ l').eval := by
  rw [eval_cons]; rw [eval_cons]; rw [← h]; rw [mul_assoc]

/--
theorem `eval_mul_eval_cons_zero` / 定理 `eval_mul_eval_cons_zero`

English:
theorem eval_mul_eval_cons_zero
  statement: [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M}
  proof: by
  rw [← eval_mul_eval_cons 0 e h]; rw [h']

中文:
定理 eval_mul_eval_cons_zero
  结论: [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M}
  证明: by
  rw [← eval_mul_eval_cons 0 e h]; rw [h']

Depends on / 依赖: eval_mul_eval_cons
-/
theorem eval_mul_eval_cons_zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M}
    (h : L.eval * l.eval = l'.eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval) :
    L.eval * l₀.eval = ((0, e) ::ᵣ l').eval := by
  rw [← eval_mul_eval_cons 0 e h]; rw [h']

/--
theorem `eval_cons_mul_eval` / 定理 `eval_cons_mul_eval`

English:
theorem eval_cons_mul_eval
  statement: [CommGroupWithZero M] (n : Int) (e : M) {L l l' : NF M}
  proof: by
  rw [eval_cons]; rw [eval_cons]; rw [← h]
  ac_rfl

中文:
定理 eval_cons_mul_eval
  结论: [CommGroupWithZero M] (n : 整数) (e : M) {L l l' : NF M}
  证明: by
  rw [eval_cons]; rw [eval_cons]; rw [← h]
  ac_rfl

Depends on / 依赖: eval_cons
-/
theorem eval_cons_mul_eval [CommGroupWithZero M] (n : Int) (e : M) {L l l' : NF M}
    (h : L.eval * l.eval = l'.eval) :
    ((n, e) ::ᵣ L).eval * l.eval = ((n, e) ::ᵣ l').eval := by
  rw [eval_cons]; rw [eval_cons]; rw [← h]
  ac_rfl

/--
theorem `eval_cons_mul_eval_cons_neg` / 定理 `eval_cons_mul_eval_cons_neg`

English:
theorem eval_cons_mul_eval_cons_neg
  statement: [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0)
  proof: by
  rw [mul_eq_eval₂ n (-n) e h]
  simp [zpow'_zero_of_ne_zero he]

中文:
定理 eval_cons_mul_eval_cons_neg
  结论: [CommGroupWithZero M] (n : 整数) {e : M} (he : e != 0)
  证明: by
  rw [mul_eq_eval₂ n (-n) e h]
  simp [zpow'_zero_of_ne_zero he]

Depends on / 依赖: _zero_of_ne_zero
-/
theorem eval_cons_mul_eval_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0)
    {L l l' : NF M} (h : L.eval * l.eval = l'.eval) :
    ((n, e) ::ᵣ L).eval * ((-n, e) ::ᵣ l).eval = l'.eval := by
  rw [mul_eq_eval₂ n (-n) e h]
  simp [zpow'_zero_of_ne_zero he]

/--
theorem `cons_eq_div_of_eq_div` / 定理 `cons_eq_div_of_eq_div`

English:
theorem cons_eq_div_of_eq_div
  statement: [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M}
  proof: by
  simp only [eval_cons, h, div_eq_mul_inv]
  ac_rfl

中文:
定理 cons_eq_div_of_eq_div
  结论: [CommGroupWithZero M] (n : 整数) (e : M) {t t_n t_d : NF M}
  证明: by
  simp only [eval_cons, h, div_eq_mul_inv]
  ac_rfl

Depends on / 依赖: div_eq_mul_inv, eval_cons
-/
theorem cons_eq_div_of_eq_div [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((n, e) ::ᵣ t).eval = ((n, e) ::ᵣ t_n).eval / t_d.eval := by
  simp only [eval_cons, h, div_eq_mul_inv]
  ac_rfl

/--
theorem `cons_eq_div_of_eq_div'` / 定理 `cons_eq_div_of_eq_div'`

English:
theorem cons_eq_div_of_eq_div'
  statement: [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M}
  proof: by
  simp only [eval_cons, h, zpow'_neg, div_eq_mul_inv, mul_inv]
  ac_rfl

中文:
定理 cons_eq_div_of_eq_div'
  结论: [CommGroupWithZero M] (n : 整数) (e : M) {t t_n t_d : NF M}
  证明: by
  simp only [eval_cons, h, zpow'_neg, div_eq_mul_inv, mul_inv]
  ac_rfl

Depends on / 依赖: _neg, div_eq_mul_inv, eval_cons, mul_inv
-/
theorem cons_eq_div_of_eq_div' [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((-n, e) ::ᵣ t).eval = t_n.eval / ((n, e) ::ᵣ t_d).eval := by
  simp only [eval_cons, h, zpow'_neg, div_eq_mul_inv, mul_inv]
  ac_rfl

/--
theorem `cons_zero_eq_div_of_eq_div` / 定理 `cons_zero_eq_div_of_eq_div`

English:
theorem cons_zero_eq_div_of_eq_div
  statement: [CommGroupWithZero M] (e : M) {t t_n t_d : NF M}
  proof: by
  simp only [eval_cons, h, div_eq_mul_inv, mul_inv, ← zpow'_neg, ← add_neg_cancel (1:Int), zpow'_add]
  ac_rfl

中文:
定理 cons_zero_eq_div_of_eq_div
  结论: [CommGroupWithZero M] (e : M) {t t_n t_d : NF M}
  证明: by
  simp only [eval_cons, h, div_eq_mul_inv, mul_inv, ← zpow'_neg, ← add_neg_cancel (1:Int), zpow'_add]
  ac_rfl

Depends on / 依赖: _add, _neg, add_neg_cancel, div_eq_mul_inv, eval_cons, mul_inv
-/
theorem cons_zero_eq_div_of_eq_div [CommGroupWithZero M] (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((0, e) ::ᵣ t).eval = ((1, e) ::ᵣ t_n).eval / ((1, e) ::ᵣ t_d).eval := by
  simp only [eval_cons, h, div_eq_mul_inv, mul_inv, ← zpow'_neg, ← add_neg_cancel (1:Int), zpow'_add]
  ac_rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (NF M)
  body: l.map fun (a, x) => (-a, x)

中文:
实例 :
  签名: Inv (NF M)
  定义体: l.map fun (a, x) => (-a, x)

Depends on / 依赖: l.map
-/
instance : Inv (NF M) where
  inv l := l.map fun (a, x) => (-a, x)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eval_inv` / 定理 `eval_inv`

English:
theorem eval_inv
  given: [CommGroupWithZero M] (l : NF M)
  statement: (l⁻¹).eval = l.eval⁻¹
  proof: by
  simp +instances only [NF.eval, List.map_map, NF.instInv, List.prod_inv]
  congr! 2
  ext p
  simp [zpow'_neg]

中文:
定理 eval_inv
  条件: [CommGroupWithZero M] (l : NF M)
  结论: (l⁻¹).eval = l.eval⁻¹
  证明: by
  simp +instances only [NF.eval, List.map_map, NF.instInv, List.prod_inv]
  congr! 2
  ext p
  simp [zpow'_neg]

Depends on / 依赖: List.map_map, List.prod_inv, NF.eval, NF.instInv, _neg, instInv, instances, map_map, prod_inv
-/
theorem eval_inv [CommGroupWithZero M] (l : NF M) : (l⁻¹).eval = l.eval⁻¹ := by
  simp +instances only [NF.eval, List.map_map, NF.instInv, List.prod_inv]
  congr! 2
  ext p
  simp [zpow'_neg]

/--
theorem `one_div_eq_eval` / 定理 `one_div_eq_eval`

English:
theorem one_div_eq_eval
  given: [CommGroupWithZero M] (l : NF M)
  statement: 1 / l.eval = (l⁻¹).eval
  proof: by
  simp [eval_inv]

中文:
定理 one_div_eq_eval
  条件: [CommGroupWithZero M] (l : NF M)
  结论: 1 / l.eval = (l⁻¹).eval
  证明: by
  simp [eval_inv]

Depends on / 依赖: eval_inv
-/
theorem one_div_eq_eval [CommGroupWithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval := by
  simp [eval_inv]

/--
theorem `inv_eq_eval` / 定理 `inv_eq_eval`

English:
theorem inv_eq_eval
  given: [CommGroupWithZero M] {l : NF M} {x : M} (h : x = l.eval)
  proof: by
  rw [h]; rw [eval_inv]

中文:
定理 inv_eq_eval
  条件: [CommGroupWithZero M] {l : NF M} {x : M} (h : x = l.eval)
  证明: by
  rw [h]; rw [eval_inv]

Depends on / 依赖: eval_inv
-/
theorem inv_eq_eval [CommGroupWithZero M] {l : NF M} {x : M} (h : x = l.eval) :
    x⁻¹ = (l⁻¹).eval := by
  rw [h]; rw [eval_inv]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (NF M) Int
  body: l.map fun (a, x) => (r * a, x)

中文:
实例 :
  签名: Pow (NF M) 整数
  定义体: l.map fun (a, x) => (r * a, x)

Depends on / 依赖: l.map
-/
instance : Pow (NF M) Int where
  pow l r := l.map fun (a, x) => (r * a, x)

/--
theorem `zpow_apply` / 定理 `zpow_apply`

English:
theorem zpow_apply
  given: (r : Int) (l : NF M)
  statement: l ^ r = l.map fun (a, x) => (r * a, x)
  proof: rfl

中文:
定理 zpow_apply
  条件: (r : 整数) (l : NF M)
  结论: l ^ r = l.map fun (a, x) => (r * a, x)
  证明: rfl
-/
@[simp] theorem zpow_apply (r : Int) (l : NF M) : l ^ r = l.map fun (a, x) => (r * a, x) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eval_zpow'` / 定理 `eval_zpow'`

English:
theorem eval_zpow'
  given: [CommGroupWithZero M] (l : NF M) (r : Int)
  proof: by
  unfold NF.eval at ⊢
  simp only [zpow_apply, list_prod_zpow', map_map]
  congr! 2
  ext p
  simp [← zpow'_mul, mul_comm]

中文:
定理 eval_zpow'
  条件: [CommGroupWithZero M] (l : NF M) (r : 整数)
  证明: by
  unfold NF.eval at ⊢
  simp only [zpow_apply, list_prod_zpow', map_map]
  congr! 2
  ext p
  simp [← zpow'_mul, mul_comm]

Depends on / 依赖: NF.eval, _mul, list_prod_zpow, map_map, mul_comm, zpow_apply
-/
theorem eval_zpow' [CommGroupWithZero M] (l : NF M) (r : Int) :
    (l ^ r).eval = zpow' l.eval r := by
  unfold NF.eval at ⊢
  simp only [zpow_apply, list_prod_zpow', map_map]
  congr! 2
  ext p
  simp [← zpow'_mul, mul_comm]

/--
theorem `zpow_eq_eval` / 定理 `zpow_eq_eval`

English:
theorem zpow_eq_eval
  statement: [CommGroupWithZero M] {l : NF M} {r : Int} (hr : r != 0) {x : M}
  proof: by
  rw [← zpow'_of_ne_zero_right x r hr]; rw [eval_zpow']; rw [hx]

中文:
定理 zpow_eq_eval
  结论: [CommGroupWithZero M] {l : NF M} {r : 整数} (hr : r != 0) {x : M}
  证明: by
  rw [← zpow'_of_ne_zero_right x r hr]; rw [eval_zpow']; rw [hx]

Depends on / 依赖: _of_ne_zero_right, eval_zpow
-/
theorem zpow_eq_eval [CommGroupWithZero M] {l : NF M} {r : Int} (hr : r != 0) {x : M}
    (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [← zpow'_of_ne_zero_right x r hr]; rw [eval_zpow']; rw [hx]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (NF M) Nat
  body: l.map fun (a, x) => (r * a, x)

中文:
实例 :
  签名: Pow (NF M) 自然数
  定义体: l.map fun (a, x) => (r * a, x)

Depends on / 依赖: l.map
-/
instance : Pow (NF M) Nat where
  pow l r := l.map fun (a, x) => (r * a, x)

/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: (r : Nat) (l : NF M)
  statement: l ^ r = l.map fun (a, x) => (r * a, x)
  proof: rfl

中文:
定理 pow_apply
  条件: (r : 自然数) (l : NF M)
  结论: l ^ r = l.map fun (a, x) => (r * a, x)
  证明: rfl
-/
@[simp] theorem pow_apply (r : Nat) (l : NF M) : l ^ r = l.map fun (a, x) => (r * a, x) :=
  rfl

/--
theorem `eval_pow` / 定理 `eval_pow`

English:
theorem eval_pow
  given: [CommGroupWithZero M] (l : NF M) (r : Nat)
  statement: (l ^ r).eval = zpow' l.eval r
  proof: eval_zpow' l r

中文:
定理 eval_pow
  条件: [CommGroupWithZero M] (l : NF M) (r : 自然数)
  结论: (l ^ r).eval = zpow' l.eval r
  证明: eval_zpow' l r

Depends on / 依赖: eval_zpow
-/
theorem eval_pow [CommGroupWithZero M] (l : NF M) (r : Nat) : (l ^ r).eval = zpow' l.eval r :=
  eval_zpow' l r

/--
theorem `pow_eq_eval` / 定理 `pow_eq_eval`

English:
theorem pow_eq_eval
  statement: [CommGroupWithZero M] {l : NF M} {r : Nat} (hr : r != 0) {x : M}
  proof: by
  rw [eval_pow]; rw [hx]
  rw [zpow'_ofNat _ hr]

中文:
定理 pow_eq_eval
  结论: [CommGroupWithZero M] {l : NF M} {r : 自然数} (hr : r != 0) {x : M}
  证明: by
  rw [eval_pow]; rw [hx]
  rw [zpow'_ofNat _ hr]

Depends on / 依赖: _ofNat, eval_pow
-/
theorem pow_eq_eval [CommGroupWithZero M] {l : NF M} {r : Nat} (hr : r != 0) {x : M}
    (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [eval_pow]; rw [hx]
  rw [zpow'_ofNat _ hr]

/--
theorem `eval_cons_of_pow_eq_zero` / 定理 `eval_cons_of_pow_eq_zero`

English:
theorem eval_cons_of_pow_eq_zero
  statement: [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0)
  proof: by
  simp [hr, zpow'_zero_of_ne_zero hx]

中文:
定理 eval_cons_of_pow_eq_zero
  结论: [CommGroupWithZero M] {r : 整数} (hr : r = 0) {x : M} (hx : x != 0)
  证明: by
  simp [hr, zpow'_zero_of_ne_zero hx]

Depends on / 依赖: _zero_of_ne_zero
-/
theorem eval_cons_of_pow_eq_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0)
    (l : NF M) :
    ((r, x) ::ᵣ l).eval = NF.eval l := by
  simp [hr, zpow'_zero_of_ne_zero hx]

/--
theorem `eval_cons_eq_eval_of_eq_of_eq` / 定理 `eval_cons_eq_eval_of_eq_of_eq`

English:
theorem eval_cons_eq_eval_of_eq_of_eq
  statement: [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M}
  proof: by
  rw [← h']; rw [eval_cons]; rw [eval_cons]; rw [h]

中文:
定理 eval_cons_eq_eval_of_eq_of_eq
  结论: [CommGroupWithZero M] (r : 整数) (x : M) {t t' l' : NF M}
  证明: by
  rw [← h']; rw [eval_cons]; rw [eval_cons]; rw [h]

Depends on / 依赖: eval_cons
-/
theorem eval_cons_eq_eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M}
    (h : NF.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').eval = NF.eval l') :
    ((r, x) ::ᵣ t).eval = NF.eval l' := by
  rw [← h']; rw [eval_cons]; rw [eval_cons]; rw [h]

end NF
end

/-! ### Negations of algebraic operations -/

@[expose] public meta section Sign
open Lean Qq

variable {v : Level} {M : Q(Type v)}

/--
Inductive type `Sign` / 归纳类型 `Sign`

English:
inductive Sign
  parameters: (M : Q(Type v))
  constructors (2):
    - plus: 
    - minus: (iM : Q(Field $M))

中文:
归纳类型 Sign
  参数: (M : Q(类型v))
  构造子 (2 个):
    - plus: 
    - minus: (iM : Q(Field $M))
-/
inductive Sign (M : Q(Type v))
  | plus
  | minus (iM : Q(Field $M))

/--
Definition of `Sign.expr` / `Sign.expr` 的定义

English:
definition Sign.expr
  signature: : Sign M -> Q($M) -> Q($M)

中文:
定义 Sign.expr
  签名: : Sign M -> Q($M) -> Q($M)
-/
def Sign.expr : Sign M -> Q($M) -> Q($M)
  | plus, a => a
  | minus _, a => q(-$a)

/--
Definition of `Sign.mulRight` / `Sign.mulRight` 的定义

English:
definition Sign.mulRight
  signature: (iM : Q(CommGroupWithZero $M)) (c y : Q($M)) (g : Sign M)
  body: do
  match (dependent := true) g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(Eq.symm (mul_neg $c _))

中文:
定义 Sign.mulRight
  签名: (iM : Q(CommGroupWithZero $M)) (c y : Q($M)) (g : Sign M)
  定义体: do
  match (dependent := true) g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(Eq.symm (mul_neg $c _))
-/
def Sign.mulRight (iM : Q(CommGroupWithZero $M)) (c y : Q($M)) (g : Sign M) :
    MetaM Q($(g.expr q($c * $y)) = $c * $(g.expr y)) := do
  match (dependent := true) g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(Eq.symm (mul_neg $c _))

/--
Definition of `Sign.mul` / `Sign.mul` 的定义

English:
definition Sign.mul
  signature: (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M)
  body: do
  match (dependent := true) g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(mul_neg $y₁ $y₂)⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_mul $y₁ $y₂)⟩
  | .minus _, .minus _ =>
    assume

中文:
定义 Sign.mul
  签名: (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M)
  定义体: do
  match (dependent := true) g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(mul_neg $y₁ $y₂)⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_mul $y₁ $y₂)⟩
  | .minus _, .minus _ =>
    assume
-/
def Sign.mul (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M) :
    MetaM (Σ (G : Sign M), Q($(g₁.expr y₁) * $(g₂.expr y₂) = $(G.expr q($y₁ * $y₂)))) := do
  match (dependent := true) g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(mul_neg $y₁ $y₂)⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_mul $y₁ $y₂)⟩
  | .minus _, .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_mul_neg $y₁ $y₂)⟩

/--
Definition of `Sign.inv` / `Sign.inv` 的定义

English:
definition Sign.inv
  signature: (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M)
  body: do
  match (dependent := true) g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(inv_neg (a := $y))

中文:
定义 Sign.inv
  签名: (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M)
  定义体: do
  match (dependent := true) g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(inv_neg (a := $y))
-/
def Sign.inv (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) :
    MetaM (Q($(g.expr y)⁻¹ = $(g.expr q($y⁻¹)))) := do
  match (dependent := true) g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(inv_neg (a := $y))

/--
Definition of `Sign.div` / `Sign.div` 的定义

English:
definition Sign.div
  signature: (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M)
  body: do
  match (dependent := true) g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(div_neg $y₁ (b := $y₂))⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_div $y₂ $y₁)⟩
  | .minus _, .minus _ =>
   

中文:
定义 Sign.div
  签名: (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M)
  定义体: do
  match (dependent := true) g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(div_neg $y₁ (b := $y₂))⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_div $y₂ $y₁)⟩
  | .minus _, .minus _ =>
   
-/
def Sign.div (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M) :
    MetaM (Σ (G : Sign M), Q($(g₁.expr y₁) / $(g₂.expr y₂) = $(G.expr q($y₁ / $y₂)))) := do
  match (dependent := true) g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(div_neg $y₁ (b := $y₂))⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_div $y₂ $y₁)⟩
  | .minus _, .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_div_neg_eq $y₁ $y₂)⟩

/--
Definition of `Sign.neg` / `Sign.neg` 的定义

English:
definition Sign.neg
  signature: (iM : Q(Field $M)) (y : Q($M)) (g : Sign M)
  body: do
  match (dependent := true) g with
  | .plus => pure ⟨.minus iM, q(rfl)⟩
  | .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_neg $y)⟩

中文:
定义 Sign.neg
  签名: (iM : Q(Field $M)) (y : Q($M)) (g : Sign M)
  定义体: do
  match (dependent := true) g with
  | .plus => pure ⟨.minus iM, q(rfl)⟩
  | .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_neg $y)⟩
-/
def Sign.neg (iM : Q(Field $M)) (y : Q($M)) (g : Sign M) :
    MetaM (Σ (G : Sign M), Q(-$(g.expr y) = $(G.expr y))) := do
  match (dependent := true) g with
  | .plus => pure ⟨.minus iM, q(rfl)⟩
  | .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_neg $y)⟩

/--
Definition of `Sign.pow` / `Sign.pow` 的定义

English:
definition Sign.pow
  signature: (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : Nat)
  body: do
  match (dependent := true) g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_pow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd.

中文:
定义 Sign.pow
  签名: (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : 自然数)
  定义体: do
  match (dependent := true) g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_pow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd.
-/
def Sign.pow (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : Nat) :
    MetaM (Σ (G : Sign M), Q($(g.expr y) ^ $s = $(G.expr q($y ^ $s)))) := do
  match (dependent := true) g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_pow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd.neg_pow $pf_s $y)⟩

/--
Definition of `Sign.zpow` / `Sign.zpow` 的定义

English:
definition Sign.zpow
  signature: (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : Int)
  body: do
  match (dependent := true) g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_zpow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd

中文:
定义 Sign.zpow
  签名: (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : 整数)
  定义体: do
  match (dependent := true) g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_zpow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd
-/
def Sign.zpow (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : Int) :
    MetaM (Σ (G : Sign M), Q($(g.expr y) ^ $s = $(G.expr q($y ^ $s)))) := do
  match (dependent := true) g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_zpow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd.neg_zpow $pf_s $y)⟩

/--
Definition of `Sign.congr` / `Sign.congr` 的定义

English:
definition Sign.congr
  signature: {y y' : Q($M)} (g : Sign M) (pf : Q($y = $y'))
  body: match g with
  | .plus => pf
  | .minus _ => q(congr_arg Neg.neg $pf)

中文:
定义 Sign.congr
  签名: {y y' : Q($M)} (g : Sign M) (pf : Q($y = $y'))
  定义体: match g with
  | .plus => pf
  | .minus _ => q(congr_arg Neg.neg $pf)

Depends on / 依赖: Neg.neg, congr_arg
-/
def Sign.congr {y y' : Q($M)} (g : Sign M) (pf : Q($y = $y')) : Q($(g.expr y)= $(g.expr y')) :=
  match g with
  | .plus => pf
  | .minus _ => q(congr_arg Neg.neg $pf)

/--
Definition of `Sign.mkEqMul` / `Sign.mkEqMul` 的定义

English:
definition Sign.mkEqMul
  signature: (iM : Q(CommGroupWithZero $M)) {a b C d e : Q($M)} {g : Sign M}
  body: do
    let pf₂' : Q($(g.expr b) = $(g.expr q($C * $d))) := g.congr pf₂
    let pf' ← Sign.mulRight iM C d g
    pure q(eq_mul_of_eq_eq_eq_mul $pf₁ $pf₂' $pf' $(g.congr pf₃))

中文:
定义 Sign.mkEqMul
  签名: (iM : Q(CommGroupWithZero $M)) {a b C d e : Q($M)} {g : Sign M}
  定义体: do
    let pf₂' : Q($(g.expr b) = $(g.expr q($C * $d))) := g.congr pf₂
    let pf' ← Sign.mulRight iM C d g
    pure q(eq_mul_of_eq_eq_eq_mul $pf₁ $pf₂' $pf' $(g.congr pf₃))
-/
def Sign.mkEqMul (iM : Q(CommGroupWithZero $M)) {a b C d e : Q($M)} {g : Sign M}
      (pf₁ : Q($a = $(g.expr b))) (pf₂ : Q($b = $C * $d))
      (pf₃ : Q($d = $e)) : MetaM Q($a = $C * $(g.expr e)) := do
    let pf₂' : Q($(g.expr b) = $(g.expr q($C * $d))) := g.congr pf₂
    let pf' ← Sign.mulRight iM C d g
    pure q(eq_mul_of_eq_eq_eq_mul $pf₁ $pf₂' $pf' $(g.congr pf₃))

end Sign

end Mathlib.Tactic.FieldSimp
