/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Cast.Lemmas

/-!

# Congruences modulo an integer

This file defines the equivalence relation `a ≡ b [ZMOD n]` on the integers, similarly to how
`Data.Nat.ModEq` defines them for the natural numbers. The notation is short for `n.ModEq a b`,
which is defined to be `a % n = b % n` for integers `a b n`.

## Tags

modeq, congruence, mod, MOD, modulo, integers

-/

@[expose] public section


/-- `a ≡ b [ZMOD n]` when `a % n = b % n`. -/
@[wikidata Q3773677]
/--
Definition of `Int.ModEq` / `Int.ModEq` 的定义

English:
definition Int.ModEq
  signature: (n a b : Int)
  body: a % n = b % n

@[inherit_doc]
notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

中文:
定义 Int.ModEq
  签名: (n a b : 整数)
  定义体: a % n = b % n

@[inherit_doc]
notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b
-/
def Int.ModEq (n a b : Int) :=
  a % n = b % n

@[inherit_doc]
notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

namespace AddCommGroup

@[simp]
/--
theorem `modEq_iff_intModEq` / 定理 `modEq_iff_intModEq`

English:
theorem modEq_iff_intModEq
  given: {a b z : Int}
  statement: a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z]
  proof: by
  rw [modEq_comm]
  simp [modEq_iff_zsmul', dvd_iff_exists_eq_mul_left, Int.ModEq,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

@[deprecated (since := "2026-01-13")]
alias modEq_iff_int_modEq := modEq_iff_intModEq

中文:
定理 modEq_iff_intModEq
  条件: {a b z : 整数}
  结论: a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z]
  证明: by
  rw [modEq_comm]
  simp [modEq_iff_zsmul', dvd_iff_exists_eq_mul_left, Int.ModEq,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

@[deprecated (since := "2026-01-13")]
alias modEq_iff_int_modEq := modEq_iff_intModEq

Depends on / 依赖: Int.ModEq, Int.dvd_iff_emod_eq_zero, Int.emod_eq_emod_iff_emod_sub_eq_zero, dvd_iff_emod_eq_zero, dvd_iff_exists_eq_mul_left, emod_eq_emod_iff_emod_sub_eq_zero, modEq_comm, modEq_iff_zsmul
-/
theorem modEq_iff_intModEq {a b z : Int} : a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z] := by
  rw [modEq_comm]
  simp [modEq_iff_zsmul', dvd_iff_exists_eq_mul_left, Int.ModEq,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

@[deprecated (since := "2026-01-13")]
alias modEq_iff_int_modEq := modEq_iff_intModEq

variable {G : Type*} [AddCommGroupWithOne G] [CharZero G]

@[simp, norm_cast]
/--
theorem `intCast_modEq_intCast` / 定理 `intCast_modEq_intCast`

English:
theorem intCast_modEq_intCast
  given: {a b z : Int}
  statement: a ≡ b [PMOD (z : G)] ↔ a ≡ b [PMOD z]
  proof: map_modEq_iff (Int.castAddHom G) Int.cast_injective

@[simp, norm_cast]

中文:
定理 intCast_modEq_intCast
  条件: {a b z : 整数}
  结论: a ≡ b [PMOD (z : G)] ↔ a ≡ b [PMOD z]
  证明: map_modEq_iff (Int.castAddHom G) Int.cast_injective

@[simp, norm_cast]

Depends on / 依赖: Int.castAddHom, Int.cast_injective, castAddHom, cast_injective, map_modEq_iff
-/
theorem intCast_modEq_intCast {a b z : Int} : a ≡ b [PMOD (z : G)] ↔ a ≡ b [PMOD z] :=
  map_modEq_iff (Int.castAddHom G) Int.cast_injective

@[simp, norm_cast]
/--
lemma `intCast_modEq_intCast'` / 引理 `intCast_modEq_intCast'`

English:
lemma intCast_modEq_intCast'
  given: {a b : Int} {n : Nat}
  statement: a ≡ b [PMOD (n : G)] ↔ a ≡ b [PMOD (n : Int)]
  proof: by
  simpa using intCast_modEq_intCast (G := G) (z := n)

alias ⟨ModEq.of_intCast, ModEq.intCast⟩ := intCast_modEq_intCast

中文:
引理 intCast_modEq_intCast'
  条件: {a b : 整数} {n : 自然数}
  结论: a ≡ b [PMOD (n : G)] ↔ a ≡ b [PMOD (n : 整数)]
  证明: by
  simpa using intCast_modEq_intCast (G := G) (z := n)

alias ⟨ModEq.of_intCast, ModEq.intCast⟩ := intCast_modEq_intCast

Depends on / 依赖: intCast_modEq_intCast
-/
lemma intCast_modEq_intCast' {a b : Int} {n : Nat} : a ≡ b [PMOD (n : G)] ↔ a ≡ b [PMOD (n : Int)] := by
  simpa using intCast_modEq_intCast (G := G) (z := n)

alias ⟨ModEq.of_intCast, ModEq.intCast⟩ := intCast_modEq_intCast

end AddCommGroup

namespace Int

variable {m n a b c d : Int}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Decidable (ModEq n a b)
  body: decEq (a % n) (b % n)

中文:
实例 :
  签名: Decidable (ModEq n a b)
  定义体: decEq (a % n) (b % n)
-/
instance : Decidable (ModEq n a b) := decEq (a % n) (b % n)

namespace ModEq

@[refl, simp]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (a : Int)
  statement: a ≡ a [ZMOD n]
  proof: @rfl _ _

中文:
定理 refl
  条件: (a : 整数)
  结论: a ≡ a [ZMOD n]
  证明: @rfl _ _
-/
protected theorem refl (a : Int) : a ≡ a [ZMOD n] :=
  @rfl _ _

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  statement: a ≡ a [ZMOD n]
  proof: ModEq.refl _

中文:
定理 rfl
  结论: a ≡ a [ZMOD n]
  证明: ModEq.refl _
-/
protected theorem rfl : a ≡ a [ZMOD n] :=
  ModEq.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Refl (ModEq n)
  body: ⟨ModEq.refl⟩

@[symm]

中文:
实例 :
  签名: Std.Refl (ModEq n)
  定义体: ⟨ModEq.refl⟩

@[symm]

Depends on / 依赖: ModEq.refl
-/
instance : Std.Refl (ModEq n) :=
  ⟨ModEq.refl⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  statement: a ≡ b [ZMOD n] -> b ≡ a [ZMOD n]
  proof: Eq.symm

@[trans]

中文:
定理 symm
  结论: a ≡ b [ZMOD n] -> b ≡ a [ZMOD n]
  证明: Eq.symm

@[trans]
-/
protected theorem symm : a ≡ b [ZMOD n] -> b ≡ a [ZMOD n] :=
  Eq.symm

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: a ≡ b [ZMOD n] -> b ≡ c [ZMOD n] -> a ≡ c [ZMOD n]
  proof: Eq.trans

中文:
定理 trans
  结论: a ≡ b [ZMOD n] -> b ≡ c [ZMOD n] -> a ≡ c [ZMOD n]
  证明: Eq.trans
-/
protected theorem trans : a ≡ b [ZMOD n] -> b ≡ c [ZMOD n] -> a ≡ c [ZMOD n] :=
  Eq.trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans Int (ModEq n)
  body: @Int.ModEq.trans n

中文:
实例 :
  签名: IsTrans 整数 (ModEq n)
  定义体: @Int.ModEq.trans n

Depends on / 依赖: Int.ModEq.trans
-/
instance : IsTrans Int (ModEq n) where
  trans := @Int.ModEq.trans n

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  statement: a ≡ b [ZMOD n] -> a % n = b % n
  proof: id

中文:
定理 eq
  结论: a ≡ b [ZMOD n] -> a % n = b % n
  证明: id
-/
protected theorem eq : a ≡ b [ZMOD n] -> a % n = b % n := id

end ModEq

/--
theorem `modEq_comm` / 定理 `modEq_comm`

English:
theorem modEq_comm
  statement: a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n]
  proof: ⟨ModEq.symm, ModEq.symm⟩

@[simp, norm_cast]

中文:
定理 modEq_comm
  结论: a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n]
  证明: ⟨ModEq.symm, ModEq.symm⟩

@[simp, norm_cast]

Depends on / 依赖: ModEq.symm
-/
theorem modEq_comm : a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n] := ⟨ModEq.symm, ModEq.symm⟩

@[simp, norm_cast]
/--
theorem `natCast_modEq_iff` / 定理 `natCast_modEq_iff`

English:
theorem natCast_modEq_iff
  given: {a b n : Nat}
  statement: a ≡ b [ZMOD n] ↔ a ≡ b [MOD n]
  proof: by
  unfold ModEq Nat.ModEq; rw [← Int.ofNat_inj]; simp

中文:
定理 natCast_modEq_iff
  条件: {a b n : 自然数}
  结论: a ≡ b [ZMOD n] ↔ a ≡ b [MOD n]
  证明: by
  unfold ModEq Nat.ModEq; rw [← Int.ofNat_inj]; simp

Depends on / 依赖: Int.ofNat_inj, Nat.ModEq, ofNat_inj
-/
theorem natCast_modEq_iff {a b n : Nat} : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n] := by
  unfold ModEq Nat.ModEq; rw [← Int.ofNat_inj]; simp

/--
theorem `modEq_zero_iff_dvd` / 定理 `modEq_zero_iff_dvd`

English:
theorem modEq_zero_iff_dvd
  statement: a ≡ 0 [ZMOD n] ↔ n ∣ a
  proof: by
  rw [ModEq]; rw [zero_emod]; rw [dvd_iff_emod_eq_zero]

中文:
定理 modEq_zero_iff_dvd
  结论: a ≡ 0 [ZMOD n] ↔ n ∣ a
  证明: by
  rw [ModEq]; rw [zero_emod]; rw [dvd_iff_emod_eq_zero]

Depends on / 依赖: dvd_iff_emod_eq_zero, zero_emod
-/
theorem modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a := by
  rw [ModEq]; rw [zero_emod]; rw [dvd_iff_emod_eq_zero]

/--
theorem `_root_.Dvd.dvd.modEq_zero_int` / 定理 `_root_.Dvd.dvd.modEq_zero_int`

English:
theorem _root_.Dvd.dvd.modEq_zero_int
  given: (h : n ∣ a)
  statement: a ≡ 0 [ZMOD n]
  proof: modEq_zero_iff_dvd.2 h

中文:
定理 _root_.Dvd.dvd.modEq_zero_int
  条件: (h : n ∣ a)
  结论: a ≡ 0 [ZMOD n]
  证明: modEq_zero_iff_dvd.2 h

Depends on / 依赖: modEq_zero_iff_dvd
-/
theorem _root_.Dvd.dvd.modEq_zero_int (h : n ∣ a) : a ≡ 0 [ZMOD n] :=
  modEq_zero_iff_dvd.2 h

/--
theorem `_root_.Dvd.dvd.zero_modEq_int` / 定理 `_root_.Dvd.dvd.zero_modEq_int`

English:
theorem _root_.Dvd.dvd.zero_modEq_int
  given: (h : n ∣ a)
  statement: 0 ≡ a [ZMOD n]
  proof: h.modEq_zero_int.symm

中文:
定理 _root_.Dvd.dvd.zero_modEq_int
  条件: (h : n ∣ a)
  结论: 0 ≡ a [ZMOD n]
  证明: h.modEq_zero_int.symm

Depends on / 依赖: h.modEq_zero_int.symm, modEq_zero_int
-/
theorem _root_.Dvd.dvd.zero_modEq_int (h : n ∣ a) : 0 ≡ a [ZMOD n] :=
  h.modEq_zero_int.symm

/--
theorem `modEq_iff_dvd` / 定理 `modEq_iff_dvd`

English:
theorem modEq_iff_dvd
  statement: a ≡ b [ZMOD n] ↔ n ∣ b - a
  proof: by
  rw [ModEq]; rw [eq_comm]
  simp [emod_eq_emod_iff_emod_sub_eq_zero, dvd_iff_emod_eq_zero]

中文:
定理 modEq_iff_dvd
  结论: a ≡ b [ZMOD n] ↔ n ∣ b - a
  证明: by
  rw [ModEq]; rw [eq_comm]
  simp [emod_eq_emod_iff_emod_sub_eq_zero, dvd_iff_emod_eq_zero]

Depends on / 依赖: dvd_iff_emod_eq_zero, emod_eq_emod_iff_emod_sub_eq_zero, eq_comm
-/
theorem modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a := by
  rw [ModEq]; rw [eq_comm]
  simp [emod_eq_emod_iff_emod_sub_eq_zero, dvd_iff_emod_eq_zero]

/--
theorem `modEq_iff_add_fac` / 定理 `modEq_iff_add_fac`

English:
theorem modEq_iff_add_fac
  given: {a b n : Int}
  statement: a ≡ b [ZMOD n] ↔ exists t, b = a + n * t
  proof: by
  rw [modEq_iff_dvd]
  exact exists_congr fun t => sub_eq_iff_eq_add'

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd

中文:
定理 modEq_iff_add_fac
  条件: {a b n : 整数}
  结论: a ≡ b [ZMOD n] ↔ 存在 t, b = a + n * t
  证明: by
  rw [modEq_iff_dvd]
  exact exists_congr fun t => sub_eq_iff_eq_add'

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd

Depends on / 依赖: exists_congr, modEq_iff_dvd, sub_eq_iff_eq_add
-/
theorem modEq_iff_add_fac {a b n : Int} : a ≡ b [ZMOD n] ↔ exists t, b = a + n * t := by
  rw [modEq_iff_dvd]
  exact exists_congr fun t => sub_eq_iff_eq_add'

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd

/--
theorem `mod_modEq` / 定理 `mod_modEq`

English:
theorem mod_modEq
  given: (a n)
  statement: a % n ≡ a [ZMOD n]
  proof: emod_emod _ _

@[simp]

中文:
定理 mod_modEq
  条件: (a n)
  结论: a % n ≡ a [ZMOD n]
  证明: emod_emod _ _

@[simp]

Depends on / 依赖: emod_emod
-/
theorem mod_modEq (a n) : a % n ≡ a [ZMOD n] :=
  emod_emod _ _

@[simp]
/--
theorem `neg_modEq_neg` / 定理 `neg_modEq_neg`

English:
theorem neg_modEq_neg
  statement: -a ≡ -b [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  simp only [modEq_iff_dvd, (by lia : -b - -a = -(b - a)), Int.dvd_neg]

@[simp]

中文:
定理 neg_modEq_neg
  结论: -a ≡ -b [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  simp only [modEq_iff_dvd, (by lia : -b - -a = -(b - a)), Int.dvd_neg]

@[simp]

Depends on / 依赖: Int.dvd_neg, dvd_neg, modEq_iff_dvd
-/
theorem neg_modEq_neg : -a ≡ -b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp only [modEq_iff_dvd, (by lia : -b - -a = -(b - a)), Int.dvd_neg]

@[simp]
/--
theorem `modEq_neg` / 定理 `modEq_neg`

English:
theorem modEq_neg
  statement: a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n]
  proof: by simp [modEq_iff_dvd]

中文:
定理 modEq_neg
  结论: a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n]
  证明: by simp [modEq_iff_dvd]

Depends on / 依赖: modEq_iff_dvd
-/
theorem modEq_neg : a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n] := by simp [modEq_iff_dvd]

namespace ModEq

/--
theorem `of_dvd` / 定理 `of_dvd`

English:
theorem of_dvd
  given: (d : m ∣ n) (h : a ≡ b [ZMOD n])
  statement: a ≡ b [ZMOD m]
  proof: modEq_iff_dvd.2 d.trans h.dvd

中文:
定理 of_dvd
  条件: (d : m ∣ n) (h : a ≡ b [ZMOD n])
  结论: a ≡ b [ZMOD m]
  证明: modEq_iff_dvd.2 d.trans h.dvd
-/
protected theorem of_dvd (d : m ∣ n) (h : a ≡ b [ZMOD n]) : a ≡ b [ZMOD m] :=
modEq_iff_dvd.2 d.trans h.dvd

/--
theorem `mul_left'` / 定理 `mul_left'`

English:
theorem mul_left'
  given: (h : a ≡ b [ZMOD n])
  statement: c * a ≡ c * b [ZMOD c * n]
  proof: by
  obtain hc | rfl | hc := lt_trichotomy c 0
  · rw [← neg_modEq_neg, ← modEq_neg, ← Int.neg_mul, ← Int.neg_mul, ← Int.neg_mul]
    simp only [ModEq, mul_emod_mul_of_pos _ _ (neg_pos.2 hc), h.eq]
  · simp only [Int.zero_mul, ModEq.rfl]
  · simp only [ModEq, mul_emod_mul_of_pos _ _ hc, h.eq]

中文:
定理 mul_left'
  条件: (h : a ≡ b [ZMOD n])
  结论: c * a ≡ c * b [ZMOD c * n]
  证明: by
  obtain hc | rfl | hc := lt_trichotomy c 0
  · rw [← neg_modEq_neg, ← modEq_neg, ← Int.neg_mul, ← Int.neg_mul, ← Int.neg_mul]
    simp only [ModEq, mul_emod_mul_of_pos _ _ (neg_pos.2 hc), h.eq]
  · simp only [Int.zero_mul, ModEq.rfl]
  · simp only [ModEq, mul_emod_mul_of_pos _ _ hc, h.eq]
-/
protected theorem mul_left' (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD c * n] := by
  obtain hc | rfl | hc := lt_trichotomy c 0
  · rw [← neg_modEq_neg, ← modEq_neg, ← Int.neg_mul, ← Int.neg_mul, ← Int.neg_mul]
    simp only [ModEq, mul_emod_mul_of_pos _ _ (neg_pos.2 hc), h.eq]
  · simp only [Int.zero_mul, ModEq.rfl]
  · simp only [ModEq, mul_emod_mul_of_pos _ _ hc, h.eq]

/--
theorem `mul_right'` / 定理 `mul_right'`

English:
theorem mul_right'
  given: (h : a ≡ b [ZMOD n])
  statement: a * c ≡ b * c [ZMOD n * c]
  proof: by
  rw [mul_comm a]; rw [mul_comm b]; rw [mul_comm n]; exact h.mul_left'

@[gcongr]

中文:
定理 mul_right'
  条件: (h : a ≡ b [ZMOD n])
  结论: a * c ≡ b * c [ZMOD n * c]
  证明: by
  rw [mul_comm a]; rw [mul_comm b]; rw [mul_comm n]; exact h.mul_left'

@[gcongr]
-/
protected theorem mul_right' (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n * c] := by
  rw [mul_comm a]; rw [mul_comm b]; rw [mul_comm n]; exact h.mul_left'

@[gcongr]
/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n])
  statement: a + c ≡ b + d [ZMOD n]
  proof: modEq_iff_dvd.2 by convert! Int.dvd_add h₁.dvd h₂.dvd using 1; lia

中文:
定理 add
  条件: (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n])
  结论: a + c ≡ b + d [ZMOD n]
  证明: modEq_iff_dvd.2 by convert! Int.dvd_add h₁.dvd h₂.dvd using 1; lia
-/
protected theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
modEq_iff_dvd.2 by convert! Int.dvd_add h₁.dvd h₂.dvd using 1; lia

/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: (c : Int) (h : a ≡ b [ZMOD n])
  statement: c + a ≡ c + b [ZMOD n]
  proof: ModEq.rfl.add h

中文:
定理 add_left
  条件: (c : 整数) (h : a ≡ b [ZMOD n])
  结论: c + a ≡ c + b [ZMOD n]
  证明: ModEq.rfl.add h
-/
protected theorem add_left (c : Int) (h : a ≡ b [ZMOD n]) : c + a ≡ c + b [ZMOD n] :=
  ModEq.rfl.add h

/--
theorem `add_right` / 定理 `add_right`

English:
theorem add_right
  given: (c : Int) (h : a ≡ b [ZMOD n])
  statement: a + c ≡ b + c [ZMOD n]
  proof: h.add ModEq.rfl

中文:
定理 add_right
  条件: (c : 整数) (h : a ≡ b [ZMOD n])
  结论: a + c ≡ b + c [ZMOD n]
  证明: h.add ModEq.rfl
-/
protected theorem add_right (c : Int) (h : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] :=
  h.add ModEq.rfl

/--
theorem `add_left_cancel` / 定理 `add_left_cancel`

English:
theorem add_left_cancel
  given: (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n])
  proof: have : d - c = b + d - (a + c) - (b - a) := by lia
modEq_iff_dvd.2 by
    rw [this]
    exact Int.dvd_sub h₂.dvd h₁.dvd

中文:
定理 add_left_cancel
  条件: (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n])
  证明: have : d - c = b + d - (a + c) - (b - a) := by lia
modEq_iff_dvd.2 by
    rw [this]
    exact Int.dvd_sub h₂.dvd h₁.dvd
-/
protected theorem add_left_cancel (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    c ≡ d [ZMOD n] :=
  have : d - c = b + d - (a + c) - (b - a) := by lia
modEq_iff_dvd.2 by
    rw [this]
    exact Int.dvd_sub h₂.dvd h₁.dvd

/--
theorem `add_left_cancel'` / 定理 `add_left_cancel'`

English:
theorem add_left_cancel'
  given: (c : Int) (h : c + a ≡ c + b [ZMOD n])
  statement: a ≡ b [ZMOD n]
  proof: ModEq.rfl.add_left_cancel h

中文:
定理 add_left_cancel'
  条件: (c : 整数) (h : c + a ≡ c + b [ZMOD n])
  结论: a ≡ b [ZMOD n]
  证明: ModEq.rfl.add_left_cancel h
-/
protected theorem add_left_cancel' (c : Int) (h : c + a ≡ c + b [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_left_cancel h

/--
theorem `add_right_cancel` / 定理 `add_right_cancel`

English:
theorem add_right_cancel
  given: (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n])
  proof: by
  rw [add_comm a]; rw [add_comm b] at h₂
  exact h₁.add_left_cancel h₂

中文:
定理 add_right_cancel
  条件: (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n])
  证明: by
  rw [add_comm a]; rw [add_comm b] at h₂
  exact h₁.add_left_cancel h₂
-/
protected theorem add_right_cancel (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  rw [add_comm a]; rw [add_comm b] at h₂
  exact h₁.add_left_cancel h₂

/--
theorem `add_right_cancel'` / 定理 `add_right_cancel'`

English:
theorem add_right_cancel'
  given: (c : Int) (h : a + c ≡ b + c [ZMOD n])
  statement: a ≡ b [ZMOD n]
  proof: ModEq.rfl.add_right_cancel h

中文:
定理 add_right_cancel'
  条件: (c : 整数) (h : a + c ≡ b + c [ZMOD n])
  结论: a ≡ b [ZMOD n]
  证明: ModEq.rfl.add_right_cancel h
-/
protected theorem add_right_cancel' (c : Int) (h : a + c ≡ b + c [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_right_cancel h

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (h : a ≡ b [ZMOD n])
  statement: -a ≡ -b [ZMOD n]
  proof: h.add_left_cancel (by simp_rw [← sub_eq_add_neg, sub_self]; rfl)

@[gcongr]

中文:
定理 neg
  条件: (h : a ≡ b [ZMOD n])
  结论: -a ≡ -b [ZMOD n]
  证明: h.add_left_cancel (by simp_rw [← sub_eq_add_neg, sub_self]; rfl)

@[gcongr]
-/
@[gcongr] protected theorem neg (h : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] :=
  h.add_left_cancel (by simp_rw [← sub_eq_add_neg, sub_self]; rfl)

@[gcongr]
/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n])
  statement: a - c ≡ b - d [ZMOD n]
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

中文:
定理 sub
  条件: (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n])
  结论: a - c ≡ b - d [ZMOD n]
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]
  exact h₁.add h₂.neg
-/
protected theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n] := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

/--
theorem `sub_left` / 定理 `sub_left`

English:
theorem sub_left
  given: (c : Int) (h : a ≡ b [ZMOD n])
  statement: c - a ≡ c - b [ZMOD n]
  proof: ModEq.rfl.sub h

中文:
定理 sub_left
  条件: (c : 整数) (h : a ≡ b [ZMOD n])
  结论: c - a ≡ c - b [ZMOD n]
  证明: ModEq.rfl.sub h
-/
protected theorem sub_left (c : Int) (h : a ≡ b [ZMOD n]) : c - a ≡ c - b [ZMOD n] :=
  ModEq.rfl.sub h

/--
theorem `sub_right` / 定理 `sub_right`

English:
theorem sub_right
  given: (c : Int) (h : a ≡ b [ZMOD n])
  statement: a - c ≡ b - c [ZMOD n]
  proof: h.sub ModEq.rfl

中文:
定理 sub_right
  条件: (c : 整数) (h : a ≡ b [ZMOD n])
  结论: a - c ≡ b - c [ZMOD n]
  证明: h.sub ModEq.rfl
-/
protected theorem sub_right (c : Int) (h : a ≡ b [ZMOD n]) : a - c ≡ b - c [ZMOD n] :=
  h.sub ModEq.rfl

/--
theorem `mul_left` / 定理 `mul_left`

English:
theorem mul_left
  given: (c : Int) (h : a ≡ b [ZMOD n])
  statement: c * a ≡ c * b [ZMOD n]
  proof: h.mul_left'.of_dvd dvd_mul_left _ _

中文:
定理 mul_left
  条件: (c : 整数) (h : a ≡ b [ZMOD n])
  结论: c * a ≡ c * b [ZMOD n]
  证明: h.mul_left'.of_dvd dvd_mul_left _ _
-/
protected theorem mul_left (c : Int) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
h.mul_left'.of_dvd dvd_mul_left _ _

/--
theorem `mul_right` / 定理 `mul_right`

English:
theorem mul_right
  given: (c : Int) (h : a ≡ b [ZMOD n])
  statement: a * c ≡ b * c [ZMOD n]
  proof: h.mul_right'.of_dvd dvd_mul_right _ _

@[gcongr]

中文:
定理 mul_right
  条件: (c : 整数) (h : a ≡ b [ZMOD n])
  结论: a * c ≡ b * c [ZMOD n]
  证明: h.mul_right'.of_dvd dvd_mul_right _ _

@[gcongr]
-/
protected theorem mul_right (c : Int) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
h.mul_right'.of_dvd dvd_mul_right _ _

@[gcongr]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n])
  statement: a * c ≡ b * d [ZMOD n]
  proof: (h₂.mul_left _).trans (h₁.mul_right _)

中文:
定理 mul
  条件: (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n])
  结论: a * c ≡ b * d [ZMOD n]
  证明: (h₂.mul_left _).trans (h₁.mul_right _)
-/
protected theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)

/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: (m : Nat) (h : a ≡ b [ZMOD n])
  statement: a ^ m ≡ b ^ m [ZMOD n]
  proof: by
  induction m with
  | zero => simp
  | succ d hd => rw [pow_succ, pow_succ]; exact hd.mul h

中文:
定理 pow
  条件: (m : 自然数) (h : a ≡ b [ZMOD n])
  结论: a ^ m ≡ b ^ m [ZMOD n]
  证明: by
  induction m with
  | zero => simp
  | succ d hd => rw [pow_succ, pow_succ]; exact hd.mul h
-/
@[gcongr] protected theorem pow (m : Nat) (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] := by
  induction m with
  | zero => simp
  | succ d hd => rw [pow_succ, pow_succ]; exact hd.mul h

/--
lemma `of_mul_left` / 引理 `of_mul_left`

English:
lemma of_mul_left
  given: (m : Int) (h : a ≡ b [ZMOD m * n])
  statement: a ≡ b [ZMOD n]
  proof: by
  rw [modEq_iff_dvd] at *; exact (dvd_mul_left n m).trans h

中文:
引理 of_mul_left
  条件: (m : 整数) (h : a ≡ b [ZMOD m * n])
  结论: a ≡ b [ZMOD n]
  证明: by
  rw [modEq_iff_dvd] at *; exact (dvd_mul_left n m).trans h

Depends on / 依赖: dvd_mul_left, modEq_iff_dvd
-/
lemma of_mul_left (m : Int) (h : a ≡ b [ZMOD m * n]) : a ≡ b [ZMOD n] := by
  rw [modEq_iff_dvd] at *; exact (dvd_mul_left n m).trans h

/--
lemma `of_mul_right` / 引理 `of_mul_right`

English:
lemma of_mul_right
  given: (m : Int)
  statement: a ≡ b [ZMOD n * m] -> a ≡ b [ZMOD n]
  proof: mul_comm m n ▸ of_mul_left _

中文:
引理 of_mul_right
  条件: (m : 整数)
  结论: a ≡ b [ZMOD n * m] -> a ≡ b [ZMOD n]
  证明: mul_comm m n ▸ of_mul_left _

Depends on / 依赖: mul_comm, of_mul_left
-/
lemma of_mul_right (m : Int) : a ≡ b [ZMOD n * m] -> a ≡ b [ZMOD n] :=
  mul_comm m n ▸ of_mul_left _

/--
theorem `cancel_right_div_gcd` / 定理 `cancel_right_div_gcd`

English:
theorem cancel_right_div_gcd
  given: (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m])
  proof: by
  let d := gcd m c
  rw [modEq_iff_dvd] at h ⊢
  refine Int.dvd_of_dvd_mul_right_of_gcd_one (?_ : m / d ∣ c / d * (b - a)) ?_
  · rw [mul_comm, ← Int.mul_ediv_assoc (b - a) (gcd_dvd_right ..), Int.sub_mul]
    exact Int.ediv_dvd_ediv (gcd_dvd_left ..) h
  · rw [gcd_div (gcd_dvd_left ..) (gcd_dvd_

中文:
定理 cancel_right_div_gcd
  条件: (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m])
  证明: by
  let d := gcd m c
  rw [modEq_iff_dvd] at h ⊢
  refine Int.dvd_of_dvd_mul_right_of_gcd_one (?_ : m / d ∣ c / d * (b - a)) ?_
  · rw [mul_comm, ← Int.mul_ediv_assoc (b - a) (gcd_dvd_right ..), Int.sub_mul]
    exact Int.ediv_dvd_ediv (gcd_dvd_left ..) h
  · rw [gcd_div (gcd_dvd_left ..) (gcd_dvd_

Depends on / 依赖: Int.dvd_of_dvd_mul_right_of_gcd_one, Int.ediv_dvd_ediv, Int.mul_ediv_assoc, Int.sub_mul, Nat.div_self, div_self, dvd_of_dvd_mul_right_of_gcd_one, ediv_dvd_ediv, gcd_div, gcd_dvd_left, gcd_dvd_right, gcd_pos_of_ne_zero_left, hm.ne, modEq_iff_dvd, mul_comm, mul_ediv_assoc, natAbs_natCast, sub_mul
-/
theorem cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m]) :
    a ≡ b [ZMOD m / gcd m c] := by
  let d := gcd m c
  rw [modEq_iff_dvd] at h ⊢
  refine Int.dvd_of_dvd_mul_right_of_gcd_one (?_ : m / d ∣ c / d * (b - a)) ?_
  · rw [mul_comm, ← Int.mul_ediv_assoc (b - a) (gcd_dvd_right ..), Int.sub_mul]
    exact Int.ediv_dvd_ediv (gcd_dvd_left ..) h
  · rw [gcd_div (gcd_dvd_left ..) (gcd_dvd_right ..), natAbs_natCast,
      Nat.div_self (gcd_pos_of_ne_zero_left c hm.ne')]

/--
theorem `cancel_left_div_gcd` / 定理 `cancel_left_div_gcd`

English:
theorem cancel_left_div_gcd
  given: (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m])
  statement: a ≡ b [ZMOD m / gcd m c]
  proof: cancel_right_div_gcd hm by simpa [mul_comm] using h

中文:
定理 cancel_left_div_gcd
  条件: (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m])
  结论: a ≡ b [ZMOD m / gcd m c]
  证明: cancel_right_div_gcd hm by simpa [mul_comm] using h

Depends on / 依赖: cancel_right_div_gcd, mul_comm
-/
theorem cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m]) : a ≡ b [ZMOD m / gcd m c] :=
cancel_right_div_gcd hm by simpa [mul_comm] using h

/--
theorem `of_div` / 定理 `of_div`

English:
theorem of_div
  given: (h : a / c ≡ b / c [ZMOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m)
  proof: by convert! h.mul_left' <;> rwa [Int.mul_ediv_cancel']

中文:
定理 of_div
  条件: (h : a / c ≡ b / c [ZMOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m)
  证明: by convert! h.mul_left' <;> rwa [Int.mul_ediv_cancel']

Depends on / 依赖: Int.mul_ediv_cancel, convert, h.mul_left, mul_ediv_cancel, mul_left
-/
theorem of_div (h : a / c ≡ b / c [ZMOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
    a ≡ b [ZMOD m] := by convert! h.mul_left' <;> rwa [Int.mul_ediv_cancel']

/--
theorem `mul_left_cancel'` / 定理 `mul_left_cancel'`

English:
theorem mul_left_cancel'
  given: (hc : c != 0)
  proof: by
  simp only [modEq_iff_dvd, ← Int.mul_sub]
  exact Int.dvd_of_mul_dvd_mul_left hc

中文:
定理 mul_left_cancel'
  条件: (hc : c != 0)
  证明: by
  simp only [modEq_iff_dvd, ← Int.mul_sub]
  exact Int.dvd_of_mul_dvd_mul_left hc
-/
protected theorem mul_left_cancel' (hc : c != 0) :
    c * a ≡ c * b [ZMOD c * m] -> a ≡ b [ZMOD m] := by
  simp only [modEq_iff_dvd, ← Int.mul_sub]
  exact Int.dvd_of_mul_dvd_mul_left hc

/--
theorem `mul_left_cancel_iff'` / 定理 `mul_left_cancel_iff'`

English:
theorem mul_left_cancel_iff'
  given: (hc : c != 0)
  proof: ⟨ModEq.mul_left_cancel' hc, Int.ModEq.mul_left'⟩

中文:
定理 mul_left_cancel_iff'
  条件: (hc : c != 0)
  证明: ⟨ModEq.mul_left_cancel' hc, Int.ModEq.mul_left'⟩
-/
protected theorem mul_left_cancel_iff' (hc : c != 0) :
    c * a ≡ c * b [ZMOD c * m] ↔ a ≡ b [ZMOD m] :=
  ⟨ModEq.mul_left_cancel' hc, Int.ModEq.mul_left'⟩

/--
theorem `mul_right_cancel'` / 定理 `mul_right_cancel'`

English:
theorem mul_right_cancel'
  given: (hc : c != 0)
  proof: by
  simp only [modEq_iff_dvd, ← Int.sub_mul]
  exact Int.dvd_of_mul_dvd_mul_right hc

中文:
定理 mul_right_cancel'
  条件: (hc : c != 0)
  证明: by
  simp only [modEq_iff_dvd, ← Int.sub_mul]
  exact Int.dvd_of_mul_dvd_mul_right hc

Depends on / 依赖: K.subset_succ, monotone_nat_of_le_succ, subset_succ
-/
protected theorem mul_right_cancel' (hc : c != 0) :
    a * c ≡ b * c [ZMOD m * c] -> a ≡ b [ZMOD m] := by
  simp only [modEq_iff_dvd, ← Int.sub_mul]
  exact Int.dvd_of_mul_dvd_mul_right hc

/--
theorem `mul_right_cancel_iff'` / 定理 `mul_right_cancel_iff'`

English:
theorem mul_right_cancel_iff'
  given: (hc : c != 0)
  proof: ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right'⟩

中文:
定理 mul_right_cancel_iff'
  条件: (hc : c != 0)
  证明: ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right'⟩

Depends on / 依赖: K.finite, finite
-/
protected theorem mul_right_cancel_iff' (hc : c != 0) :
    a * c ≡ b * c [ZMOD m * c] ↔ a ≡ b [ZMOD m] :=
  ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right'⟩

/--
theorem `dvd_iff` / 定理 `dvd_iff`

English:
theorem dvd_iff
  given: (h : a ≡ b [ZMOD n])
  statement: n ∣ a ↔ n ∣ b
  proof: by
  simp only [← modEq_zero_iff_dvd]
  exact ⟨fun ha => h.symm.trans ha, h.trans⟩

中文:
定理 dvd_iff
  条件: (h : a ≡ b [ZMOD n])
  结论: n ∣ a ↔ n ∣ b
  证明: by
  simp only [← modEq_zero_iff_dvd]
  exact ⟨fun ha => h.symm.trans ha, h.trans⟩

Depends on / 依赖: h.symm.trans, h.trans, modEq_zero_iff_dvd
-/
theorem dvd_iff (h : a ≡ b [ZMOD n]) : n ∣ a ↔ n ∣ b := by
  simp only [← modEq_zero_iff_dvd]
  exact ⟨fun ha => h.symm.trans ha, h.trans⟩

end ModEq

@[simp]
/--
theorem `abs_modEq_two` / 定理 `abs_modEq_two`

English:
theorem abs_modEq_two
  statement: |a| ≡ a [ZMOD 2]
  proof: by
  grind [Int.ModEq]

@[simp]

中文:
定理 abs_modEq_two
  结论: |a| ≡ a [ZMOD 2]
  证明: by
  grind [Int.ModEq]

@[simp]

Depends on / 依赖: Int.ModEq
-/
theorem abs_modEq_two : |a| ≡ a [ZMOD 2] := by
  grind [Int.ModEq]

@[simp]
/--
theorem `modulus_modEq_zero` / 定理 `modulus_modEq_zero`

English:
theorem modulus_modEq_zero
  statement: n ≡ 0 [ZMOD n]
  proof: by simp [ModEq]

@[simp]

中文:
定理 modulus_modEq_zero
  结论: n ≡ 0 [ZMOD n]
  证明: by simp [ModEq]

@[simp]
-/
theorem modulus_modEq_zero : n ≡ 0 [ZMOD n] := by simp [ModEq]

@[simp]
/--
theorem `modEq_abs` / 定理 `modEq_abs`

English:
theorem modEq_abs
  statement: a ≡ b [ZMOD |n|] ↔ a ≡ b [ZMOD n]
  proof: by simp [ModEq]

中文:
定理 modEq_abs
  结论: a ≡ b [ZMOD |n|] ↔ a ≡ b [ZMOD n]
  证明: by simp [ModEq]
-/
theorem modEq_abs : a ≡ b [ZMOD |n|] ↔ a ≡ b [ZMOD n] := by simp [ModEq]

/--
theorem `modEq_natAbs` / 定理 `modEq_natAbs`

English:
theorem modEq_natAbs
  statement: a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n]
  proof: by simp [natCast_natAbs]

@[simp]

中文:
定理 modEq_natAbs
  结论: a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n]
  证明: by simp [natCast_natAbs]

@[simp]

Depends on / 依赖: natCast_natAbs
-/
theorem modEq_natAbs : a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n] := by simp [natCast_natAbs]

@[simp]
/--
theorem `add_modEq_left_iff` / 定理 `add_modEq_left_iff`

English:
theorem add_modEq_left_iff
  statement: a + b ≡ a [ZMOD n] ↔ n ∣ b
  proof: by
  simp [modEq_iff_dvd]

@[simp]

中文:
定理 add_modEq_left_iff
  结论: a + b ≡ a [ZMOD n] ↔ n ∣ b
  证明: by
  simp [modEq_iff_dvd]

@[simp]

Depends on / 依赖: modEq_iff_dvd
-/
theorem add_modEq_left_iff : a + b ≡ a [ZMOD n] ↔ n ∣ b := by
  simp [modEq_iff_dvd]

@[simp]
/--
theorem `add_modEq_right_iff` / 定理 `add_modEq_right_iff`

English:
theorem add_modEq_right_iff
  statement: a + b ≡ b [ZMOD n] ↔ n ∣ a
  proof: by
  rw [add_comm]; rw [add_modEq_left_iff]

@[simp]

中文:
定理 add_modEq_right_iff
  结论: a + b ≡ b [ZMOD n] ↔ n ∣ a
  证明: by
  rw [add_comm]; rw [add_modEq_left_iff]

@[simp]

Depends on / 依赖: add_comm, add_modEq_left_iff
-/
theorem add_modEq_right_iff : a + b ≡ b [ZMOD n] ↔ n ∣ a := by
  rw [add_comm]; rw [add_modEq_left_iff]

@[simp]
/--
theorem `left_modEq_add_iff` / 定理 `left_modEq_add_iff`

English:
theorem left_modEq_add_iff
  statement: a ≡ a + b [ZMOD n] ↔ n ∣ b
  proof: by
  rw [modEq_comm]; rw [add_modEq_left_iff]

@[simp]

中文:
定理 left_modEq_add_iff
  结论: a ≡ a + b [ZMOD n] ↔ n ∣ b
  证明: by
  rw [modEq_comm]; rw [add_modEq_left_iff]

@[simp]

Depends on / 依赖: add_modEq_left_iff, modEq_comm
-/
theorem left_modEq_add_iff : a ≡ a + b [ZMOD n] ↔ n ∣ b := by
  rw [modEq_comm]; rw [add_modEq_left_iff]

@[simp]
/--
theorem `right_modEq_add_iff` / 定理 `right_modEq_add_iff`

English:
theorem right_modEq_add_iff
  statement: b ≡ a + b [ZMOD n] ↔ n ∣ a
  proof: by
  rw [modEq_comm]; rw [add_modEq_right_iff]

@[simp]

中文:
定理 right_modEq_add_iff
  结论: b ≡ a + b [ZMOD n] ↔ n ∣ a
  证明: by
  rw [modEq_comm]; rw [add_modEq_right_iff]

@[simp]

Depends on / 依赖: add_modEq_right_iff, modEq_comm
-/
theorem right_modEq_add_iff : b ≡ a + b [ZMOD n] ↔ n ∣ a := by
  rw [modEq_comm]; rw [add_modEq_right_iff]

@[simp]
/--
theorem `add_modulus_modEq_iff` / 定理 `add_modulus_modEq_iff`

English:
theorem add_modulus_modEq_iff
  statement: a + n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 add_modulus_modEq_iff
  结论: a + n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem add_modulus_modEq_iff : a + n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modulus_add_modEq_iff` / 定理 `modulus_add_modEq_iff`

English:
theorem modulus_add_modEq_iff
  statement: n + a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  rw [add_comm]; rw [add_modulus_modEq_iff]

@[simp]

中文:
定理 modulus_add_modEq_iff
  结论: n + a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  rw [add_comm]; rw [add_modulus_modEq_iff]

@[simp]

Depends on / 依赖: add_comm, add_modulus_modEq_iff
-/
theorem modulus_add_modEq_iff : n + a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  rw [add_comm]; rw [add_modulus_modEq_iff]

@[simp]
/--
theorem `modEq_add_modulus_iff` / 定理 `modEq_add_modulus_iff`

English:
theorem modEq_add_modulus_iff
  statement: a ≡ b + n [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 modEq_add_modulus_iff
  结论: a ≡ b + n [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem modEq_add_modulus_iff : a ≡ b + n [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modEq_modulus_add_iff` / 定理 `modEq_modulus_add_iff`

English:
theorem modEq_modulus_add_iff
  statement: a ≡ n + b [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 modEq_modulus_add_iff
  结论: a ≡ n + b [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem modEq_modulus_add_iff : a ≡ n + b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `add_mul_modulus_modEq_iff` / 定理 `add_mul_modulus_modEq_iff`

English:
theorem add_mul_modulus_modEq_iff
  statement: a + b * n ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 add_mul_modulus_modEq_iff
  结论: a + b * n ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem add_mul_modulus_modEq_iff : a + b * n ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `mul_modulus_add_modEq_iff` / 定理 `mul_modulus_add_modEq_iff`

English:
theorem mul_modulus_add_modEq_iff
  statement: b * n + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  proof: by
  rw [add_comm]; rw [add_mul_modulus_modEq_iff]

@[simp]

中文:
定理 mul_modulus_add_modEq_iff
  结论: b * n + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  证明: by
  rw [add_comm]; rw [add_mul_modulus_modEq_iff]

@[simp]

Depends on / 依赖: add_comm, add_mul_modulus_modEq_iff
-/
theorem mul_modulus_add_modEq_iff : b * n + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [add_comm]; rw [add_mul_modulus_modEq_iff]

@[simp]
/--
theorem `modEq_add_mul_modulus_iff` / 定理 `modEq_add_mul_modulus_iff`

English:
theorem modEq_add_mul_modulus_iff
  statement: a ≡ b + c * n [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 modEq_add_mul_modulus_iff
  结论: a ≡ b + c * n [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem modEq_add_mul_modulus_iff : a ≡ b + c * n [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modEq_mul_modulus_add_iff` / 定理 `modEq_mul_modulus_add_iff`

English:
theorem modEq_mul_modulus_add_iff
  statement: a ≡ b * n + c [ZMOD n] ↔ a ≡ c [ZMOD n]
  proof: by
  rw [add_comm]; rw [modEq_add_mul_modulus_iff]

@[simp]

中文:
定理 modEq_mul_modulus_add_iff
  结论: a ≡ b * n + c [ZMOD n] ↔ a ≡ c [ZMOD n]
  证明: by
  rw [add_comm]; rw [modEq_add_mul_modulus_iff]

@[simp]

Depends on / 依赖: add_comm, modEq_add_mul_modulus_iff
-/
theorem modEq_mul_modulus_add_iff : a ≡ b * n + c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [add_comm]; rw [modEq_add_mul_modulus_iff]

@[simp]
/--
theorem `add_modulus_mul_modEq_iff` / 定理 `add_modulus_mul_modEq_iff`

English:
theorem add_modulus_mul_modEq_iff
  statement: a + n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 add_modulus_mul_modEq_iff
  结论: a + n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem add_modulus_mul_modEq_iff : a + n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modulus_mul_add_modEq_iff` / 定理 `modulus_mul_add_modEq_iff`

English:
theorem modulus_mul_add_modEq_iff
  statement: n * b + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  proof: by
  rw [add_comm]; rw [add_modulus_mul_modEq_iff]

@[simp]

中文:
定理 modulus_mul_add_modEq_iff
  结论: n * b + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  证明: by
  rw [add_comm]; rw [add_modulus_mul_modEq_iff]

@[simp]

Depends on / 依赖: add_comm, add_modulus_mul_modEq_iff
-/
theorem modulus_mul_add_modEq_iff : n * b + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [add_comm]; rw [add_modulus_mul_modEq_iff]

@[simp]
/--
theorem `modEq_add_modulus_mul_iff` / 定理 `modEq_add_modulus_mul_iff`

English:
theorem modEq_add_modulus_mul_iff
  statement: a ≡ b + n * c [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 modEq_add_modulus_mul_iff
  结论: a ≡ b + n * c [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem modEq_add_modulus_mul_iff : a ≡ b + n * c [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modEq_modulus_mul_add_iff` / 定理 `modEq_modulus_mul_add_iff`

English:
theorem modEq_modulus_mul_add_iff
  statement: a ≡ n * b + c [ZMOD n] ↔ a ≡ c [ZMOD n]
  proof: by
  rw [add_comm]; rw [modEq_add_modulus_mul_iff]

@[simp]

中文:
定理 modEq_modulus_mul_add_iff
  结论: a ≡ n * b + c [ZMOD n] ↔ a ≡ c [ZMOD n]
  证明: by
  rw [add_comm]; rw [modEq_add_modulus_mul_iff]

@[simp]

Depends on / 依赖: add_comm, modEq_add_modulus_mul_iff
-/
theorem modEq_modulus_mul_add_iff : a ≡ n * b + c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [add_comm]; rw [modEq_add_modulus_mul_iff]

@[simp]
/--
theorem `sub_modulus_modEq_iff` / 定理 `sub_modulus_modEq_iff`

English:
theorem sub_modulus_modEq_iff
  statement: a - n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  rw [← add_modulus_modEq_iff]; rw [sub_add_cancel]

@[simp]

中文:
定理 sub_modulus_modEq_iff
  结论: a - n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  rw [← add_modulus_modEq_iff]; rw [sub_add_cancel]

@[simp]

Depends on / 依赖: add_modulus_modEq_iff, sub_add_cancel
-/
theorem sub_modulus_modEq_iff : a - n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  rw [← add_modulus_modEq_iff]; rw [sub_add_cancel]

@[simp]
/--
theorem `sub_modulus_mul_modEq_iff` / 定理 `sub_modulus_mul_modEq_iff`

English:
theorem sub_modulus_mul_modEq_iff
  statement: a - n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  proof: by
  rw [← add_modulus_mul_modEq_iff]; rw [sub_add_cancel]

@[simp]

中文:
定理 sub_modulus_mul_modEq_iff
  结论: a - n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
  证明: by
  rw [← add_modulus_mul_modEq_iff]; rw [sub_add_cancel]

@[simp]

Depends on / 依赖: add_modulus_mul_modEq_iff, sub_add_cancel
-/
theorem sub_modulus_mul_modEq_iff : a - n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [← add_modulus_mul_modEq_iff]; rw [sub_add_cancel]

@[simp]
/--
theorem `modEq_sub_modulus_iff` / 定理 `modEq_sub_modulus_iff`

English:
theorem modEq_sub_modulus_iff
  statement: a ≡ b - n [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  rw [← modEq_add_modulus_iff]; rw [sub_add_cancel]

@[simp]

中文:
定理 modEq_sub_modulus_iff
  结论: a ≡ b - n [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  rw [← modEq_add_modulus_iff]; rw [sub_add_cancel]

@[simp]

Depends on / 依赖: modEq_add_modulus_iff, sub_add_cancel
-/
theorem modEq_sub_modulus_iff : a ≡ b - n [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  rw [← modEq_add_modulus_iff]; rw [sub_add_cancel]

@[simp]
/--
theorem `modEq_sub_modulus_mul_iff` / 定理 `modEq_sub_modulus_mul_iff`

English:
theorem modEq_sub_modulus_mul_iff
  statement: a ≡ b - n * c [ZMOD n] ↔ a ≡ b [ZMOD n]
  proof: by
  rw [← modEq_add_modulus_mul_iff]; rw [sub_add_cancel]

中文:
定理 modEq_sub_modulus_mul_iff
  结论: a ≡ b - n * c [ZMOD n] ↔ a ≡ b [ZMOD n]
  证明: by
  rw [← modEq_add_modulus_mul_iff]; rw [sub_add_cancel]

Depends on / 依赖: modEq_add_modulus_mul_iff, sub_add_cancel
-/
theorem modEq_sub_modulus_mul_iff : a ≡ b - n * c [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  rw [← modEq_add_modulus_mul_iff]; rw [sub_add_cancel]

/--
theorem `modEq_one` / 定理 `modEq_one`

English:
theorem modEq_one
  statement: a ≡ b [ZMOD 1]
  proof: modEq_of_dvd (one_dvd _)

中文:
定理 modEq_one
  结论: a ≡ b [ZMOD 1]
  证明: modEq_of_dvd (one_dvd _)

Depends on / 依赖: modEq_of_dvd, one_dvd
-/
theorem modEq_one : a ≡ b [ZMOD 1] :=
  modEq_of_dvd (one_dvd _)

/--
theorem `modEq_sub` / 定理 `modEq_sub`

English:
theorem modEq_sub
  given: (a b : Int)
  statement: a ≡ b [ZMOD a - b]
  proof: (modEq_of_dvd dvd_rfl).symm

@[simp]

中文:
定理 modEq_sub
  条件: (a b : 整数)
  结论: a ≡ b [ZMOD a - b]
  证明: (modEq_of_dvd dvd_rfl).symm

@[simp]

Depends on / 依赖: dvd_rfl, modEq_of_dvd
-/
theorem modEq_sub (a b : Int) : a ≡ b [ZMOD a - b] :=
  (modEq_of_dvd dvd_rfl).symm

@[simp]
/--
theorem `modEq_zero_iff` / 定理 `modEq_zero_iff`

English:
theorem modEq_zero_iff
  statement: a ≡ b [ZMOD 0] ↔ a = b
  proof: by rw [ModEq, emod_zero, emod_zero]

中文:
定理 modEq_zero_iff
  结论: a ≡ b [ZMOD 0] ↔ a = b
  证明: by rw [ModEq, emod_zero, emod_zero]

Depends on / 依赖: emod_zero
-/
theorem modEq_zero_iff : a ≡ b [ZMOD 0] ↔ a = b := by rw [ModEq, emod_zero, emod_zero]

/--
theorem `add_modEq_left` / 定理 `add_modEq_left`

English:
theorem add_modEq_left
  statement: n + a ≡ a [ZMOD n]
  proof: by simp

中文:
定理 add_modEq_left
  结论: n + a ≡ a [ZMOD n]
  证明: by simp
-/
theorem add_modEq_left : n + a ≡ a [ZMOD n] := by simp

/--
theorem `add_modEq_right` / 定理 `add_modEq_right`

English:
theorem add_modEq_right
  statement: a + n ≡ a [ZMOD n]
  proof: by simp

中文:
定理 add_modEq_right
  结论: a + n ≡ a [ZMOD n]
  证明: by simp
-/
theorem add_modEq_right : a + n ≡ a [ZMOD n] := by simp

/--
theorem `modEq_and_modEq_iff_modEq_lcm` / 定理 `modEq_and_modEq_iff_modEq_lcm`

English:
theorem modEq_and_modEq_iff_modEq_lcm
  given: {a b m n : Int}
  proof: by
  simp only [modEq_iff_dvd, coe_lcm_dvd_iff]

中文:
定理 modEq_and_modEq_iff_modEq_lcm
  条件: {a b m n : 整数}
  证明: by
  simp only [modEq_iff_dvd, coe_lcm_dvd_iff]

Depends on / 依赖: coe_lcm_dvd_iff, modEq_iff_dvd
-/
theorem modEq_and_modEq_iff_modEq_lcm {a b m n : Int} :
    a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m.lcm n] := by
  simp only [modEq_iff_dvd, coe_lcm_dvd_iff]

/--
theorem `modEq_and_modEq_iff_modEq_mul` / 定理 `modEq_and_modEq_iff_modEq_mul`

English:
theorem modEq_and_modEq_iff_modEq_mul
  given: {a b m n : Int} (hmn : m.natAbs.Coprime n.natAbs)
  proof: by
  convert! ← modEq_and_modEq_iff_modEq_lcm using 1
  rw [lcm_eq_mul_iff.mpr (.inr <| .inr hmn)]; rw [← natAbs_mul]; rw [modEq_natAbs]

中文:
定理 modEq_and_modEq_iff_modEq_mul
  条件: {a b m n : 整数} (hmn : m.natAbs.Coprime n.natAbs)
  证明: by
  convert! ← modEq_and_modEq_iff_modEq_lcm using 1
  rw [lcm_eq_mul_iff.mpr (.inr <| .inr hmn)]; rw [← natAbs_mul]; rw [modEq_natAbs]

Depends on / 依赖: convert, lcm_eq_mul_iff, lcm_eq_mul_iff.mpr, modEq_and_modEq_iff_modEq_lcm, modEq_natAbs, natAbs_mul
-/
theorem modEq_and_modEq_iff_modEq_mul {a b m n : Int} (hmn : m.natAbs.Coprime n.natAbs) :
    a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m * n] := by
  convert! ← modEq_and_modEq_iff_modEq_lcm using 1
  rw [lcm_eq_mul_iff.mpr (.inr <| .inr hmn)]; rw [← natAbs_mul]; rw [modEq_natAbs]

/--
theorem `gcd_a_modEq` / 定理 `gcd_a_modEq`

English:
theorem gcd_a_modEq
  given: (a b : Nat)
  statement: (a : Int) * Nat.gcdA a b ≡ Nat.gcd a b [ZMOD b]
  proof: by
  rw [← add_zero ((a : Int) * _)]; rw [Nat.gcd_eq_gcd_ab]
  exact (dvd_mul_right _ _).zero_modEq_int.add_left _

中文:
定理 gcd_a_modEq
  条件: (a b : 自然数)
  结论: (a : 整数) * 自然数.gcdA a b ≡ 自然数.gcd a b [ZMOD b]
  证明: by
  rw [← add_zero ((a : Int) * _)]; rw [Nat.gcd_eq_gcd_ab]
  exact (dvd_mul_right _ _).zero_modEq_int.add_left _

Depends on / 依赖: Nat.gcd_eq_gcd_ab, add_left, add_zero, dvd_mul_right, gcd_eq_gcd_ab, zero_modEq_int, zero_modEq_int.add_left
-/
theorem gcd_a_modEq (a b : Nat) : (a : Int) * Nat.gcdA a b ≡ Nat.gcd a b [ZMOD b] := by
  rw [← add_zero ((a : Int) * _)]; rw [Nat.gcd_eq_gcd_ab]
  exact (dvd_mul_right _ _).zero_modEq_int.add_left _

/--
theorem `modEq_add_fac_self` / 定理 `modEq_add_fac_self`

English:
theorem modEq_add_fac_self
  given: {a t n : Int}
  statement: a + n * t ≡ a [ZMOD n]
  proof: by simp

中文:
定理 modEq_add_fac_self
  条件: {a t n : 整数}
  结论: a + n * t ≡ a [ZMOD n]
  证明: by simp
-/
theorem modEq_add_fac_self {a t n : Int} : a + n * t ≡ a [ZMOD n] := by simp

/--
theorem `mod_coprime` / 定理 `mod_coprime`

English:
theorem mod_coprime
  given: {a b : Nat} (hab : Nat.Coprime a b)
  statement: exists y : Int, a * y ≡ 1 [ZMOD b]
  proof: ⟨Nat.gcdA a b,
    have hgcd : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hab
    calc
      ↑a * Nat.gcdA a b ≡ ↑a * Nat.gcdA a b + ↑b * Nat.gcdB a b [ZMOD ↑b] := by simp
      _ ≡ 1 [ZMOD ↑b] := by rw [← Nat.gcd_eq_gcd_ab, hgcd]; rfl
      ⟩

中文:
定理 mod_coprime
  条件: {a b : 自然数} (hab : 自然数.Coprime a b)
  结论: 存在 y : 整数, a * y ≡ 1 [ZMOD b]
  证明: ⟨Nat.gcdA a b,
    have hgcd : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hab
    calc
      ↑a * Nat.gcdA a b ≡ ↑a * Nat.gcdA a b + ↑b * Nat.gcdB a b [ZMOD ↑b] := by simp
      _ ≡ 1 [ZMOD ↑b] := by rw [← Nat.gcd_eq_gcd_ab, hgcd]; rfl
      ⟩

Depends on / 依赖: Coprime, Nat.Coprime.gcd_eq_one, Nat.gcd, Nat.gcdA, Nat.gcdB, Nat.gcd_eq_gcd_ab, gcd_eq_gcd_ab, gcd_eq_one
-/
theorem mod_coprime {a b : Nat} (hab : Nat.Coprime a b) : exists y : Int, a * y ≡ 1 [ZMOD b] :=
  ⟨Nat.gcdA a b,
    have hgcd : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hab
    calc
      ↑a * Nat.gcdA a b ≡ ↑a * Nat.gcdA a b + ↑b * Nat.gcdB a b [ZMOD ↑b] := by simp
      _ ≡ 1 [ZMOD ↑b] := by rw [← Nat.gcd_eq_gcd_ab, hgcd]; rfl
      ⟩

/--
theorem `existsUnique_equiv` / 定理 `existsUnique_equiv`

English:
theorem existsUnique_equiv
  given: (a : Int) {b : Int} (hb : 0 < b)
  proof: ⟨a % b, emod_nonneg _ (ne_of_gt hb),
    by
      have : a % b < |b| := emod_lt_abs _ (ne_of_gt hb)
      rwa [abs_of_pos hb] at this, by simp [ModEq]⟩

中文:
定理 existsUnique_equiv
  条件: (a : 整数) {b : 整数} (hb : 0 < b)
  证明: ⟨a % b, emod_nonneg _ (ne_of_gt hb),
    by
      have : a % b < |b| := emod_lt_abs _ (ne_of_gt hb)
      rwa [abs_of_pos hb] at this, by simp [ModEq]⟩

Depends on / 依赖: abs_of_pos, emod_lt_abs, emod_nonneg, ne_of_gt
-/
theorem existsUnique_equiv (a : Int) {b : Int} (hb : 0 < b) :
    exists z : Int, 0 <= z ∧ z < b ∧ z ≡ a [ZMOD b] :=
  ⟨a % b, emod_nonneg _ (ne_of_gt hb),
    by
      have : a % b < |b| := emod_lt_abs _ (ne_of_gt hb)
      rwa [abs_of_pos hb] at this, by simp [ModEq]⟩

/--
theorem `existsUnique_equiv_nat` / 定理 `existsUnique_equiv_nat`

English:
theorem existsUnique_equiv_nat
  given: (a : Int) {b : Int} (hb : 0 < b)
  statement: exists z : Nat, ↑z < b ∧ ↑z ≡ a [ZMOD b]
  proof: let ⟨z, hz1, hz2, hz3⟩ := existsUnique_equiv a hb
  ⟨z.natAbs, by
    constructor <;> rw [natAbs_of_nonneg hz1] <;> assumption⟩

中文:
定理 existsUnique_equiv_nat
  条件: (a : 整数) {b : 整数} (hb : 0 < b)
  结论: 存在 z : 自然数, ↑z < b ∧ ↑z ≡ a [ZMOD b]
  证明: let ⟨z, hz1, hz2, hz3⟩ := existsUnique_equiv a hb
  ⟨z.natAbs, by
    constructor <;> rw [natAbs_of_nonneg hz1] <;> assumption⟩

Depends on / 依赖: existsUnique_equiv, natAbs, natAbs_of_nonneg, z.natAbs
-/
theorem existsUnique_equiv_nat (a : Int) {b : Int} (hb : 0 < b) : exists z : Nat, ↑z < b ∧ ↑z ≡ a [ZMOD b] :=
  let ⟨z, hz1, hz2, hz3⟩ := existsUnique_equiv a hb
  ⟨z.natAbs, by
    constructor <;> rw [natAbs_of_nonneg hz1] <;> assumption⟩

/--
theorem `mod_mul_right_mod` / 定理 `mod_mul_right_mod`

English:
theorem mod_mul_right_mod
  given: (a b c : Int)
  statement: a % (b * c) % b = a % b
  proof: (mod_modEq _ _).of_mul_right _

中文:
定理 mod_mul_right_mod
  条件: (a b c : 整数)
  结论: a % (b * c) % b = a % b
  证明: (mod_modEq _ _).of_mul_right _

Depends on / 依赖: mod_modEq, of_mul_right
-/
theorem mod_mul_right_mod (a b c : Int) : a % (b * c) % b = a % b :=
  (mod_modEq _ _).of_mul_right _

/--
theorem `mod_mul_left_mod` / 定理 `mod_mul_left_mod`

English:
theorem mod_mul_left_mod
  given: (a b c : Int)
  statement: a % (b * c) % c = a % c
  proof: (mod_modEq _ _).of_mul_left _

中文:
定理 mod_mul_left_mod
  条件: (a b c : 整数)
  结论: a % (b * c) % c = a % c
  证明: (mod_modEq _ _).of_mul_left _

Depends on / 依赖: mod_modEq, of_mul_left
-/
theorem mod_mul_left_mod (a b c : Int) : a % (b * c) % c = a % c :=
  (mod_modEq _ _).of_mul_left _

/--
theorem `ext_ediv_modEq` / 定理 `ext_ediv_modEq`

English:
theorem ext_ediv_modEq
  given: {n a b : Int} (h0 : a / n = b / n) (h1 : a ≡ b [ZMOD n])
  statement: a = b
  proof: ext_ediv_emod h0 h1

中文:
定理 ext_ediv_modEq
  条件: {n a b : 整数} (h0 : a / n = b / n) (h1 : a ≡ b [ZMOD n])
  结论: a = b
  证明: ext_ediv_emod h0 h1

Depends on / 依赖: ext_ediv_emod
-/
theorem ext_ediv_modEq {n a b : Int} (h0 : a / n = b / n) (h1 : a ≡ b [ZMOD n]) : a = b :=
  ext_ediv_emod h0 h1

/--
theorem `ext_ediv_modEq_iff` / 定理 `ext_ediv_modEq_iff`

English:
theorem ext_ediv_modEq_iff
  given: (n a b : Int)
  statement: a = b ↔ a / n = b / n ∧ a ≡ b [ZMOD n]
  proof: ext_ediv_emod_iff _ _ _

中文:
定理 ext_ediv_modEq_iff
  条件: (n a b : 整数)
  结论: a = b ↔ a / n = b / n ∧ a ≡ b [ZMOD n]
  证明: ext_ediv_emod_iff _ _ _

Depends on / 依赖: ext_ediv_emod_iff
-/
theorem ext_ediv_modEq_iff (n a b : Int) : a = b ↔ a / n = b / n ∧ a ≡ b [ZMOD n] :=
  ext_ediv_emod_iff _ _ _

/--
theorem `modEq_iff_eq_of_div_eq` / 定理 `modEq_iff_eq_of_div_eq`

English:
theorem modEq_iff_eq_of_div_eq
  given: {n a b : Int} (h : a / n = b / n)
  proof: by grind [ext_ediv_modEq_iff]

中文:
定理 modEq_iff_eq_of_div_eq
  条件: {n a b : 整数} (h : a / n = b / n)
  证明: by grind [ext_ediv_modEq_iff]

Depends on / 依赖: ext_ediv_modEq_iff
-/
theorem modEq_iff_eq_of_div_eq {n a b : Int} (h : a / n = b / n) :
    a ≡ b [ZMOD n] ↔ a = b := by grind [ext_ediv_modEq_iff]

end Int
