/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Algebra.CharZero.Defs

/-!
# Congruences modulo a natural number

This file defines the equivalence relation `a ≡ b [MOD n]` on the natural numbers,
and proves basic properties about it such as the Chinese Remainder Theorem
`modEq_and_modEq_iff_modEq_mul`.

## Notation

`a ≡ b [MOD n]` is notation for `Nat.ModEq n a b`, which is defined to mean `a % n = b % n`.

## Tags

ModEq, congruence, mod, MOD, modulo
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Function.support

/--
Definition of `Nat.ModEq` / `Nat.ModEq` 的定义

English:
definition Nat.ModEq
  signature: (n a b : Nat)
  body: a % n = b % n

@[inherit_doc]
notation:50 a " ≡ " b " [MOD " n "]" => Nat.ModEq n a b

中文:
定义 自然数.ModEq
  签名: (n a b : 自然数)
  定义体: a % n = b % n

@[inherit_doc]
notation:50 a " ≡ " b " [MOD " n "]" => Nat.ModEq n a b
-/
def Nat.ModEq (n a b : Nat) :=
  a % n = b % n

@[inherit_doc]
notation:50 a " ≡ " b " [MOD " n "]" => Nat.ModEq n a b

namespace AddCommGroup

@[simp]
/--
theorem `modEq_iff_natModEq` / 定理 `modEq_iff_natModEq`

English:
theorem modEq_iff_natModEq
  given: {a b n : Nat}
  statement: a ≡ b [PMOD n] ↔ a ≡ b [MOD n]
  proof: by
  constructor
  · rw [modEq_iff_nsmul, Nat.ModEq]
    rintro ⟨k, l, h⟩
    simpa using congr($h % n)
  · rw [Nat.ModEq]
    intro h
    rw [← Nat.div_add_mod' a n]; rw [← Nat.div_add_mod' b n]; rw [← Nat.nsmul_eq_mul]; rw [← Nat.nsmul_eq_mul]; rw [h]
.trans (nsmul_add_modEq _).symm exact nsmul_ad

中文:
定理 modEq_iff_natModEq
  条件: {a b n : 自然数}
  结论: a ≡ b [PMOD n] ↔ a ≡ b [MOD n]
  证明: by
  constructor
  · rw [modEq_iff_nsmul, Nat.ModEq]
    rintro ⟨k, l, h⟩
    simpa using congr($h % n)
  · rw [Nat.ModEq]
    intro h
    rw [← Nat.div_add_mod' a n]; rw [← Nat.div_add_mod' b n]; rw [← Nat.nsmul_eq_mul]; rw [← Nat.nsmul_eq_mul]; rw [h]
.trans (nsmul_add_modEq _).symm exact nsmul_ad

Depends on / 依赖: Nat.ModEq, Nat.div_add_mod, Nat.nsmul_eq_mul, div_add_mod, modEq_iff_nsmul, nsmul_add_modEq, nsmul_eq_mul
-/
theorem modEq_iff_natModEq {a b n : Nat} : a ≡ b [PMOD n] ↔ a ≡ b [MOD n] := by
  constructor
  · rw [modEq_iff_nsmul, Nat.ModEq]
    rintro ⟨k, l, h⟩
    simpa using congr($h % n)
  · rw [Nat.ModEq]
    intro h
    rw [← Nat.div_add_mod' a n]; rw [← Nat.div_add_mod' b n]; rw [← Nat.nsmul_eq_mul]; rw [← Nat.nsmul_eq_mul]; rw [h]
.trans (nsmul_add_modEq _).symm exact nsmul_add_modEq _

variable {M : Type*} [AddCommMonoidWithOne M]

/--
theorem `ModEq.natCast` / 定理 `ModEq.natCast`

English:
theorem ModEq.natCast
  given: {a b n : Nat} (h : a ≡ b [MOD n])
  statement: a ≡ b [PMOD (n : M)]
  proof: by
  rw [← modEq_iff_natModEq] at h
  exact h.map (Nat.castAddMonoidHom M)

@[simp, norm_cast]

中文:
定理 ModEq.natCast
  条件: {a b n : 自然数} (h : a ≡ b [MOD n])
  结论: a ≡ b [PMOD (n : M)]
  证明: by
  rw [← modEq_iff_natModEq] at h
  exact h.map (Nat.castAddMonoidHom M)

@[simp, norm_cast]

Depends on / 依赖: Nat.castAddMonoidHom, castAddMonoidHom, h.map, modEq_iff_natModEq
-/
theorem ModEq.natCast {a b n : Nat} (h : a ≡ b [MOD n]) : a ≡ b [PMOD (n : M)] := by
  rw [← modEq_iff_natModEq] at h
  exact h.map (Nat.castAddMonoidHom M)

@[simp, norm_cast]
/--
theorem `natCast_modEq_natCast` / 定理 `natCast_modEq_natCast`

English:
theorem natCast_modEq_natCast
  given: [CharZero M] {a b n : Nat}
  statement: a ≡ b [PMOD (n : M)] ↔ a ≡ b [MOD n]
  proof: by
  simpa using map_modEq_iff (Nat.castAddMonoidHom M) Nat.cast_injective

alias ⟨_root_.Nat.ModEq.of_natCast, _⟩ := natCast_modEq_natCast

中文:
定理 natCast_modEq_natCast
  条件: [特征零 M] {a b n : 自然数}
  结论: a ≡ b [PMOD (n : M)] ↔ a ≡ b [MOD n]
  证明: by
  simpa using map_modEq_iff (Nat.castAddMonoidHom M) Nat.cast_injective

alias ⟨_root_.Nat.ModEq.of_natCast, _⟩ := natCast_modEq_natCast

Depends on / 依赖: Nat.castAddMonoidHom, Nat.cast_injective, castAddMonoidHom, cast_injective, map_modEq_iff
-/
theorem natCast_modEq_natCast [CharZero M] {a b n : Nat} : a ≡ b [PMOD (n : M)] ↔ a ≡ b [MOD n] := by
  simpa using map_modEq_iff (Nat.castAddMonoidHom M) Nat.cast_injective

alias ⟨_root_.Nat.ModEq.of_natCast, _⟩ := natCast_modEq_natCast

end AddCommGroup

namespace Nat

variable {m n a b c d : Nat}

-- Since `ModEq` is semi-reducible, we need to provide the decidable instance manually
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Decidable (ModEq n a b)
  body: inferInstanceAs Decidable (a % n = b % n)

中文:
实例 :
  签名: 可判定 (ModEq n a b)
  定义体: inferInstanceAs Decidable (a % n = b % n)

Depends on / 依赖: Decidable
-/
instance : Decidable (ModEq n a b) := inferInstanceAs Decidable (a % n = b % n)

namespace ModEq

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (a : Nat)
  statement: a ≡ a [MOD n]
  proof: rfl

中文:
定理 refl
  条件: (a : 自然数)
  结论: a ≡ a [MOD n]
  证明: rfl
-/
protected theorem refl (a : Nat) : a ≡ a [MOD n] := rfl

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  statement: a ≡ a [MOD n]
  proof: ModEq.refl _

中文:
定理 rfl
  结论: a ≡ a [MOD n]
  证明: ModEq.refl _
-/
protected theorem rfl : a ≡ a [MOD n] :=
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
  statement: a ≡ b [MOD n] -> b ≡ a [MOD n]
  proof: Eq.symm

@[trans]

中文:
定理 symm
  结论: a ≡ b [MOD n] -> b ≡ a [MOD n]
  证明: Eq.symm

@[trans]
-/
protected theorem symm : a ≡ b [MOD n] -> b ≡ a [MOD n] :=
  Eq.symm

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: a ≡ b [MOD n] -> b ≡ c [MOD n] -> a ≡ c [MOD n]
  proof: Eq.trans

中文:
定理 trans
  结论: a ≡ b [MOD n] -> b ≡ c [MOD n] -> a ≡ c [MOD n]
  证明: Eq.trans
-/
protected theorem trans : a ≡ b [MOD n] -> b ≡ c [MOD n] -> a ≡ c [MOD n] :=
  Eq.trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (ModEq n) (ModEq n) (ModEq n)
  body: Nat.ModEq.trans

中文:
实例 :
  签名: Trans (ModEq n) (ModEq n) (ModEq n)
  定义体: Nat.ModEq.trans

Depends on / 依赖: Nat.ModEq.trans
-/
instance : Trans (ModEq n) (ModEq n) (ModEq n) where
  trans := Nat.ModEq.trans

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  statement: a ≡ b [MOD n] ↔ b ≡ a [MOD n]
  proof: ⟨ModEq.symm, ModEq.symm⟩

中文:
定理 comm
  结论: a ≡ b [MOD n] ↔ b ≡ a [MOD n]
  证明: ⟨ModEq.symm, ModEq.symm⟩
-/
protected theorem comm : a ≡ b [MOD n] ↔ b ≡ a [MOD n] :=
  ⟨ModEq.symm, ModEq.symm⟩

end ModEq

/--
theorem `modEq_zero_iff_dvd` / 定理 `modEq_zero_iff_dvd`

English:
theorem modEq_zero_iff_dvd
  statement: a ≡ 0 [MOD n] ↔ n ∣ a
  proof: by rw [ModEq, zero_mod, dvd_iff_mod_eq_zero]

中文:
定理 modEq_zero_iff_dvd
  结论: a ≡ 0 [MOD n] ↔ n ∣ a
  证明: by rw [ModEq, zero_mod, dvd_iff_mod_eq_zero]

Depends on / 依赖: dvd_iff_mod_eq_zero, zero_mod
-/
theorem modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a := by rw [ModEq, zero_mod, dvd_iff_mod_eq_zero]

/--
theorem `_root_.Dvd.dvd.modEq_zero_nat` / 定理 `_root_.Dvd.dvd.modEq_zero_nat`

English:
theorem _root_.Dvd.dvd.modEq_zero_nat
  given: (h : n ∣ a)
  statement: a ≡ 0 [MOD n]
  proof: modEq_zero_iff_dvd.2 h

中文:
定理 _root_.Dvd.dvd.modEq_zero_nat
  条件: (h : n ∣ a)
  结论: a ≡ 0 [MOD n]
  证明: modEq_zero_iff_dvd.2 h

Depends on / 依赖: modEq_zero_iff_dvd
-/
theorem _root_.Dvd.dvd.modEq_zero_nat (h : n ∣ a) : a ≡ 0 [MOD n] :=
  modEq_zero_iff_dvd.2 h

/--
theorem `_root_.Dvd.dvd.zero_modEq_nat` / 定理 `_root_.Dvd.dvd.zero_modEq_nat`

English:
theorem _root_.Dvd.dvd.zero_modEq_nat
  given: (h : n ∣ a)
  statement: 0 ≡ a [MOD n]
  proof: h.modEq_zero_nat.symm

中文:
定理 _root_.Dvd.dvd.zero_modEq_nat
  条件: (h : n ∣ a)
  结论: 0 ≡ a [MOD n]
  证明: h.modEq_zero_nat.symm

Depends on / 依赖: h.modEq_zero_nat.symm, modEq_zero_nat
-/
theorem _root_.Dvd.dvd.zero_modEq_nat (h : n ∣ a) : 0 ≡ a [MOD n] :=
  h.modEq_zero_nat.symm

/--
theorem `modEq_iff_dvd` / 定理 `modEq_iff_dvd`

English:
theorem modEq_iff_dvd
  statement: a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
  proof: by
  rw [ModEq]; rw [eq_comm]; rw [← Int.natCast_inj]; rw [Int.natCast_mod]; rw [Int.natCast_mod]; rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]; rw [Int.dvd_iff_emod_eq_zero]

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd

中文:
定理 modEq_iff_dvd
  结论: a ≡ b [MOD n] ↔ (n : 整数) ∣ b - a
  证明: by
  rw [ModEq]; rw [eq_comm]; rw [← Int.natCast_inj]; rw [Int.natCast_mod]; rw [Int.natCast_mod]; rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]; rw [Int.dvd_iff_emod_eq_zero]

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd

Depends on / 依赖: Int.dvd_iff_emod_eq_zero, Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.natCast_inj, Int.natCast_mod, dvd_iff_emod_eq_zero, emod_eq_emod_iff_emod_sub_eq_zero, eq_comm, natCast_inj, natCast_mod
-/
theorem modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a := by
  rw [ModEq]; rw [eq_comm]; rw [← Int.natCast_inj]; rw [Int.natCast_mod]; rw [Int.natCast_mod]; rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]; rw [Int.dvd_iff_emod_eq_zero]

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd

/--
theorem `modEq_iff_dvd'` / 定理 `modEq_iff_dvd'`

English:
theorem modEq_iff_dvd'
  given: (h : a <= b)
  statement: a ≡ b [MOD n] ↔ n ∣ b - a
  proof: by
  rw [modEq_iff_dvd]; rw [← Int.natCast_dvd_natCast]; rw [Int.ofNat_sub h]

中文:
定理 modEq_iff_dvd'
  条件: (h : a <= b)
  结论: a ≡ b [MOD n] ↔ n ∣ b - a
  证明: by
  rw [modEq_iff_dvd]; rw [← Int.natCast_dvd_natCast]; rw [Int.ofNat_sub h]

Depends on / 依赖: Int.natCast_dvd_natCast, Int.ofNat_sub, modEq_iff_dvd, natCast_dvd_natCast, ofNat_sub
-/
theorem modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b - a := by
  rw [modEq_iff_dvd]; rw [← Int.natCast_dvd_natCast]; rw [Int.ofNat_sub h]

/--
theorem `ModEq.dvd'` / 定理 `ModEq.dvd'`

English:
theorem ModEq.dvd'
  given: (h : a ≡ b [MOD n])
  statement: n ∣ b - a
  proof: by
  obtain h0 | h0 : a <= b ∨ b <= a := le_total a b
  · exact (modEq_iff_dvd' h0).mp h
  · rw [Nat.sub_eq_zero_of_le h0]
    exact Nat.dvd_zero n

alias ⟨_, modEq_of_dvd'⟩ := modEq_iff_dvd'

中文:
定理 ModEq.dvd'
  条件: (h : a ≡ b [MOD n])
  结论: n ∣ b - a
  证明: by
  obtain h0 | h0 : a <= b ∨ b <= a := le_total a b
  · exact (modEq_iff_dvd' h0).mp h
  · rw [Nat.sub_eq_zero_of_le h0]
    exact Nat.dvd_zero n

alias ⟨_, modEq_of_dvd'⟩ := modEq_iff_dvd'

Depends on / 依赖: Nat.dvd_zero, Nat.sub_eq_zero_of_le, dvd_zero, le_total, modEq_iff_dvd, sub_eq_zero_of_le
-/
theorem ModEq.dvd' (h : a ≡ b [MOD n]) : n ∣ b - a := by
  obtain h0 | h0 : a <= b ∨ b <= a := le_total a b
  · exact (modEq_iff_dvd' h0).mp h
  · rw [Nat.sub_eq_zero_of_le h0]
    exact Nat.dvd_zero n

alias ⟨_, modEq_of_dvd'⟩ := modEq_iff_dvd'

/--
theorem `mod_modEq` / 定理 `mod_modEq`

English:
theorem mod_modEq
  given: (a n)
  statement: a % n ≡ a [MOD n]
  proof: mod_mod _ _

中文:
定理 mod_modEq
  条件: (a n)
  结论: a % n ≡ a [MOD n]
  证明: mod_mod _ _

Depends on / 依赖: mod_mod
-/
theorem mod_modEq (a n) : a % n ≡ a [MOD n] :=
  mod_mod _ _

namespace ModEq

/--
theorem `modulus_mul_add` / 定理 `modulus_mul_add`

English:
theorem modulus_mul_add
  statement: m * a + b ≡ b [MOD m]
  proof: by simp [Nat.ModEq]

中文:
定理 modulus_mul_add
  结论: m * a + b ≡ b [MOD m]
  证明: by simp [Nat.ModEq]

Depends on / 依赖: Nat.ModEq
-/
theorem modulus_mul_add : m * a + b ≡ b [MOD m] := by simp [Nat.ModEq]

/--
lemma `of_dvd` / 引理 `of_dvd`

English:
lemma of_dvd
  given: (d : m ∣ n) (h : a ≡ b [MOD n])
  statement: a ≡ b [MOD m]
  proof: modEq_of_dvd .trans h.dvd Int.ofNat_dvd.mpr d

中文:
引理 of_dvd
  条件: (d : m ∣ n) (h : a ≡ b [MOD n])
  结论: a ≡ b [MOD m]
  证明: modEq_of_dvd .trans h.dvd Int.ofNat_dvd.mpr d

Depends on / 依赖: Int.ofNat_dvd.mpr, h.dvd, modEq_of_dvd, ofNat_dvd
-/
lemma of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m] :=
modEq_of_dvd .trans h.dvd Int.ofNat_dvd.mpr d

/--
theorem `mul_left'` / 定理 `mul_left'`

English:
theorem mul_left'
  given: (c : Nat) (h : a ≡ b [MOD n])
  statement: c * a ≡ c * b [MOD c * n]
  proof: by
  unfold ModEq at *; rw [mul_mod_mul_left, mul_mod_mul_left, h]

中文:
定理 mul_left'
  条件: (c : 自然数) (h : a ≡ b [MOD n])
  结论: c * a ≡ c * b [MOD c * n]
  证明: by
  unfold ModEq at *; rw [mul_mod_mul_left, mul_mod_mul_left, h]
-/
protected theorem mul_left' (c : Nat) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD c * n] := by
  unfold ModEq at *; rw [mul_mod_mul_left, mul_mod_mul_left, h]

/--
theorem `mul_left` / 定理 `mul_left`

English:
theorem mul_left
  given: (c : Nat) (h : a ≡ b [MOD n])
  statement: c * a ≡ c * b [MOD n]
  proof: (h.mul_left' _).of_dvd (dvd_mul_left _ _)

中文:
定理 mul_left
  条件: (c : 自然数) (h : a ≡ b [MOD n])
  结论: c * a ≡ c * b [MOD n]
  证明: (h.mul_left' _).of_dvd (dvd_mul_left _ _)
-/
protected theorem mul_left (c : Nat) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] :=
  (h.mul_left' _).of_dvd (dvd_mul_left _ _)

/--
theorem `mul_right'` / 定理 `mul_right'`

English:
theorem mul_right'
  given: (c : Nat) (h : a ≡ b [MOD n])
  statement: a * c ≡ b * c [MOD n * c]
  proof: by
  rw [mul_comm a]; rw [mul_comm b]; rw [mul_comm n]; exact h.mul_left' c

中文:
定理 mul_right'
  条件: (c : 自然数) (h : a ≡ b [MOD n])
  结论: a * c ≡ b * c [MOD n * c]
  证明: by
  rw [mul_comm a]; rw [mul_comm b]; rw [mul_comm n]; exact h.mul_left' c
-/
protected theorem mul_right' (c : Nat) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n * c] := by
  rw [mul_comm a]; rw [mul_comm b]; rw [mul_comm n]; exact h.mul_left' c

/--
theorem `mul_right` / 定理 `mul_right`

English:
theorem mul_right
  given: (c : Nat) (h : a ≡ b [MOD n])
  statement: a * c ≡ b * c [MOD n]
  proof: by
  rw [mul_comm a]; rw [mul_comm b]; exact h.mul_left c

@[gcongr]

中文:
定理 mul_right
  条件: (c : 自然数) (h : a ≡ b [MOD n])
  结论: a * c ≡ b * c [MOD n]
  证明: by
  rw [mul_comm a]; rw [mul_comm b]; exact h.mul_left c

@[gcongr]
-/
protected theorem mul_right (c : Nat) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n] := by
  rw [mul_comm a]; rw [mul_comm b]; exact h.mul_left c

@[gcongr]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n])
  statement: a * c ≡ b * d [MOD n]
  proof: (h₂.mul_left _).trans (h₁.mul_right _)

@[gcongr]

中文:
定理 mul
  条件: (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n])
  结论: a * c ≡ b * d [MOD n]
  证明: (h₂.mul_left _).trans (h₁.mul_right _)

@[gcongr]
-/
protected theorem mul (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)

@[gcongr]
/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: (m : Nat) (h : a ≡ b [MOD n])
  statement: a ^ m ≡ b ^ m [MOD n]
  proof: by
  induction m with
  | zero => rfl
  | succ d hd =>
    rw [Nat.pow_succ]; rw [Nat.pow_succ]
    exact hd.mul h

@[gcongr]

中文:
定理 pow
  条件: (m : 自然数) (h : a ≡ b [MOD n])
  结论: a ^ m ≡ b ^ m [MOD n]
  证明: by
  induction m with
  | zero => rfl
  | succ d hd =>
    rw [Nat.pow_succ]; rw [Nat.pow_succ]
    exact hd.mul h

@[gcongr]
-/
protected theorem pow (m : Nat) (h : a ≡ b [MOD n]) : a ^ m ≡ b ^ m [MOD n] := by
  induction m with
  | zero => rfl
  | succ d hd =>
    rw [Nat.pow_succ]; rw [Nat.pow_succ]
    exact hd.mul h

@[gcongr]
/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n])
  statement: a + c ≡ b + d [MOD n]
  proof: by
  rw [modEq_iff_dvd]; rw [Int.natCast_add]; rw [Int.natCast_add]; rw [add_sub_add_comm]
  exact Int.dvd_add h₁.dvd h₂.dvd

中文:
定理 add
  条件: (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n])
  结论: a + c ≡ b + d [MOD n]
  证明: by
  rw [modEq_iff_dvd]; rw [Int.natCast_add]; rw [Int.natCast_add]; rw [add_sub_add_comm]
  exact Int.dvd_add h₁.dvd h₂.dvd
-/
protected theorem add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] := by
  rw [modEq_iff_dvd]; rw [Int.natCast_add]; rw [Int.natCast_add]; rw [add_sub_add_comm]
  exact Int.dvd_add h₁.dvd h₂.dvd

/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: (c : Nat) (h : a ≡ b [MOD n])
  statement: c + a ≡ c + b [MOD n]
  proof: ModEq.rfl.add h

中文:
定理 add_left
  条件: (c : 自然数) (h : a ≡ b [MOD n])
  结论: c + a ≡ c + b [MOD n]
  证明: ModEq.rfl.add h
-/
protected theorem add_left (c : Nat) (h : a ≡ b [MOD n]) : c + a ≡ c + b [MOD n] :=
  ModEq.rfl.add h

/--
theorem `add_right` / 定理 `add_right`

English:
theorem add_right
  given: (c : Nat) (h : a ≡ b [MOD n])
  statement: a + c ≡ b + c [MOD n]
  proof: h.add ModEq.rfl

中文:
定理 add_right
  条件: (c : 自然数) (h : a ≡ b [MOD n])
  结论: a + c ≡ b + c [MOD n]
  证明: h.add ModEq.rfl
-/
protected theorem add_right (c : Nat) (h : a ≡ b [MOD n]) : a + c ≡ b + c [MOD n] :=
  h.add ModEq.rfl

/--
theorem `add_left_cancel` / 定理 `add_left_cancel`

English:
theorem add_left_cancel
  given: (h₁ : a ≡ b [MOD n]) (h₂ : a + c ≡ b + d [MOD n])
  proof: by
  simp only [modEq_iff_dvd, Int.natCast_add] at *
  rw [add_sub_add_comm] at h₂
  convert! Int.dvd_sub h₂ h₁ using 1
  rw [add_sub_cancel_left]

中文:
定理 add_left_cancel
  条件: (h₁ : a ≡ b [MOD n]) (h₂ : a + c ≡ b + d [MOD n])
  证明: by
  simp only [modEq_iff_dvd, Int.natCast_add] at *
  rw [add_sub_add_comm] at h₂
  convert! Int.dvd_sub h₂ h₁ using 1
  rw [add_sub_cancel_left]
-/
protected theorem add_left_cancel (h₁ : a ≡ b [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
    c ≡ d [MOD n] := by
  simp only [modEq_iff_dvd, Int.natCast_add] at *
  rw [add_sub_add_comm] at h₂
  convert! Int.dvd_sub h₂ h₁ using 1
  rw [add_sub_cancel_left]

/--
theorem `add_left_cancel'` / 定理 `add_left_cancel'`

English:
theorem add_left_cancel'
  given: (c : Nat) (h : c + a ≡ c + b [MOD n])
  statement: a ≡ b [MOD n]
  proof: ModEq.rfl.add_left_cancel h

@[simp]

中文:
定理 add_left_cancel'
  条件: (c : 自然数) (h : c + a ≡ c + b [MOD n])
  结论: a ≡ b [MOD n]
  证明: ModEq.rfl.add_left_cancel h

@[simp]
-/
protected theorem add_left_cancel' (c : Nat) (h : c + a ≡ c + b [MOD n]) : a ≡ b [MOD n] :=
  ModEq.rfl.add_left_cancel h

@[simp]
/--
theorem `add_iff_left` / 定理 `add_iff_left`

English:
theorem add_iff_left
  given: (h : a ≡ b [MOD n])
  statement: a + c ≡ b + d [MOD n] ↔ c ≡ d [MOD n]
  proof: ⟨h.add_left_cancel, h.add⟩

中文:
定理 add_iff_left
  条件: (h : a ≡ b [MOD n])
  结论: a + c ≡ b + d [MOD n] ↔ c ≡ d [MOD n]
  证明: ⟨h.add_left_cancel, h.add⟩
-/
protected theorem add_iff_left (h : a ≡ b [MOD n]) : a + c ≡ b + d [MOD n] ↔ c ≡ d [MOD n] :=
  ⟨h.add_left_cancel, h.add⟩

/--
theorem `add_right_cancel` / 定理 `add_right_cancel`

English:
theorem add_right_cancel
  given: (h₁ : c ≡ d [MOD n]) (h₂ : a + c ≡ b + d [MOD n])
  proof: by
  rw [add_comm a]; rw [add_comm b] at h₂
  exact h₁.add_left_cancel h₂

中文:
定理 add_right_cancel
  条件: (h₁ : c ≡ d [MOD n]) (h₂ : a + c ≡ b + d [MOD n])
  证明: by
  rw [add_comm a]; rw [add_comm b] at h₂
  exact h₁.add_left_cancel h₂
-/
protected theorem add_right_cancel (h₁ : c ≡ d [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
    a ≡ b [MOD n] := by
  rw [add_comm a]; rw [add_comm b] at h₂
  exact h₁.add_left_cancel h₂

/--
theorem `add_right_cancel'` / 定理 `add_right_cancel'`

English:
theorem add_right_cancel'
  given: (c : Nat) (h : a + c ≡ b + c [MOD n])
  statement: a ≡ b [MOD n]
  proof: ModEq.rfl.add_right_cancel h

@[simp]

中文:
定理 add_right_cancel'
  条件: (c : 自然数) (h : a + c ≡ b + c [MOD n])
  结论: a ≡ b [MOD n]
  证明: ModEq.rfl.add_right_cancel h

@[simp]
-/
protected theorem add_right_cancel' (c : Nat) (h : a + c ≡ b + c [MOD n]) : a ≡ b [MOD n] :=
  ModEq.rfl.add_right_cancel h

@[simp]
/--
theorem `add_iff_right` / 定理 `add_iff_right`

English:
theorem add_iff_right
  given: (h : c ≡ d [MOD n])
  statement: a + c ≡ b + d [MOD n] ↔ a ≡ b [MOD n]
  proof: ⟨h.add_right_cancel, (.add · h)⟩

中文:
定理 add_iff_right
  条件: (h : c ≡ d [MOD n])
  结论: a + c ≡ b + d [MOD n] ↔ a ≡ b [MOD n]
  证明: ⟨h.add_right_cancel, (.add · h)⟩
-/
protected theorem add_iff_right (h : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] ↔ a ≡ b [MOD n] :=
  ⟨h.add_right_cancel, (.add · h)⟩

/--
lemma `sub'` / 引理 `sub'`

English:
lemma sub'
  given: (h : c <= a ↔ d <= b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n])
  proof: by
  obtain hac | hca := lt_or_ge a c
  · rw [Nat.sub_eq_zero_of_le hac.le, Nat.sub_eq_zero_of_le ((lt_iff_lt_of_le_iff_le h).1 hac).le]
  rw [modEq_iff_dvd]; rw [Int.natCast_sub hca]; rw [Int.natCast_sub <| h.1 hca]; rw [sub_sub_sub_comm]
  exact Int.dvd_sub hab.dvd hcd.dvd

中文:
引理 sub'
  条件: (h : c <= a ↔ d <= b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n])
  证明: by
  obtain hac | hca := lt_or_ge a c
  · rw [Nat.sub_eq_zero_of_le hac.le, Nat.sub_eq_zero_of_le ((lt_iff_lt_of_le_iff_le h).1 hac).le]
  rw [modEq_iff_dvd]; rw [Int.natCast_sub hca]; rw [Int.natCast_sub <| h.1 hca]; rw [sub_sub_sub_comm]
  exact Int.dvd_sub hab.dvd hcd.dvd
-/
protected lemma sub' (h : c <= a ↔ d <= b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n]) :
    a - c ≡ b - d [MOD n] := by
  obtain hac | hca := lt_or_ge a c
  · rw [Nat.sub_eq_zero_of_le hac.le, Nat.sub_eq_zero_of_le ((lt_iff_lt_of_le_iff_le h).1 hac).le]
  rw [modEq_iff_dvd]; rw [Int.natCast_sub hca]; rw [Int.natCast_sub <| h.1 hca]; rw [sub_sub_sub_comm]
  exact Int.dvd_sub hab.dvd hcd.dvd

/--
lemma `sub_left'` / 引理 `sub_left'`

English:
lemma sub_left'
  given: (h : b <= a ↔ c <= a) (hbc : b ≡ c [MOD n])
  statement: a - b ≡ a - c [MOD n]
  proof: .sub' h .rfl hbc

中文:
引理 sub_left'
  条件: (h : b <= a ↔ c <= a) (hbc : b ≡ c [MOD n])
  结论: a - b ≡ a - c [MOD n]
  证明: .sub' h .rfl hbc
-/
protected lemma sub_left' (h : b <= a ↔ c <= a) (hbc : b ≡ c [MOD n]) : a - b ≡ a - c [MOD n] :=
  .sub' h .rfl hbc

/--
lemma `sub_right'` / 引理 `sub_right'`

English:
lemma sub_right'
  given: (h : a <= b ↔ a <= c) (hbc : b ≡ c [MOD n])
  statement: b - a ≡ c - a [MOD n]
  proof: .sub' h hbc .rfl

@[gcongr]

中文:
引理 sub_right'
  条件: (h : a <= b ↔ a <= c) (hbc : b ≡ c [MOD n])
  结论: b - a ≡ c - a [MOD n]
  证明: .sub' h hbc .rfl

@[gcongr]
-/
protected lemma sub_right' (h : a <= b ↔ a <= c) (hbc : b ≡ c [MOD n]) : b - a ≡ c - a [MOD n] :=
  .sub' h hbc .rfl

@[gcongr]
/--
lemma `sub` / 引理 `sub`

English:
lemma sub
  given: (hca : c <= a) (hdb : d <= b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n])
  proof: .sub' (iff_of_true hca hdb) hab hcd

@[gcongr]

中文:
引理 sub
  条件: (hca : c <= a) (hdb : d <= b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n])
  证明: .sub' (iff_of_true hca hdb) hab hcd

@[gcongr]
-/
protected lemma sub (hca : c <= a) (hdb : d <= b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n]) :
    a - c ≡ b - d [MOD n] := .sub' (iff_of_true hca hdb) hab hcd

@[gcongr]
/--
lemma `sub_left` / 引理 `sub_left`

English:
lemma sub_left
  given: (hba : b <= a) (hca : c <= a) (hbc : b ≡ c [MOD n])
  proof: .sub hba hca .rfl hbc

@[gcongr]

中文:
引理 sub_left
  条件: (hba : b <= a) (hca : c <= a) (hbc : b ≡ c [MOD n])
  证明: .sub hba hca .rfl hbc

@[gcongr]
-/
protected lemma sub_left (hba : b <= a) (hca : c <= a) (hbc : b ≡ c [MOD n]) :
    a - b ≡ a - c [MOD n] := .sub hba hca .rfl hbc

@[gcongr]
/--
lemma `sub_right` / 引理 `sub_right`

English:
lemma sub_right
  given: (hab : a <= b) (hac : a <= c) (hbc : b ≡ c [MOD n])
  proof: .sub hab hac hbc .rfl

中文:
引理 sub_right
  条件: (hab : a <= b) (hac : a <= c) (hbc : b ≡ c [MOD n])
  证明: .sub hab hac hbc .rfl
-/
protected lemma sub_right (hab : a <= b) (hac : a <= c) (hbc : b ≡ c [MOD n]) :
    b - a ≡ c - a [MOD n] := .sub hab hac hbc .rfl

/--
theorem `mul_left_cancel'` / 定理 `mul_left_cancel'`

English:
theorem mul_left_cancel'
  given: {a b c m : Nat} (hc : c != 0)
  proof: by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.mul_sub]
  exact fun h => (Int.dvd_of_mul_dvd_mul_left (Int.ofNat_ne_zero.mpr hc) h)

中文:
定理 mul_left_cancel'
  条件: {a b c m : 自然数} (hc : c != 0)
  证明: by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.mul_sub]
  exact fun h => (Int.dvd_of_mul_dvd_mul_left (Int.ofNat_ne_zero.mpr hc) h)
-/
protected theorem mul_left_cancel' {a b c m : Nat} (hc : c != 0) :
    c * a ≡ c * b [MOD c * m] -> a ≡ b [MOD m] := by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.mul_sub]
  exact fun h => (Int.dvd_of_mul_dvd_mul_left (Int.ofNat_ne_zero.mpr hc) h)

/--
theorem `mul_left_cancel_iff'` / 定理 `mul_left_cancel_iff'`

English:
theorem mul_left_cancel_iff'
  given: {a b c m : Nat} (hc : c != 0)
  proof: ⟨ModEq.mul_left_cancel' hc, ModEq.mul_left' _⟩

中文:
定理 mul_left_cancel_iff'
  条件: {a b c m : 自然数} (hc : c != 0)
  证明: ⟨ModEq.mul_left_cancel' hc, ModEq.mul_left' _⟩
-/
protected theorem mul_left_cancel_iff' {a b c m : Nat} (hc : c != 0) :
    c * a ≡ c * b [MOD c * m] ↔ a ≡ b [MOD m] :=
  ⟨ModEq.mul_left_cancel' hc, ModEq.mul_left' _⟩

/--
theorem `mul_right_cancel'` / 定理 `mul_right_cancel'`

English:
theorem mul_right_cancel'
  given: {a b c m : Nat} (hc : c != 0)
  proof: by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.sub_mul]
  exact fun h => (Int.dvd_of_mul_dvd_mul_right (Int.ofNat_ne_zero.mpr hc) h)

中文:
定理 mul_right_cancel'
  条件: {a b c m : 自然数} (hc : c != 0)
  证明: by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.sub_mul]
  exact fun h => (Int.dvd_of_mul_dvd_mul_right (Int.ofNat_ne_zero.mpr hc) h)
-/
protected theorem mul_right_cancel' {a b c m : Nat} (hc : c != 0) :
    a * c ≡ b * c [MOD m * c] -> a ≡ b [MOD m] := by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.sub_mul]
  exact fun h => (Int.dvd_of_mul_dvd_mul_right (Int.ofNat_ne_zero.mpr hc) h)

/--
theorem `mul_right_cancel_iff'` / 定理 `mul_right_cancel_iff'`

English:
theorem mul_right_cancel_iff'
  given: {a b c m : Nat} (hc : c != 0)
  proof: ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right' _⟩

中文:
定理 mul_right_cancel_iff'
  条件: {a b c m : 自然数} (hc : c != 0)
  证明: ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right' _⟩
-/
protected theorem mul_right_cancel_iff' {a b c m : Nat} (hc : c != 0) :
    a * c ≡ b * c [MOD m * c] ↔ a ≡ b [MOD m] :=
  ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right' _⟩

/--
lemma `of_mul_left` / 引理 `of_mul_left`

English:
lemma of_mul_left
  given: (m : Nat) (h : a ≡ b [MOD m * n])
  statement: a ≡ b [MOD n]
  proof: by
  rw [modEq_iff_dvd] at *
  exact (dvd_mul_left (n : Int) (m : Int)).trans h

中文:
引理 of_mul_left
  条件: (m : 自然数) (h : a ≡ b [MOD m * n])
  结论: a ≡ b [MOD n]
  证明: by
  rw [modEq_iff_dvd] at *
  exact (dvd_mul_left (n : Int) (m : Int)).trans h

Depends on / 依赖: dvd_mul_left, modEq_iff_dvd
-/
lemma of_mul_left (m : Nat) (h : a ≡ b [MOD m * n]) : a ≡ b [MOD n] := by
  rw [modEq_iff_dvd] at *
  exact (dvd_mul_left (n : Int) (m : Int)).trans h

/--
lemma `of_mul_right` / 引理 `of_mul_right`

English:
lemma of_mul_right
  given: (m : Nat)
  statement: a ≡ b [MOD n * m] -> a ≡ b [MOD n]
  proof: mul_comm m n ▸ of_mul_left _

中文:
引理 of_mul_right
  条件: (m : 自然数)
  结论: a ≡ b [MOD n * m] -> a ≡ b [MOD n]
  证明: mul_comm m n ▸ of_mul_left _

Depends on / 依赖: mul_comm, of_mul_left
-/
lemma of_mul_right (m : Nat) : a ≡ b [MOD n * m] -> a ≡ b [MOD n] := mul_comm m n ▸ of_mul_left _

/--
theorem `of_div` / 定理 `of_div`

English:
theorem of_div
  given: (h : a / c ≡ b / c [MOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m)
  proof: by convert! h.mul_left' c <;> rwa [Nat.mul_div_cancel']

中文:
定理 of_div
  条件: (h : a / c ≡ b / c [MOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m)
  证明: by convert! h.mul_left' c <;> rwa [Nat.mul_div_cancel']

Depends on / 依赖: Nat.mul_div_cancel, convert, h.mul_left, mul_div_cancel, mul_left
-/
theorem of_div (h : a / c ≡ b / c [MOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
    a ≡ b [MOD m] := by convert! h.mul_left' c <;> rwa [Nat.mul_div_cancel']

end ModEq

@[simp]
/--
theorem `modulus_modEq_zero` / 定理 `modulus_modEq_zero`

English:
theorem modulus_modEq_zero
  statement: n ≡ 0 [MOD n]
  proof: by simp [ModEq]

@[simp]

中文:
定理 modulus_modEq_zero
  结论: n ≡ 0 [MOD n]
  证明: by simp [ModEq]

@[simp]
-/
theorem modulus_modEq_zero : n ≡ 0 [MOD n] := by simp [ModEq]

@[simp]
/--
theorem `add_modEq_left_iff` / 定理 `add_modEq_left_iff`

English:
theorem add_modEq_left_iff
  statement: a + b ≡ a [MOD n] ↔ n ∣ b
  proof: by
  simp [modEq_iff_dvd, Int.natCast_dvd_natCast]

@[simp]

中文:
定理 add_modEq_left_iff
  结论: a + b ≡ a [MOD n] ↔ n ∣ b
  证明: by
  simp [modEq_iff_dvd, Int.natCast_dvd_natCast]

@[simp]

Depends on / 依赖: Int.natCast_dvd_natCast, modEq_iff_dvd, natCast_dvd_natCast
-/
theorem add_modEq_left_iff : a + b ≡ a [MOD n] ↔ n ∣ b := by
  simp [modEq_iff_dvd, Int.natCast_dvd_natCast]

@[simp]
/--
theorem `add_modEq_right_iff` / 定理 `add_modEq_right_iff`

English:
theorem add_modEq_right_iff
  statement: a + b ≡ b [MOD n] ↔ n ∣ a
  proof: by
  rw [add_comm]; rw [add_modEq_left_iff]

@[simp]

中文:
定理 add_modEq_right_iff
  结论: a + b ≡ b [MOD n] ↔ n ∣ a
  证明: by
  rw [add_comm]; rw [add_modEq_left_iff]

@[simp]

Depends on / 依赖: add_comm, add_modEq_left_iff
-/
theorem add_modEq_right_iff : a + b ≡ b [MOD n] ↔ n ∣ a := by
  rw [add_comm]; rw [add_modEq_left_iff]

@[simp]
/--
theorem `left_modEq_add_iff` / 定理 `left_modEq_add_iff`

English:
theorem left_modEq_add_iff
  statement: a ≡ a + b [MOD n] ↔ n ∣ b
  proof: by
  rw [ModEq.comm]; rw [add_modEq_left_iff]

@[simp]

中文:
定理 left_modEq_add_iff
  结论: a ≡ a + b [MOD n] ↔ n ∣ b
  证明: by
  rw [ModEq.comm]; rw [add_modEq_left_iff]

@[simp]

Depends on / 依赖: ModEq.comm, add_modEq_left_iff
-/
theorem left_modEq_add_iff : a ≡ a + b [MOD n] ↔ n ∣ b := by
  rw [ModEq.comm]; rw [add_modEq_left_iff]

@[simp]
/--
theorem `right_modEq_add_iff` / 定理 `right_modEq_add_iff`

English:
theorem right_modEq_add_iff
  statement: b ≡ a + b [MOD n] ↔ n ∣ a
  proof: by
  rw [ModEq.comm]; rw [add_modEq_right_iff]

@[simp]

中文:
定理 right_modEq_add_iff
  结论: b ≡ a + b [MOD n] ↔ n ∣ a
  证明: by
  rw [ModEq.comm]; rw [add_modEq_right_iff]

@[simp]

Depends on / 依赖: ModEq.comm, add_modEq_right_iff
-/
theorem right_modEq_add_iff : b ≡ a + b [MOD n] ↔ n ∣ a := by
  rw [ModEq.comm]; rw [add_modEq_right_iff]

@[simp]
/--
theorem `add_modulus_modEq_iff` / 定理 `add_modulus_modEq_iff`

English:
theorem add_modulus_modEq_iff
  statement: a + n ≡ b [MOD n] ↔ a ≡ b [MOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 add_modulus_modEq_iff
  结论: a + n ≡ b [MOD n] ↔ a ≡ b [MOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem add_modulus_modEq_iff : a + n ≡ b [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modulus_add_modEq_iff` / 定理 `modulus_add_modEq_iff`

English:
theorem modulus_add_modEq_iff
  statement: n + a ≡ b [MOD n] ↔ a ≡ b [MOD n]
  proof: by
  rw [add_comm]; rw [add_modulus_modEq_iff]

@[simp]

中文:
定理 modulus_add_modEq_iff
  结论: n + a ≡ b [MOD n] ↔ a ≡ b [MOD n]
  证明: by
  rw [add_comm]; rw [add_modulus_modEq_iff]

@[simp]

Depends on / 依赖: add_comm, add_modulus_modEq_iff
-/
theorem modulus_add_modEq_iff : n + a ≡ b [MOD n] ↔ a ≡ b [MOD n] := by
  rw [add_comm]; rw [add_modulus_modEq_iff]

@[simp]
/--
theorem `modEq_add_modulus_iff` / 定理 `modEq_add_modulus_iff`

English:
theorem modEq_add_modulus_iff
  statement: a ≡ b + n [MOD n] ↔ a ≡ b [MOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 modEq_add_modulus_iff
  结论: a ≡ b + n [MOD n] ↔ a ≡ b [MOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem modEq_add_modulus_iff : a ≡ b + n [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modEq_modulus_add_iff` / 定理 `modEq_modulus_add_iff`

English:
theorem modEq_modulus_add_iff
  statement: a ≡ n + b [MOD n] ↔ a ≡ b [MOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 modEq_modulus_add_iff
  结论: a ≡ n + b [MOD n] ↔ a ≡ b [MOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem modEq_modulus_add_iff : a ≡ n + b [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `add_mul_modulus_modEq_iff` / 定理 `add_mul_modulus_modEq_iff`

English:
theorem add_mul_modulus_modEq_iff
  statement: a + b * n ≡ c [MOD n] ↔ a ≡ c [MOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 add_mul_modulus_modEq_iff
  结论: a + b * n ≡ c [MOD n] ↔ a ≡ c [MOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem add_mul_modulus_modEq_iff : a + b * n ≡ c [MOD n] ↔ a ≡ c [MOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `mul_modulus_add_modEq_iff` / 定理 `mul_modulus_add_modEq_iff`

English:
theorem mul_modulus_add_modEq_iff
  statement: b * n + a ≡ c [MOD n] ↔ a ≡ c [MOD n]
  proof: by
  rw [add_comm]; rw [add_mul_modulus_modEq_iff]

@[simp]

中文:
定理 mul_modulus_add_modEq_iff
  结论: b * n + a ≡ c [MOD n] ↔ a ≡ c [MOD n]
  证明: by
  rw [add_comm]; rw [add_mul_modulus_modEq_iff]

@[simp]

Depends on / 依赖: add_comm, add_mul_modulus_modEq_iff
-/
theorem mul_modulus_add_modEq_iff : b * n + a ≡ c [MOD n] ↔ a ≡ c [MOD n] := by
  rw [add_comm]; rw [add_mul_modulus_modEq_iff]

@[simp]
/--
theorem `modEq_add_mul_modulus_iff` / 定理 `modEq_add_mul_modulus_iff`

English:
theorem modEq_add_mul_modulus_iff
  statement: a ≡ b + c * n [MOD n] ↔ a ≡ b [MOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 modEq_add_mul_modulus_iff
  结论: a ≡ b + c * n [MOD n] ↔ a ≡ b [MOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem modEq_add_mul_modulus_iff : a ≡ b + c * n [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modEq_mul_modulus_add_iff` / 定理 `modEq_mul_modulus_add_iff`

English:
theorem modEq_mul_modulus_add_iff
  statement: a ≡ b * n + c [MOD n] ↔ a ≡ c [MOD n]
  proof: by
  rw [add_comm]; rw [modEq_add_mul_modulus_iff]

@[simp]

中文:
定理 modEq_mul_modulus_add_iff
  结论: a ≡ b * n + c [MOD n] ↔ a ≡ c [MOD n]
  证明: by
  rw [add_comm]; rw [modEq_add_mul_modulus_iff]

@[simp]

Depends on / 依赖: add_comm, modEq_add_mul_modulus_iff
-/
theorem modEq_mul_modulus_add_iff : a ≡ b * n + c [MOD n] ↔ a ≡ c [MOD n] := by
  rw [add_comm]; rw [modEq_add_mul_modulus_iff]

@[simp]
/--
theorem `add_modulus_mul_modEq_iff` / 定理 `add_modulus_mul_modEq_iff`

English:
theorem add_modulus_mul_modEq_iff
  statement: a + n * b ≡ c [MOD n] ↔ a ≡ c [MOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 add_modulus_mul_modEq_iff
  结论: a + n * b ≡ c [MOD n] ↔ a ≡ c [MOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem add_modulus_mul_modEq_iff : a + n * b ≡ c [MOD n] ↔ a ≡ c [MOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modulus_mul_add_modEq_iff` / 定理 `modulus_mul_add_modEq_iff`

English:
theorem modulus_mul_add_modEq_iff
  statement: n * b + a ≡ c [MOD n] ↔ a ≡ c [MOD n]
  proof: by
  rw [add_comm]; rw [add_modulus_mul_modEq_iff]

@[simp]

中文:
定理 modulus_mul_add_modEq_iff
  结论: n * b + a ≡ c [MOD n] ↔ a ≡ c [MOD n]
  证明: by
  rw [add_comm]; rw [add_modulus_mul_modEq_iff]

@[simp]

Depends on / 依赖: add_comm, add_modulus_mul_modEq_iff
-/
theorem modulus_mul_add_modEq_iff : n * b + a ≡ c [MOD n] ↔ a ≡ c [MOD n] := by
  rw [add_comm]; rw [add_modulus_mul_modEq_iff]

@[simp]
/--
theorem `modEq_add_modulus_mul_iff` / 定理 `modEq_add_modulus_mul_iff`

English:
theorem modEq_add_modulus_mul_iff
  statement: a ≡ b + n * c [MOD n] ↔ a ≡ b [MOD n]
  proof: by
  simp [ModEq]

@[simp]

中文:
定理 modEq_add_modulus_mul_iff
  结论: a ≡ b + n * c [MOD n] ↔ a ≡ b [MOD n]
  证明: by
  simp [ModEq]

@[simp]
-/
theorem modEq_add_modulus_mul_iff : a ≡ b + n * c [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/--
theorem `modEq_modulus_mul_add_iff` / 定理 `modEq_modulus_mul_add_iff`

English:
theorem modEq_modulus_mul_add_iff
  statement: a ≡ n * b + c [MOD n] ↔ a ≡ c [MOD n]
  proof: by
  rw [add_comm]; rw [modEq_add_modulus_mul_iff]

@[simp]

中文:
定理 modEq_modulus_mul_add_iff
  结论: a ≡ n * b + c [MOD n] ↔ a ≡ c [MOD n]
  证明: by
  rw [add_comm]; rw [modEq_add_modulus_mul_iff]

@[simp]

Depends on / 依赖: add_comm, modEq_add_modulus_mul_iff
-/
theorem modEq_modulus_mul_add_iff : a ≡ n * b + c [MOD n] ↔ a ≡ c [MOD n] := by
  rw [add_comm]; rw [modEq_add_modulus_mul_iff]

@[simp]
/--
theorem `sub_modulus_modEq_iff` / 定理 `sub_modulus_modEq_iff`

English:
theorem sub_modulus_modEq_iff
  given: (h : n <= a)
  statement: a - n ≡ b [MOD n] ↔ a ≡ b [MOD n]
  proof: by
  rw [← add_modulus_modEq_iff]; rw [Nat.sub_add_cancel h]

@[simp]

中文:
定理 sub_modulus_modEq_iff
  条件: (h : n <= a)
  结论: a - n ≡ b [MOD n] ↔ a ≡ b [MOD n]
  证明: by
  rw [← add_modulus_modEq_iff]; rw [Nat.sub_add_cancel h]

@[simp]

Depends on / 依赖: Nat.sub_add_cancel, add_modulus_modEq_iff, sub_add_cancel
-/
theorem sub_modulus_modEq_iff (h : n <= a) : a - n ≡ b [MOD n] ↔ a ≡ b [MOD n] := by
  rw [← add_modulus_modEq_iff]; rw [Nat.sub_add_cancel h]

@[simp]
/--
theorem `modEq_sub_modulus_iff` / 定理 `modEq_sub_modulus_iff`

English:
theorem modEq_sub_modulus_iff
  given: (h : n <= b)
  statement: a ≡ b - n [MOD n] ↔ a ≡ b [MOD n]
  proof: by
  rw [← modEq_add_modulus_iff]; rw [Nat.sub_add_cancel h]

中文:
定理 modEq_sub_modulus_iff
  条件: (h : n <= b)
  结论: a ≡ b - n [MOD n] ↔ a ≡ b [MOD n]
  证明: by
  rw [← modEq_add_modulus_iff]; rw [Nat.sub_add_cancel h]

Depends on / 依赖: Nat.sub_add_cancel, modEq_add_modulus_iff, sub_add_cancel
-/
theorem modEq_sub_modulus_iff (h : n <= b) : a ≡ b - n [MOD n] ↔ a ≡ b [MOD n] := by
  rw [← modEq_add_modulus_iff]; rw [Nat.sub_add_cancel h]

/--
lemma `modEq_sub` / 引理 `modEq_sub`

English:
lemma modEq_sub
  given: (h : b <= a)
  statement: a ≡ b [MOD a - b]
  proof: (modEq_of_dvd <| by rw [Int.ofNat_sub h]).symm

中文:
引理 modEq_sub
  条件: (h : b <= a)
  结论: a ≡ b [MOD a - b]
  证明: (modEq_of_dvd <| by rw [Int.ofNat_sub h]).symm

Depends on / 依赖: Int.ofNat_sub, modEq_of_dvd, ofNat_sub
-/
lemma modEq_sub (h : b <= a) : a ≡ b [MOD a - b] := (modEq_of_dvd <| by rw [Int.ofNat_sub h]).symm

/--
lemma `modEq_one` / 引理 `modEq_one`

English:
lemma modEq_one
  statement: a ≡ b [MOD 1]
  proof: modEq_of_dvd one_dvd _

中文:
引理 modEq_one
  结论: a ≡ b [MOD 1]
  证明: modEq_of_dvd one_dvd _

Depends on / 依赖: modEq_of_dvd, one_dvd
-/
lemma modEq_one : a ≡ b [MOD 1] := modEq_of_dvd one_dvd _

/--
lemma `modEq_zero_iff` / 引理 `modEq_zero_iff`

English:
lemma modEq_zero_iff
  statement: a ≡ b [MOD 0] ↔ a = b
  proof: by rw [ModEq, mod_zero, mod_zero]

中文:
引理 modEq_zero_iff
  结论: a ≡ b [MOD 0] ↔ a = b
  证明: by rw [ModEq, mod_zero, mod_zero]
-/
@[simp] lemma modEq_zero_iff : a ≡ b [MOD 0] ↔ a = b := by rw [ModEq, mod_zero, mod_zero]

/--
lemma `add_modEq_left` / 引理 `add_modEq_left`

English:
lemma add_modEq_left
  statement: n + a ≡ a [MOD n]
  proof: by simp

中文:
引理 add_modEq_left
  结论: n + a ≡ a [MOD n]
  证明: by simp
-/
lemma add_modEq_left : n + a ≡ a [MOD n] := by simp

/--
lemma `add_modEq_right` / 引理 `add_modEq_right`

English:
lemma add_modEq_right
  statement: a + n ≡ a [MOD n]
  proof: by simp

中文:
引理 add_modEq_right
  结论: a + n ≡ a [MOD n]
  证明: by simp
-/
lemma add_modEq_right : a + n ≡ a [MOD n] := by simp

/--
theorem `modEq_iff_exists_eq_add` / 定理 `modEq_iff_exists_eq_add`

English:
theorem modEq_iff_exists_eq_add
  given: (h : a <= b)
  statement: a ≡ b [MOD n] ↔ exists (t : Nat), b = a + n * t
  proof: by
  rw [modEq_iff_dvd' h]; rw [dvd_def]
  exact exists_congr (fun _ => Nat.sub_eq_iff_eq_add' h)

中文:
定理 modEq_iff_存在_eq_add
  条件: (h : a <= b)
  结论: a ≡ b [MOD n] ↔ 存在 (t : 自然数), b = a + n * t
  证明: by
  rw [modEq_iff_dvd' h]; rw [dvd_def]
  exact exists_congr (fun _ => Nat.sub_eq_iff_eq_add' h)

Depends on / 依赖: Nat.sub_eq_iff_eq_add, dvd_def, exists_congr, modEq_iff_dvd, sub_eq_iff_eq_add
-/
theorem modEq_iff_exists_eq_add (h : a <= b) : a ≡ b [MOD n] ↔ exists (t : Nat), b = a + n * t := by
  rw [modEq_iff_dvd' h]; rw [dvd_def]
  exact exists_congr (fun _ => Nat.sub_eq_iff_eq_add' h)

namespace ModEq

/--
theorem `le_of_lt_add` / 定理 `le_of_lt_add`

English:
theorem le_of_lt_add
  given: (h1 : a ≡ b [MOD m]) (h2 : a < b + m)
  statement: a <= b
  proof: (le_total a b).elim id fun h3 =>
    Nat.le_of_sub_eq_zero
      (eq_zero_of_dvd_of_lt ((modEq_iff_dvd' h3).mp h1.symm) (by lia))

中文:
定理 le_of_lt_add
  条件: (h1 : a ≡ b [MOD m]) (h2 : a < b + m)
  结论: a <= b
  证明: (le_total a b).elim id fun h3 =>
    Nat.le_of_sub_eq_zero
      (eq_zero_of_dvd_of_lt ((modEq_iff_dvd' h3).mp h1.symm) (by lia))

Depends on / 依赖: Nat.le_of_sub_eq_zero, eq_zero_of_dvd_of_lt, h1.symm, le_of_sub_eq_zero, le_total, modEq_iff_dvd
-/
theorem le_of_lt_add (h1 : a ≡ b [MOD m]) (h2 : a < b + m) : a <= b :=
  (le_total a b).elim id fun h3 =>
    Nat.le_of_sub_eq_zero
      (eq_zero_of_dvd_of_lt ((modEq_iff_dvd' h3).mp h1.symm) (by lia))

/--
theorem `add_le_of_lt` / 定理 `add_le_of_lt`

English:
theorem add_le_of_lt
  given: (h1 : a ≡ b [MOD m]) (h2 : a < b)
  statement: a + m <= b
  proof: le_of_lt_add (add_modEq_right.trans h1) (by lia)

中文:
定理 add_le_of_lt
  条件: (h1 : a ≡ b [MOD m]) (h2 : a < b)
  结论: a + m <= b
  证明: le_of_lt_add (add_modEq_right.trans h1) (by lia)

Depends on / 依赖: add_modEq_right, add_modEq_right.trans, le_of_lt_add
-/
theorem add_le_of_lt (h1 : a ≡ b [MOD m]) (h2 : a < b) : a + m <= b :=
  le_of_lt_add (add_modEq_right.trans h1) (by lia)

/--
theorem `dvd_iff` / 定理 `dvd_iff`

English:
theorem dvd_iff
  given: (h : a ≡ b [MOD m]) (hdm : d ∣ m)
  statement: d ∣ a ↔ d ∣ b
  proof: by
  simp only [← modEq_zero_iff_dvd]
  replace h := h.of_dvd hdm
  exact ⟨h.symm.trans, h.trans⟩

中文:
定理 dvd_iff
  条件: (h : a ≡ b [MOD m]) (hdm : d ∣ m)
  结论: d ∣ a ↔ d ∣ b
  证明: by
  simp only [← modEq_zero_iff_dvd]
  replace h := h.of_dvd hdm
  exact ⟨h.symm.trans, h.trans⟩

Depends on / 依赖: h.of_dvd, h.symm.trans, h.trans, modEq_zero_iff_dvd, of_dvd, replace
-/
theorem dvd_iff (h : a ≡ b [MOD m]) (hdm : d ∣ m) : d ∣ a ↔ d ∣ b := by
  simp only [← modEq_zero_iff_dvd]
  replace h := h.of_dvd hdm
  exact ⟨h.symm.trans, h.trans⟩

/--
theorem `gcd_eq` / 定理 `gcd_eq`

English:
theorem gcd_eq
  given: (h : a ≡ b [MOD m])
  statement: gcd a m = gcd b m
  proof: by
  have h1 := gcd_dvd_right a m
  have h2 := gcd_dvd_right b m
  exact
    dvd_antisymm (dvd_gcd ((h.dvd_iff h1).mp (gcd_dvd_left a m)) h1)
      (dvd_gcd ((h.dvd_iff h2).mpr (gcd_dvd_left b m)) h2)

中文:
定理 gcd_eq
  条件: (h : a ≡ b [MOD m])
  结论: 最大公约数 a m = 最大公约数 b m
  证明: by
  have h1 := gcd_dvd_right a m
  have h2 := gcd_dvd_right b m
  exact
    dvd_antisymm (dvd_gcd ((h.dvd_iff h1).mp (gcd_dvd_left a m)) h1)
      (dvd_gcd ((h.dvd_iff h2).mpr (gcd_dvd_left b m)) h2)

Depends on / 依赖: dvd_antisymm, dvd_gcd, dvd_iff, gcd_dvd_left, gcd_dvd_right, h.dvd_iff
-/
theorem gcd_eq (h : a ≡ b [MOD m]) : gcd a m = gcd b m := by
  have h1 := gcd_dvd_right a m
  have h2 := gcd_dvd_right b m
  exact
    dvd_antisymm (dvd_gcd ((h.dvd_iff h1).mp (gcd_dvd_left a m)) h1)
      (dvd_gcd ((h.dvd_iff h2).mpr (gcd_dvd_left b m)) h2)

/--
lemma `eq_of_abs_lt` / 引理 `eq_of_abs_lt`

English:
lemma eq_of_abs_lt
  given: (h : a ≡ b [MOD m]) (h2 : |(b : Int) - a| < m)
  statement: a = b
  proof: by
  apply Int.ofNat.inj
  rw [eq_comm]; rw [← sub_eq_zero]
  exact Int.eq_zero_of_abs_lt_dvd h.dvd h2

中文:
引理 eq_of_abs_lt
  条件: (h : a ≡ b [MOD m]) (h2 : |(b : 整数) - a| < m)
  结论: a = b
  证明: by
  apply Int.ofNat.inj
  rw [eq_comm]; rw [← sub_eq_zero]
  exact Int.eq_zero_of_abs_lt_dvd h.dvd h2

Depends on / 依赖: Int.eq_zero_of_abs_lt_dvd, Int.ofNat.inj, eq_comm, eq_zero_of_abs_lt_dvd, h.dvd, sub_eq_zero
-/
lemma eq_of_abs_lt (h : a ≡ b [MOD m]) (h2 : |(b : Int) - a| < m) : a = b := by
  apply Int.ofNat.inj
  rw [eq_comm]; rw [← sub_eq_zero]
  exact Int.eq_zero_of_abs_lt_dvd h.dvd h2

/--
lemma `eq_of_lt_of_lt` / 引理 `eq_of_lt_of_lt`

English:
lemma eq_of_lt_of_lt
  given: (h : a ≡ b [MOD m]) (ha : a < m) (hb : b < m)
  statement: a = b
  proof: h.eq_of_abs_lt Int.abs_sub_lt_of_lt_lt ha hb

中文:
引理 eq_of_lt_of_lt
  条件: (h : a ≡ b [MOD m]) (ha : a < m) (hb : b < m)
  结论: a = b
  证明: h.eq_of_abs_lt Int.abs_sub_lt_of_lt_lt ha hb

Depends on / 依赖: Int.abs_sub_lt_of_lt_lt, abs_sub_lt_of_lt_lt, eq_of_abs_lt, h.eq_of_abs_lt
-/
lemma eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m) (hb : b < m) : a = b :=
h.eq_of_abs_lt Int.abs_sub_lt_of_lt_lt ha hb

/--
lemma `cancel_left_div_gcd` / 引理 `cancel_left_div_gcd`

English:
lemma cancel_left_div_gcd
  given: (hm : 0 < m) (h : c * a ≡ c * b [MOD m])
  statement: a ≡ b [MOD m / gcd m c]
  proof: by
  let d := gcd m c
  have hmd := gcd_dvd_left m c
  have hcd := gcd_dvd_right m c
  rw [modEq_iff_dvd]
  refine @Int.dvd_of_dvd_mul_right_of_gcd_one (m / d) (c / d) (b - a) ?_ ?_
  · show (m / d : Int) ∣ c / d * (b - a)
    rw [mul_comm]; rw [← Int.mul_ediv_assoc (b - a) (Int.natCast_dvd_natCast.

中文:
引理 cancel_left_div_gcd
  条件: (hm : 0 < m) (h : c * a ≡ c * b [MOD m])
  结论: a ≡ b [MOD m / 最大公约数 m c]
  证明: by
  let d := gcd m c
  have hmd := gcd_dvd_left m c
  have hcd := gcd_dvd_right m c
  rw [modEq_iff_dvd]
  refine @Int.dvd_of_dvd_mul_right_of_gcd_one (m / d) (c / d) (b - a) ?_ ?_
  · show (m / d : Int) ∣ c / d * (b - a)
    rw [mul_comm]; rw [← Int.mul_ediv_assoc (b - a) (Int.natCast_dvd_natCast.

Depends on / 依赖: Int.dvd_of_dvd_mul_right_of_gcd_one, Int.ediv_dvd_ediv, Int.gcd, Int.gcd_natCast_natCast, Int.mul_ediv_assoc, Int.mul_sub, Int.natCast_div, Int.natCast_dvd_natCast.mpr, dvd_of_dvd_mul_right_of_gcd_one, ediv_dvd_ediv, gcd_dvd_left, gcd_dvd_right, gcd_natCast_natCast, modEq_iff_dvd, modEq_iff_dvd.mp, mul_comm, mul_ediv_assoc, mul_sub, natCast_div, natCast_dvd_natCast
-/
lemma cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m / gcd m c] := by
  let d := gcd m c
  have hmd := gcd_dvd_left m c
  have hcd := gcd_dvd_right m c
  rw [modEq_iff_dvd]
  refine @Int.dvd_of_dvd_mul_right_of_gcd_one (m / d) (c / d) (b - a) ?_ ?_
  · show (m / d : Int) ∣ c / d * (b - a)
    rw [mul_comm]; rw [← Int.mul_ediv_assoc (b - a) (Int.natCast_dvd_natCast.mpr hcd)]; rw [mul_comm]
    apply Int.ediv_dvd_ediv (Int.natCast_dvd_natCast.mpr hmd)
    rw [Int.mul_sub]
    exact modEq_iff_dvd.mp h
  · show Int.gcd (m / d) (c / d) = 1
    simp only [d, ← Int.natCast_div, Int.gcd_natCast_natCast (m / d) (c / d),
      gcd_div hmd hcd, Nat.div_self (gcd_pos_of_pos_left c hm)]

/--
lemma `cancel_right_div_gcd` / 引理 `cancel_right_div_gcd`

English:
lemma cancel_right_div_gcd
  given: (hm : 0 < m) (h : a * c ≡ b * c [MOD m])
  statement: a ≡ b [MOD m / gcd m c]
  proof: by
  apply cancel_left_div_gcd hm
  simpa [mul_comm] using h

中文:
引理 cancel_right_div_gcd
  条件: (hm : 0 < m) (h : a * c ≡ b * c [MOD m])
  结论: a ≡ b [MOD m / 最大公约数 m c]
  证明: by
  apply cancel_left_div_gcd hm
  simpa [mul_comm] using h

Depends on / 依赖: cancel_left_div_gcd, mul_comm
-/
lemma cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m / gcd m c] := by
  apply cancel_left_div_gcd hm
  simpa [mul_comm] using h

/--
lemma `cancel_left_div_gcd'` / 引理 `cancel_left_div_gcd'`

English:
lemma cancel_left_div_gcd'
  given: (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : c * a ≡ d * b [MOD m])
  proof: (h.trans <| hcd.symm.mul_right b).cancel_left_div_gcd hm

中文:
引理 cancel_left_div_gcd'
  条件: (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : c * a ≡ d * b [MOD m])
  证明: (h.trans <| hcd.symm.mul_right b).cancel_left_div_gcd hm

Depends on / 依赖: cancel_left_div_gcd, h.trans, hcd.symm.mul_right, mul_right
-/
lemma cancel_left_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : c * a ≡ d * b [MOD m]) :
    a ≡ b [MOD m / gcd m c] :=
  (h.trans <| hcd.symm.mul_right b).cancel_left_div_gcd hm

/--
lemma `cancel_right_div_gcd'` / 引理 `cancel_right_div_gcd'`

English:
lemma cancel_right_div_gcd'
  given: (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : a * c ≡ b * d [MOD m])
  proof: (h.trans <| hcd.symm.mul_left b).cancel_right_div_gcd hm

中文:
引理 cancel_right_div_gcd'
  条件: (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : a * c ≡ b * d [MOD m])
  证明: (h.trans <| hcd.symm.mul_left b).cancel_right_div_gcd hm

Depends on / 依赖: cancel_right_div_gcd, h.trans, hcd.symm.mul_left, mul_left
-/
lemma cancel_right_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : a * c ≡ b * d [MOD m]) :
    a ≡ b [MOD m / gcd m c] :=
  (h.trans <| hcd.symm.mul_left b).cancel_right_div_gcd hm

/--
lemma `cancel_left_of_coprime` / 引理 `cancel_left_of_coprime`

English:
lemma cancel_left_of_coprime
  given: (hmc : gcd m c = 1) (h : c * a ≡ c * b [MOD m])
  statement: a ≡ b [MOD m]
  proof: by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simp only [gcd_zero_left] at hmc
    simp only [hmc, one_mul, modEq_zero_iff] at h
    subst h
    rfl
  simpa [hmc] using h.cancel_left_div_gcd hm

中文:
引理 cancel_left_of_coprime
  条件: (hmc : 最大公约数 m c = 1) (h : c * a ≡ c * b [MOD m])
  结论: a ≡ b [MOD m]
  证明: by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simp only [gcd_zero_left] at hmc
    simp only [hmc, one_mul, modEq_zero_iff] at h
    subst h
    rfl
  simpa [hmc] using h.cancel_left_div_gcd hm

Depends on / 依赖: cancel_left_div_gcd, eq_zero_or_pos, gcd_zero_left, h.cancel_left_div_gcd, m.eq_zero_or_pos, modEq_zero_iff, one_mul
-/
lemma cancel_left_of_coprime (hmc : gcd m c = 1) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m] := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simp only [gcd_zero_left] at hmc
    simp only [hmc, one_mul, modEq_zero_iff] at h
    subst h
    rfl
  simpa [hmc] using h.cancel_left_div_gcd hm

/--
lemma `cancel_right_of_coprime` / 引理 `cancel_right_of_coprime`

English:
lemma cancel_right_of_coprime
  given: (hmc : gcd m c = 1) (h : a * c ≡ b * c [MOD m])
  statement: a ≡ b [MOD m]
  proof: cancel_left_of_coprime hmc by simpa [mul_comm] using h

中文:
引理 cancel_right_of_coprime
  条件: (hmc : 最大公约数 m c = 1) (h : a * c ≡ b * c [MOD m])
  结论: a ≡ b [MOD m]
  证明: cancel_left_of_coprime hmc by simpa [mul_comm] using h

Depends on / 依赖: cancel_left_of_coprime, mul_comm
-/
lemma cancel_right_of_coprime (hmc : gcd m c = 1) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m] :=
cancel_left_of_coprime hmc by simpa [mul_comm] using h

end ModEq

/--
Definition of `chineseRemainder'` / `chineseRemainder'` 的定义

English:
definition chineseRemainder'
  signature: (h : a ≡ b [MOD gcd n m])
  body: if hn : n = 0 then ⟨a, by
    rw [hn]; rw [gcd_zero_left] at h; constructor
    · rfl
    · exact h⟩
  else
    if hm : m = 0 then ⟨b, by
      rw [hm]; rw [gcd_zero_right] at h; constructor
      · exact h.symm
      · rfl⟩
    else
      ⟨let (c, d) := xgcd n m; Int.toNat ((n * c * b + m * d * a) 

中文:
定义 chineseRemainder'
  签名: (h : a ≡ b [MOD 最大公约数 n m])
  定义体: if hn : n = 0 then ⟨a, by
    rw [hn]; rw [gcd_zero_left] at h; constructor
    · rfl
    · exact h⟩
  else
    if hm : m = 0 then ⟨b, by
      rw [hm]; rw [gcd_zero_right] at h; constructor
      · exact h.symm
      · rfl⟩
    else
      ⟨let (c, d) := xgcd n m; Int.toNat ((n * c * b + m * d * a) 

Depends on / 依赖: Int.emod_nonneg, Int.natCast_ne_zero, Int.toNat, Int.toNat_of_nonneg, Nat.gcd_eq_zero, emod_nonneg, gcd_eq_zero, gcd_zero_left, gcd_zero_right, h.symm, hnonzero, lcm_ne_zero, modEq_iff_dvd, natCast_ne_zero, toNat_of_nonneg, xgcd_val
-/
def chineseRemainder' (h : a ≡ b [MOD gcd n m]) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  if hn : n = 0 then ⟨a, by
    rw [hn]; rw [gcd_zero_left] at h; constructor
    · rfl
    · exact h⟩
  else
    if hm : m = 0 then ⟨b, by
      rw [hm]; rw [gcd_zero_right] at h; constructor
      · exact h.symm
      · rfl⟩
    else
      ⟨let (c, d) := xgcd n m; Int.toNat ((n * c * b + m * d * a) / gcd n m % lcm n m), by
        rw [xgcd_val]
        dsimp
        rw [modEq_iff_dvd]; rw [modEq_iff_dvd]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_ne_zero.2 (lcm_ne_zero hn hm)))]
        have hnonzero : (gcd n m : Int) != 0 := by
          norm_cast
          rw [Nat.gcd_eq_zero_iff]; rw [not_and]
          exact fun _ => hm
        have hcoedvd : forall t, (gcd n m : Int) ∣ t * (b - a) := fun t => h.dvd.mul_left _
        have := gcd_eq_gcd_ab n m
        constructor <;> rw [Int.emod_def, ← sub_add] <;>
            refine Int.dvd_add ?_ (dvd_mul_of_dvd_left ?_ _) <;>
          try norm_cast
        · rw [← sub_eq_iff_eq_add'] at this
          rw [← this]; rw [Int.sub_mul]; rw [← add_sub_assoc]; rw [add_comm]; rw [add_sub_assoc]; rw [← Int.mul_sub]; rw [Int.add_ediv_of_dvd_left]; rw [Int.mul_ediv_cancel_left _ hnonzero]; rw [Int.mul_ediv_assoc _ h.dvd]; rw [← sub_sub]; rw [sub_self]; rw [zero_sub]; rw [Int.dvd_neg]; rw [mul_assoc]
          · exact dvd_mul_right _ _
          norm_cast
          exact dvd_mul_right _ _
        · exact dvd_lcm_left n m
        · rw [← sub_eq_iff_eq_add] at this
          rw [← this]; rw [Int.sub_mul]; rw [sub_add]; rw [← Int.mul_sub]; rw [Int.sub_ediv_of_dvd]; rw [Int.mul_ediv_cancel_left _ hnonzero]; rw [Int.mul_ediv_assoc _ h.dvd]; rw [← sub_add]; rw [sub_self]; rw [zero_add]; rw [mul_assoc]
          · exact dvd_mul_right _ _
          · exact hcoedvd _
        · exact dvd_lcm_right n m⟩

/--
Definition of `chineseRemainder` / `chineseRemainder` 的定义

English:
definition chineseRemainder
  signature: (co : n.Coprime m) (a b : Nat)
  body: chineseRemainder' (by convert! @modEq_one a b)

中文:
定义 chineseRemainder
  签名: (co : n.Coprime m) (a b : 自然数)
  定义体: chineseRemainder' (by convert! @modEq_one a b)

Depends on / 依赖: chineseRemainder, convert, modEq_one
-/
def chineseRemainder (co : n.Coprime m) (a b : Nat) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  chineseRemainder' (by convert! @modEq_one a b)

/--
theorem `chineseRemainder'_lt_lcm` / 定理 `chineseRemainder'_lt_lcm`

English:
theorem chineseRemainder'_lt_lcm
  given: (h : a ≡ b [MOD gcd n m]) (hn : n != 0) (hm : m != 0)
  proof: by
  dsimp only [chineseRemainder']
  rw [dif_neg hn]; rw [dif_neg hm]; rw [Subtype.coe_mk]; rw [xgcd_val]; rw [← Int.toNat_natCast (lcm n m)]
  have lcm_pos := Int.natCast_pos.mpr (Nat.pos_of_ne_zero (lcm_ne_zero hn hm))
  exact (Int.toNat_lt_toNat lcm_pos).mpr (Int.emod_lt_of_pos _ lcm_pos)

中文:
定理 chineseRemainder'_lt_lcm
  条件: (h : a ≡ b [MOD 最大公约数 n m]) (hn : n != 0) (hm : m != 0)
  证明: by
  dsimp only [chineseRemainder']
  rw [dif_neg hn]; rw [dif_neg hm]; rw [Subtype.coe_mk]; rw [xgcd_val]; rw [← Int.toNat_natCast (lcm n m)]
  have lcm_pos := Int.natCast_pos.mpr (Nat.pos_of_ne_zero (lcm_ne_zero hn hm))
  exact (Int.toNat_lt_toNat lcm_pos).mpr (Int.emod_lt_of_pos _ lcm_pos)
-/
theorem chineseRemainder'_lt_lcm (h : a ≡ b [MOD gcd n m]) (hn : n != 0) (hm : m != 0) :
    ↑(chineseRemainder' h) < lcm n m := by
  dsimp only [chineseRemainder']
  rw [dif_neg hn]; rw [dif_neg hm]; rw [Subtype.coe_mk]; rw [xgcd_val]; rw [← Int.toNat_natCast (lcm n m)]
  have lcm_pos := Int.natCast_pos.mpr (Nat.pos_of_ne_zero (lcm_ne_zero hn hm))
  exact (Int.toNat_lt_toNat lcm_pos).mpr (Int.emod_lt_of_pos _ lcm_pos)

/--
theorem `chineseRemainder_lt_mul` / 定理 `chineseRemainder_lt_mul`

English:
theorem chineseRemainder_lt_mul
  given: (co : n.Coprime m) (a b : Nat) (hn : n != 0) (hm : m != 0)
  proof: lt_of_lt_of_le (chineseRemainder'_lt_lcm _ hn hm) (le_of_eq co.lcm_eq_mul)

中文:
定理 chineseRemainder_lt_mul
  条件: (co : n.Coprime m) (a b : 自然数) (hn : n != 0) (hm : m != 0)
  证明: lt_of_lt_of_le (chineseRemainder'_lt_lcm _ hn hm) (le_of_eq co.lcm_eq_mul)

Depends on / 依赖: _lt_lcm, chineseRemainder, co.lcm_eq_mul, lcm_eq_mul, le_of_eq, lt_of_lt_of_le
-/
theorem chineseRemainder_lt_mul (co : n.Coprime m) (a b : Nat) (hn : n != 0) (hm : m != 0) :
    ↑(chineseRemainder co a b) < n * m :=
  lt_of_lt_of_le (chineseRemainder'_lt_lcm _ hn hm) (le_of_eq co.lcm_eq_mul)

/--
theorem `mod_lcm` / 定理 `mod_lcm`

English:
theorem mod_lcm
  given: (hn : a ≡ b [MOD n]) (hm : a ≡ b [MOD m])
  statement: a ≡ b [MOD lcm n m]
  proof: Nat.modEq_iff_dvd.mpr Int.coe_lcm_dvd (Nat.modEq_iff_dvd.mp hn) (Nat.modEq_iff_dvd.mp hm)

中文:
定理 mod_lcm
  条件: (hn : a ≡ b [MOD n]) (hm : a ≡ b [MOD m])
  结论: a ≡ b [MOD 最小公倍数 n m]
  证明: Nat.modEq_iff_dvd.mpr Int.coe_lcm_dvd (Nat.modEq_iff_dvd.mp hn) (Nat.modEq_iff_dvd.mp hm)

Depends on / 依赖: Int.coe_lcm_dvd, Nat.modEq_iff_dvd.mp, Nat.modEq_iff_dvd.mpr, coe_lcm_dvd, modEq_iff_dvd
-/
theorem mod_lcm (hn : a ≡ b [MOD n]) (hm : a ≡ b [MOD m]) : a ≡ b [MOD lcm n m] :=
Nat.modEq_iff_dvd.mpr Int.coe_lcm_dvd (Nat.modEq_iff_dvd.mp hn) (Nat.modEq_iff_dvd.mp hm)

/--
theorem `chineseRemainder_modEq_unique` / 定理 `chineseRemainder_modEq_unique`

English:
theorem chineseRemainder_modEq_unique
  statement: (co : n.Coprime m) {a b z}
  proof: by
  simpa [Nat.Coprime.lcm_eq_mul co] using
    mod_lcm (hzan.trans ((chineseRemainder co a b).prop.1).symm)
      (hzbm.trans ((chineseRemainder co a b).prop.2).symm)

中文:
定理 chineseRemainder_modEq_unique
  结论: (co : n.Coprime m) {a b z}
  证明: by
  simpa [Nat.Coprime.lcm_eq_mul co] using
    mod_lcm (hzan.trans ((chineseRemainder co a b).prop.1).symm)
      (hzbm.trans ((chineseRemainder co a b).prop.2).symm)

Depends on / 依赖: Coprime, Nat.Coprime.lcm_eq_mul, chineseRemainder, hzan.trans, hzbm.trans, lcm_eq_mul, mod_lcm
-/
theorem chineseRemainder_modEq_unique (co : n.Coprime m) {a b z}
    (hzan : z ≡ a [MOD n]) (hzbm : z ≡ b [MOD m]) : z ≡ chineseRemainder co a b [MOD n * m] := by
  simpa [Nat.Coprime.lcm_eq_mul co] using
    mod_lcm (hzan.trans ((chineseRemainder co a b).prop.1).symm)
      (hzbm.trans ((chineseRemainder co a b).prop.2).symm)

/--
theorem `modEq_and_modEq_iff_modEq_mul` / 定理 `modEq_and_modEq_iff_modEq_mul`

English:
theorem modEq_and_modEq_iff_modEq_mul
  given: {a b m n : Nat} (hmn : m.Coprime n)
  proof: ⟨fun h => by
    rw [Nat.modEq_iff_dvd]; rw [Nat.modEq_iff_dvd]; rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast]; rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast] at h
    rw [Nat.modEq_iff_dvd]; rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast]
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2,


中文:
定理 modEq_and_modEq_iff_modEq_mul
  条件: {a b m n : 自然数} (hmn : m.Coprime n)
  证明: ⟨fun h => by
    rw [Nat.modEq_iff_dvd]; rw [Nat.modEq_iff_dvd]; rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast]; rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast] at h
    rw [Nat.modEq_iff_dvd]; rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast]
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2,


Depends on / 依赖: Int.dvd_natAbs, Int.natCast_dvd_natCast, Nat.modEq_iff_dvd, Subfield, Subsingleton, Subsingleton.elim, Subtype, Subtype.prop, ZMod.castHom, castHom, dvd_natAbs, dvd_rfl, h.of_mul_left, h.of_mul_right, hmn.mul_dvd_of_dvd_of_dvd, modEq_iff_dvd, mul_dvd_of_dvd_of_dvd, natCast_dvd_natCast, of_mul_left, of_mul_right
-/
theorem modEq_and_modEq_iff_modEq_mul {a b m n : Nat} (hmn : m.Coprime n) :
    a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n] :=
  ⟨fun h => by
    rw [Nat.modEq_iff_dvd]; rw [Nat.modEq_iff_dvd]; rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast]; rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast] at h
    rw [Nat.modEq_iff_dvd]; rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast]
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2,
   fun h => ⟨h.of_mul_right _, h.of_mul_left _⟩⟩

/--
theorem `coprime_of_mul_modEq_one` / 定理 `coprime_of_mul_modEq_one`

English:
theorem coprime_of_mul_modEq_one
  given: (b : Nat) {a n : Nat} (h : a * b ≡ 1 [MOD n])
  statement: a.Coprime n
  proof: by
  obtain ⟨g, hh⟩ := Nat.gcd_dvd_right a n
  rw [Nat.coprime_iff_gcd_eq_one]; rw [← Nat.dvd_one]; rw [← Nat.modEq_zero_iff_dvd]
  calc
    1 ≡ a * b [MOD a.gcd n] := (hh ▸ h).symm.of_mul_right g
    _ ≡ 0 * b [MOD a.gcd n] := (Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_left _ _)).mul_right b
    _ = 

中文:
定理 coprime_of_mul_modEq_one
  条件: (b : 自然数) {a n : 自然数} (h : a * b ≡ 1 [MOD n])
  结论: a.Coprime n
  证明: by
  obtain ⟨g, hh⟩ := Nat.gcd_dvd_right a n
  rw [Nat.coprime_iff_gcd_eq_one]; rw [← Nat.dvd_one]; rw [← Nat.modEq_zero_iff_dvd]
  calc
    1 ≡ a * b [MOD a.gcd n] := (hh ▸ h).symm.of_mul_right g
    _ ≡ 0 * b [MOD a.gcd n] := (Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_left _ _)).mul_right b
    _ = 

Depends on / 依赖: Nat.coprime_iff_gcd_eq_one, Nat.dvd_one, Nat.gcd_dvd_left, Nat.gcd_dvd_right, Nat.modEq_zero_iff_dvd, Nat.modEq_zero_iff_dvd.mpr, a.gcd, coprime_iff_gcd_eq_one, dvd_one, gcd_dvd_left, gcd_dvd_right, modEq_zero_iff_dvd, mul_right, of_mul_right, symm.of_mul_right, zero_mul
-/
theorem coprime_of_mul_modEq_one (b : Nat) {a n : Nat} (h : a * b ≡ 1 [MOD n]) : a.Coprime n := by
  obtain ⟨g, hh⟩ := Nat.gcd_dvd_right a n
  rw [Nat.coprime_iff_gcd_eq_one]; rw [← Nat.dvd_one]; rw [← Nat.modEq_zero_iff_dvd]
  calc
    1 ≡ a * b [MOD a.gcd n] := (hh ▸ h).symm.of_mul_right g
    _ ≡ 0 * b [MOD a.gcd n] := (Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_left _ _)).mul_right b
    _ = 0 := by rw [zero_mul]

/--
theorem `add_mod_add_ite` / 定理 `add_mod_add_ite`

English:
theorem add_mod_add_ite
  given: (a b c : Nat)
  proof: have : (a + b) % c = (a % c + b % c) % c := ((mod_modEq _ _).add <| mod_modEq _ _).symm
  if hc0 : c = 0 then by simp [hc0, Nat.mod_zero]
  else by
    rw [this]
    split_ifs with h
    · have h2 : (a % c + b % c) / c < 2 :=
        Nat.div_lt_of_lt_mul
          (by
            rw [mul_two]
      

中文:
定理 add_mod_add_ite
  条件: (a b c : 自然数)
  证明: have : (a + b) % c = (a % c + b % c) % c := ((mod_modEq _ _).add <| mod_modEq _ _).symm
  if hc0 : c = 0 then by simp [hc0, Nat.mod_zero]
  else by
    rw [this]
    split_ifs with h
    · have h2 : (a % c + b % c) / c < 2 :=
        Nat.div_lt_of_lt_mul
          (by
            rw [mul_two]
      

Depends on / 依赖: Nat.div_lt_of_lt_mul, Nat.div_pos, Nat.mod_lt, Nat.mod_zero, Nat.pos_of_ne_zero, add_comm, add_lt_add, add_right_cancel_iff, div_lt_of_lt_mul, div_pos, mod_lt, mod_modEq, mod_zero, mul_two, pos_of_ne_zero, split_ifs
-/
theorem add_mod_add_ite (a b c : Nat) :
    ((a + b) % c + if c <= a % c + b % c then c else 0) = a % c + b % c :=
  have : (a + b) % c = (a % c + b % c) % c := ((mod_modEq _ _).add <| mod_modEq _ _).symm
  if hc0 : c = 0 then by simp [hc0, Nat.mod_zero]
  else by
    rw [this]
    split_ifs with h
    · have h2 : (a % c + b % c) / c < 2 :=
        Nat.div_lt_of_lt_mul
          (by
            rw [mul_two]
            exact
              add_lt_add (Nat.mod_lt _ (Nat.pos_of_ne_zero hc0))
                (Nat.mod_lt _ (Nat.pos_of_ne_zero hc0)))
      have h0 : 0 < (a % c + b % c) / c := Nat.div_pos h (Nat.pos_of_ne_zero hc0)
      rw [← @add_right_cancel_iff _ _ _ (c * ((a % c + b % c) / c))]; rw [add_comm _ c]; rw [add_assoc]; rw [mod_add_div]; rw [le_antisymm (le_of_lt_succ h2) h0]; rw [mul_one]; rw [add_comm]
    · rw [Nat.mod_eq_of_lt (lt_of_not_ge h), add_zero]

/--
theorem `add_mod_of_add_mod_lt` / 定理 `add_mod_of_add_mod_lt`

English:
theorem add_mod_of_add_mod_lt
  given: {a b c : Nat} (hc : a % c + b % c < c)
  proof: by rw [← add_mod_add_ite, if_neg (not_le_of_gt hc), add_zero]

中文:
定理 add_mod_of_add_mod_lt
  条件: {a b c : 自然数} (hc : a % c + b % c < c)
  证明: by rw [← add_mod_add_ite, if_neg (not_le_of_gt hc), add_zero]

Depends on / 依赖: add_mod_add_ite, add_zero, if_neg, not_le_of_gt
-/
theorem add_mod_of_add_mod_lt {a b c : Nat} (hc : a % c + b % c < c) :
    (a + b) % c = a % c + b % c := by rw [← add_mod_add_ite, if_neg (not_le_of_gt hc), add_zero]

/--
theorem `add_mod_add_of_le_add_mod` / 定理 `add_mod_add_of_le_add_mod`

English:
theorem add_mod_add_of_le_add_mod
  given: {a b c : Nat} (hc : c <= a % c + b % c)
  proof: by rw [← add_mod_add_ite, if_pos hc]

中文:
定理 add_mod_add_of_le_add_mod
  条件: {a b c : 自然数} (hc : c <= a % c + b % c)
  证明: by rw [← add_mod_add_ite, if_pos hc]

Depends on / 依赖: add_mod_add_ite, if_pos
-/
theorem add_mod_add_of_le_add_mod {a b c : Nat} (hc : c <= a % c + b % c) :
    (a + b) % c + c = a % c + b % c := by rw [← add_mod_add_ite, if_pos hc]

/--
theorem `add_div_eq_of_add_mod_lt` / 定理 `add_div_eq_of_add_mod_lt`

English:
theorem add_div_eq_of_add_mod_lt
  given: {a b c : Nat} (hc : a % c + b % c < c)
  proof: if hc0 : c = 0 then by simp [hc0]
  else by rw [Nat.add_div (Nat.pos_of_ne_zero hc0), if_neg (not_le_of_gt hc), add_zero]

中文:
定理 add_div_eq_of_add_mod_lt
  条件: {a b c : 自然数} (hc : a % c + b % c < c)
  证明: if hc0 : c = 0 then by simp [hc0]
  else by rw [Nat.add_div (Nat.pos_of_ne_zero hc0), if_neg (not_le_of_gt hc), add_zero]

Depends on / 依赖: Nat.add_div, Nat.pos_of_ne_zero, add_div, add_zero, if_neg, not_le_of_gt, pos_of_ne_zero
-/
theorem add_div_eq_of_add_mod_lt {a b c : Nat} (hc : a % c + b % c < c) :
    (a + b) / c = a / c + b / c :=
  if hc0 : c = 0 then by simp [hc0]
  else by rw [Nat.add_div (Nat.pos_of_ne_zero hc0), if_neg (not_le_of_gt hc), add_zero]

/--
theorem `add_div_of_dvd_right` / 定理 `add_div_of_dvd_right`

English:
theorem add_div_of_dvd_right
  given: {a b c : Nat} (hca : c ∣ a)
  statement: (a + b) / c = a / c + b / c
  proof: if h : c = 0 then by simp [h]
  else
    add_div_eq_of_add_mod_lt
      (by
        rw [Nat.mod_eq_zero_of_dvd hca]; rw [zero_add]
        exact Nat.mod_lt _ (zero_lt_of_ne_zero h))

中文:
定理 add_div_of_dvd_right
  条件: {a b c : 自然数} (hca : c ∣ a)
  结论: (a + b) / c = a / c + b / c
  证明: if h : c = 0 then by simp [h]
  else
    add_div_eq_of_add_mod_lt
      (by
        rw [Nat.mod_eq_zero_of_dvd hca]; rw [zero_add]
        exact Nat.mod_lt _ (zero_lt_of_ne_zero h))
-/
protected theorem add_div_of_dvd_right {a b c : Nat} (hca : c ∣ a) : (a + b) / c = a / c + b / c :=
  if h : c = 0 then by simp [h]
  else
    add_div_eq_of_add_mod_lt
      (by
        rw [Nat.mod_eq_zero_of_dvd hca]; rw [zero_add]
        exact Nat.mod_lt _ (zero_lt_of_ne_zero h))

/--
theorem `add_div_of_dvd_left` / 定理 `add_div_of_dvd_left`

English:
theorem add_div_of_dvd_left
  given: {a b c : Nat} (hca : c ∣ b)
  statement: (a + b) / c = a / c + b / c
  proof: by
  rwa [add_comm, Nat.add_div_of_dvd_right, add_comm]

中文:
定理 add_div_of_dvd_left
  条件: {a b c : 自然数} (hca : c ∣ b)
  结论: (a + b) / c = a / c + b / c
  证明: by
  rwa [add_comm, Nat.add_div_of_dvd_right, add_comm]
-/
protected theorem add_div_of_dvd_left {a b c : Nat} (hca : c ∣ b) : (a + b) / c = a / c + b / c := by
  rwa [add_comm, Nat.add_div_of_dvd_right, add_comm]

/--
theorem `add_div_eq_of_le_mod_add_mod` / 定理 `add_div_eq_of_le_mod_add_mod`

English:
theorem add_div_eq_of_le_mod_add_mod
  given: {a b c : Nat} (hc : c <= a % c + b % c) (hc0 : 0 < c)
  proof: by rw [Nat.add_div hc0, if_pos hc]

@[deprecated Nat.div_add_div_le_add_div (since := "2026-08-05")]

中文:
定理 add_div_eq_of_le_mod_add_mod
  条件: {a b c : 自然数} (hc : c <= a % c + b % c) (hc0 : 0 < c)
  证明: by rw [Nat.add_div hc0, if_pos hc]

@[deprecated Nat.div_add_div_le_add_div (since := "2026-08-05")]

Depends on / 依赖: Nat.add_div, add_div, if_pos
-/
theorem add_div_eq_of_le_mod_add_mod {a b c : Nat} (hc : c <= a % c + b % c) (hc0 : 0 < c) :
    (a + b) / c = a / c + b / c + 1 := by rw [Nat.add_div hc0, if_pos hc]

@[deprecated Nat.div_add_div_le_add_div (since := "2026-08-05")]
/--
theorem `add_div_le_add_div` / 定理 `add_div_le_add_div`

English:
theorem add_div_le_add_div
  given: (a b c : Nat)
  statement: a / c + b / c <= (a + b) / c
  proof: Nat.div_add_div_le_add_div

中文:
定理 add_div_le_add_div
  条件: (a b c : 自然数)
  结论: a / c + b / c <= (a + b) / c
  证明: Nat.div_add_div_le_add_div

Depends on / 依赖: Nat.div_add_div_le_add_div, div_add_div_le_add_div
-/
theorem add_div_le_add_div (a b c : Nat) : a / c + b / c <= (a + b) / c :=
  Nat.div_add_div_le_add_div

/--
theorem `add_div_le_div_add_div_add_one` / 定理 `add_div_le_div_add_div_add_one`

English:
theorem add_div_le_div_add_div_add_one
  given: (a b c : Nat)
  statement: (a + b) / c <= a / c + b / c + 1
  proof: by
  by_cases h : c = 0
  · simp [h]
  · rw [Nat.add_div (Nat.pos_of_ne_zero h), Nat.add_le_add_iff_left]
    split <;> decide

中文:
定理 add_div_le_div_add_div_add_one
  条件: (a b c : 自然数)
  结论: (a + b) / c <= a / c + b / c + 1
  证明: by
  by_cases h : c = 0
  · simp [h]
  · rw [Nat.add_div (Nat.pos_of_ne_zero h), Nat.add_le_add_iff_left]
    split <;> decide

Depends on / 依赖: Nat.add_div, Nat.add_le_add_iff_left, Nat.pos_of_ne_zero, add_div, add_le_add_iff_left, pos_of_ne_zero
-/
theorem add_div_le_div_add_div_add_one (a b c : Nat) : (a + b) / c <= a / c + b / c + 1 := by
  by_cases h : c = 0
  · simp [h]
  · rw [Nat.add_div (Nat.pos_of_ne_zero h), Nat.add_le_add_iff_left]
    split <;> decide

/--
theorem `le_mod_add_mod_of_dvd_add_of_not_dvd` / 定理 `le_mod_add_mod_of_dvd_add_of_not_dvd`

English:
theorem le_mod_add_mod_of_dvd_add_of_not_dvd
  given: {a b c : Nat} (h : c ∣ a + b) (ha : ¬c ∣ a)
  proof: by_contradiction fun hc => by
    have : (a + b) % c = a % c + b % c := add_mod_of_add_mod_lt (lt_of_not_ge hc)
    simp_all [dvd_iff_mod_eq_zero]

中文:
定理 le_mod_add_mod_of_dvd_add_of_not_dvd
  条件: {a b c : 自然数} (h : c ∣ a + b) (ha : ¬c ∣ a)
  证明: by_contradiction fun hc => by
    have : (a + b) % c = a % c + b % c := add_mod_of_add_mod_lt (lt_of_not_ge hc)
    simp_all [dvd_iff_mod_eq_zero]

Depends on / 依赖: add_mod_of_add_mod_lt, by_contradiction, dvd_iff_mod_eq_zero, lt_of_not_ge
-/
theorem le_mod_add_mod_of_dvd_add_of_not_dvd {a b c : Nat} (h : c ∣ a + b) (ha : ¬c ∣ a) :
    c <= a % c + b % c :=
  by_contradiction fun hc => by
    have : (a + b) % c = a % c + b % c := add_mod_of_add_mod_lt (lt_of_not_ge hc)
    simp_all [dvd_iff_mod_eq_zero]

/--
lemma `mod_sub_of_le` / 引理 `mod_sub_of_le`

English:
lemma mod_sub_of_le
  given: {a b n : Nat} (h : b <= a % n)
  statement: a % n - b = (a - b) % n
  proof: by
  rcases n.eq_zero_or_pos with rfl | hn; · simp only [mod_zero]
  nth_rw 2 [← div_add_mod a n]; rw [Nat.add_sub_assoc h, mul_add_mod]
  exact (mod_eq_of_lt <| (sub_le ..).trans_lt (mod_lt a hn)).symm

中文:
引理 mod_sub_of_le
  条件: {a b n : 自然数} (h : b <= a % n)
  结论: a % n - b = (a - b) % n
  证明: by
  rcases n.eq_zero_or_pos with rfl | hn; · simp only [mod_zero]
  nth_rw 2 [← div_add_mod a n]; rw [Nat.add_sub_assoc h, mul_add_mod]
  exact (mod_eq_of_lt <| (sub_le ..).trans_lt (mod_lt a hn)).symm

Depends on / 依赖: Nat.add_sub_assoc, add_sub_assoc, div_add_mod, eq_zero_or_pos, mod_eq_of_lt, mod_lt, mod_zero, mul_add_mod, n.eq_zero_or_pos, nth_rw, sub_le, trans_lt
-/
lemma mod_sub_of_le {a b n : Nat} (h : b <= a % n) : a % n - b = (a - b) % n := by
  rcases n.eq_zero_or_pos with rfl | hn; · simp only [mod_zero]
  nth_rw 2 [← div_add_mod a n]; rw [Nat.add_sub_assoc h, mul_add_mod]
  exact (mod_eq_of_lt <| (sub_le ..).trans_lt (mod_lt a hn)).symm

/--
theorem `odd_mul_odd` / 定理 `odd_mul_odd`

English:
theorem odd_mul_odd
  given: {n m : Nat}
  statement: n % 2 = 1 -> m % 2 = 1 -> n * m % 2 = 1
  proof: by
  simpa [Nat.ModEq] using @ModEq.mul 2 n 1 m 1

中文:
定理 odd_mul_odd
  条件: {n m : 自然数}
  结论: n % 2 = 1 -> m % 2 = 1 -> n * m % 2 = 1
  证明: by
  simpa [Nat.ModEq] using @ModEq.mul 2 n 1 m 1

Depends on / 依赖: ModEq.mul, Nat.ModEq
-/
theorem odd_mul_odd {n m : Nat} : n % 2 = 1 -> m % 2 = 1 -> n * m % 2 = 1 := by
  simpa [Nat.ModEq] using @ModEq.mul 2 n 1 m 1

/--
theorem `odd_mul_odd_div_two` / 定理 `odd_mul_odd_div_two`

English:
theorem odd_mul_odd_div_two
  given: {m n : Nat} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1)
  proof: have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp_all
mul_right_injective₀ two_ne_zero by
    dsimp
    rw [mul_add]; rw [two_mul_odd_div_two hm1]; rw [mul_left_comm]; rw [two_mul_odd_div_two hn1]; rw [two_mul_odd_div_two (Nat.odd_mul_odd hm1 hn1)]; rw [Nat.mul_sub]; rw [mul_one]; rw [←
      

中文:
定理 odd_mul_odd_div_two
  条件: {m n : 自然数} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1)
  证明: have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp_all
mul_right_injective₀ two_ne_zero by
    dsimp
    rw [mul_add]; rw [two_mul_odd_div_two hm1]; rw [mul_left_comm]; rw [two_mul_odd_div_two hn1]; rw [two_mul_odd_div_two (Nat.odd_mul_odd hm1 hn1)]; rw [Nat.mul_sub]; rw [mul_one]; rw [←
      

Depends on / 依赖: Nat.add_sub_assoc, Nat.le_mul_of_pos_right, Nat.mul_sub, Nat.odd_mul_odd, Nat.pos_of_ne_zero, Nat.sub_add_cancel, add_sub_assoc, le_mul_of_pos_right, mul_add, mul_left_comm, mul_one, mul_sub, odd_mul_odd, pos_of_ne_zero, sub_add_cancel, two_mul_odd_div_two, two_ne_zero
-/
theorem odd_mul_odd_div_two {m n : Nat} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) :
    m * n / 2 = m * (n / 2) + m / 2 :=
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp_all
mul_right_injective₀ two_ne_zero by
    dsimp
    rw [mul_add]; rw [two_mul_odd_div_two hm1]; rw [mul_left_comm]; rw [two_mul_odd_div_two hn1]; rw [two_mul_odd_div_two (Nat.odd_mul_odd hm1 hn1)]; rw [Nat.mul_sub]; rw [mul_one]; rw [←
      Nat.add_sub_assoc (by lia)]; rw [Nat.sub_add_cancel (Nat.le_mul_of_pos_right m hn0)]

/--
theorem `odd_of_mod_four_eq_one` / 定理 `odd_of_mod_four_eq_one`

English:
theorem odd_of_mod_four_eq_one
  given: {n : Nat}
  statement: n % 4 = 1 -> n % 2 = 1
  proof: by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 1 2

中文:
定理 odd_of_mod_four_eq_one
  条件: {n : 自然数}
  结论: n % 4 = 1 -> n % 2 = 1
  证明: by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 1 2

Depends on / 依赖: ModEq.of_mul_left, of_mul_left
-/
theorem odd_of_mod_four_eq_one {n : Nat} : n % 4 = 1 -> n % 2 = 1 := by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 1 2

/--
theorem `odd_of_mod_four_eq_three` / 定理 `odd_of_mod_four_eq_three`

English:
theorem odd_of_mod_four_eq_three
  given: {n : Nat}
  statement: n % 4 = 3 -> n % 2 = 1
  proof: by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 3 2

中文:
定理 odd_of_mod_four_eq_three
  条件: {n : 自然数}
  结论: n % 4 = 3 -> n % 2 = 1
  证明: by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 3 2

Depends on / 依赖: ModEq.of_mul_left, of_mul_left
-/
theorem odd_of_mod_four_eq_three {n : Nat} : n % 4 = 3 -> n % 2 = 1 := by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 3 2

/--
theorem `odd_mod_four_iff` / 定理 `odd_mod_four_iff`

English:
theorem odd_mod_four_iff
  given: {n : Nat}
  statement: n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3
  proof: have help : forall m : Nat, m < 4 -> m % 2 = 1 -> m = 1 ∨ m = 3 := by decide
  ⟨fun hn =>
help (n % 4) (mod_lt n (by lia)) (mod_mod_of_dvd n (by decide : 2 ∣ 4)).trans hn,
    fun h => Or.elim h odd_of_mod_four_eq_one odd_of_mod_four_eq_three⟩

中文:
定理 odd_mod_four_iff
  条件: {n : 自然数}
  结论: n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3
  证明: have help : forall m : Nat, m < 4 -> m % 2 = 1 -> m = 1 ∨ m = 3 := by decide
  ⟨fun hn =>
help (n % 4) (mod_lt n (by lia)) (mod_mod_of_dvd n (by decide : 2 ∣ 4)).trans hn,
    fun h => Or.elim h odd_of_mod_four_eq_one odd_of_mod_four_eq_three⟩

Depends on / 依赖: Or.elim, mod_lt, mod_mod_of_dvd, odd_of_mod_four_eq_one, odd_of_mod_four_eq_three
-/
theorem odd_mod_four_iff {n : Nat} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 :=
  have help : forall m : Nat, m < 4 -> m % 2 = 1 -> m = 1 ∨ m = 3 := by decide
  ⟨fun hn =>
help (n % 4) (mod_lt n (by lia)) (mod_mod_of_dvd n (by decide : 2 ∣ 4)).trans hn,
    fun h => Or.elim h odd_of_mod_four_eq_one odd_of_mod_four_eq_three⟩

/--
lemma `mod_eq_of_modEq` / 引理 `mod_eq_of_modEq`

English:
lemma mod_eq_of_modEq
  given: {a b n} (h : a ≡ b [MOD n]) (hb : b < n)
  statement: a % n = b
  proof: Eq.trans h (mod_eq_of_lt hb)

中文:
引理 mod_eq_of_modEq
  条件: {a b n} (h : a ≡ b [MOD n]) (hb : b < n)
  结论: a % n = b
  证明: Eq.trans h (mod_eq_of_lt hb)

Depends on / 依赖: Eq.trans, mod_eq_of_lt
-/
lemma mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b < n) : a % n = b :=
  Eq.trans h (mod_eq_of_lt hb)

/--
theorem `ext_div_modEq` / 定理 `ext_div_modEq`

English:
theorem ext_div_modEq
  given: {n a b : Nat} (h0 : a / n = b / n) (h1 : a ≡ b [MOD n])
  statement: a = b
  proof: ext_div_mod h0 h1

中文:
定理 ext_div_modEq
  条件: {n a b : 自然数} (h0 : a / n = b / n) (h1 : a ≡ b [MOD n])
  结论: a = b
  证明: ext_div_mod h0 h1

Depends on / 依赖: ext_div_mod
-/
theorem ext_div_modEq {n a b : Nat} (h0 : a / n = b / n) (h1 : a ≡ b [MOD n]) : a = b :=
  ext_div_mod h0 h1

/--
theorem `ext_div_modEq_iff` / 定理 `ext_div_modEq_iff`

English:
theorem ext_div_modEq_iff
  given: (n a b : Nat)
  statement: a = b ↔ a / n = b / n ∧ a ≡ b [MOD n]
  proof: ext_div_mod_iff _ _ _

中文:
定理 ext_div_modEq_iff
  条件: (n a b : 自然数)
  结论: a = b ↔ a / n = b / n ∧ a ≡ b [MOD n]
  证明: ext_div_mod_iff _ _ _

Depends on / 依赖: ext_div_mod_iff
-/
theorem ext_div_modEq_iff (n a b : Nat) : a = b ↔ a / n = b / n ∧ a ≡ b [MOD n] :=
  ext_div_mod_iff _ _ _

/--
theorem `modEq_iff_eq_of_div_eq` / 定理 `modEq_iff_eq_of_div_eq`

English:
theorem modEq_iff_eq_of_div_eq
  given: {n a b : Nat} (h : a / n = b / n)
  proof: by grind [ext_div_modEq_iff]

中文:
定理 modEq_iff_eq_of_div_eq
  条件: {n a b : 自然数} (h : a / n = b / n)
  证明: by grind [ext_div_modEq_iff]

Depends on / 依赖: ext_div_modEq_iff
-/
theorem modEq_iff_eq_of_div_eq {n a b : Nat} (h : a / n = b / n) :
    a ≡ b [MOD n] ↔ a = b := by grind [ext_div_modEq_iff]

end Nat
