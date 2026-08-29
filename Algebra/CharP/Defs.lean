/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Order.Lattice

/-!
# Characteristic of semirings

## Main definitions
* `CharP R p` expresses that the ring (additive monoid with one) `R` has characteristic `p`
* `ringChar`: the characteristic of a ring
* `ExpChar R p` expresses that the ring (additive monoid with one) `R` has
  exponential characteristic `p` (which is `1` if `R` has characteristic 0, and `p` if it has
  prime characteristic `p`)
-/

@[expose] public section

assert_not_exists Field Finset OrderHom

variable (R : Type*)

namespace CharP
section AddMonoidWithOne
variable [AddMonoidWithOne R] (p : Nat)

/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R.

*Warning*: for a semiring `R`, `CharP R 0` and `CharZero R` need not coincide.
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `CharZero R` requires an injection `ℕ ↪ R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
@[mk_iff]
/--
Definition of `_root_.CharP` / `_root_.CharP` 的定义

English:
class _root_.CharP
  parameters: (R : Type*) [AddMonoidWithOne R] (p : outParam Nat)
  axioms and operations (1):
    - cast_eq_zero_iff((R p)) : forall x : Nat, (x : R) = 0 ↔ p ∣ x

中文:
类 _root_.特征p
  参数: (R : 类型) [加法带幺幺半群 R] (p : outParam 自然数)
  公理与运算 (1 个):
    - cast_eq_zero_iff((R p)) : 对任意 x : 自然数, (x : R) = 0 ↔ p ∣ x
-/
class _root_.CharP (R : Type*) [AddMonoidWithOne R] (p : outParam Nat) : Prop where
  cast_eq_zero_iff (R p) : forall x : Nat, (x : R) = 0 ↔ p ∣ x

variable [CharP R p] {a b : Nat}

/--
lemma `_root_.CharP.ofNat_eq_zero'` / 引理 `_root_.CharP.ofNat_eq_zero'`

English:
lemma _root_.CharP.ofNat_eq_zero'
  statement: (p : Nat) [CharP R p]
  proof: by
  rwa [← CharP.cast_eq_zero_iff R p] at h

中文:
引理 _root_.特征p.of自然数_eq_zero'
  结论: (p : 自然数) [特征p R p]
  证明: by
  rwa [← CharP.cast_eq_zero_iff R p] at h

Depends on / 依赖: CharP.cast_eq_zero_iff, cast_eq_zero_iff
-/
lemma _root_.CharP.ofNat_eq_zero' (p : Nat) [CharP R p]
    (a : Nat) [a.AtLeastTwo] (h : p ∣ a) :
    (ofNat(a) : R) = 0 := by
  rwa [← CharP.cast_eq_zero_iff R p] at h

variable {R} in
/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: {q : Nat} (h : p = q)
  statement: CharP R q
  proof: h ▸ ‹CharP R p›

中文:
引理 congr
  条件: {q : 自然数} (h : p = q)
  结论: 特征p R q
  证明: h ▸ ‹CharP R p›
-/
lemma congr {q : Nat} (h : p = q) : CharP R q := h ▸ ‹CharP R p›

/--
lemma `cast_eq_zero` / 引理 `cast_eq_zero`

English:
lemma cast_eq_zero
  statement: (p : R) = 0
  proof: (cast_eq_zero_iff R p p).2 dvd_rfl

中文:
引理 cast_eq_zero
  结论: (p : R) = 0
  证明: (cast_eq_zero_iff R p p).2 dvd_rfl
-/
@[simp] lemma cast_eq_zero : (p : R) = 0 := (cast_eq_zero_iff R p p).2 dvd_rfl

/--
lemma `cast_eq_mod` / 引理 `cast_eq_mod`

English:
lemma cast_eq_mod
  given: (k : Nat)
  statement: (k : R) = (k % p : Nat)
  proof: have (a : Nat) : ((p * a : Nat) : R) = 0 := by
    rw [CharP.cast_eq_zero_iff R p]
    exact Nat.dvd_mul_right p a
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Nat.mod_add_div]
    _ = ↑(k % p) := by simp [this]

中文:
引理 cast_eq_mod
  条件: (k : 自然数)
  结论: (k : R) = (k % p : 自然数)
  证明: have (a : Nat) : ((p * a : Nat) : R) = 0 := by
    rw [CharP.cast_eq_zero_iff R p]
    exact Nat.dvd_mul_right p a
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Nat.mod_add_div]
    _ = ↑(k % p) := by simp [this]

Depends on / 依赖: CharP.cast_eq_zero_iff, Nat.dvd_mul_right, Nat.mod_add_div, cast_eq_zero_iff, dvd_mul_right, mod_add_div
-/
lemma cast_eq_mod (k : Nat) : (k : R) = (k % p : Nat) :=
  have (a : Nat) : ((p * a : Nat) : R) = 0 := by
    rw [CharP.cast_eq_zero_iff R p]
    exact Nat.dvd_mul_right p a
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Nat.mod_add_div]
    _ = ↑(k % p) := by simp [this]

/--
lemma `cast_eq_iff_mod_eq` / 引理 `cast_eq_iff_mod_eq`

English:
lemma cast_eq_iff_mod_eq
  given: [IsLeftCancelAdd R]
  statement: (a : R) = (b : R) ↔ a % p = b % p
  proof: by
  wlog! hle : a <= b
  · simpa only [eq_comm] using (this _ _ hle.le)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.cast_add]; rw [left_eq_add]; rw [CharP.cast_eq_zero_iff R p]
  constructor
  · simp +contextual [Nat.add_mod, Nat.dvd_iff_mod_eq_zero]
  intro h
  have := Nat.sub_mod_e

中文:
引理 cast_eq_iff_mod_eq
  条件: [是左消去加法 R]
  结论: (a : R) = (b : R) ↔ a % p = b % p
  证明: by
  wlog! hle : a <= b
  · simpa only [eq_comm] using (this _ _ hle.le)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.cast_add]; rw [left_eq_add]; rw [CharP.cast_eq_zero_iff R p]
  constructor
  · simp +contextual [Nat.add_mod, Nat.dvd_iff_mod_eq_zero]
  intro h
  have := Nat.sub_mod_e

Depends on / 依赖: CharP.cast_eq_zero_iff, Nat.add_mod, Nat.cast_add, Nat.dvd_iff_mod_eq_zero, Nat.exists_eq_add_of_le, Nat.sub_mod_eq_zero_of_mod_eq, add_mod, cast_add, cast_eq_zero_iff, contextual, dvd_iff_mod_eq_zero, eq_comm, exists_eq_add_of_le, h.symm, hle.le, left_eq_add, sub_mod_eq_zero_of_mod_eq
-/
lemma cast_eq_iff_mod_eq [IsLeftCancelAdd R] : (a : R) = (b : R) ↔ a % p = b % p := by
  wlog! hle : a <= b
  · simpa only [eq_comm] using (this _ _ hle.le)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.cast_add]; rw [left_eq_add]; rw [CharP.cast_eq_zero_iff R p]
  constructor
  · simp +contextual [Nat.add_mod, Nat.dvd_iff_mod_eq_zero]
  intro h
  have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  simpa [Nat.dvd_iff_mod_eq_zero] using this

-- TODO: This lemma needs to be `@[simp]` for confluence in the presence of `CharP.cast_eq_zero` and
-- `Nat.cast_ofNat`, but with `no_index` on its entire LHS, it matches literally every expression so
-- is too expensive. If https://github.com/leanprover/lean4/issues/2867 is fixed in a performant way, this can be made `@[simp]`.
--
-- @[simp]
/--
lemma `ofNat_eq_zero` / 引理 `ofNat_eq_zero`

English:
lemma ofNat_eq_zero
  given: [p.AtLeastTwo]
  statement: (ofNat(p) : R) = 0
  proof: cast_eq_zero R p

中文:
引理 of自然数_eq_zero
  条件: [p.AtLeastTwo]
  结论: (of自然数(p) : R) = 0
  证明: cast_eq_zero R p

Depends on / 依赖: cast_eq_zero
-/
lemma ofNat_eq_zero [p.AtLeastTwo] : (ofNat(p) : R) = 0 := cast_eq_zero R p

/--
lemma `eq` / 引理 `eq`

English:
lemma eq
  given: {p q : Nat} (hp : CharP R p) (hq : CharP R q)
  statement: p = q
  proof: Nat.dvd_antisymm ((cast_eq_zero_iff (self := hp) R p q).1 (@cast_eq_zero _ _ _ hq))
    ((cast_eq_zero_iff (self := hq) R q p).1 (@cast_eq_zero _ _ _ hp))

中文:
引理 eq
  条件: {p q : 自然数} (hp : 特征p R p) (hq : 特征p R q)
  结论: p = q
  证明: Nat.dvd_antisymm ((cast_eq_zero_iff (self := hp) R p q).1 (@cast_eq_zero _ _ _ hq))
    ((cast_eq_zero_iff (self := hq) R q p).1 (@cast_eq_zero _ _ _ hp))

Depends on / 依赖: Nat.dvd_antisymm, cast_eq_zero, cast_eq_zero_iff, dvd_antisymm
-/
lemma eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q :=
  Nat.dvd_antisymm ((cast_eq_zero_iff (self := hp) R p q).1 (@cast_eq_zero _ _ _ hq))
    ((cast_eq_zero_iff (self := hq) R q p).1 (@cast_eq_zero _ _ _ hp))

/--
Instance `ofCharZero` / 实例 `ofCharZero`

English:
instance ofCharZero
  signature: [CharZero R]
  body: by rw [zero_dvd_iff, ← Nat.cast_zero, Nat.cast_inj]

中文:
实例 ofCharZero
  签名: [特征零 R]
  定义体: by rw [zero_dvd_iff, ← Nat.cast_zero, Nat.cast_inj]

Depends on / 依赖: Nat.cast_inj, Nat.cast_zero, cast_inj, cast_zero, zero_dvd_iff
-/
instance ofCharZero [CharZero R] : CharP R 0 where
  cast_eq_zero_iff x := by rw [zero_dvd_iff, ← Nat.cast_zero, Nat.cast_inj]

end AddMonoidWithOne

section AddGroupWithOne
variable [AddGroupWithOne R] (p : Nat) [CharP R p] {a b : Int}

/--
lemma `intCast_eq_zero_iff` / 引理 `intCast_eq_zero_iff`

English:
lemma intCast_eq_zero_iff
  given: (a : Int)
  statement: (a : R) = 0 ↔ (p : Int) ∣ a
  proof: by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← Int.dvd_neg]
    lift -a to Nat using Int.neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_natCast]; rw [CharP.cast_eq_zero_iff R p]; rw [Int.natCast_dvd_natCast]
  · simp
  · lift a to Nat using le_of_lt h 

中文:
引理 intCast_eq_zero_iff
  条件: (a : 整数)
  结论: (a : R) = 0 ↔ (p : 整数) ∣ a
  证明: by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← Int.dvd_neg]
    lift -a to Nat using Int.neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_natCast]; rw [CharP.cast_eq_zero_iff R p]; rw [Int.natCast_dvd_natCast]
  · simp
  · lift a to Nat using le_of_lt h 

Depends on / 依赖: CharP.cast_eq_zero_iff, CommSemiring, Int.cast_natCast, Int.cast_neg, Int.dvd_neg, Int.natCast_dvd_natCast, Int.neg_nonneg.mpr, R.carrier, carrier, cast_eq_zero_iff, cast_natCast, cast_neg, dvd_neg, le_of_lt, lt_trichotomy, natCast_dvd_natCast, neg_eq_zero, neg_nonneg
-/
lemma intCast_eq_zero_iff (a : Int) : (a : R) = 0 ↔ (p : Int) ∣ a := by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← Int.dvd_neg]
    lift -a to Nat using Int.neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_natCast]; rw [CharP.cast_eq_zero_iff R p]; rw [Int.natCast_dvd_natCast]
  · simp
  · lift a to Nat using le_of_lt h with b
    rw [Int.cast_natCast]; rw [CharP.cast_eq_zero_iff R p]; rw [Int.natCast_dvd_natCast]

/--
lemma `charP_to_charZero` / 引理 `charP_to_charZero`

English:
lemma charP_to_charZero
  given: [CharP R 0]
  statement: CharZero R
  proof: charZero_of_inj_zero fun n h0 => eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)

中文:
引理 charP_to_charZero
  条件: [特征p R 0]
  结论: 特征零 R
  证明: charZero_of_inj_zero fun n h0 => eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)

Depends on / 依赖: cast_eq_zero_iff, charZero_of_inj_zero, eq_zero_of_zero_dvd
-/
lemma charP_to_charZero [CharP R 0] : CharZero R :=
  charZero_of_inj_zero fun n h0 => eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)

/--
lemma `charP_zero_iff_charZero` / 引理 `charP_zero_iff_charZero`

English:
lemma charP_zero_iff_charZero
  statement: CharP R 0 ↔ CharZero R
  proof: ⟨fun _ => charP_to_charZero R, fun _ => ofCharZero R⟩

中文:
引理 charP_zero_iff_charZero
  结论: 特征p R 0 ↔ 特征零 R
  证明: ⟨fun _ => charP_to_charZero R, fun _ => ofCharZero R⟩

Depends on / 依赖: charP_to_charZero, ofCharZero
-/
lemma charP_zero_iff_charZero : CharP R 0 ↔ CharZero R :=
  ⟨fun _ => charP_to_charZero R, fun _ => ofCharZero R⟩

end AddGroupWithOne

section NonAssocSemiring
variable [NonAssocSemiring R]

/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  statement: exists p, CharP R p
  proof: letI := Classical.decEq R
  by_cases
    (fun H : forall p : Nat, (p : R) = 0 -> p = 0 =>
      ⟨0, ⟨fun x => by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; simp⟩⟩⟩)
    fun H =>
    ⟨Nat.find (not_forall.1 H),
      ⟨fun x =>
        ⟨fun H1 =>
          Nat.dvd_of_mod_eq_zero
            (by_con

中文:
引理 «存在»
  结论: 存在 p, 特征p R p
  证明: letI := Classical.decEq R
  by_cases
    (fun H : forall p : Nat, (p : R) = 0 -> p = 0 =>
      ⟨0, ⟨fun x => by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; simp⟩⟩⟩)
    fun H =>
    ⟨Nat.find (not_forall.1 H),
      ⟨fun x =>
        ⟨fun H1 =>
          Nat.dvd_of_mod_eq_zero
            (by_con
-/
lemma «exists» : exists p, CharP R p :=
  letI := Classical.decEq R
  by_cases
    (fun H : forall p : Nat, (p : R) = 0 -> p = 0 =>
      ⟨0, ⟨fun x => by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; simp⟩⟩⟩)
    fun H =>
    ⟨Nat.find (not_forall.1 H),
      ⟨fun x =>
        ⟨fun H1 =>
          Nat.dvd_of_mod_eq_zero
            (by_contradiction fun H2 =>
              Nat.find_min (not_forall.1 H)
                (Nat.mod_lt x <|
Nat.pos_of_ne_zero not_of_not_imp Nat.find_spec (not_forall.1 H))
                (not_imp_of_and_not
                  ⟨by
                    rwa [← Nat.mod_add_div x (Nat.find (not_forall.1 H)), Nat.cast_add,
                      Nat.cast_mul,
                      of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H)),
                      zero_mul, add_zero] at H1,
                    H2⟩)),
          fun H1 => by
          rw [← Nat.mul_div_cancel' H1]; rw [Nat.cast_mul]; rw [of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H))]; rw [zero_mul]⟩⟩⟩

/--
lemma `existsUnique` / 引理 `existsUnique`

English:
lemma existsUnique
  statement: exists! p, CharP R p
  proof: let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩

中文:
引理 存在Unique
  结论: 存在! p, 特征p R p
  证明: let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩

Depends on / 依赖: CharP.eq, CharP.exists
-/
lemma existsUnique : exists! p, CharP R p :=
  let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩

end NonAssocSemiring
end CharP

/--
Definition of `ringChar` / `ringChar` 的定义

English:
definition ringChar
  signature: [NonAssocSemiring R]
  body: Classical.choose (CharP.existsUnique R)

中文:
定义 ringChar
  签名: [非结合半环 R]
  定义体: Classical.choose (CharP.existsUnique R)

Depends on / 依赖: CharP.existsUnique, Classical, Classical.choose, existsUnique
-/
noncomputable def ringChar [NonAssocSemiring R] : Nat := Classical.choose (CharP.existsUnique R)

namespace ringChar
variable [NonAssocSemiring R]

/--
lemma `spec` / 引理 `spec`

English:
lemma spec
  statement: forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x
  proof: by
  let : CharP R (ringChar R) := (Classical.choose_spec (CharP.existsUnique R)).1
  exact CharP.cast_eq_zero_iff R (ringChar R)

中文:
引理 spec
  结论: 对任意 x : 自然数, (x : R) = 0 ↔ ringChar R ∣ x
  证明: by
  let : CharP R (ringChar R) := (Classical.choose_spec (CharP.existsUnique R)).1
  exact CharP.cast_eq_zero_iff R (ringChar R)

Depends on / 依赖: CharP.cast_eq_zero_iff, CharP.existsUnique, Classical, Classical.choose_spec, cast_eq_zero_iff, choose_spec, existsUnique, ringChar
-/
lemma spec : forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x := by
  let : CharP R (ringChar R) := (Classical.choose_spec (CharP.existsUnique R)).1
  exact CharP.cast_eq_zero_iff R (ringChar R)

/--
lemma `eq` / 引理 `eq`

English:
lemma eq
  given: (p : Nat) [C : CharP R p]
  statement: ringChar R = p
  proof: ((Classical.choose_spec (CharP.existsUnique R)).2 p C).symm

中文:
引理 eq
  条件: (p : 自然数) [C : 特征p R p]
  结论: ringChar R = p
  证明: ((Classical.choose_spec (CharP.existsUnique R)).2 p C).symm

Depends on / 依赖: CharP.existsUnique, Classical, Classical.choose_spec, choose_spec, existsUnique
-/
lemma eq (p : Nat) [C : CharP R p] : ringChar R = p :=
  ((Classical.choose_spec (CharP.existsUnique R)).2 p C).symm

instance (priority := low) charP : CharP R (ringChar R) :=
  ⟨spec R⟩

variable {R}

/--
lemma `of_eq` / 引理 `of_eq`

English:
lemma of_eq
  given: {p : Nat} (h : ringChar R = p)
  statement: CharP R p
  proof: CharP.congr (ringChar R) h

中文:
引理 of_eq
  条件: {p : 自然数} (h : ringChar R = p)
  结论: 特征p R p
  证明: CharP.congr (ringChar R) h

Depends on / 依赖: CharP.congr, ringChar
-/
lemma of_eq {p : Nat} (h : ringChar R = p) : CharP R p :=
  CharP.congr (ringChar R) h

/--
lemma `eq_iff` / 引理 `eq_iff`

English:
lemma eq_iff
  given: {p : Nat}
  statement: ringChar R = p ↔ CharP R p
  proof: ⟨of_eq, @eq R _ p⟩

中文:
引理 eq_iff
  条件: {p : 自然数}
  结论: ringChar R = p ↔ 特征p R p
  证明: ⟨of_eq, @eq R _ p⟩

Depends on / 依赖: of_eq
-/
lemma eq_iff {p : Nat} : ringChar R = p ↔ CharP R p :=
  ⟨of_eq, @eq R _ p⟩

/--
lemma `dvd` / 引理 `dvd`

English:
lemma dvd
  given: {x : Nat} (hx : (x : R) = 0)
  statement: ringChar R ∣ x
  proof: (spec R x).1 hx

@[simp]

中文:
引理 dvd
  条件: {x : 自然数} (hx : (x : R) = 0)
  结论: ringChar R ∣ x
  证明: (spec R x).1 hx

@[simp]
-/
lemma dvd {x : Nat} (hx : (x : R) = 0) : ringChar R ∣ x :=
  (spec R x).1 hx

@[simp]
/--
lemma `eq_zero` / 引理 `eq_zero`

English:
lemma eq_zero
  given: [CharZero R]
  statement: ringChar R = 0
  proof: eq R 0

中文:
引理 eq_zero
  条件: [特征零 R]
  结论: ringChar R = 0
  证明: eq R 0
-/
lemma eq_zero [CharZero R] : ringChar R = 0 :=
  eq R 0

/--
lemma `Nat.cast_ringChar` / 引理 `Nat.cast_ringChar`

English:
lemma Nat.cast_ringChar
  statement: (ringChar R : R) = 0
  proof: by rw [ringChar.spec]

@[simp]

中文:
引理 自然数.cast_ringChar
  结论: (ringChar R : R) = 0
  证明: by rw [ringChar.spec]

@[simp]

Depends on / 依赖: CommRingCat, ConcreteCategory, ConcreteCategory.hom, ringChar, ringChar.spec
-/
lemma Nat.cast_ringChar : (ringChar R : R) = 0 := by rw [ringChar.spec]

@[simp]
/--
lemma `ringChar_eq_one` / 引理 `ringChar_eq_one`

English:
lemma ringChar_eq_one
  statement: ringChar R = 1 ↔ Subsingleton R
  proof: by
  rw [← Nat.dvd_one]; rw [← spec]; rw [eq_comm]; rw [Nat.cast_one]; rw [subsingleton_iff_zero_eq_one]

@[nontriviality]

中文:
引理 ringChar_eq_one
  结论: ringChar R = 1 ↔ 子单例 R
  证明: by
  rw [← Nat.dvd_one]; rw [← spec]; rw [eq_comm]; rw [Nat.cast_one]; rw [subsingleton_iff_zero_eq_one]

@[nontriviality]

Depends on / 依赖: Nat.cast_one, Nat.dvd_one, cast_one, dvd_one, eq_comm, subsingleton_iff_zero_eq_one
-/
lemma ringChar_eq_one : ringChar R = 1 ↔ Subsingleton R := by
  rw [← Nat.dvd_one]; rw [← spec]; rw [eq_comm]; rw [Nat.cast_one]; rw [subsingleton_iff_zero_eq_one]

@[nontriviality]
/--
lemma `ringChar_subsingleton` / 引理 `ringChar_subsingleton`

English:
lemma ringChar_subsingleton
  given: [Subsingleton R]
  statement: ringChar R = 1
  proof: by simpa

中文:
引理 ringChar_subsingleton
  条件: [子单例 R]
  结论: ringChar R = 1
  证明: by simpa

Depends on / 依赖: f.hom
-/
lemma ringChar_subsingleton [Subsingleton R] : ringChar R = 1 := by simpa

end ringChar

/--
lemma `CharP.neg_one_ne_one` / 引理 `CharP.neg_one_ne_one`

English:
lemma CharP.neg_one_ne_one
  given: [AddGroupWithOne R] (p : Nat) [CharP R p] [Fact (2 < p)]
  proof: by
  rw [ne_comm]; rw [← sub_ne_zero]; rw [sub_neg_eq_add]; rw [one_add_one_eq_two]; rw [← Nat.cast_two]; rw [Ne]; rw [CharP.cast_eq_zero_iff R p 2]
exact fun h => (Fact.out : 2 < p).not_ge Nat.le_of_dvd Nat.zero_lt_two h

中文:
引理 特征p.neg_one_ne_one
  条件: [加法带幺群 R] (p : 自然数) [特征p R p] [Fact (2 < p)]
  证明: by
  rw [ne_comm]; rw [← sub_ne_zero]; rw [sub_neg_eq_add]; rw [one_add_one_eq_two]; rw [← Nat.cast_two]; rw [Ne]; rw [CharP.cast_eq_zero_iff R p 2]
exact fun h => (Fact.out : 2 < p).not_ge Nat.le_of_dvd Nat.zero_lt_two h

Depends on / 依赖: CharP.cast_eq_zero_iff, Fact.out, Nat.cast_two, Nat.le_of_dvd, Nat.zero_lt_two, cast_eq_zero_iff, cast_two, le_of_dvd, ne_comm, not_ge, one_add_one_eq_two, sub_ne_zero, sub_neg_eq_add, zero_lt_two
-/
lemma CharP.neg_one_ne_one [AddGroupWithOne R] (p : Nat) [CharP R p] [Fact (2 < p)] :
    (-1 : R) != (1 : R) := by
  rw [ne_comm]; rw [← sub_ne_zero]; rw [sub_neg_eq_add]; rw [one_add_one_eq_two]; rw [← Nat.cast_two]; rw [Ne]; rw [CharP.cast_eq_zero_iff R p 2]
exact fun h => (Fact.out : 2 < p).not_ge Nat.le_of_dvd Nat.zero_lt_two h

namespace CharP

section

variable [NonAssocRing R]

/--
lemma `ringChar_zero_iff_CharZero` / 引理 `ringChar_zero_iff_CharZero`

English:
lemma ringChar_zero_iff_CharZero
  statement: ringChar R = 0 ↔ CharZero R
  proof: by
  rw [ringChar.eq_iff]; rw [charP_zero_iff_charZero]

中文:
引理 ringChar_zero_iff_CharZero
  结论: ringChar R = 0 ↔ 特征零 R
  证明: by
  rw [ringChar.eq_iff]; rw [charP_zero_iff_charZero]

Depends on / 依赖: charP_zero_iff_charZero, eq_iff, ringChar, ringChar.eq_iff
-/
lemma ringChar_zero_iff_CharZero : ringChar R = 0 ↔ CharZero R := by
  rw [ringChar.eq_iff]; rw [charP_zero_iff_charZero]

end

section Semiring

variable [NonAssocSemiring R]

/--
lemma `char_ne_one` / 引理 `char_ne_one`

English:
lemma char_ne_one
  given: [Nontrivial R] (p : Nat) [hc : CharP R p]
  statement: p != 1
  proof: fun hp : p = 1 =>
  have : (1 : R) = 0 := by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p)
  absurd this one_ne_zero

中文:
引理 char_ne_one
  条件: [非平凡 R] (p : 自然数) [hc : 特征p R p]
  结论: p != 1
  证明: fun hp : p = 1 =>
  have : (1 : R) = 0 := by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p)
  absurd this one_ne_zero
-/
lemma char_ne_one [Nontrivial R] (p : Nat) [hc : CharP R p] : p != 1 := fun hp : p = 1 =>
  have : (1 : R) = 0 := by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p)
  absurd this one_ne_zero

section NoZeroDivisors

variable [NoZeroDivisors R]

/--
lemma `char_is_prime_of_two_le` / 引理 `char_is_prime_of_two_le`

English:
lemma char_is_prime_of_two_le
  given: (p : Nat) [CharP R p] (hp : 2 <= p)
  statement: Nat.Prime p
  proof: suffices forall (d) (_ : d ∣ p), d = 1 ∨ d = p from Nat.prime_def.mpr ⟨hp, this⟩
  fun (d : Nat) (hdvd : exists e, p = d * e) =>
  let ⟨e, hmul⟩ := hdvd
  have : (p : R) = 0 := (cast_eq_zero_iff R p p).mpr (dvd_refl p)
  have : (d : R) * e = 0 := @Nat.cast_mul R _ d e ▸ hmul ▸ this
  Or.elim (eq_zer

中文:
引理 char_is_prime_of_two_le
  条件: (p : 自然数) [特征p R p] (hp : 2 <= p)
  结论: 自然数.素 p
  证明: suffices forall (d) (_ : d ∣ p), d = 1 ∨ d = p from Nat.prime_def.mpr ⟨hp, this⟩
  fun (d : Nat) (hdvd : exists e, p = d * e) =>
  let ⟨e, hmul⟩ := hdvd
  have : (p : R) = 0 := (cast_eq_zero_iff R p p).mpr (dvd_refl p)
  have : (d : R) * e = 0 := @Nat.cast_mul R _ d e ▸ hmul ▸ this
  Or.elim (eq_zer

Depends on / 依赖: Nat.cast_mul, Nat.prime_def.mpr, Or.elim, Or.inr, antisymm, cast_eq_zero_iff, cast_mul, dvd_refl, eq_zero_or_eq_zero_of_mul_eq_zero, prime_def, this.antisymm
-/
lemma char_is_prime_of_two_le (p : Nat) [CharP R p] (hp : 2 <= p) : Nat.Prime p :=
  suffices forall (d) (_ : d ∣ p), d = 1 ∨ d = p from Nat.prime_def.mpr ⟨hp, this⟩
  fun (d : Nat) (hdvd : exists e, p = d * e) =>
  let ⟨e, hmul⟩ := hdvd
  have : (p : R) = 0 := (cast_eq_zero_iff R p p).mpr (dvd_refl p)
  have : (d : R) * e = 0 := @Nat.cast_mul R _ d e ▸ hmul ▸ this
  Or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
    (fun hd : (d : R) = 0 =>
      have : p ∣ d := (cast_eq_zero_iff R p d).mp hd
      show d = 1 ∨ d = p from Or.inr (this.antisymm' ⟨e, hmul⟩))
    fun he : (e : R) = 0 =>
    have : p ∣ e := (cast_eq_zero_iff R p e).mp he
    have : e ∣ p := dvd_of_mul_left_eq d (Eq.symm hmul)
    have : e = p := ‹e ∣ p›.antisymm ‹p ∣ e›
    have h₀ : 0 < p := by grind
    have : d * p = 1 * p := by grind
    show d = 1 ∨ d = p from Or.inl (mul_right_cancel₀ h₀.ne' this)

section Nontrivial

variable [Nontrivial R]

/--
lemma `char_is_prime_or_zero` / 引理 `char_is_prime_or_zero`

English:
lemma char_is_prime_or_zero
  given: (p : Nat) [hc : CharP R p]
  statement: Nat.Prime p ∨ p = 0
  proof: match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : Nat)) (@char_ne_one R _ _ (1 : Nat) hc)
  | m + 2, hc => Or.inl (@char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_left 2 m))

中文:
引理 char_is_prime_or_zero
  条件: (p : 自然数) [hc : 特征p R p]
  结论: 自然数.素 p ∨ p = 0
  证明: match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : Nat)) (@char_ne_one R _ _ (1 : Nat) hc)
  | m + 2, hc => Or.inl (@char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_left 2 m))

Depends on / 依赖: Eq.refl, Nat.le_add_left, Or.inl, Or.inr, absurd, char_is_prime_of_two_le, char_ne_one, le_add_left
-/
lemma char_is_prime_or_zero (p : Nat) [hc : CharP R p] : Nat.Prime p ∨ p = 0 :=
  match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : Nat)) (@char_ne_one R _ _ (1 : Nat) hc)
  | m + 2, hc => Or.inl (@char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_left 2 m))

/--
lemma `char_prime_of_ne_zero` / 引理 `char_prime_of_ne_zero`

English:
lemma char_prime_of_ne_zero
  given: {p : Nat} [CharP R p] (hp : p != 0)
  statement: p.Prime
  proof: (CharP.char_is_prime_or_zero R p).resolve_right hp

中文:
引理 char_prime_of_ne_zero
  条件: {p : 自然数} [特征p R p] (hp : p != 0)
  结论: p.素
  证明: (CharP.char_is_prime_or_zero R p).resolve_right hp

Depends on / 依赖: CharP.char_is_prime_or_zero, char_is_prime_or_zero, resolve_right
-/
lemma char_prime_of_ne_zero {p : Nat} [CharP R p] (hp : p != 0) : p.Prime :=
  (CharP.char_is_prime_or_zero R p).resolve_right hp

/--
lemma `exists'` / 引理 `exists'`

English:
lemma exists'
  given: (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R]
  proof: by
  obtain ⟨p, hchar⟩ := CharP.exists R
  rcases char_is_prime_or_zero R p with h | rfl
  exacts [Or.inr ⟨p, Fact.mk h, hchar⟩, Or.inl (charP_to_charZero R)]

中文:
引理 存在'
  条件: (R : 类型) [非结合环 R] [无零因子 R] [非平凡 R]
  证明: by
  obtain ⟨p, hchar⟩ := CharP.exists R
  rcases char_is_prime_or_zero R p with h | rfl
  exacts [Or.inr ⟨p, Fact.mk h, hchar⟩, Or.inl (charP_to_charZero R)]

Depends on / 依赖: CharP.exists, Fact.mk, Or.inl, Or.inr, charP_to_charZero, char_is_prime_or_zero, exacts
-/
lemma exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ∨ exists p : Nat, Fact p.Prime ∧ CharP R p := by
  obtain ⟨p, hchar⟩ := CharP.exists R
  rcases char_is_prime_or_zero R p with h | rfl
  exacts [Or.inr ⟨p, Fact.mk h, hchar⟩, Or.inl (charP_to_charZero R)]

/--
lemma `char_is_prime_of_pos` / 引理 `char_is_prime_of_pos`

English:
lemma char_is_prime_of_pos
  given: (p : Nat) [NeZero p] [CharP R p]
  statement: Fact p.Prime
  proof: ⟨(CharP.char_is_prime_or_zero R _).resolve_right NeZero.ne p⟩

中文:
引理 char_is_prime_of_pos
  条件: (p : 自然数) [NeZero p] [特征p R p]
  结论: Fact p.素
  证明: ⟨(CharP.char_is_prime_or_zero R _).resolve_right NeZero.ne p⟩

Depends on / 依赖: CharP.char_is_prime_or_zero, NeZero, NeZero.ne, char_is_prime_or_zero, resolve_right
-/
lemma char_is_prime_of_pos (p : Nat) [NeZero p] [CharP R p] : Fact p.Prime :=
⟨(CharP.char_is_prime_or_zero R _).resolve_right NeZero.ne p⟩

end Nontrivial

end NoZeroDivisors

end Semiring

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

-- This lemma is not an instance, to make sure that trying to prove `α` is a subsingleton does
-- not try to find a ring structure on `α`, which can be expensive.
/--
lemma `CharOne.subsingleton` / 引理 `CharOne.subsingleton`

English:
lemma CharOne.subsingleton
  given: [CharP R 1]
  statement: Subsingleton R
  proof: Subsingleton.intro
    suffices forall r : R, r = 0 from fun a b => show a = b by rw [this a, this b]
    fun r =>
    calc
      r = 1 * r := by rw [one_mul]
      _ = (1 : Nat) * r := by rw [Nat.cast_one]
      _ = 0 * r := by rw [CharP.cast_eq_zero]
      _ = 0 := by rw [zero_mul]

中文:
引理 CharOne.subsingleton
  条件: [特征p R 1]
  结论: 子单例 R
  证明: Subsingleton.intro
    suffices forall r : R, r = 0 from fun a b => show a = b by rw [this a, this b]
    fun r =>
    calc
      r = 1 * r := by rw [one_mul]
      _ = (1 : Nat) * r := by rw [Nat.cast_one]
      _ = 0 * r := by rw [CharP.cast_eq_zero]
      _ = 0 := by rw [zero_mul]

Depends on / 依赖: CharP.cast_eq_zero, Nat.cast_one, Subsingleton, Subsingleton.intro, cast_eq_zero, cast_one, one_mul, zero_mul
-/
lemma CharOne.subsingleton [CharP R 1] : Subsingleton R :=
Subsingleton.intro
    suffices forall r : R, r = 0 from fun a b => show a = b by rw [this a, this b]
    fun r =>
    calc
      r = 1 * r := by rw [one_mul]
      _ = (1 : Nat) * r := by rw [Nat.cast_one]
      _ = 0 * r := by rw [CharP.cast_eq_zero]
      _ = 0 := by rw [zero_mul]

/--
lemma `false_of_nontrivial_of_char_one` / 引理 `false_of_nontrivial_of_char_one`

English:
lemma false_of_nontrivial_of_char_one
  given: [Nontrivial R] [CharP R 1]
  statement: False
  proof: by
  have : Subsingleton R := CharOne.subsingleton
  exact false_of_nontrivial_of_subsingleton R

中文:
引理 false_of_nontrivial_of_char_one
  条件: [非平凡 R] [特征p R 1]
  结论: 假
  证明: by
  have : Subsingleton R := CharOne.subsingleton
  exact false_of_nontrivial_of_subsingleton R

Depends on / 依赖: CharOne, CharOne.subsingleton, Subsingleton, false_of_nontrivial_of_subsingleton, subsingleton
-/
lemma false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False := by
  have : Subsingleton R := CharOne.subsingleton
  exact false_of_nontrivial_of_subsingleton R

/--
lemma `ringChar_ne_one` / 引理 `ringChar_ne_one`

English:
lemma ringChar_ne_one
  given: [Nontrivial R]
  statement: ringChar R != 1
  proof: by
  simpa using not_subsingleton R

中文:
引理 ringChar_ne_one
  条件: [非平凡 R]
  结论: ringChar R != 1
  证明: by
  simpa using not_subsingleton R

Depends on / 依赖: not_subsingleton
-/
lemma ringChar_ne_one [Nontrivial R] : ringChar R != 1 := by
  simpa using not_subsingleton R

/--
lemma `nontrivial_of_char_ne_one` / 引理 `nontrivial_of_char_ne_one`

English:
lemma nontrivial_of_char_ne_one
  given: {v : Nat} (hv : v != 1) [hr : CharP R v]
  statement: Nontrivial R
  proof: ⟨⟨(1 : Nat), 0, fun h =>
hv by rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h⟩⟩

中文:
引理 nontrivial_of_char_ne_one
  条件: {v : 自然数} (hv : v != 1) [hr : 特征p R v]
  结论: 非平凡 R
  证明: ⟨⟨(1 : Nat), 0, fun h =>
hv by rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h⟩⟩

Depends on / 依赖: CharP.cast_eq_zero_iff, Nat.dvd_one, cast_eq_zero_iff, dvd_one
-/
lemma nontrivial_of_char_ne_one {v : Nat} (hv : v != 1) [hr : CharP R v] : Nontrivial R :=
  ⟨⟨(1 : Nat), 0, fun h =>
hv by rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h⟩⟩

end NonAssocSemiring
end CharP

namespace NeZero

variable [AddMonoidWithOne R] {r : R} {n p : Nat}

/--
lemma `of_not_dvd` / 引理 `of_not_dvd`

English:
lemma of_not_dvd
  given: [CharP R p] (h : ¬p ∣ n)
  statement: NeZero (n : R)
  proof: ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩

中文:
引理 of_not_dvd
  条件: [特征p R p] (h : ¬p ∣ n)
  结论: NeZero (n : R)
  证明: ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩

Depends on / 依赖: CharP.cast_eq_zero_iff, cast_eq_zero_iff, not.mpr
-/
lemma of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R) :=
  ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩

/--
lemma `not_char_dvd` / 引理 `not_char_dvd`

English:
lemma not_char_dvd
  given: (p : Nat) [CharP R p] (k : Nat) [h : NeZero (k : R)]
  statement: ¬p ∣ k
  proof: by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne, ← neZero_iff]

中文:
引理 not_char_dvd
  条件: (p : 自然数) [特征p R p] (k : 自然数) [h : NeZero (k : R)]
  结论: ¬p ∣ k
  证明: by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne, ← neZero_iff]

Depends on / 依赖: CharP.cast_eq_zero_iff, CommRing, R.carrier, carrier, cast_eq_zero_iff, neZero_iff
-/
lemma not_char_dvd (p : Nat) [CharP R p] (k : Nat) [h : NeZero (k : R)] : ¬p ∣ k := by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne, ← neZero_iff]

end NeZero

/-!
### Exponential characteristic

This section defines the exponential characteristic, which is defined to be 1 for a ring with
characteristic 0 and the same as the ordinary characteristic, if the ordinary characteristic is
prime. This concept is useful to simplify some theorem statements.
This file establishes a few basic results relating it to the (ordinary characteristic).
The definition is stated for a semiring, but the actual results are for nontrivial rings
(as far as exponential characteristic one is concerned), respectively a ring without zero-divisors
(for prime characteristic).
-/

section AddMonoidWithOne
variable [AddMonoidWithOne R]

/--
Definition of `inductive` / `inductive` 的定义

English:
class inductive
  parameters: ExpChar
  (no additional axioms)

中文:
类 inductive
  参数: ExpChar
  (无附加公理)
-/
class inductive ExpChar : Nat -> Prop
  | zero [CharZero R] : ExpChar 1
  | prime {q : Nat} (hprime : q.Prime) [hchar : CharP R q] : ExpChar q

/--
Instance `expChar_prime` / 实例 `expChar_prime`

English:
instance expChar_prime
  signature: (p) [CharP R p] [Fact p.Prime]
  body: ExpChar.prime Fact.out

中文:
实例 expChar_prime
  签名: (p) [特征p R p] [Fact p.素]
  定义体: ExpChar.prime Fact.out

Depends on / 依赖: ExpChar, ExpChar.prime, Fact.out
-/
instance expChar_prime (p) [CharP R p] [Fact p.Prime] : ExpChar R p := ExpChar.prime Fact.out
/--
Instance `expChar_one` / 实例 `expChar_one`

English:
instance expChar_one
  signature: [CharZero R]
  body: ExpChar.zero

中文:
实例 expChar_one
  签名: [特征零 R]
  定义体: ExpChar.zero

Depends on / 依赖: ExpChar, ExpChar.zero
-/
instance expChar_one [CharZero R] : ExpChar R 1 := ExpChar.zero

/--
lemma `expChar_ne_zero` / 引理 `expChar_ne_zero`

English:
lemma expChar_ne_zero
  given: (p : Nat) [hR : ExpChar R p]
  statement: p != 0
  proof: by
  cases hR
  · exact one_ne_zero
  · exact ‹p.Prime›.ne_zero

中文:
引理 expChar_ne_zero
  条件: (p : 自然数) [hR : ExpChar R p]
  结论: p != 0
  证明: by
  cases hR
  · exact one_ne_zero
  · exact ‹p.Prime›.ne_zero

Depends on / 依赖: ne_zero, one_ne_zero, p.Prime
-/
lemma expChar_ne_zero (p : Nat) [hR : ExpChar R p] : p != 0 := by
  cases hR
  · exact one_ne_zero
  · exact ‹p.Prime›.ne_zero

variable {R} in
/--
lemma `ExpChar.eq` / 引理 `ExpChar.eq`

English:
lemma ExpChar.eq
  given: {p q : Nat} (hp : ExpChar R p) (hq : ExpChar R q)
  statement: p = q
  proof: by
  rcases hp with ⟨hp⟩ | ⟨hp'⟩
  · rcases hq with hq | hq'
    exacts [rfl, False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hq'))]
  · rcases hq with hq | hq'
    exacts [False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hp')),
      CharP.eq R ‹_› ‹_›]

中文:
引理 ExpChar.eq
  条件: {p q : 自然数} (hp : ExpChar R p) (hq : ExpChar R q)
  结论: p = q
  证明: by
  rcases hp with ⟨hp⟩ | ⟨hp'⟩
  · rcases hq with hq | hq'
    exacts [rfl, False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hq'))]
  · rcases hq with hq | hq'
    exacts [False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hp')),
      CharP.eq R ‹_› ‹_›]

Depends on / 依赖: CharP.eq, CharP.ofCharZero, False.elim, Nat.not_prime_zero, exacts, not_prime_zero, ofCharZero
-/
lemma ExpChar.eq {p q : Nat} (hp : ExpChar R p) (hq : ExpChar R q) : p = q := by
  rcases hp with ⟨hp⟩ | ⟨hp'⟩
  · rcases hq with hq | hq'
    exacts [rfl, False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hq'))]
  · rcases hq with hq | hq'
    exacts [False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hp')),
      CharP.eq R ‹_› ‹_›]

/--
lemma `ExpChar.congr` / 引理 `ExpChar.congr`

English:
lemma ExpChar.congr
  given: {p : Nat} (q : Nat) [hq : ExpChar R q] (h : q = p)
  statement: ExpChar R p
  proof: h ▸ hq

中文:
引理 ExpChar.congr
  条件: {p : 自然数} (q : 自然数) [hq : ExpChar R q] (h : q = p)
  结论: ExpChar R p
  证明: h ▸ hq
-/
lemma ExpChar.congr {p : Nat} (q : Nat) [hq : ExpChar R q] (h : q = p) : ExpChar R p := h ▸ hq

/--
lemma `expChar_one_of_char_zero` / 引理 `expChar_one_of_char_zero`

English:
lemma expChar_one_of_char_zero
  given: (q : Nat) [hp : CharP R 0] [hq : ExpChar R q]
  statement: q = 1
  proof: by
  rcases hq with q | hq_prime
  · rfl
· exact False.elim hq_prime.ne_zero ‹CharP R q›.eq R hp

中文:
引理 expChar_one_of_char_zero
  条件: (q : 自然数) [hp : 特征p R 0] [hq : ExpChar R q]
  结论: q = 1
  证明: by
  rcases hq with q | hq_prime
  · rfl
· exact False.elim hq_prime.ne_zero ‹CharP R q›.eq R hp

Depends on / 依赖: False.elim, hq_prime, hq_prime.ne_zero, ne_zero
-/
lemma expChar_one_of_char_zero (q : Nat) [hp : CharP R 0] [hq : ExpChar R q] : q = 1 := by
  rcases hq with q | hq_prime
  · rfl
· exact False.elim hq_prime.ne_zero ‹CharP R q›.eq R hp

/--
lemma `char_eq_expChar_iff` / 引理 `char_eq_expChar_iff`

English:
lemma char_eq_expChar_iff
  given: (p q : Nat) [hp : CharP R p] [hq : ExpChar R q]
  statement: p = q ↔ p.Prime
  proof: by
  rcases hq with q | hq_prime
  · rw [(CharP.eq R hp (.ofCharZero R) : p = 0)]
    decide
  · exact ⟨fun hpq => hpq.symm ▸ hq_prime, fun _ => CharP.eq R hp ‹CharP R q›⟩

中文:
引理 char_eq_expChar_iff
  条件: (p q : 自然数) [hp : 特征p R p] [hq : ExpChar R q]
  结论: p = q ↔ p.素
  证明: by
  rcases hq with q | hq_prime
  · rw [(CharP.eq R hp (.ofCharZero R) : p = 0)]
    decide
  · exact ⟨fun hpq => hpq.symm ▸ hq_prime, fun _ => CharP.eq R hp ‹CharP R q›⟩

Depends on / 依赖: CharP.eq, hpq.symm, hq_prime, ofCharZero
-/
lemma char_eq_expChar_iff (p q : Nat) [hp : CharP R p] [hq : ExpChar R q] : p = q ↔ p.Prime := by
  rcases hq with q | hq_prime
  · rw [(CharP.eq R hp (.ofCharZero R) : p = 0)]
    decide
  · exact ⟨fun hpq => hpq.symm ▸ hq_prime, fun _ => CharP.eq R hp ‹CharP R q›⟩

/--
lemma `expChar_is_prime_or_one` / 引理 `expChar_is_prime_or_one`

English:
lemma expChar_is_prime_or_one
  given: (q : Nat) [hq : ExpChar R q]
  statement: Nat.Prime q ∨ q = 1
  proof: by
  cases hq with
  | zero => exact .inr rfl
  | prime hp => exact .inl hp

中文:
引理 expChar_is_prime_or_one
  条件: (q : 自然数) [hq : ExpChar R q]
  结论: 自然数.素 q ∨ q = 1
  证明: by
  cases hq with
  | zero => exact .inr rfl
  | prime hp => exact .inl hp
-/
lemma expChar_is_prime_or_one (q : Nat) [hq : ExpChar R q] : Nat.Prime q ∨ q = 1 := by
  cases hq with
  | zero => exact .inr rfl
  | prime hp => exact .inl hp

/--
lemma `expChar_pos` / 引理 `expChar_pos`

English:
lemma expChar_pos
  given: (q : Nat) [ExpChar R q]
  statement: 0 < q
  proof: by
  rcases expChar_is_prime_or_one R q with h | rfl
  exacts [Nat.Prime.pos h, Nat.one_pos]

中文:
引理 expChar_pos
  条件: (q : 自然数) [ExpChar R q]
  结论: 0 < q
  证明: by
  rcases expChar_is_prime_or_one R q with h | rfl
  exacts [Nat.Prime.pos h, Nat.one_pos]

Depends on / 依赖: Nat.Prime.pos, Nat.one_pos, exacts, expChar_is_prime_or_one, one_pos
-/
lemma expChar_pos (q : Nat) [ExpChar R q] : 0 < q := by
  rcases expChar_is_prime_or_one R q with h | rfl
  exacts [Nat.Prime.pos h, Nat.one_pos]

/--
lemma `expChar_pow_pos` / 引理 `expChar_pow_pos`

English:
lemma expChar_pow_pos
  given: (q : Nat) [ExpChar R q] (n : Nat)
  statement: 0 < q ^ n
  proof: Nat.pow_pos (expChar_pos R q)

中文:
引理 expChar_pow_pos
  条件: (q : 自然数) [ExpChar R q] (n : 自然数)
  结论: 0 < q ^ n
  证明: Nat.pow_pos (expChar_pos R q)

Depends on / 依赖: Nat.pow_pos, expChar_pos, pow_pos
-/
lemma expChar_pow_pos (q : Nat) [ExpChar R q] (n : Nat) : 0 < q ^ n :=
  Nat.pow_pos (expChar_pos R q)

end AddMonoidWithOne

section NonAssocSemiring
variable [NonAssocSemiring R]

/--
Definition of `ringExpChar` / `ringExpChar` 的定义

English:
definition ringExpChar
  signature: : Nat
  body: max (ringChar R) 1

中文:
定义 ringExpChar
  签名: : 自然数
  定义体: max (ringChar R) 1

Depends on / 依赖: ringChar
-/
noncomputable def ringExpChar : Nat := max (ringChar R) 1

/--
lemma `ringExpChar.eq` / 引理 `ringExpChar.eq`

English:
lemma ringExpChar.eq
  given: (q : Nat) [h : ExpChar R q]
  statement: ringExpChar R = q
  proof: by
  rcases h with _ | h
  · have := CharP.ofCharZero R
    rw [ringExpChar]; rw [ringChar.eq R 0]; rfl
  rw [ringExpChar]; rw [ringChar.eq R q]
  exact Nat.max_eq_left h.one_lt.le

中文:
引理 ringExpChar.eq
  条件: (q : 自然数) [h : ExpChar R q]
  结论: ringExpChar R = q
  证明: by
  rcases h with _ | h
  · have := CharP.ofCharZero R
    rw [ringExpChar]; rw [ringChar.eq R 0]; rfl
  rw [ringExpChar]; rw [ringChar.eq R q]
  exact Nat.max_eq_left h.one_lt.le

Depends on / 依赖: CharP.ofCharZero, Nat.max_eq_left, h.one_lt.le, max_eq_left, ofCharZero, one_lt, ringChar, ringChar.eq, ringExpChar
-/
lemma ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar R = q := by
  rcases h with _ | h
  · have := CharP.ofCharZero R
    rw [ringExpChar]; rw [ringChar.eq R 0]; rfl
  rw [ringExpChar]; rw [ringChar.eq R q]
  exact Nat.max_eq_left h.one_lt.le

/--
lemma `ringExpChar.eq_one` / 引理 `ringExpChar.eq_one`

English:
lemma ringExpChar.eq_one
  given: [CharZero R]
  statement: ringExpChar R = 1
  proof: by
  rw [ringExpChar]; rw [ringChar.eq_zero]; rw [max_eq_right (Nat.zero_le _)]

中文:
引理 ringExpChar.eq_one
  条件: [特征零 R]
  结论: ringExpChar R = 1
  证明: by
  rw [ringExpChar]; rw [ringChar.eq_zero]; rw [max_eq_right (Nat.zero_le _)]
-/
@[simp] lemma ringExpChar.eq_one [CharZero R] : ringExpChar R = 1 := by
  rw [ringExpChar]; rw [ringChar.eq_zero]; rw [max_eq_right (Nat.zero_le _)]

section Nontrivial
variable [Nontrivial R]

/--
lemma `char_zero_of_expChar_one` / 引理 `char_zero_of_expChar_one`

English:
lemma char_zero_of_expChar_one
  given: (p : Nat) [hp : CharP R p] [hq : ExpChar R 1]
  statement: p = 0
  proof: by
  cases hq
  · exact CharP.eq R hp (.ofCharZero R)
  · exact False.elim (CharP.char_ne_one R 1 rfl)

中文:
引理 char_zero_of_expChar_one
  条件: (p : 自然数) [hp : 特征p R p] [hq : ExpChar R 1]
  结论: p = 0
  证明: by
  cases hq
  · exact CharP.eq R hp (.ofCharZero R)
  · exact False.elim (CharP.char_ne_one R 1 rfl)

Depends on / 依赖: CharP.char_ne_one, CharP.eq, False.elim, char_ne_one, ofCharZero
-/
lemma char_zero_of_expChar_one (p : Nat) [hp : CharP R p] [hq : ExpChar R 1] : p = 0 := by
  cases hq
  · exact CharP.eq R hp (.ofCharZero R)
  · exact False.elim (CharP.char_ne_one R 1 rfl)

-- This could be an instance, but there are no `ExpChar R 1` instances in mathlib.
/--
lemma `charZero_of_expChar_one'` / 引理 `charZero_of_expChar_one'`

English:
lemma charZero_of_expChar_one'
  given: [hq : ExpChar R 1]
  statement: CharZero R
  proof: by
  cases hq
  · assumption
  · exact False.elim (CharP.char_ne_one R 1 rfl)

中文:
引理 charZero_of_expChar_one'
  条件: [hq : ExpChar R 1]
  结论: 特征零 R
  证明: by
  cases hq
  · assumption
  · exact False.elim (CharP.char_ne_one R 1 rfl)

Depends on / 依赖: CharP.char_ne_one, False.elim, char_ne_one
-/
lemma charZero_of_expChar_one' [hq : ExpChar R 1] : CharZero R := by
  cases hq
  · assumption
  · exact False.elim (CharP.char_ne_one R 1 rfl)

/--
lemma `expChar_one_iff_char_zero` / 引理 `expChar_one_iff_char_zero`

English:
lemma expChar_one_iff_char_zero
  given: (p q : Nat) [CharP R p] [ExpChar R q]
  statement: q = 1 ↔ p = 0
  proof: by
  constructor
  · rintro rfl
    exact char_zero_of_expChar_one R p
  · rintro rfl
    exact expChar_one_of_char_zero R q

中文:
引理 expChar_one_iff_char_zero
  条件: (p q : 自然数) [特征p R p] [ExpChar R q]
  结论: q = 1 ↔ p = 0
  证明: by
  constructor
  · rintro rfl
    exact char_zero_of_expChar_one R p
  · rintro rfl
    exact expChar_one_of_char_zero R q

Depends on / 依赖: char_zero_of_expChar_one, expChar_one_of_char_zero
-/
lemma expChar_one_iff_char_zero (p q : Nat) [CharP R p] [ExpChar R q] : q = 1 ↔ p = 0 := by
  constructor
  · rintro rfl
    exact char_zero_of_expChar_one R p
  · rintro rfl
    exact expChar_one_of_char_zero R q

end Nontrivial
end NonAssocSemiring

/--
lemma `ExpChar.exists` / 引理 `ExpChar.exists`

English:
lemma ExpChar.exists
  given: [Ring R] [IsDomain R]
  statement: exists q, ExpChar R q
  proof: by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' R
  exacts [⟨1, .zero⟩, ⟨p, .prime hp⟩]

中文:
引理 ExpChar.存在
  条件: [环 R] [是整环 R]
  结论: 存在 q, ExpChar R q
  证明: by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' R
  exacts [⟨1, .zero⟩, ⟨p, .prime hp⟩]

Depends on / 依赖: CharP.exists, exacts
-/
lemma ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar R q := by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' R
  exacts [⟨1, .zero⟩, ⟨p, .prime hp⟩]

/--
lemma `ExpChar.exists_unique` / 引理 `ExpChar.exists_unique`

English:
lemma ExpChar.exists_unique
  given: [Ring R] [IsDomain R]
  statement: exists! q, ExpChar R q
  proof: let ⟨q, H⟩ := ExpChar.exists R
  ⟨q, H, fun _ H2 => ExpChar.eq H2 H⟩

中文:
引理 ExpChar.存在_unique
  条件: [环 R] [是整环 R]
  结论: 存在! q, ExpChar R q
  证明: let ⟨q, H⟩ := ExpChar.exists R
  ⟨q, H, fun _ H2 => ExpChar.eq H2 H⟩

Depends on / 依赖: ExpChar, ExpChar.eq, ExpChar.exists
-/
lemma ExpChar.exists_unique [Ring R] [IsDomain R] : exists! q, ExpChar R q :=
  let ⟨q, H⟩ := ExpChar.exists R
  ⟨q, H, fun _ H2 => ExpChar.eq H2 H⟩

/--
Instance `ringExpChar.expChar` / 实例 `ringExpChar.expChar`

English:
instance ringExpChar.expChar
  signature: [Ring R] [IsDomain R]
  body: by
  obtain ⟨q, _⟩ := ExpChar.exists R
  rwa [ringExpChar.eq R q]

中文:
实例 ringExpChar.expChar
  签名: [环 R] [是整环 R]
  定义体: by
  obtain ⟨q, _⟩ := ExpChar.exists R
  rwa [ringExpChar.eq R q]

Depends on / 依赖: ExpChar, ExpChar.exists, ringExpChar, ringExpChar.eq
-/
instance ringExpChar.expChar [Ring R] [IsDomain R] : ExpChar R (ringExpChar R) := by
  obtain ⟨q, _⟩ := ExpChar.exists R
  rwa [ringExpChar.eq R q]

variable {R} in
/--
lemma `ringExpChar.of_eq` / 引理 `ringExpChar.of_eq`

English:
lemma ringExpChar.of_eq
  given: [Ring R] [IsDomain R] {q : Nat} (h : ringExpChar R = q)
  statement: ExpChar R q
  proof: h ▸ ringExpChar.expChar R

中文:
引理 ringExpChar.of_eq
  条件: [环 R] [是整环 R] {q : 自然数} (h : ringExpChar R = q)
  结论: ExpChar R q
  证明: h ▸ ringExpChar.expChar R

Depends on / 依赖: expChar, ringExpChar, ringExpChar.expChar
-/
lemma ringExpChar.of_eq [Ring R] [IsDomain R] {q : Nat} (h : ringExpChar R = q) : ExpChar R q :=
  h ▸ ringExpChar.expChar R

variable {R} in
/--
lemma `ringExpChar.eq_iff` / 引理 `ringExpChar.eq_iff`

English:
lemma ringExpChar.eq_iff
  given: [Ring R] [IsDomain R] {q : Nat}
  statement: ringExpChar R = q ↔ ExpChar R q
  proof: ⟨ringExpChar.of_eq, fun _ => ringExpChar.eq R q⟩

中文:
引理 ringExpChar.eq_iff
  条件: [环 R] [是整环 R] {q : 自然数}
  结论: ringExpChar R = q ↔ ExpChar R q
  证明: ⟨ringExpChar.of_eq, fun _ => ringExpChar.eq R q⟩

Depends on / 依赖: of_eq, ringExpChar, ringExpChar.eq, ringExpChar.of_eq
-/
lemma ringExpChar.eq_iff [Ring R] [IsDomain R] {q : Nat} : ringExpChar R = q ↔ ExpChar R q :=
  ⟨ringExpChar.of_eq, fun _ => ringExpChar.eq R q⟩
