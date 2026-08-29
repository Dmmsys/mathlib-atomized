/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Int.Init
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.OfNat

/-!
# Basic operations on the integers

This file builds on `Data.Int.Init` by adding basic lemmas on integers.
depending on Mathlib definitions.
-/

public section

open Nat

namespace Int
variable {a b c d m n : Int}

attribute [gcongr] ofNat_le

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: : Nontrivial Int
  body: ⟨⟨0, 1, Int.zero_ne_one⟩⟩

中文:
实例 instNontrivial
  签名: : 非平凡 整数
  定义体: ⟨⟨0, 1, Int.zero_ne_one⟩⟩

Depends on / 依赖: Int.zero_ne_one, zero_ne_one
-/
instance instNontrivial : Nontrivial Int := ⟨⟨0, 1, Int.zero_ne_one⟩⟩

/--
lemma `ofNat_injective` / 引理 `ofNat_injective`

English:
lemma ofNat_injective
  statement: Function.Injective ofNat
  proof: @Int.ofNat.inj

中文:
引理 of自然数_injective
  结论: 函数.单射 of自然数
  证明: @Int.ofNat.inj
-/
@[simp] lemma ofNat_injective : Function.Injective ofNat := @Int.ofNat.inj

section strongRec

variable {P : Int -> Sort*} {lt : forall n < m, P n} {ge : forall n >= m, (forall k < n, P k) -> P n}

/--
lemma `strongRec_of_ge` / 引理 `strongRec_of_ge`

English:
lemma strongRec_of_ge
  proof: by
  refine m.strongRec (fun n hnm hmn => (Int.not_lt.mpr hmn hnm).elim) (fun n _ ih hn => ?_) n
  rw [Int.strongRec]; rw [dif_neg (Int.not_lt.mpr hn)]
  congr; revert ih
  refine n.inductionOn' m (fun _ => ?_) (fun k hmk ih' ih => ?_) (fun k hkm ih' _ => ?_) <;> ext l hl
  · rw [inductionOn'_self, 

中文:
引理 strongRec_of_ge
  证明: by
  refine m.strongRec (fun n hnm hmn => (Int.not_lt.mpr hmn hnm).elim) (fun n _ ih hn => ?_) n
  rw [Int.strongRec]; rw [dif_neg (Int.not_lt.mpr hn)]
  congr; revert ih
  refine n.inductionOn' m (fun _ => ?_) (fun k hmk ih' ih => ?_) (fun k hkm ih' _ => ?_) <;> ext l hl
  · rw [inductionOn'_self, 

Depends on / 依赖: Int.lt_trans, Int.not_lt.mpr, Int.strongRec, _add_one, _self, _sub_one, dif_neg, inductionOn, k.lt_succ, lt_succ, lt_trans, m.strongRec, n.inductionOn, not_lt, revert, split_ifs, strongRec, strongRec_of_lt
-/
lemma strongRec_of_ge :
    forall hn : m <= n, m.strongRec lt ge n = ge n hn fun k _ => m.strongRec lt ge k := by
  refine m.strongRec (fun n hnm hmn => (Int.not_lt.mpr hmn hnm).elim) (fun n _ ih hn => ?_) n
  rw [Int.strongRec]; rw [dif_neg (Int.not_lt.mpr hn)]
  congr; revert ih
  refine n.inductionOn' m (fun _ => ?_) (fun k hmk ih' ih => ?_) (fun k hkm ih' _ => ?_) <;> ext l hl
  · rw [inductionOn'_self, strongRec_of_lt hl]
  · rw [inductionOn'_add_one hmk]; split_ifs with hlm
    · rw [strongRec_of_lt hlm]
    · rw [ih' fun l hl => ih l (Int.lt_trans hl k.lt_succ), ih _ hl]
  · rw [inductionOn'_sub_one hkm, ih']
    exact fun l hlk hml => (Int.not_lt.mpr hkm <| Int.lt_of_le_of_lt hml hlk).elim

end strongRec


/--
lemma `natAbs_surjective` / 引理 `natAbs_surjective`

English:
lemma natAbs_surjective
  statement: natAbs.Surjective
  proof: fun n => ⟨n, natAbs_natCast n⟩

中文:
引理 natAbs_surjective
  结论: natAbs.满射
  证明: fun n => ⟨n, natAbs_natCast n⟩

Depends on / 依赖: natAbs_natCast
-/
lemma natAbs_surjective : natAbs.Surjective := fun n => ⟨n, natAbs_natCast n⟩

/--
lemma `pow_right_injective` / 引理 `pow_right_injective`

English:
lemma pow_right_injective
  given: (h : 1 < a.natAbs)
  statement: ((a ^ ·) : Nat -> Int).Injective
  proof: by
  refine (?_ : (natAbs ∘ (a ^ · : Nat -> Int)).Injective).of_comp
  convert! Nat.pow_right_injective h using 2
  rw [Function.comp_apply]; rw [natAbs_pow]

中文:
引理 pow_right_injective
  条件: (h : 1 < a.natAbs)
  结论: ((a ^ ·) : 自然数 -> 整数).单射
  证明: by
  refine (?_ : (natAbs ∘ (a ^ · : Nat -> Int)).Injective).of_comp
  convert! Nat.pow_right_injective h using 2
  rw [Function.comp_apply]; rw [natAbs_pow]

Depends on / 依赖: Function, Function.comp_apply, Injective, Nat.pow_right_injective, comp_apply, convert, natAbs, natAbs_pow, of_comp, pow_right_injective
-/
lemma pow_right_injective (h : 1 < a.natAbs) : ((a ^ ·) : Nat -> Int).Injective := by
  refine (?_ : (natAbs ∘ (a ^ · : Nat -> Int)).Injective).of_comp
  convert! Nat.pow_right_injective h using 2
  rw [Function.comp_apply]; rw [natAbs_pow]


/--
theorem `ofNat_dvd_natCast` / 定理 `ofNat_dvd_natCast`

English:
theorem ofNat_dvd_natCast
  given: {x y : Nat}
  statement: (ofNat(x) : Int) ∣ (y : Int) ↔ OfNat.ofNat x ∣ y
  proof: natCast_dvd_natCast

中文:
定理 of自然数_dvd_natCast
  条件: {x y : 自然数}
  结论: (of自然数(x) : 整数) ∣ (y : 整数) ↔ Of自然数.of自然数 x ∣ y
  证明: natCast_dvd_natCast
-/
@[norm_cast] theorem ofNat_dvd_natCast {x y : Nat} : (ofNat(x) : Int) ∣ (y : Int) ↔ OfNat.ofNat x ∣ y :=
  natCast_dvd_natCast

/--
theorem `natCast_dvd_ofNat` / 定理 `natCast_dvd_ofNat`

English:
theorem natCast_dvd_ofNat
  given: {x y : Nat}
  statement: (x : Int) ∣ (ofNat(y) : Int) ↔ x ∣ OfNat.ofNat y
  proof: natCast_dvd_natCast

中文:
定理 natCast_dvd_of自然数
  条件: {x y : 自然数}
  结论: (x : 整数) ∣ (of自然数(y) : 整数) ↔ x ∣ Of自然数.of自然数 y
  证明: natCast_dvd_natCast
-/
@[norm_cast] theorem natCast_dvd_ofNat {x y : Nat} : (x : Int) ∣ (ofNat(y) : Int) ↔ x ∣ OfNat.ofNat y :=
  natCast_dvd_natCast

/--
lemma `natCast_dvd` / 引理 `natCast_dvd`

English:
lemma natCast_dvd
  given: {m : Nat}
  statement: (m : Int) ∣ n ↔ m ∣ n.natAbs
  proof: by
  obtain hn | hn := natAbs_eq n <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.dvd_neg]

中文:
引理 natCast_dvd
  条件: {m : 自然数}
  结论: (m : 整数) ∣ n ↔ m ∣ n.natAbs
  证明: by
  obtain hn | hn := natAbs_eq n <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.dvd_neg]

Depends on / 依赖: Int.dvd_neg, dvd_neg, natAbs_eq, natCast_dvd_natCast
-/
lemma natCast_dvd {m : Nat} : (m : Int) ∣ n ↔ m ∣ n.natAbs := by
  obtain hn | hn := natAbs_eq n <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.dvd_neg]

/--
lemma `dvd_natCast` / 引理 `dvd_natCast`

English:
lemma dvd_natCast
  given: {n : Nat}
  statement: m ∣ (n : Int) ↔ m.natAbs ∣ n
  proof: by
  obtain hn | hn := natAbs_eq m <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.neg_dvd]

中文:
引理 dvd_natCast
  条件: {n : 自然数}
  结论: m ∣ (n : 整数) ↔ m.natAbs ∣ n
  证明: by
  obtain hn | hn := natAbs_eq m <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.neg_dvd]

Depends on / 依赖: Int.neg_dvd, Subsingleton, Subsingleton.elim, eq_univ_of_forall, natAbs_eq, natCast_dvd_natCast, neg_dvd
-/
lemma dvd_natCast {n : Nat} : m ∣ (n : Int) ↔ m.natAbs ∣ n := by
  obtain hn | hn := natAbs_eq m <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.neg_dvd]

/--
lemma `eq_zero_of_dvd_of_nonneg_of_lt` / 引理 `eq_zero_of_dvd_of_nonneg_of_lt`

English:
lemma eq_zero_of_dvd_of_nonneg_of_lt
  given: (hm : 0 <= m) (hmn : m < n) (hnm : n ∣ m)
  statement: m = 0
  proof: eq_zero_of_dvd_of_natAbs_lt_natAbs hnm (natAbs_lt_natAbs_of_nonneg_of_lt hm hmn)

中文:
引理 eq_zero_of_dvd_of_nonneg_of_lt
  条件: (hm : 0 <= m) (hmn : m < n) (hnm : n ∣ m)
  结论: m = 0
  证明: eq_zero_of_dvd_of_natAbs_lt_natAbs hnm (natAbs_lt_natAbs_of_nonneg_of_lt hm hmn)

Depends on / 依赖: eq_zero_of_dvd_of_natAbs_lt_natAbs, natAbs_lt_natAbs_of_nonneg_of_lt
-/
lemma eq_zero_of_dvd_of_nonneg_of_lt (hm : 0 <= m) (hmn : m < n) (hnm : n ∣ m) : m = 0 :=
  eq_zero_of_dvd_of_natAbs_lt_natAbs hnm (natAbs_lt_natAbs_of_nonneg_of_lt hm hmn)

/--
lemma `eq_of_mod_eq_of_natAbs_sub_lt_natAbs` / 引理 `eq_of_mod_eq_of_natAbs_sub_lt_natAbs`

English:
lemma eq_of_mod_eq_of_natAbs_sub_lt_natAbs
  statement: {a b c : Int} (h1 : a % b = c)
  proof: Int.eq_of_sub_eq_zero (eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_self_sub_of_emod_eq h1) h2)

中文:
引理 eq_of_mod_eq_of_natAbs_sub_lt_natAbs
  结论: {a b c : 整数} (h1 : a % b = c)
  证明: Int.eq_of_sub_eq_zero (eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_self_sub_of_emod_eq h1) h2)

Depends on / 依赖: Int.eq_of_sub_eq_zero, dvd_self_sub_of_emod_eq, eq_of_sub_eq_zero, eq_zero_of_dvd_of_natAbs_lt_natAbs
-/
lemma eq_of_mod_eq_of_natAbs_sub_lt_natAbs {a b c : Int} (h1 : a % b = c)
    (h2 : natAbs (a - c) < natAbs b) : a = c :=
  Int.eq_of_sub_eq_zero (eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_self_sub_of_emod_eq h1) h2)

/--
lemma `natAbs_le_of_dvd_ne_zero` / 引理 `natAbs_le_of_dvd_ne_zero`

English:
lemma natAbs_le_of_dvd_ne_zero
  given: (hmn : m ∣ n) (hn : n != 0)
  statement: natAbs m <= natAbs n
  proof: not_lt.mp (mt (eq_zero_of_dvd_of_natAbs_lt_natAbs hmn) hn)

中文:
引理 natAbs_le_of_dvd_ne_zero
  条件: (hmn : m ∣ n) (hn : n != 0)
  结论: natAbs m <= natAbs n
  证明: not_lt.mp (mt (eq_zero_of_dvd_of_natAbs_lt_natAbs hmn) hn)

Depends on / 依赖: eq_zero_of_dvd_of_natAbs_lt_natAbs, not_lt, not_lt.mp
-/
lemma natAbs_le_of_dvd_ne_zero (hmn : m ∣ n) (hn : n != 0) : natAbs m <= natAbs n :=
  not_lt.mp (mt (eq_zero_of_dvd_of_natAbs_lt_natAbs hmn) hn)

/--
theorem `gcd_emod` / 定理 `gcd_emod`

English:
theorem gcd_emod
  given: (m n : Int)
  statement: (m % n).gcd n = m.gcd n
  proof: by
  conv_rhs => rw [← m.emod_add_mul_ediv n, gcd_add_mul_left_left]

中文:
定理 gcd_emod
  条件: (m n : 整数)
  结论: (m % n).最大公约数 n = m.最大公约数 n
  证明: by
  conv_rhs => rw [← m.emod_add_mul_ediv n, gcd_add_mul_left_left]

Depends on / 依赖: conv_rhs, emod_add_mul_ediv, gcd_add_mul_left_left, m.emod_add_mul_ediv
-/
theorem gcd_emod (m n : Int) : (m % n).gcd n = m.gcd n := by
  conv_rhs => rw [← m.emod_add_mul_ediv n, gcd_add_mul_left_left]

end Int
