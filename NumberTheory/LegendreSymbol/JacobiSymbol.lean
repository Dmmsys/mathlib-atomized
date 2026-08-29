/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Thomas Zhu, Mario Carneiro
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# The Jacobi Symbol

We define the Jacobi symbol and prove its main properties.

## Main definitions

We define the Jacobi symbol, `jacobiSym a b`, for integers `a` and natural numbers `b`
as the product over the prime factors `p` of `b` of the Legendre symbols `legendreSym p a`.
This agrees with the mathematical definition when `b` is odd.

The prime factors are obtained via `Nat.factors`. Since `Nat.factors 0 = []`,
this implies in particular that `jacobiSym a 0 = 1` for all `a`.

## Main statements

We prove the main properties of the Jacobi symbol, including the following.

* Multiplicativity in both arguments (`jacobiSym.mul_left`, `jacobiSym.mul_right`)

* The value of the symbol is `1` or `-1` when the arguments are coprime
  (`jacobiSym.eq_one_or_neg_one`)

* The symbol vanishes if and only if `b ≠ 0` and the arguments are not coprime
  (`jacobiSym.eq_zero_iff_not_coprime`)

* If the symbol has the value `-1`, then `a : ZMod b` is not a square
  (`ZMod.nonsquare_of_jacobiSym_eq_neg_one`); the converse holds when `b = p` is a prime
  (`ZMod.nonsquare_iff_jacobiSym_eq_neg_one`); in particular, in this case `a` is a
  square mod `p` when the symbol has the value `1` (`ZMod.isSquare_of_jacobiSym_eq_one`).

* Quadratic reciprocity (`jacobiSym.quadratic_reciprocity`,
  `jacobiSym.quadratic_reciprocity_one_mod_four`,
  `jacobiSym.quadratic_reciprocity_three_mod_four`)

* The supplementary laws for `a = -1`, `a = 2`, `a = -2` (`jacobiSym.at_neg_one`,
  `jacobiSym.at_two`, `jacobiSym.at_neg_two`)

* The symbol depends on `a` only via its residue class mod `b` (`jacobiSym.mod_left`)
  and on `b` only via its residue class mod `4*a` (`jacobiSym.mod_right`)

* A `csimp` rule for `jacobiSym` and `legendreSym` that evaluates `J(a | b)` efficiently by
  reducing to the case `0 ≤ a < b` and `a`, `b` odd, and then swaps `a`, `b` and recurses using
  quadratic reciprocity.

## Notation

We define the notation `J(a | b)` for `jacobiSym a b`, localized to `NumberTheorySymbols`.

## Tags
Jacobi symbol, quadratic reciprocity
-/

@[expose] public section


section Jacobi

/-!
### Definition of the Jacobi symbol

We define the Jacobi symbol $\Bigl(\frac{a}{b}\Bigr)$ for integers `a` and natural numbers `b`
as the product of the Legendre symbols $\Bigl(\frac{a}{p}\Bigr)$, where `p` runs through the
prime divisors (with multiplicity) of `b`, as provided by `b.factors`. This agrees with the
Jacobi symbol when `b` is odd and gives less meaningful values when it is not (e.g., the symbol
is `1` when `b = 0`). This is called `jacobiSym a b`.

We define localized notation (scope `NumberTheorySymbols`) `J(a | b)` for the Jacobi
symbol `jacobiSym a b`.
-/


open Nat ZMod

-- Since we need the fact that the factors are prime, we use `List.pmap`.
/--
Definition of `jacobiSym` / `jacobiSym` 的定义

English:
definition jacobiSym
  signature: (a : Int) (b : Nat)
  body: (b.primeFactorsList.pmap (fun p pp => @legendreSym p ⟨pp⟩ a) fun _ pf =>
    prime_of_mem_primeFactorsList pf).prod

中文:
定义 jacobiSym
  签名: (a : 整数) (b : 自然数)
  定义体: (b.primeFactorsList.pmap (fun p pp => @legendreSym p ⟨pp⟩ a) fun _ pf =>
    prime_of_mem_primeFactorsList pf).prod

Depends on / 依赖: b.primeFactorsList.pmap, legendreSym, primeFactorsList, prime_of_mem_primeFactorsList
-/
def jacobiSym (a : Int) (b : Nat) : Int :=
  (b.primeFactorsList.pmap (fun p pp => @legendreSym p ⟨pp⟩ a) fun _ pf =>
    prime_of_mem_primeFactorsList pf).prod

-- Notation for the Jacobi symbol.
@[inherit_doc]
scoped[NumberTheorySymbols] notation "J(" a " | " b ")" => jacobiSym a b

open NumberTheorySymbols

/-!
### Properties of the Jacobi symbol
-/


namespace jacobiSym

/-- The symbol `J(a | 0)` has the value `1`. -/
@[simp]
/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  given: (a : Int)
  statement: J(a | 0) = 1
  proof: by
  simp only [jacobiSym, primeFactorsList_zero, List.prod_nil, List.pmap]

中文:
定理 zero_right
  条件: (a : 整数)
  结论: J(a | 0) = 1
  证明: by
  simp only [jacobiSym, primeFactorsList_zero, List.prod_nil, List.pmap]

Depends on / 依赖: List.pmap, List.prod_nil, jacobiSym, primeFactorsList_zero, prod_nil
-/
theorem zero_right (a : Int) : J(a | 0) = 1 := by
  simp only [jacobiSym, primeFactorsList_zero, List.prod_nil, List.pmap]

/-- The symbol `J(a | 1)` has the value `1`. -/
@[simp]
/--
theorem `one_right` / 定理 `one_right`

English:
theorem one_right
  given: (a : Int)
  statement: J(a | 1) = 1
  proof: by
  simp only [jacobiSym, primeFactorsList_one, List.prod_nil, List.pmap]

中文:
定理 one_right
  条件: (a : 整数)
  结论: J(a | 1) = 1
  证明: by
  simp only [jacobiSym, primeFactorsList_one, List.prod_nil, List.pmap]

Depends on / 依赖: List.pmap, List.prod_nil, jacobiSym, primeFactorsList_one, prod_nil
-/
theorem one_right (a : Int) : J(a | 1) = 1 := by
  simp only [jacobiSym, primeFactorsList_one, List.prod_nil, List.pmap]

/--
theorem `legendreSym.to_jacobiSym` / 定理 `legendreSym.to_jacobiSym`

English:
theorem legendreSym.to_jacobiSym
  given: (p : Nat) [fp : Fact p.Prime] (a : Int)
  proof: by
  simp only [jacobiSym, primeFactorsList_prime fp.1, List.prod_cons, List.prod_nil, mul_one,
    List.pmap]

中文:
定理 legendreSym.to_jacobiSym
  条件: (p : 自然数) [fp : Fact p.Prime] (a : 整数)
  证明: by
  simp only [jacobiSym, primeFactorsList_prime fp.1, List.prod_cons, List.prod_nil, mul_one,
    List.pmap]

Depends on / 依赖: List.pmap, List.prod_cons, List.prod_nil, jacobiSym, mul_one, primeFactorsList_prime, prod_cons, prod_nil
-/
theorem legendreSym.to_jacobiSym (p : Nat) [fp : Fact p.Prime] (a : Int) :
    legendreSym p a = J(a | p) := by
  simp only [jacobiSym, primeFactorsList_prime fp.1, List.prod_cons, List.prod_nil, mul_one,
    List.pmap]

/--
theorem `mul_right'` / 定理 `mul_right'`

English:
theorem mul_right'
  given: (a : Int) {b₁ b₂ : Nat} (hb₁ : b₁ != 0) (hb₂ : b₂ != 0)
  proof: by
  rw [jacobiSym]; rw [((perm_primeFactorsList_mul hb₁ hb₂).pmap _).prod_eq]; rw [List.pmap_append]; rw [List.prod_append]
  pick_goal 2
  · exact fun p hp =>
      (List.mem_append.mp hp).elim prime_of_mem_primeFactorsList prime_of_mem_primeFactorsList
  · rfl

中文:
定理 mul_right'
  条件: (a : 整数) {b₁ b₂ : 自然数} (hb₁ : b₁ != 0) (hb₂ : b₂ != 0)
  证明: by
  rw [jacobiSym]; rw [((perm_primeFactorsList_mul hb₁ hb₂).pmap _).prod_eq]; rw [List.pmap_append]; rw [List.prod_append]
  pick_goal 2
  · exact fun p hp =>
      (List.mem_append.mp hp).elim prime_of_mem_primeFactorsList prime_of_mem_primeFactorsList
  · rfl

Depends on / 依赖: List.mem_append.mp, List.pmap_append, List.prod_append, jacobiSym, mem_append, perm_primeFactorsList_mul, pick_goal, pmap_append, prime_of_mem_primeFactorsList, prod_append, prod_eq
-/
theorem mul_right' (a : Int) {b₁ b₂ : Nat} (hb₁ : b₁ != 0) (hb₂ : b₂ != 0) :
    J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) := by
  rw [jacobiSym]; rw [((perm_primeFactorsList_mul hb₁ hb₂).pmap _).prod_eq]; rw [List.pmap_append]; rw [List.prod_append]
  pick_goal 2
  · exact fun p hp =>
      (List.mem_append.mp hp).elim prime_of_mem_primeFactorsList prime_of_mem_primeFactorsList
  · rfl

/--
theorem `mul_right` / 定理 `mul_right`

English:
theorem mul_right
  given: (a : Int) (b₁ b₂ : Nat) [NeZero b₁] [NeZero b₂]
  proof: mul_right' a (NeZero.ne b₁) (NeZero.ne b₂)

中文:
定理 mul_right
  条件: (a : 整数) (b₁ b₂ : 自然数) [NeZero b₁] [NeZero b₂]
  证明: mul_right' a (NeZero.ne b₁) (NeZero.ne b₂)

Depends on / 依赖: NeZero, NeZero.ne, mul_right
-/
theorem mul_right (a : Int) (b₁ b₂ : Nat) [NeZero b₁] [NeZero b₂] :
    J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) :=
  mul_right' a (NeZero.ne b₁) (NeZero.ne b₂)

/--
theorem `trichotomy` / 定理 `trichotomy`

English:
theorem trichotomy
  given: (a : Int) (b : Nat)
  statement: J(a | b) = 0 ∨ J(a | b) = 1 ∨ J(a | b) = -1
  proof: ((MonoidHom.mrange (@SignType.castHom Int _ _).toMonoidHom).copy {0, 1, -1} <| by
    rw [Set.pair_comm]
    exact (SignType.range_eq SignType.castHom).symm).list_prod_mem
      (by
        intro _ ha'
        rcases List.mem_pmap.mp ha' with ⟨p, hp, rfl⟩
        have : Fact p.Prime := ⟨prime_of_mem

中文:
定理 trichotomy
  条件: (a : 整数) (b : 自然数)
  结论: J(a | b) = 0 ∨ J(a | b) = 1 ∨ J(a | b) = -1
  证明: ((MonoidHom.mrange (@SignType.castHom Int _ _).toMonoidHom).copy {0, 1, -1} <| by
    rw [Set.pair_comm]
    exact (SignType.range_eq SignType.castHom).symm).list_prod_mem
      (by
        intro _ ha'
        rcases List.mem_pmap.mp ha' with ⟨p, hp, rfl⟩
        have : Fact p.Prime := ⟨prime_of_mem

Depends on / 依赖: List.mem_pmap.mp, MonoidHom, MonoidHom.mrange, Set.pair_comm, SignType, SignType.castHom, SignType.range_eq, castHom, list_prod_mem, mem_pmap, mrange, p.Prime, pair_comm, prime_of_mem_primeFactorsList, quadraticChar_isQuadratic, range_eq, toMonoidHom
-/
theorem trichotomy (a : Int) (b : Nat) : J(a | b) = 0 ∨ J(a | b) = 1 ∨ J(a | b) = -1 :=
  ((MonoidHom.mrange (@SignType.castHom Int _ _).toMonoidHom).copy {0, 1, -1} <| by
    rw [Set.pair_comm]
    exact (SignType.range_eq SignType.castHom).symm).list_prod_mem
      (by
        intro _ ha'
        rcases List.mem_pmap.mp ha' with ⟨p, hp, rfl⟩
        have : Fact p.Prime := ⟨prime_of_mem_primeFactorsList hp⟩
        exact quadraticChar_isQuadratic (ZMod p) a)

/-- The symbol `J(1 | b)` has the value `1`. -/
@[simp]
/--
theorem `one_left` / 定理 `one_left`

English:
theorem one_left
  given: (b : Nat)
  statement: J(1 | b) = 1
  proof: List.prod_eq_one fun z hz => by
    let ⟨p, hp, he⟩ := List.mem_pmap.1 hz
    rw [← he]; rw [legendreSym.at_one]

中文:
定理 one_left
  条件: (b : 自然数)
  结论: J(1 | b) = 1
  证明: List.prod_eq_one fun z hz => by
    let ⟨p, hp, he⟩ := List.mem_pmap.1 hz
    rw [← he]; rw [legendreSym.at_one]

Depends on / 依赖: List.mem_pmap, List.prod_eq_one, at_one, legendreSym, legendreSym.at_one, mem_pmap, prod_eq_one
-/
theorem one_left (b : Nat) : J(1 | b) = 1 :=
  List.prod_eq_one fun z hz => by
    let ⟨p, hp, he⟩ := List.mem_pmap.1 hz
    rw [← he]; rw [legendreSym.at_one]

/--
theorem `mul_left` / 定理 `mul_left`

English:
theorem mul_left
  given: (a₁ a₂ : Int) (b : Nat)
  statement: J(a₁ * a₂ | b) = J(a₁ | b) * J(a₂ | b)
  proof: by
  simp_rw [jacobiSym, List.pmap_eq_map_attach, legendreSym.mul]
  exact List.prod_map_mul (l := (primeFactorsList b).attach)
    (f := fun x => @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₁)
    (g := fun x => @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₂)

中文:
定理 mul_left
  条件: (a₁ a₂ : 整数) (b : 自然数)
  结论: J(a₁ * a₂ | b) = J(a₁ | b) * J(a₂ | b)
  证明: by
  simp_rw [jacobiSym, List.pmap_eq_map_attach, legendreSym.mul]
  exact List.prod_map_mul (l := (primeFactorsList b).attach)
    (f := fun x => @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₁)
    (g := fun x => @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₂)

Depends on / 依赖: List.pmap_eq_map_attach, List.prod_map_mul, attach, jacobiSym, legendreSym, legendreSym.mul, pmap_eq_map_attach, primeFactorsList, prime_of_mem_primeFactorsList, prod_map_mul, simp_rw
-/
theorem mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = J(a₁ | b) * J(a₂ | b) := by
  simp_rw [jacobiSym, List.pmap_eq_map_attach, legendreSym.mul]
  exact List.prod_map_mul (l := (primeFactorsList b).attach)
    (f := fun x => @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₁)
    (g := fun x => @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₂)

/--
theorem `eq_zero_iff_not_coprime` / 定理 `eq_zero_iff_not_coprime`

English:
theorem eq_zero_iff_not_coprime
  given: {a : Int} {b : Nat} [NeZero b]
  statement: J(a | b) = 0 ↔ a.gcd b != 1
  proof: List.prod_eq_zero_iff.trans
    (by
      rw [List.mem_pmap]; rw [Int.gcd_eq_natAbs]; rw [Ne]; rw [Prime.not_coprime_iff_dvd]
      simp_rw [legendreSym.eq_zero_iff _ _, intCast_zmod_eq_zero_iff_dvd,
        mem_primeFactorsList (NeZero.ne b), ← Int.natCast_dvd, Int.natCast_dvd_natCast, exists_prop,

中文:
定理 eq_zero_iff_not_coprime
  条件: {a : 整数} {b : 自然数} [NeZero b]
  结论: J(a | b) = 0 ↔ a.gcd b != 1
  证明: List.prod_eq_zero_iff.trans
    (by
      rw [List.mem_pmap]; rw [Int.gcd_eq_natAbs]; rw [Ne]; rw [Prime.not_coprime_iff_dvd]
      simp_rw [legendreSym.eq_zero_iff _ _, intCast_zmod_eq_zero_iff_dvd,
        mem_primeFactorsList (NeZero.ne b), ← Int.natCast_dvd, Int.natCast_dvd_natCast, exists_prop,

Depends on / 依赖: Int.gcd_eq_natAbs, Int.natCast_dvd, Int.natCast_dvd_natCast, List.mem_pmap, List.prod_eq_zero_iff.trans, NeZero, NeZero.ne, Prime.not_coprime_iff_dvd, _root_, _root_.and_comm, and_assoc, and_comm, eq_zero_iff, exists_prop, gcd_eq_natAbs, intCast_zmod_eq_zero_iff_dvd, legendreSym, legendreSym.eq_zero_iff, mem_pmap, mem_primeFactorsList
-/
theorem eq_zero_iff_not_coprime {a : Int} {b : Nat} [NeZero b] : J(a | b) = 0 ↔ a.gcd b != 1 :=
  List.prod_eq_zero_iff.trans
    (by
      rw [List.mem_pmap]; rw [Int.gcd_eq_natAbs]; rw [Ne]; rw [Prime.not_coprime_iff_dvd]
      simp_rw [legendreSym.eq_zero_iff _ _, intCast_zmod_eq_zero_iff_dvd,
        mem_primeFactorsList (NeZero.ne b), ← Int.natCast_dvd, Int.natCast_dvd_natCast, exists_prop,
        and_assoc, _root_.and_comm])

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: {a : Int} {b : Nat} (h : a.gcd b = 1)
  statement: J(a | b) != 0
  proof: by
  rcases eq_zero_or_neZero b with hb | _
  · rw [hb, zero_right]
    exact one_ne_zero
  · contrapose! h; exact eq_zero_iff_not_coprime.1 h

中文:
定理 ne_zero
  条件: {a : 整数} {b : 自然数} (h : a.gcd b = 1)
  结论: J(a | b) != 0
  证明: by
  rcases eq_zero_or_neZero b with hb | _
  · rw [hb, zero_right]
    exact one_ne_zero
  · contrapose! h; exact eq_zero_iff_not_coprime.1 h
-/
protected theorem ne_zero {a : Int} {b : Nat} (h : a.gcd b = 1) : J(a | b) != 0 := by
  rcases eq_zero_or_neZero b with hb | _
  · rw [hb, zero_right]
    exact one_ne_zero
  · contrapose! h; exact eq_zero_iff_not_coprime.1 h

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: {a : Int} {b : Nat}
  statement: J(a | b) = 0 ↔ b != 0 ∧ a.gcd b != 1
  proof: ⟨fun h => by
    rcases eq_or_ne b 0 with hb | hb
    · rw [hb, zero_right] at h; cases h
exact ⟨hb, mt jacobiSym.ne_zero Classical.not_not.2 h⟩, fun ⟨hb, h⟩ => by
    rw [← neZero_iff] at hb; exact eq_zero_iff_not_coprime.2 h⟩

中文:
定理 eq_zero_iff
  条件: {a : 整数} {b : 自然数}
  结论: J(a | b) = 0 ↔ b != 0 ∧ a.gcd b != 1
  证明: ⟨fun h => by
    rcases eq_or_ne b 0 with hb | hb
    · rw [hb, zero_right] at h; cases h
exact ⟨hb, mt jacobiSym.ne_zero Classical.not_not.2 h⟩, fun ⟨hb, h⟩ => by
    rw [← neZero_iff] at hb; exact eq_zero_iff_not_coprime.2 h⟩

Depends on / 依赖: Classical, Classical.not_not, eq_or_ne, eq_zero_iff_not_coprime, jacobiSym, jacobiSym.ne_zero, neZero_iff, ne_zero, not_not, zero_right
-/
theorem eq_zero_iff {a : Int} {b : Nat} : J(a | b) = 0 ↔ b != 0 ∧ a.gcd b != 1 :=
  ⟨fun h => by
    rcases eq_or_ne b 0 with hb | hb
    · rw [hb, zero_right] at h; cases h
exact ⟨hb, mt jacobiSym.ne_zero Classical.not_not.2 h⟩, fun ⟨hb, h⟩ => by
    rw [← neZero_iff] at hb; exact eq_zero_iff_not_coprime.2 h⟩

/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  given: {b : Nat} (hb : 1 < b)
  statement: J(0 | b) = 0
  proof: (@eq_zero_iff_not_coprime 0 b ⟨ne_zero_of_lt hb⟩).mpr by
    rw [Int.gcd_zero_left]; rw [Int.natAbs_natCast]; exact hb.ne'

中文:
定理 zero_left
  条件: {b : 自然数} (hb : 1 < b)
  结论: J(0 | b) = 0
  证明: (@eq_zero_iff_not_coprime 0 b ⟨ne_zero_of_lt hb⟩).mpr by
    rw [Int.gcd_zero_left]; rw [Int.natAbs_natCast]; exact hb.ne'

Depends on / 依赖: Int.gcd_zero_left, Int.natAbs_natCast, eq_zero_iff_not_coprime, gcd_zero_left, hb.ne, natAbs_natCast, ne_zero_of_lt
-/
theorem zero_left {b : Nat} (hb : 1 < b) : J(0 | b) = 0 :=
(@eq_zero_iff_not_coprime 0 b ⟨ne_zero_of_lt hb⟩).mpr by
    rw [Int.gcd_zero_left]; rw [Int.natAbs_natCast]; exact hb.ne'

/--
theorem `eq_one_or_neg_one` / 定理 `eq_one_or_neg_one`

English:
theorem eq_one_or_neg_one
  given: {a : Int} {b : Nat} (h : a.gcd b = 1)
  statement: J(a | b) = 1 ∨ J(a | b) = -1
  proof: (trichotomy a b).resolve_left jacobiSym.ne_zero h

中文:
定理 eq_one_or_neg_one
  条件: {a : 整数} {b : 自然数} (h : a.gcd b = 1)
  结论: J(a | b) = 1 ∨ J(a | b) = -1
  证明: (trichotomy a b).resolve_left jacobiSym.ne_zero h

Depends on / 依赖: jacobiSym, jacobiSym.ne_zero, ne_zero, resolve_left, trichotomy
-/
theorem eq_one_or_neg_one {a : Int} {b : Nat} (h : a.gcd b = 1) : J(a | b) = 1 ∨ J(a | b) = -1 :=
(trichotomy a b).resolve_left jacobiSym.ne_zero h

/--
theorem `pow_left` / 定理 `pow_left`

English:
theorem pow_left
  given: (a : Int) (e b : Nat)
  statement: J(a ^ e | b) = J(a | b) ^ e
  proof: Nat.recOn e (by rw [_root_.pow_zero, _root_.pow_zero, one_left]) fun _ ih => by
    rw [_root_.pow_succ]; rw [_root_.pow_succ]; rw [mul_left]; rw [ih]

中文:
定理 pow_left
  条件: (a : 整数) (e b : 自然数)
  结论: J(a ^ e | b) = J(a | b) ^ e
  证明: Nat.recOn e (by rw [_root_.pow_zero, _root_.pow_zero, one_left]) fun _ ih => by
    rw [_root_.pow_succ]; rw [_root_.pow_succ]; rw [mul_left]; rw [ih]

Depends on / 依赖: Nat.recOn, _root_, _root_.pow_succ, _root_.pow_zero, mul_left, one_left, pow_succ, pow_zero
-/
theorem pow_left (a : Int) (e b : Nat) : J(a ^ e | b) = J(a | b) ^ e :=
  Nat.recOn e (by rw [_root_.pow_zero, _root_.pow_zero, one_left]) fun _ ih => by
    rw [_root_.pow_succ]; rw [_root_.pow_succ]; rw [mul_left]; rw [ih]

/--
theorem `pow_right` / 定理 `pow_right`

English:
theorem pow_right
  given: (a : Int) (b e : Nat)
  statement: J(a | b ^ e) = J(a | b) ^ e
  proof: by
  induction e with
  | zero => rw [Nat.pow_zero, _root_.pow_zero, one_right]
  | succ e ih =>
    rcases eq_zero_or_neZero b with hb | _
    · rw [hb, zero_pow e.succ_ne_zero, zero_right, one_pow]
    · rw [_root_.pow_succ, _root_.pow_succ, mul_right, ih]

中文:
定理 pow_right
  条件: (a : 整数) (b e : 自然数)
  结论: J(a | b ^ e) = J(a | b) ^ e
  证明: by
  induction e with
  | zero => rw [Nat.pow_zero, _root_.pow_zero, one_right]
  | succ e ih =>
    rcases eq_zero_or_neZero b with hb | _
    · rw [hb, zero_pow e.succ_ne_zero, zero_right, one_pow]
    · rw [_root_.pow_succ, _root_.pow_succ, mul_right, ih]

Depends on / 依赖: Nat.pow_zero, _root_, _root_.pow_succ, _root_.pow_zero, e.succ_ne_zero, eq_zero_or_neZero, mul_right, one_pow, one_right, pow_succ, pow_zero, succ_ne_zero, zero_pow, zero_right
-/
theorem pow_right (a : Int) (b e : Nat) : J(a | b ^ e) = J(a | b) ^ e := by
  induction e with
  | zero => rw [Nat.pow_zero, _root_.pow_zero, one_right]
  | succ e ih =>
    rcases eq_zero_or_neZero b with hb | _
    · rw [hb, zero_pow e.succ_ne_zero, zero_right, one_pow]
    · rw [_root_.pow_succ, _root_.pow_succ, mul_right, ih]

/--
theorem `sq_one` / 定理 `sq_one`

English:
theorem sq_one
  given: {a : Int} {b : Nat} (h : a.gcd b = 1)
  statement: J(a | b) ^ 2 = 1
  proof: by
  rcases eq_one_or_neg_one h with h₁ | h₁ <;> rw [h₁] <;> rfl

中文:
定理 sq_one
  条件: {a : 整数} {b : 自然数} (h : a.gcd b = 1)
  结论: J(a | b) ^ 2 = 1
  证明: by
  rcases eq_one_or_neg_one h with h₁ | h₁ <;> rw [h₁] <;> rfl

Depends on / 依赖: eq_one_or_neg_one
-/
theorem sq_one {a : Int} {b : Nat} (h : a.gcd b = 1) : J(a | b) ^ 2 = 1 := by
  rcases eq_one_or_neg_one h with h₁ | h₁ <;> rw [h₁] <;> rfl

/--
theorem `sq_one'` / 定理 `sq_one'`

English:
theorem sq_one'
  given: {a : Int} {b : Nat} (h : a.gcd b = 1)
  statement: J(a ^ 2 | b) = 1
  proof: by rw [pow_left, sq_one h]

中文:
定理 sq_one'
  条件: {a : 整数} {b : 自然数} (h : a.gcd b = 1)
  结论: J(a ^ 2 | b) = 1
  证明: by rw [pow_left, sq_one h]

Depends on / 依赖: pow_left, sq_one
-/
theorem sq_one' {a : Int} {b : Nat} (h : a.gcd b = 1) : J(a ^ 2 | b) = 1 := by rw [pow_left, sq_one h]

/--
theorem `mod_left` / 定理 `mod_left`

English:
theorem mod_left
  given: (a : Int) (b : Nat)
  statement: J(a | b) = J(a % b | b)
  proof: congr_arg List.prod
    List.pmap_congr_left _
      (by
        rintro p hp _ h₂
        conv_rhs =>
          rw [legendreSym.mod]; rw [Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.2 <|
            dvd_of_mem_primeFactorsList hp)]; rw [← legendreSym.mod])

中文:
定理 mod_left
  条件: (a : 整数) (b : 自然数)
  结论: J(a | b) = J(a % b | b)
  证明: congr_arg List.prod
    List.pmap_congr_left _
      (by
        rintro p hp _ h₂
        conv_rhs =>
          rw [legendreSym.mod]; rw [Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.2 <|
            dvd_of_mem_primeFactorsList hp)]; rw [← legendreSym.mod])

Depends on / 依赖: Int.emod_emod_of_dvd, Int.natCast_dvd_natCast, List.pmap_congr_left, List.prod, congr_arg, conv_rhs, dvd_of_mem_primeFactorsList, emod_emod_of_dvd, legendreSym, legendreSym.mod, natCast_dvd_natCast, pmap_congr_left
-/
theorem mod_left (a : Int) (b : Nat) : J(a | b) = J(a % b | b) :=
congr_arg List.prod
    List.pmap_congr_left _
      (by
        rintro p hp _ h₂
        conv_rhs =>
          rw [legendreSym.mod]; rw [Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.2 <|
            dvd_of_mem_primeFactorsList hp)]; rw [← legendreSym.mod])

/--
theorem `mod_left'` / 定理 `mod_left'`

English:
theorem mod_left'
  given: {a₁ a₂ : Int} {b : Nat} (h : a₁ % b = a₂ % b)
  statement: J(a₁ | b) = J(a₂ | b)
  proof: by
  rw [mod_left]; rw [h]; rw [← mod_left]

中文:
定理 mod_left'
  条件: {a₁ a₂ : 整数} {b : 自然数} (h : a₁ % b = a₂ % b)
  结论: J(a₁ | b) = J(a₂ | b)
  证明: by
  rw [mod_left]; rw [h]; rw [← mod_left]

Depends on / 依赖: mod_left
-/
theorem mod_left' {a₁ a₂ : Int} {b : Nat} (h : a₁ % b = a₂ % b) : J(a₁ | b) = J(a₂ | b) := by
  rw [mod_left]; rw [h]; rw [← mod_left]

/--
theorem `prime_dvd_of_eq_neg_one` / 定理 `prime_dvd_of_eq_neg_one`

English:
theorem prime_dvd_of_eq_neg_one
  statement: {p : Nat} [Fact p.Prime] {a : Int} (h : J(a | p) = -1) {x y : Int}
  proof: by
  rw [← legendreSym.to_jacobiSym] at h
  exact legendreSym.prime_dvd_of_eq_neg_one h hxy

中文:
定理 prime_dvd_of_eq_neg_one
  结论: {p : 自然数} [Fact p.Prime] {a : 整数} (h : J(a | p) = -1) {x y : 整数}
  证明: by
  rw [← legendreSym.to_jacobiSym] at h
  exact legendreSym.prime_dvd_of_eq_neg_one h hxy

Depends on / 依赖: legendreSym, legendreSym.prime_dvd_of_eq_neg_one, legendreSym.to_jacobiSym, prime_dvd_of_eq_neg_one, to_jacobiSym
-/
theorem prime_dvd_of_eq_neg_one {p : Nat} [Fact p.Prime] {a : Int} (h : J(a | p) = -1) {x y : Int}
    (hxy : ↑p ∣ (x ^ 2 - a * y ^ 2 : Int)) : ↑p ∣ x ∧ ↑p ∣ y := by
  rw [← legendreSym.to_jacobiSym] at h
  exact legendreSym.prime_dvd_of_eq_neg_one h hxy

/--
theorem `list_prod_left` / 定理 `list_prod_left`

English:
theorem list_prod_left
  given: {l : List Int} {n : Nat}
  statement: J(l.prod | n) = (l.map fun a => J(a | n)).prod
  proof: by
  induction l with
  | nil => simp only [List.prod_nil, List.map_nil, one_left]
  | cons n l' ih => rw [List.map, List.prod_cons, List.prod_cons, mul_left, ih]

中文:
定理 list_prod_left
  条件: {l : List 整数} {n : 自然数}
  结论: J(l.prod | n) = (l.map fun a => J(a | n)).prod
  证明: by
  induction l with
  | nil => simp only [List.prod_nil, List.map_nil, one_left]
  | cons n l' ih => rw [List.map, List.prod_cons, List.prod_cons, mul_left, ih]

Depends on / 依赖: List.map, List.map_nil, List.prod_cons, List.prod_nil, map_nil, mul_left, one_left, prod_cons, prod_nil
-/
theorem list_prod_left {l : List Int} {n : Nat} : J(l.prod | n) = (l.map fun a => J(a | n)).prod := by
  induction l with
  | nil => simp only [List.prod_nil, List.map_nil, one_left]
  | cons n l' ih => rw [List.map, List.prod_cons, List.prod_cons, mul_left, ih]

/--
theorem `list_prod_right` / 定理 `list_prod_right`

English:
theorem list_prod_right
  given: {a : Int} {l : List Nat} (hl : forall n in l, n != 0)
  proof: by
  induction l with
  | nil => simp only [List.prod_nil, one_right, List.map_nil]
  | cons n l' ih =>
    have hn := hl n List.mem_cons_self
    -- `n ≠ 0`
    have hl' := List.prod_ne_zero fun hf => hl 0 (List.mem_cons_of_mem _ hf) rfl
    -- `l'.prod ≠ 0`
    have h := fun m hm => hl m (List.mem

中文:
定理 list_prod_right
  条件: {a : 整数} {l : List 自然数} (hl : 对任意 n in l, n != 0)
  证明: by
  induction l with
  | nil => simp only [List.prod_nil, one_right, List.map_nil]
  | cons n l' ih =>
    have hn := hl n List.mem_cons_self
    -- `n ≠ 0`
    have hl' := List.prod_ne_zero fun hf => hl 0 (List.mem_cons_of_mem _ hf) rfl
    -- `l'.prod ≠ 0`
    have h := fun m hm => hl m (List.mem

Depends on / 依赖: List.map_nil, List.mem_cons_self, List.prod_nil, map_nil, mem_cons_self, one_right, prod_nil
-/
theorem list_prod_right {a : Int} {l : List Nat} (hl : forall n in l, n != 0) :
    J(a | l.prod) = (l.map fun n => J(a | n)).prod := by
  induction l with
  | nil => simp only [List.prod_nil, one_right, List.map_nil]
  | cons n l' ih =>
    have hn := hl n List.mem_cons_self
    -- `n ≠ 0`
    have hl' := List.prod_ne_zero fun hf => hl 0 (List.mem_cons_of_mem _ hf) rfl
    -- `l'.prod ≠ 0`
    have h := fun m hm => hl m (List.mem_cons_of_mem _ hm)
    -- `∀ (m : ℕ), m ∈ l' → m ≠ 0`
    rw [List.map]; rw [List.prod_cons]; rw [List.prod_cons]; rw [mul_right' a hn hl']; rw [ih h]

/--
theorem `eq_neg_one_at_prime_divisor_of_eq_neg_one` / 定理 `eq_neg_one_at_prime_divisor_of_eq_neg_one`

English:
theorem eq_neg_one_at_prime_divisor_of_eq_neg_one
  given: {a : Int} {n : Nat} (h : J(a | n) = -1)
  proof: by
  have hn₀ : n != 0 := by
    rintro rfl
    rw [zero_right]; rw [CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  have hf₀ (p) (hp : p in n.primeFactorsList) : p != 0 := (Nat.pos_of_mem_primeFactorsList hp).ne.symm
  rw [← Nat.prod_primeFactorsList hn₀]; rw [list_prod_right hf₀] at h
  o

中文:
定理 eq_neg_one_at_prime_divisor_of_eq_neg_one
  条件: {a : 整数} {n : 自然数} (h : J(a | n) = -1)
  证明: by
  have hn₀ : n != 0 := by
    rintro rfl
    rw [zero_right]; rw [CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  have hf₀ (p) (hp : p in n.primeFactorsList) : p != 0 := (Nat.pos_of_mem_primeFactorsList hp).ne.symm
  rw [← Nat.prod_primeFactorsList hn₀]; rw [list_prod_right hf₀] at h
  o

Depends on / 依赖: CharZero, CharZero.eq_neg_self_iff, List.mem_map.mp, List.neg_one_mem_of_prod_eq_neg_one, Nat.dvd_of_mem_primeFactorsList, Nat.pos_of_mem_primeFactorsList, Nat.prime_of_mem_primeFactorsList, Nat.prod_primeFactorsList, dvd_of_mem_primeFactorsList, eq_neg_self_iff, list_prod_right, mem_map, n.primeFactorsList, ne.symm, neg_one_mem_of_prod_eq_neg_one, one_ne_zero, pos_of_mem_primeFactorsList, primeFactorsList, prime_of_mem_primeFactorsList, prod_primeFactorsList
-/
theorem eq_neg_one_at_prime_divisor_of_eq_neg_one {a : Int} {n : Nat} (h : J(a | n) = -1) :
    exists p : Nat, p.Prime ∧ p ∣ n ∧ J(a | p) = -1 := by
  have hn₀ : n != 0 := by
    rintro rfl
    rw [zero_right]; rw [CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  have hf₀ (p) (hp : p in n.primeFactorsList) : p != 0 := (Nat.pos_of_mem_primeFactorsList hp).ne.symm
  rw [← Nat.prod_primeFactorsList hn₀]; rw [list_prod_right hf₀] at h
  obtain ⟨p, hmem, hj⟩ := List.mem_map.mp (List.neg_one_mem_of_prod_eq_neg_one h)
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hmem, Nat.dvd_of_mem_primeFactorsList hmem, hj⟩

end jacobiSym

namespace ZMod

open jacobiSym

/--
theorem `nonsquare_of_jacobiSym_eq_neg_one` / 定理 `nonsquare_of_jacobiSym_eq_neg_one`

English:
theorem nonsquare_of_jacobiSym_eq_neg_one
  given: {a : Int} {b : Nat} (h : J(a | b) = -1)
  proof: fun ⟨r, ha⟩ => by
  rw [← r.coe_valMinAbs]; rw [← Int.cast_mul]; rw [intCast_eq_intCast_iff']; rw [← sq] at ha
  apply (by simp : ¬(0 : Int) <= -1)
  rw [← h]; rw [mod_left]; rw [ha]; rw [← mod_left]; rw [pow_left]
  apply sq_nonneg

中文:
定理 nonsquare_of_jacobiSym_eq_neg_one
  条件: {a : 整数} {b : 自然数} (h : J(a | b) = -1)
  证明: fun ⟨r, ha⟩ => by
  rw [← r.coe_valMinAbs]; rw [← Int.cast_mul]; rw [intCast_eq_intCast_iff']; rw [← sq] at ha
  apply (by simp : ¬(0 : Int) <= -1)
  rw [← h]; rw [mod_left]; rw [ha]; rw [← mod_left]; rw [pow_left]
  apply sq_nonneg

Depends on / 依赖: Int.cast_mul, cast_mul, coe_valMinAbs, intCast_eq_intCast_iff, mod_left, pow_left, r.coe_valMinAbs, sq_nonneg
-/
theorem nonsquare_of_jacobiSym_eq_neg_one {a : Int} {b : Nat} (h : J(a | b) = -1) :
    ¬IsSquare (a : ZMod b) := fun ⟨r, ha⟩ => by
  rw [← r.coe_valMinAbs]; rw [← Int.cast_mul]; rw [intCast_eq_intCast_iff']; rw [← sq] at ha
  apply (by simp : ¬(0 : Int) <= -1)
  rw [← h]; rw [mod_left]; rw [ha]; rw [← mod_left]; rw [pow_left]
  apply sq_nonneg

/--
theorem `nonsquare_iff_jacobiSym_eq_neg_one` / 定理 `nonsquare_iff_jacobiSym_eq_neg_one`

English:
theorem nonsquare_iff_jacobiSym_eq_neg_one
  given: {a : Int} {p : Nat} [Fact p.Prime]
  proof: by
  rw [← legendreSym.to_jacobiSym]
  exact legendreSym.eq_neg_one_iff p

中文:
定理 nonsquare_iff_jacobiSym_eq_neg_one
  条件: {a : 整数} {p : 自然数} [Fact p.Prime]
  证明: by
  rw [← legendreSym.to_jacobiSym]
  exact legendreSym.eq_neg_one_iff p

Depends on / 依赖: eq_neg_one_iff, legendreSym, legendreSym.eq_neg_one_iff, legendreSym.to_jacobiSym, to_jacobiSym
-/
theorem nonsquare_iff_jacobiSym_eq_neg_one {a : Int} {p : Nat} [Fact p.Prime] :
    J(a | p) = -1 ↔ ¬IsSquare (a : ZMod p) := by
  rw [← legendreSym.to_jacobiSym]
  exact legendreSym.eq_neg_one_iff p

/--
theorem `isSquare_of_jacobiSym_eq_one` / 定理 `isSquare_of_jacobiSym_eq_one`

English:
theorem isSquare_of_jacobiSym_eq_one
  given: {a : Int} {p : Nat} [Fact p.Prime] (h : J(a | p) = 1)
  proof: Classical.not_not.mp by rw [← nonsquare_iff_jacobiSym_eq_neg_one, h]; decide

中文:
定理 isSquare_of_jacobiSym_eq_one
  条件: {a : 整数} {p : 自然数} [Fact p.Prime] (h : J(a | p) = 1)
  证明: Classical.not_not.mp by rw [← nonsquare_iff_jacobiSym_eq_neg_one, h]; decide

Depends on / 依赖: Classical, Classical.not_not.mp, nonsquare_iff_jacobiSym_eq_neg_one, not_not
-/
theorem isSquare_of_jacobiSym_eq_one {a : Int} {p : Nat} [Fact p.Prime] (h : J(a | p) = 1) :
    IsSquare (a : ZMod p) :=
Classical.not_not.mp by rw [← nonsquare_iff_jacobiSym_eq_neg_one, h]; decide

end ZMod

/-!
### Values at `-1`, `2` and `-2`
-/


namespace jacobiSym

/--
theorem `value_at` / 定理 `value_at`

English:
theorem value_at
  statement: (a : Int) {R : Type*} [Semiring R] (χ : R ->* Int)
  proof: by
  conv_rhs => rw [← prod_primeFactorsList hb.pos.ne', cast_list_prod, map_list_prod χ]
  rw [jacobiSym]; rw [List.map_map]; rw [← List.pmap_eq_map
    fun _ => prime_of_mem_primeFactorsList]
  congr 1; apply List.pmap_congr_left
  exact fun p h pp _ => hp p pp (hb.ne_two_of_dvd_nat <| dvd_of_mem_

中文:
定理 value_at
  结论: (a : 整数) {R : 类型} [Semiring R] (χ : R ->* 整数)
  证明: by
  conv_rhs => rw [← prod_primeFactorsList hb.pos.ne', cast_list_prod, map_list_prod χ]
  rw [jacobiSym]; rw [List.map_map]; rw [← List.pmap_eq_map
    fun _ => prime_of_mem_primeFactorsList]
  congr 1; apply List.pmap_congr_left
  exact fun p h pp _ => hp p pp (hb.ne_two_of_dvd_nat <| dvd_of_mem_

Depends on / 依赖: List.map_map, List.pmap_congr_left, List.pmap_eq_map, cast_list_prod, conv_rhs, dvd_of_mem_primeFactorsList, hb.ne_two_of_dvd_nat, hb.pos.ne, jacobiSym, map_list_prod, map_map, ne_two_of_dvd_nat, pmap_congr_left, pmap_eq_map, prime_of_mem_primeFactorsList, prod_primeFactorsList
-/
theorem value_at (a : Int) {R : Type*} [Semiring R] (χ : R ->* Int)
    (hp : forall (p : Nat) (pp : p.Prime), p != 2 -> @legendreSym p ⟨pp⟩ a = χ p) {b : Nat} (hb : Odd b) :
    J(a | b) = χ b := by
  conv_rhs => rw [← prod_primeFactorsList hb.pos.ne', cast_list_prod, map_list_prod χ]
  rw [jacobiSym]; rw [List.map_map]; rw [← List.pmap_eq_map
    fun _ => prime_of_mem_primeFactorsList]
  congr 1; apply List.pmap_congr_left
  exact fun p h pp _ => hp p pp (hb.ne_two_of_dvd_nat <| dvd_of_mem_primeFactorsList h)

/--
theorem `at_neg_one` / 定理 `at_neg_one`

English:
theorem at_neg_one
  given: {b : Nat} (hb : Odd b)
  statement: J(-1 | b) = χ₄ b
  proof: -- Porting note: In mathlib3, it was written `χ₄` and Lean could guess that it had to use
  -- `χ₄.to_monoid_hom`. This is not the case with Lean 4.
  value_at (-1) χ₄.toMonoidHom (fun p pp => @legendreSym.at_neg_one p ⟨pp⟩) hb

中文:
定理 at_neg_one
  条件: {b : 自然数} (hb : Odd b)
  结论: J(-1 | b) = χ₄ b
  证明: -- Porting note: In mathlib3, it was written `χ₄` and Lean could guess that it had to use
  -- `χ₄.to_monoid_hom`. This is not the case with Lean 4.
  value_at (-1) χ₄.toMonoidHom (fun p pp => @legendreSym.at_neg_one p ⟨pp⟩) hb
-/
theorem at_neg_one {b : Nat} (hb : Odd b) : J(-1 | b) = χ₄ b :=
  -- Porting note: In mathlib3, it was written `χ₄` and Lean could guess that it had to use
  -- `χ₄.to_monoid_hom`. This is not the case with Lean 4.
  value_at (-1) χ₄.toMonoidHom (fun p pp => @legendreSym.at_neg_one p ⟨pp⟩) hb

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (a : Int) {b : Nat} (hb : Odd b)
  statement: J(-a | b) = χ₄ b * J(a | b)
  proof: by
  rw [neg_eq_neg_one_mul]; rw [mul_left]; rw [at_neg_one hb]

中文:
定理 neg
  条件: (a : 整数) {b : 自然数} (hb : Odd b)
  结论: J(-a | b) = χ₄ b * J(a | b)
  证明: by
  rw [neg_eq_neg_one_mul]; rw [mul_left]; rw [at_neg_one hb]
-/
protected theorem neg (a : Int) {b : Nat} (hb : Odd b) : J(-a | b) = χ₄ b * J(a | b) := by
  rw [neg_eq_neg_one_mul]; rw [mul_left]; rw [at_neg_one hb]

/--
theorem `at_two` / 定理 `at_two`

English:
theorem at_two
  given: {b : Nat} (hb : Odd b)
  statement: J(2 | b) = χ₈ b
  proof: value_at 2 χ₈.toMonoidHom (fun p pp => @legendreSym.at_two p ⟨pp⟩) hb

中文:
定理 at_two
  条件: {b : 自然数} (hb : Odd b)
  结论: J(2 | b) = χ₈ b
  证明: value_at 2 χ₈.toMonoidHom (fun p pp => @legendreSym.at_two p ⟨pp⟩) hb

Depends on / 依赖: at_two, legendreSym, legendreSym.at_two, toMonoidHom, value_at
-/
theorem at_two {b : Nat} (hb : Odd b) : J(2 | b) = χ₈ b :=
  value_at 2 χ₈.toMonoidHom (fun p pp => @legendreSym.at_two p ⟨pp⟩) hb

/--
theorem `at_neg_two` / 定理 `at_neg_two`

English:
theorem at_neg_two
  given: {b : Nat} (hb : Odd b)
  statement: J(-2 | b) = χ₈' b
  proof: value_at (-2) χ₈'.toMonoidHom (fun p pp => @legendreSym.at_neg_two p ⟨pp⟩) hb

中文:
定理 at_neg_two
  条件: {b : 自然数} (hb : Odd b)
  结论: J(-2 | b) = χ₈' b
  证明: value_at (-2) χ₈'.toMonoidHom (fun p pp => @legendreSym.at_neg_two p ⟨pp⟩) hb

Depends on / 依赖: at_neg_two, legendreSym, legendreSym.at_neg_two, toMonoidHom, value_at
-/
theorem at_neg_two {b : Nat} (hb : Odd b) : J(-2 | b) = χ₈' b :=
  value_at (-2) χ₈'.toMonoidHom (fun p pp => @legendreSym.at_neg_two p ⟨pp⟩) hb

/--
theorem `div_four_left` / 定理 `div_four_left`

English:
theorem div_four_left
  given: {a : Int} {b : Nat} (ha4 : a % 4 = 0) (hb2 : b % 2 = 1)
  proof: by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha4
  have : Int.gcd (2 : Nat) b = 1 := by
    rw [Int.gcd_natCast_natCast]; rw [← b.mod_add_div 2]; rw [hb2]; rw [Nat.gcd_add_mul_left_right]; rw [Nat.gcd_one_right]
  rw [Int.mul_ediv_cancel_left _ (by decide)]; rw [jacobiSym.mul_left]; rw [(by decid

中文:
定理 div_four_left
  条件: {a : 整数} {b : 自然数} (ha4 : a % 4 = 0) (hb2 : b % 2 = 1)
  证明: by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha4
  have : Int.gcd (2 : Nat) b = 1 := by
    rw [Int.gcd_natCast_natCast]; rw [← b.mod_add_div 2]; rw [hb2]; rw [Nat.gcd_add_mul_left_right]; rw [Nat.gcd_one_right]
  rw [Int.mul_ediv_cancel_left _ (by decide)]; rw [jacobiSym.mul_left]; rw [(by decid

Depends on / 依赖: Int.dvd_of_emod_eq_zero, Int.gcd, Int.gcd_natCast_natCast, Int.mul_ediv_cancel_left, Nat.gcd_add_mul_left_right, Nat.gcd_one_right, b.mod_add_div, dvd_of_emod_eq_zero, gcd_add_mul_left_right, gcd_natCast_natCast, gcd_one_right, jacobiSym, jacobiSym.mul_left, jacobiSym.sq_one, mod_add_div, mul_ediv_cancel_left, mul_left, one_mul, sq_one
-/
theorem div_four_left {a : Int} {b : Nat} (ha4 : a % 4 = 0) (hb2 : b % 2 = 1) :
    J(a / 4 | b) = J(a | b) := by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha4
  have : Int.gcd (2 : Nat) b = 1 := by
    rw [Int.gcd_natCast_natCast]; rw [← b.mod_add_div 2]; rw [hb2]; rw [Nat.gcd_add_mul_left_right]; rw [Nat.gcd_one_right]
  rw [Int.mul_ediv_cancel_left _ (by decide)]; rw [jacobiSym.mul_left]; rw [(by decide : (4 : Int) = (2 : Nat) ^ 2)]; rw [jacobiSym.sq_one' this]; rw [one_mul]

/--
theorem `at_four` / 定理 `at_four`

English:
theorem at_four
  given: {b : Nat} (hb : Odd b)
  statement: J(4 | b) = 1
  proof: by
  have : J((4 : Int) | b) = J((4 : Int) / 4 | b) :=
    (div_four_left (by decide) (Nat.odd_iff.mp hb)).symm
  simpa [one_left]

中文:
定理 at_four
  条件: {b : 自然数} (hb : Odd b)
  结论: J(4 | b) = 1
  证明: by
  have : J((4 : Int) | b) = J((4 : Int) / 4 | b) :=
    (div_four_left (by decide) (Nat.odd_iff.mp hb)).symm
  simpa [one_left]

Depends on / 依赖: Nat.odd_iff.mp, div_four_left, odd_iff, one_left
-/
theorem at_four {b : Nat} (hb : Odd b) : J(4 | b) = 1 := by
  have : J((4 : Int) | b) = J((4 : Int) / 4 | b) :=
    (div_four_left (by decide) (Nat.odd_iff.mp hb)).symm
  simpa [one_left]

/--
theorem `even_odd` / 定理 `even_odd`

English:
theorem even_odd
  given: {a : Int} {b : Nat} (ha2 : a % 2 = 0) (hb2 : b % 2 = 1)
  proof: by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha2
  rw [Int.mul_ediv_cancel_left _ (by decide)]; rw [jacobiSym.mul_left]; rw [jacobiSym.at_two (Nat.odd_iff.mpr hb2)]; rw [ZMod.χ₈_nat_eq_if_mod_eight]; rw [if_neg (Nat.mod_two_ne_zero.mpr hb2)]
  grind

中文:
定理 even_odd
  条件: {a : 整数} {b : 自然数} (ha2 : a % 2 = 0) (hb2 : b % 2 = 1)
  证明: by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha2
  rw [Int.mul_ediv_cancel_left _ (by decide)]; rw [jacobiSym.mul_left]; rw [jacobiSym.at_two (Nat.odd_iff.mpr hb2)]; rw [ZMod.χ₈_nat_eq_if_mod_eight]; rw [if_neg (Nat.mod_two_ne_zero.mpr hb2)]
  grind

Depends on / 依赖: Int.dvd_of_emod_eq_zero, Int.mul_ediv_cancel_left, Nat.mod_two_ne_zero.mpr, Nat.odd_iff.mpr, at_two, dvd_of_emod_eq_zero, if_neg, jacobiSym, jacobiSym.at_two, jacobiSym.mul_left, mod_two_ne_zero, mul_ediv_cancel_left, mul_left, odd_iff
-/
theorem even_odd {a : Int} {b : Nat} (ha2 : a % 2 = 0) (hb2 : b % 2 = 1) :
    (if b % 8 = 3 ∨ b % 8 = 5 then -J(a / 2 | b) else J(a / 2 | b)) = J(a | b) := by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha2
  rw [Int.mul_ediv_cancel_left _ (by decide)]; rw [jacobiSym.mul_left]; rw [jacobiSym.at_two (Nat.odd_iff.mpr hb2)]; rw [ZMod.χ₈_nat_eq_if_mod_eight]; rw [if_neg (Nat.mod_two_ne_zero.mpr hb2)]
  grind

end jacobiSym

/-!
### Quadratic Reciprocity
-/


/--
Definition of `qrSign` / `qrSign` 的定义

English:
definition qrSign
  signature: (m n : Nat)
  body: J(χ₄ m | n)

中文:
定义 qrSign
  签名: (m n : 自然数)
  定义体: J(χ₄ m | n)
-/
def qrSign (m n : Nat) : Int :=
  J(χ₄ m | n)

namespace qrSign

/--
theorem `neg_one_pow` / 定理 `neg_one_pow`

English:
theorem neg_one_pow
  given: {m n : Nat} (hm : Odd m) (hn : Odd n)
  proof: by
  rw [qrSign]; rw [pow_mul]; rw [← χ₄_eq_neg_one_pow (odd_iff.mp hm)]
  rcases odd_mod_four_iff.mp (odd_iff.mp hm) with h | h
  · rw [χ₄_nat_one_mod_four h, jacobiSym.one_left, one_pow]
  · rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (odd_iff.mp hn), jacobiSym.at_neg_one hn]

中文:
定理 neg_one_pow
  条件: {m n : 自然数} (hm : Odd m) (hn : Odd n)
  证明: by
  rw [qrSign]; rw [pow_mul]; rw [← χ₄_eq_neg_one_pow (odd_iff.mp hm)]
  rcases odd_mod_four_iff.mp (odd_iff.mp hm) with h | h
  · rw [χ₄_nat_one_mod_four h, jacobiSym.one_left, one_pow]
  · rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (odd_iff.mp hn), jacobiSym.at_neg_one hn]

Depends on / 依赖: at_neg_one, jacobiSym, jacobiSym.at_neg_one, jacobiSym.one_left, odd_iff, odd_iff.mp, odd_mod_four_iff, odd_mod_four_iff.mp, one_left, one_pow, pow_mul, qrSign
-/
theorem neg_one_pow {m n : Nat} (hm : Odd m) (hn : Odd n) :
    qrSign m n = (-1) ^ (m / 2 * (n / 2)) := by
  rw [qrSign]; rw [pow_mul]; rw [← χ₄_eq_neg_one_pow (odd_iff.mp hm)]
  rcases odd_mod_four_iff.mp (odd_iff.mp hm) with h | h
  · rw [χ₄_nat_one_mod_four h, jacobiSym.one_left, one_pow]
  · rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (odd_iff.mp hn), jacobiSym.at_neg_one hn]

/--
theorem `sq_eq_one` / 定理 `sq_eq_one`

English:
theorem sq_eq_one
  given: {m n : Nat} (hm : Odd m) (hn : Odd n)
  statement: qrSign m n ^ 2 = 1
  proof: by
  rw [neg_one_pow hm hn]; rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]

中文:
定理 sq_eq_one
  条件: {m n : 自然数} (hm : Odd m) (hn : Odd n)
  结论: qrSign m n ^ 2 = 1
  证明: by
  rw [neg_one_pow hm hn]; rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]

Depends on / 依赖: mul_comm, neg_one_pow, neg_one_sq, one_pow, pow_mul
-/
theorem sq_eq_one {m n : Nat} (hm : Odd m) (hn : Odd n) : qrSign m n ^ 2 = 1 := by
  rw [neg_one_pow hm hn]; rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]

/--
theorem `mul_left` / 定理 `mul_left`

English:
theorem mul_left
  given: (m₁ m₂ n : Nat)
  statement: qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n
  proof: by
  simp_rw [qrSign, Nat.cast_mul, map_mul, jacobiSym.mul_left]

中文:
定理 mul_left
  条件: (m₁ m₂ n : 自然数)
  结论: qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n
  证明: by
  simp_rw [qrSign, Nat.cast_mul, map_mul, jacobiSym.mul_left]

Depends on / 依赖: DecidableLE, LocallyFiniteOrder, Nat.cast_mul, cast_mul, jacobiSym, jacobiSym.mul_left, map_mul, mul_left, qrSign, simp_rw
-/
theorem mul_left (m₁ m₂ n : Nat) : qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n := by
  simp_rw [qrSign, Nat.cast_mul, map_mul, jacobiSym.mul_left]

/--
theorem `mul_right` / 定理 `mul_right`

English:
theorem mul_right
  given: (m n₁ n₂ : Nat) [NeZero n₁] [NeZero n₂]
  proof: jacobiSym.mul_right (χ₄ m) n₁ n₂

中文:
定理 mul_right
  条件: (m n₁ n₂ : 自然数) [NeZero n₁] [NeZero n₂]
  证明: jacobiSym.mul_right (χ₄ m) n₁ n₂

Depends on / 依赖: DecidableLT, LocallyFiniteOrder, jacobiSym, jacobiSym.mul_right, mul_right
-/
theorem mul_right (m n₁ n₂ : Nat) [NeZero n₁] [NeZero n₂] :
    qrSign m (n₁ * n₂) = qrSign m n₁ * qrSign m n₂ :=
  jacobiSym.mul_right (χ₄ m) n₁ n₂

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: {m n : Nat} (hm : Odd m) (hn : Odd n)
  statement: qrSign m n = qrSign n m
  proof: by
  rw [neg_one_pow hm hn]; rw [neg_one_pow hn hm]; rw [mul_comm (m / 2)]

中文:
定理 symm
  条件: {m n : 自然数} (hm : Odd m) (hn : Odd n)
  结论: qrSign m n = qrSign n m
  证明: by
  rw [neg_one_pow hm hn]; rw [neg_one_pow hn hm]; rw [mul_comm (m / 2)]
-/
protected theorem symm {m n : Nat} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [neg_one_pow hm hn]; rw [neg_one_pow hn hm]; rw [mul_comm (m / 2)]

/--
theorem `eq_iff_eq` / 定理 `eq_iff_eq`

English:
theorem eq_iff_eq
  given: {m n : Nat} (hm : Odd m) (hn : Odd n) (x y : Int)
  proof: by
  refine
      ⟨fun h' =>
        let h := h'.symm
        ?_,
        fun h => ?_⟩ <;>
    rw [h]; rw [← mul_assoc]; rw [← pow_two]; rw [sq_eq_one hm hn]; rw [one_mul]

中文:
定理 eq_iff_eq
  条件: {m n : 自然数} (hm : Odd m) (hn : Odd n) (x y : 整数)
  证明: by
  refine
      ⟨fun h' =>
        let h := h'.symm
        ?_,
        fun h => ?_⟩ <;>
    rw [h]; rw [← mul_assoc]; rw [← pow_two]; rw [sq_eq_one hm hn]; rw [one_mul]

Depends on / 依赖: mul_assoc, one_mul, pow_two, sq_eq_one
-/
theorem eq_iff_eq {m n : Nat} (hm : Odd m) (hn : Odd n) (x y : Int) :
    qrSign m n * x = y ↔ x = qrSign m n * y := by
  refine
      ⟨fun h' =>
        let h := h'.symm
        ?_,
        fun h => ?_⟩ <;>
    rw [h]; rw [← mul_assoc]; rw [← pow_two]; rw [sq_eq_one hm hn]; rw [one_mul]

end qrSign

namespace jacobiSym

/--
theorem `quadratic_reciprocity'` / 定理 `quadratic_reciprocity'`

English:
theorem quadratic_reciprocity'
  given: {a b : Nat} (ha : Odd a) (hb : Odd b)
  proof: by
  -- define the right-hand side for fixed `a` as a `ℕ →* ℤ`
  let rhs : Nat -> Nat ->* Int := fun a =>
    { toFun := fun x => qrSign x a * J(x | a)
      map_one' := by convert! ← mul_one (M := Int) _; (on_goal 1 => symm); all_goals apply one_left
      map_mul' := fun x y => by
        simp_rw 

中文:
定理 quadratic_reciprocity'
  条件: {a b : 自然数} (ha : Odd a) (hb : Odd b)
  证明: by
  -- define the right-hand side for fixed `a` as a `ℕ →* ℤ`
  let rhs : Nat -> Nat ->* Int := fun a =>
    { toFun := fun x => qrSign x a * J(x | a)
      map_one' := by convert! ← mul_one (M := Int) _; (on_goal 1 => symm); all_goals apply one_left
      map_mul' := fun x y => by
        simp_rw 
-/
theorem quadratic_reciprocity' {a b : Nat} (ha : Odd a) (hb : Odd b) :
    J(a | b) = qrSign b a * J(b | a) := by
  -- define the right-hand side for fixed `a` as a `ℕ →* ℤ`
  let rhs : Nat -> Nat ->* Int := fun a =>
    { toFun := fun x => qrSign x a * J(x | a)
      map_one' := by convert! ← mul_one (M := Int) _; (on_goal 1 => symm); all_goals apply one_left
      map_mul' := fun x y => by
        simp_rw [qrSign.mul_left x y a, Nat.cast_mul, mul_left, mul_mul_mul_comm] }
  have rhs_apply : forall a b : Nat, rhs a b = qrSign b a * J(b | a) := fun a b => rfl
  refine value_at a (rhs a) (fun p pp hp => Eq.symm ?_) hb
  have hpo := pp.eq_two_or_odd'.resolve_left hp
  rw [@legendreSym.to_jacobiSym p ⟨pp⟩]; rw [rhs_apply]; rw [Nat.cast_id]; rw [qrSign.eq_iff_eq hpo ha]; rw [qrSign.symm hpo ha]
  refine value_at p (rhs p) (fun q pq hq => ?_) ha
  have hqo := pq.eq_two_or_odd'.resolve_left hq
  rw [rhs_apply]; rw [Nat.cast_id]; rw [← @legendreSym.to_jacobiSym p ⟨pp⟩]; rw [qrSign.symm hqo hpo]; rw [qrSign.neg_one_pow hpo hqo]; rw [@legendreSym.quadratic_reciprocity' p q ⟨pp⟩ ⟨pq⟩ hp hq]

/--
theorem `quadratic_reciprocity` / 定理 `quadratic_reciprocity`

English:
theorem quadratic_reciprocity
  given: {a b : Nat} (ha : Odd a) (hb : Odd b)
  proof: by
  rw [← qrSign.neg_one_pow ha hb]; rw [qrSign.symm ha hb]; rw [quadratic_reciprocity' ha hb]

中文:
定理 quadratic_reciprocity
  条件: {a b : 自然数} (ha : Odd a) (hb : Odd b)
  证明: by
  rw [← qrSign.neg_one_pow ha hb]; rw [qrSign.symm ha hb]; rw [quadratic_reciprocity' ha hb]

Depends on / 依赖: neg_one_pow, qrSign, qrSign.neg_one_pow, qrSign.symm, quadratic_reciprocity
-/
theorem quadratic_reciprocity {a b : Nat} (ha : Odd a) (hb : Odd b) :
    J(a | b) = (-1) ^ (a / 2 * (b / 2)) * J(b | a) := by
  rw [← qrSign.neg_one_pow ha hb]; rw [qrSign.symm ha hb]; rw [quadratic_reciprocity' ha hb]

/--
theorem `quadratic_reciprocity_one_mod_four` / 定理 `quadratic_reciprocity_one_mod_four`

English:
theorem quadratic_reciprocity_one_mod_four
  given: {a b : Nat} (ha : a % 4 = 1) (hb : Odd b)
  proof: by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb]; rw [pow_mul]; rw [neg_one_pow_div_two_of_one_mod_four ha]; rw [one_pow]; rw [one_mul]

中文:
定理 quadratic_reciprocity_one_mod_four
  条件: {a b : 自然数} (ha : a % 4 = 1) (hb : Odd b)
  证明: by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb]; rw [pow_mul]; rw [neg_one_pow_div_two_of_one_mod_four ha]; rw [one_pow]; rw [one_mul]

Depends on / 依赖: neg_one_pow_div_two_of_one_mod_four, odd_iff, odd_iff.mpr, odd_of_mod_four_eq_one, one_mul, one_pow, pow_mul, quadratic_reciprocity
-/
theorem quadratic_reciprocity_one_mod_four {a b : Nat} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb]; rw [pow_mul]; rw [neg_one_pow_div_two_of_one_mod_four ha]; rw [one_pow]; rw [one_mul]

/--
theorem `quadratic_reciprocity_one_mod_four'` / 定理 `quadratic_reciprocity_one_mod_four'`

English:
theorem quadratic_reciprocity_one_mod_four'
  given: {a b : Nat} (ha : Odd a) (hb : b % 4 = 1)
  proof: (quadratic_reciprocity_one_mod_four hb ha).symm

中文:
定理 quadratic_reciprocity_one_mod_four'
  条件: {a b : 自然数} (ha : Odd a) (hb : b % 4 = 1)
  证明: (quadratic_reciprocity_one_mod_four hb ha).symm

Depends on / 依赖: quadratic_reciprocity_one_mod_four
-/
theorem quadratic_reciprocity_one_mod_four' {a b : Nat} (ha : Odd a) (hb : b % 4 = 1) :
    J(a | b) = J(b | a) :=
  (quadratic_reciprocity_one_mod_four hb ha).symm

/--
theorem `quadratic_reciprocity_three_mod_four` / 定理 `quadratic_reciprocity_three_mod_four`

English:
theorem quadratic_reciprocity_three_mod_four
  given: {a b : Nat} (ha : a % 4 = 3) (hb : b % 4 = 3)
  proof: by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity]; rw [pow_mul]; rw [nop ha]; rw [nop hb]; rw [neg_one_mul] <;>
    rwa [odd_iff, odd_of_mod_four_eq_three]

中文:
定理 quadratic_reciprocity_three_mod_four
  条件: {a b : 自然数} (ha : a % 4 = 3) (hb : b % 4 = 3)
  证明: by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity]; rw [pow_mul]; rw [nop ha]; rw [nop hb]; rw [neg_one_mul] <;>
    rwa [odd_iff, odd_of_mod_four_eq_three]

Depends on / 依赖: neg_one_mul, neg_one_pow_div_two_of_three_mod_four, odd_iff, odd_of_mod_four_eq_three, pow_mul, quadratic_reciprocity
-/
theorem quadratic_reciprocity_three_mod_four {a b : Nat} (ha : a % 4 = 3) (hb : b % 4 = 3) :
    J(a | b) = -J(b | a) := by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity]; rw [pow_mul]; rw [nop ha]; rw [nop hb]; rw [neg_one_mul] <;>
    rwa [odd_iff, odd_of_mod_four_eq_three]

/--
theorem `quadratic_reciprocity_if` / 定理 `quadratic_reciprocity_if`

English:
theorem quadratic_reciprocity_if
  given: {a b : Nat} (ha2 : a % 2 = 1) (hb2 : b % 2 = 1)
  proof: by
  rcases Nat.odd_mod_four_iff.mp ha2 with ha1 | ha3
  · simpa [ha1] using jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hb2) ha1
  rcases Nat.odd_mod_four_iff.mp hb2 with hb1 | hb3
  · simpa [hb1] using jacobiSym.quadratic_reciprocity_one_mod_four hb1 (Nat.odd_iff.mpr ha2)
  simp

中文:
定理 quadratic_reciprocity_if
  条件: {a b : 自然数} (ha2 : a % 2 = 1) (hb2 : b % 2 = 1)
  证明: by
  rcases Nat.odd_mod_four_iff.mp ha2 with ha1 | ha3
  · simpa [ha1] using jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hb2) ha1
  rcases Nat.odd_mod_four_iff.mp hb2 with hb1 | hb3
  · simpa [hb1] using jacobiSym.quadratic_reciprocity_one_mod_four hb1 (Nat.odd_iff.mpr ha2)
  simp

Depends on / 依赖: Nat.odd_iff.mpr, Nat.odd_mod_four_iff.mp, jacobiSym, jacobiSym.quadratic_reciprocity_one_mod_four, jacobiSym.quadratic_reciprocity_three_mod_four, odd_iff, odd_mod_four_iff, quadratic_reciprocity_one_mod_four, quadratic_reciprocity_three_mod_four
-/
theorem quadratic_reciprocity_if {a b : Nat} (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) :
    (if a % 4 = 3 ∧ b % 4 = 3 then -J(b | a) else J(b | a)) = J(a | b) := by
  rcases Nat.odd_mod_four_iff.mp ha2 with ha1 | ha3
  · simpa [ha1] using jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hb2) ha1
  rcases Nat.odd_mod_four_iff.mp hb2 with hb1 | hb3
  · simpa [hb1] using jacobiSym.quadratic_reciprocity_one_mod_four hb1 (Nat.odd_iff.mpr ha2)
  simpa [ha3, hb3] using (jacobiSym.quadratic_reciprocity_three_mod_four ha3 hb3).symm

/--
theorem `mod_right'` / 定理 `mod_right'`

English:
theorem mod_right'
  given: (a : Nat) {b : Nat} (hb : Odd b)
  statement: J(a | b) = J(a | b % (4 * a))
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha₀)
  · rw [mul_zero, mod_zero]
  have hb' : Odd (b % (4 * a)) := hb.mod_even (Even.mul_right (by decide) _)
  rcases exists_eq_pow_mul_and_not_dvd ha₀ 2 (by simp) with ⟨e, a', ha₁', ha₂⟩
  have ha₁ := odd_iff.mpr (two_dvd_ne_zero.mp ha₁')
  nth_rw 2 [ha₂]; nth_

中文:
定理 mod_right'
  条件: (a : 自然数) {b : 自然数} (hb : Odd b)
  结论: J(a | b) = J(a | b % (4 * a))
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha₀)
  · rw [mul_zero, mod_zero]
  have hb' : Odd (b % (4 * a)) := hb.mod_even (Even.mul_right (by decide) _)
  rcases exists_eq_pow_mul_and_not_dvd ha₀ 2 (by simp) with ⟨e, a', ha₁', ha₂⟩
  have ha₁ := odd_iff.mpr (two_dvd_ne_zero.mp ha₁')
  nth_rw 2 [ha₂]; nth_

Depends on / 依赖: Even.mul_right, Nat.cast_mul, Nat.cast_pow, Nat.cast_two, at_two, cast_mul, cast_pow, cast_two, eq_or_ne, exists_eq_pow_mul_and_not_dvd, hb.mod_even, mod_even, mod_zero, mul_left, mul_right, mul_zero, nth_rw, odd_iff, odd_iff.mpr, pow_left
-/
theorem mod_right' (a : Nat) {b : Nat} (hb : Odd b) : J(a | b) = J(a | b % (4 * a)) := by
  rcases eq_or_ne a 0 with (rfl | ha₀)
  · rw [mul_zero, mod_zero]
  have hb' : Odd (b % (4 * a)) := hb.mod_even (Even.mul_right (by decide) _)
  rcases exists_eq_pow_mul_and_not_dvd ha₀ 2 (by simp) with ⟨e, a', ha₁', ha₂⟩
  have ha₁ := odd_iff.mpr (two_dvd_ne_zero.mp ha₁')
  nth_rw 2 [ha₂]; nth_rw 1 [ha₂]
  rw [Nat.cast_mul]; rw [mul_left]; rw [mul_left]; rw [quadratic_reciprocity' ha₁ hb]; rw [quadratic_reciprocity' ha₁ hb']; rw [Nat.cast_pow]; rw [pow_left]; rw [pow_left]; rw [Nat.cast_two]; rw [at_two hb]; rw [at_two hb']
  congr 1; swap
  · congr 1
    · simp_rw [qrSign]
      rw [χ₄_nat_mod_four]; rw [χ₄_nat_mod_four (b % (4 * a))]; rw [mod_mod_of_dvd b (dvd_mul_right 4 a)]
    · rw [mod_left ↑(b % _), mod_left b, Int.natCast_mod, Int.emod_emod_of_dvd b]
      simp only [ha₂, Nat.cast_mul, ← mul_assoc]
      apply dvd_mul_left
  rcases e with - | e; · simp
  · rw [χ₈_nat_mod_eight, χ₈_nat_mod_eight (b % (4 * a)), mod_mod_of_dvd b]
    use 2 ^ e * a'; rw [ha₂, Nat.pow_succ]; ring

/--
theorem `mod_right` / 定理 `mod_right`

English:
theorem mod_right
  given: (a : Int) {b : Nat} (hb : Odd b)
  statement: J(a | b) = J(a | b % (4 * a.natAbs))
  proof: by
  rcases Int.natAbs_eq a with ha | ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb]; rw [jacobiSym.neg _ hb']; rw [mod_right' _ hb]; rw [χ₄_nat_mod_four]; rw [χ

中文:
定理 mod_right
  条件: (a : 整数) {b : 自然数} (hb : Odd b)
  结论: J(a | b) = J(a | b % (4 * a.natAbs))
  证明: by
  rcases Int.natAbs_eq a with ha | ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb]; rw [jacobiSym.neg _ hb']; rw [mod_right' _ hb]; rw [χ₄_nat_mod_four]; rw [χ

Depends on / 依赖: Even.mul_right, Int.natAbs_eq, a.natAbs, dvd_mul_right, hb.mod_even, jacobiSym, jacobiSym.neg, mod_even, mod_mod_of_dvd, mod_right, mul_right, natAbs, natAbs_eq, nth_rw
-/
theorem mod_right (a : Int) {b : Nat} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  rcases Int.natAbs_eq a with ha | ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb]; rw [jacobiSym.neg _ hb']; rw [mod_right' _ hb]; rw [χ₄_nat_mod_four]; rw [χ₄_nat_mod_four (b % (4 * _))]; rw [mod_mod_of_dvd b (dvd_mul_right 4 _)]

end jacobiSym

end Jacobi


section FastJacobi

/-!
### Fast computation of the Jacobi symbol
We follow the implementation as in `Mathlib/Tactic/NormNum/LegendreSymbol.lean`.
-/

-- `fastLegendreSym` is used for computing the Legendre symbol in a `norm_num` extension,
-- i.e. needs to be used publicly.
set_option backward.privateInPublic true

open NumberTheorySymbols jacobiSym

/--
Definition of `fastJacobiSymAux` / `fastJacobiSymAux` 的定义

English:
definition fastJacobiSymAux
  signature: (a b : Nat) (flip : Bool) (ha0 : a > 0)
  body: if ha4 : a % 4 = 0 then
    fastJacobiSymAux (a / 4) b flip
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha4)) (by decide))
  else if ha2 : a % 2 = 0 then
    fastJacobiSymAux (a / 2) b (xor (b % 8 = 3 ∨ b % 8 = 5) flip)
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero 

中文:
定义 fastJacobiSymAux
  签名: (a b : 自然数) (flip : 布尔) (ha0 : a > 0)
  定义体: if ha4 : a % 4 = 0 then
    fastJacobiSymAux (a / 4) b flip
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha4)) (by decide))
  else if ha2 : a % 2 = 0 then
    fastJacobiSymAux (a / 2) b (xor (b % 8 = 3 ∨ b % 8 = 5) flip)
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero 
-/
private def fastJacobiSymAux (a b : Nat) (flip : Bool) (ha0 : a > 0) : Int :=
  if ha4 : a % 4 = 0 then
    fastJacobiSymAux (a / 4) b flip
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha4)) (by decide))
  else if ha2 : a % 2 = 0 then
    fastJacobiSymAux (a / 2) b (xor (b % 8 = 3 ∨ b % 8 = 5) flip)
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha2)) (by decide))
  else if ha1 : a = 1 then
    if flip then -1 else 1
  else if hba : b % a = 0 then
    0
  else
    fastJacobiSymAux (b % a) a (xor (a % 4 = 3 ∧ b % 4 = 3) flip) (Nat.pos_of_ne_zero hba)
termination_by a
decreasing_by
  · exact a.div_lt_self ha0 (by decide)
  · exact a.div_lt_self ha0 (by decide)
  · exact b.mod_lt ha0

/--
theorem `fastJacobiSymAux.eq_jacobiSym` / 定理 `fastJacobiSymAux.eq_jacobiSym`

English:
theorem fastJacobiSymAux.eq_jacobiSym
  statement: {a b : Nat} {flip : Bool} {ha0 : a > 0}
  proof: by
  induction a using Nat.strongRecOn generalizing b flip with | ind a IH =>
  unfold fastJacobiSymAux
  split <;> rename_i ha4
  · rw [IH (a / 4) (a.div_lt_self ha0 (by decide)) hb2 hb1]
    simp only [Int.natCast_ediv, Nat.cast_ofNat, div_four_left (a := a) (mod_cast ha4) hb2]
  split <;> rename_

中文:
定理 fastJacobiSymAux.eq_jacobiSym
  结论: {a b : 自然数} {flip : 布尔} {ha0 : a > 0}
  证明: by
  induction a using Nat.strongRecOn generalizing b flip with | ind a IH =>
  unfold fastJacobiSymAux
  split <;> rename_i ha4
  · rw [IH (a / 4) (a.div_lt_self ha0 (by decide)) hb2 hb1]
    simp only [Int.natCast_ediv, Nat.cast_ofNat, div_four_left (a := a) (mod_cast ha4) hb2]
  split <;> rename_
-/
private theorem fastJacobiSymAux.eq_jacobiSym {a b : Nat} {flip : Bool} {ha0 : a > 0}
    (hb2 : b % 2 = 1) (hb1 : b > 1) :
    fastJacobiSymAux a b flip ha0 = if flip then -J(a | b) else J(a | b) := by
  induction a using Nat.strongRecOn generalizing b flip with | ind a IH =>
  unfold fastJacobiSymAux
  split <;> rename_i ha4
  · rw [IH (a / 4) (a.div_lt_self ha0 (by decide)) hb2 hb1]
    simp only [Int.natCast_ediv, Nat.cast_ofNat, div_four_left (a := a) (mod_cast ha4) hb2]
  split <;> rename_i ha2
  · rw [IH (a / 2) (a.div_lt_self ha0 (by decide)) hb2 hb1]
    simp only [Int.natCast_ediv, Nat.cast_ofNat, ← even_odd (a := a) (mod_cast ha2) hb2]
    by_cases h : b % 8 = 3 ∨ b % 8 = 5 <;> simp [h]; cases flip <;> simp
  split <;> rename_i ha1
  · subst ha1; simp
  split <;> rename_i hba
  · suffices J(a | b) = 0 by simp [this]
    refine eq_zero_iff.mpr ⟨fun h => absurd (h ▸ hb1) (by decide), ?_⟩
    rwa [Int.gcd_natCast_natCast, Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero hba)]
  rw [IH (b % a) (b.mod_lt ha0) (Nat.mod_two_ne_zero.mp ha2) (lt_of_le_of_ne ha0 (Ne.symm ha1))]
  simp only [Int.natCast_mod, ← mod_left]
  rw [← quadratic_reciprocity_if (Nat.mod_two_ne_zero.mp ha2) hb2]
  by_cases h : a % 4 = 3 ∧ b % 4 = 3 <;> simp [h]; cases flip <;> simp

/--
Definition of `fastJacobiSym` / `fastJacobiSym` 的定义

English:
definition fastJacobiSym
  signature: (a : Int) (b : Nat)
  body: if hb0 : b = 0 then
    1
  else if _ : b % 2 = 0 then
    if a % 2 = 0 then
      0
    else
      have : b / 2 < b := b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two
      fastJacobiSym a (b / 2)
  else if b = 1 then
    1
  else if hab : a % b = 0 then
    0
  else
    fastJacobiSymAux (a % b).

中文:
定义 fastJacobiSym
  签名: (a : 整数) (b : 自然数)
  定义体: if hb0 : b = 0 then
    1
  else if _ : b % 2 = 0 then
    if a % 2 = 0 then
      0
    else
      have : b / 2 < b := b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two
      fastJacobiSym a (b / 2)
  else if b = 1 then
    1
  else if hab : a % b = 0 then
    0
  else
    fastJacobiSymAux (a % b).
-/
private def fastJacobiSym (a : Int) (b : Nat) : Int :=
  if hb0 : b = 0 then
    1
  else if _ : b % 2 = 0 then
    if a % 2 = 0 then
      0
    else
      have : b / 2 < b := b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two
      fastJacobiSym a (b / 2)
  else if b = 1 then
    1
  else if hab : a % b = 0 then
    0
  else
    fastJacobiSymAux (a % b).natAbs b false (Int.natAbs_pos.mpr hab)

set_option backward.privateInPublic.warn false in
/--
theorem `fastJacobiSym.eq` / 定理 `fastJacobiSym.eq`

English:
theorem fastJacobiSym.eq
  statement: jacobiSym = fastJacobiSym
  proof: by
  ext a b
  induction b using Nat.strongRecOn with | ind b IH =>
  unfold fastJacobiSym
  split_ifs with hb0 hb2 ha2 hb1 hab
  · rw [hb0, zero_right]
  · refine eq_zero_iff.mpr ⟨hb0, ne_of_gt ?_⟩
    refine Nat.le_of_dvd (Int.gcd_pos_iff.mpr (mod_cast .inr hb0)) ?_
    refine Nat.dvd_gcd (Int.ofN

中文:
定理 fastJacobiSym.eq
  结论: jacobiSym = fastJacobiSym
  证明: by
  ext a b
  induction b using Nat.strongRecOn with | ind b IH =>
  unfold fastJacobiSym
  split_ifs with hb0 hb2 ha2 hb1 hab
  · rw [hb0, zero_right]
  · refine eq_zero_iff.mpr ⟨hb0, ne_of_gt ?_⟩
    refine Nat.le_of_dvd (Int.gcd_pos_iff.mpr (mod_cast .inr hb0)) ?_
    refine Nat.dvd_gcd (Int.ofN
-/
@[csimp] private theorem fastJacobiSym.eq : jacobiSym = fastJacobiSym := by
  ext a b
  induction b using Nat.strongRecOn with | ind b IH =>
  unfold fastJacobiSym
  split_ifs with hb0 hb2 ha2 hb1 hab
  · rw [hb0, zero_right]
  · refine eq_zero_iff.mpr ⟨hb0, ne_of_gt ?_⟩
    refine Nat.le_of_dvd (Int.gcd_pos_iff.mpr (mod_cast .inr hb0)) ?_
    refine Nat.dvd_gcd (Int.ofNat_dvd_left.mp (Int.dvd_of_emod_eq_zero ha2)) ?_
    exact Int.ofNat_dvd_left.mp (Int.dvd_of_emod_eq_zero (mod_cast hb2))
  · dsimp only
    rw [← IH (b / 2) (b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two)]
    obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero hb2
    rw [mul_right' a (by decide) fun h => hb0 (mul_eq_zero_of_right 2 h)]; rw [b.mul_div_cancel_left (by decide)]; rw [mod_left a 2]; rw [Nat.cast_ofNat]; rw [Int.emod_two_ne_zero.mp ha2]; rw [one_left]; rw [one_mul]
  · rw [hb1, one_right]
  · rw [mod_left, hab, zero_left (lt_of_le_of_ne (Nat.pos_of_ne_zero hb0) (Ne.symm hb1))]
  · rw [fastJacobiSymAux.eq_jacobiSym, if_neg Bool.false_ne_true, mod_left a b,
      Int.natAbs_of_nonneg (a.emod_nonneg (mod_cast hb0))]
    · exact Nat.mod_two_ne_zero.mp hb2
    · exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hb0) (Ne.symm hb1)

/-- Computes `legendreSym p a` using `fastJacobiSym`. -/
@[inline, nolint unusedArguments]
/--
Definition of `fastLegendreSym` / `fastLegendreSym` 的定义

English:
definition fastLegendreSym
  signature: (p : Nat) [Fact p.Prime] (a : Int)
  body: J(a | p)

中文:
定义 fastLegendreSym
  签名: (p : 自然数) [Fact p.Prime] (a : 整数)
  定义体: J(a | p)
-/
private def fastLegendreSym (p : Nat) [Fact p.Prime] (a : Int) : Int := J(a | p)

set_option backward.privateInPublic.warn false in
/--
theorem `fastLegendreSym.eq` / 定理 `fastLegendreSym.eq`

English:
theorem fastLegendreSym.eq
  statement: legendreSym = fastLegendreSym
  proof: by
  ext p _ a; rw [legendreSym.to_jacobiSym, fastLegendreSym]

中文:
定理 fastLegendreSym.eq
  结论: legendreSym = fastLegendreSym
  证明: by
  ext p _ a; rw [legendreSym.to_jacobiSym, fastLegendreSym]
-/
@[csimp] private theorem fastLegendreSym.eq : legendreSym = fastLegendreSym := by
  ext p _ a; rw [legendreSym.to_jacobiSym, fastLegendreSym]

end FastJacobi
