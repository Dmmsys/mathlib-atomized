/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Data.Int.SuccPred

/-!
# Pentagonal numbers

This file introduces (generalized) pentagonal numbers $k(3k-1)/2$ for integer $k$.

Some sources, such as A001318 in the OEIS, order generalized pentagonal numbers by indices
$k = 0, 1, -1, 2, -2, \cdots$ to form a strictly monotone sequence. This file doesn't follow this
convention, but implicitly shows the monotonicity in `pentagonal_lt_pentagonal_neg` and
`pentagonal_neg_lt_pentagonal_add_one`.

## Main definitions

* `pentagonal`: pentagonal numbers as a function `ℤ → ℕ`.

## References

* https://en.wikipedia.org/wiki/Pentagonal_number
-/

public section

/--
Definition of `pentagonal` / `pentagonal` 的定义

English:
definition pentagonal
  signature: (k : Int)
  body: (k * (3 * k - 1) / 2).toNat

中文:
定义 pentagonal
  签名: (k : 整数)
  定义体: (k * (3 * k - 1) / 2).toNat

Depends on / 依赖: Function, Function.comp_def, Seq.seq, commutative_map, comp_def, map_map, seq_map_assoc
-/
def pentagonal (k : Int) : Nat := (k * (3 * k - 1) / 2).toNat

/--
theorem `pentagonal_def` / 定理 `pentagonal_def`

English:
theorem pentagonal_def
  given: (k : Int)
  statement: pentagonal k = (k * (3 * k - 1) / 2).toNat
  proof: by rfl

中文:
定理 pentagonal_def
  条件: (k : 整数)
  结论: pentagonal k = (k * (3 * k - 1) / 2).to自然数
  证明: by rfl
-/
theorem pentagonal_def (k : Int) : pentagonal k = (k * (3 * k - 1) / 2).toNat := by rfl

/--
theorem `pentagonal_neg` / 定理 `pentagonal_neg`

English:
theorem pentagonal_neg
  given: (k : Int)
  statement: pentagonal (-k) = (k * (3 * k + 1) / 2).toNat
  proof: by
  grind [pentagonal_def]

中文:
定理 pentagonal_neg
  条件: (k : 整数)
  结论: pentagonal (-k) = (k * (3 * k + 1) / 2).to自然数
  证明: by
  grind [pentagonal_def]

Depends on / 依赖: pentagonal_def
-/
theorem pentagonal_neg (k : Int) : pentagonal (-k) = (k * (3 * k + 1) / 2).toNat := by
  grind [pentagonal_def]

/--
theorem `natCast_pentagonal` / 定理 `natCast_pentagonal`

English:
theorem natCast_pentagonal
  given: (k : Int)
  statement: (pentagonal k : Int) = k * (3 * k - 1) / 2
  proof: by
  rcases k with (_ | _) | _ <;> grind [pentagonal_def]

中文:
定理 natCast_pentagonal
  条件: (k : 整数)
  结论: (pentagonal k : 整数) = k * (3 * k - 1) / 2
  证明: by
  rcases k with (_ | _) | _ <;> grind [pentagonal_def]

Depends on / 依赖: pentagonal_def
-/
theorem natCast_pentagonal (k : Int) : (pentagonal k : Int) = k * (3 * k - 1) / 2 := by
  rcases k with (_ | _) | _ <;> grind [pentagonal_def]

/--
theorem `two_mul_natCast_pentagonal` / 定理 `two_mul_natCast_pentagonal`

English:
theorem two_mul_natCast_pentagonal
  given: (k : Int)
  statement: 2 * (pentagonal k : Int) = k * (3 * k - 1)
  proof: by
  rw [natCast_pentagonal]
  exact Int.two_mul_ediv_two_of_even (by grind)

中文:
定理 two_mul_natCast_pentagonal
  条件: (k : 整数)
  结论: 2 * (pentagonal k : 整数) = k * (3 * k - 1)
  证明: by
  rw [natCast_pentagonal]
  exact Int.two_mul_ediv_two_of_even (by grind)

Depends on / 依赖: Int.two_mul_ediv_two_of_even, natCast_pentagonal, two_mul_ediv_two_of_even
-/
theorem two_mul_natCast_pentagonal (k : Int) : 2 * (pentagonal k : Int) = k * (3 * k - 1) := by
  rw [natCast_pentagonal]
  exact Int.two_mul_ediv_two_of_even (by grind)

/--
theorem `two_mul_natCast_pentagonal_neg` / 定理 `two_mul_natCast_pentagonal_neg`

English:
theorem two_mul_natCast_pentagonal_neg
  given: (k : Int)
  statement: 2 * (pentagonal (-k) : Int) = k * (3 * k + 1)
  proof: by
  grind [two_mul_natCast_pentagonal]

中文:
定理 two_mul_natCast_pentagonal_neg
  条件: (k : 整数)
  结论: 2 * (pentagonal (-k) : 整数) = k * (3 * k + 1)
  证明: by
  grind [two_mul_natCast_pentagonal]

Depends on / 依赖: two_mul_natCast_pentagonal
-/
theorem two_mul_natCast_pentagonal_neg (k : Int) : 2 * (pentagonal (-k) : Int) = k * (3 * k + 1) := by
  grind [two_mul_natCast_pentagonal]

/--
theorem `pentagonal_injective` / 定理 `pentagonal_injective`

English:
theorem pentagonal_injective
  statement: Function.Injective pentagonal
  proof: by
  intro x y h
  replace h : (3 * (x + y) - 1) * (x - y) = 0 := by grind [two_mul_natCast_pentagonal]
  cases mul_eq_zero.mp h <;> grind

@[simp]

中文:
定理 pentagonal_injective
  结论: 函数.单射 pentagonal
  证明: by
  intro x y h
  replace h : (3 * (x + y) - 1) * (x - y) = 0 := by grind [two_mul_natCast_pentagonal]
  cases mul_eq_zero.mp h <;> grind

@[simp]

Depends on / 依赖: mul_eq_zero, mul_eq_zero.mp, replace, two_mul_natCast_pentagonal
-/
theorem pentagonal_injective : Function.Injective pentagonal := by
  intro x y h
  replace h : (3 * (x + y) - 1) * (x - y) = 0 := by grind [two_mul_natCast_pentagonal]
  cases mul_eq_zero.mp h <;> grind

@[simp]
/--
theorem `pentagonal_inj` / 定理 `pentagonal_inj`

English:
theorem pentagonal_inj
  given: {x y : Int}
  statement: pentagonal x = pentagonal y ↔ x = y
  proof: pentagonal_injective.eq_iff

中文:
定理 pentagonal_inj
  条件: {x y : 整数}
  结论: pentagonal x = pentagonal y ↔ x = y
  证明: pentagonal_injective.eq_iff

Depends on / 依赖: eq_iff, pentagonal_injective, pentagonal_injective.eq_iff
-/
theorem pentagonal_inj {x y : Int} : pentagonal x = pentagonal y ↔ x = y :=
  pentagonal_injective.eq_iff

/--
theorem `pentagonal_lt_pentagonal_neg` / 定理 `pentagonal_lt_pentagonal_neg`

English:
theorem pentagonal_lt_pentagonal_neg
  given: {k : Int} (h : 0 < k)
  statement: pentagonal k < pentagonal (-k)
  proof: by
  grind [natCast_pentagonal]

中文:
定理 pentagonal_lt_pentagonal_neg
  条件: {k : 整数} (h : 0 < k)
  结论: pentagonal k < pentagonal (-k)
  证明: by
  grind [natCast_pentagonal]

Depends on / 依赖: natCast_pentagonal
-/
theorem pentagonal_lt_pentagonal_neg {k : Int} (h : 0 < k) : pentagonal k < pentagonal (-k) := by
  grind [natCast_pentagonal]

/--
theorem `pentagonal_neg_lt_pentagonal_add_one` / 定理 `pentagonal_neg_lt_pentagonal_add_one`

English:
theorem pentagonal_neg_lt_pentagonal_add_one
  given: {k : Int} (h : 0 <= k)
  proof: by
  grind [natCast_pentagonal]

中文:
定理 pentagonal_neg_lt_pentagonal_add_one
  条件: {k : 整数} (h : 0 <= k)
  证明: by
  grind [natCast_pentagonal]

Depends on / 依赖: natCast_pentagonal
-/
theorem pentagonal_neg_lt_pentagonal_add_one {k : Int} (h : 0 <= k) :
    pentagonal (-k) < pentagonal (k + 1) := by
  grind [natCast_pentagonal]

/--
theorem `pentagonal_strictMonoOn` / 定理 `pentagonal_strictMonoOn`

English:
theorem pentagonal_strictMonoOn
  statement: StrictMonoOn pentagonal (Set.Ici 0)
  proof: by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Ici
  grind [natCast_pentagonal]

中文:
定理 pentagonal_strictMonoOn
  结论: StrictMonoOn pentagonal (集合.左闭右无界区间 0)
  证明: by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Ici
  grind [natCast_pentagonal]

Depends on / 依赖: Set.ordConnected_Ici, natCast_pentagonal, ordConnected_Ici, strictMonoOn_of_lt_add_one
-/
theorem pentagonal_strictMonoOn : StrictMonoOn pentagonal (Set.Ici 0) := by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Ici
  grind [natCast_pentagonal]

/--
theorem `pentagonal_strictAntiOn` / 定理 `pentagonal_strictAntiOn`

English:
theorem pentagonal_strictAntiOn
  statement: StrictAntiOn pentagonal (Set.Iic 0)
  proof: by
  apply strictAntiOn_of_add_one_lt Set.ordConnected_Iic
  grind [natCast_pentagonal]

中文:
定理 pentagonal_strictAntiOn
  结论: StrictAntiOn pentagonal (集合.左无界右闭区间 0)
  证明: by
  apply strictAntiOn_of_add_one_lt Set.ordConnected_Iic
  grind [natCast_pentagonal]

Depends on / 依赖: Set.ordConnected_Iic, natCast_pentagonal, ordConnected_Iic, strictAntiOn_of_add_one_lt
-/
theorem pentagonal_strictAntiOn : StrictAntiOn pentagonal (Set.Iic 0) := by
  apply strictAntiOn_of_add_one_lt Set.ordConnected_Iic
  grind [natCast_pentagonal]
