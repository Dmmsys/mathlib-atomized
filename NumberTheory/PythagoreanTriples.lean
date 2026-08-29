/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen
-/
module

public import Mathlib.Data.Int.NatPrime
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.Field

/-!
# Pythagorean Triples

The main result is the classification of Pythagorean triples. The final result is for general
Pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof. The parametrization maps the point
`(x / z, y / z)` to the slope of the line through `(-1, 0)` and `(x / z, y / z)`. This quickly
shows that `(x / z, y / z) = (2 * m * n / (m ^ 2 + n ^ 2), (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))` where
`m / n` is the slope. In order to identify numerators and denominators we now need results showing
that these are coprime. This is easy except for the prime 2. In order to deal with that we have to
analyze the parity of `x`, `y`, `m` and `n` and eliminate all the impossible cases. This takes up
the bulk of the proof below.
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

/--
theorem `sq_ne_two_fin_zmod_four` / 定理 `sq_ne_two_fin_zmod_four`

English:
theorem sq_ne_two_fin_zmod_four
  given: (z : ZMod 4)
  statement: z * z != 2
  proof: by
  change Fin 4 at z
  fin_cases z <;> decide

中文:
定理 sq_ne_two_fin_zmod_four
  条件: (z : ZMod 4)
  结论: z * z != 2
  证明: by
  change Fin 4 at z
  fin_cases z <;> decide

Depends on / 依赖: fin_cases
-/
theorem sq_ne_two_fin_zmod_four (z : ZMod 4) : z * z != 2 := by
  change Fin 4 at z
  fin_cases z <;> decide

/--
theorem `Int.sq_ne_two_mod_four` / 定理 `Int.sq_ne_two_mod_four`

English:
theorem Int.sq_ne_two_mod_four
  given: (z : Int)
  statement: z * z % 4 != 2
  proof: by
  suffices ¬z * z % (4 : Nat) = 2 % (4 : Nat) by exact this
  rw [← ZMod.intCast_eq_intCast_iff']
  simpa using sq_ne_two_fin_zmod_four _

noncomputable section

中文:
定理 整数.sq_ne_two_mod_four
  条件: (z : 整数)
  结论: z * z % 4 != 2
  证明: by
  suffices ¬z * z % (4 : Nat) = 2 % (4 : Nat) by exact this
  rw [← ZMod.intCast_eq_intCast_iff']
  simpa using sq_ne_two_fin_zmod_four _

noncomputable section

Depends on / 依赖: ZMod.intCast_eq_intCast_iff, intCast_eq_intCast_iff, sq_ne_two_fin_zmod_four
-/
theorem Int.sq_ne_two_mod_four (z : Int) : z * z % 4 != 2 := by
  suffices ¬z * z % (4 : Nat) = 2 % (4 : Nat) by exact this
  rw [← ZMod.intCast_eq_intCast_iff']
  simpa using sq_ne_two_fin_zmod_four _

noncomputable section

/--
Definition of `PythagoreanTriple` / `PythagoreanTriple` 的定义

English:
definition PythagoreanTriple
  signature: (x y z : Int)
  body: x * x + y * y = z * z

中文:
定义 PythagoreanTriple
  签名: (x y z : 整数)
  定义体: x * x + y * y = z * z
-/
def PythagoreanTriple (x y z : Int) : Prop :=
  x * x + y * y = z * z

/--
theorem `pythagoreanTriple_comm` / 定理 `pythagoreanTriple_comm`

English:
theorem pythagoreanTriple_comm
  given: {x y z : Int}
  statement: PythagoreanTriple x y z ↔ PythagoreanTriple y x z
  proof: by
  delta PythagoreanTriple
  rw [add_comm]

中文:
定理 pythagoreanTriple_comm
  条件: {x y z : 整数}
  结论: PythagoreanTriple x y z ↔ PythagoreanTriple y x z
  证明: by
  delta PythagoreanTriple
  rw [add_comm]

Depends on / 依赖: PythagoreanTriple, add_comm
-/
theorem pythagoreanTriple_comm {x y z : Int} : PythagoreanTriple x y z ↔ PythagoreanTriple y x z := by
  delta PythagoreanTriple
  rw [add_comm]

/--
theorem `PythagoreanTriple.zero` / 定理 `PythagoreanTriple.zero`

English:
theorem PythagoreanTriple.zero
  statement: PythagoreanTriple 0 0 0
  proof: by
  simp only [PythagoreanTriple, zero_mul, zero_add]

中文:
定理 PythagoreanTriple.zero
  结论: PythagoreanTriple 0 0 0
  证明: by
  simp only [PythagoreanTriple, zero_mul, zero_add]

Depends on / 依赖: PythagoreanTriple, zero_add, zero_mul
-/
theorem PythagoreanTriple.zero : PythagoreanTriple 0 0 0 := by
  simp only [PythagoreanTriple, zero_mul, zero_add]

namespace PythagoreanTriple

variable {x y z : Int}

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (h : PythagoreanTriple x y z)
  statement: x * x + y * y = z * z
  proof: h

@[symm]

中文:
定理 eq
  条件: (h : PythagoreanTriple x y z)
  结论: x * x + y * y = z * z
  证明: h

@[symm]

Depends on / 依赖: Set.mem_union, mem_union
-/
theorem eq (h : PythagoreanTriple x y z) : x * x + y * y = z * z :=
  h

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : PythagoreanTriple x y z)
  statement: PythagoreanTriple y x z
  proof: by
  rwa [pythagoreanTriple_comm]

中文:
定理 symm
  条件: (h : PythagoreanTriple x y z)
  结论: PythagoreanTriple y x z
  证明: by
  rwa [pythagoreanTriple_comm]

Depends on / 依赖: IndepSets, IndepSets.union, Set.subset_union_left, Set.subset_union_right, h.left, h.right, indepSets_of_indepSets_of_le_left, pythagoreanTriple_comm, subset_union_left, subset_union_right
-/
theorem symm (h : PythagoreanTriple x y z) : PythagoreanTriple y x z := by
  rwa [pythagoreanTriple_comm]

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: (h : PythagoreanTriple x y z) (k : Int)
  statement: PythagoreanTriple (k * x) (k * y) (k * z)
  proof: calc
    k * x * (k * x) + k * y * (k * y) = k ^ 2 * (x * x + y * y) := by ring
    _ = k ^ 2 * (z * z) := by rw [h.eq]
    _ = k * z * (k * z) := by ring

中文:
定理 mul
  条件: (h : PythagoreanTriple x y z) (k : 整数)
  结论: PythagoreanTriple (k * x) (k * y) (k * z)
  证明: calc
    k * x * (k * x) + k * y * (k * y) = k ^ 2 * (x * x + y * y) := by ring
    _ = k ^ 2 * (z * z) := by rw [h.eq]
    _ = k * z * (k * z) := by ring

Depends on / 依赖: Set.mem_iUnion, h.eq, mem_iUnion
-/
theorem mul (h : PythagoreanTriple x y z) (k : Int) : PythagoreanTriple (k * x) (k * y) (k * z) :=
  calc
    k * x * (k * x) + k * y * (k * y) = k ^ 2 * (x * x + y * y) := by ring
    _ = k ^ 2 * (z * z) := by rw [h.eq]
    _ = k * z * (k * z) := by ring

/--
theorem `mul_iff` / 定理 `mul_iff`

English:
theorem mul_iff
  given: (k : Int) (hk : k != 0)
  proof: by
  refine ⟨?_, fun h => h.mul k⟩
  simp only [PythagoreanTriple]
  intro h
  rw [← mul_left_inj' (mul_ne_zero hk hk)]
  convert! h using 1 <;> ring

中文:
定理 mul_iff
  条件: (k : 整数) (hk : k != 0)
  证明: by
  refine ⟨?_, fun h => h.mul k⟩
  simp only [PythagoreanTriple]
  intro h
  rw [← mul_left_inj' (mul_ne_zero hk hk)]
  convert! h using 1 <;> ring

Depends on / 依赖: PythagoreanTriple, Set.mem_iUnion, convert, h.mul, mem_iUnion, mul_left_inj, mul_ne_zero, simp_rw
-/
theorem mul_iff (k : Int) (hk : k != 0) :
    PythagoreanTriple (k * x) (k * y) (k * z) ↔ PythagoreanTriple x y z := by
  refine ⟨?_, fun h => h.mul k⟩
  simp only [PythagoreanTriple]
  intro h
  rw [← mul_left_inj' (mul_ne_zero hk hk)]
  convert! h using 1 <;> ring

/-- A Pythagorean triple `x, y, z` is “classified” if there exist integers `k, m, n` such that
either
* `x = k * (m ^ 2 - n ^ 2)` and `y = k * (2 * m * n)`, or
* `x = k * (2 * m * n)` and `y = k * (m ^ 2 - n ^ 2)`. -/
@[nolint unusedArguments]
/--
Definition of `IsClassified` / `IsClassified` 的定义

English:
definition IsClassified
  signature: (_ : PythagoreanTriple x y z)
  body: exists k m n : Int,
    (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      Int.gcd m n = 1

中文:
定义 IsClassified
  签名: (_ : PythagoreanTriple x y z)
  定义体: exists k m n : Int,
    (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      Int.gcd m n = 1

Depends on / 依赖: Int.gcd, Set.mem_inter_iff, mem_inter_iff
-/
def IsClassified (_ : PythagoreanTriple x y z) :=
  exists k m n : Int,
    (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      Int.gcd m n = 1

/-- A primitive Pythagorean triple `x, y, z` is a Pythagorean triple with `x` and `y` coprime.
Such a triple is “primitively classified” if there exist coprime integers `m, n` such that either
* `x = m ^ 2 - n ^ 2` and `y = 2 * m * n`, or
* `x = 2 * m * n` and `y = m ^ 2 - n ^ 2`.
-/
@[nolint unusedArguments]
/--
Definition of `IsPrimitiveClassified` / `IsPrimitiveClassified` 的定义

English:
definition IsPrimitiveClassified
  signature: (_ : PythagoreanTriple x y z)
  body: exists m n : Int,
    (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
      Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)

中文:
定义 IsPrimitiveClassified
  签名: (_ : PythagoreanTriple x y z)
  定义体: exists m n : Int,
    (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
      Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)

Depends on / 依赖: Int.gcd, Set.mem_iInter.mp, mem_iInter
-/
def IsPrimitiveClassified (_ : PythagoreanTriple x y z) :=
  exists m n : Int,
    (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
      Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)

variable (h : PythagoreanTriple x y z)
include h

/--
theorem `mul_isClassified` / 定理 `mul_isClassified`

English:
theorem mul_isClassified
  given: (k : Int) (hc : h.IsClassified)
  statement: (h.mul k).IsClassified
  proof: by
  obtain ⟨l, m, n, ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co⟩⟩ := hc <;> use k * l, m, n <;> grind

中文:
定理 mul_isClassified
  条件: (k : 整数) (hc : h.IsClassified)
  结论: (h.mul k).IsClassified
  证明: by
  obtain ⟨l, m, n, ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co⟩⟩ := hc <;> use k * l, m, n <;> grind

Depends on / 依赖: Set.biInter_subset_of_mem, biInter_subset_of_mem
-/
theorem mul_isClassified (k : Int) (hc : h.IsClassified) : (h.mul k).IsClassified := by
  obtain ⟨l, m, n, ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co⟩⟩ := hc <;> use k * l, m, n <;> grind

/--
theorem `even_odd_of_coprime` / 定理 `even_odd_of_coprime`

English:
theorem even_odd_of_coprime
  given: (hc : Int.gcd x y = 1)
  proof: by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  -- x even, y even
  · exfalso
    apply Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) _ _ hc
    · apply Int.natCast_dvd.1
      apply Int.dvd_of_emod_eq_zero hx
    · apply Int.natCast_dvd.1
      apply Int.dvd_of_emod_eq_zero hy
  -- x even, y odd
  · left
    exact ⟨hx, hy⟩
  -- x odd, y even
  · right
    exact ⟨hx, hy⟩
  -- x odd, y odd
  · exfalso
    obtain ⟨x0, y0, rfl, rfl⟩ : exists x0 y0, x = x0 * 2 + 1 ∧ y = y0 * 2 + 1 := by
      obtain ⟨x0, hx2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hx)
      obtain ⟨y0, hy2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hy)
      rw [sub_eq_iff_eq_add] at hx2 hy2
      exact ⟨x0, y0, hx2, hy2⟩
    apply Int.sq_ne_two_mod_four z
    rw [show z * z = 4 * (x0 * x0 + x0 + y0 * y0 + y0) + 2 by
        rw [← h.eq]
        ring]
    simp only [Int.add_emod, Int.mul_emod_right, zero_add]
    decide

中文:
定理 even_odd_of_coprime
  条件: (hc : 整数.最大公约数 x y = 1)
  证明: by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  -- x even, y even
  · exfalso
    apply Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) _ _ hc
    · apply Int.natCast_dvd.1
      apply Int.dvd_of_emod_eq_zero hx
    · apply Int.natCast_dvd.1
      apply Int.dvd_of_emod_eq_zero hy
  -- x even, y odd
  · left
    exact ⟨hx, hy⟩
  -- x odd, y even
  · right
    exact ⟨hx, hy⟩
  -- x odd, y odd
  · exfalso
    obtain ⟨x0, y0, rfl, rfl⟩ : exists x0 y0, x = x0 * 2 + 1 ∧ y = y0 * 2 + 1 := by
      obtain ⟨x0, hx2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hx)
      obtain ⟨y0, hy2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hy)
      rw [sub_eq_iff_eq_add] at hx2 hy2
      exact ⟨x0, y0, hx2, hy2⟩
    apply Int.sq_ne_two_mod_four z
    rw [show z * z = 4 * (x0 * x0 + x0 + y0 * y0 + y0) + 2 by
        rw [← h.eq]
        ring]
    simp only [Int.add_emod, Int.mul_emod_right, zero_add]
    decide

Depends on / 依赖: Int.emod_two_eq_zero_or_one, emod_two_eq_zero_or_one
-/
theorem even_odd_of_coprime (hc : Int.gcd x y = 1) :
    x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0 := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  -- x even, y even
  · exfalso
    apply Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) _ _ hc
    · apply Int.natCast_dvd.1
      apply Int.dvd_of_emod_eq_zero hx
    · apply Int.natCast_dvd.1
      apply Int.dvd_of_emod_eq_zero hy
  -- x even, y odd
  · left
    exact ⟨hx, hy⟩
  -- x odd, y even
  · right
    exact ⟨hx, hy⟩
  -- x odd, y odd
  · exfalso
    obtain ⟨x0, y0, rfl, rfl⟩ : exists x0 y0, x = x0 * 2 + 1 ∧ y = y0 * 2 + 1 := by
      obtain ⟨x0, hx2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hx)
      obtain ⟨y0, hy2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hy)
      rw [sub_eq_iff_eq_add] at hx2 hy2
      exact ⟨x0, y0, hx2, hy2⟩
    apply Int.sq_ne_two_mod_four z
    rw [show z * z = 4 * (x0 * x0 + x0 + y0 * y0 + y0) + 2 by
        rw [← h.eq]
        ring]
    simp only [Int.add_emod, Int.mul_emod_right, zero_add]
    decide

/--
theorem `gcd_dvd` / 定理 `gcd_dvd`

English:
theorem gcd_dvd
  statement: (Int.gcd x y : Int) ∣ z
  proof: by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simp [h0, hz]
  obtain ⟨k, x0, y0, _, h2, rfl, rfl⟩ :
    exists (k : Nat) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  rw [Int.gcd_mul_right]; rw [h2]; rw [Int.natAbs_natCast]; rw [one_mul]
  rw [← Int.pow_dvd_pow_iff two_ne_zero]; rw [sq z]; rw [← h.eq]
  rw [(by ring : x0 * k * (x0 * k) + y0 * k * (y0 * k) = (k : Int) ^ 2 * (x0 * x0 + y0 * y0))]
  exact dvd_mul_right _ _

中文:
定理 gcd_dvd
  结论: (整数.最大公约数 x y : 整数) ∣ z
  证明: by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simp [h0, hz]
  obtain ⟨k, x0, y0, _, h2, rfl, rfl⟩ :
    exists (k : Nat) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  rw [Int.gcd_mul_right]; rw [h2]; rw [Int.natAbs_natCast]; rw [one_mul]
  rw [← Int.pow_dvd_pow_iff two_ne_zero]; rw [sq z]; rw [← h.eq]
  rw [(by ring : x0 * k * (x0 * k) + y0 * k * (y0 * k) = (k : Int) ^ 2 * (x0 * x0 + y0 * y0))]
  exact dvd_mul_right _ _

Depends on / 依赖: Int.exists_gcd_one, Int.gcd, Int.gcd_eq_zero_iff.mp, Int.gcd_mul_right, Int.natAbs_natCast, Int.pow_dvd_pow_iff, Nat.pos_of_ne_zero, PythagoreanTriple, add_zero, exists_gcd_one, gcd_eq_zero_iff, gcd_mul_right, mul_zero, natAbs_natCast, one_mul, or_self_iff, pos_of_ne_zero, pow_dvd_pow_iff, two_ne_zero, zero_eq_mul
-/
theorem gcd_dvd : (Int.gcd x y : Int) ∣ z := by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simp [h0, hz]
  obtain ⟨k, x0, y0, _, h2, rfl, rfl⟩ :
    exists (k : Nat) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  rw [Int.gcd_mul_right]; rw [h2]; rw [Int.natAbs_natCast]; rw [one_mul]
  rw [← Int.pow_dvd_pow_iff two_ne_zero]; rw [sq z]; rw [← h.eq]
  rw [(by ring : x0 * k * (x0 * k) + y0 * k * (y0 * k) = (k : Int) ^ 2 * (x0 * x0 + y0 * y0))]
  exact dvd_mul_right _ _

/--
theorem `normalize` / 定理 `normalize`

English:
theorem normalize
  statement: PythagoreanTriple (x / Int.gcd x y) (y / Int.gcd x y) (z / Int.gcd x y)
  proof: by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simpa [h0, hx, hy, hz] using zero
  rcases h.gcd_dvd with ⟨z0, rfl⟩
  obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ :
    exists (k : Nat) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  have hk : (k : Int) != 0 := by
    norm_cast
    rwa [pos_iff_ne_zero] at k0
  rw [Int.gcd_mul_right]; rw [h2]; rw [Int.natAbs_natCast]; rw [one_mul] at h ⊢
  rw [mul_comm x0]; rw [mul_comm y0]; rw [mul_iff k hk] at h
  rwa [Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel_left _ hk]

中文:
定理 normalize
  结论: PythagoreanTriple (x / 整数.最大公约数 x y) (y / 整数.最大公约数 x y) (z / 整数.最大公约数 x y)
  证明: by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simpa [h0, hx, hy, hz] using zero
  rcases h.gcd_dvd with ⟨z0, rfl⟩
  obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ :
    exists (k : Nat) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  have hk : (k : Int) != 0 := by
    norm_cast
    rwa [pos_iff_ne_zero] at k0
  rw [Int.gcd_mul_right]; rw [h2]; rw [Int.natAbs_natCast]; rw [one_mul] at h ⊢
  rw [mul_comm x0]; rw [mul_comm y0]; rw [mul_iff k hk] at h
  rwa [Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel_left _ hk]

Depends on / 依赖: Int.exists_gcd_one, Int.gcd, Int.gcd_eq_zero_iff.mp, Nat.pos_of_ne_zero, PythagoreanTriple, add_zero, exists_gcd_one, gcd_dvd, gcd_eq_zero_iff, h.gcd_dvd, mul_zero, or_self_iff, pos_iff_ne_zero, pos_of_ne_zero, zero_eq_mul
-/
theorem normalize : PythagoreanTriple (x / Int.gcd x y) (y / Int.gcd x y) (z / Int.gcd x y) := by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simpa [h0, hx, hy, hz] using zero
  rcases h.gcd_dvd with ⟨z0, rfl⟩
  obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ :
    exists (k : Nat) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  have hk : (k : Int) != 0 := by
    norm_cast
    rwa [pos_iff_ne_zero] at k0
  rw [Int.gcd_mul_right]; rw [h2]; rw [Int.natAbs_natCast]; rw [one_mul] at h ⊢
  rw [mul_comm x0]; rw [mul_comm y0]; rw [mul_iff k hk] at h
  rwa [Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel_left _ hk]

/--
theorem `isClassified_of_isPrimitiveClassified` / 定理 `isClassified_of_isPrimitiveClassified`

English:
theorem isClassified_of_isPrimitiveClassified
  given: (hp : h.IsPrimitiveClassified)
  statement: h.IsClassified
  proof: by
  obtain ⟨m, n, H⟩ := hp
  use 1, m, n
  lia

中文:
定理 isClassified_of_isPrimitiveClassified
  条件: (hp : h.IsPrimitiveClassified)
  结论: h.IsClassified
  证明: by
  obtain ⟨m, n, H⟩ := hp
  use 1, m, n
  lia

Depends on / 依赖: Finset, Finset.mem_insert.mp, Finset.mem_singleton.mp, Finset.set_biInter_insert, Finset.set_biInter_singleton, classical, filter_upwards, h_indep, h_inter, hf_m, hij.symm, mem_insert, mem_singleton, set_biInter_insert, set_biInter_singleton
-/
theorem isClassified_of_isPrimitiveClassified (hp : h.IsPrimitiveClassified) : h.IsClassified := by
  obtain ⟨m, n, H⟩ := hp
  use 1, m, n
  lia

/--
theorem `isClassified_of_normalize_isPrimitiveClassified` / 定理 `isClassified_of_normalize_isPrimitiveClassified`

English:
theorem isClassified_of_normalize_isPrimitiveClassified
  given: (hc : h.normalize.IsPrimitiveClassified)
  proof: by
  convert!
    h.normalize.mul_isClassified (Int.gcd x y)
      (isClassified_of_isPrimitiveClassified h.normalize hc) <;>
    rw [Int.mul_ediv_cancel']
  · exact Int.gcd_dvd_left ..
  · exact Int.gcd_dvd_right ..
  · exact h.gcd_dvd

中文:
定理 isClassified_of_normalize_isPrimitiveClassified
  条件: (hc : h.normalize.IsPrimitiveClassified)
  证明: by
  convert!
    h.normalize.mul_isClassified (Int.gcd x y)
      (isClassified_of_isPrimitiveClassified h.normalize hc) <;>
    rw [Int.mul_ediv_cancel']
  · exact Int.gcd_dvd_left ..
  · exact Int.gcd_dvd_right ..
  · exact h.gcd_dvd

Depends on / 依赖: Int.gcd, Int.gcd_dvd_left, Int.gcd_dvd_right, Int.mul_ediv_cancel, convert, gcd_dvd, gcd_dvd_left, gcd_dvd_right, h.gcd_dvd, h.normalize, h.normalize.mul_isClassified, h_indep, iIndepSets, iIndepSets.indepSets, indepSets, isClassified_of_isPrimitiveClassified, mul_ediv_cancel, mul_isClassified, normalize
-/
theorem isClassified_of_normalize_isPrimitiveClassified (hc : h.normalize.IsPrimitiveClassified) :
    h.IsClassified := by
  convert!
    h.normalize.mul_isClassified (Int.gcd x y)
      (isClassified_of_isPrimitiveClassified h.normalize hc) <;>
    rw [Int.mul_ediv_cancel']
  · exact Int.gcd_dvd_left ..
  · exact Int.gcd_dvd_right ..
  · exact h.gcd_dvd

/--
theorem `ne_zero_of_coprime` / 定理 `ne_zero_of_coprime`

English:
theorem ne_zero_of_coprime
  given: (hc : Int.gcd x y = 1)
  statement: z != 0
  proof: by
  suffices 0 < z * z by
    rintro rfl
    norm_num at this
  rw [← h.eq]; rw [← sq]; rw [← sq]
  have hc' : Int.gcd x y != 0 := by
    rw [hc]
    exact one_ne_zero
  rcases Int.ne_zero_of_gcd hc' with hxz | hyz
  · apply lt_add_of_pos_of_le (sq_pos_of_ne_zero hxz) (sq_nonneg y)
  · apply lt_add_of_le_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hyz)

中文:
定理 ne_zero_of_coprime
  条件: (hc : 整数.最大公约数 x y = 1)
  结论: z != 0
  证明: by
  suffices 0 < z * z by
    rintro rfl
    norm_num at this
  rw [← h.eq]; rw [← sq]; rw [← sq]
  have hc' : Int.gcd x y != 0 := by
    rw [hc]
    exact one_ne_zero
  rcases Int.ne_zero_of_gcd hc' with hxz | hyz
  · apply lt_add_of_pos_of_le (sq_pos_of_ne_zero hxz) (sq_nonneg y)
  · apply lt_add_of_le_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hyz)

Depends on / 依赖: Int.gcd, Int.ne_zero_of_gcd, MeasurableSet, h.eq, h_indep, lt_add_of_le_of_pos, lt_add_of_pos_of_le, measurableSet_generateFrom, ne_zero_of_gcd, one_ne_zero, sq_nonneg, sq_pos_of_ne_zero
-/
theorem ne_zero_of_coprime (hc : Int.gcd x y = 1) : z != 0 := by
  suffices 0 < z * z by
    rintro rfl
    norm_num at this
  rw [← h.eq]; rw [← sq]; rw [← sq]
  have hc' : Int.gcd x y != 0 := by
    rw [hc]
    exact one_ne_zero
  rcases Int.ne_zero_of_gcd hc' with hxz | hyz
  · apply lt_add_of_pos_of_le (sq_pos_of_ne_zero hxz) (sq_nonneg y)
  · apply lt_add_of_le_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hyz)

/--
theorem `isPrimitiveClassified_of_coprime_of_zero_left` / 定理 `isPrimitiveClassified_of_coprime_of_zero_left`

English:
theorem isPrimitiveClassified_of_coprime_of_zero_left
  given: (hc : Int.gcd x y = 1) (hx : x = 0)
  proof: by
  subst x
  change Nat.gcd 0 (Int.natAbs y) = 1 at hc
  rw [Nat.gcd_zero_left (Int.natAbs y)] at hc
  rcases Int.natAbs_eq y with hy | hy
  · use 1, 0
    rw [hy]; rw [hc]; rw [Int.gcd_zero_right]
    decide
  · use 0, 1
    rw [hy]; rw [hc]; rw [Int.gcd_zero_left]
    decide

中文:
定理 isPrimitiveClassified_of_coprime_of_zero_left
  条件: (hc : 整数.最大公约数 x y = 1) (hx : x = 0)
  证明: by
  subst x
  change Nat.gcd 0 (Int.natAbs y) = 1 at hc
  rw [Nat.gcd_zero_left (Int.natAbs y)] at hc
  rcases Int.natAbs_eq y with hy | hy
  · use 1, 0
    rw [hy]; rw [hc]; rw [Int.gcd_zero_right]
    decide
  · use 0, 1
    rw [hy]; rw [hc]; rw [Int.gcd_zero_left]
    decide

Depends on / 依赖: Int.gcd_zero_left, Int.gcd_zero_right, Int.natAbs, Int.natAbs_eq, Nat.gcd, Nat.gcd_zero_left, gcd_zero_left, gcd_zero_right, h_indep, measurableSet_generateFrom, natAbs, natAbs_eq
-/
theorem isPrimitiveClassified_of_coprime_of_zero_left (hc : Int.gcd x y = 1) (hx : x = 0) :
    h.IsPrimitiveClassified := by
  subst x
  change Nat.gcd 0 (Int.natAbs y) = 1 at hc
  rw [Nat.gcd_zero_left (Int.natAbs y)] at hc
  rcases Int.natAbs_eq y with hy | hy
  · use 1, 0
    rw [hy]; rw [hc]; rw [Int.gcd_zero_right]
    decide
  · use 0, 1
    rw [hy]; rw [hc]; rw [Int.gcd_zero_left]
    decide

/--
theorem `coprime_of_coprime` / 定理 `coprime_of_coprime`

English:
theorem coprime_of_coprime
  given: (hc : Int.gcd x y = 1)
  statement: Int.gcd y z = 1
  proof: by
  by_contra H
  obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  apply hp.not_dvd_one
  rw [← hc]
  apply Nat.dvd_gcd (Int.Prime.dvd_natAbs_of_coe_dvd_sq hp _ _) hpy
  rw [sq]; rw [eq_sub_of_add_eq h]
  rw [← Int.natCast_dvd] at hpy hpz
  exact dvd_sub (hpz.mul_right _) (hpy.mul_right _)

中文:
定理 coprime_of_coprime
  条件: (hc : 整数.最大公约数 x y = 1)
  结论: 整数.最大公约数 y z = 1
  证明: by
  by_contra H
  obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  apply hp.not_dvd_one
  rw [← hc]
  apply Nat.dvd_gcd (Int.Prime.dvd_natAbs_of_coe_dvd_sq hp _ _) hpy
  rw [sq]; rw [eq_sub_of_add_eq h]
  rw [← Int.natCast_dvd] at hpy hpz
  exact dvd_sub (hpz.mul_right _) (hpy.mul_right _)

Depends on / 依赖: Int.Prime.dvd_natAbs_of_coe_dvd_sq, Int.natCast_dvd, Nat.Prime.not_coprime_iff_dvd.mp, Nat.dvd_gcd, dvd_gcd, dvd_natAbs_of_coe_dvd_sq, dvd_sub, eq_sub_of_add_eq, hp.not_dvd_one, hpy.mul_right, hpz.mul_right, mul_right, natCast_dvd, not_coprime_iff_dvd, not_dvd_one
-/
theorem coprime_of_coprime (hc : Int.gcd x y = 1) : Int.gcd y z = 1 := by
  by_contra H
  obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  apply hp.not_dvd_one
  rw [← hc]
  apply Nat.dvd_gcd (Int.Prime.dvd_natAbs_of_coe_dvd_sq hp _ _) hpy
  rw [sq]; rw [eq_sub_of_add_eq h]
  rw [← Int.natCast_dvd] at hpy hpz
  exact dvd_sub (hpz.mul_right _) (hpy.mul_right _)

end PythagoreanTriple

section circleEquivGen

/-!
### A parametrization of the unit circle

For the classification of Pythagorean triples, we will use a parametrization of the unit circle.
-/


variable {K : Type*} [Field K]

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
Definition of `circleEquivGen` / `circleEquivGen` 的定义

English:
definition circleEquivGen
  signature: (hk : forall x : K, 1 + x ^ 2 != 0)
  body: ⟨⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩, by field [hk x], by
      simp only [Ne, div_eq_iff (hk x), neg_mul, one_mul, neg_add, sub_eq_add_neg, add_left_inj]
      simpa only [eq_neg_iff_add_eq_zero, one_pow] using hk 1⟩
  invFun p := (p : K × K).1 / ((p : K × K).2 + 1)
  left_inv x := by
    have h2 : (1 + 1 : K) = 2 := by norm_num
    have h3 : (2 : K) != 0 := by
      convert! hk 1
      rw [one_pow 2]; rw [h2]
    simp [field, hk x, h2, add_assoc, add_comm, add_sub_cancel, mul_comm]
  right_inv := fun ⟨⟨x, y⟩, hxy, hy⟩ => by
    change x ^ 2 + y ^ 2 = 1 at hxy
    have h2 : y + 1 != 0 := mt eq_neg_of_add_eq_zero_left hy
    have h3 : (y + 1) ^ 2 + x ^ 2 = 2 * (y + 1) := by
      rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm]
      ring
    have h4 : (2 : K) != 0 := by
      convert! hk 1
      rw [one_pow 2]
      ring
    simp only [Prod.mk_inj, Subtype.mk_eq_mk]
    constructor
    · simp [field, h3]
    · grind

@[simp]

中文:
定义 circleEquivGen
  签名: (hk : 对任意 x : K, 1 + x ^ 2 != 0)
  定义体: ⟨⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩, by field [hk x], by
      simp only [Ne, div_eq_iff (hk x), neg_mul, one_mul, neg_add, sub_eq_add_neg, add_left_inj]
      simpa only [eq_neg_iff_add_eq_zero, one_pow] using hk 1⟩
  invFun p := (p : K × K).1 / ((p : K × K).2 + 1)
  left_inv x := by
    have h2 : (1 + 1 : K) = 2 := by norm_num
    have h3 : (2 : K) != 0 := by
      convert! hk 1
      rw [one_pow 2]; rw [h2]
    simp [field, hk x, h2, add_assoc, add_comm, add_sub_cancel, mul_comm]
  right_inv := fun ⟨⟨x, y⟩, hxy, hy⟩ => by
    change x ^ 2 + y ^ 2 = 1 at hxy
    have h2 : y + 1 != 0 := mt eq_neg_of_add_eq_zero_left hy
    have h3 : (y + 1) ^ 2 + x ^ 2 = 2 * (y + 1) := by
      rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm]
      ring
    have h4 : (2 : K) != 0 := by
      convert! hk 1
      rw [one_pow 2]
      ring
    simp only [Prod.mk_inj, Subtype.mk_eq_mk]
    constructor
    · simp [field, h3]
    · grind

@[simp]

Depends on / 依赖: Filter, Filter.eventually_true, IndepSets, IndepSets.indep_aux, Set.empty_inter, Set.inter_comm, Set.s, Set.sdiff_self_inter, add_assoc, add_comm, add_left_inj, add_sub_cancel, convert, div_eq_iff, empty_inter, eq_neg_iff_add_eq_zero, eq_zero_or_isMarkovKernel, eventually_true, filter_upwards, indep_aux
-/
def circleEquivGen (hk : forall x : K, 1 + x ^ 2 != 0) :
    K ≃ { p : K × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 != -1 } where
  toFun x :=
    ⟨⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩, by field [hk x], by
      simp only [Ne, div_eq_iff (hk x), neg_mul, one_mul, neg_add, sub_eq_add_neg, add_left_inj]
      simpa only [eq_neg_iff_add_eq_zero, one_pow] using hk 1⟩
  invFun p := (p : K × K).1 / ((p : K × K).2 + 1)
  left_inv x := by
    have h2 : (1 + 1 : K) = 2 := by norm_num
    have h3 : (2 : K) != 0 := by
      convert! hk 1
      rw [one_pow 2]; rw [h2]
    simp [field, hk x, h2, add_assoc, add_comm, add_sub_cancel, mul_comm]
  right_inv := fun ⟨⟨x, y⟩, hxy, hy⟩ => by
    change x ^ 2 + y ^ 2 = 1 at hxy
    have h2 : y + 1 != 0 := mt eq_neg_of_add_eq_zero_left hy
    have h3 : (y + 1) ^ 2 + x ^ 2 = 2 * (y + 1) := by
      rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm]
      ring
    have h4 : (2 : K) != 0 := by
      convert! hk 1
      rw [one_pow 2]
      ring
    simp only [Prod.mk_inj, Subtype.mk_eq_mk]
    constructor
    · simp [field, h3]
    · grind

@[simp]
/--
theorem `circleEquivGen_apply` / 定理 `circleEquivGen_apply`

English:
theorem circleEquivGen_apply
  given: (hk : forall x : K, 1 + x ^ 2 != 0) (x : K)
  proof: rfl

@[simp]

中文:
定理 circleEquivGen_apply
  条件: (hk : 对任意 x : K, 1 + x ^ 2 != 0) (x : K)
  证明: rfl

@[simp]

Depends on / 依赖: generateFrom_le, hyp.indep
-/
theorem circleEquivGen_apply (hk : forall x : K, 1 + x ^ 2 != 0) (x : K) :
    (circleEquivGen hk x : K × K) = ⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩ :=
  rfl

@[simp]
/--
theorem `circleEquivGen_symm_apply` / 定理 `circleEquivGen_symm_apply`

English:
theorem circleEquivGen_symm_apply
  statement: (hk : forall x : K, 1 + x ^ 2 != 0)
  proof: rfl

中文:
定理 circleEquivGen_symm_apply
  结论: (hk : 对任意 x : K, 1 + x ^ 2 != 0)
  证明: rfl
-/
theorem circleEquivGen_symm_apply (hk : forall x : K, 1 + x ^ 2 != 0)
    (v : { p : K × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 != -1 }) :
    (circleEquivGen hk).symm v = (v : K × K).1 / ((v : K × K).2 + 1) :=
  rfl

end circleEquivGen

/--
theorem `coprime_sq_sub_sq_add_of_even_odd` / 定理 `coprime_sq_sub_sq_add_of_even_odd`

English:
theorem coprime_sq_sub_sq_add_of_even_odd
  statement: {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 0)
  proof: by
  by_contra H
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  rw [← Int.natCast_dvd] at hp1 hp2
  have h2m : (p : Int) ∣ 2 * m ^ 2 := by
    convert! dvd_add hp2 hp1 using 1
    ring
  have h2n : (p : Int) ∣ 2 * n ^ 2 := by
    convert! dvd_sub hp2 hp1 using 1
    ring
  have hmc : p = 2 ∨ p ∣ Int.natAbs m := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2m
  have hnc : p = 2 ∨ p ∣ Int.natAbs n := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2n
  by_cases h2 : p = 2
  · have h3 : (m ^ 2 + n ^ 2) % 2 = 1 := by
      simp only [sq, Int.add_emod, Int.mul_emod, hm, hn, dvd_refl, Int.emod_emod_of_dvd]
      decide
    have h4 : (m ^ 2 + n ^ 2) % 2 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      rwa [h2] at hp2
    rw [h4] at h3
    exact zero_ne_one h3
  · apply hp.not_dvd_one
    rw [← h]
    exact Nat.dvd_gcd (Or.resolve_left hmc h2) (Or.resolve_left hnc h2)

中文:
定理 coprime_sq_sub_sq_add_of_even_odd
  结论: {m n : 整数} (h : 整数.最大公约数 m n = 1) (hm : m % 2 = 0)
  证明: by
  by_contra H
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  rw [← Int.natCast_dvd] at hp1 hp2
  have h2m : (p : Int) ∣ 2 * m ^ 2 := by
    convert! dvd_add hp2 hp1 using 1
    ring
  have h2n : (p : Int) ∣ 2 * n ^ 2 := by
    convert! dvd_sub hp2 hp1 using 1
    ring
  have hmc : p = 2 ∨ p ∣ Int.natAbs m := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2m
  have hnc : p = 2 ∨ p ∣ Int.natAbs n := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2n
  by_cases h2 : p = 2
  · have h3 : (m ^ 2 + n ^ 2) % 2 = 1 := by
      simp only [sq, Int.add_emod, Int.mul_emod, hm, hn, dvd_refl, Int.emod_emod_of_dvd]
      decide
    have h4 : (m ^ 2 + n ^ 2) % 2 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      rwa [h2] at hp2
    rw [h4] at h3
    exact zero_ne_one h3
  · apply hp.not_dvd_one
    rw [← h]
    exact Nat.dvd_gcd (Or.resolve_left hmc h2) (Or.resolve_left hnc h2)

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.symm, Indep.congr, IndepSets, IndepSets.indep, IsMarkovKernel, Kernel, ae_isProbabilityMeasure, eq_or_ne, exists_ae_eq_isMarkovKernel, generateFrom_piiUnionInter_le, generateFrom_piiUnionInter_singleton_left, hs.ae_isProbabilityMeasure, measura, measurableSet_generateFrom
-/
private theorem coprime_sq_sub_sq_add_of_even_odd {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 0)
    (hn : n % 2 = 1) : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 := by
  by_contra H
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  rw [← Int.natCast_dvd] at hp1 hp2
  have h2m : (p : Int) ∣ 2 * m ^ 2 := by
    convert! dvd_add hp2 hp1 using 1
    ring
  have h2n : (p : Int) ∣ 2 * n ^ 2 := by
    convert! dvd_sub hp2 hp1 using 1
    ring
  have hmc : p = 2 ∨ p ∣ Int.natAbs m := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2m
  have hnc : p = 2 ∨ p ∣ Int.natAbs n := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2n
  by_cases h2 : p = 2
  · have h3 : (m ^ 2 + n ^ 2) % 2 = 1 := by
      simp only [sq, Int.add_emod, Int.mul_emod, hm, hn, dvd_refl, Int.emod_emod_of_dvd]
      decide
    have h4 : (m ^ 2 + n ^ 2) % 2 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      rwa [h2] at hp2
    rw [h4] at h3
    exact zero_ne_one h3
  · apply hp.not_dvd_one
    rw [← h]
    exact Nat.dvd_gcd (Or.resolve_left hmc h2) (Or.resolve_left hnc h2)

/--
theorem `coprime_sq_sub_sq_add_of_odd_even` / 定理 `coprime_sq_sub_sq_add_of_odd_even`

English:
theorem coprime_sq_sub_sq_add_of_odd_even
  statement: {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
  proof: by
  rw [Int.gcd]; rw [← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2)]; rw [add_comm]
  apply coprime_sq_sub_sq_add_of_even_odd _ hn hm; rwa [Int.gcd_comm]

中文:
定理 coprime_sq_sub_sq_add_of_odd_even
  结论: {m n : 整数} (h : 整数.最大公约数 m n = 1) (hm : m % 2 = 1)
  证明: by
  rw [Int.gcd]; rw [← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2)]; rw [add_comm]
  apply coprime_sq_sub_sq_add_of_even_odd _ hn hm; rwa [Int.gcd_comm]
-/
private theorem coprime_sq_sub_sq_add_of_odd_even {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
    (hn : n % 2 = 0) : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 := by
  rw [Int.gcd]; rw [← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2)]; rw [add_comm]
  apply coprime_sq_sub_sq_add_of_even_odd _ hn hm; rwa [Int.gcd_comm]

/--
theorem `coprime_sq_sub_mul_of_even_odd` / 定理 `coprime_sq_sub_mul_of_even_odd`

English:
theorem coprime_sq_sub_mul_of_even_odd
  statement: {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 0)
  proof: by
  by_contra H
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  rw [← Int.natCast_dvd] at hp1 hp2
  have hnp : ¬(p : Int) ∣ Int.gcd m n := by
    rw [h]
    norm_cast
    exact mt Nat.dvd_one.mp (Nat.Prime.ne_one hp)
  rcases Int.Prime.dvd_mul hp hp2 with hp2m | hpn
  · rw [Int.natAbs_mul] at hp2m
    rcases (Nat.Prime.dvd_mul hp).mp hp2m with hp2 | hpm
    · have hp2' : p = 2 := (Nat.le_of_dvd zero_lt_two hp2).antisymm hp.two_le
      revert hp1
      rw [hp2']
      apply mt Int.emod_eq_zero_of_dvd
      simp only [sq, Nat.cast_ofNat, Int.sub_emod, Int.mul_emod, hm, hn,
        mul_zero, EuclideanDomain.zero_mod, mul_one, zero_sub]
      decide
    apply mt (Int.dvd_coe_gcd (Int.natCast_dvd.mpr hpm)) hnp
    apply or_self_iff.mp
    apply Int.Prime.dvd_mul' hp
    rw [(by ring : n * n = -(m ^ 2 - n ^ 2) + m * m)]
    exact hp1.neg_right.add ((Int.natCast_dvd.2 hpm).mul_right _)
  rw [Int.gcd_comm] at hnp
  apply mt (Int.dvd_coe_gcd (Int.natCast_dvd.mpr hpn)) hnp
  apply or_self_iff.mp
  apply Int.Prime.dvd_mul' hp
  rw [(by ring : m * m = m ^ 2 - n ^ 2 + n * n)]
  apply dvd_add hp1
  exact (Int.natCast_dvd.mpr hpn).mul_right n

中文:
定理 coprime_sq_sub_mul_of_even_odd
  结论: {m n : 整数} (h : 整数.最大公约数 m n = 1) (hm : m % 2 = 0)
  证明: by
  by_contra H
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  rw [← Int.natCast_dvd] at hp1 hp2
  have hnp : ¬(p : Int) ∣ Int.gcd m n := by
    rw [h]
    norm_cast
    exact mt Nat.dvd_one.mp (Nat.Prime.ne_one hp)
  rcases Int.Prime.dvd_mul hp hp2 with hp2m | hpn
  · rw [Int.natAbs_mul] at hp2m
    rcases (Nat.Prime.dvd_mul hp).mp hp2m with hp2 | hpm
    · have hp2' : p = 2 := (Nat.le_of_dvd zero_lt_two hp2).antisymm hp.two_le
      revert hp1
      rw [hp2']
      apply mt Int.emod_eq_zero_of_dvd
      simp only [sq, Nat.cast_ofNat, Int.sub_emod, Int.mul_emod, hm, hn,
        mul_zero, EuclideanDomain.zero_mod, mul_one, zero_sub]
      decide
    apply mt (Int.dvd_coe_gcd (Int.natCast_dvd.mpr hpm)) hnp
    apply or_self_iff.mp
    apply Int.Prime.dvd_mul' hp
    rw [(by ring : n * n = -(m ^ 2 - n ^ 2) + m * m)]
    exact hp1.neg_right.add ((Int.natCast_dvd.2 hpm).mul_right _)
  rw [Int.gcd_comm] at hnp
  apply mt (Int.dvd_coe_gcd (Int.natCast_dvd.mpr hpn)) hnp
  apply or_self_iff.mp
  apply Int.Prime.dvd_mul' hp
  rw [(by ring : m * m = m ^ 2 - n ^ 2 + n * n)]
  apply dvd_add hp1
  exact (Int.natCast_dvd.mpr hpn).mul_right n
-/
private theorem coprime_sq_sub_mul_of_even_odd {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 0)
    (hn : n % 2 = 1) : Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  by_contra H
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  rw [← Int.natCast_dvd] at hp1 hp2
  have hnp : ¬(p : Int) ∣ Int.gcd m n := by
    rw [h]
    norm_cast
    exact mt Nat.dvd_one.mp (Nat.Prime.ne_one hp)
  rcases Int.Prime.dvd_mul hp hp2 with hp2m | hpn
  · rw [Int.natAbs_mul] at hp2m
    rcases (Nat.Prime.dvd_mul hp).mp hp2m with hp2 | hpm
    · have hp2' : p = 2 := (Nat.le_of_dvd zero_lt_two hp2).antisymm hp.two_le
      revert hp1
      rw [hp2']
      apply mt Int.emod_eq_zero_of_dvd
      simp only [sq, Nat.cast_ofNat, Int.sub_emod, Int.mul_emod, hm, hn,
        mul_zero, EuclideanDomain.zero_mod, mul_one, zero_sub]
      decide
    apply mt (Int.dvd_coe_gcd (Int.natCast_dvd.mpr hpm)) hnp
    apply or_self_iff.mp
    apply Int.Prime.dvd_mul' hp
    rw [(by ring : n * n = -(m ^ 2 - n ^ 2) + m * m)]
    exact hp1.neg_right.add ((Int.natCast_dvd.2 hpm).mul_right _)
  rw [Int.gcd_comm] at hnp
  apply mt (Int.dvd_coe_gcd (Int.natCast_dvd.mpr hpn)) hnp
  apply or_self_iff.mp
  apply Int.Prime.dvd_mul' hp
  rw [(by ring : m * m = m ^ 2 - n ^ 2 + n * n)]
  apply dvd_add hp1
  exact (Int.natCast_dvd.mpr hpn).mul_right n

/--
theorem `coprime_sq_sub_mul_of_odd_even` / 定理 `coprime_sq_sub_mul_of_odd_even`

English:
theorem coprime_sq_sub_mul_of_odd_even
  statement: {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
  proof: by
  rw [Int.gcd]; rw [← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  rw [(by ring : 2 * m * n = 2 * n * m)]; rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2)]
  apply coprime_sq_sub_mul_of_even_odd _ hn hm; rwa [Int.gcd_comm]

中文:
定理 coprime_sq_sub_mul_of_odd_even
  结论: {m n : 整数} (h : 整数.最大公约数 m n = 1) (hm : m % 2 = 1)
  证明: by
  rw [Int.gcd]; rw [← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  rw [(by ring : 2 * m * n = 2 * n * m)]; rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2)]
  apply coprime_sq_sub_mul_of_even_odd _ hn hm; rwa [Int.gcd_comm]

Depends on / 依赖: Set.disjoint_singleton_left.mpr, Set.mem_singleton_iff, Set.ofPred_eq_eq_singleton, convert, disjoint_singleton_left, exists_eq_left, iIndepSet, iIndepSet.indep_generateFrom_of_disjoint, indep_generateFrom_of_disjoint, lt_irrefl, mem_singleton_iff, ofPred_eq_eq_singleton
-/
private theorem coprime_sq_sub_mul_of_odd_even {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
    (hn : n % 2 = 0) : Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  rw [Int.gcd]; rw [← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  rw [(by ring : 2 * m * n = 2 * n * m)]; rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2)]
  apply coprime_sq_sub_mul_of_even_odd _ hn hm; rwa [Int.gcd_comm]

/--
theorem `coprime_sq_sub_mul` / 定理 `coprime_sq_sub_mul`

English:
theorem coprime_sq_sub_mul
  statement: {m n : Int} (h : Int.gcd m n = 1)
  proof: by
  rcases hmn with h1 | h2
  · exact coprime_sq_sub_mul_of_even_odd h h1.left h1.right
  · exact coprime_sq_sub_mul_of_odd_even h h2.left h2.right

中文:
定理 coprime_sq_sub_mul
  结论: {m n : 整数} (h : 整数.最大公约数 m n = 1)
  证明: by
  rcases hmn with h1 | h2
  · exact coprime_sq_sub_mul_of_even_odd h h1.left h1.right
  · exact coprime_sq_sub_mul_of_odd_even h h2.left h2.right

Depends on / 依赖: Set.disjoint_singleton_left.mpr, Set.mem_singleton_iff, Set.ofPred_eq_eq_singleton, convert, disjoint_singleton_left, exists_eq_left, hk.not_ge, iIndepSet, iIndepSet.indep_generateFrom_of_disjoint, indep_generateFrom_of_disjoint, mem_singleton_iff, not_ge, ofPred_eq_eq_singleton
-/
private theorem coprime_sq_sub_mul {m n : Int} (h : Int.gcd m n = 1)
    (hmn : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  rcases hmn with h1 | h2
  · exact coprime_sq_sub_mul_of_even_odd h h1.left h1.right
  · exact coprime_sq_sub_mul_of_odd_even h h2.left h2.right

/--
theorem `coprime_sq_sub_sq_sum_of_odd_odd` / 定理 `coprime_sq_sub_sq_sum_of_odd_odd`

English:
theorem coprime_sq_sub_sq_sum_of_odd_odd
  statement: {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
  proof: by
  obtain ⟨m0, hm2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
  obtain ⟨n0, hn2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
  rw [sub_eq_iff_eq_add] at hm2 hn2
  subst m
  subst n
  have h1 : (m0 * 2 + 1) ^ 2 + (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 + n0 ^ 2 + m0 + n0) + 1) := by
    ring
  have h2 : (m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 - n0 ^ 2 + m0 - n0)) := by ring
  have h3 : ((m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2) / 2 % 2 = 0 := by
    rw [h2]; rw [Int.mul_ediv_cancel_left]; rw [Int.mul_emod_right]
    decide
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, h3, ?_⟩
  have h20 : (2 : Int) != 0 := by decide
  rw [h1]; rw [h2]; rw [Int.mul_ediv_cancel_left _ h20]; rw [Int.mul_ediv_cancel_left _ h20]
  by_contra h4
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h4
  apply hp.not_dvd_one
  rw [← h]
  rw [← Int.natCast_dvd] at hp1 hp2
  apply Nat.dvd_gcd
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    convert! dvd_add hp1 hp2
    ring
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    convert! dvd_sub hp2 hp1
    ring

中文:
定理 coprime_sq_sub_sq_sum_of_odd_odd
  结论: {m n : 整数} (h : 整数.最大公约数 m n = 1) (hm : m % 2 = 1)
  证明: by
  obtain ⟨m0, hm2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
  obtain ⟨n0, hn2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
  rw [sub_eq_iff_eq_add] at hm2 hn2
  subst m
  subst n
  have h1 : (m0 * 2 + 1) ^ 2 + (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 + n0 ^ 2 + m0 + n0) + 1) := by
    ring
  have h2 : (m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 - n0 ^ 2 + m0 - n0)) := by ring
  have h3 : ((m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2) / 2 % 2 = 0 := by
    rw [h2]; rw [Int.mul_ediv_cancel_left]; rw [Int.mul_emod_right]
    decide
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, h3, ?_⟩
  have h20 : (2 : Int) != 0 := by decide
  rw [h1]; rw [h2]; rw [Int.mul_ediv_cancel_left _ h20]; rw [Int.mul_ediv_cancel_left _ h20]
  by_contra h4
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h4
  apply hp.not_dvd_one
  rw [← h]
  rw [← Int.natCast_dvd] at hp1 hp2
  apply Nat.dvd_gcd
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    convert! dvd_add hp1 hp2
    ring
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    convert! dvd_sub hp2 hp1
    ring

Depends on / 依赖: iIndepSet, iIndepSet.indep_generateFrom_le, indep_generateFrom_le, lt_succ_self, n.lt_succ_self
-/
private theorem coprime_sq_sub_sq_sum_of_odd_odd {m n : Int} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
    (hn : n % 2 = 1) :
    2 ∣ m ^ 2 + n ^ 2 ∧
      2 ∣ m ^ 2 - n ^ 2 ∧
        (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 := by
  obtain ⟨m0, hm2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
  obtain ⟨n0, hn2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
  rw [sub_eq_iff_eq_add] at hm2 hn2
  subst m
  subst n
  have h1 : (m0 * 2 + 1) ^ 2 + (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 + n0 ^ 2 + m0 + n0) + 1) := by
    ring
  have h2 : (m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 - n0 ^ 2 + m0 - n0)) := by ring
  have h3 : ((m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2) / 2 % 2 = 0 := by
    rw [h2]; rw [Int.mul_ediv_cancel_left]; rw [Int.mul_emod_right]
    decide
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, h3, ?_⟩
  have h20 : (2 : Int) != 0 := by decide
  rw [h1]; rw [h2]; rw [Int.mul_ediv_cancel_left _ h20]; rw [Int.mul_ediv_cancel_left _ h20]
  by_contra h4
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h4
  apply hp.not_dvd_one
  rw [← h]
  rw [← Int.natCast_dvd] at hp1 hp2
  apply Nat.dvd_gcd
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    convert! dvd_add hp1 hp2
    ring
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    convert! dvd_sub hp2 hp1
    ring

namespace PythagoreanTriple

variable {x y z : Int} (h : PythagoreanTriple x y z)

/--
theorem `isPrimitiveClassified_aux` / 定理 `isPrimitiveClassified_aux`

English:
theorem isPrimitiveClassified_aux
  statement: (hc : x.gcd y = 1) (hzpos : 0 < z) {m n : Int}
  proof: by
  have hz : z != 0 := ne_of_gt hzpos
  have h2 : y = m ^ 2 - n ^ 2 ∧ z = m ^ 2 + n ^ 2 := by
    apply Rat.div_int_inj hzpos hm2n2 (h.coprime_of_coprime hc) H
    rw [hw2]
    norm_cast
  use m, n
  apply And.intro _ (And.intro co pp)
  right
  refine ⟨?_, h2.left⟩
  rw [← Rat.intCast_inj]; rw [← div_left_inj' (mt Rat.intCast_inj.mp hz)]; rw [hv2]; rw [h2.right]
  norm_cast

中文:
定理 isPrimitiveClassified_aux
  结论: (hc : x.最大公约数 y = 1) (hzpos : 0 < z) {m n : 整数}
  证明: by
  have hz : z != 0 := ne_of_gt hzpos
  have h2 : y = m ^ 2 - n ^ 2 ∧ z = m ^ 2 + n ^ 2 := by
    apply Rat.div_int_inj hzpos hm2n2 (h.coprime_of_coprime hc) H
    rw [hw2]
    norm_cast
  use m, n
  apply And.intro _ (And.intro co pp)
  right
  refine ⟨?_, h2.left⟩
  rw [← Rat.intCast_inj]; rw [← div_left_inj' (mt Rat.intCast_inj.mp hz)]; rw [hv2]; rw [h2.right]
  norm_cast

Depends on / 依赖: And.intro, Rat.div_int_inj, Rat.intCast_inj, Rat.intCast_inj.mp, coprime_of_coprime, div_int_inj, div_left_inj, h.coprime_of_coprime, h2.left, h2.right, intCast_inj, ne_of_gt
-/
theorem isPrimitiveClassified_aux (hc : x.gcd y = 1) (hzpos : 0 < z) {m n : Int}
    (hm2n2 : 0 < m ^ 2 + n ^ 2) (hv2 : (x : Rat) / z = 2 * m * n / ((m : Rat) ^ 2 + (n : Rat) ^ 2))
    (hw2 : (y : Rat) / z = ((m : Rat) ^ 2 - (n : Rat) ^ 2) / ((m : Rat) ^ 2 + (n : Rat) ^ 2))
    (H : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1) (co : Int.gcd m n = 1)
    (pp : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) : h.IsPrimitiveClassified := by
  have hz : z != 0 := ne_of_gt hzpos
  have h2 : y = m ^ 2 - n ^ 2 ∧ z = m ^ 2 + n ^ 2 := by
    apply Rat.div_int_inj hzpos hm2n2 (h.coprime_of_coprime hc) H
    rw [hw2]
    norm_cast
  use m, n
  apply And.intro _ (And.intro co pp)
  right
  refine ⟨?_, h2.left⟩
  rw [← Rat.intCast_inj]; rw [← div_left_inj' (mt Rat.intCast_inj.mp hz)]; rw [hv2]; rw [h2.right]
  norm_cast

/--
theorem `isPrimitiveClassified_of_coprime_of_odd_of_pos` / 定理 `isPrimitiveClassified_of_coprime_of_odd_of_pos`

English:
theorem isPrimitiveClassified_of_coprime_of_odd_of_pos
  statement: (hc : Int.gcd x y = 1) (hyo : y % 2 = 1)
  proof: by
  by_cases h0 : x = 0
  · exact h.isPrimitiveClassified_of_coprime_of_zero_left hc h0
  let v := (x : Rat) / z
  let w := (y : Rat) / z
  have hq : v ^ 2 + w ^ 2 = 1 := by
    simp [field, v, w]
    simp only [sq]
    norm_cast
  have hvz : v != 0 := by simp [field, v, -mul_eq_zero, -div_eq_zero_iff, h0]
  have hw1 : w != -1 := by
    contrapose hvz with hw1
    rw [hw1]; rw [neg_sq]; rw [one_pow]; rw [add_eq_right] at hq
    exact eq_zero_of_pow_eq_zero hq
  have hQ : forall x : Rat, 1 + x ^ 2 != 0 := by
    intro q
    apply ne_of_gt
    exact lt_add_of_pos_of_le zero_lt_one (sq_nonneg q)
  have hp : (⟨v, w⟩ : Rat × Rat) in { p : Rat × Rat | p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 != -1 } := ⟨hq, hw1⟩
  let q := (circleEquivGen hQ).symm ⟨⟨v, w⟩, hp⟩
  have ht4 : v = 2 * q / (1 + q ^ 2) ∧ w = (1 - q ^ 2) / (1 + q ^ 2) := by
    apply Prod.mk.inj
    exact congr_arg Subtype.val ((circleEquivGen hQ).apply_symm_apply ⟨⟨v, w⟩, hp⟩).symm
  let m := (q.den : Int)
  let n := q.num
  have hm0 : m != 0 := by
    -- Added to adapt to https://github.com/leanprover/lean4/pull/2734.
    -- Without `unfold`, `norm_cast` can't see the coercion.
    -- One might try `zeta := true` in `Tactic.NormCast.derive`,
    -- but that seems to break many other things.
    unfold m
    norm_cast
    apply Rat.den_nz q
  have hq2 : q = n / m := (Rat.num_div_den q).symm
  have hm2n2 : 0 < m ^ 2 + n ^ 2 := by positivity
  have hm2n20 : (m ^ 2 + n ^ 2 : Rat) != 0 := by positivity
  have hw2 : w = ((m : Rat) ^ 2 - (n : Rat) ^ 2) / ((m : Rat) ^ 2 + (n : Rat) ^ 2) := by
    calc
      w = (1 - q ^ 2) / (1 + q ^ 2) := by apply ht4.2
      _ = (1 - (↑n / ↑m) ^ 2) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by field
  have hv2 : v = 2 * m * n / ((m : Rat) ^ 2 + (n : Rat) ^ 2) := by
    calc
      v = 2 * q / (1 + q ^ 2) := by apply ht4.1
      _ = 2 * (n / m) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by field
  have hnmcp : Int.gcd n m = 1 := q.reduced
  have hmncp : Int.gcd m n = 1 := by
    rw [Int.gcd_comm]
    exact hnmcp
  rcases Int.emod_two_eq_zero_or_one m with hm2 | hm2 <;>
    rcases Int.emod_two_eq_zero_or_one n with hn2 | hn2
  · -- m even, n even
    exfalso
    have h1 : 2 ∣ (Int.gcd n m : Int) :=
      Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hn2) (Int.dvd_of_emod_eq_zero hm2)
    lia
  · -- m even, n odd
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    · apply Or.intro_left
      exact And.intro hm2 hn2
    · apply coprime_sq_sub_sq_add_of_even_odd hmncp hm2 hn2
  · -- m odd, n even
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    · apply Or.intro_right
      exact And.intro hm2 hn2
    apply coprime_sq_sub_sq_add_of_odd_even hmncp hm2 hn2
  · -- m odd, n odd
    exfalso
    have h1 :
      2 ∣ m ^ 2 + n ^ 2 ∧
        2 ∣ m ^ 2 - n ^ 2 ∧
          (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 :=
      coprime_sq_sub_sq_sum_of_odd_odd hmncp hm2 hn2
    have h2 : y = (m ^ 2 - n ^ 2) / 2 ∧ z = (m ^ 2 + n ^ 2) / 2 := by
      apply Rat.div_int_inj hzpos _ (h.coprime_of_coprime hc) h1.2.2.2
      · change w = _
        rw [← Rat.divInt_eq_div]; rw [← Rat.divInt_mul_right (by simp : (2 : Int) != 0)]
        rw [Int.ediv_mul_cancel h1.1]; rw [Int.ediv_mul_cancel h1.2.1]; rw [hw2]; rw [Rat.divInt_eq_div]
        norm_cast
      · lia
    norm_num [h2.1, h1.2.2.1] at hyo

中文:
定理 isPrimitiveClassified_of_coprime_of_odd_of_pos
  结论: (hc : 整数.最大公约数 x y = 1) (hyo : y % 2 = 1)
  证明: by
  by_cases h0 : x = 0
  · exact h.isPrimitiveClassified_of_coprime_of_zero_left hc h0
  let v := (x : Rat) / z
  let w := (y : Rat) / z
  have hq : v ^ 2 + w ^ 2 = 1 := by
    simp [field, v, w]
    simp only [sq]
    norm_cast
  have hvz : v != 0 := by simp [field, v, -mul_eq_zero, -div_eq_zero_iff, h0]
  have hw1 : w != -1 := by
    contrapose hvz with hw1
    rw [hw1]; rw [neg_sq]; rw [one_pow]; rw [add_eq_right] at hq
    exact eq_zero_of_pow_eq_zero hq
  have hQ : forall x : Rat, 1 + x ^ 2 != 0 := by
    intro q
    apply ne_of_gt
    exact lt_add_of_pos_of_le zero_lt_one (sq_nonneg q)
  have hp : (⟨v, w⟩ : Rat × Rat) in { p : Rat × Rat | p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 != -1 } := ⟨hq, hw1⟩
  let q := (circleEquivGen hQ).symm ⟨⟨v, w⟩, hp⟩
  have ht4 : v = 2 * q / (1 + q ^ 2) ∧ w = (1 - q ^ 2) / (1 + q ^ 2) := by
    apply Prod.mk.inj
    exact congr_arg Subtype.val ((circleEquivGen hQ).apply_symm_apply ⟨⟨v, w⟩, hp⟩).symm
  let m := (q.den : Int)
  let n := q.num
  have hm0 : m != 0 := by
    -- Added to adapt to https://github.com/leanprover/lean4/pull/2734.
    -- Without `unfold`, `norm_cast` can't see the coercion.
    -- One might try `zeta := true` in `Tactic.NormCast.derive`,
    -- but that seems to break many other things.
    unfold m
    norm_cast
    apply Rat.den_nz q
  have hq2 : q = n / m := (Rat.num_div_den q).symm
  have hm2n2 : 0 < m ^ 2 + n ^ 2 := by positivity
  have hm2n20 : (m ^ 2 + n ^ 2 : Rat) != 0 := by positivity
  have hw2 : w = ((m : Rat) ^ 2 - (n : Rat) ^ 2) / ((m : Rat) ^ 2 + (n : Rat) ^ 2) := by
    calc
      w = (1 - q ^ 2) / (1 + q ^ 2) := by apply ht4.2
      _ = (1 - (↑n / ↑m) ^ 2) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by field
  have hv2 : v = 2 * m * n / ((m : Rat) ^ 2 + (n : Rat) ^ 2) := by
    calc
      v = 2 * q / (1 + q ^ 2) := by apply ht4.1
      _ = 2 * (n / m) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by field
  have hnmcp : Int.gcd n m = 1 := q.reduced
  have hmncp : Int.gcd m n = 1 := by
    rw [Int.gcd_comm]
    exact hnmcp
  rcases Int.emod_two_eq_zero_or_one m with hm2 | hm2 <;>
    rcases Int.emod_two_eq_zero_or_one n with hn2 | hn2
  · -- m even, n even
    exfalso
    have h1 : 2 ∣ (Int.gcd n m : Int) :=
      Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hn2) (Int.dvd_of_emod_eq_zero hm2)
    lia
  · -- m even, n odd
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    · apply Or.intro_left
      exact And.intro hm2 hn2
    · apply coprime_sq_sub_sq_add_of_even_odd hmncp hm2 hn2
  · -- m odd, n even
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    · apply Or.intro_right
      exact And.intro hm2 hn2
    apply coprime_sq_sub_sq_add_of_odd_even hmncp hm2 hn2
  · -- m odd, n odd
    exfalso
    have h1 :
      2 ∣ m ^ 2 + n ^ 2 ∧
        2 ∣ m ^ 2 - n ^ 2 ∧
          (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 :=
      coprime_sq_sub_sq_sum_of_odd_odd hmncp hm2 hn2
    have h2 : y = (m ^ 2 - n ^ 2) / 2 ∧ z = (m ^ 2 + n ^ 2) / 2 := by
      apply Rat.div_int_inj hzpos _ (h.coprime_of_coprime hc) h1.2.2.2
      · change w = _
        rw [← Rat.divInt_eq_div]; rw [← Rat.divInt_mul_right (by simp : (2 : Int) != 0)]
        rw [Int.ediv_mul_cancel h1.1]; rw [Int.ediv_mul_cancel h1.2.1]; rw [hw2]; rw [Rat.divInt_eq_div]
        norm_cast
      · lia
    norm_num [h2.1, h1.2.2.1] at hyo

Depends on / 依赖: add_eq_right, contrapose, div_eq_zero_iff, eq_zero_of_pow_eq_zero, h.isPrimitiveClassified_of_coprime_of_zero_left, isPrimitiveClassified_of_coprime_of_zero_left, mul_eq_zero, ne_of_gt, neg_sq, one_pow
-/
theorem isPrimitiveClassified_of_coprime_of_odd_of_pos (hc : Int.gcd x y = 1) (hyo : y % 2 = 1)
    (hzpos : 0 < z) : h.IsPrimitiveClassified := by
  by_cases h0 : x = 0
  · exact h.isPrimitiveClassified_of_coprime_of_zero_left hc h0
  let v := (x : Rat) / z
  let w := (y : Rat) / z
  have hq : v ^ 2 + w ^ 2 = 1 := by
    simp [field, v, w]
    simp only [sq]
    norm_cast
  have hvz : v != 0 := by simp [field, v, -mul_eq_zero, -div_eq_zero_iff, h0]
  have hw1 : w != -1 := by
    contrapose hvz with hw1
    rw [hw1]; rw [neg_sq]; rw [one_pow]; rw [add_eq_right] at hq
    exact eq_zero_of_pow_eq_zero hq
  have hQ : forall x : Rat, 1 + x ^ 2 != 0 := by
    intro q
    apply ne_of_gt
    exact lt_add_of_pos_of_le zero_lt_one (sq_nonneg q)
  have hp : (⟨v, w⟩ : Rat × Rat) in { p : Rat × Rat | p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 != -1 } := ⟨hq, hw1⟩
  let q := (circleEquivGen hQ).symm ⟨⟨v, w⟩, hp⟩
  have ht4 : v = 2 * q / (1 + q ^ 2) ∧ w = (1 - q ^ 2) / (1 + q ^ 2) := by
    apply Prod.mk.inj
    exact congr_arg Subtype.val ((circleEquivGen hQ).apply_symm_apply ⟨⟨v, w⟩, hp⟩).symm
  let m := (q.den : Int)
  let n := q.num
  have hm0 : m != 0 := by
    -- Added to adapt to https://github.com/leanprover/lean4/pull/2734.
    -- Without `unfold`, `norm_cast` can't see the coercion.
    -- One might try `zeta := true` in `Tactic.NormCast.derive`,
    -- but that seems to break many other things.
    unfold m
    norm_cast
    apply Rat.den_nz q
  have hq2 : q = n / m := (Rat.num_div_den q).symm
  have hm2n2 : 0 < m ^ 2 + n ^ 2 := by positivity
  have hm2n20 : (m ^ 2 + n ^ 2 : Rat) != 0 := by positivity
  have hw2 : w = ((m : Rat) ^ 2 - (n : Rat) ^ 2) / ((m : Rat) ^ 2 + (n : Rat) ^ 2) := by
    calc
      w = (1 - q ^ 2) / (1 + q ^ 2) := by apply ht4.2
      _ = (1 - (↑n / ↑m) ^ 2) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by field
  have hv2 : v = 2 * m * n / ((m : Rat) ^ 2 + (n : Rat) ^ 2) := by
    calc
      v = 2 * q / (1 + q ^ 2) := by apply ht4.1
      _ = 2 * (n / m) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by field
  have hnmcp : Int.gcd n m = 1 := q.reduced
  have hmncp : Int.gcd m n = 1 := by
    rw [Int.gcd_comm]
    exact hnmcp
  rcases Int.emod_two_eq_zero_or_one m with hm2 | hm2 <;>
    rcases Int.emod_two_eq_zero_or_one n with hn2 | hn2
  · -- m even, n even
    exfalso
    have h1 : 2 ∣ (Int.gcd n m : Int) :=
      Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hn2) (Int.dvd_of_emod_eq_zero hm2)
    lia
  · -- m even, n odd
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    · apply Or.intro_left
      exact And.intro hm2 hn2
    · apply coprime_sq_sub_sq_add_of_even_odd hmncp hm2 hn2
  · -- m odd, n even
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    · apply Or.intro_right
      exact And.intro hm2 hn2
    apply coprime_sq_sub_sq_add_of_odd_even hmncp hm2 hn2
  · -- m odd, n odd
    exfalso
    have h1 :
      2 ∣ m ^ 2 + n ^ 2 ∧
        2 ∣ m ^ 2 - n ^ 2 ∧
          (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 :=
      coprime_sq_sub_sq_sum_of_odd_odd hmncp hm2 hn2
    have h2 : y = (m ^ 2 - n ^ 2) / 2 ∧ z = (m ^ 2 + n ^ 2) / 2 := by
      apply Rat.div_int_inj hzpos _ (h.coprime_of_coprime hc) h1.2.2.2
      · change w = _
        rw [← Rat.divInt_eq_div]; rw [← Rat.divInt_mul_right (by simp : (2 : Int) != 0)]
        rw [Int.ediv_mul_cancel h1.1]; rw [Int.ediv_mul_cancel h1.2.1]; rw [hw2]; rw [Rat.divInt_eq_div]
        norm_cast
      · lia
    norm_num [h2.1, h1.2.2.1] at hyo

/--
theorem `isPrimitiveClassified_of_coprime_of_pos` / 定理 `isPrimitiveClassified_of_coprime_of_pos`

English:
theorem isPrimitiveClassified_of_coprime_of_pos
  given: (hc : Int.gcd x y = 1) (hzpos : 0 < z)
  proof: by
  rcases h.even_odd_of_coprime hc with h1 | h2
  · exact h.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h1.right hzpos
  rw [Int.gcd_comm] at hc
  obtain ⟨m, n, H⟩ := h.symm.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h2.left hzpos
  use m, n; tauto

中文:
定理 isPrimitiveClassified_of_coprime_of_pos
  条件: (hc : 整数.最大公约数 x y = 1) (hzpos : 0 < z)
  证明: by
  rcases h.even_odd_of_coprime hc with h1 | h2
  · exact h.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h1.right hzpos
  rw [Int.gcd_comm] at hc
  obtain ⟨m, n, H⟩ := h.symm.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h2.left hzpos
  use m, n; tauto

Depends on / 依赖: Finset, Finset.coe_subset, Finset.mem_insert.mp, Int.gcd_comm, Set.univ, classical, coe_subset, even_odd_of_coprime, gcd_comm, h.even_odd_of_coprime, h.isPrimitiveClassified_of_coprime_of_odd_of_pos, h.symm.isPrimitiveClassified_of_coprime_of_odd_of_pos, h1.right, h2.left, h_f_mem, h_f_mem_pi, h_fo, h_t1, hft1_mem, hn_mem
-/
theorem isPrimitiveClassified_of_coprime_of_pos (hc : Int.gcd x y = 1) (hzpos : 0 < z) :
    h.IsPrimitiveClassified := by
  rcases h.even_odd_of_coprime hc with h1 | h2
  · exact h.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h1.right hzpos
  rw [Int.gcd_comm] at hc
  obtain ⟨m, n, H⟩ := h.symm.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h2.left hzpos
  use m, n; tauto

/--
theorem `isPrimitiveClassified_of_coprime` / 定理 `isPrimitiveClassified_of_coprime`

English:
theorem isPrimitiveClassified_of_coprime
  given: (hc : Int.gcd x y = 1)
  statement: h.IsPrimitiveClassified
  proof: by
  by_cases! hz : 0 < z
  · exact h.isPrimitiveClassified_of_coprime_of_pos hc hz
  have h' : PythagoreanTriple x y (-z) := by simpa [PythagoreanTriple, neg_mul_neg] using h.eq
  apply h'.isPrimitiveClassified_of_coprime_of_pos hc
  apply lt_of_le_of_ne _ (h'.ne_zero_of_coprime hc).symm
  exact le_neg.mp hz

中文:
定理 isPrimitiveClassified_of_coprime
  条件: (hc : 整数.最大公约数 x y = 1)
  结论: h.IsPrimitiveClassified
  证明: by
  by_cases! hz : 0 < z
  · exact h.isPrimitiveClassified_of_coprime_of_pos hc hz
  have h' : PythagoreanTriple x y (-z) := by simpa [PythagoreanTriple, neg_mul_neg] using h.eq
  apply h'.isPrimitiveClassified_of_coprime_of_pos hc
  apply lt_of_le_of_ne _ (h'.ne_zero_of_coprime hc).symm
  exact le_neg.mp hz

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.symm, Finset, Finset.induction, IsMarkovKernel, Kernel, MeasurableSet, PythagoreanTriple, ae_isProbabilityMeasure, classical, eq_or_ne, exists_ae_eq_isMarkovKernel, generateFrom, h.eq, h.isPrimitiveClassified_of_coprime_of_pos, hS_eq_generate, h_ind, h_ind.ae_isProbabilityMeasure, h_rec
-/
theorem isPrimitiveClassified_of_coprime (hc : Int.gcd x y = 1) : h.IsPrimitiveClassified := by
  by_cases! hz : 0 < z
  · exact h.isPrimitiveClassified_of_coprime_of_pos hc hz
  have h' : PythagoreanTriple x y (-z) := by simpa [PythagoreanTriple, neg_mul_neg] using h.eq
  apply h'.isPrimitiveClassified_of_coprime_of_pos hc
  apply lt_of_le_of_ne _ (h'.ne_zero_of_coprime hc).symm
  exact le_neg.mp hz

/--
theorem `classified` / 定理 `classified`

English:
theorem classified
  statement: h.IsClassified
  proof: by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    use 0, 1, 0
    simp [hx, hy]
  apply h.isClassified_of_normalize_isPrimitiveClassified
  apply h.normalize.isPrimitiveClassified_of_coprime
  apply Int.gcd_div_gcd_div_gcd (Nat.pos_of_ne_zero h0)

中文:
定理 classified
  结论: h.IsClassified
  证明: by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    use 0, 1, 0
    simp [hx, hy]
  apply h.isClassified_of_normalize_isPrimitiveClassified
  apply h.normalize.isPrimitiveClassified_of_coprime
  apply Int.gcd_div_gcd_div_gcd (Nat.pos_of_ne_zero h0)

Depends on / 依赖: Int.gcd, Int.gcd_div_gcd_div_gcd, Int.gcd_eq_zero_iff.mp, Nat.pos_of_ne_zero, gcd_div_gcd_div_gcd, gcd_eq_zero_iff, h.isClassified_of_normalize_isPrimitiveClassified, h.normalize.isPrimitiveClassified_of_coprime, isClassified_of_normalize_isPrimitiveClassified, isPrimitiveClassified_of_coprime, normalize, pos_of_ne_zero
-/
theorem classified : h.IsClassified := by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    use 0, 1, 0
    simp [hx, hy]
  apply h.isClassified_of_normalize_isPrimitiveClassified
  apply h.normalize.isPrimitiveClassified_of_coprime
  apply Int.gcd_div_gcd_div_gcd (Nat.pos_of_ne_zero h0)

/--
theorem `coprime_classification` / 定理 `coprime_classification`

English:
theorem coprime_classification
  proof: by
  constructor
  · intro h
    obtain ⟨m, n, H⟩ := h.left.isPrimitiveClassified_of_coprime h.right
    use m, n
    rcases H with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co, pp⟩
    · refine ⟨Or.inl ⟨rfl, rfl⟩, ?_, co, pp⟩
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq]; rw [← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_, co, pp⟩
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq]; rw [← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
  · delta PythagoreanTriple
    rintro ⟨m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl, co, pp⟩ <;>
      first
      | constructor; ring; exact coprime_sq_sub_mul co pp
      | constructor; ring; rw [Int.gcd_comm]; exact coprime_sq_sub_mul co pp

中文:
定理 coprime_classification
  证明: by
  constructor
  · intro h
    obtain ⟨m, n, H⟩ := h.left.isPrimitiveClassified_of_coprime h.right
    use m, n
    rcases H with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co, pp⟩
    · refine ⟨Or.inl ⟨rfl, rfl⟩, ?_, co, pp⟩
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq]; rw [← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_, co, pp⟩
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq]; rw [← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
  · delta PythagoreanTriple
    rintro ⟨m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl, co, pp⟩ <;>
      first
      | constructor; ring; exact coprime_sq_sub_mul co pp
      | constructor; ring; rw [Int.gcd_comm]; exact coprime_sq_sub_mul co pp

Depends on / 依赖: Or.inl, Or.inr, PythagoreanTriple, eq_or_eq_neg_of_sq_eq_sq, h.left.eq, h.left.isPrimitiveClassified_of_coprime, h.right, iIndep, iIndep.iIndepSets, iIndepSets, isPrimitiveClassified_of_coprime
-/
theorem coprime_classification :
    PythagoreanTriple x y z ∧ Int.gcd x y = 1 ↔
      exists m n,
        (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
          (z = m ^ 2 + n ^ 2 ∨ z = -(m ^ 2 + n ^ 2)) ∧
            Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by
  constructor
  · intro h
    obtain ⟨m, n, H⟩ := h.left.isPrimitiveClassified_of_coprime h.right
    use m, n
    rcases H with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co, pp⟩
    · refine ⟨Or.inl ⟨rfl, rfl⟩, ?_, co, pp⟩
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq]; rw [← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_, co, pp⟩
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq]; rw [← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
  · delta PythagoreanTriple
    rintro ⟨m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl, co, pp⟩ <;>
      first
      | constructor; ring; exact coprime_sq_sub_mul co pp
      | constructor; ring; rw [Int.gcd_comm]; exact coprime_sq_sub_mul co pp

/--
theorem `coprime_classification'` / 定理 `coprime_classification'`

English:
theorem coprime_classification'
  statement: {x y z : Int} (h : PythagoreanTriple x y z)
  proof: by
  obtain ⟨m, n, ht1, ht2, ht3, ht4⟩ :=
    PythagoreanTriple.coprime_classification.mp (And.intro h h_coprime)
  rcases le_or_gt 0 m with hm | hm
  · use m, n
    rcases ht1 with h_odd | h_even
    · apply And.intro h_odd.1
      apply And.intro h_odd.2
      rcases ht2 with h_pos | h_neg
      · apply And.intro h_pos (And.intro ht3 (And.intro ht4 hm))
      · exfalso
        revert h_pos
        rw [h_neg]
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (by positivity)))
    exfalso
    rcases h_even with ⟨rfl, -⟩
    rw [mul_assoc]; rw [Int.mul_emod_right] at h_parity
    exact zero_ne_one h_parity
  · use -m, -n
    rcases ht1 with h_odd | h_even
    · rw [neg_sq m]
      rw [neg_sq n]
      apply And.intro h_odd.1
      constructor
      · rw [h_odd.2]
        ring
      rcases ht2 with h_pos | h_neg
      · apply And.intro h_pos
        constructor
        · delta Int.gcd
          rw [Int.natAbs_neg]; rw [Int.natAbs_neg]
          exact ht3
        · rw [Int.neg_emod_two, Int.neg_emod_two]
          apply And.intro ht4
          lia
      · exfalso
        revert h_pos
        rw [h_neg]
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (by positivity)))
    exfalso
    rcases h_even with ⟨rfl, -⟩
    rw [mul_assoc]; rw [Int.mul_emod_right] at h_parity
    exact zero_ne_one h_parity

中文:
定理 coprime_classification'
  结论: {x y z : 整数} (h : PythagoreanTriple x y z)
  证明: by
  obtain ⟨m, n, ht1, ht2, ht3, ht4⟩ :=
    PythagoreanTriple.coprime_classification.mp (And.intro h h_coprime)
  rcases le_or_gt 0 m with hm | hm
  · use m, n
    rcases ht1 with h_odd | h_even
    · apply And.intro h_odd.1
      apply And.intro h_odd.2
      rcases ht2 with h_pos | h_neg
      · apply And.intro h_pos (And.intro ht3 (And.intro ht4 hm))
      · exfalso
        revert h_pos
        rw [h_neg]
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (by positivity)))
    exfalso
    rcases h_even with ⟨rfl, -⟩
    rw [mul_assoc]; rw [Int.mul_emod_right] at h_parity
    exact zero_ne_one h_parity
  · use -m, -n
    rcases ht1 with h_odd | h_even
    · rw [neg_sq m]
      rw [neg_sq n]
      apply And.intro h_odd.1
      constructor
      · rw [h_odd.2]
        ring
      rcases ht2 with h_pos | h_neg
      · apply And.intro h_pos
        constructor
        · delta Int.gcd
          rw [Int.natAbs_neg]; rw [Int.natAbs_neg]
          exact ht3
        · rw [Int.neg_emod_two, Int.neg_emod_two]
          apply And.intro ht4
          lia
      · exfalso
        revert h_pos
        rw [h_neg]
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (by positivity)))
    exfalso
    rcases h_even with ⟨rfl, -⟩
    rw [mul_assoc]; rw [Int.mul_emod_right] at h_parity
    exact zero_ne_one h_parity

Depends on / 依赖: And.intro, Int.mul_emod_right, PythagoreanTriple, PythagoreanTriple.coprime_classification.mp, coprime_classification, h_coprime, h_even, h_neg, h_odd, h_pos, imp_false, imp_false.mpr, le_or_gt, mul_assoc, mul_emod_right, neg_nonpos, neg_nonpos.mpr, not_lt, not_lt.mpr, revert
-/
theorem coprime_classification' {x y z : Int} (h : PythagoreanTriple x y z)
    (h_coprime : Int.gcd x y = 1) (h_parity : x % 2 = 1) (h_pos : 0 < z) :
    exists m n,
      x = m ^ 2 - n ^ 2 ∧
        y = 2 * m * n ∧
          z = m ^ 2 + n ^ 2 ∧
            Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 <= m := by
  obtain ⟨m, n, ht1, ht2, ht3, ht4⟩ :=
    PythagoreanTriple.coprime_classification.mp (And.intro h h_coprime)
  rcases le_or_gt 0 m with hm | hm
  · use m, n
    rcases ht1 with h_odd | h_even
    · apply And.intro h_odd.1
      apply And.intro h_odd.2
      rcases ht2 with h_pos | h_neg
      · apply And.intro h_pos (And.intro ht3 (And.intro ht4 hm))
      · exfalso
        revert h_pos
        rw [h_neg]
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (by positivity)))
    exfalso
    rcases h_even with ⟨rfl, -⟩
    rw [mul_assoc]; rw [Int.mul_emod_right] at h_parity
    exact zero_ne_one h_parity
  · use -m, -n
    rcases ht1 with h_odd | h_even
    · rw [neg_sq m]
      rw [neg_sq n]
      apply And.intro h_odd.1
      constructor
      · rw [h_odd.2]
        ring
      rcases ht2 with h_pos | h_neg
      · apply And.intro h_pos
        constructor
        · delta Int.gcd
          rw [Int.natAbs_neg]; rw [Int.natAbs_neg]
          exact ht3
        · rw [Int.neg_emod_two, Int.neg_emod_two]
          apply And.intro ht4
          lia
      · exfalso
        revert h_pos
        rw [h_neg]
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (by positivity)))
    exfalso
    rcases h_even with ⟨rfl, -⟩
    rw [mul_assoc]; rw [Int.mul_emod_right] at h_parity
    exact zero_ne_one h_parity

/--
theorem `classification` / 定理 `classification`

English:
theorem classification
  proof: by
  constructor
  · intro h
    obtain ⟨k, m, n, H⟩ := h.classified
    use k, m, n
    rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq]; rw [← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq]; rw [← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
  · rintro ⟨k, m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl⟩ <;> delta PythagoreanTriple <;> ring

中文:
定理 classification
  证明: by
  constructor
  · intro h
    obtain ⟨k, m, n, H⟩ := h.classified
    use k, m, n
    rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq]; rw [← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq]; rw [← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
  · rintro ⟨k, m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl⟩ <;> delta PythagoreanTriple <;> ring

Depends on / 依赖: Or.inl, Or.inr, PythagoreanTriple, classified, eq_or_eq_neg_of_sq_eq_sq, h.classified, h.eq, iIndepSet_iff_meas_biInter, meas_biInter
-/
theorem classification :
    PythagoreanTriple x y z ↔
      exists k m n,
        (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
            x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
          (z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2)) := by
  constructor
  · intro h
    obtain ⟨k, m, n, H⟩ := h.classified
    use k, m, n
    rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq]; rw [← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq]; rw [← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
  · rintro ⟨k, m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl⟩ <;> delta PythagoreanTriple <;> ring

end PythagoreanTriple
