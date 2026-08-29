/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Lemmas on integer matrices

Here we collect some results about matrices over `ℚ` and `ℤ`.

## Main definitions and results

* `Matrix.num`, `Matrix.den`: express a rational matrix `A` as the quotient of an integer matrix
  by a (non-zero) natural.

## TODO

Consider generalizing these constructions to matrices over localizations of rings (or semirings).
-/

@[expose] public section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]


/--
lemma `map_mul_natCast` / 引理 `map_mul_natCast`

English:
lemma map_mul_natCast
  given: {α : Type*} [NonAssocSemiring α] (A B : Matrix n n Nat)
  proof: Matrix.map_mul (f := Nat.castRingHom α)

中文:
引理 map_mul_natCast
  条件: {α : 类型} [非结合半环 α] (A B : 矩阵 n n 自然数)
  证明: Matrix.map_mul (f := Nat.castRingHom α)

Depends on / 依赖: Matrix, Matrix.map_mul, Nat.castRingHom, castRingHom, map_mul
-/
lemma map_mul_natCast {α : Type*} [NonAssocSemiring α] (A B : Matrix n n Nat) :
    map (A * B) ((↑) : Nat -> α) = map A (↑) * map B (↑) :=
  Matrix.map_mul (f := Nat.castRingHom α)

/--
lemma `map_mul_intCast` / 引理 `map_mul_intCast`

English:
lemma map_mul_intCast
  given: {α : Type*} [NonAssocRing α] (A B : Matrix n n Int)
  proof: Matrix.map_mul (f := Int.castRingHom α)

中文:
引理 map_mul_intCast
  条件: {α : 类型} [非结合环 α] (A B : 矩阵 n n 整数)
  证明: Matrix.map_mul (f := Int.castRingHom α)

Depends on / 依赖: Int.castRingHom, Matrix, Matrix.map_mul, castRingHom, map_mul
-/
lemma map_mul_intCast {α : Type*} [NonAssocRing α] (A B : Matrix n n Int) :
    map (A * B) ((↑) : Int -> α) = map A (↑) * map B (↑) :=
  Matrix.map_mul (f := Int.castRingHom α)

/--
lemma `map_mul_ratCast` / 引理 `map_mul_ratCast`

English:
lemma map_mul_ratCast
  given: {α : Type*} [DivisionRing α] [CharZero α] (A B : Matrix n n Rat)
  proof: Matrix.map_mul (f := Rat.castHom α)

中文:
引理 map_mul_ratCast
  条件: {α : 类型} [除环 α] [特征零 α] (A B : 矩阵 n n 有理数)
  证明: Matrix.map_mul (f := Rat.castHom α)

Depends on / 依赖: Matrix, Matrix.map_mul, Rat.castHom, castHom, map_mul
-/
lemma map_mul_ratCast {α : Type*} [DivisionRing α] [CharZero α] (A B : Matrix n n Rat) :
    map (A * B) ((↑) : Rat -> α) = map A (↑) * map B (↑) :=
  Matrix.map_mul (f := Rat.castHom α)

/-!
## Denominator of a rational matrix
-/

/--
Definition of `den` / `den` 的定义

English:
definition den
  signature: (A : Matrix m n Rat)
  body: Finset.univ.lcm (fun P : m × n => (A P.1 P.2).den)

中文:
定义 den
  签名: (A : 矩阵 m n 有理数)
  定义体: Finset.univ.lcm (fun P : m × n => (A P.1 P.2).den)
-/
protected def den (A : Matrix m n Rat) : Nat := Finset.univ.lcm (fun P : m × n => (A P.1 P.2).den)

/--
Definition of `num` / `num` 的定义

English:
definition num
  signature: (A : Matrix m n Rat)
  body: ((A.den : Rat) • A).map Rat.num

中文:
定义 num
  签名: (A : 矩阵 m n 有理数)
  定义体: ((A.den : Rat) • A).map Rat.num
-/
protected def num (A : Matrix m n Rat) : Matrix m n Int := ((A.den : Rat) • A).map Rat.num

/--
lemma `den_ne_zero` / 引理 `den_ne_zero`

English:
lemma den_ne_zero
  given: (A : Matrix m n Rat)
  statement: A.den != 0
  proof: by
  simp [Matrix.den, Finset.lcm_eq_zero_iff]

中文:
引理 den_ne_zero
  条件: (A : 矩阵 m n 有理数)
  结论: A.den != 0
  证明: by
  simp [Matrix.den, Finset.lcm_eq_zero_iff]

Depends on / 依赖: Finset, Finset.lcm_eq_zero_iff, Matrix, Matrix.den, lcm_eq_zero_iff
-/
lemma den_ne_zero (A : Matrix m n Rat) : A.den != 0 := by
  simp [Matrix.den, Finset.lcm_eq_zero_iff]

/--
lemma `num_eq_zero_iff` / 引理 `num_eq_zero_iff`

English:
lemma num_eq_zero_iff
  given: (A : Matrix m n Rat)
  statement: A.num = 0 ↔ A = 0
  proof: by
  simp [Matrix.num, ← ext_iff, A.den_ne_zero]

中文:
引理 num_eq_zero_iff
  条件: (A : 矩阵 m n 有理数)
  结论: A.num = 0 ↔ A = 0
  证明: by
  simp [Matrix.num, ← ext_iff, A.den_ne_zero]

Depends on / 依赖: A.den_ne_zero, Matrix, Matrix.num, den_ne_zero, ext_iff
-/
lemma num_eq_zero_iff (A : Matrix m n Rat) : A.num = 0 ↔ A = 0 := by
  simp [Matrix.num, ← ext_iff, A.den_ne_zero]

/--
lemma `den_dvd_iff` / 引理 `den_dvd_iff`

English:
lemma den_dvd_iff
  given: {A : Matrix m n Rat} {r : Nat}
  proof: by
  simp [Matrix.den]

中文:
引理 den_dvd_iff
  条件: {A : 矩阵 m n 有理数} {r : 自然数}
  证明: by
  simp [Matrix.den]

Depends on / 依赖: Matrix, Matrix.den
-/
lemma den_dvd_iff {A : Matrix m n Rat} {r : Nat} :
    A.den ∣ r ↔ forall i j, (A i j).den ∣ r := by
  simp [Matrix.den]

/--
lemma `num_div_den` / 引理 `num_div_den`

English:
lemma num_div_den
  given: (A : Matrix m n Rat) (i : m) (j : n)
  proof: by
  obtain ⟨k, hk⟩ := den_dvd_iff.mp (dvd_refl A.den) i j
  rw [Matrix.num]; rw [map_apply]; rw [smul_apply]; rw [smul_eq_mul]; rw [mul_comm]; rw [div_eq_iff Nat.cast_ne_zero.mpr A.den_ne_zero]; rw [hk]; rw [Nat.cast_mul]; rw [← mul_assoc]; rw [Rat.mul_den_eq_num]; rw [← Int.cast_natCast k]; rw [← 

中文:
引理 num_div_den
  条件: (A : 矩阵 m n 有理数) (i : m) (j : n)
  证明: by
  obtain ⟨k, hk⟩ := den_dvd_iff.mp (dvd_refl A.den) i j
  rw [Matrix.num]; rw [map_apply]; rw [smul_apply]; rw [smul_eq_mul]; rw [mul_comm]; rw [div_eq_iff Nat.cast_ne_zero.mpr A.den_ne_zero]; rw [hk]; rw [Nat.cast_mul]; rw [← mul_assoc]; rw [Rat.mul_den_eq_num]; rw [← Int.cast_natCast k]; rw [← 

Depends on / 依赖: A.den, A.den_ne_zero, Int.cast_mul, Int.cast_natCast, Matrix, Matrix.num, Nat.cast_mul, Nat.cast_ne_zero.mpr, Rat.mul_den_eq_num, Rat.num_intCast, cast_mul, cast_natCast, cast_ne_zero, den_dvd_iff, den_dvd_iff.mp, den_ne_zero, div_eq_iff, dvd_refl, map_apply, mul_assoc
-/
lemma num_div_den (A : Matrix m n Rat) (i : m) (j : n) :
    A.num i j / A.den = A i j := by
  obtain ⟨k, hk⟩ := den_dvd_iff.mp (dvd_refl A.den) i j
  rw [Matrix.num]; rw [map_apply]; rw [smul_apply]; rw [smul_eq_mul]; rw [mul_comm]; rw [div_eq_iff Nat.cast_ne_zero.mpr A.den_ne_zero]; rw [hk]; rw [Nat.cast_mul]; rw [← mul_assoc]; rw [Rat.mul_den_eq_num]; rw [← Int.cast_natCast k]; rw [← Int.cast_mul]; rw [Rat.num_intCast]

/--
lemma `inv_denom_smul_num` / 引理 `inv_denom_smul_num`

English:
lemma inv_denom_smul_num
  given: (A : Matrix m n Rat)
  proof: by
  ext
  simp [← Matrix.num_div_den A, div_eq_inv_mul]

@[simp]

中文:
引理 inv_denom_smul_num
  条件: (A : 矩阵 m n 有理数)
  证明: by
  ext
  simp [← Matrix.num_div_den A, div_eq_inv_mul]

@[simp]

Depends on / 依赖: Matrix, Matrix.num_div_den, div_eq_inv_mul, num_div_den
-/
lemma inv_denom_smul_num (A : Matrix m n Rat) :
    (A.den⁻¹ : Rat) • A.num.map (↑) = A := by
  ext
  simp [← Matrix.num_div_den A, div_eq_inv_mul]

@[simp]
/--
lemma `den_neg` / 引理 `den_neg`

English:
lemma den_neg
  given: (A : Matrix m n Rat)
  statement: (-A).den = A.den
  proof: eq_of_forall_dvd by simp [den_dvd_iff]

@[simp]

中文:
引理 den_neg
  条件: (A : 矩阵 m n 有理数)
  结论: (-A).den = A.den
  证明: eq_of_forall_dvd by simp [den_dvd_iff]

@[simp]

Depends on / 依赖: den_dvd_iff, eq_of_forall_dvd
-/
lemma den_neg (A : Matrix m n Rat) : (-A).den = A.den :=
eq_of_forall_dvd by simp [den_dvd_iff]

@[simp]
/--
lemma `num_neg` / 引理 `num_neg`

English:
lemma num_neg
  given: (A : Matrix m n Rat)
  statement: (-A).num = -A.num
  proof: by
  ext
  simp [Matrix.num]

中文:
引理 num_neg
  条件: (A : 矩阵 m n 有理数)
  结论: (-A).num = -A.num
  证明: by
  ext
  simp [Matrix.num]

Depends on / 依赖: Matrix, Matrix.num
-/
lemma num_neg (A : Matrix m n Rat) : (-A).num = -A.num := by
  ext
  simp [Matrix.num]

/--
lemma `den_transpose` / 引理 `den_transpose`

English:
lemma den_transpose
  given: (A : Matrix m n Rat)
  statement: (Aᵀ).den = A.den
  proof: eq_of_forall_dvd fun _ => by simpa [den_dvd_iff] using forall_comm

中文:
引理 den_transpose
  条件: (A : 矩阵 m n 有理数)
  结论: (Aᵀ).den = A.den
  证明: eq_of_forall_dvd fun _ => by simpa [den_dvd_iff] using forall_comm
-/
@[simp] lemma den_transpose (A : Matrix m n Rat) : (Aᵀ).den = A.den :=
  eq_of_forall_dvd fun _ => by simpa [den_dvd_iff] using forall_comm

/--
lemma `num_transpose` / 引理 `num_transpose`

English:
lemma num_transpose
  given: (A : Matrix m n Rat)
  statement: (Aᵀ).num = (A.num)ᵀ
  proof: by
  ext; simp [Matrix.num]

中文:
引理 num_transpose
  条件: (A : 矩阵 m n 有理数)
  结论: (Aᵀ).num = (A.num)ᵀ
  证明: by
  ext; simp [Matrix.num]
-/
@[simp] lemma num_transpose (A : Matrix m n Rat) : (Aᵀ).num = (A.num)ᵀ := by
  ext; simp [Matrix.num]

/-!
### Compatibility with `map`
-/

@[simp]
/--
lemma `den_map_intCast` / 引理 `den_map_intCast`

English:
lemma den_map_intCast
  given: (A : Matrix m n Int)
  statement: (A.map (↑)).den = 1
  proof: by
  simp [← Nat.dvd_one, Matrix.den_dvd_iff]

@[simp]

中文:
引理 den_map_intCast
  条件: (A : 矩阵 m n 整数)
  结论: (A.map (↑)).den = 1
  证明: by
  simp [← Nat.dvd_one, Matrix.den_dvd_iff]

@[simp]

Depends on / 依赖: Matrix, Matrix.den_dvd_iff, Nat.dvd_one, den_dvd_iff, dvd_one
-/
lemma den_map_intCast (A : Matrix m n Int) : (A.map (↑)).den = 1 := by
  simp [← Nat.dvd_one, Matrix.den_dvd_iff]

@[simp]
/--
lemma `num_map_intCast` / 引理 `num_map_intCast`

English:
lemma num_map_intCast
  given: (A : Matrix m n Int)
  statement: (A.map (↑)).num = A
  proof: by
  simp [Matrix.num, Function.comp_def]

@[simp]

中文:
引理 num_map_intCast
  条件: (A : 矩阵 m n 整数)
  结论: (A.map (↑)).num = A
  证明: by
  simp [Matrix.num, Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Matrix, Matrix.num, comp_def
-/
lemma num_map_intCast (A : Matrix m n Int) : (A.map (↑)).num = A := by
  simp [Matrix.num, Function.comp_def]

@[simp]
/--
lemma `den_map_natCast` / 引理 `den_map_natCast`

English:
lemma den_map_natCast
  given: (A : Matrix m n Nat)
  statement: (A.map (↑)).den = 1
  proof: by
  simp [← Nat.dvd_one, Matrix.den_dvd_iff]

@[simp]

中文:
引理 den_map_natCast
  条件: (A : 矩阵 m n 自然数)
  结论: (A.map (↑)).den = 1
  证明: by
  simp [← Nat.dvd_one, Matrix.den_dvd_iff]

@[simp]

Depends on / 依赖: Matrix, Matrix.den_dvd_iff, Nat.dvd_one, den_dvd_iff, dvd_one
-/
lemma den_map_natCast (A : Matrix m n Nat) : (A.map (↑)).den = 1 := by
  simp [← Nat.dvd_one, Matrix.den_dvd_iff]

@[simp]
/--
lemma `num_map_natCast` / 引理 `num_map_natCast`

English:
lemma num_map_natCast
  given: (A : Matrix m n Nat)
  statement: (A.map (↑)).num = A.map (↑)
  proof: by
  simp [Matrix.num, Function.comp_def]

中文:
引理 num_map_natCast
  条件: (A : 矩阵 m n 自然数)
  结论: (A.map (↑)).num = A.map (↑)
  证明: by
  simp [Matrix.num, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Matrix, Matrix.num, comp_def
-/
lemma num_map_natCast (A : Matrix m n Nat) : (A.map (↑)).num = A.map (↑) := by
  simp [Matrix.num, Function.comp_def]

/-!
### Casts from scalar types
-/

@[simp]
/--
lemma `den_natCast` / 引理 `den_natCast`

English:
lemma den_natCast
  given: [DecidableEq m] (a : Nat)
  statement: (a : Matrix m m Rat).den = 1
  proof: by
  simpa [← diagonal_natCast] using den_map_natCast (a : Matrix m m Nat)

@[simp]

中文:
引理 den_natCast
  条件: [DecidableEq m] (a : 自然数)
  结论: (a : 矩阵 m m 有理数).den = 1
  证明: by
  simpa [← diagonal_natCast] using den_map_natCast (a : Matrix m m Nat)

@[simp]

Depends on / 依赖: Matrix, den_map_natCast, diagonal_natCast
-/
lemma den_natCast [DecidableEq m] (a : Nat) : (a : Matrix m m Rat).den = 1 := by
  simpa [← diagonal_natCast] using den_map_natCast (a : Matrix m m Nat)

@[simp]
/--
lemma `num_natCast` / 引理 `num_natCast`

English:
lemma num_natCast
  given: [DecidableEq m] (a : Nat)
  statement: (a : Matrix m m Rat).num = a
  proof: by
  simpa [← diagonal_natCast] using num_map_natCast (a : Matrix m m Nat)

@[simp]

中文:
引理 num_natCast
  条件: [DecidableEq m] (a : 自然数)
  结论: (a : 矩阵 m m 有理数).num = a
  证明: by
  simpa [← diagonal_natCast] using num_map_natCast (a : Matrix m m Nat)

@[simp]

Depends on / 依赖: Matrix, diagonal_natCast, num_map_natCast
-/
lemma num_natCast [DecidableEq m] (a : Nat) : (a : Matrix m m Rat).num = a := by
  simpa [← diagonal_natCast] using num_map_natCast (a : Matrix m m Nat)

@[simp]
/--
lemma `den_ofNat` / 引理 `den_ofNat`

English:
lemma den_ofNat
  given: [DecidableEq m] (a : Nat) [a.AtLeastTwo]
  proof: den_natCast a

@[simp]

中文:
引理 den_of自然数
  条件: [DecidableEq m] (a : 自然数) [a.AtLeastTwo]
  证明: den_natCast a

@[simp]

Depends on / 依赖: den_natCast
-/
lemma den_ofNat [DecidableEq m] (a : Nat) [a.AtLeastTwo] :
    (ofNat(a) : Matrix m m Rat).den = 1 :=
  den_natCast a

@[simp]
/--
lemma `num_ofNat` / 引理 `num_ofNat`

English:
lemma num_ofNat
  given: [DecidableEq m] (a : Nat) [a.AtLeastTwo]
  proof: num_natCast a

@[simp]

中文:
引理 num_of自然数
  条件: [DecidableEq m] (a : 自然数) [a.AtLeastTwo]
  证明: num_natCast a

@[simp]

Depends on / 依赖: num_natCast
-/
lemma num_ofNat [DecidableEq m] (a : Nat) [a.AtLeastTwo] :
    (ofNat(a) : Matrix m m Rat).num = a :=
  num_natCast a

@[simp]
/--
lemma `den_intCast` / 引理 `den_intCast`

English:
lemma den_intCast
  given: [DecidableEq m] (a : Int)
  statement: (a : Matrix m m Rat).den = 1
  proof: by
  simpa [← diagonal_intCast] using den_map_intCast (a : Matrix m m Int)

@[simp]

中文:
引理 den_intCast
  条件: [DecidableEq m] (a : 整数)
  结论: (a : 矩阵 m m 有理数).den = 1
  证明: by
  simpa [← diagonal_intCast] using den_map_intCast (a : Matrix m m Int)

@[simp]

Depends on / 依赖: Matrix, den_map_intCast, diagonal_intCast
-/
lemma den_intCast [DecidableEq m] (a : Int) : (a : Matrix m m Rat).den = 1 := by
  simpa [← diagonal_intCast] using den_map_intCast (a : Matrix m m Int)

@[simp]
/--
lemma `num_intCast` / 引理 `num_intCast`

English:
lemma num_intCast
  given: [DecidableEq m] (a : Int)
  statement: (a : Matrix m m Rat).num = a
  proof: by
  simpa [← diagonal_intCast] using num_map_intCast (a : Matrix m m Int)

@[simp]

中文:
引理 num_intCast
  条件: [DecidableEq m] (a : 整数)
  结论: (a : 矩阵 m m 有理数).num = a
  证明: by
  simpa [← diagonal_intCast] using num_map_intCast (a : Matrix m m Int)

@[simp]

Depends on / 依赖: Matrix, diagonal_intCast, num_map_intCast
-/
lemma num_intCast [DecidableEq m] (a : Int) : (a : Matrix m m Rat).num = a := by
  simpa [← diagonal_intCast] using num_map_intCast (a : Matrix m m Int)

@[simp]
/--
lemma `den_zero` / 引理 `den_zero`

English:
lemma den_zero
  statement: (0 : Matrix m n Rat).den = 1
  proof: den_map_natCast 0

@[simp]

中文:
引理 den_zero
  结论: (0 : 矩阵 m n 有理数).den = 1
  证明: den_map_natCast 0

@[simp]

Depends on / 依赖: den_map_natCast
-/
lemma den_zero : (0 : Matrix m n Rat).den = 1 :=
  den_map_natCast 0

@[simp]
/--
lemma `num_zero` / 引理 `num_zero`

English:
lemma num_zero
  statement: (0 : Matrix m n Rat).num = 0
  proof: num_map_natCast 0

@[simp]

中文:
引理 num_zero
  结论: (0 : 矩阵 m n 有理数).num = 0
  证明: num_map_natCast 0

@[simp]

Depends on / 依赖: num_map_natCast
-/
lemma num_zero : (0 : Matrix m n Rat).num = 0 :=
  num_map_natCast 0

@[simp]
/--
lemma `den_one` / 引理 `den_one`

English:
lemma den_one
  given: [DecidableEq m]
  statement: (1 : Matrix m m Rat).den = 1
  proof: den_natCast 1

@[simp]

中文:
引理 den_one
  条件: [DecidableEq m]
  结论: (1 : 矩阵 m m 有理数).den = 1
  证明: den_natCast 1

@[simp]

Depends on / 依赖: den_natCast
-/
lemma den_one [DecidableEq m] : (1 : Matrix m m Rat).den = 1 :=
  den_natCast 1

@[simp]
/--
lemma `num_one` / 引理 `num_one`

English:
lemma num_one
  given: [DecidableEq m]
  statement: (1 : Matrix m m Rat).num = 1
  proof: num_natCast 1

中文:
引理 num_one
  条件: [DecidableEq m]
  结论: (1 : 矩阵 m m 有理数).num = 1
  证明: num_natCast 1

Depends on / 依赖: num_natCast
-/
lemma num_one [DecidableEq m] : (1 : Matrix m m Rat).num = 1 :=
  num_natCast 1

end Matrix
