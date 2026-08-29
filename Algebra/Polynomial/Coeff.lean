/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Theory of univariate polynomials

The theorems include formulas for computing coefficients, such as
`coeff_add`, `coeff_sum`, `coeff_mul`

-/

@[expose] public section


noncomputable section

open Finsupp Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : Nat}
variable [Semiring R] {p q r : R[X]}

section Coeff

@[simp]
/--
theorem `coeff_add` / 定理 `coeff_add`

English:
theorem coeff_add
  given: (p q : R[X]) (n : Nat)
  statement: coeff (p + q) n = coeff p n + coeff q n
  proof: by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp_rw [← ofFinsupp_add, coeff]
  exact Finsupp.add_apply _ _ _

@[simp]

中文:
定理 coeff_add
  条件: (p q : R[X]) (n : 自然数)
  结论: coeff (p + q) n = coeff p n + coeff q n
  证明: by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp_rw [← ofFinsupp_add, coeff]
  exact Finsupp.add_apply _ _ _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.add_apply, add_apply, ofFinsupp_add, simp_rw
-/
theorem coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n = coeff p n + coeff q n := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp_rw [← ofFinsupp_add, coeff]
  exact Finsupp.add_apply _ _ _

@[simp]
/--
theorem `coeff_smul` / 定理 `coeff_smul`

English:
theorem coeff_smul
  given: [SMulZeroClass S R] (r : S) (p : R[X]) (n : Nat)
  proof: by
  rfl

中文:
定理 coeff_smul
  条件: [SMulZero类 S R] (r : S) (p : R[X]) (n : 自然数)
  证明: by
  rfl
-/
theorem coeff_smul [SMulZeroClass S R] (r : S) (p : R[X]) (n : Nat) :
    coeff (r • p) n = r • coeff p n := by
  rfl

/--
theorem `support_smul` / 定理 `support_smul`

English:
theorem support_smul
  given: [SMulZeroClass S R] (r : S) (p : R[X])
  proof: by
  intro i hi
  rw [mem_support_iff] at hi ⊢
  contrapose hi
  simp [hi]

中文:
定理 support_smul
  条件: [SMulZero类 S R] (r : S) (p : R[X])
  证明: by
  intro i hi
  rw [mem_support_iff] at hi ⊢
  contrapose hi
  simp [hi]

Depends on / 依赖: contrapose, mem_support_iff
-/
theorem support_smul [SMulZeroClass S R] (r : S) (p : R[X]) :
    support (r • p) subseteq support p := by
  intro i hi
  rw [mem_support_iff] at hi ⊢
  contrapose hi
  simp [hi]

open scoped Pointwise in
/--
theorem `card_support_mul_le` / 定理 `card_support_mul_le`

English:
theorem card_support_mul_le
  statement: #(p * q).support <= #p.support * #q.support
  proof: by
  calc #(p * q).support
    _ = #(p.toFinsupp * q.toFinsupp).coeff.support := by rw [← support_toFinsupp, toFinsupp_mul]
    _ <= #(p.toFinsupp.coeff.support + q.toFinsupp.coeff.support) := by
      grw [AddMonoidAlgebra.support_coeff_mul_subset]
    _ <= #p.support * #q.support := Finset.card_im

中文:
定理 card_support_mul_le
  结论: #(p * q).support <= #p.support * #q.support
  证明: by
  calc #(p * q).support
    _ = #(p.toFinsupp * q.toFinsupp).coeff.support := by rw [← support_toFinsupp, toFinsupp_mul]
    _ <= #(p.toFinsupp.coeff.support + q.toFinsupp.coeff.support) := by
      grw [AddMonoidAlgebra.support_coeff_mul_subset]
    _ <= #p.support * #q.support := Finset.card_im

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.support_coeff_mul_subset, Finset, Finset.card_image, coeff.support, p.support, p.toFinsupp, p.toFinsupp.coeff.support, q.support, q.toFinsupp, q.toFinsupp.coeff.support, support, support_coeff_mul_subset, support_toFinsupp, toFinsupp, toFinsupp_mul
-/
theorem card_support_mul_le : #(p * q).support <= #p.support * #q.support := by
  calc #(p * q).support
    _ = #(p.toFinsupp * q.toFinsupp).coeff.support := by rw [← support_toFinsupp, toFinsupp_mul]
    _ <= #(p.toFinsupp.coeff.support + q.toFinsupp.coeff.support) := by
      grw [AddMonoidAlgebra.support_coeff_mul_subset]
    _ <= #p.support * #q.support := Finset.card_image₂_le ..

set_option backward.isDefEq.respectTransparency false in
/-- `Polynomial.sum` as a linear map. -/
@[simps]
/--
Definition of `lsum` / `lsum` 的定义

English:
definition lsum
  signature: {R A M : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [Module R A] [Module R M]
  body: p.sum (f · ·)
  map_add' p q := sum_add_index p q _ (fun n => (f n).map_zero) fun n _ _ => (f n).map_add _ _
  map_smul' c p := by
    rw [sum_eq_of_subset (f · ·) (fun n => (f n).map_zero) (support_smul c p)]
    simp only [sum_def, Finset.smul_sum, coeff_smul, map_smul, RingHom.id_apply]

中文:
定义 lsum
  签名: {R A M : 类型} [半环 R] [半环 A] [加法交换幺半群 M] [模 R A] [模 R M]
  定义体: p.sum (f · ·)
  map_add' p q := sum_add_index p q _ (fun n => (f n).map_zero) fun n _ _ => (f n).map_add _ _
  map_smul' c p := by
    rw [sum_eq_of_subset (f · ·) (fun n => (f n).map_zero) (support_smul c p)]
    simp only [sum_def, Finset.smul_sum, coeff_smul, map_smul, RingHom.id_apply]

Depends on / 依赖: p.sum
-/
def lsum {R A M : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [Module R A] [Module R M]
    (f : Nat -> A ->ₗ[R] M) : A[X] ->ₗ[R] M where
  toFun p := p.sum (f · ·)
  map_add' p q := sum_add_index p q _ (fun n => (f n).map_zero) fun n _ _ => (f n).map_add _ _
  map_smul' c p := by
    rw [sum_eq_of_subset (f · ·) (fun n => (f n).map_zero) (support_smul c p)]
    simp only [sum_def, Finset.smul_sum, coeff_smul, map_smul, RingHom.id_apply]

variable (R) in
/--
Definition of `lcoeff` / `lcoeff` 的定义

English:
definition lcoeff
  signature: (n : Nat)
  body: coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n

@[simp]

中文:
定义 lcoeff
  签名: (n : 自然数)
  定义体: coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n

@[simp]
-/
def lcoeff (n : Nat) : R[X] ->ₗ[R] R where
  toFun p := coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n

@[simp]
/--
theorem `lcoeff_apply` / 定理 `lcoeff_apply`

English:
theorem lcoeff_apply
  given: (n : Nat) (f : R[X])
  statement: lcoeff R n f = coeff f n
  proof: rfl

@[simp]

中文:
定理 lcoeff_apply
  条件: (n : 自然数) (f : R[X])
  结论: lcoeff R n f = coeff f n
  证明: rfl

@[simp]
-/
theorem lcoeff_apply (n : Nat) (f : R[X]) : lcoeff R n f = coeff f n :=
  rfl

@[simp]
/--
theorem `finsetSum_coeff` / 定理 `finsetSum_coeff`

English:
theorem finsetSum_coeff
  given: {ι : Type*} (s : Finset ι) (f : ι -> R[X]) (n : Nat)
  proof: map_sum (lcoeff R n) _ _

@[deprecated (since := "2026-04-08")] alias finset_sum_coeff := finsetSum_coeff

中文:
定理 finsetSum_coeff
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> R[X]) (n : 自然数)
  证明: map_sum (lcoeff R n) _ _

@[deprecated (since := "2026-04-08")] alias finset_sum_coeff := finsetSum_coeff

Depends on / 依赖: lcoeff, map_sum
-/
theorem finsetSum_coeff {ι : Type*} (s : Finset ι) (f : ι -> R[X]) (n : Nat) :
    coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n :=
  map_sum (lcoeff R n) _ _

@[deprecated (since := "2026-04-08")] alias finset_sum_coeff := finsetSum_coeff

/--
lemma `coeff_list_sum` / 引理 `coeff_list_sum`

English:
lemma coeff_list_sum
  given: (l : List R[X]) (n : Nat)
  proof: map_list_sum (lcoeff R n) _

中文:
引理 coeff_list_sum
  条件: (l : 列表 R[X]) (n : 自然数)
  证明: map_list_sum (lcoeff R n) _

Depends on / 依赖: lcoeff, map_list_sum
-/
lemma coeff_list_sum (l : List R[X]) (n : Nat) :
    l.sum.coeff n = (l.map (lcoeff R n)).sum :=
  map_list_sum (lcoeff R n) _

/--
lemma `coeff_list_sum_map` / 引理 `coeff_list_sum_map`

English:
lemma coeff_list_sum_map
  given: {ι : Type*} (l : List ι) (f : ι -> R[X]) (n : Nat)
  proof: by
  simp_rw [coeff_list_sum, List.map_map, Function.comp_def, lcoeff_apply]

@[simp]

中文:
引理 coeff_list_sum_map
  条件: {ι : 类型} (l : 列表 ι) (f : ι -> R[X]) (n : 自然数)
  证明: by
  simp_rw [coeff_list_sum, List.map_map, Function.comp_def, lcoeff_apply]

@[simp]

Depends on / 依赖: Function, Function.comp_def, List.map_map, coeff_list_sum, comp_def, lcoeff_apply, map_map, simp_rw
-/
lemma coeff_list_sum_map {ι : Type*} (l : List ι) (f : ι -> R[X]) (n : Nat) :
    (l.map f).sum.coeff n = (l.map (fun a => (f a).coeff n)).sum := by
  simp_rw [coeff_list_sum, List.map_map, Function.comp_def, lcoeff_apply]

@[simp]
/--
theorem `coeff_sum` / 定理 `coeff_sum`

English:
theorem coeff_sum
  given: [Semiring S] (n : Nat) (f : Nat -> R -> S[X])
  proof: by
  simp [Polynomial.sum]

中文:
定理 coeff_sum
  条件: [半环 S] (n : 自然数) (f : 自然数 -> R -> S[X])
  证明: by
  simp [Polynomial.sum]

Depends on / 依赖: Polynomial, Polynomial.sum
-/
theorem coeff_sum [Semiring S] (n : Nat) (f : Nat -> R -> S[X]) :
    coeff (p.sum f) n = p.sum fun a b => coeff (f a b) n := by
  simp [Polynomial.sum]

/--
theorem `coeff_mul` / 定理 `coeff_mul`

English:
theorem coeff_mul
  given: (p q : R[X]) (n : Nat)
  proof: by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp_rw [← ofFinsupp_mul, coeff]
  exact AddMonoidAlgebra.coeff_mul_antidiag p q n _ Finset.mem_antidiagonal

@[simp]

中文:
定理 coeff_mul
  条件: (p q : R[X]) (n : 自然数)
  证明: by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp_rw [← ofFinsupp_mul, coeff]
  exact AddMonoidAlgebra.coeff_mul_antidiag p q n _ Finset.mem_antidiagonal

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff_mul_antidiag, Finset, Finset.mem_antidiagonal, coeff_mul_antidiag, mem_antidiagonal, ofFinsupp_mul, simp_rw
-/
theorem coeff_mul (p q : R[X]) (n : Nat) :
    coeff (p * q) n = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2 := by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp_rw [← ofFinsupp_mul, coeff]
  exact AddMonoidAlgebra.coeff_mul_antidiag p q n _ Finset.mem_antidiagonal

@[simp]
/--
theorem `mul_coeff_zero` / 定理 `mul_coeff_zero`

English:
theorem mul_coeff_zero
  given: (p q : R[X])
  statement: coeff (p * q) 0 = coeff p 0 * coeff q 0
  proof: by simp [coeff_mul]

中文:
定理 mul_coeff_zero
  条件: (p q : R[X])
  结论: coeff (p * q) 0 = coeff p 0 * coeff q 0
  证明: by simp [coeff_mul]

Depends on / 依赖: coeff_mul
-/
theorem mul_coeff_zero (p q : R[X]) : coeff (p * q) 0 = coeff p 0 * coeff q 0 := by simp [coeff_mul]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_coeff_one` / 定理 `mul_coeff_one`

English:
theorem mul_coeff_one
  given: (p q : R[X])
  proof: by
  rw [coeff_mul]; rw [Nat.antidiagonal_eq_map]
  simp [sum_range_succ]

中文:
定理 mul_coeff_one
  条件: (p q : R[X])
  证明: by
  rw [coeff_mul]; rw [Nat.antidiagonal_eq_map]
  simp [sum_range_succ]

Depends on / 依赖: Nat.antidiagonal_eq_map, antidiagonal_eq_map, coeff_mul, sum_range_succ
-/
theorem mul_coeff_one (p q : R[X]) :
    coeff (p * q) 1 = coeff p 0 * coeff q 1 + coeff p 1 * coeff q 0 := by
  rw [coeff_mul]; rw [Nat.antidiagonal_eq_map]
  simp [sum_range_succ]

/-- `constantCoeff p` returns the constant term of the polynomial `p`,
  defined as `coeff p 0`. This is a ring homomorphism. -/
@[simps]
/--
Definition of `constantCoeff` / `constantCoeff` 的定义

English:
definition constantCoeff
  signature: : R[X] ->+* R where
  body: coeff p 0
  map_one' := coeff_one_zero
  map_mul' := mul_coeff_zero
  map_zero' := coeff_zero 0
  map_add' p q := coeff_add p q 0

中文:
定义 constantCoeff
  签名: : R[X] ->+* R where
  定义体: coeff p 0
  map_one' := coeff_one_zero
  map_mul' := mul_coeff_zero
  map_zero' := coeff_zero 0
  map_add' p q := coeff_add p q 0
-/
def constantCoeff : R[X] ->+* R where
  toFun p := coeff p 0
  map_one' := coeff_one_zero
  map_mul' := mul_coeff_zero
  map_zero' := coeff_zero 0
  map_add' p q := coeff_add p q 0

/--
lemma `constantCoeff_surjective` / 引理 `constantCoeff_surjective`

English:
lemma constantCoeff_surjective
  statement: Function.Surjective (constantCoeff (R := R))
  proof: fun x => ⟨C x, by simp⟩

中文:
引理 constantCoeff_surjective
  结论: 函数.满射 (constantCoeff (R := R))
  证明: fun x => ⟨C x, by simp⟩
-/
lemma constantCoeff_surjective : Function.Surjective (constantCoeff (R := R)) :=
  fun x => ⟨C x, by simp⟩

/--
theorem `isUnit_C` / 定理 `isUnit_C`

English:
theorem isUnit_C
  given: {x : R}
  statement: IsUnit (C x) ↔ IsUnit x
  proof: ⟨fun h => (congr_arg IsUnit coeff_C_zero).mp (h.map <| @constantCoeff R _), fun h => h.map C⟩

中文:
定理 isUnit_C
  条件: {x : R}
  结论: 是单位 (C x) ↔ 是单位 x
  证明: ⟨fun h => (congr_arg IsUnit coeff_C_zero).mp (h.map <| @constantCoeff R _), fun h => h.map C⟩

Depends on / 依赖: IsUnit, coeff_C_zero, congr_arg, constantCoeff, h.map
-/
theorem isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x :=
  ⟨fun h => (congr_arg IsUnit coeff_C_zero).mp (h.map <| @constantCoeff R _), fun h => h.map C⟩

/--
theorem `coeff_mul_X_zero` / 定理 `coeff_mul_X_zero`

English:
theorem coeff_mul_X_zero
  given: (p : R[X])
  statement: coeff (p * X) 0 = 0
  proof: by simp

中文:
定理 coeff_mul_X_zero
  条件: (p : R[X])
  结论: coeff (p * X) 0 = 0
  证明: by simp
-/
theorem coeff_mul_X_zero (p : R[X]) : coeff (p * X) 0 = 0 := by simp

/--
theorem `coeff_X_mul_zero` / 定理 `coeff_X_mul_zero`

English:
theorem coeff_X_mul_zero
  given: (p : R[X])
  statement: coeff (X * p) 0 = 0
  proof: by simp

中文:
定理 coeff_X_mul_zero
  条件: (p : R[X])
  结论: coeff (X * p) 0 = 0
  证明: by simp
-/
theorem coeff_X_mul_zero (p : R[X]) : coeff (X * p) 0 = 0 := by simp

/--
theorem `coeff_C_mul_X_pow` / 定理 `coeff_C_mul_X_pow`

English:
theorem coeff_C_mul_X_pow
  given: (x : R) (k n : Nat)
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [coeff_monomial]
  simp [eq_comm]

中文:
定理 coeff_C_mul_X_pow
  条件: (x : R) (k n : 自然数)
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [coeff_monomial]
  simp [eq_comm]

Depends on / 依赖: C_mul_X_pow_eq_monomial, coeff_monomial, eq_comm
-/
theorem coeff_C_mul_X_pow (x : R) (k n : Nat) :
    coeff (C x * X ^ k : R[X]) n = if n = k then x else 0 := by
  rw [C_mul_X_pow_eq_monomial]; rw [coeff_monomial]
  simp [eq_comm]

/--
theorem `coeff_C_mul_X` / 定理 `coeff_C_mul_X`

English:
theorem coeff_C_mul_X
  given: (x : R) (n : Nat)
  statement: coeff (C x * X : R[X]) n = if n = 1 then x else 0
  proof: by
  rw [← pow_one X]; rw [coeff_C_mul_X_pow]

@[simp, grind =]

中文:
定理 coeff_C_mul_X
  条件: (x : R) (n : 自然数)
  结论: coeff (C x * X : R[X]) n = if n = 1 then x else 0
  证明: by
  rw [← pow_one X]; rw [coeff_C_mul_X_pow]

@[simp, grind =]

Depends on / 依赖: coeff_C_mul_X_pow, pow_one
-/
theorem coeff_C_mul_X (x : R) (n : Nat) : coeff (C x * X : R[X]) n = if n = 1 then x else 0 := by
  rw [← pow_one X]; rw [coeff_C_mul_X_pow]

@[simp, grind =]
/--
theorem `coeff_C_mul` / 定理 `coeff_C_mul`

English:
theorem coeff_C_mul
  given: (p : R[X])
  statement: coeff (C a * p) n = a * coeff p n
  proof: by
  rcases p with ⟨p⟩
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  exact p.coeff_single_zero_mul a n

中文:
定理 coeff_C_mul
  条件: (p : R[X])
  结论: coeff (C a * p) n = a * coeff p n
  证明: by
  rcases p with ⟨p⟩
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  exact p.coeff_single_zero_mul a n

Depends on / 依赖: coeff_single_zero_mul, monomial_zero_left, ofFinsupp_mul, ofFinsupp_single, p.coeff_single_zero_mul, simp_rw
-/
theorem coeff_C_mul (p : R[X]) : coeff (C a * p) n = a * coeff p n := by
  rcases p with ⟨p⟩
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  exact p.coeff_single_zero_mul a n

/--
theorem `C_mul'` / 定理 `C_mul'`

English:
theorem C_mul'
  given: (a : R) (f : R[X])
  statement: C a * f = a • f
  proof: by
  ext
  rw [coeff_C_mul]; rw [coeff_smul]; rw [smul_eq_mul]

@[simp]

中文:
定理 C_mul'
  条件: (a : R) (f : R[X])
  结论: C a * f = a • f
  证明: by
  ext
  rw [coeff_C_mul]; rw [coeff_smul]; rw [smul_eq_mul]

@[simp]

Depends on / 依赖: coeff_C_mul, coeff_smul, smul_eq_mul
-/
theorem C_mul' (a : R) (f : R[X]) : C a * f = a • f := by
  ext
  rw [coeff_C_mul]; rw [coeff_smul]; rw [smul_eq_mul]

@[simp]
/--
theorem `coeff_mul_C` / 定理 `coeff_mul_C`

English:
theorem coeff_mul_C
  given: (p : R[X]) (n : Nat) (a : R)
  statement: coeff (p * C a) n = coeff p n * a
  proof: by
  rcases p with ⟨p⟩
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  exact p.coeff_mul_single_zero a n

中文:
定理 coeff_mul_C
  条件: (p : R[X]) (n : 自然数) (a : R)
  结论: coeff (p * C a) n = coeff p n * a
  证明: by
  rcases p with ⟨p⟩
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  exact p.coeff_mul_single_zero a n

Depends on / 依赖: coeff_mul_single_zero, monomial_zero_left, ofFinsupp_mul, ofFinsupp_single, p.coeff_mul_single_zero, simp_rw
-/
theorem coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff (p * C a) n = coeff p n * a := by
  rcases p with ⟨p⟩
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  exact p.coeff_mul_single_zero a n

/--
lemma `coeff_mul_natCast` / 引理 `coeff_mul_natCast`

English:
lemma coeff_mul_natCast
  given: {a k : Nat}
  proof: coeff_mul_C _ _ _

中文:
引理 coeff_mul_natCast
  条件: {a k : 自然数}
  证明: coeff_mul_C _ _ _
-/
@[simp] lemma coeff_mul_natCast {a k : Nat} :
    coeff (p * (a : R[X])) k = coeff p k * (↑a : R) := coeff_mul_C _ _ _

/--
lemma `coeff_natCast_mul` / 引理 `coeff_natCast_mul`

English:
lemma coeff_natCast_mul
  given: {a k : Nat}
  proof: coeff_C_mul _

中文:
引理 coeff_natCast_mul
  条件: {a k : 自然数}
  证明: coeff_C_mul _
-/
@[simp] lemma coeff_natCast_mul {a k : Nat} :
    coeff ((a : R[X]) * p) k = a * coeff p k := coeff_C_mul _

/--
lemma `coeff_mul_ofNat` / 引理 `coeff_mul_ofNat`

English:
lemma coeff_mul_ofNat
  given: {a k : Nat} [Nat.AtLeastTwo a]
  proof: coeff_mul_C _ _ _

中文:
引理 coeff_mul_of自然数
  条件: {a k : 自然数} [自然数.AtLeastTwo a]
  证明: coeff_mul_C _ _ _
-/
@[simp] lemma coeff_mul_ofNat {a k : Nat} [Nat.AtLeastTwo a] :
    coeff (p * (ofNat(a) : R[X])) k = coeff p k * ofNat(a) := coeff_mul_C _ _ _

/--
lemma `coeff_ofNat_mul` / 引理 `coeff_ofNat_mul`

English:
lemma coeff_ofNat_mul
  given: {a k : Nat} [Nat.AtLeastTwo a]
  proof: coeff_C_mul _

中文:
引理 coeff_of自然数_mul
  条件: {a k : 自然数} [自然数.AtLeastTwo a]
  证明: coeff_C_mul _
-/
@[simp] lemma coeff_ofNat_mul {a k : Nat} [Nat.AtLeastTwo a] :
    coeff ((ofNat(a) : R[X]) * p) k = ofNat(a) * coeff p k := coeff_C_mul _

/--
lemma `coeff_mul_intCast` / 引理 `coeff_mul_intCast`

English:
lemma coeff_mul_intCast
  given: [Ring S] {p : S[X]} {a : Int} {k : Nat}
  proof: coeff_mul_C _ _ _

中文:
引理 coeff_mul_intCast
  条件: [环 S] {p : S[X]} {a : 整数} {k : 自然数}
  证明: coeff_mul_C _ _ _
-/
@[simp] lemma coeff_mul_intCast [Ring S] {p : S[X]} {a : Int} {k : Nat} :
    coeff (p * (a : S[X])) k = coeff p k * (↑a : S) := coeff_mul_C _ _ _

/--
lemma `coeff_intCast_mul` / 引理 `coeff_intCast_mul`

English:
lemma coeff_intCast_mul
  given: [Ring S] {p : S[X]} {a : Int} {k : Nat}
  proof: coeff_C_mul _

@[simp, grind =]

中文:
引理 coeff_intCast_mul
  条件: [环 S] {p : S[X]} {a : 整数} {k : 自然数}
  证明: coeff_C_mul _

@[simp, grind =]
-/
@[simp] lemma coeff_intCast_mul [Ring S] {p : S[X]} {a : Int} {k : Nat} :
    coeff ((a : S[X]) * p) k = a * coeff p k := coeff_C_mul _

@[simp, grind =]
/--
theorem `coeff_X_pow` / 定理 `coeff_X_pow`

English:
theorem coeff_X_pow
  given: (k n : Nat)
  statement: coeff (X ^ k : R[X]) n = if n = k then 1 else 0
  proof: by
  simp only [one_mul, map_one, ← coeff_C_mul_X_pow]

中文:
定理 coeff_X_pow
  条件: (k n : 自然数)
  结论: coeff (X ^ k : R[X]) n = if n = k then 1 else 0
  证明: by
  simp only [one_mul, map_one, ← coeff_C_mul_X_pow]

Depends on / 依赖: coeff_C_mul_X_pow, map_one, one_mul
-/
theorem coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n = if n = k then 1 else 0 := by
  simp only [one_mul, map_one, ← coeff_C_mul_X_pow]

/--
theorem `coeff_X_pow_self` / 定理 `coeff_X_pow_self`

English:
theorem coeff_X_pow_self
  given: (n : Nat)
  statement: coeff (X ^ n : R[X]) n = 1
  proof: by simp

中文:
定理 coeff_X_pow_self
  条件: (n : 自然数)
  结论: coeff (X ^ n : R[X]) n = 1
  证明: by simp
-/
theorem coeff_X_pow_self (n : Nat) : coeff (X ^ n : R[X]) n = 1 := by simp

section Fewnomials

open Finset

/--
theorem `support_binomial` / 定理 `support_binomial`

English:
theorem support_binomial
  given: {k m : Nat} (hkm : k != m) {x y : R} (hx : x != 0) (hy : y != 0)
  proof: by
  apply subset_antisymm (support_binomial_subset k m x y)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm, if_neg hkm.symm, mul_zero, zero_add,
    add_zero, Ne, hx, hy, not_false_eq_true, and_true

中文:
定理 support_binomial
  条件: {k m : 自然数} (hkm : k != m) {x y : R} (hx : x != 0) (hy : y != 0)
  证明: by
  apply subset_antisymm (support_binomial_subset k m x y)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm, if_neg hkm.symm, mul_zero, zero_add,
    add_zero, Ne, hx, hy, not_false_eq_true, and_true

Depends on / 依赖: add_zero, and_true, coeff_C_mul, coeff_X_pow, coeff_X_pow_self, coeff_add, hkm.symm, if_neg, insert_subset_iff, mem_support_iff, mul_one, mul_zero, not_false_eq_true, simp_rw, singleton_subset_iff, subset_antisymm, support_binomial_subset, zero_add
-/
theorem support_binomial {k m : Nat} (hkm : k != m) {x y : R} (hx : x != 0) (hy : y != 0) :
    support (C x * X ^ k + C y * X ^ m) = {k, m} := by
  apply subset_antisymm (support_binomial_subset k m x y)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm, if_neg hkm.symm, mul_zero, zero_add,
    add_zero, Ne, hx, hy, not_false_eq_true, and_true]

/--
theorem `support_trinomial` / 定理 `support_trinomial`

English:
theorem support_trinomial
  statement: {k m n : Nat} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x != 0)
  proof: by
  apply subset_antisymm (support_trinomial_subset k m n x y z)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne,
    if_neg hmn.ne', if_neg (hkm.trans hmn).ne, if_n

中文:
定理 support_trinomial
  结论: {k m n : 自然数} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x != 0)
  证明: by
  apply subset_antisymm (support_trinomial_subset k m n x y z)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne,
    if_neg hmn.ne', if_neg (hkm.trans hmn).ne, if_n

Depends on / 依赖: add_zero, and_true, coeff_C_mul, coeff_X_pow, coeff_X_pow_self, coeff_add, hkm.ne, hkm.trans, hmn.ne, if_neg, insert_subset_iff, mem_support_iff, mul_one, mul_zero, not_false_eq_true, simp_rw, singleton_subset_iff, subset_antisymm, support_trinomial_subset, zero_add
-/
theorem support_trinomial {k m n : Nat} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x != 0)
    (hy : y != 0) (hz : z != 0) :
    support (C x * X ^ k + C y * X ^ m + C z * X ^ n) = {k, m, n} := by
  apply subset_antisymm (support_trinomial_subset k m n x y z)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne,
    if_neg hmn.ne', if_neg (hkm.trans hmn).ne, if_neg (hkm.trans hmn).ne', mul_zero, add_zero,
    zero_add, Ne, hx, hy, hz, not_false_eq_true, and_true]

/--
theorem `card_support_binomial` / 定理 `card_support_binomial`

English:
theorem card_support_binomial
  given: {k m : Nat} (h : k != m) {x y : R} (hx : x != 0) (hy : y != 0)
  proof: by
  rw [support_binomial h hx hy]; rw [card_insert_of_notMem (mt mem_singleton.mp h)]; rw [card_singleton]

中文:
定理 card_support_binomial
  条件: {k m : 自然数} (h : k != m) {x y : R} (hx : x != 0) (hy : y != 0)
  证明: by
  rw [support_binomial h hx hy]; rw [card_insert_of_notMem (mt mem_singleton.mp h)]; rw [card_singleton]

Depends on / 依赖: card_insert_of_notMem, card_singleton, mem_singleton, mem_singleton.mp, support_binomial
-/
theorem card_support_binomial {k m : Nat} (h : k != m) {x y : R} (hx : x != 0) (hy : y != 0) :
    #(support (C x * X ^ k + C y * X ^ m)) = 2 := by
  rw [support_binomial h hx hy]; rw [card_insert_of_notMem (mt mem_singleton.mp h)]; rw [card_singleton]

/--
theorem `card_support_trinomial` / 定理 `card_support_trinomial`

English:
theorem card_support_trinomial
  statement: {k m n : Nat} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x != 0)
  proof: by
  rw [support_trinomial hkm hmn hx hy hz]; rw [card_insert_of_notMem
      (mt mem_insert.mp (not_or_intro hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne)))]; rw [card_insert_of_notMem (mt mem_singleton.mp hmn.ne)]; rw [card_singleton]

中文:
定理 card_support_trinomial
  结论: {k m n : 自然数} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x != 0)
  证明: by
  rw [support_trinomial hkm hmn hx hy hz]; rw [card_insert_of_notMem
      (mt mem_insert.mp (not_or_intro hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne)))]; rw [card_insert_of_notMem (mt mem_singleton.mp hmn.ne)]; rw [card_singleton]

Depends on / 依赖: card_insert_of_notMem, card_singleton, hkm.ne, hkm.trans, hmn.ne, mem_insert, mem_insert.mp, mem_singleton, mem_singleton.mp, not_or_intro, support_trinomial
-/
theorem card_support_trinomial {k m n : Nat} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x != 0)
    (hy : y != 0) (hz : z != 0) : #(support (C x * X ^ k + C y * X ^ m + C z * X ^ n)) = 3 := by
  rw [support_trinomial hkm hmn hx hy hz]; rw [card_insert_of_notMem
      (mt mem_insert.mp (not_or_intro hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne)))]; rw [card_insert_of_notMem (mt mem_singleton.mp hmn.ne)]; rw [card_singleton]

end Fewnomials

@[simp]
/--
theorem `coeff_mul_X_pow` / 定理 `coeff_mul_X_pow`

English:
theorem coeff_mul_X_pow
  given: (p : R[X]) (n d : Nat)
  proof: by
  rw [coeff_mul]; rw [Finset.sum_eq_single (d]; rw [n)]; rw [coeff_X_pow]; rw [if_pos rfl]; rw [mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    grind [mem_antidiagonal]
  · grind [mem_antidiagonal]

@[simp]

中文:
定理 coeff_mul_X_pow
  条件: (p : R[X]) (n d : 自然数)
  证明: by
  rw [coeff_mul]; rw [Finset.sum_eq_single (d]; rw [n)]; rw [coeff_X_pow]; rw [if_pos rfl]; rw [mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    grind [mem_antidiagonal]
  · grind [mem_antidiagonal]

@[simp]

Depends on / 依赖: Finset, Finset.sum_eq_single, coeff_X_pow, coeff_mul, if_neg, if_pos, mem_antidiagonal, mul_one, mul_zero, sum_eq_single
-/
theorem coeff_mul_X_pow (p : R[X]) (n d : Nat) :
    coeff (p * Polynomial.X ^ n) (d + n) = coeff p d := by
  rw [coeff_mul]; rw [Finset.sum_eq_single (d]; rw [n)]; rw [coeff_X_pow]; rw [if_pos rfl]; rw [mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    grind [mem_antidiagonal]
  · grind [mem_antidiagonal]

@[simp]
/--
theorem `coeff_X_pow_mul` / 定理 `coeff_X_pow_mul`

English:
theorem coeff_X_pow_mul
  given: (p : R[X]) (n d : Nat)
  proof: by
  rw [(commute_X_pow p n).eq]; rw [coeff_mul_X_pow]

中文:
定理 coeff_X_pow_mul
  条件: (p : R[X]) (n d : 自然数)
  证明: by
  rw [(commute_X_pow p n).eq]; rw [coeff_mul_X_pow]

Depends on / 依赖: coeff_mul_X_pow, commute_X_pow
-/
theorem coeff_X_pow_mul (p : R[X]) (n d : Nat) :
    coeff (Polynomial.X ^ n * p) (d + n) = coeff p d := by
  rw [(commute_X_pow p n).eq]; rw [coeff_mul_X_pow]

/--
theorem `coeff_mul_X_pow'` / 定理 `coeff_mul_X_pow'`

English:
theorem coeff_mul_X_pow'
  given: (p : R[X]) (n d : Nat)
  proof: by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h

中文:
定理 coeff_mul_X_pow'
  条件: (p : R[X]) (n d : 自然数)
  证明: by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h

Depends on / 依赖: Finset, Finset.sum_eq_zero, add_tsub_cancel_right, coeff_X_pow, coeff_mul, coeff_mul_X_pow, if_neg, le_of_add_le_right, mem_antidiagonal, mem_antidiagonal.mp, mul_zero, not_le, not_le.mp, split_ifs, sum_eq_zero, trans_lt, tsub_add_cancel_of_le
-/
theorem coeff_mul_X_pow' (p : R[X]) (n d : Nat) :
    (p * X ^ n).coeff d = ite (n <= d) (p.coeff (d - n)) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne

/--
theorem `coeff_X_pow_mul'` / 定理 `coeff_X_pow_mul'`

English:
theorem coeff_X_pow_mul'
  given: (p : R[X]) (n d : Nat)
  proof: by
  rw [(commute_X_pow p n).eq]; rw [coeff_mul_X_pow']

@[simp]

中文:
定理 coeff_X_pow_mul'
  条件: (p : R[X]) (n d : 自然数)
  证明: by
  rw [(commute_X_pow p n).eq]; rw [coeff_mul_X_pow']

@[simp]

Depends on / 依赖: coeff_mul_X_pow, commute_X_pow
-/
theorem coeff_X_pow_mul' (p : R[X]) (n d : Nat) :
    (X ^ n * p).coeff d = ite (n <= d) (p.coeff (d - n)) 0 := by
  rw [(commute_X_pow p n).eq]; rw [coeff_mul_X_pow']

@[simp]
/--
theorem `coeff_mul_X` / 定理 `coeff_mul_X`

English:
theorem coeff_mul_X
  given: (p : R[X]) (n : Nat)
  statement: coeff (p * X) (n + 1) = coeff p n
  proof: by
  simpa only [pow_one] using coeff_mul_X_pow p 1 n

@[simp]

中文:
定理 coeff_mul_X
  条件: (p : R[X]) (n : 自然数)
  结论: coeff (p * X) (n + 1) = coeff p n
  证明: by
  simpa only [pow_one] using coeff_mul_X_pow p 1 n

@[simp]

Depends on / 依赖: coeff_mul_X_pow, pow_one
-/
theorem coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X) (n + 1) = coeff p n := by
  simpa only [pow_one] using coeff_mul_X_pow p 1 n

@[simp]
/--
theorem `coeff_X_mul` / 定理 `coeff_X_mul`

English:
theorem coeff_X_mul
  given: (p : R[X]) (n : Nat)
  statement: coeff (X * p) (n + 1) = coeff p n
  proof: by
  rw [(commute_X p).eq]; rw [coeff_mul_X]

中文:
定理 coeff_X_mul
  条件: (p : R[X]) (n : 自然数)
  结论: coeff (X * p) (n + 1) = coeff p n
  证明: by
  rw [(commute_X p).eq]; rw [coeff_mul_X]

Depends on / 依赖: coeff_mul_X, commute_X
-/
theorem coeff_X_mul (p : R[X]) (n : Nat) : coeff (X * p) (n + 1) = coeff p n := by
  rw [(commute_X p).eq]; rw [coeff_mul_X]

/--
theorem `coeff_mul_monomial` / 定理 `coeff_mul_monomial`

English:
theorem coeff_mul_monomial
  given: (p : R[X]) (n d : Nat) (r : R)
  proof: by
  rw [← C_mul_X_pow_eq_monomial]; rw [← X_pow_mul]; rw [← mul_assoc]; rw [coeff_mul_C]; rw [coeff_mul_X_pow]

中文:
定理 coeff_mul_monomial
  条件: (p : R[X]) (n d : 自然数) (r : R)
  证明: by
  rw [← C_mul_X_pow_eq_monomial]; rw [← X_pow_mul]; rw [← mul_assoc]; rw [coeff_mul_C]; rw [coeff_mul_X_pow]

Depends on / 依赖: C_mul_X_pow_eq_monomial, X_pow_mul, coeff_mul_C, coeff_mul_X_pow, mul_assoc
-/
theorem coeff_mul_monomial (p : R[X]) (n d : Nat) (r : R) :
    coeff (p * monomial n r) (d + n) = coeff p d * r := by
  rw [← C_mul_X_pow_eq_monomial]; rw [← X_pow_mul]; rw [← mul_assoc]; rw [coeff_mul_C]; rw [coeff_mul_X_pow]

/--
theorem `coeff_monomial_mul` / 定理 `coeff_monomial_mul`

English:
theorem coeff_monomial_mul
  given: (p : R[X]) (n d : Nat) (r : R)
  proof: by
  rw [← C_mul_X_pow_eq_monomial]; rw [mul_assoc]; rw [coeff_C_mul]; rw [X_pow_mul]; rw [coeff_mul_X_pow]

中文:
定理 coeff_monomial_mul
  条件: (p : R[X]) (n d : 自然数) (r : R)
  证明: by
  rw [← C_mul_X_pow_eq_monomial]; rw [mul_assoc]; rw [coeff_C_mul]; rw [X_pow_mul]; rw [coeff_mul_X_pow]

Depends on / 依赖: C_mul_X_pow_eq_monomial, X_pow_mul, coeff_C_mul, coeff_mul_X_pow, mul_assoc
-/
theorem coeff_monomial_mul (p : R[X]) (n d : Nat) (r : R) :
    coeff (monomial n r * p) (d + n) = r * coeff p d := by
  rw [← C_mul_X_pow_eq_monomial]; rw [mul_assoc]; rw [coeff_C_mul]; rw [X_pow_mul]; rw [coeff_mul_X_pow]

-- This can already be proved by `simp`.
/--
theorem `coeff_mul_monomial_zero` / 定理 `coeff_mul_monomial_zero`

English:
theorem coeff_mul_monomial_zero
  given: (p : R[X]) (d : Nat) (r : R)
  proof: coeff_mul_monomial p 0 d r

中文:
定理 coeff_mul_monomial_zero
  条件: (p : R[X]) (d : 自然数) (r : R)
  证明: coeff_mul_monomial p 0 d r

Depends on / 依赖: coeff_mul_monomial
-/
theorem coeff_mul_monomial_zero (p : R[X]) (d : Nat) (r : R) :
    coeff (p * monomial 0 r) d = coeff p d * r :=
  coeff_mul_monomial p 0 d r

-- This can already be proved by `simp`.
/--
theorem `coeff_monomial_zero_mul` / 定理 `coeff_monomial_zero_mul`

English:
theorem coeff_monomial_zero_mul
  given: (p : R[X]) (d : Nat) (r : R)
  proof: coeff_monomial_mul p 0 d r

中文:
定理 coeff_monomial_zero_mul
  条件: (p : R[X]) (d : 自然数) (r : R)
  证明: coeff_monomial_mul p 0 d r

Depends on / 依赖: coeff_monomial_mul
-/
theorem coeff_monomial_zero_mul (p : R[X]) (d : Nat) (r : R) :
    coeff (monomial 0 r * p) d = r * coeff p d :=
  coeff_monomial_mul p 0 d r

/--
theorem `mul_X_pow_eq_zero` / 定理 `mul_X_pow_eq_zero`

English:
theorem mul_X_pow_eq_zero
  given: {p : R[X]} {n : Nat} (H : p * X ^ n = 0)
  statement: p = 0
  proof: ext fun k => (coeff_mul_X_pow p n k).symm.trans ext_iff.1 H (k + n)

中文:
定理 mul_X_pow_eq_zero
  条件: {p : R[X]} {n : 自然数} (H : p * X ^ n = 0)
  结论: p = 0
  证明: ext fun k => (coeff_mul_X_pow p n k).symm.trans ext_iff.1 H (k + n)

Depends on / 依赖: coeff_mul_X_pow, ext_iff, symm.trans
-/
theorem mul_X_pow_eq_zero {p : R[X]} {n : Nat} (H : p * X ^ n = 0) : p = 0 :=
ext fun k => (coeff_mul_X_pow p n k).symm.trans ext_iff.1 H (k + n)

/--
theorem `isRegular_X_pow` / 定理 `isRegular_X_pow`

English:
theorem isRegular_X_pow
  given: (n : Nat)
  statement: IsRegular (X ^ n : R[X])
  proof: by
  suffices IsLeftRegular (X ^ n : R[X]) from
    ⟨this, this.right_of_commute (fun p => commute_X_pow p n)⟩
  intro P Q (hPQ : X ^ n * P = X ^ n * Q)
  ext i
  rw [← coeff_X_pow_mul P n i]; rw [hPQ]; rw [coeff_X_pow_mul Q n i]

中文:
定理 isRegular_X_pow
  条件: (n : 自然数)
  结论: 是正则 (X ^ n : R[X])
  证明: by
  suffices IsLeftRegular (X ^ n : R[X]) from
    ⟨this, this.right_of_commute (fun p => commute_X_pow p n)⟩
  intro P Q (hPQ : X ^ n * P = X ^ n * Q)
  ext i
  rw [← coeff_X_pow_mul P n i]; rw [hPQ]; rw [coeff_X_pow_mul Q n i]

Depends on / 依赖: IsLeftRegular, coeff_X_pow_mul, commute_X_pow, right_of_commute, this.right_of_commute
-/
theorem isRegular_X_pow (n : Nat) : IsRegular (X ^ n : R[X]) := by
  suffices IsLeftRegular (X ^ n : R[X]) from
    ⟨this, this.right_of_commute (fun p => commute_X_pow p n)⟩
  intro P Q (hPQ : X ^ n * P = X ^ n * Q)
  ext i
  rw [← coeff_X_pow_mul P n i]; rw [hPQ]; rw [coeff_X_pow_mul Q n i]

/--
theorem `isRegular_X` / 定理 `isRegular_X`

English:
theorem isRegular_X
  statement: IsRegular (X : R[X])
  proof: pow_one (X : R[X]) ▸ isRegular_X_pow 1

中文:
定理 isRegular_X
  结论: 是正则 (X : R[X])
  证明: pow_one (X : R[X]) ▸ isRegular_X_pow 1
-/
@[simp] theorem isRegular_X : IsRegular (X : R[X]) := pow_one (X : R[X]) ▸ isRegular_X_pow 1

/--
theorem `coeff_X_add_C_pow` / 定理 `coeff_X_add_C_pow`

English:
theorem coeff_X_add_C_pow
  given: (r : R) (n k : Nat)
  proof: by
  rw [(commute_X (C r : R[X])).add_pow, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, ← C_eq_natCast, ← C_pow, coeff_mul_C]
  rw [Finset.sum_eq_single k]; rw [coeff_X_pow_self]; rw [one_mul]
  · intro _ _ h
    simp [coeff_X_pow, h.symm]
  · simp only [coeff_X_pow_self, one_mul, not_lt, Fin

中文:
定理 coeff_X_add_C_pow
  条件: (r : R) (n k : 自然数)
  证明: by
  rw [(commute_X (C r : R[X])).add_pow, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, ← C_eq_natCast, ← C_pow, coeff_mul_C]
  rw [Finset.sum_eq_single k]; rw [coeff_X_pow_self]; rw [one_mul]
  · intro _ _ h
    simp [coeff_X_pow, h.symm]
  · simp only [coeff_X_pow_self, one_mul, not_lt, Fin

Depends on / 依赖: C_eq_natCast, C_pow, Finset, Finset.mem_range, Finset.sum_eq_single, Nat.cast_zero, Nat.choose_eq_zero_of_lt, add_pow, cast_zero, choose_eq_zero_of_lt, coeff_X_pow, coeff_X_pow_self, coeff_mul_C, commute_X, h.symm, lcoeff_apply, map_sum, mem_range, mul_zero, not_lt
-/
theorem coeff_X_add_C_pow (r : R) (n k : Nat) :
    ((X + C r) ^ n).coeff k = r ^ (n - k) * (n.choose k : R) := by
  rw [(commute_X (C r : R[X])).add_pow, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, ← C_eq_natCast, ← C_pow, coeff_mul_C]
  rw [Finset.sum_eq_single k]; rw [coeff_X_pow_self]; rw [one_mul]
  · intro _ _ h
    simp [coeff_X_pow, h.symm]
  · simp only [coeff_X_pow_self, one_mul, not_lt, Finset.mem_range]
    intro h
    rw [Nat.choose_eq_zero_of_lt h]; rw [Nat.cast_zero]; rw [mul_zero]

/--
theorem `coeff_X_add_one_pow` / 定理 `coeff_X_add_one_pow`

English:
theorem coeff_X_add_one_pow
  given: (R : Type*) [Semiring R] (n k : Nat)
  proof: by rw [← C_1, coeff_X_add_C_pow, one_pow, one_mul]

中文:
定理 coeff_X_add_one_pow
  条件: (R : 类型) [半环 R] (n k : 自然数)
  证明: by rw [← C_1, coeff_X_add_C_pow, one_pow, one_mul]

Depends on / 依赖: coeff_X_add_C_pow, one_mul, one_pow
-/
theorem coeff_X_add_one_pow (R : Type*) [Semiring R] (n k : Nat) :
    ((X + 1) ^ n).coeff k = (n.choose k : R) := by rw [← C_1, coeff_X_add_C_pow, one_pow, one_mul]

/--
theorem `coeff_one_add_X_pow` / 定理 `coeff_one_add_X_pow`

English:
theorem coeff_one_add_X_pow
  given: (R : Type*) [Semiring R] (n k : Nat)
  proof: by rw [add_comm _ X, coeff_X_add_one_pow]

中文:
定理 coeff_one_add_X_pow
  条件: (R : 类型) [半环 R] (n k : 自然数)
  证明: by rw [add_comm _ X, coeff_X_add_one_pow]

Depends on / 依赖: add_comm, coeff_X_add_one_pow
-/
theorem coeff_one_add_X_pow (R : Type*) [Semiring R] (n k : Nat) :
    ((1 + X) ^ n).coeff k = (n.choose k : R) := by rw [add_comm _ X, coeff_X_add_one_pow]

/--
theorem `one_add_X_pow_sub_X_pow` / 定理 `one_add_X_pow_sub_X_pow`

English:
theorem one_add_X_pow_sub_X_pow
  given: {S : Type*} [CommRing S] (d : Nat)
  proof: by
  ext i
  simp [Polynomial.coeff_one_add_X_pow]
  split_ifs <;> simp_all [Nat.choose_eq_zero_of_lt, lt_iff_le_and_ne]

中文:
定理 one_add_X_pow_sub_X_pow
  条件: {S : 类型} [交换环 S] (d : 自然数)
  证明: by
  ext i
  simp [Polynomial.coeff_one_add_X_pow]
  split_ifs <;> simp_all [Nat.choose_eq_zero_of_lt, lt_iff_le_and_ne]

Depends on / 依赖: Nat.choose_eq_zero_of_lt, Polynomial, Polynomial.coeff_one_add_X_pow, choose_eq_zero_of_lt, coeff_one_add_X_pow, lt_iff_le_and_ne, split_ifs
-/
theorem one_add_X_pow_sub_X_pow {S : Type*} [CommRing S] (d : Nat) :
    (1 + X : S[X]) ^ d - X ^ d = ∑ i in range d, d.choose i • X ^ i := by
  ext i
  simp [Polynomial.coeff_one_add_X_pow]
  split_ifs <;> simp_all [Nat.choose_eq_zero_of_lt, lt_iff_le_and_ne]

/--
theorem `C_dvd_iff_dvd_coeff` / 定理 `C_dvd_iff_dvd_coeff`

English:
theorem C_dvd_iff_dvd_coeff
  given: (r : R) (φ : R[X])
  statement: C r ∣ φ ↔ forall i, r ∣ φ.coeff i
  proof: by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose c hc using h
    classical
      let c' : Nat -> R := fun i => if i in φ.support then c i else 0
      let ψ : R[X] := ∑ i in φ.support, monomial i (c' i)
      use ψ
      ext i
      simp onl

中文:
定理 C_dvd_iff_dvd_coeff
  条件: (r : R) (φ : R[X])
  结论: C r ∣ φ ↔ 对任意 i, r ∣ φ.coeff i
  证明: by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose c hc using h
    classical
      let c' : Nat -> R := fun i => if i in φ.support then c i else 0
      let ψ : R[X] := ∑ i in φ.support, monomial i (c' i)
      use ψ
      ext i
      simp onl

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.sum_ite_eq, classical, coeff_C_mul, coeff_monomial, dvd_mul_right, finsetSum_coeff, mem_support_iff, monomial, mul_zero, not_not, split_ifs, sum_ite_eq, support
-/
theorem C_dvd_iff_dvd_coeff (r : R) (φ : R[X]) : C r ∣ φ ↔ forall i, r ∣ φ.coeff i := by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose c hc using h
    classical
      let c' : Nat -> R := fun i => if i in φ.support then c i else 0
      let ψ : R[X] := ∑ i in φ.support, monomial i (c' i)
      use ψ
      ext i
      simp only [c', ψ, coeff_C_mul, mem_support_iff, coeff_monomial, finsetSum_coeff,
        Finset.sum_ite_eq']
      split_ifs with hi
      · rw [hc]
      · rw [Classical.not_not] at hi
        rwa [mul_zero]

/--
theorem `smul_eq_C_mul` / 定理 `smul_eq_C_mul`

English:
theorem smul_eq_C_mul
  given: (a : R)
  statement: a • p = C a * p
  proof: by simp [ext_iff]

中文:
定理 smul_eq_C_mul
  条件: (a : R)
  结论: a • p = C a * p
  证明: by simp [ext_iff]

Depends on / 依赖: ext_iff
-/
theorem smul_eq_C_mul (a : R) : a • p = C a * p := by simp [ext_iff]

/--
theorem `update_eq_add_sub_coeff` / 定理 `update_eq_add_sub_coeff`

English:
theorem update_eq_add_sub_coeff
  given: {R : Type*} [Ring R] (p : R[X]) (n : Nat) (a : R)
  proof: by
  ext
  rw [coeff_update_apply]; rw [coeff_add]; rw [coeff_C_mul_X_pow]
  split_ifs with h <;> simp [h]

中文:
定理 update_eq_add_sub_coeff
  条件: {R : 类型} [环 R] (p : R[X]) (n : 自然数) (a : R)
  证明: by
  ext
  rw [coeff_update_apply]; rw [coeff_add]; rw [coeff_C_mul_X_pow]
  split_ifs with h <;> simp [h]

Depends on / 依赖: coeff_C_mul_X_pow, coeff_add, coeff_update_apply, split_ifs
-/
theorem update_eq_add_sub_coeff {R : Type*} [Ring R] (p : R[X]) (n : Nat) (a : R) :
    p.update n a = p + Polynomial.C (a - p.coeff n) * Polynomial.X ^ n := by
  ext
  rw [coeff_update_apply]; rw [coeff_add]; rw [coeff_C_mul_X_pow]
  split_ifs with h <;> simp [h]

end Coeff

section cast

/--
theorem `natCast_coeff_zero` / 定理 `natCast_coeff_zero`

English:
theorem natCast_coeff_zero
  given: {n : Nat} {R : Type*} [Semiring R]
  statement: (n : R[X]).coeff 0 = n
  proof: by
  simp only [coeff_natCast_ite, ite_true]

@[norm_cast]

中文:
定理 natCast_coeff_zero
  条件: {n : 自然数} {R : 类型} [半环 R]
  结论: (n : R[X]).coeff 0 = n
  证明: by
  simp only [coeff_natCast_ite, ite_true]

@[norm_cast]

Depends on / 依赖: coeff_natCast_ite, ite_true
-/
theorem natCast_coeff_zero {n : Nat} {R : Type*} [Semiring R] : (n : R[X]).coeff 0 = n := by
  simp only [coeff_natCast_ite, ite_true]

@[norm_cast]
/--
theorem `natCast_inj` / 定理 `natCast_inj`

English:
theorem natCast_inj
  given: {m n : Nat} {R : Type*} [Semiring R] [CharZero R]
  proof: by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

@[simp]

中文:
定理 natCast_inj
  条件: {m n : 自然数} {R : 类型} [半环 R] [特征零 R]
  证明: by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

@[simp]

Depends on / 依赖: apply_fun, p.coeff
-/
theorem natCast_inj {m n : Nat} {R : Type*} [Semiring R] [CharZero R] :
    (↑m : R[X]) = ↑n ↔ m = n := by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

@[simp]
/--
theorem `intCast_coeff_zero` / 定理 `intCast_coeff_zero`

English:
theorem intCast_coeff_zero
  given: {i : Int} {R : Type*} [Ring R]
  statement: (i : R[X]).coeff 0 = i
  proof: by
  cases i <;> simp

@[norm_cast]

中文:
定理 intCast_coeff_zero
  条件: {i : 整数} {R : 类型} [环 R]
  结论: (i : R[X]).coeff 0 = i
  证明: by
  cases i <;> simp

@[norm_cast]
-/
theorem intCast_coeff_zero {i : Int} {R : Type*} [Ring R] : (i : R[X]).coeff 0 = i := by
  cases i <;> simp

@[norm_cast]
/--
theorem `intCast_inj` / 定理 `intCast_inj`

English:
theorem intCast_inj
  given: {m n : Int} {R : Type*} [Ring R] [CharZero R]
  statement: (↑m : R[X]) = ↑n ↔ m = n
  proof: by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

中文:
定理 intCast_inj
  条件: {m n : 整数} {R : 类型} [环 R] [特征零 R]
  结论: (↑m : R[X]) = ↑n ↔ m = n
  证明: by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

Depends on / 依赖: apply_fun, p.coeff
-/
theorem intCast_inj {m n : Int} {R : Type*} [Ring R] [CharZero R] : (↑m : R[X]) = ↑n ↔ m = n := by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

end cast

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: [CharZero R]
  body: natCast_inj.mp

中文:
实例 charZero
  签名: [特征零 R]
  定义体: natCast_inj.mp

Depends on / 依赖: natCast_inj, natCast_inj.mp
-/
instance charZero [CharZero R] : CharZero R[X] where cast_injective _x _y := natCast_inj.mp

/--
Instance `charP` / 实例 `charP`

English:
instance charP
  signature: {p : Nat} [CharP R p]
  body: by
    rw [← CharP.cast_eq_zero_iff R]; rw [← C_inj (R := R)]; rw [map_natCast]; rw [C_0]

中文:
实例 charP
  签名: {p : 自然数} [特征p R p]
  定义体: by
    rw [← CharP.cast_eq_zero_iff R]; rw [← C_inj (R := R)]; rw [map_natCast]; rw [C_0]

Depends on / 依赖: C_inj, CharP.cast_eq_zero_iff, Semiring, Semiring.toGrindSemiring, cast_eq_zero_iff, map_natCast, toGrindSemiring
-/
instance charP {p : Nat} [CharP R p] : CharP R[X] p where
  cast_eq_zero_iff n := by
    rw [← CharP.cast_eq_zero_iff R]; rw [← C_inj (R := R)]; rw [map_natCast]; rw [C_0]

end Polynomial
