/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Chris Hughes
-/
module

public import Mathlib.Algebra.Order.SuccPred.WithBot
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Split polynomials

A polynomial `f : R[X]` splits if it is a product of constant and monic linear polynomials.

## Main definitions

* `Polynomial.Splits f`: A predicate on a polynomial `f` saying that `f` is a product of
  constant and monic linear polynomials.

-/

@[expose] public section

variable {R : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

/--
Definition of `Splits` / `Splits` 的定义

English:
definition Splits
  signature: (f : R[X])
  body: f in Submonoid.closure ({C a | a : R} union {X + C a | a : R})

@[simp, aesop safe apply]

中文:
定义 Splits
  签名: (f : R[X])
  定义体: f in Submonoid.closure ({C a | a : R} union {X + C a | a : R})

@[simp, aesop safe apply]

Depends on / 依赖: Submonoid, Submonoid.closure, closure
-/
def Splits (f : R[X]) : Prop := f in Submonoid.closure ({C a | a : R} union {X + C a | a : R})

@[simp, aesop safe apply]
/--
theorem `Splits.C` / 定理 `Splits.C`

English:
theorem Splits.C
  given: (a : R)
  statement: Splits (C a)
  proof: Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

@[simp, aesop safe apply]

中文:
定理 Splits.C
  条件: (a : R)
  结论: Splits (C a)
  证明: Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
-/
protected theorem Splits.C (a : R) : Splits (C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
/--
theorem `Splits.zero` / 定理 `Splits.zero`

English:
theorem Splits.zero
  statement: Splits (0 : R[X])
  proof: by
  simpa using Splits.C (0 : R)

@[simp, aesop safe apply]

中文:
定理 Splits.zero
  结论: Splits (0 : R[X])
  证明: by
  simpa using Splits.C (0 : R)

@[simp, aesop safe apply]
-/
protected theorem Splits.zero : Splits (0 : R[X]) := by
  simpa using Splits.C (0 : R)

@[simp, aesop safe apply]
/--
theorem `Splits.one` / 定理 `Splits.one`

English:
theorem Splits.one
  statement: Splits (1 : R[X])
  proof: Splits.C (1 : R)

@[simp, aesop safe apply]

中文:
定理 Splits.one
  结论: Splits (1 : R[X])
  证明: Splits.C (1 : R)

@[simp, aesop safe apply]
-/
protected theorem Splits.one : Splits (1 : R[X]) :=
  Splits.C (1 : R)

@[simp, aesop safe apply]
/--
theorem `Splits.X_add_C` / 定理 `Splits.X_add_C`

English:
theorem Splits.X_add_C
  given: (a : R)
  statement: Splits (X + C a)
  proof: Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

@[simp, aesop safe apply]

中文:
定理 Splits.X_add_C
  条件: (a : R)
  结论: Splits (X + C a)
  证明: Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

@[simp, aesop safe apply]

Depends on / 依赖: Set.mem_union_right, Submonoid, Submonoid.mem_closure_of_mem, mem_closure_of_mem, mem_union_right
-/
theorem Splits.X_add_C (a : R) : Splits (X + C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
/--
theorem `Splits.X` / 定理 `Splits.X`

English:
theorem Splits.X
  statement: Splits (X : R[X])
  proof: by
  simpa using Splits.X_add_C (0 : R)

@[simp, aesop safe apply]

中文:
定理 Splits.X
  结论: Splits (X : R[X])
  证明: by
  simpa using Splits.X_add_C (0 : R)

@[simp, aesop safe apply]
-/
protected theorem Splits.X : Splits (X : R[X]) := by
  simpa using Splits.X_add_C (0 : R)

@[simp, aesop safe apply]
/--
theorem `Splits.mul` / 定理 `Splits.mul`

English:
theorem Splits.mul
  given: {f g : R[X]} (hf : Splits f) (hg : Splits g)
  proof: mul_mem hf hg

中文:
定理 Splits.mul
  条件: {f g : R[X]} (hf : Splits f) (hg : Splits g)
  证明: mul_mem hf hg
-/
protected theorem Splits.mul {f g : R[X]} (hf : Splits f) (hg : Splits g) :
    Splits (f * g) :=
  mul_mem hf hg

/--
theorem `Splits.C_mul` / 定理 `Splits.C_mul`

English:
theorem Splits.C_mul
  given: {f : R[X]} (hf : Splits f) (a : R)
  statement: Splits (C a * f)
  proof: (Splits.C a).mul hf

@[simp, aesop safe apply]

中文:
定理 Splits.C_mul
  条件: {f : R[X]} (hf : Splits f) (a : R)
  结论: Splits (C a * f)
  证明: (Splits.C a).mul hf

@[simp, aesop safe apply]
-/
protected theorem Splits.C_mul {f : R[X]} (hf : Splits f) (a : R) : Splits (C a * f) :=
  (Splits.C a).mul hf

@[simp, aesop safe apply]
/--
theorem `Splits.listProd` / 定理 `Splits.listProd`

English:
theorem Splits.listProd
  given: {l : List R[X]} (h : forall f in l, Splits f)
  statement: Splits l.prod
  proof: list_prod_mem h

@[simp, aesop safe apply]

中文:
定理 Splits.listProd
  条件: {l : 列表 R[X]} (h : 对任意 f in l, Splits f)
  结论: Splits l.乘积
  证明: list_prod_mem h

@[simp, aesop safe apply]

Depends on / 依赖: list_prod_mem
-/
theorem Splits.listProd {l : List R[X]} (h : forall f in l, Splits f) : Splits l.prod :=
  list_prod_mem h

@[simp, aesop safe apply]
/--
theorem `Splits.pow` / 定理 `Splits.pow`

English:
theorem Splits.pow
  given: {f : R[X]} (hf : Splits f) (n : Nat)
  statement: Splits (f ^ n)
  proof: pow_mem hf n

中文:
定理 Splits.pow
  条件: {f : R[X]} (hf : Splits f) (n : 自然数)
  结论: Splits (f ^ n)
  证明: pow_mem hf n
-/
protected theorem Splits.pow {f : R[X]} (hf : Splits f) (n : Nat) : Splits (f ^ n) :=
  pow_mem hf n

/--
theorem `Splits.X_pow` / 定理 `Splits.X_pow`

English:
theorem Splits.X_pow
  given: (n : Nat)
  statement: Splits (X ^ n : R[X])
  proof: Splits.X.pow n

中文:
定理 Splits.X_pow
  条件: (n : 自然数)
  结论: Splits (X ^ n : R[X])
  证明: Splits.X.pow n

Depends on / 依赖: Splits, Splits.X.pow
-/
theorem Splits.X_pow (n : Nat) : Splits (X ^ n : R[X]) :=
  Splits.X.pow n

/--
theorem `Splits.C_mul_X_pow` / 定理 `Splits.C_mul_X_pow`

English:
theorem Splits.C_mul_X_pow
  given: (a : R) (n : Nat)
  statement: Splits (C a * X ^ n)
  proof: (Splits.X_pow n).C_mul a

@[simp, aesop safe apply]

中文:
定理 Splits.C_mul_X_pow
  条件: (a : R) (n : 自然数)
  结论: Splits (C a * X ^ n)
  证明: (Splits.X_pow n).C_mul a

@[simp, aesop safe apply]

Depends on / 依赖: C_mul, Splits, Splits.X_pow, X_pow, e.symm
-/
theorem Splits.C_mul_X_pow (a : R) (n : Nat) : Splits (C a * X ^ n) :=
  (Splits.X_pow n).C_mul a

@[simp, aesop safe apply]
/--
theorem `Splits.monomial` / 定理 `Splits.monomial`

English:
theorem Splits.monomial
  given: (n : Nat) (a : R)
  statement: Splits (monomial n a)
  proof: by
  simp [← C_mul_X_pow_eq_monomial]

中文:
定理 Splits.monomial
  条件: (n : 自然数) (a : R)
  结论: Splits (monomial n a)
  证明: by
  simp [← C_mul_X_pow_eq_monomial]

Depends on / 依赖: C_mul_X_pow_eq_monomial
-/
theorem Splits.monomial (n : Nat) (a : R) : Splits (monomial n a) := by
  simp [← C_mul_X_pow_eq_monomial]

/--
theorem `Splits.map` / 定理 `Splits.map`

English:
theorem Splits.map
  given: {f : R[X]} (hf : Splits f) {S : Type*} [Semiring S] (i : R ->+* S)
  proof: by
  induction hf using Submonoid.closure_induction <;> aesop

中文:
定理 Splits.map
  条件: {f : R[X]} (hf : Splits f) {S : 类型} [半环 S] (i : R ->+* S)
  证明: by
  induction hf using Submonoid.closure_induction <;> aesop
-/
protected theorem Splits.map {f : R[X]} (hf : Splits f) {S : Type*} [Semiring S] (i : R ->+* S) :
    Splits (map i f) := by
  induction hf using Submonoid.closure_induction <;> aesop

/--
theorem `Splits.of_natDegree_eq_zero` / 定理 `Splits.of_natDegree_eq_zero`

English:
theorem Splits.of_natDegree_eq_zero
  given: {f : R[X]} (hf : natDegree f = 0)
  proof: by
  rw [← (natDegree_eq_zero.mp hf).choose_spec]; aesop

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_eq_zero := Splits.of_natDegree_eq_zero

中文:
定理 Splits.of_natDegree_eq_zero
  条件: {f : R[X]} (hf : natDegree f = 0)
  证明: by
  rw [← (natDegree_eq_zero.mp hf).choose_spec]; aesop

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_eq_zero := Splits.of_natDegree_eq_zero

Depends on / 依赖: choose_spec, natDegree_eq_zero, natDegree_eq_zero.mp
-/
theorem Splits.of_natDegree_eq_zero {f : R[X]} (hf : natDegree f = 0) :
    Splits f := by
  rw [← (natDegree_eq_zero.mp hf).choose_spec]; aesop

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_eq_zero := Splits.of_natDegree_eq_zero

/--
theorem `Splits.of_degree_le_zero` / 定理 `Splits.of_degree_le_zero`

English:
theorem Splits.of_degree_le_zero
  given: {f : R[X]} (hf : degree f <= 0)
  proof: .of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr hf)

@[deprecated (since := "2026-06-06")] alias splits_of_degree_le_zero := Splits.of_degree_le_zero

中文:
定理 Splits.of_degree_le_zero
  条件: {f : R[X]} (hf : degree f <= 0)
  证明: .of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr hf)

@[deprecated (since := "2026-06-06")] alias splits_of_degree_le_zero := Splits.of_degree_le_zero

Depends on / 依赖: natDegree_eq_zero_iff_degree_le_zero, natDegree_eq_zero_iff_degree_le_zero.mpr, of_natDegree_eq_zero
-/
theorem Splits.of_degree_le_zero {f : R[X]} (hf : degree f <= 0) :
    Splits f :=
  .of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr hf)

@[deprecated (since := "2026-06-06")] alias splits_of_degree_le_zero := Splits.of_degree_le_zero

/--
theorem `_root_.IsUnit.splits` / 定理 `_root_.IsUnit.splits`

English:
theorem _root_.IsUnit.splits
  given: [NoZeroDivisors R] {f : R[X]} (hf : IsUnit f)
  statement: Splits f
  proof: .of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hf)

中文:
定理 _root_.是单位.splits
  条件: [无零因子 R] {f : R[X]} (hf : 是单位 f)
  结论: Splits f
  证明: .of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hf)

Depends on / 依赖: natDegree_eq_zero_of_isUnit, of_natDegree_eq_zero
-/
theorem _root_.IsUnit.splits [NoZeroDivisors R] {f : R[X]} (hf : IsUnit f) : Splits f :=
  .of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hf)

/--
theorem `Splits.of_natDegree_le_one_of_invertible` / 定理 `Splits.of_natDegree_le_one_of_invertible`

English:
theorem Splits.of_natDegree_le_one_of_invertible
  statement: {f : R[X]}
  proof: by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · replace h : Invertible a := by simpa [leadingCoeff, ha] using h
    rw [← mul_invOf_cancel_left a b]; rw [C_mul]; rw [← mul_add]
    exact (Splits.C a).mul (Splits.X_add_C _)

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_le_one_of_invertible := Splits.of_natDegree_le_one_of_invertible

中文:
定理 Splits.of_natDegree_le_one_of_invertible
  结论: {f : R[X]}
  证明: by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · replace h : Invertible a := by simpa [leadingCoeff, ha] using h
    rw [← mul_invOf_cancel_left a b]; rw [C_mul]; rw [← mul_add]
    exact (Splits.C a).mul (Splits.X_add_C _)

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_le_one_of_invertible := Splits.of_natDegree_le_one_of_invertible

Depends on / 依赖: C_mul, Invertible, Splits, Splits.C, Splits.X_add_C, X_add_C, eq_or_ne, exists_eq_X_add_C_of_natDegree_le_one, leadingCoeff, mul_add, mul_invOf_cancel_left, replace
-/
theorem Splits.of_natDegree_le_one_of_invertible {f : R[X]}
    (hf : f.natDegree <= 1) (h : Invertible f.leadingCoeff) : f.Splits := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · replace h : Invertible a := by simpa [leadingCoeff, ha] using h
    rw [← mul_invOf_cancel_left a b]; rw [C_mul]; rw [← mul_add]
    exact (Splits.C a).mul (Splits.X_add_C _)

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_le_one_of_invertible := Splits.of_natDegree_le_one_of_invertible

/--
theorem `Splits.of_degree_le_one_of_invertible` / 定理 `Splits.of_degree_le_one_of_invertible`

English:
theorem Splits.of_degree_le_one_of_invertible
  statement: {f : R[X]}
  proof: .of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hf) h

@[deprecated (since := "2026-06-06")]
alias splits_of_degree_le_one_of_invertible := Splits.of_degree_le_one_of_invertible

中文:
定理 Splits.of_degree_le_one_of_invertible
  结论: {f : R[X]}
  证明: .of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hf) h

@[deprecated (since := "2026-06-06")]
alias splits_of_degree_le_one_of_invertible := Splits.of_degree_le_one_of_invertible

Depends on / 依赖: natDegree_le_of_degree_le, of_natDegree_le_one_of_invertible
-/
theorem Splits.of_degree_le_one_of_invertible {f : R[X]}
    (hf : f.degree <= 1) (h : Invertible f.leadingCoeff) : f.Splits :=
  .of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hf) h

@[deprecated (since := "2026-06-06")]
alias splits_of_degree_le_one_of_invertible := Splits.of_degree_le_one_of_invertible

/--
theorem `Splits.of_natDegree_le_one_of_monic` / 定理 `Splits.of_natDegree_le_one_of_monic`

English:
theorem Splits.of_natDegree_le_one_of_monic
  given: {f : R[X]} (hf : f.natDegree <= 1) (h : Monic f)
  proof: .of_natDegree_le_one_of_invertible hf (h.leadingCoeff ▸ invertibleOne)

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_le_one_of_monic := Splits.of_natDegree_le_one_of_monic

中文:
定理 Splits.of_natDegree_le_one_of_monic
  条件: {f : R[X]} (hf : f.natDegree <= 1) (h : Monic f)
  证明: .of_natDegree_le_one_of_invertible hf (h.leadingCoeff ▸ invertibleOne)

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_le_one_of_monic := Splits.of_natDegree_le_one_of_monic

Depends on / 依赖: h.leadingCoeff, invertibleOne, leadingCoeff, of_natDegree_le_one_of_invertible
-/
theorem Splits.of_natDegree_le_one_of_monic {f : R[X]} (hf : f.natDegree <= 1) (h : Monic f) :
    f.Splits :=
  .of_natDegree_le_one_of_invertible hf (h.leadingCoeff ▸ invertibleOne)

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_le_one_of_monic := Splits.of_natDegree_le_one_of_monic

/--
theorem `Splits.of_degree_le_one_of_monic` / 定理 `Splits.of_degree_le_one_of_monic`

English:
theorem Splits.of_degree_le_one_of_monic
  given: {f : R[X]} (hf : f.degree <= 1) (h : Monic f)
  proof: .of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hf) h

@[deprecated (since := "2026-06-06")]
alias splits_of_degree_le_one_of_monic := Splits.of_degree_le_one_of_monic

中文:
定理 Splits.of_degree_le_one_of_monic
  条件: {f : R[X]} (hf : f.degree <= 1) (h : Monic f)
  证明: .of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hf) h

@[deprecated (since := "2026-06-06")]
alias splits_of_degree_le_one_of_monic := Splits.of_degree_le_one_of_monic

Depends on / 依赖: natDegree_le_of_degree_le, of_natDegree_le_one_of_monic
-/
theorem Splits.of_degree_le_one_of_monic {f : R[X]} (hf : f.degree <= 1) (h : Monic f) :
    f.Splits :=
  .of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hf) h

@[deprecated (since := "2026-06-06")]
alias splits_of_degree_le_one_of_monic := Splits.of_degree_le_one_of_monic

end Semiring

section CommSemiring

variable [CommSemiring R]

@[simp, aesop safe apply]
/--
theorem `Splits.multisetProd` / 定理 `Splits.multisetProd`

English:
theorem Splits.multisetProd
  given: {m : Multiset R[X]} (hm : forall f in m, Splits f)
  statement: Splits m.prod
  proof: multiset_prod_mem _ hm

@[simp, aesop safe apply]

中文:
定理 Splits.multisetProd
  条件: {m : Multiset R[X]} (hm : 对任意 f in m, Splits f)
  结论: Splits m.乘积
  证明: multiset_prod_mem _ hm

@[simp, aesop safe apply]

Depends on / 依赖: multiset_prod_mem
-/
theorem Splits.multisetProd {m : Multiset R[X]} (hm : forall f in m, Splits f) : Splits m.prod :=
  multiset_prod_mem _ hm

@[simp, aesop safe apply]
/--
theorem `Splits.prod` / 定理 `Splits.prod`

English:
theorem Splits.prod
  statement: {ι : Type*} {f : ι -> R[X]} {s : Finset ι}
  proof: prod_mem h

中文:
定理 Splits.乘积
  结论: {ι : 类型} {f : ι -> R[X]} {s : 有限集 ι}
  证明: prod_mem h
-/
protected theorem Splits.prod {ι : Type*} {f : ι -> R[X]} {s : Finset ι}
    (h : forall i in s, Splits (f i)) : Splits (∏ i in s, f i) :=
  prod_mem h

/--
lemma `Splits.taylor` / 引理 `Splits.taylor`

English:
lemma Splits.taylor
  given: {p : R[X]} (hp : p.Splits) (r : R)
  statement: (p.taylor r).Splits
  proof: by
  have (i : _) : (X + C r + C i).Splits := by simpa [add_assoc] using Splits.X_add_C (r + i)
  induction hp using Submonoid.closure_induction <;> aesop

中文:
引理 Splits.taylor
  条件: {p : R[X]} (hp : p.Splits) (r : R)
  结论: (p.taylor r).Splits
  证明: by
  have (i : _) : (X + C r + C i).Splits := by simpa [add_assoc] using Splits.X_add_C (r + i)
  induction hp using Submonoid.closure_induction <;> aesop

Depends on / 依赖: Splits, Splits.X_add_C, Submonoid, Submonoid.closure_induction, X_add_C, add_assoc, closure_induction
-/
lemma Splits.taylor {p : R[X]} (hp : p.Splits) (r : R) : (p.taylor r).Splits := by
  have (i : _) : (X + C r + C i).Splits := by simpa [add_assoc] using Splits.X_add_C (r + i)
  induction hp using Submonoid.closure_induction <;> aesop

/--
theorem `splits_iff_exists_multiset'` / 定理 `splits_iff_exists_multiset'`

English:
theorem splits_iff_exists_multiset'
  given: {f : R[X]}
  proof: by
  refine ⟨fun hf => ?_, ?_⟩
  · let S : Submonoid R[X] := MonoidHom.mrange C
    have hS : S = {C a | a : R} := MonoidHom.coe_mrange C
    rw [Splits]; rw [Submonoid.closure_union]; rw [← hS]; rw [Submonoid.closure_eq]; rw [Submonoid.mem_sup] at hf
    obtain ⟨-, ⟨a, rfl⟩, g, hg, rfl⟩ := hf
    obtain ⟨mg, hmg, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hg
    choose! j hj using hmg
    have hmg : mg = (mg.map j).map (X + C ·) := by simp [Multiset.map_congr rfl hj]
    rw [hmg]; rw [leadingCoeff_mul_monic]; rw [leadingCoeff_C]
    · use mg.map j
    · rw [hmg]
      apply monic_multiset_prod_of_monic
      simp [monic_X_add_C]
  · rintro ⟨m, hm⟩
    exact hm ▸ (Splits.C _).mul (.multisetProd (by simp [Splits.X_add_C]))

中文:
定理 splits_iff_存在_multiset'
  条件: {f : R[X]}
  证明: by
  refine ⟨fun hf => ?_, ?_⟩
  · let S : Submonoid R[X] := MonoidHom.mrange C
    have hS : S = {C a | a : R} := MonoidHom.coe_mrange C
    rw [Splits]; rw [Submonoid.closure_union]; rw [← hS]; rw [Submonoid.closure_eq]; rw [Submonoid.mem_sup] at hf
    obtain ⟨-, ⟨a, rfl⟩, g, hg, rfl⟩ := hf
    obtain ⟨mg, hmg, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hg
    choose! j hj using hmg
    have hmg : mg = (mg.map j).map (X + C ·) := by simp [Multiset.map_congr rfl hj]
    rw [hmg]; rw [leadingCoeff_mul_monic]; rw [leadingCoeff_C]
    · use mg.map j
    · rw [hmg]
      apply monic_multiset_prod_of_monic
      simp [monic_X_add_C]
  · rintro ⟨m, hm⟩
    exact hm ▸ (Splits.C _).mul (.multisetProd (by simp [Splits.X_add_C]))

Depends on / 依赖: MonoidHom, MonoidHom.coe_mrange, MonoidHom.mrange, Multiset, Multiset.map_congr, Splits, Submonoid, Submonoid.closure_eq, Submonoid.closure_union, Submonoid.exists_multiset_of_mem_closure, Submonoid.mem_sup, closure_eq, closure_union, coe_mrange, exists_multiset_of_mem_closure, leadin, leadingCoeff_mul_monic, map_congr, mem_sup, mg.map
-/
theorem splits_iff_exists_multiset' {f : R[X]} :
    Splits f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X + C ·)).prod := by
  refine ⟨fun hf => ?_, ?_⟩
  · let S : Submonoid R[X] := MonoidHom.mrange C
    have hS : S = {C a | a : R} := MonoidHom.coe_mrange C
    rw [Splits]; rw [Submonoid.closure_union]; rw [← hS]; rw [Submonoid.closure_eq]; rw [Submonoid.mem_sup] at hf
    obtain ⟨-, ⟨a, rfl⟩, g, hg, rfl⟩ := hf
    obtain ⟨mg, hmg, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hg
    choose! j hj using hmg
    have hmg : mg = (mg.map j).map (X + C ·) := by simp [Multiset.map_congr rfl hj]
    rw [hmg]; rw [leadingCoeff_mul_monic]; rw [leadingCoeff_C]
    · use mg.map j
    · rw [hmg]
      apply monic_multiset_prod_of_monic
      simp [monic_X_add_C]
  · rintro ⟨m, hm⟩
    exact hm ▸ (Splits.C _).mul (.multisetProd (by simp [Splits.X_add_C]))

/--
theorem `Splits.natDegree_le_one_of_irreducible` / 定理 `Splits.natDegree_le_one_of_irreducible`

English:
theorem Splits.natDegree_le_one_of_irreducible
  statement: {f : R[X]} (hf : Splits f)
  proof: by
  nontriviality R
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rcases m.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · rw [hm]
    simp
  · obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons]; rw [Multiset.prod_cons] at hm
    rw [hm] at h
    simp only [irreducible_mul_iff, IsUnit.mul_iff, not_isUnit_X_add_C, false_and, and_false,
      or_false, false_or, ← Multiset.prod_toList, List.prod_isUnit_iff] at h
    have : m = 0 := by simpa [not_isUnit_X_add_C, ← Multiset.eq_zero_iff_forall_notMem] using h.1.2
    grw [hm, this, natDegree_mul_le]
    simp

中文:
定理 Splits.natDegree_le_one_of_irreducible
  结论: {f : R[X]} (hf : Splits f)
  证明: by
  nontriviality R
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rcases m.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · rw [hm]
    simp
  · obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons]; rw [Multiset.prod_cons] at hm
    rw [hm] at h
    simp only [irreducible_mul_iff, IsUnit.mul_iff, not_isUnit_X_add_C, false_and, and_false,
      or_false, false_or, ← Multiset.prod_toList, List.prod_isUnit_iff] at h
    have : m = 0 := by simpa [not_isUnit_X_add_C, ← Multiset.eq_zero_iff_forall_notMem] using h.1.2
    grw [hm, this, natDegree_mul_le]
    simp

Depends on / 依赖: IsUnit, IsUnit.mul_iff, List.prod_isUnit_iff, Multiset, Multiset.eq_zero_iff_forall_notMem, Multiset.exists_cons_of_mem, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_toList, and_false, empty_or_exists_mem, eq_zero_iff_forall_notMem, exists_cons_of_mem, false_and, false_or, irreducible_mul_iff, m.empty_or_exists_mem, map_cons, mul_iff, nontriviality
-/
theorem Splits.natDegree_le_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : natDegree f <= 1 := by
  nontriviality R
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rcases m.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · rw [hm]
    simp
  · obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons]; rw [Multiset.prod_cons] at hm
    rw [hm] at h
    simp only [irreducible_mul_iff, IsUnit.mul_iff, not_isUnit_X_add_C, false_and, and_false,
      or_false, false_or, ← Multiset.prod_toList, List.prod_isUnit_iff] at h
    have : m = 0 := by simpa [not_isUnit_X_add_C, ← Multiset.eq_zero_iff_forall_notMem] using h.1.2
    grw [hm, this, natDegree_mul_le]
    simp

/--
theorem `Splits.degree_le_one_of_irreducible` / 定理 `Splits.degree_le_one_of_irreducible`

English:
theorem Splits.degree_le_one_of_irreducible
  statement: {f : R[X]} (hf : Splits f)
  proof: degree_le_of_natDegree_le (hf.natDegree_le_one_of_irreducible h)

中文:
定理 Splits.degree_le_one_of_irreducible
  结论: {f : R[X]} (hf : Splits f)
  证明: degree_le_of_natDegree_le (hf.natDegree_le_one_of_irreducible h)

Depends on / 依赖: degree_le_of_natDegree_le, hf.natDegree_le_one_of_irreducible, natDegree_le_one_of_irreducible
-/
theorem Splits.degree_le_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : degree f <= 1 :=
  degree_le_of_natDegree_le (hf.natDegree_le_one_of_irreducible h)

/--
theorem `Splits.comp_of_natDegree_le_one_of_invertible` / 定理 `Splits.comp_of_natDegree_le_one_of_invertible`

English:
theorem Splits.comp_of_natDegree_le_one_of_invertible
  statement: {f g : R[X]} (hf : f.Splits)
  proof: by
  rcases lt_or_eq_of_le hg with hg | hg
  · rw [eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hg)]
    simp
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rw [hm]; rw [mul_comp]; rw [C_comp]; rw [multiset_prod_comp]
  refine (Splits.C _).mul (multisetProd ?_)
  simp only [Multiset.mem_map]
  rintro - ⟨-, ⟨a, -, rfl⟩, rfl⟩
  apply of_natDegree_le_one_of_invertible (by simpa)
  rw [leadingCoeff]; rw [hg] at h
  simpa [leadingCoeff, hg]

中文:
定理 Splits.comp_of_natDegree_le_one_of_invertible
  结论: {f g : R[X]} (hf : f.Splits)
  证明: by
  rcases lt_or_eq_of_le hg with hg | hg
  · rw [eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hg)]
    simp
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rw [hm]; rw [mul_comp]; rw [C_comp]; rw [multiset_prod_comp]
  refine (Splits.C _).mul (multisetProd ?_)
  simp only [Multiset.mem_map]
  rintro - ⟨-, ⟨a, -, rfl⟩, rfl⟩
  apply of_natDegree_le_one_of_invertible (by simpa)
  rw [leadingCoeff]; rw [hg] at h
  simpa [leadingCoeff, hg]

Depends on / 依赖: C_comp, Multiset, Multiset.mem_map, Nat.lt_one_iff.mp, Splits, Splits.C, eq_C_of_natDegree_eq_zero, leadingCoeff, lt_one_iff, lt_or_eq_of_le, mem_map, mul_comp, multisetProd, multiset_prod_comp, of_natDegree_le_one_of_invertible, splits_iff_exists_multiset
-/
theorem Splits.comp_of_natDegree_le_one_of_invertible {f g : R[X]} (hf : f.Splits)
    (hg : g.natDegree <= 1) (h : Invertible g.leadingCoeff) : (f.comp g).Splits := by
  rcases lt_or_eq_of_le hg with hg | hg
  · rw [eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hg)]
    simp
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rw [hm]; rw [mul_comp]; rw [C_comp]; rw [multiset_prod_comp]
  refine (Splits.C _).mul (multisetProd ?_)
  simp only [Multiset.mem_map]
  rintro - ⟨-, ⟨a, -, rfl⟩, rfl⟩
  apply of_natDegree_le_one_of_invertible (by simpa)
  rw [leadingCoeff]; rw [hg] at h
  simpa [leadingCoeff, hg]

/--
theorem `Splits.comp_of_degree_le_one_of_invertible` / 定理 `Splits.comp_of_degree_le_one_of_invertible`

English:
theorem Splits.comp_of_degree_le_one_of_invertible
  statement: {f g : R[X]} (hf : f.Splits)
  proof: hf.comp_of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hg) h

中文:
定理 Splits.comp_of_degree_le_one_of_invertible
  结论: {f g : R[X]} (hf : f.Splits)
  证明: hf.comp_of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hg) h

Depends on / 依赖: comp_of_natDegree_le_one_of_invertible, hf.comp_of_natDegree_le_one_of_invertible, natDegree_le_of_degree_le
-/
theorem Splits.comp_of_degree_le_one_of_invertible {f g : R[X]} (hf : f.Splits)
    (hg : g.degree <= 1) (h : Invertible g.leadingCoeff) : (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hg) h

/--
theorem `Splits.comp_of_natDegree_le_one_of_monic` / 定理 `Splits.comp_of_natDegree_le_one_of_monic`

English:
theorem Splits.comp_of_natDegree_le_one_of_monic
  statement: {f g : R[X]} (hf : f.Splits)
  proof: hf.comp_of_natDegree_le_one_of_invertible hg (h.leadingCoeff ▸ invertibleOne)

中文:
定理 Splits.comp_of_natDegree_le_one_of_monic
  结论: {f g : R[X]} (hf : f.Splits)
  证明: hf.comp_of_natDegree_le_one_of_invertible hg (h.leadingCoeff ▸ invertibleOne)

Depends on / 依赖: comp_of_natDegree_le_one_of_invertible, h.leadingCoeff, hf.comp_of_natDegree_le_one_of_invertible, invertibleOne, leadingCoeff
-/
theorem Splits.comp_of_natDegree_le_one_of_monic {f g : R[X]} (hf : f.Splits)
    (hg : g.natDegree <= 1) (h : Monic g) : (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one_of_invertible hg (h.leadingCoeff ▸ invertibleOne)

/--
theorem `Splits.comp_of_degree_le_one_of_monic` / 定理 `Splits.comp_of_degree_le_one_of_monic`

English:
theorem Splits.comp_of_degree_le_one_of_monic
  statement: {f g : R[X]} (hf : f.Splits)
  proof: hf.comp_of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hg) h

中文:
定理 Splits.comp_of_degree_le_one_of_monic
  结论: {f g : R[X]} (hf : f.Splits)
  证明: hf.comp_of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hg) h

Depends on / 依赖: comp_of_natDegree_le_one_of_monic, hf.comp_of_natDegree_le_one_of_monic, natDegree_le_of_degree_le
-/
theorem Splits.comp_of_degree_le_one_of_monic {f g : R[X]} (hf : f.Splits)
    (hg : g.degree <= 1) (h : Monic g) : (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hg) h

/--
theorem `Splits.comp_X_add_C` / 定理 `Splits.comp_X_add_C`

English:
theorem Splits.comp_X_add_C
  given: {f : R[X]} (hf : f.Splits) (a : R)
  statement: (f.comp (X + C a)).Splits
  proof: hf.comp_of_natDegree_le_one_of_monic (natDegree_add_C.trans_le natDegree_X_le) (monic_X_add_C a)

中文:
定理 Splits.comp_X_add_C
  条件: {f : R[X]} (hf : f.Splits) (a : R)
  结论: (f.comp (X + C a)).Splits
  证明: hf.comp_of_natDegree_le_one_of_monic (natDegree_add_C.trans_le natDegree_X_le) (monic_X_add_C a)

Depends on / 依赖: comp_of_natDegree_le_one_of_monic, hf.comp_of_natDegree_le_one_of_monic, monic_X_add_C, natDegree_X_le, natDegree_add_C, natDegree_add_C.trans_le, trans_le
-/
theorem Splits.comp_X_add_C {f : R[X]} (hf : f.Splits) (a : R) : (f.comp (X + C a)).Splits :=
  hf.comp_of_natDegree_le_one_of_monic (natDegree_add_C.trans_le natDegree_X_le) (monic_X_add_C a)

/--
theorem `Splits.of_algHom` / 定理 `Splits.of_algHom`

English:
theorem Splits.of_algHom
  statement: {f : R[X]} {A B : Type*} [Semiring A] [Semiring B]
  proof: by
  rw [← e.comp_algebraMap]; rw [← map_map]
  apply hf.map

中文:
定理 Splits.of_algHom
  结论: {f : R[X]} {A B : 类型} [半环 A] [半环 B]
  证明: by
  rw [← e.comp_algebraMap]; rw [← map_map]
  apply hf.map

Depends on / 依赖: comp_algebraMap, e.comp_algebraMap, hf.map, map_map
-/
theorem Splits.of_algHom {f : R[X]} {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (hf : Splits (f.map (algebraMap R A))) (e : A ->ₐ[R] B) :
    Splits (f.map (algebraMap R B)) := by
  rw [← e.comp_algebraMap]; rw [← map_map]
  apply hf.map

/--
theorem `Splits.of_isScalarTower` / 定理 `Splits.of_isScalarTower`

English:
theorem Splits.of_isScalarTower
  statement: {f : R[X]} {A : Type*} (B : Type*) [CommSemiring A] [Semiring B]
  proof: hf.of_algHom (IsScalarTower.toAlgHom R A B)

中文:
定理 Splits.of_isScalarTower
  结论: {f : R[X]} {A : 类型} (B : 类型) [交换半环 A] [半环 B]
  证明: hf.of_algHom (IsScalarTower.toAlgHom R A B)

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, hf.of_algHom, of_algHom, toAlgHom
-/
theorem Splits.of_isScalarTower {f : R[X]} {A : Type*} (B : Type*) [CommSemiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hf : Splits (f.map (algebraMap R A))) : Splits (f.map (algebraMap R B)) :=
  hf.of_algHom (IsScalarTower.toAlgHom R A B)

end CommSemiring

section Ring

variable [Ring R]

@[simp, aesop safe apply]
/--
theorem `Splits.X_sub_C` / 定理 `Splits.X_sub_C`

English:
theorem Splits.X_sub_C
  given: (a : R)
  statement: Splits (X - C a)
  proof: by
  simpa using! Splits.X_add_C (-a)

@[aesop safe apply]

中文:
定理 Splits.X_sub_C
  条件: (a : R)
  结论: Splits (X - C a)
  证明: by
  simpa using! Splits.X_add_C (-a)

@[aesop safe apply]

Depends on / 依赖: Splits, Splits.X_add_C, X_add_C
-/
theorem Splits.X_sub_C (a : R) : Splits (X - C a) := by
  simpa using! Splits.X_add_C (-a)

@[aesop safe apply]
/--
theorem `Splits.neg` / 定理 `Splits.neg`

English:
theorem Splits.neg
  given: {f : R[X]} (hf : Splits f)
  statement: Splits (-f)
  proof: by
  rw [← neg_one_mul]; rw [← C_1]; rw [← C_neg]
  exact hf.C_mul (-1)

@[simp]

中文:
定理 Splits.neg
  条件: {f : R[X]} (hf : Splits f)
  结论: Splits (-f)
  证明: by
  rw [← neg_one_mul]; rw [← C_1]; rw [← C_neg]
  exact hf.C_mul (-1)

@[simp]
-/
protected theorem Splits.neg {f : R[X]} (hf : Splits f) : Splits (-f) := by
  rw [← neg_one_mul]; rw [← C_1]; rw [← C_neg]
  exact hf.C_mul (-1)

@[simp]
/--
theorem `splits_neg_iff` / 定理 `splits_neg_iff`

English:
theorem splits_neg_iff
  given: {f : R[X]}
  statement: Splits (-f) ↔ Splits f
  proof: ⟨fun hf => neg_neg f ▸ hf.neg, .neg⟩

中文:
定理 splits_neg_iff
  条件: {f : R[X]}
  结论: Splits (-f) ↔ Splits f
  证明: ⟨fun hf => neg_neg f ▸ hf.neg, .neg⟩

Depends on / 依赖: hf.neg, neg_neg
-/
theorem splits_neg_iff {f : R[X]} : Splits (-f) ↔ Splits f :=
  ⟨fun hf => neg_neg f ▸ hf.neg, .neg⟩

/--
theorem `Splits.comp_neg_X` / 定理 `Splits.comp_neg_X`

English:
theorem Splits.comp_neg_X
  given: {f : R[X]} (hf : f.Splits)
  statement: (f.comp (-X)).Splits
  proof: by
  refine Submonoid.closure_induction ?_ (by simp)
    (fun f g _ _ hf hg => mul_comp_neg_X f g ▸ hf.mul hg) hf
  · rintro f (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · simp
    · rw [add_comp, X_comp, C_comp, neg_add_eq_sub, ← neg_sub]
      exact (X_sub_C a).neg

中文:
定理 Splits.comp_neg_X
  条件: {f : R[X]} (hf : f.Splits)
  结论: (f.comp (-X)).Splits
  证明: by
  refine Submonoid.closure_induction ?_ (by simp)
    (fun f g _ _ hf hg => mul_comp_neg_X f g ▸ hf.mul hg) hf
  · rintro f (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · simp
    · rw [add_comp, X_comp, C_comp, neg_add_eq_sub, ← neg_sub]
      exact (X_sub_C a).neg

Depends on / 依赖: C_comp, Submonoid, Submonoid.closure_induction, X_comp, X_sub_C, add_comp, closure_induction, hf.mul, mul_comp_neg_X, neg_add_eq_sub, neg_sub
-/
theorem Splits.comp_neg_X {f : R[X]} (hf : f.Splits) : (f.comp (-X)).Splits := by
  refine Submonoid.closure_induction ?_ (by simp)
    (fun f g _ _ hf hg => mul_comp_neg_X f g ▸ hf.mul hg) hf
  · rintro f (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · simp
    · rw [add_comp, X_comp, C_comp, neg_add_eq_sub, ← neg_sub]
      exact (X_sub_C a).neg

end Ring

section CommRing

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

/--
theorem `splits_iff_exists_multiset` / 定理 `splits_iff_exists_multiset`

English:
theorem splits_iff_exists_multiset
  proof: by
  refine splits_iff_exists_multiset'.trans ⟨?_, ?_⟩ <;>
    rintro ⟨m, hm⟩ <;> exact ⟨m.map (- ·), by simpa⟩

中文:
定理 splits_iff_存在_multiset
  证明: by
  refine splits_iff_exists_multiset'.trans ⟨?_, ?_⟩ <;>
    rintro ⟨m, hm⟩ <;> exact ⟨m.map (- ·), by simpa⟩

Depends on / 依赖: m.map, splits_iff_exists_multiset
-/
theorem splits_iff_exists_multiset :
    Splits f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod := by
  refine splits_iff_exists_multiset'.trans ⟨?_, ?_⟩ <;>
    rintro ⟨m, hm⟩ <;> exact ⟨m.map (- ·), by simpa⟩

/--
theorem `Splits.exists_eval_eq_zero` / 定理 `Splits.exists_eval_eq_zero`

English:
theorem Splits.exists_eval_eq_zero
  given: (hf : Splits f) (hf0 : degree f != 0)
  proof: by
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
  by_cases hf₀ : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf₀]
  obtain rfl | ⟨a, ha⟩ := m.empty_or_exists_mem
  · rw [hm, Multiset.map_zero, Multiset.prod_zero, mul_one, degree_C hf₀] at hf0
    contradiction
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
  exact ⟨a, by rw [hm]; simp⟩

中文:
定理 Splits.存在_eval_eq_zero
  条件: (hf : Splits f) (hf0 : degree f != 0)
  证明: by
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
  by_cases hf₀ : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf₀]
  obtain rfl | ⟨a, ha⟩ := m.empty_or_exists_mem
  · rw [hm, Multiset.map_zero, Multiset.prod_zero, mul_one, degree_C hf₀] at hf0
    contradiction
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
  exact ⟨a, by rw [hm]; simp⟩

Depends on / 依赖: Multiset, Multiset.exists_cons_of_mem, Multiset.map_zero, Multiset.prod_zero, degree_C, empty_or_exists_mem, exists_cons_of_mem, f.leadingCoeff, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, m.empty_or_exists_mem, map_zero, mul_one, prod_zero, splits_iff_exists_multiset, splits_iff_exists_multiset.mp
-/
theorem Splits.exists_eval_eq_zero (hf : Splits f) (hf0 : degree f != 0) :
    exists a, eval a f = 0 := by
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
  by_cases hf₀ : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf₀]
  obtain rfl | ⟨a, ha⟩ := m.empty_or_exists_mem
  · rw [hm, Multiset.map_zero, Multiset.prod_zero, mul_one, degree_C hf₀] at hf0
    contradiction
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
  exact ⟨a, by rw [hm]; simp⟩

/--
Definition of `rootOfSplits` / `rootOfSplits` 的定义

English:
definition rootOfSplits
  signature: (hf : f.Splits) (hfd : f.degree != 0)
  body: Classical.choose hf.exists_eval_eq_zero hfd

@[simp]

中文:
定义 rootOfSplits
  签名: (hf : f.Splits) (hfd : f.degree != 0)
  定义体: Classical.choose hf.exists_eval_eq_zero hfd

@[simp]

Depends on / 依赖: Classical, Classical.choose, exists_eval_eq_zero, hf.exists_eval_eq_zero
-/
noncomputable def rootOfSplits (hf : f.Splits) (hfd : f.degree != 0) : R :=
Classical.choose hf.exists_eval_eq_zero hfd

@[simp]
/--
theorem `eval_rootOfSplits` / 定理 `eval_rootOfSplits`

English:
theorem eval_rootOfSplits
  given: (hf : f.Splits) (hfd : f.degree != 0)
  proof: Classical.choose_spec hf.exists_eval_eq_zero hfd

中文:
定理 eval_rootOfSplits
  条件: (hf : f.Splits) (hfd : f.degree != 0)
  证明: Classical.choose_spec hf.exists_eval_eq_zero hfd

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_eval_eq_zero, hf.exists_eval_eq_zero
-/
theorem eval_rootOfSplits (hf : f.Splits) (hfd : f.degree != 0) :
    f.eval (rootOfSplits hf hfd) = 0 :=
Classical.choose_spec hf.exists_eval_eq_zero hfd

/--
theorem `Splits.comp_X_sub_C` / 定理 `Splits.comp_X_sub_C`

English:
theorem Splits.comp_X_sub_C
  given: (hf : f.Splits) (a : R)
  statement: (f.comp (X - C a)).Splits
  proof: hf.comp_of_natDegree_le_one_of_monic (natDegree_sub_C.trans_le natDegree_X_le) (monic_X_sub_C a)

中文:
定理 Splits.comp_X_sub_C
  条件: (hf : f.Splits) (a : R)
  结论: (f.comp (X - C a)).Splits
  证明: hf.comp_of_natDegree_le_one_of_monic (natDegree_sub_C.trans_le natDegree_X_le) (monic_X_sub_C a)

Depends on / 依赖: comp_of_natDegree_le_one_of_monic, hf.comp_of_natDegree_le_one_of_monic, monic_X_sub_C, natDegree_X_le, natDegree_sub_C, natDegree_sub_C.trans_le, trans_le
-/
theorem Splits.comp_X_sub_C (hf : f.Splits) (a : R) : (f.comp (X - C a)).Splits :=
  hf.comp_of_natDegree_le_one_of_monic (natDegree_sub_C.trans_le natDegree_X_le) (monic_X_sub_C a)

variable [IsDomain R]

/--
theorem `Splits.eq_prod_roots` / 定理 `Splits.eq_prod_roots`

English:
theorem Splits.eq_prod_roots
  given: (hf : Splits f)
  proof: by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
    suffices hf : f.roots = m by rwa [hf]
    rw [hm]; rw [roots_C_mul _ hf0]; rw [roots_multiset_prod_X_sub_C]

中文:
定理 Splits.eq_prod_roots
  条件: (hf : Splits f)
  证明: by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
    suffices hf : f.roots = m by rwa [hf]
    rw [hm]; rw [roots_C_mul _ hf0]; rw [roots_multiset_prod_X_sub_C]

Depends on / 依赖: f.leadingCoeff, f.roots, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, roots_C_mul, roots_multiset_prod_X_sub_C, splits_iff_exists_multiset, splits_iff_exists_multiset.mp
-/
theorem Splits.eq_prod_roots (hf : Splits f) :
    f = C f.leadingCoeff * (f.roots.map (X - C ·)).prod := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
    suffices hf : f.roots = m by rwa [hf]
    rw [hm]; rw [roots_C_mul _ hf0]; rw [roots_multiset_prod_X_sub_C]

/--
theorem `Splits.eq_prod_roots_of_monic` / 定理 `Splits.eq_prod_roots_of_monic`

English:
theorem Splits.eq_prod_roots_of_monic
  given: (hf : Splits f) (hm : f.Monic)
  proof: by
  conv_lhs => rw [hf.eq_prod_roots, hm.leadingCoeff, C_1, one_mul]

中文:
定理 Splits.eq_prod_roots_of_monic
  条件: (hf : Splits f) (hm : f.Monic)
  证明: by
  conv_lhs => rw [hf.eq_prod_roots, hm.leadingCoeff, C_1, one_mul]

Depends on / 依赖: conv_lhs, eq_prod_roots, hf.eq_prod_roots, hm.leadingCoeff, leadingCoeff, one_mul
-/
theorem Splits.eq_prod_roots_of_monic (hf : Splits f) (hm : f.Monic) :
    f = (f.roots.map (X - C ·)).prod := by
  conv_lhs => rw [hf.eq_prod_roots, hm.leadingCoeff, C_1, one_mul]

/--
theorem `Splits.eval_eq_prod_roots` / 定理 `Splits.eval_eq_prod_roots`

English:
theorem Splits.eval_eq_prod_roots
  given: (hf : Splits f) (x : R)
  proof: by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [eval_multiset_prod]

中文:
定理 Splits.eval_eq_prod_roots
  条件: (hf : Splits f) (x : R)
  证明: by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [eval_multiset_prod]

Depends on / 依赖: conv_lhs, eq_prod_roots, eval_multiset_prod, hf.eq_prod_roots
-/
theorem Splits.eval_eq_prod_roots (hf : Splits f) (x : R) :
    f.eval x = f.leadingCoeff * (f.roots.map (x - ·)).prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [eval_multiset_prod]

/--
theorem `Splits.eval_eq_prod_roots_of_monic` / 定理 `Splits.eval_eq_prod_roots_of_monic`

English:
theorem Splits.eval_eq_prod_roots_of_monic
  given: (hf : Splits f) (hm : Monic f) (x : R)
  proof: by
  simp [hf.eval_eq_prod_roots, hm]

omit [IsDomain R] in

中文:
定理 Splits.eval_eq_prod_roots_of_monic
  条件: (hf : Splits f) (hm : Monic f) (x : R)
  证明: by
  simp [hf.eval_eq_prod_roots, hm]

omit [IsDomain R] in

Depends on / 依赖: CanLift, NonUnitalStarSubalgebra, eval_eq_prod_roots, hf.eval_eq_prod_roots
-/
theorem Splits.eval_eq_prod_roots_of_monic (hf : Splits f) (hm : Monic f) (x : R) :
    f.eval x = (f.roots.map (x - ·)).prod := by
  simp [hf.eval_eq_prod_roots, hm]

omit [IsDomain R] in
/--
theorem `Splits.aeval_eq_prod_aroots_of_monic` / 定理 `Splits.aeval_eq_prod_aroots_of_monic`

English:
theorem Splits.aeval_eq_prod_aroots_of_monic
  proof: by
  simp [hf.eval_eq_prod_roots_of_monic (hm.map (algebraMap R A)), ← eval_map_algebraMap]

中文:
定理 Splits.aeval_eq_prod_aroots_of_monic
  证明: by
  simp [hf.eval_eq_prod_roots_of_monic (hm.map (algebraMap R A)), ← eval_map_algebraMap]

Depends on / 依赖: algebraMap, eval_eq_prod_roots_of_monic, eval_map_algebraMap, hf.eval_eq_prod_roots_of_monic, hm.map
-/
theorem Splits.aeval_eq_prod_aroots_of_monic
    (hf : (f.map (algebraMap R A)).Splits) (hm : Monic f) (x : A) :
    f.aeval x = ((f.aroots A).map (x - ·)).prod := by
  simp [hf.eval_eq_prod_roots_of_monic (hm.map (algebraMap R A)), ← eval_map_algebraMap]

/--
theorem `Splits.eval_derivative` / 定理 `Splits.eval_derivative`

English:
theorem Splits.eval_derivative
  given: [DecidableEq R] (hf : f.Splits) (x : R)
  proof: by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [derivative_prod, eval_multisetSum, eval_multiset_prod]

中文:
定理 Splits.eval_derivative
  条件: [DecidableEq R] (hf : f.Splits) (x : R)
  证明: by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [derivative_prod, eval_multisetSum, eval_multiset_prod]

Depends on / 依赖: conv_lhs, derivative_prod, eq_prod_roots, eval_multisetSum, eval_multiset_prod, hf.eq_prod_roots
-/
theorem Splits.eval_derivative [DecidableEq R] (hf : f.Splits) (x : R) :
    eval x f.derivative = f.leadingCoeff *
      (f.roots.map fun a => ((f.roots.erase a).map (x - ·)).prod).sum := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [derivative_prod, eval_multisetSum, eval_multiset_prod]

/--
theorem `Splits.eval_root_derivative` / 定理 `Splits.eval_root_derivative`

English:
theorem Splits.eval_root_derivative
  statement: [DecidableEq R] (hf : f.Splits) (hm : f.Monic) {x : R}
  proof: by
  rw [← eval_multiset_prod_X_sub_C_derivative hx]; rw [← hf.eq_prod_roots_of_monic hm]

omit [IsDomain R] in

中文:
定理 Splits.eval_root_derivative
  结论: [DecidableEq R] (hf : f.Splits) (hm : f.Monic) {x : R}
  证明: by
  rw [← eval_multiset_prod_X_sub_C_derivative hx]; rw [← hf.eq_prod_roots_of_monic hm]

omit [IsDomain R] in

Depends on / 依赖: eq_prod_roots_of_monic, eval_multiset_prod_X_sub_C_derivative, hf.eq_prod_roots_of_monic
-/
theorem Splits.eval_root_derivative [DecidableEq R] (hf : f.Splits) (hm : f.Monic) {x : R}
    (hx : x in f.roots) : eval x f.derivative = ((f.roots.erase x).map (x - ·)).prod := by
  rw [← eval_multiset_prod_X_sub_C_derivative hx]; rw [← hf.eq_prod_roots_of_monic hm]

omit [IsDomain R] in
/--
theorem `Splits.of_splits_map_of_injective` / 定理 `Splits.of_splits_map_of_injective`

English:
theorem Splits.of_splits_map_of_injective
  statement: {S : Type*} [CommRing S] [IsDomain S] {i : R ->+* S}
  proof: by
  choose j hj using hi
  rw [splits_iff_exists_multiset]
  refine ⟨(f.map i).roots.pmap j fun _ => id, map_injective i hi ?_⟩
  conv_lhs => rw [hf.eq_prod_roots, leadingCoeff_map_of_injective hi]
  simp [Multiset.pmap_eq_map, hj, Multiset.map_pmap, Polynomial.map_multiset_prod]

中文:
定理 Splits.of_splits_map_of_injective
  结论: {S : 类型} [交换环 S] [是整环 S] {i : R ->+* S}
  证明: by
  choose j hj using hi
  rw [splits_iff_exists_multiset]
  refine ⟨(f.map i).roots.pmap j fun _ => id, map_injective i hi ?_⟩
  conv_lhs => rw [hf.eq_prod_roots, leadingCoeff_map_of_injective hi]
  simp [Multiset.pmap_eq_map, hj, Multiset.map_pmap, Polynomial.map_multiset_prod]

Depends on / 依赖: Multiset, Multiset.map_pmap, Multiset.pmap_eq_map, Polynomial, Polynomial.map_multiset_prod, conv_lhs, eq_prod_roots, f.map, hf.eq_prod_roots, leadingCoeff_map_of_injective, map_injective, map_multiset_prod, map_pmap, pmap_eq_map, roots.pmap, splits_iff_exists_multiset
-/
theorem Splits.of_splits_map_of_injective {S : Type*} [CommRing S] [IsDomain S] {i : R ->+* S}
    (hi : Function.Injective i) (hf : Splits (f.map i))
    (hi : forall a in (f.map i).roots, a in i.range) : Splits f := by
  choose j hj using hi
  rw [splits_iff_exists_multiset]
  refine ⟨(f.map i).roots.pmap j fun _ => id, map_injective i hi ?_⟩
  conv_lhs => rw [hf.eq_prod_roots, leadingCoeff_map_of_injective hi]
  simp [Multiset.pmap_eq_map, hj, Multiset.map_pmap, Polynomial.map_multiset_prod]

/--
theorem `Splits.mem_lift_of_roots_mem_range` / 定理 `Splits.mem_lift_of_roots_mem_range`

English:
theorem Splits.mem_lift_of_roots_mem_range
  statement: (hf : f.Splits) (hm : f.Monic)
  proof: by
  rw [hf.eq_prod_roots_of_monic hm]; rw [lifts_iff_liftsRing]
  refine Subring.multiset_prod_mem _ _ fun g hg => ?_
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hg
  exact Subring.sub_mem _ (X_mem_lifts i) (C'_mem_lifts (hr x hx))

中文:
定理 Splits.mem_lift_of_roots_mem_range
  结论: (hf : f.Splits) (hm : f.Monic)
  证明: by
  rw [hf.eq_prod_roots_of_monic hm]; rw [lifts_iff_liftsRing]
  refine Subring.multiset_prod_mem _ _ fun g hg => ?_
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hg
  exact Subring.sub_mem _ (X_mem_lifts i) (C'_mem_lifts (hr x hx))

Depends on / 依赖: Multiset, Multiset.mem_map.mp, Subring, Subring.multiset_prod_mem, Subring.sub_mem, X_mem_lifts, _mem_lifts, eq_prod_roots_of_monic, hf.eq_prod_roots_of_monic, lifts_iff_liftsRing, mem_map, multiset_prod_mem, sub_mem
-/
theorem Splits.mem_lift_of_roots_mem_range (hf : f.Splits) (hm : f.Monic)
    {S : Type*} [Ring S] (i : S ->+* R) (hr : forall a in f.roots, a in i.range) :
    f in Polynomial.lifts i := by
  rw [hf.eq_prod_roots_of_monic hm]; rw [lifts_iff_liftsRing]
  refine Subring.multiset_prod_mem _ _ fun g hg => ?_
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hg
  exact Subring.sub_mem _ (X_mem_lifts i) (C'_mem_lifts (hr x hx))

/--
theorem `Splits.eq_X_sub_C_of_single_root` / 定理 `Splits.eq_X_sub_C_of_single_root`

English:
theorem Splits.eq_X_sub_C_of_single_root
  given: (hf : Splits f) {x : R} (hr : f.roots = {x})
  proof: by
  rw [hf.eq_prod_roots]; rw [hr]
  simp

中文:
定理 Splits.eq_X_sub_C_of_single_root
  条件: (hf : Splits f) {x : R} (hr : f.roots = {x})
  证明: by
  rw [hf.eq_prod_roots]; rw [hr]
  simp

Depends on / 依赖: eq_prod_roots, hf.eq_prod_roots
-/
theorem Splits.eq_X_sub_C_of_single_root (hf : Splits f) {x : R} (hr : f.roots = {x}) :
    f = C f.leadingCoeff * (X - C x) := by
  rw [hf.eq_prod_roots]; rw [hr]
  simp

/--
theorem `Splits.natDegree_eq_card_roots` / 定理 `Splits.natDegree_eq_card_roots`

English:
theorem Splits.natDegree_eq_card_roots
  given: (hf : Splits f)
  proof: by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · conv_lhs => rw [hf.eq_prod_roots, natDegree_C_mul hf0, natDegree_multiset_prod_X_sub_C_eq_card]

中文:
定理 Splits.natDegree_eq_card_roots
  条件: (hf : Splits f)
  证明: by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · conv_lhs => rw [hf.eq_prod_roots, natDegree_C_mul hf0, natDegree_multiset_prod_X_sub_C_eq_card]

Depends on / 依赖: conv_lhs, eq_prod_roots, f.leadingCoeff, hf.eq_prod_roots, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, natDegree_C_mul, natDegree_multiset_prod_X_sub_C_eq_card
-/
theorem Splits.natDegree_eq_card_roots (hf : Splits f) :
    f.natDegree = f.roots.card := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · conv_lhs => rw [hf.eq_prod_roots, natDegree_C_mul hf0, natDegree_multiset_prod_X_sub_C_eq_card]

/--
theorem `Splits.degree_eq_card_roots` / 定理 `Splits.degree_eq_card_roots`

English:
theorem Splits.degree_eq_card_roots
  given: (hf : Splits f) (hf0 : f != 0)
  proof: (degree_eq_iff_natDegree_eq hf0).mpr hf.natDegree_eq_card_roots

中文:
定理 Splits.degree_eq_card_roots
  条件: (hf : Splits f) (hf0 : f != 0)
  证明: (degree_eq_iff_natDegree_eq hf0).mpr hf.natDegree_eq_card_roots

Depends on / 依赖: degree_eq_iff_natDegree_eq, hf.natDegree_eq_card_roots, natDegree_eq_card_roots
-/
theorem Splits.degree_eq_card_roots (hf : Splits f) (hf0 : f != 0) :
    f.degree = f.roots.card :=
  (degree_eq_iff_natDegree_eq hf0).mpr hf.natDegree_eq_card_roots

/--
theorem `splits_iff_card_roots` / 定理 `splits_iff_card_roots`

English:
theorem splits_iff_card_roots
  statement: Splits f ↔ f.roots.card = f.natDegree
  proof: ⟨fun h => h.natDegree_eq_card_roots.symm, fun h => splits_iff_exists_multiset.mpr
    ⟨f.roots, (C_leadingCoeff_mul_prod_multiset_X_sub_C h).symm⟩⟩

中文:
定理 splits_iff_card_roots
  结论: Splits f ↔ f.roots.card = f.natDegree
  证明: ⟨fun h => h.natDegree_eq_card_roots.symm, fun h => splits_iff_exists_multiset.mpr
    ⟨f.roots, (C_leadingCoeff_mul_prod_multiset_X_sub_C h).symm⟩⟩

Depends on / 依赖: C_leadingCoeff_mul_prod_multiset_X_sub_C, f.roots, h.natDegree_eq_card_roots.symm, natDegree_eq_card_roots, splits_iff_exists_multiset, splits_iff_exists_multiset.mpr
-/
theorem splits_iff_card_roots : Splits f ↔ f.roots.card = f.natDegree :=
  ⟨fun h => h.natDegree_eq_card_roots.symm, fun h => splits_iff_exists_multiset.mpr
    ⟨f.roots, (C_leadingCoeff_mul_prod_multiset_X_sub_C h).symm⟩⟩

/--
theorem `Splits.roots_ne_zero` / 定理 `Splits.roots_ne_zero`

English:
theorem Splits.roots_ne_zero
  given: (hf : Splits f) (hf0 : natDegree f != 0)
  proof: by
  simpa [hf.natDegree_eq_card_roots] using hf0

中文:
定理 Splits.roots_ne_zero
  条件: (hf : Splits f) (hf0 : natDegree f != 0)
  证明: by
  simpa [hf.natDegree_eq_card_roots] using hf0

Depends on / 依赖: hf.natDegree_eq_card_roots, natDegree_eq_card_roots
-/
theorem Splits.roots_ne_zero (hf : Splits f) (hf0 : natDegree f != 0) :
    f.roots != 0 := by
  simpa [hf.natDegree_eq_card_roots] using hf0

/--
theorem `Splits.roots_map_of_ne_zero` / 定理 `Splits.roots_map_of_ne_zero`

English:
theorem Splits.roots_map_of_ne_zero
  statement: {S : Type*} [CommRing S] [IsDomain S]
  proof: by
  induction hf using Submonoid.closure_induction with
  | mem p hp => obtain (⟨r, rfl⟩ | ⟨a, rfl⟩) := hp <;> simp
  | one => simp
  | mul x y _ _ hx hy => simp_all [roots_mul, show x * y != 0 by aesop]

中文:
定理 Splits.roots_map_of_ne_zero
  结论: {S : 类型} [交换环 S] [是整环 S]
  证明: by
  induction hf using Submonoid.closure_induction with
  | mem p hp => obtain (⟨r, rfl⟩ | ⟨a, rfl⟩) := hp <;> simp
  | one => simp
  | mul x y _ _ hx hy => simp_all [roots_mul, show x * y != 0 by aesop]

Depends on / 依赖: Submonoid, Submonoid.closure_induction, closure_induction, roots_mul
-/
theorem Splits.roots_map_of_ne_zero {S : Type*} [CommRing S] [IsDomain S]
    {f : R[X]} (hf : Splits f) {φ : R ->+* S} (hφ : f.map φ != 0) :
    (f.map φ).roots = f.roots.map φ := by
  induction hf using Submonoid.closure_induction with
  | mem p hp => obtain (⟨r, rfl⟩ | ⟨a, rfl⟩) := hp <;> simp
  | one => simp
  | mul x y _ _ hx hy => simp_all [roots_mul, show x * y != 0 by aesop]

/--
theorem `Splits.roots_map_of_injective` / 定理 `Splits.roots_map_of_injective`

English:
theorem Splits.roots_map_of_injective
  statement: {S : Type*} [CommRing S] [IsDomain S]
  proof: (roots_map_of_injective_of_card_eq_natDegree hi hf.natDegree_eq_card_roots.symm).symm

omit [IsDomain R] in

中文:
定理 Splits.roots_map_of_injective
  结论: {S : 类型} [交换环 S] [是整环 S]
  证明: (roots_map_of_injective_of_card_eq_natDegree hi hf.natDegree_eq_card_roots.symm).symm

omit [IsDomain R] in

Depends on / 依赖: hf.natDegree_eq_card_roots.symm, natDegree_eq_card_roots, roots_map_of_injective_of_card_eq_natDegree
-/
theorem Splits.roots_map_of_injective {S : Type*} [CommRing S] [IsDomain S]
    (hf : f.Splits) {i : R ->+* S} (hi : Function.Injective i) : (f.map i).roots = f.roots.map i :=
  (roots_map_of_injective_of_card_eq_natDegree hi hf.natDegree_eq_card_roots.symm).symm

omit [IsDomain R] in
/--
theorem `Splits.image_rootSet_of_map_ne_zero` / 定理 `Splits.image_rootSet_of_map_ne_zero`

English:
theorem Splits.image_rootSet_of_map_ne_zero
  statement: (hf : (f.map (algebraMap R A)).Splits)
  proof: by
  classical
  replace hφ : (f.map (algebraMap R A)).map (φ : A ->+* B) != 0 := by
    rwa [map_map, φ.comp_algebraMap]
  replace hf := hf.roots_map_of_ne_zero hφ
  rw [map_map]; rw [φ.comp_algebraMap] at hf
  simp [rootSet, aroots, hf, Multiset.toFinset_map]

中文:
定理 Splits.image_rootSet_of_map_ne_zero
  结论: (hf : (f.map (algebraMap R A)).Splits)
  证明: by
  classical
  replace hφ : (f.map (algebraMap R A)).map (φ : A ->+* B) != 0 := by
    rwa [map_map, φ.comp_algebraMap]
  replace hf := hf.roots_map_of_ne_zero hφ
  rw [map_map]; rw [φ.comp_algebraMap] at hf
  simp [rootSet, aroots, hf, Multiset.toFinset_map]

Depends on / 依赖: Multiset, Multiset.toFinset_map, algebraMap, aroots, classical, comp_algebraMap, f.map, hf.roots_map_of_ne_zero, map_map, replace, rootSet, roots_map_of_ne_zero, toFinset_map
-/
theorem Splits.image_rootSet_of_map_ne_zero (hf : (f.map (algebraMap R A)).Splits)
    (φ : A ->ₐ[R] B) (hφ : f.map (algebraMap R B) != 0) : φ '' f.rootSet A = f.rootSet B := by
  classical
  replace hφ : (f.map (algebraMap R A)).map (φ : A ->+* B) != 0 := by
    rwa [map_map, φ.comp_algebraMap]
  replace hf := hf.roots_map_of_ne_zero hφ
  rw [map_map]; rw [φ.comp_algebraMap] at hf
  simp [rootSet, aroots, hf, Multiset.toFinset_map]

/--
theorem `Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots` / 定理 `Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots`

English:
theorem Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots
  given: (hf : Splits f)
  proof: by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [coeff_zero_eq_eval_zero, eval_multiset_prod, hf.natDegree_eq_card_roots,
    mul_assoc, mul_left_comm]

中文:
定理 Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots
  条件: (hf : Splits f)
  证明: by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [coeff_zero_eq_eval_zero, eval_multiset_prod, hf.natDegree_eq_card_roots,
    mul_assoc, mul_left_comm]

Depends on / 依赖: coeff_zero_eq_eval_zero, conv_lhs, eq_prod_roots, eval_multiset_prod, hf.eq_prod_roots, hf.natDegree_eq_card_roots, mul_assoc, mul_left_comm, natDegree_eq_card_roots
-/
theorem Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots (hf : Splits f) :
    f.coeff 0 = (-1) ^ f.natDegree * f.leadingCoeff * f.roots.prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [coeff_zero_eq_eval_zero, eval_multiset_prod, hf.natDegree_eq_card_roots,
    mul_assoc, mul_left_comm]

/--
theorem `Splits.coeff_zero_eq_prod_roots_of_monic` / 定理 `Splits.coeff_zero_eq_prod_roots_of_monic`

English:
theorem Splits.coeff_zero_eq_prod_roots_of_monic
  given: (hf : Splits f) (hm : Monic f)
  proof: by
  simp [hf.coeff_zero_eq_leadingCoeff_mul_prod_roots, hm]

中文:
定理 Splits.coeff_zero_eq_prod_roots_of_monic
  条件: (hf : Splits f) (hm : Monic f)
  证明: by
  simp [hf.coeff_zero_eq_leadingCoeff_mul_prod_roots, hm]

Depends on / 依赖: coeff_zero_eq_leadingCoeff_mul_prod_roots, hf.coeff_zero_eq_leadingCoeff_mul_prod_roots
-/
theorem Splits.coeff_zero_eq_prod_roots_of_monic (hf : Splits f) (hm : Monic f) :
    coeff f 0 = (-1) ^ f.natDegree * f.roots.prod := by
  simp [hf.coeff_zero_eq_leadingCoeff_mul_prod_roots, hm]

/--
theorem `Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff` / 定理 `Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff`

English:
theorem Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  given: (hf : Splits f)
  proof: by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [Multiset.sum_map_neg', monic_X_sub_C, Monic.nextCoeff_multiset_prod]

中文:
定理 Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  条件: (hf : Splits f)
  证明: by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [Multiset.sum_map_neg', monic_X_sub_C, Monic.nextCoeff_multiset_prod]

Depends on / 依赖: Monic.nextCoeff_multiset_prod, Multiset, Multiset.sum_map_neg, conv_lhs, eq_prod_roots, hf.eq_prod_roots, monic_X_sub_C, nextCoeff_multiset_prod, sum_map_neg
-/
theorem Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff (hf : Splits f) :
    f.nextCoeff = -f.leadingCoeff * f.roots.sum := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [Multiset.sum_map_neg', monic_X_sub_C, Monic.nextCoeff_multiset_prod]

/--
theorem `Splits.nextCoeff_eq_neg_sum_roots_of_monic` / 定理 `Splits.nextCoeff_eq_neg_sum_roots_of_monic`

English:
theorem Splits.nextCoeff_eq_neg_sum_roots_of_monic
  given: (hf : Splits f) (hm : Monic f)
  proof: by
  simp [hf.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff, hm]

中文:
定理 Splits.nextCoeff_eq_neg_sum_roots_of_monic
  条件: (hf : Splits f) (hm : Monic f)
  证明: by
  simp [hf.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff, hm]

Depends on / 依赖: hf.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff, nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
-/
theorem Splits.nextCoeff_eq_neg_sum_roots_of_monic (hf : Splits f) (hm : Monic f) :
    f.nextCoeff = -f.roots.sum := by
  simp [hf.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff, hm]

/--
theorem `splits_X_sub_C_mul_iff` / 定理 `splits_X_sub_C_mul_iff`

English:
theorem splits_X_sub_C_mul_iff
  given: {a : R}
  statement: Splits ((X - C a) * f) ↔ Splits f
  proof: by
  refine ⟨fun hf => ?_, ((Splits.X_sub_C _).mul ·)⟩
  by_cases hf₀ : f = 0
  · aesop
  have := hf.eq_prod_roots
  rw [leadingCoeff_mul]; rw [leadingCoeff_X_sub_C]; rw [one_mul]; rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hf₀)]; rw [roots_X_sub_C]; rw [Multiset.singleton_add]; rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [mul_left_comm] at this
  rw [mul_left_cancel₀ (X_sub_C_ne_zero _) this]
  aesop

中文:
定理 splits_X_sub_C_mul_iff
  条件: {a : R}
  结论: Splits ((X - C a) * f) ↔ Splits f
  证明: by
  refine ⟨fun hf => ?_, ((Splits.X_sub_C _).mul ·)⟩
  by_cases hf₀ : f = 0
  · aesop
  have := hf.eq_prod_roots
  rw [leadingCoeff_mul]; rw [leadingCoeff_X_sub_C]; rw [one_mul]; rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hf₀)]; rw [roots_X_sub_C]; rw [Multiset.singleton_add]; rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [mul_left_comm] at this
  rw [mul_left_cancel₀ (X_sub_C_ne_zero _) this]
  aesop

Depends on / 依赖: Multiset, Multiset.map_cons, Multiset.prod_cons, Multiset.singleton_add, Splits, Splits.X_sub_C, X_sub_C, X_sub_C_ne_zero, eq_prod_roots, hf.eq_prod_roots, leadingCoeff_X_sub_C, leadingCoeff_mul, map_cons, mul_left_comm, mul_ne_zero, one_mul, prod_cons, roots_X_sub_C, roots_mul, singleton_add
-/
theorem splits_X_sub_C_mul_iff {a : R} : Splits ((X - C a) * f) ↔ Splits f := by
  refine ⟨fun hf => ?_, ((Splits.X_sub_C _).mul ·)⟩
  by_cases hf₀ : f = 0
  · aesop
  have := hf.eq_prod_roots
  rw [leadingCoeff_mul]; rw [leadingCoeff_X_sub_C]; rw [one_mul]; rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hf₀)]; rw [roots_X_sub_C]; rw [Multiset.singleton_add]; rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [mul_left_comm] at this
  rw [mul_left_cancel₀ (X_sub_C_ne_zero _) this]
  aesop

/--
theorem `splits_mul` / 定理 `splits_mul`

English:
theorem splits_mul
  given: (hf₀ : f != 0) (hg₀ : g != 0)
  proof: by
  refine ⟨fun h => ?_, and_imp.mpr .mul⟩
  generalize hp : f * g = p at *
  generalize hn : p.natDegree = n
  induction n generalizing p f g with
  | zero =>
    rw [← hp]; rw [natDegree_mul hf₀ hg₀]; rw [Nat.add_eq_zero_iff] at hn
    exact ⟨.of_natDegree_eq_zero hn.1, .of_natDegree_eq_zero hn.2⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := Splits.exists_eval_eq_zero h (degree_ne_of_natDegree_ne <| hn ▸ by simp)
    have := dvd_iff_isRoot.mpr ha
    rw [← hp]; rw [(prime_X_sub_C a).dvd_mul] at this
    wlog hf : X - C a ∣ f with hf2
· exact .symm hf2 n ih hg₀ hf₀ p ((mul_comm g f).trans hp) h hn a ha this.symm
        this.resolve_left hf
    obtain ⟨f, rfl⟩ := hf
    rw [mul_assoc] at hp; subst hp
    rw [natDegree_mul (by aesop) (by aesop)]; rw [natDegree_X_sub_C]; rw [add_comm]; rw [Nat.succ_inj] at hn
    have := ih (by aesop) hg₀ (f * g) rfl (splits_X_sub_C_mul_iff.mp h) hn
    aesop

@[deprecated (since := "2026-06-08")] alias splits_mul_iff := splits_mul

中文:
定理 splits_mul
  条件: (hf₀ : f != 0) (hg₀ : g != 0)
  证明: by
  refine ⟨fun h => ?_, and_imp.mpr .mul⟩
  generalize hp : f * g = p at *
  generalize hn : p.natDegree = n
  induction n generalizing p f g with
  | zero =>
    rw [← hp]; rw [natDegree_mul hf₀ hg₀]; rw [Nat.add_eq_zero_iff] at hn
    exact ⟨.of_natDegree_eq_zero hn.1, .of_natDegree_eq_zero hn.2⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := Splits.exists_eval_eq_zero h (degree_ne_of_natDegree_ne <| hn ▸ by simp)
    have := dvd_iff_isRoot.mpr ha
    rw [← hp]; rw [(prime_X_sub_C a).dvd_mul] at this
    wlog hf : X - C a ∣ f with hf2
· exact .symm hf2 n ih hg₀ hf₀ p ((mul_comm g f).trans hp) h hn a ha this.symm
        this.resolve_left hf
    obtain ⟨f, rfl⟩ := hf
    rw [mul_assoc] at hp; subst hp
    rw [natDegree_mul (by aesop) (by aesop)]; rw [natDegree_X_sub_C]; rw [add_comm]; rw [Nat.succ_inj] at hn
    have := ih (by aesop) hg₀ (f * g) rfl (splits_X_sub_C_mul_iff.mp h) hn
    aesop

@[deprecated (since := "2026-06-08")] alias splits_mul_iff := splits_mul

Depends on / 依赖: Nat.add_eq_zero_iff, Splits, Splits.exists_eval_eq_zero, add_eq_zero_iff, and_imp, and_imp.mpr, degree_ne_of_natDegree_ne, dvd_iff_isRoot, dvd_iff_isRoot.mpr, dvd_mul, exists_eval_eq_zero, generalize, generalizing, natDegree, natDegree_mul, of_natDegree_eq_zero, p.natDegree, prime_X_sub_C
-/
theorem splits_mul (hf₀ : f != 0) (hg₀ : g != 0) :
    Splits (f * g) ↔ Splits f ∧ Splits g := by
  refine ⟨fun h => ?_, and_imp.mpr .mul⟩
  generalize hp : f * g = p at *
  generalize hn : p.natDegree = n
  induction n generalizing p f g with
  | zero =>
    rw [← hp]; rw [natDegree_mul hf₀ hg₀]; rw [Nat.add_eq_zero_iff] at hn
    exact ⟨.of_natDegree_eq_zero hn.1, .of_natDegree_eq_zero hn.2⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := Splits.exists_eval_eq_zero h (degree_ne_of_natDegree_ne <| hn ▸ by simp)
    have := dvd_iff_isRoot.mpr ha
    rw [← hp]; rw [(prime_X_sub_C a).dvd_mul] at this
    wlog hf : X - C a ∣ f with hf2
· exact .symm hf2 n ih hg₀ hf₀ p ((mul_comm g f).trans hp) h hn a ha this.symm
        this.resolve_left hf
    obtain ⟨f, rfl⟩ := hf
    rw [mul_assoc] at hp; subst hp
    rw [natDegree_mul (by aesop) (by aesop)]; rw [natDegree_X_sub_C]; rw [add_comm]; rw [Nat.succ_inj] at hn
    have := ih (by aesop) hg₀ (f * g) rfl (splits_X_sub_C_mul_iff.mp h) hn
    aesop

@[deprecated (since := "2026-06-08")] alias splits_mul_iff := splits_mul

/--
lemma `splits_mul'` / 引理 `splits_mul'`

English:
lemma splits_mul'
  statement: (f * g).Splits ↔ (f.Splits ∨ g = 0) ∧ (g.Splits ∨ f = 0) where
  proof: by grind [splits_mul]
  mpr := by rintro ⟨hp | rfl, hq | rfl⟩ <;> simp [*]

中文:
引理 splits_mul'
  结论: (f * g).Splits ↔ (f.Splits ∨ g = 0) ∧ (g.Splits ∨ f = 0) where
  证明: by grind [splits_mul]
  mpr := by rintro ⟨hp | rfl, hq | rfl⟩ <;> simp [*]

Depends on / 依赖: splits_mul
-/
lemma splits_mul' : (f * g).Splits ↔ (f.Splits ∨ g = 0) ∧ (g.Splits ∨ f = 0) where
  mp hpq := by grind [splits_mul]
  mpr := by rintro ⟨hp | rfl, hq | rfl⟩ <;> simp [*]

/--
lemma `splits_mul_iff_left` / 引理 `splits_mul_iff_left`

English:
lemma splits_mul_iff_left
  given: (hg₀ : g != 0) (hg : g.Splits)
  statement: (f * g).Splits ↔ f.Splits
  proof: by
  simp [splits_mul', *]

中文:
引理 splits_mul_iff_left
  条件: (hg₀ : g != 0) (hg : g.Splits)
  结论: (f * g).Splits ↔ f.Splits
  证明: by
  simp [splits_mul', *]

Depends on / 依赖: splits_mul
-/
lemma splits_mul_iff_left (hg₀ : g != 0) (hg : g.Splits) : (f * g).Splits ↔ f.Splits := by
  simp [splits_mul', *]

/--
lemma `splits_mul_iff_right` / 引理 `splits_mul_iff_right`

English:
lemma splits_mul_iff_right
  given: (hf₀ : f != 0) (hg : f.Splits)
  statement: (f * g).Splits ↔ g.Splits
  proof: by
  simp [splits_mul', *]

中文:
引理 splits_mul_iff_right
  条件: (hf₀ : f != 0) (hg : f.Splits)
  结论: (f * g).Splits ↔ g.Splits
  证明: by
  simp [splits_mul', *]

Depends on / 依赖: splits_mul
-/
lemma splits_mul_iff_right (hf₀ : f != 0) (hg : f.Splits) : (f * g).Splits ↔ g.Splits := by
  simp [splits_mul', *]

/--
lemma `splits_X_mul` / 引理 `splits_X_mul`

English:
lemma splits_X_mul
  statement: (X * f).Splits ↔ f.Splits
  proof: by simp [splits_mul']

中文:
引理 splits_X_mul
  结论: (X * f).Splits ↔ f.Splits
  证明: by simp [splits_mul']
-/
@[simp] lemma splits_X_mul : (X * f).Splits ↔ f.Splits := by simp [splits_mul']
/--
lemma `splits_mul_X` / 引理 `splits_mul_X`

English:
lemma splits_mul_X
  statement: (f * X).Splits ↔ f.Splits
  proof: by simp [mul_comm f]

alias ⟨Splits.of_X_mul, _⟩ := splits_X_mul
alias ⟨Splits.of_mul_X, _⟩ := splits_mul_X

中文:
引理 splits_mul_X
  结论: (f * X).Splits ↔ f.Splits
  证明: by simp [mul_comm f]

alias ⟨Splits.of_X_mul, _⟩ := splits_X_mul
alias ⟨Splits.of_mul_X, _⟩ := splits_mul_X
-/
@[simp] lemma splits_mul_X : (f * X).Splits ↔ f.Splits := by simp [mul_comm f]

alias ⟨Splits.of_X_mul, _⟩ := splits_X_mul
alias ⟨Splits.of_mul_X, _⟩ := splits_mul_X

/--
theorem `Splits.of_dvd` / 定理 `Splits.of_dvd`

English:
theorem Splits.of_dvd
  given: (hg : Splits g) (hg₀ : g != 0) (hfg : f ∣ g)
  statement: Splits f
  proof: by
  obtain ⟨g, rfl⟩ := hfg
  exact ((splits_mul (by simp_all) (by simp_all)).mp hg).1

中文:
定理 Splits.of_dvd
  条件: (hg : Splits g) (hg₀ : g != 0) (hfg : f ∣ g)
  结论: Splits f
  证明: by
  obtain ⟨g, rfl⟩ := hfg
  exact ((splits_mul (by simp_all) (by simp_all)).mp hg).1

Depends on / 依赖: splits_mul
-/
theorem Splits.of_dvd (hg : Splits g) (hg₀ : g != 0) (hfg : f ∣ g) : Splits f := by
  obtain ⟨g, rfl⟩ := hfg
  exact ((splits_mul (by simp_all) (by simp_all)).mp hg).1

/--
theorem `splits_prod_iff` / 定理 `splits_prod_iff`

English:
theorem splits_prod_iff
  given: {ι : Type*} {f : ι -> R[X]} {s : Finset ι} (hf : forall i in s, f i != 0)
  proof: ⟨fun h _ hx => h.of_dvd (Finset.prod_ne_zero_iff.mpr hf) (Finset.dvd_prod_of_mem f hx),
    Splits.prod⟩

@[deprecated "Use `Splits.degree_le_one_of_irreducible` instead." (since := "2026-01-13")]

中文:
定理 splits_prod_iff
  条件: {ι : 类型} {f : ι -> R[X]} {s : 有限集 ι} (hf : 对任意 i in s, f i != 0)
  证明: ⟨fun h _ hx => h.of_dvd (Finset.prod_ne_zero_iff.mpr hf) (Finset.dvd_prod_of_mem f hx),
    Splits.prod⟩

@[deprecated "Use `Splits.degree_le_one_of_irreducible` instead." (since := "2026-01-13")]

Depends on / 依赖: Finset, Finset.dvd_prod_of_mem, Finset.prod_ne_zero_iff.mpr, Splits, Splits.prod, dvd_prod_of_mem, h.of_dvd, of_dvd, prod_ne_zero_iff
-/
theorem splits_prod_iff {ι : Type*} {f : ι -> R[X]} {s : Finset ι} (hf : forall i in s, f i != 0) :
    (∏ x in s, f x).Splits ↔ forall x in s, (f x).Splits :=
  ⟨fun h _ hx => h.of_dvd (Finset.prod_ne_zero_iff.mpr hf) (Finset.dvd_prod_of_mem f hx),
    Splits.prod⟩

@[deprecated "Use `Splits.degree_le_one_of_irreducible` instead." (since := "2026-01-13")]
/--
theorem `Splits.splits` / 定理 `Splits.splits`

English:
theorem Splits.splits
  given: (hf : Splits f)
  proof: or_iff_not_imp_left.mpr fun hf0 _ hg hgf => degree_le_of_natDegree_le
    (hf.of_dvd hf0 hgf).natDegree_le_one_of_irreducible hg

中文:
定理 Splits.splits
  条件: (hf : Splits f)
  证明: or_iff_not_imp_left.mpr fun hf0 _ hg hgf => degree_le_of_natDegree_le
    (hf.of_dvd hf0 hgf).natDegree_le_one_of_irreducible hg

Depends on / 依赖: degree_le_of_natDegree_le, hf.of_dvd, natDegree_le_one_of_irreducible, of_dvd, or_iff_not_imp_left, or_iff_not_imp_left.mpr
-/
theorem Splits.splits (hf : Splits f) :
    f = 0 ∨ forall {g : R[X]}, Irreducible g -> g ∣ f -> degree g <= 1 :=
or_iff_not_imp_left.mpr fun hf0 _ hg hgf => degree_le_of_natDegree_le
    (hf.of_dvd hf0 hgf).natDegree_le_one_of_irreducible hg

/--
lemma `map_sub_sprod_roots_eq_prod_map_eval` / 引理 `map_sub_sprod_roots_eq_prod_map_eval`

English:
lemma map_sub_sprod_roots_eq_prod_map_eval
  proof: by
  have := hg'.eq_prod_roots
  rw [hg.leadingCoeff]; rw [map_one]; rw [one_mul] at this
  conv_rhs => rw [this]
  simp_rw [eval_multiset_prod, Multiset.prod_map_product_eq_prod_prod, Multiset.map_map]
  congr! with x hx
  ext; simp

中文:
引理 map_sub_sprod_roots_eq_prod_map_eval
  证明: by
  have := hg'.eq_prod_roots
  rw [hg.leadingCoeff]; rw [map_one]; rw [one_mul] at this
  conv_rhs => rw [this]
  simp_rw [eval_multiset_prod, Multiset.prod_map_product_eq_prod_prod, Multiset.map_map]
  congr! with x hx
  ext; simp

Depends on / 依赖: Multiset, Multiset.map_map, Multiset.prod_map_product_eq_prod_prod, conv_rhs, eq_prod_roots, eval_multiset_prod, hg.leadingCoeff, leadingCoeff, map_map, map_one, one_mul, prod_map_product_eq_prod_prod, simp_rw
-/
lemma map_sub_sprod_roots_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((s ×ˢ g.roots).map fun ij => ij.1 - ij.2).prod = (s.map g.eval).prod := by
  have := hg'.eq_prod_roots
  rw [hg.leadingCoeff]; rw [map_one]; rw [one_mul] at this
  conv_rhs => rw [this]
  simp_rw [eval_multiset_prod, Multiset.prod_map_product_eq_prod_prod, Multiset.map_map]
  congr! with x hx
  ext; simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_sub_roots_sprod_eq_prod_map_eval` / 引理 `map_sub_roots_sprod_eq_prod_map_eval`

English:
lemma map_sub_roots_sprod_eq_prod_map_eval
  proof: by
  trans ((s ×ˢ g.roots).map fun ij => (-1) * (ij.1 - ij.2)).prod
  · rw [← Multiset.map_swap_product, Multiset.map_map]; simp
  · rw [Multiset.prod_map_mul]; simp [map_sub_sprod_roots_eq_prod_map_eval _ _ hg hg']

中文:
引理 map_sub_roots_sprod_eq_prod_map_eval
  证明: by
  trans ((s ×ˢ g.roots).map fun ij => (-1) * (ij.1 - ij.2)).prod
  · rw [← Multiset.map_swap_product, Multiset.map_map]; simp
  · rw [Multiset.prod_map_mul]; simp [map_sub_sprod_roots_eq_prod_map_eval _ _ hg hg']

Depends on / 依赖: Multiset, Multiset.map_map, Multiset.map_swap_product, Multiset.prod_map_mul, g.roots, map_map, map_sub_sprod_roots_eq_prod_map_eval, map_swap_product, prod_map_mul
-/
lemma map_sub_roots_sprod_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((g.roots ×ˢ s).map fun ij => ij.1 - ij.2).prod =
      (-1) ^ (s.card * g.roots.card) * (s.map g.eval).prod := by
  trans ((s ×ˢ g.roots).map fun ij => (-1) * (ij.1 - ij.2)).prod
  · rw [← Multiset.map_swap_product, Multiset.map_map]; simp
  · rw [Multiset.prod_map_mul]; simp [map_sub_sprod_roots_eq_prod_map_eval _ _ hg hg']

end CommRing

section DivisionSemiring

variable [DivisionSemiring R]

/--
theorem `Splits.of_natDegree_le_one` / 定理 `Splits.of_natDegree_le_one`

English:
theorem Splits.of_natDegree_le_one
  given: {f : R[X]} (hf : natDegree f <= 1)
  statement: Splits f
  proof: by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · simp_all
  · rw [← mul_inv_cancel_left₀ ha b, C_mul, ← mul_add]
    exact (X_add_C (a⁻¹ * b)).C_mul a

中文:
定理 Splits.of_natDegree_le_one
  条件: {f : R[X]} (hf : natDegree f <= 1)
  结论: Splits f
  证明: by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · simp_all
  · rw [← mul_inv_cancel_left₀ ha b, C_mul, ← mul_add]
    exact (X_add_C (a⁻¹ * b)).C_mul a

Depends on / 依赖: C_mul, X_add_C, exists_eq_X_add_C_of_natDegree_le_one, mul_add
-/
theorem Splits.of_natDegree_le_one {f : R[X]} (hf : natDegree f <= 1) : Splits f := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · simp_all
  · rw [← mul_inv_cancel_left₀ ha b, C_mul, ← mul_add]
    exact (X_add_C (a⁻¹ * b)).C_mul a

/--
theorem `Splits.of_natDegree_eq_one` / 定理 `Splits.of_natDegree_eq_one`

English:
theorem Splits.of_natDegree_eq_one
  given: {f : R[X]} (hf : natDegree f = 1)
  statement: Splits f
  proof: of_natDegree_le_one hf.le

中文:
定理 Splits.of_natDegree_eq_one
  条件: {f : R[X]} (hf : natDegree f = 1)
  结论: Splits f
  证明: of_natDegree_le_one hf.le

Depends on / 依赖: hf.le, of_natDegree_le_one
-/
theorem Splits.of_natDegree_eq_one {f : R[X]} (hf : natDegree f = 1) : Splits f :=
  of_natDegree_le_one hf.le

/--
theorem `Splits.of_degree_le_one` / 定理 `Splits.of_degree_le_one`

English:
theorem Splits.of_degree_le_one
  given: {f : R[X]} (hf : degree f <= 1)
  statement: Splits f
  proof: of_natDegree_le_one (natDegree_le_of_degree_le hf)

中文:
定理 Splits.of_degree_le_one
  条件: {f : R[X]} (hf : degree f <= 1)
  结论: Splits f
  证明: of_natDegree_le_one (natDegree_le_of_degree_le hf)

Depends on / 依赖: natDegree_le_of_degree_le, of_natDegree_le_one
-/
theorem Splits.of_degree_le_one {f : R[X]} (hf : degree f <= 1) : Splits f :=
  of_natDegree_le_one (natDegree_le_of_degree_le hf)

/--
theorem `Splits.of_degree_eq_one` / 定理 `Splits.of_degree_eq_one`

English:
theorem Splits.of_degree_eq_one
  given: {f : R[X]} (hf : degree f = 1)
  statement: Splits f
  proof: of_degree_le_one hf.le

中文:
定理 Splits.of_degree_eq_one
  条件: {f : R[X]} (hf : degree f = 1)
  结论: Splits f
  证明: of_degree_le_one hf.le

Depends on / 依赖: hf.le, of_degree_le_one
-/
theorem Splits.of_degree_eq_one {f : R[X]} (hf : degree f = 1) : Splits f :=
  of_degree_le_one hf.le

end DivisionSemiring

section Field

section

variable {S : Type*} [Field R] [CommRing S] [IsDomain S]

/--
theorem `Splits.of_splits_map` / 定理 `Splits.of_splits_map`

English:
theorem Splits.of_splits_map
  statement: {f : R[X]} (i : R ->+* S)
  proof: hf.of_splits_map_of_injective i.injective hi

中文:
定理 Splits.of_splits_map
  结论: {f : R[X]} (i : R ->+* S)
  证明: hf.of_splits_map_of_injective i.injective hi

Depends on / 依赖: hf.of_splits_map_of_injective, i.injective, injective, of_splits_map_of_injective
-/
theorem Splits.of_splits_map {f : R[X]} (i : R ->+* S)
    (hf : Splits (f.map i)) (hi : forall a in (f.map i).roots, a in i.range) : Splits f :=
  hf.of_splits_map_of_injective i.injective hi

/--
theorem `Splits.roots_map` / 定理 `Splits.roots_map`

English:
theorem Splits.roots_map
  given: {f : R[X]} (hf : f.Splits) (i : R ->+* S)
  proof: hf.roots_map_of_injective i.injective

中文:
定理 Splits.roots_map
  条件: {f : R[X]} (hf : f.Splits) (i : R ->+* S)
  证明: hf.roots_map_of_injective i.injective

Depends on / 依赖: hf.roots_map_of_injective, i.injective, injective, roots_map_of_injective
-/
theorem Splits.roots_map {f : R[X]} (hf : f.Splits) (i : R ->+* S) :
    (f.map i).roots = f.roots.map i :=
  hf.roots_map_of_injective i.injective

/--
theorem `Splits.mem_range_of_isRoot` / 定理 `Splits.mem_range_of_isRoot`

English:
theorem Splits.mem_range_of_isRoot
  statement: {f : R[X]}
  proof: by
  rw [← mem_roots (map_ne_zero hf0)]; rw [hf.roots_map]; rw [Multiset.mem_map] at hx
  obtain ⟨x, -, hx⟩ := hx
  exact ⟨x, hx⟩

中文:
定理 Splits.mem_range_of_isRoot
  结论: {f : R[X]}
  证明: by
  rw [← mem_roots (map_ne_zero hf0)]; rw [hf.roots_map]; rw [Multiset.mem_map] at hx
  obtain ⟨x, -, hx⟩ := hx
  exact ⟨x, hx⟩

Depends on / 依赖: Multiset, Multiset.mem_map, hf.roots_map, map_ne_zero, mem_map, mem_roots, roots_map
-/
theorem Splits.mem_range_of_isRoot {f : R[X]}
    (hf : f.Splits) (hf0 : f != 0) {i : R ->+* S} {x : S} (hx : (f.map i).IsRoot x) :
    x in i.range := by
  rw [← mem_roots (map_ne_zero hf0)]; rw [hf.roots_map]; rw [Multiset.mem_map] at hx
  obtain ⟨x, -, hx⟩ := hx
  exact ⟨x, hx⟩

/--
theorem `Splits.aeval_eq_prod_aroots` / 定理 `Splits.aeval_eq_prod_aroots`

English:
theorem Splits.aeval_eq_prod_aroots
  statement: [Algebra R S]
  proof: by
  simp [← eval_map_algebraMap, hf.eval_eq_prod_roots]

中文:
定理 Splits.aeval_eq_prod_aroots
  结论: [代数 R S]
  证明: by
  simp [← eval_map_algebraMap, hf.eval_eq_prod_roots]

Depends on / 依赖: eval_eq_prod_roots, eval_map_algebraMap, hf.eval_eq_prod_roots
-/
theorem Splits.aeval_eq_prod_aroots [Algebra R S]
    {f : R[X]} (hf : (f.map (algebraMap R S)).Splits) (x : S) :
    f.aeval x = algebraMap R S f.leadingCoeff * ((f.aroots S).map (x - ·)).prod := by
  simp [← eval_map_algebraMap, hf.eval_eq_prod_roots]

end

section

variable {A B : Type*} [CommRing R] [Field A] [Algebra R A]
  [CommRing B] [IsDomain B] [Algebra R B] {f : R[X]}

/--
theorem `Splits.image_rootSet` / 定理 `Splits.image_rootSet`

English:
theorem Splits.image_rootSet
  statement: (hf : (f.map (algebraMap R A)).Splits)
  proof: by
  classical
  rw [rootSet]; rw [← Finset.coe_image]; rw [← Multiset.toFinset_map]; rw [← g.coe_toRingHom]; rw [← hf.roots_map]; rw [map_map]; rw [g.comp_algebraMap]; rw [← rootSet]

中文:
定理 Splits.image_rootSet
  结论: (hf : (f.map (algebraMap R A)).Splits)
  证明: by
  classical
  rw [rootSet]; rw [← Finset.coe_image]; rw [← Multiset.toFinset_map]; rw [← g.coe_toRingHom]; rw [← hf.roots_map]; rw [map_map]; rw [g.comp_algebraMap]; rw [← rootSet]

Depends on / 依赖: Finset, Finset.coe_image, Multiset, Multiset.toFinset_map, classical, coe_image, coe_toRingHom, comp_algebraMap, g.coe_toRingHom, g.comp_algebraMap, hf.roots_map, map_map, rootSet, roots_map, toFinset_map
-/
theorem Splits.image_rootSet (hf : (f.map (algebraMap R A)).Splits)
    (g : A ->ₐ[R] B) : g '' f.rootSet A = f.rootSet B := by
  classical
  rw [rootSet]; rw [← Finset.coe_image]; rw [← Multiset.toFinset_map]; rw [← g.coe_toRingHom]; rw [← hf.roots_map]; rw [map_map]; rw [g.comp_algebraMap]; rw [← rootSet]

/--
theorem `Splits.adjoin_rootSet_eq_range` / 定理 `Splits.adjoin_rootSet_eq_range`

English:
theorem Splits.adjoin_rootSet_eq_range
  proof: by
  rw [← hf.image_rootSet g]; rw [Algebra.adjoin_image]; rw [← Algebra.map_top]
  exact (Subalgebra.map_injective g.injective).eq_iff

中文:
定理 Splits.adjoin_rootSet_eq_range
  证明: by
  rw [← hf.image_rootSet g]; rw [Algebra.adjoin_image]; rw [← Algebra.map_top]
  exact (Subalgebra.map_injective g.injective).eq_iff

Depends on / 依赖: Algebra, Algebra.adjoin_image, Algebra.map_top, Subalgebra, Subalgebra.map_injective, adjoin_image, eq_iff, g.injective, hf.image_rootSet, image_rootSet, injective, map_injective, map_top
-/
theorem Splits.adjoin_rootSet_eq_range
    (hf : (f.map (algebraMap R A)).Splits) (g : A ->ₐ[R] B) :
    Algebra.adjoin R (f.rootSet B) = g.range ↔ Algebra.adjoin R (f.rootSet A) = ⊤ := by
  rw [← hf.image_rootSet g]; rw [Algebra.adjoin_image]; rw [← Algebra.map_top]
  exact (Subalgebra.map_injective g.injective).eq_iff

end

section

variable {A B : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [CommRing B]
  [IsDomain B] [Algebra R B] [Algebra A B] [FaithfulSMul A B] [IsScalarTower R A B] {f : R[X]}

/--
theorem `Splits.map_aroots_algebraMap` / 定理 `Splits.map_aroots_algebraMap`

English:
theorem Splits.map_aroots_algebraMap
  given: (hf : (f.map (algebraMap R A)).Splits)
  proof: by
  rw [← aroots_map B A]; rw [aroots]; rw [aroots]; rw [hf.roots_map_of_injective (FaithfulSMul.algebraMap_injective A B)]

中文:
定理 Splits.map_aroots_algebraMap
  条件: (hf : (f.map (algebraMap R A)).Splits)
  证明: by
  rw [← aroots_map B A]; rw [aroots]; rw [aroots]; rw [hf.roots_map_of_injective (FaithfulSMul.algebraMap_injective A B)]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, aroots, aroots_map, hf.roots_map_of_injective, roots_map_of_injective
-/
theorem Splits.map_aroots_algebraMap (hf : (f.map (algebraMap R A)).Splits) :
    (f.aroots A).map (algebraMap A B) = f.aroots B := by
  rw [← aroots_map B A]; rw [aroots]; rw [aroots]; rw [hf.roots_map_of_injective (FaithfulSMul.algebraMap_injective A B)]

/--
theorem `Splits.image_rootSet_algebraMap` / 定理 `Splits.image_rootSet_algebraMap`

English:
theorem Splits.image_rootSet_algebraMap
  given: (hf : (f.map (algebraMap R A)).Splits)
  proof: by
  classical
  rw [rootSet]; rw [← Finset.coe_image]; rw [← Multiset.toFinset_map]; rw [hf.map_aroots_algebraMap]; rw [← rootSet]

中文:
定理 Splits.image_rootSet_algebraMap
  条件: (hf : (f.map (algebraMap R A)).Splits)
  证明: by
  classical
  rw [rootSet]; rw [← Finset.coe_image]; rw [← Multiset.toFinset_map]; rw [hf.map_aroots_algebraMap]; rw [← rootSet]

Depends on / 依赖: Finset, Finset.coe_image, Multiset, Multiset.toFinset_map, classical, coe_image, hf.map_aroots_algebraMap, map_aroots_algebraMap, rootSet, toFinset_map
-/
theorem Splits.image_rootSet_algebraMap (hf : (f.map (algebraMap R A)).Splits) :
    (algebraMap A B) '' f.rootSet A = f.rootSet B := by
  classical
  rw [rootSet]; rw [← Finset.coe_image]; rw [← Multiset.toFinset_map]; rw [hf.map_aroots_algebraMap]; rw [← rootSet]

end

variable [Field R] {f g : R[X]}

/--
theorem `Splits.dvd_of_roots_le_roots` / 定理 `Splits.dvd_of_roots_le_roots`

English:
theorem Splits.dvd_of_roots_le_roots
  given: (hp : f.Splits) (hp0 : f != 0) (hq : f.roots <= g.roots)
  proof: by
  rw [hp.eq_prod_roots]; rw [C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hq)).trans
    (prod_multiset_X_sub_C_dvd _)

中文:
定理 Splits.dvd_of_roots_le_roots
  条件: (hp : f.Splits) (hp0 : f != 0) (hq : f.roots <= g.roots)
  证明: by
  rw [hp.eq_prod_roots]; rw [C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hq)).trans
    (prod_multiset_X_sub_C_dvd _)

Depends on / 依赖: C_mul_dvd, Multiset, Multiset.map_le_map, Multiset.prod_dvd_prod_of_le, eq_prod_roots, hp.eq_prod_roots, leadingCoeff_ne_zero, map_le_map, prod_dvd_prod_of_le, prod_multiset_X_sub_C_dvd
-/
theorem Splits.dvd_of_roots_le_roots (hp : f.Splits) (hp0 : f != 0) (hq : f.roots <= g.roots) :
    f ∣ g := by
  rw [hp.eq_prod_roots]; rw [C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hq)).trans
    (prod_multiset_X_sub_C_dvd _)

/--
theorem `Splits.dvd_iff_roots_le_roots` / 定理 `Splits.dvd_iff_roots_le_roots`

English:
theorem Splits.dvd_iff_roots_le_roots
  given: (hf : f.Splits) (hf0 : f != 0) (hg0 : g != 0)
  proof: ⟨roots.le_of_dvd hg0, hf.dvd_of_roots_le_roots hf0⟩

中文:
定理 Splits.dvd_iff_roots_le_roots
  条件: (hf : f.Splits) (hf0 : f != 0) (hg0 : g != 0)
  证明: ⟨roots.le_of_dvd hg0, hf.dvd_of_roots_le_roots hf0⟩

Depends on / 依赖: dvd_of_roots_le_roots, hf.dvd_of_roots_le_roots, le_of_dvd, roots.le_of_dvd
-/
theorem Splits.dvd_iff_roots_le_roots (hf : f.Splits) (hf0 : f != 0) (hg0 : g != 0) :
    f ∣ g ↔ f.roots <= g.roots :=
  ⟨roots.le_of_dvd hg0, hf.dvd_of_roots_le_roots hf0⟩

/--
theorem `Splits.comp_of_natDegree_le_one` / 定理 `Splits.comp_of_natDegree_le_one`

English:
theorem Splits.comp_of_natDegree_le_one
  given: {f g : R[X]} (hf : f.Splits) (hg : g.natDegree <= 1)
  proof: by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  · exact Splits.comp_of_natDegree_le_one_of_invertible hf hg
      (invertibleOfNonzero (leadingCoeff_ne_zero.mpr hg0))

中文:
定理 Splits.comp_of_natDegree_le_one
  条件: {f g : R[X]} (hf : f.Splits) (hg : g.natDegree <= 1)
  证明: by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  · exact Splits.comp_of_natDegree_le_one_of_invertible hf hg
      (invertibleOfNonzero (leadingCoeff_ne_zero.mpr hg0))

Depends on / 依赖: Splits, Splits.comp_of_natDegree_le_one_of_invertible, comp_of_natDegree_le_one_of_invertible, eq_or_ne, invertibleOfNonzero, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr
-/
theorem Splits.comp_of_natDegree_le_one {f g : R[X]} (hf : f.Splits) (hg : g.natDegree <= 1) :
    (f.comp g).Splits := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  · exact Splits.comp_of_natDegree_le_one_of_invertible hf hg
      (invertibleOfNonzero (leadingCoeff_ne_zero.mpr hg0))

/--
theorem `Splits.comp_of_degree_le_one` / 定理 `Splits.comp_of_degree_le_one`

English:
theorem Splits.comp_of_degree_le_one
  given: {f g : R[X]} (hf : f.Splits) (hg : g.degree <= 1)
  proof: hf.comp_of_natDegree_le_one (natDegree_le_of_degree_le hg)

中文:
定理 Splits.comp_of_degree_le_one
  条件: {f g : R[X]} (hf : f.Splits) (hg : g.degree <= 1)
  证明: hf.comp_of_natDegree_le_one (natDegree_le_of_degree_le hg)

Depends on / 依赖: comp_of_natDegree_le_one, hf.comp_of_natDegree_le_one, natDegree_le_of_degree_le
-/
theorem Splits.comp_of_degree_le_one {f g : R[X]} (hf : f.Splits) (hg : g.degree <= 1) :
    (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one (natDegree_le_of_degree_le hg)

/--
theorem `splits_iff_comp_splits_of_natDegree_eq_one` / 定理 `splits_iff_comp_splits_of_natDegree_eq_one`

English:
theorem splits_iff_comp_splits_of_natDegree_eq_one
  given: {f g : R[X]} (hg : g.natDegree = 1)
  proof: by
  refine ⟨fun hf => hf.comp_of_natDegree_le_one hg.le, fun hf => ?_⟩
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hg.le
  have ha : a != 0 := by contrapose! hg; simp [hg]
  have : f = (f.comp (C a * X + C b)).comp ((C a⁻¹ * (X - C b))) := by
    simp only [comp_assoc, add_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc]; rw [← C_mul]; rw [mul_inv_cancel₀ ha]; rw [C_1]; rw [one_mul]; rw [sub_add_cancel]; rw [comp_X]
  rw [this]
  refine Splits.comp_of_natDegree_le_one hf ?_
  rw [natDegree_C_mul (mt inv_eq_zero.mp ha)]; rw [natDegree_X_sub_C]

中文:
定理 splits_iff_comp_splits_of_natDegree_eq_one
  条件: {f g : R[X]} (hg : g.natDegree = 1)
  证明: by
  refine ⟨fun hf => hf.comp_of_natDegree_le_one hg.le, fun hf => ?_⟩
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hg.le
  have ha : a != 0 := by contrapose! hg; simp [hg]
  have : f = (f.comp (C a * X + C b)).comp ((C a⁻¹ * (X - C b))) := by
    simp only [comp_assoc, add_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc]; rw [← C_mul]; rw [mul_inv_cancel₀ ha]; rw [C_1]; rw [one_mul]; rw [sub_add_cancel]; rw [comp_X]
  rw [this]
  refine Splits.comp_of_natDegree_le_one hf ?_
  rw [natDegree_C_mul (mt inv_eq_zero.mp ha)]; rw [natDegree_X_sub_C]

Depends on / 依赖: C_comp, C_mul, Splits, Splits.comp_of_natDegree_le_one, X_comp, add_comp, comp_X, comp_assoc, comp_of_natDegree_le_one, contrapose, exists_eq_X_add_C_of_natDegree_le_one, f.comp, hf.comp_of_natDegree_le_one, hg.le, mul_assoc, mul_comp, natDegree_C_mu, one_mul, sub_add_cancel
-/
theorem splits_iff_comp_splits_of_natDegree_eq_one {f g : R[X]} (hg : g.natDegree = 1) :
    f.Splits ↔ (f.comp g).Splits := by
  refine ⟨fun hf => hf.comp_of_natDegree_le_one hg.le, fun hf => ?_⟩
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hg.le
  have ha : a != 0 := by contrapose! hg; simp [hg]
  have : f = (f.comp (C a * X + C b)).comp ((C a⁻¹ * (X - C b))) := by
    simp only [comp_assoc, add_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc]; rw [← C_mul]; rw [mul_inv_cancel₀ ha]; rw [C_1]; rw [one_mul]; rw [sub_add_cancel]; rw [comp_X]
  rw [this]
  refine Splits.comp_of_natDegree_le_one hf ?_
  rw [natDegree_C_mul (mt inv_eq_zero.mp ha)]; rw [natDegree_X_sub_C]

/--
theorem `splits_iff_comp_splits_of_degree_eq_one` / 定理 `splits_iff_comp_splits_of_degree_eq_one`

English:
theorem splits_iff_comp_splits_of_degree_eq_one
  given: {f g : R[X]} (hg : g.degree = 1)
  proof: splits_iff_comp_splits_of_natDegree_eq_one (natDegree_eq_of_degree_eq_some hg)

中文:
定理 splits_iff_comp_splits_of_degree_eq_one
  条件: {f g : R[X]} (hg : g.degree = 1)
  证明: splits_iff_comp_splits_of_natDegree_eq_one (natDegree_eq_of_degree_eq_some hg)

Depends on / 依赖: natDegree_eq_of_degree_eq_some, splits_iff_comp_splits_of_natDegree_eq_one
-/
theorem splits_iff_comp_splits_of_degree_eq_one {f g : R[X]} (hg : g.degree = 1) :
    f.Splits ↔ (f.comp g).Splits :=
  splits_iff_comp_splits_of_natDegree_eq_one (natDegree_eq_of_degree_eq_some hg)

/--
theorem `Splits.degree_eq_one_of_irreducible` / 定理 `Splits.degree_eq_one_of_irreducible`

English:
theorem Splits.degree_eq_one_of_irreducible
  statement: {f : R[X]} (hf : Splits f)
  proof: le_antisymm (hf.degree_le_one_of_irreducible h)
    ((WithBot.one_le_iff_pos _).mpr (degree_pos_of_irreducible h))

中文:
定理 Splits.degree_eq_one_of_irreducible
  结论: {f : R[X]} (hf : Splits f)
  证明: le_antisymm (hf.degree_le_one_of_irreducible h)
    ((WithBot.one_le_iff_pos _).mpr (degree_pos_of_irreducible h))

Depends on / 依赖: WithBot, WithBot.one_le_iff_pos, degree_le_one_of_irreducible, degree_pos_of_irreducible, hf.degree_le_one_of_irreducible, le_antisymm, one_le_iff_pos
-/
theorem Splits.degree_eq_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : degree f = 1 :=
  le_antisymm (hf.degree_le_one_of_irreducible h)
    ((WithBot.one_le_iff_pos _).mpr (degree_pos_of_irreducible h))

/--
theorem `Splits.natDegree_eq_one_of_irreducible` / 定理 `Splits.natDegree_eq_one_of_irreducible`

English:
theorem Splits.natDegree_eq_one_of_irreducible
  statement: {f : R[X]} (hf : Splits f)
  proof: natDegree_eq_of_degree_eq_some (hf.degree_eq_one_of_irreducible h)

中文:
定理 Splits.natDegree_eq_one_of_irreducible
  结论: {f : R[X]} (hf : Splits f)
  证明: natDegree_eq_of_degree_eq_some (hf.degree_eq_one_of_irreducible h)

Depends on / 依赖: degree_eq_one_of_irreducible, hf.degree_eq_one_of_irreducible, natDegree_eq_of_degree_eq_some
-/
theorem Splits.natDegree_eq_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : natDegree f = 1 :=
  natDegree_eq_of_degree_eq_some (hf.degree_eq_one_of_irreducible h)

/--
theorem `Splits.eval_derivative_eq_eval_mul_sum` / 定理 `Splits.eval_derivative_eq_eval_mul_sum`

English:
theorem Splits.eval_derivative_eq_eval_mul_sum
  given: (hf : Splits f) {x : R} (hx : f.eval x != 0)
  proof: by
  classical
  simp only [hf.eval_derivative, hf.eval_eq_prod_roots, ← Multiset.sum_map_mul_left, mul_assoc]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl fun z hz => ?_)
  rw [← Multiset.prod_map_erase hz]; rw [mul_one_div]; rw [mul_div_cancel_left₀]
  aesop (add simp sub_eq_zero)

中文:
定理 Splits.eval_derivative_eq_eval_mul_sum
  条件: (hf : Splits f) {x : R} (hx : f.eval x != 0)
  证明: by
  classical
  simp only [hf.eval_derivative, hf.eval_eq_prod_roots, ← Multiset.sum_map_mul_left, mul_assoc]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl fun z hz => ?_)
  rw [← Multiset.prod_map_erase hz]; rw [mul_one_div]; rw [mul_div_cancel_left₀]
  aesop (add simp sub_eq_zero)

Depends on / 依赖: Multiset, Multiset.map_congr, Multiset.prod_map_erase, Multiset.sum, Multiset.sum_map_mul_left, classical, congr_arg, eval_derivative, eval_eq_prod_roots, hf.eval_derivative, hf.eval_eq_prod_roots, map_congr, mul_assoc, mul_one_div, prod_map_erase, sub_eq_zero, sum_map_mul_left
-/
theorem Splits.eval_derivative_eq_eval_mul_sum (hf : Splits f) {x : R} (hx : f.eval x != 0) :
    f.derivative.eval x = f.eval x * (f.roots.map fun z => 1 / (x - z)).sum := by
  classical
  simp only [hf.eval_derivative, hf.eval_eq_prod_roots, ← Multiset.sum_map_mul_left, mul_assoc]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl fun z hz => ?_)
  rw [← Multiset.prod_map_erase hz]; rw [mul_one_div]; rw [mul_div_cancel_left₀]
  aesop (add simp sub_eq_zero)

/--
theorem `Splits.eval_derivative_div_eval_of_ne_zero` / 定理 `Splits.eval_derivative_div_eval_of_ne_zero`

English:
theorem Splits.eval_derivative_div_eval_of_ne_zero
  given: (hf : Splits f) {x : R} (hx : f.eval x != 0)
  proof: by
  rw [hf.eval_derivative_eq_eval_mul_sum hx]; rw [mul_div_cancel_left₀ _ hx]

中文:
定理 Splits.eval_derivative_div_eval_of_ne_zero
  条件: (hf : Splits f) {x : R} (hx : f.eval x != 0)
  证明: by
  rw [hf.eval_derivative_eq_eval_mul_sum hx]; rw [mul_div_cancel_left₀ _ hx]

Depends on / 依赖: eval_derivative_eq_eval_mul_sum, hf.eval_derivative_eq_eval_mul_sum
-/
theorem Splits.eval_derivative_div_eval_of_ne_zero (hf : Splits f) {x : R} (hx : f.eval x != 0) :
    f.derivative.eval x / f.eval x = (f.roots.map fun z => 1 / (x - z)).sum := by
  rw [hf.eval_derivative_eq_eval_mul_sum hx]; rw [mul_div_cancel_left₀ _ hx]

/--
theorem `Splits.mem_subfield_of_isRoot` / 定理 `Splits.mem_subfield_of_isRoot`

English:
theorem Splits.mem_subfield_of_isRoot
  statement: (F : Subfield R) {f : F[X]} (hf : Splits f) (hf0 : f != 0)
  proof: by
  simpa using hf.mem_range_of_isRoot hf0 hx

中文:
定理 Splits.mem_subfield_of_isRoot
  结论: (F : 子域 R) {f : F[X]} (hf : Splits f) (hf0 : f != 0)
  证明: by
  simpa using hf.mem_range_of_isRoot hf0 hx

Depends on / 依赖: hf.mem_range_of_isRoot, mem_range_of_isRoot
-/
theorem Splits.mem_subfield_of_isRoot (F : Subfield R) {f : F[X]} (hf : Splits f) (hf0 : f != 0)
    {x : R} (hx : (f.map F.subtype).IsRoot x) : x in F := by
  simpa using hf.mem_range_of_isRoot hf0 hx

/--
theorem `Splits.of_natDegree_eq_two` / 定理 `Splits.of_natDegree_eq_two`

English:
theorem Splits.of_natDegree_eq_two
  given: {x : R} (h₁ : f.natDegree = 2) (h₂ : f.eval x = 0)
  proof: by
  have h : (f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C x)]; rw [h₁]; rw [natDegree_X_sub_C]
  rw [← mul_divByMonic_eq_iff_isRoot.mpr h₂]; rw [splits_mul (X_sub_C_ne_zero x) (by aesop)]
  exact ⟨Splits.X_sub_C x, Splits.of_natDegree_eq_one h⟩

中文:
定理 Splits.of_natDegree_eq_two
  条件: {x : R} (h₁ : f.natDegree = 2) (h₂ : f.eval x = 0)
  证明: by
  have h : (f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C x)]; rw [h₁]; rw [natDegree_X_sub_C]
  rw [← mul_divByMonic_eq_iff_isRoot.mpr h₂]; rw [splits_mul (X_sub_C_ne_zero x) (by aesop)]
  exact ⟨Splits.X_sub_C x, Splits.of_natDegree_eq_one h⟩

Depends on / 依赖: Splits, Splits.X_sub_C, Splits.of_natDegree_eq_one, X_sub_C, X_sub_C_ne_zero, monic_X_sub_C, mul_divByMonic_eq_iff_isRoot, mul_divByMonic_eq_iff_isRoot.mpr, natDegree, natDegree_X_sub_C, natDegree_divByMonic, of_natDegree_eq_one, splits_mul
-/
theorem Splits.of_natDegree_eq_two {x : R} (h₁ : f.natDegree = 2) (h₂ : f.eval x = 0) :
    Splits f := by
  have h : (f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C x)]; rw [h₁]; rw [natDegree_X_sub_C]
  rw [← mul_divByMonic_eq_iff_isRoot.mpr h₂]; rw [splits_mul (X_sub_C_ne_zero x) (by aesop)]
  exact ⟨Splits.X_sub_C x, Splits.of_natDegree_eq_one h⟩

/--
theorem `Splits.of_degree_eq_two` / 定理 `Splits.of_degree_eq_two`

English:
theorem Splits.of_degree_eq_two
  given: {x : R} (h₁ : f.degree = 2) (h₂ : f.eval x = 0)
  statement: Splits f
  proof: Splits.of_natDegree_eq_two (natDegree_eq_of_degree_eq_some h₁) h₂

中文:
定理 Splits.of_degree_eq_two
  条件: {x : R} (h₁ : f.degree = 2) (h₂ : f.eval x = 0)
  结论: Splits f
  证明: Splits.of_natDegree_eq_two (natDegree_eq_of_degree_eq_some h₁) h₂

Depends on / 依赖: Splits, Splits.of_natDegree_eq_two, natDegree_eq_of_degree_eq_some, of_natDegree_eq_two
-/
theorem Splits.of_degree_eq_two {x : R} (h₁ : f.degree = 2) (h₂ : f.eval x = 0) : Splits f :=
  Splits.of_natDegree_eq_two (natDegree_eq_of_degree_eq_some h₁) h₂

open UniqueFactorizationMonoid in
@[deprecated "Use `Splits.degree_eq_one_of_irreducible` instead." (since := "2026-01-13")]
/--
theorem `splits_iff_splits` / 定理 `splits_iff_splits`

English:
theorem splits_iff_splits
  given: {f : R[X]}
  proof: by
  refine ⟨fun hf => or_iff_not_imp_left.mpr fun h0 g hg hgf =>
    (hf.of_dvd h0 hgf).degree_eq_one_of_irreducible hg, ?_⟩
  rintro (rfl | hf)
  · aesop
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨u, hu⟩ := factors_prod hf0
  rw [← hu]
  refine (Splits.multisetProd fun g hg => ?_).mul u.isUnit.splits
  exact Splits.of_degree_eq_one (hf (irreducible_of_factor g hg) (dvd_of_mem_factors hg))

中文:
定理 splits_iff_splits
  条件: {f : R[X]}
  证明: by
  refine ⟨fun hf => or_iff_not_imp_left.mpr fun h0 g hg hgf =>
    (hf.of_dvd h0 hgf).degree_eq_one_of_irreducible hg, ?_⟩
  rintro (rfl | hf)
  · aesop
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨u, hu⟩ := factors_prod hf0
  rw [← hu]
  refine (Splits.multisetProd fun g hg => ?_).mul u.isUnit.splits
  exact Splits.of_degree_eq_one (hf (irreducible_of_factor g hg) (dvd_of_mem_factors hg))

Depends on / 依赖: Splits, Splits.multisetProd, Splits.of_degree_eq_one, degree_eq_one_of_irreducible, dvd_of_mem_factors, factors_prod, hf.of_dvd, irreducible_of_factor, isUnit, multisetProd, of_degree_eq_one, of_dvd, or_iff_not_imp_left, or_iff_not_imp_left.mpr, splits, u.isUnit.splits
-/
theorem splits_iff_splits {f : R[X]} :
    Splits f ↔ f = 0 ∨ forall {g : R[X]}, Irreducible g -> g ∣ f -> degree g = 1 := by
  refine ⟨fun hf => or_iff_not_imp_left.mpr fun h0 g hg hgf =>
    (hf.of_dvd h0 hgf).degree_eq_one_of_irreducible hg, ?_⟩
  rintro (rfl | hf)
  · aesop
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨u, hu⟩ := factors_prod hf0
  rw [← hu]
  refine (Splits.multisetProd fun g hg => ?_).mul u.isUnit.splits
  exact Splits.of_degree_eq_one (hf (irreducible_of_factor g hg) (dvd_of_mem_factors hg))

end Field

noncomputable section

open Polynomial

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

section Splits

section CommRing

variable [CommRing K] [Field L] [Field F]
variable (i : K ->+* L)

variable {i}

variable (i)

end CommRing

variable [CommRing R] [Field K] [Field L] [Field F]
variable (i : K ->+* L)

section UFD

attribute [local instance] PrincipalIdealRing.to_uniqueFactorizationMonoid

local infixl:50 " ~ᵤ " => Associated

open UniqueFactorizationMonoid Associates

end UFD

variable [Algebra R K] [Algebra R L]

end Splits

end

end Polynomial
