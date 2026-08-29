/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Separable

/-!

# Perfect fields and rings

In this file we define perfect fields, together with a generalisation to (commutative) rings in
prime characteristic.

## Main definitions / statements:
* `PerfectRing`: a ring of characteristic `p` (prime) is said to be perfect in the sense of Serre,
  if its absolute Frobenius map `x ↦ xᵖ` is bijective.
* `PerfectField`: a field `K` is said to be perfect if every irreducible polynomial over `K` is
  separable.
* `PerfectRing.toPerfectField`: a field that is perfect in the sense of Serre is a perfect field.
* `PerfectField.toPerfectRing`: a perfect field of characteristic `p` (prime) is perfect in the
  sense of Serre.
* `PerfectField.ofCharZero`: all fields of characteristic zero are perfect.
* `PerfectField.ofFinite`: all finite fields are perfect.
* `PerfectField.separable_iff_squarefree`: a polynomial over a perfect field is separable iff
  it is square-free.
* `Algebra.IsAlgebraic.isSeparable_of_perfectField`, `Algebra.IsAlgebraic.perfectField`:
  if `L / K` is an algebraic extension, `K` is a perfect field, then `L / K` is separable,
  and `L` is also a perfect field.

-/

@[expose] public section

open Function Polynomial

/--
Definition of `PerfectRing` / `PerfectRing` 的定义

English:
class PerfectRing
  parameters: (R : Type*) (p : Nat) [Pow R Nat]
  axioms and operations (1):
    - bijective_frobenius : Bijective fun x : R => x ^ p

中文:
类 完美环
  参数: (R : 类型) (p : 自然数) [幂 R 自然数]
  公理与运算 (1 个):
    - bijective_frobenius : 双射 fun x : R => x ^ p
-/
class PerfectRing (R : Type*) (p : Nat) [Pow R Nat] : Prop where
  /-- A ring is perfect if the Frobenius map is bijective. -/
  bijective_frobenius : Bijective fun x : R => x ^ p

section PerfectRing

section Monoid
variable (M : Type*) (p q : Nat) [CommMonoid M] [PerfectRing M p] [PerfectRing M q]

namespace PerfectRing

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : PerfectRing M 1
  body: ⟨by simpa using! bijective_id⟩

中文:
实例 one
  签名: : 完美环 M 1
  定义体: ⟨by simpa using! bijective_id⟩

Depends on / 依赖: bijective_id
-/
instance one : PerfectRing M 1 :=
  ⟨by simpa using! bijective_id⟩

/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : PerfectRing M (p * q)
  body: ⟨by simp_rw [pow_mul]; exact PerfectRing.bijective_frobenius.comp PerfectRing.bijective_frobenius⟩

中文:
实例 mul
  签名: : 完美环 M (p * q)
  定义体: ⟨by simp_rw [pow_mul]; exact PerfectRing.bijective_frobenius.comp PerfectRing.bijective_frobenius⟩

Depends on / 依赖: PerfectRing, PerfectRing.bijective_frobenius, PerfectRing.bijective_frobenius.comp, bijective_frobenius, pow_mul, simp_rw
-/
instance mul : PerfectRing M (p * q) :=
  ⟨by simp_rw [pow_mul]; exact PerfectRing.bijective_frobenius.comp PerfectRing.bijective_frobenius⟩

/--
Instance `pow` / 实例 `pow`

English:
instance pow
  signature: (n : Nat)
  body: n.recOn (inferInstanceAs (PerfectRing M 1)) fun n _ => inferInstanceAs (PerfectRing M (p ^ n * p))

中文:
实例 pow
  签名: (n : 自然数)
  定义体: n.recOn (inferInstanceAs (PerfectRing M 1)) fun n _ => inferInstanceAs (PerfectRing M (p ^ n * p))

Depends on / 依赖: PerfectRing, n.recOn
-/
instance pow (n : Nat) : PerfectRing M (p ^ n) :=
  n.recOn (inferInstanceAs (PerfectRing M 1)) fun n _ => inferInstanceAs (PerfectRing M (p ^ n * p))

end PerfectRing

/-- The `p`-th power automorphism for a perfect monoid. -/
@[simps! apply]
/--
Definition of `powMulEquiv` / `powMulEquiv` 的定义

English:
definition powMulEquiv
  signature: : M ≃* M
  body: .ofBijective (powMonoidHom p) PerfectRing.bijective_frobenius

@[simp]

中文:
定义 powMulEquiv
  签名: : M ≃* M
  定义体: .ofBijective (powMonoidHom p) PerfectRing.bijective_frobenius

@[simp]

Depends on / 依赖: PerfectRing, PerfectRing.bijective_frobenius, bijective_frobenius, ofBijective, powMonoidHom
-/
noncomputable def powMulEquiv : M ≃* M :=
  .ofBijective (powMonoidHom p) PerfectRing.bijective_frobenius

@[simp]
/--
theorem `powMulEquiv_symm_pow_p` / 定理 `powMulEquiv_symm_pow_p`

English:
theorem powMulEquiv_symm_pow_p
  given: (x : M)
  statement: ((powMulEquiv M p).symm x) ^ p = x
  proof: (powMulEquiv M p).apply_symm_apply x

中文:
定理 powMulEquiv_symm_pow_p
  条件: (x : M)
  结论: ((powMulEquiv M p).symm x) ^ p = x
  证明: (powMulEquiv M p).apply_symm_apply x

Depends on / 依赖: apply_symm_apply, powMulEquiv
-/
theorem powMulEquiv_symm_pow_p (x : M) : ((powMulEquiv M p).symm x) ^ p = x :=
  (powMulEquiv M p).apply_symm_apply x

/--
theorem `powMulEquiv_one` / 定理 `powMulEquiv_one`

English:
theorem powMulEquiv_one
  statement: powMulEquiv M 1 = .refl M
  proof: MulEquiv.ext pow_one

中文:
定理 powMulEquiv_one
  结论: powMulEquiv M 1 = .refl M
  证明: MulEquiv.ext pow_one
-/
@[simp] theorem powMulEquiv_one : powMulEquiv M 1 = .refl M :=
  MulEquiv.ext pow_one

/--
theorem `powMulEquiv_mul` / 定理 `powMulEquiv_mul`

English:
theorem powMulEquiv_mul
  statement: powMulEquiv M (p * q) = (powMulEquiv M p).trans (powMulEquiv M q)
  proof: MulEquiv.ext fun x => pow_mul x p q

中文:
定理 powMulEquiv_mul
  结论: powMulEquiv M (p * q) = (powMulEquiv M p).trans (powMulEquiv M q)
  证明: MulEquiv.ext fun x => pow_mul x p q

Depends on / 依赖: MulEquiv, MulEquiv.ext, pow_mul
-/
theorem powMulEquiv_mul : powMulEquiv M (p * q) = (powMulEquiv M p).trans (powMulEquiv M q) :=
  MulEquiv.ext fun x => pow_mul x p q

/--
theorem `powMulEquiv_mul'` / 定理 `powMulEquiv_mul'`

English:
theorem powMulEquiv_mul'
  statement: powMulEquiv M (p * q) = (powMulEquiv M q).trans (powMulEquiv M p)
  proof: MulEquiv.ext fun x => pow_mul' x p q

中文:
定理 powMulEquiv_mul'
  结论: powMulEquiv M (p * q) = (powMulEquiv M q).trans (powMulEquiv M p)
  证明: MulEquiv.ext fun x => pow_mul' x p q

Depends on / 依赖: MulEquiv, MulEquiv.ext, pow_mul
-/
theorem powMulEquiv_mul' : powMulEquiv M (p * q) = (powMulEquiv M q).trans (powMulEquiv M p) :=
  MulEquiv.ext fun x => pow_mul' x p q

/--
theorem `powMulEquiv_pow` / 定理 `powMulEquiv_pow`

English:
theorem powMulEquiv_pow
  given: (n : Nat)
  statement: powMulEquiv M (p ^ n) = powMulEquiv M p ^ n
  proof: n.recOn (powMulEquiv_one M) fun n ih => by
    rw [pow_succ (powMulEquiv M p)]; rw [← ih]; rw [MulAut.mul_def]; rw [← powMulEquiv_mul]
    congr
    rw [pow_succ']

中文:
定理 powMulEquiv_pow
  条件: (n : 自然数)
  结论: powMulEquiv M (p ^ n) = powMulEquiv M p ^ n
  证明: n.recOn (powMulEquiv_one M) fun n ih => by
    rw [pow_succ (powMulEquiv M p)]; rw [← ih]; rw [MulAut.mul_def]; rw [← powMulEquiv_mul]
    congr
    rw [pow_succ']

Depends on / 依赖: MulAut, MulAut.mul_def, mul_def, n.recOn, powMulEquiv, powMulEquiv_mul, powMulEquiv_one, pow_succ
-/
theorem powMulEquiv_pow (n : Nat) : powMulEquiv M (p ^ n) = powMulEquiv M p ^ n :=
  n.recOn (powMulEquiv_one M) fun n ih => by
    rw [pow_succ (powMulEquiv M p)]; rw [← ih]; rw [MulAut.mul_def]; rw [← powMulEquiv_mul]
    congr
    rw [pow_succ']

end Monoid

section CommSemiring
variable (R : Type*) (p m n : Nat) [CommSemiring R] [ExpChar R p]

/--
lemma `PerfectRing.ofSurjective` / 引理 `PerfectRing.ofSurjective`

English:
lemma PerfectRing.ofSurjective
  statement: (R : Type*) (p : Nat) [CommRing R] [ExpChar R p]
  proof: ⟨frobenius_inj R p, h⟩

中文:
引理 完美环.ofSurjective
  结论: (R : 类型) (p : 自然数) [交换环 R] [ExpChar R p]
  证明: ⟨frobenius_inj R p, h⟩

Depends on / 依赖: frobenius_inj
-/
lemma PerfectRing.ofSurjective (R : Type*) (p : Nat) [CommRing R] [ExpChar R p]
    [IsReduced R] (h : Surjective <| frobenius R p) : PerfectRing R p :=
  ⟨frobenius_inj R p, h⟩

/--
Instance `PerfectRing.ofFiniteOfIsReduced` / 实例 `PerfectRing.ofFiniteOfIsReduced`

English:
instance PerfectRing.ofFiniteOfIsReduced
  signature: (R : Type*) [CommRing R] [ExpChar R p]
  body: ofSurjective _ _ Finite.surjective_of_injective (frobenius_inj R p)

中文:
实例 完美环.ofFiniteOfIsReduced
  签名: (R : 类型) [交换环 R] [ExpChar R p]
  定义体: ofSurjective _ _ Finite.surjective_of_injective (frobenius_inj R p)

Depends on / 依赖: Finite, Finite.surjective_of_injective, frobenius_inj, ofSurjective, surjective_of_injective
-/
instance PerfectRing.ofFiniteOfIsReduced (R : Type*) [CommRing R] [ExpChar R p]
    [Finite R] [IsReduced R] : PerfectRing R p :=
ofSurjective _ _ Finite.surjective_of_injective (frobenius_inj R p)

variable [PerfectRing R p]

@[simp]
/--
theorem `bijective_frobenius` / 定理 `bijective_frobenius`

English:
theorem bijective_frobenius
  statement: Bijective (frobenius R p)
  proof: PerfectRing.bijective_frobenius

中文:
定理 bijective_frobenius
  结论: 双射 (frobenius R p)
  证明: PerfectRing.bijective_frobenius

Depends on / 依赖: PerfectRing, PerfectRing.bijective_frobenius, bijective_frobenius
-/
theorem bijective_frobenius : Bijective (frobenius R p) := PerfectRing.bijective_frobenius

/--
theorem `bijective_iterateFrobenius` / 定理 `bijective_iterateFrobenius`

English:
theorem bijective_iterateFrobenius
  statement: Bijective (iterateFrobenius R p n)
  proof: PerfectRing.bijective_frobenius

@[simp]

中文:
定理 bijective_iterateFrobenius
  结论: 双射 (iterateFrobenius R p n)
  证明: PerfectRing.bijective_frobenius

@[simp]

Depends on / 依赖: PerfectRing, PerfectRing.bijective_frobenius, bijective_frobenius
-/
theorem bijective_iterateFrobenius : Bijective (iterateFrobenius R p n) :=
  PerfectRing.bijective_frobenius

@[simp]
/--
theorem `injective_frobenius` / 定理 `injective_frobenius`

English:
theorem injective_frobenius
  statement: Injective (frobenius R p)
  proof: (bijective_frobenius R p).1

@[simp]

中文:
定理 injective_frobenius
  结论: 单射 (frobenius R p)
  证明: (bijective_frobenius R p).1

@[simp]

Depends on / 依赖: bijective_frobenius
-/
theorem injective_frobenius : Injective (frobenius R p) := (bijective_frobenius R p).1

@[simp]
/--
theorem `surjective_frobenius` / 定理 `surjective_frobenius`

English:
theorem surjective_frobenius
  statement: Surjective (frobenius R p)
  proof: (bijective_frobenius R p).2

中文:
定理 surjective_frobenius
  结论: 满射 (frobenius R p)
  证明: (bijective_frobenius R p).2

Depends on / 依赖: bijective_frobenius
-/
theorem surjective_frobenius : Surjective (frobenius R p) := (bijective_frobenius R p).2

/-- The Frobenius automorphism for a perfect ring. -/
@[simps! apply]
/--
Definition of `frobeniusEquiv` / `frobeniusEquiv` 的定义

English:
definition frobeniusEquiv
  signature: : R ≃+* R
  body: RingEquiv.ofBijective (frobenius R p) PerfectRing.bijective_frobenius

中文:
定义 frobeniusEquiv
  签名: : R ≃+* R
  定义体: RingEquiv.ofBijective (frobenius R p) PerfectRing.bijective_frobenius

Depends on / 依赖: PerfectRing, PerfectRing.bijective_frobenius, RingEquiv, RingEquiv.ofBijective, bijective_frobenius, frobenius, ofBijective
-/
noncomputable def frobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (frobenius R p) PerfectRing.bijective_frobenius

/--
theorem `powMulEquiv_eq_toMulEquiv_frobeniusEquiv` / 定理 `powMulEquiv_eq_toMulEquiv_frobeniusEquiv`

English:
theorem powMulEquiv_eq_toMulEquiv_frobeniusEquiv
  proof: rfl

@[simp]

中文:
定理 powMulEquiv_eq_toMulEquiv_frobeniusEquiv
  证明: rfl

@[simp]
-/
@[simp] theorem powMulEquiv_eq_toMulEquiv_frobeniusEquiv :
    powMulEquiv R p = (frobeniusEquiv R p).toMulEquiv := rfl

@[simp]
/--
theorem `coe_frobeniusEquiv` / 定理 `coe_frobeniusEquiv`

English:
theorem coe_frobeniusEquiv
  statement: ⇑(frobeniusEquiv R p) = frobenius R p
  proof: rfl

中文:
定理 coe_frobeniusEquiv
  结论: ⇑(frobeniusEquiv R p) = frobenius R p
  证明: rfl
-/
theorem coe_frobeniusEquiv : ⇑(frobeniusEquiv R p) = frobenius R p := rfl

/--
theorem `frobeniusEquiv_def` / 定理 `frobeniusEquiv_def`

English:
theorem frobeniusEquiv_def
  given: (x : R)
  statement: frobeniusEquiv R p x = x ^ p
  proof: rfl

中文:
定理 frobeniusEquiv_def
  条件: (x : R)
  结论: frobeniusEquiv R p x = x ^ p
  证明: rfl
-/
theorem frobeniusEquiv_def (x : R) : frobeniusEquiv R p x = x ^ p := rfl

/-- The iterated Frobenius automorphism for a perfect ring. -/
@[simps! apply]
/--
Definition of `iterateFrobeniusEquiv` / `iterateFrobeniusEquiv` 的定义

English:
definition iterateFrobeniusEquiv
  signature: : R ≃+* R
  body: RingEquiv.ofBijective (iterateFrobenius R p n) (bijective_iterateFrobenius R p n)

@[simp]

中文:
定义 iterateFrobeniusEquiv
  签名: : R ≃+* R
  定义体: RingEquiv.ofBijective (iterateFrobenius R p n) (bijective_iterateFrobenius R p n)

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, bijective_iterateFrobenius, iterateFrobenius, ofBijective
-/
noncomputable def iterateFrobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (iterateFrobenius R p n) (bijective_iterateFrobenius R p n)

@[simp]
/--
theorem `coe_iterateFrobeniusEquiv` / 定理 `coe_iterateFrobeniusEquiv`

English:
theorem coe_iterateFrobeniusEquiv
  statement: ⇑(iterateFrobeniusEquiv R p n) = iterateFrobenius R p n
  proof: rfl

中文:
定理 coe_iterateFrobeniusEquiv
  结论: ⇑(iterateFrobeniusEquiv R p n) = iterateFrobenius R p n
  证明: rfl
-/
theorem coe_iterateFrobeniusEquiv : ⇑(iterateFrobeniusEquiv R p n) = iterateFrobenius R p n := rfl

/--
theorem `iterateFrobeniusEquiv_def` / 定理 `iterateFrobeniusEquiv_def`

English:
theorem iterateFrobeniusEquiv_def
  given: (x : R)
  statement: iterateFrobeniusEquiv R p n x = x ^ p ^ n
  proof: rfl

中文:
定理 iterateFrobeniusEquiv_def
  条件: (x : R)
  结论: iterateFrobeniusEquiv R p n x = x ^ p ^ n
  证明: rfl
-/
theorem iterateFrobeniusEquiv_def (x : R) : iterateFrobeniusEquiv R p n x = x ^ p ^ n := rfl

/--
theorem `iterateFrobeniusEquiv_add_apply` / 定理 `iterateFrobeniusEquiv_add_apply`

English:
theorem iterateFrobeniusEquiv_add_apply
  given: (x : R)
  statement: iterateFrobeniusEquiv R p (m + n) x =
  proof: iterateFrobenius_add_apply R p m n x

中文:
定理 iterateFrobeniusEquiv_add_apply
  条件: (x : R)
  结论: iterateFrobeniusEquiv R p (m + n) x =
  证明: iterateFrobenius_add_apply R p m n x

Depends on / 依赖: iterateFrobenius_add_apply
-/
theorem iterateFrobeniusEquiv_add_apply (x : R) : iterateFrobeniusEquiv R p (m + n) x =
    iterateFrobeniusEquiv R p m (iterateFrobeniusEquiv R p n x) :=
  iterateFrobenius_add_apply R p m n x

/--
theorem `iterateFrobeniusEquiv_add` / 定理 `iterateFrobeniusEquiv_add`

English:
theorem iterateFrobeniusEquiv_add
  statement: iterateFrobeniusEquiv R p (m + n) =
  proof: RingEquiv.ext (iterateFrobeniusEquiv_add_apply R p m n)

中文:
定理 iterateFrobeniusEquiv_add
  结论: iterateFrobeniusEquiv R p (m + n) =
  证明: RingEquiv.ext (iterateFrobeniusEquiv_add_apply R p m n)

Depends on / 依赖: RingEquiv, RingEquiv.ext, iterateFrobeniusEquiv_add_apply
-/
theorem iterateFrobeniusEquiv_add : iterateFrobeniusEquiv R p (m + n) =
    (iterateFrobeniusEquiv R p n).trans (iterateFrobeniusEquiv R p m) :=
  RingEquiv.ext (iterateFrobeniusEquiv_add_apply R p m n)

/--
theorem `iterateFrobeniusEquiv_symm_add_apply` / 定理 `iterateFrobeniusEquiv_symm_add_apply`

English:
theorem iterateFrobeniusEquiv_symm_add_apply
  given: (x : R)
  statement: (iterateFrobeniusEquiv R p (m + n)).symm x =
  proof: (iterateFrobeniusEquiv R p (m + n)).injective by rw [RingEquiv.apply_symm_apply, add_comm,
    iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

中文:
定理 iterateFrobeniusEquiv_symm_add_apply
  条件: (x : R)
  结论: (iterateFrobeniusEquiv R p (m + n)).symm x =
  证明: (iterateFrobeniusEquiv R p (m + n)).injective by rw [RingEquiv.apply_symm_apply, add_comm,
    iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

Depends on / 依赖: RingEquiv, RingEquiv.apply_symm_apply, add_comm, apply_symm_apply, injective, iterateFrobeniusEquiv, iterateFrobeniusEquiv_add_apply
-/
theorem iterateFrobeniusEquiv_symm_add_apply (x : R) : (iterateFrobeniusEquiv R p (m + n)).symm x =
    (iterateFrobeniusEquiv R p m).symm ((iterateFrobeniusEquiv R p n).symm x) :=
(iterateFrobeniusEquiv R p (m + n)).injective by rw [RingEquiv.apply_symm_apply, add_comm,
    iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/--
theorem `iterateFrobeniusEquiv_symm_add` / 定理 `iterateFrobeniusEquiv_symm_add`

English:
theorem iterateFrobeniusEquiv_symm_add
  statement: (iterateFrobeniusEquiv R p (m + n)).symm =
  proof: RingEquiv.ext (iterateFrobeniusEquiv_symm_add_apply R p m n)

中文:
定理 iterateFrobeniusEquiv_symm_add
  结论: (iterateFrobeniusEquiv R p (m + n)).symm =
  证明: RingEquiv.ext (iterateFrobeniusEquiv_symm_add_apply R p m n)

Depends on / 依赖: RingEquiv, RingEquiv.ext, iterateFrobeniusEquiv_symm_add_apply
-/
theorem iterateFrobeniusEquiv_symm_add : (iterateFrobeniusEquiv R p (m + n)).symm =
    (iterateFrobeniusEquiv R p n).symm.trans (iterateFrobeniusEquiv R p m).symm :=
  RingEquiv.ext (iterateFrobeniusEquiv_symm_add_apply R p m n)

/--
theorem `iterateFrobeniusEquiv_zero_apply` / 定理 `iterateFrobeniusEquiv_zero_apply`

English:
theorem iterateFrobeniusEquiv_zero_apply
  given: (x : R)
  statement: iterateFrobeniusEquiv R p 0 x = x
  proof: by
  rw [iterateFrobeniusEquiv_def]; rw [pow_zero]; rw [pow_one]

中文:
定理 iterateFrobeniusEquiv_zero_apply
  条件: (x : R)
  结论: iterateFrobeniusEquiv R p 0 x = x
  证明: by
  rw [iterateFrobeniusEquiv_def]; rw [pow_zero]; rw [pow_one]

Depends on / 依赖: iterateFrobeniusEquiv_def, pow_one, pow_zero
-/
theorem iterateFrobeniusEquiv_zero_apply (x : R) : iterateFrobeniusEquiv R p 0 x = x := by
  rw [iterateFrobeniusEquiv_def]; rw [pow_zero]; rw [pow_one]

/--
theorem `iterateFrobeniusEquiv_one_apply` / 定理 `iterateFrobeniusEquiv_one_apply`

English:
theorem iterateFrobeniusEquiv_one_apply
  given: (x : R)
  statement: iterateFrobeniusEquiv R p 1 x = x ^ p
  proof: by
  rw [iterateFrobeniusEquiv_def]; rw [pow_one]

@[simp]

中文:
定理 iterateFrobeniusEquiv_one_apply
  条件: (x : R)
  结论: iterateFrobeniusEquiv R p 1 x = x ^ p
  证明: by
  rw [iterateFrobeniusEquiv_def]; rw [pow_one]

@[simp]

Depends on / 依赖: iterateFrobeniusEquiv_def, pow_one
-/
theorem iterateFrobeniusEquiv_one_apply (x : R) : iterateFrobeniusEquiv R p 1 x = x ^ p := by
  rw [iterateFrobeniusEquiv_def]; rw [pow_one]

@[simp]
/--
theorem `iterateFrobeniusEquiv_zero` / 定理 `iterateFrobeniusEquiv_zero`

English:
theorem iterateFrobeniusEquiv_zero
  statement: iterateFrobeniusEquiv R p 0 = RingEquiv.refl R
  proof: RingEquiv.ext (iterateFrobeniusEquiv_zero_apply R p)

@[simp]

中文:
定理 iterateFrobeniusEquiv_zero
  结论: iterateFrobeniusEquiv R p 0 = 环等价.refl R
  证明: RingEquiv.ext (iterateFrobeniusEquiv_zero_apply R p)

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.ext, iterateFrobeniusEquiv_zero_apply
-/
theorem iterateFrobeniusEquiv_zero : iterateFrobeniusEquiv R p 0 = RingEquiv.refl R :=
  RingEquiv.ext (iterateFrobeniusEquiv_zero_apply R p)

@[simp]
/--
theorem `iterateFrobeniusEquiv_one` / 定理 `iterateFrobeniusEquiv_one`

English:
theorem iterateFrobeniusEquiv_one
  statement: iterateFrobeniusEquiv R p 1 = frobeniusEquiv R p
  proof: RingEquiv.ext (iterateFrobeniusEquiv_one_apply R p)

中文:
定理 iterateFrobeniusEquiv_one
  结论: iterateFrobeniusEquiv R p 1 = frobeniusEquiv R p
  证明: RingEquiv.ext (iterateFrobeniusEquiv_one_apply R p)

Depends on / 依赖: RingEquiv, RingEquiv.ext, iterateFrobeniusEquiv_one_apply
-/
theorem iterateFrobeniusEquiv_one : iterateFrobeniusEquiv R p 1 = frobeniusEquiv R p :=
  RingEquiv.ext (iterateFrobeniusEquiv_one_apply R p)

/--
theorem `iterateFrobeniusEquiv_eq_pow` / 定理 `iterateFrobeniusEquiv_eq_pow`

English:
theorem iterateFrobeniusEquiv_eq_pow
  statement: iterateFrobeniusEquiv R p n = frobeniusEquiv R p ^ n
  proof: DFunLike.ext' show _ = ⇑(RingAut.toPerm _ _) by
    rw [map_pow]; rw [Equiv.Perm.coe_pow]; exact (pow_iterate p n).symm

中文:
定理 iterateFrobeniusEquiv_eq_pow
  结论: iterateFrobeniusEquiv R p n = frobeniusEquiv R p ^ n
  证明: DFunLike.ext' show _ = ⇑(RingAut.toPerm _ _) by
    rw [map_pow]; rw [Equiv.Perm.coe_pow]; exact (pow_iterate p n).symm

Depends on / 依赖: DFunLike, DFunLike.ext, Equiv.Perm.coe_pow, RingAut, RingAut.toPerm, coe_pow, map_pow, pow_iterate, toPerm
-/
theorem iterateFrobeniusEquiv_eq_pow : iterateFrobeniusEquiv R p n = frobeniusEquiv R p ^ n :=
DFunLike.ext' show _ = ⇑(RingAut.toPerm _ _) by
    rw [map_pow]; rw [Equiv.Perm.coe_pow]; exact (pow_iterate p n).symm

/--
theorem `iterateFrobeniusEquiv_symm` / 定理 `iterateFrobeniusEquiv_symm`

English:
theorem iterateFrobeniusEquiv_symm
  proof: by
  rw [iterateFrobeniusEquiv_eq_pow]; exact (inv_pow _ _).symm

@[simp]

中文:
定理 iterateFrobeniusEquiv_symm
  证明: by
  rw [iterateFrobeniusEquiv_eq_pow]; exact (inv_pow _ _).symm

@[simp]

Depends on / 依赖: inv_pow, iterateFrobeniusEquiv_eq_pow
-/
theorem iterateFrobeniusEquiv_symm :
    (iterateFrobeniusEquiv R p n).symm = (frobeniusEquiv R p).symm ^ n := by
  rw [iterateFrobeniusEquiv_eq_pow]; exact (inv_pow _ _).symm

@[simp]
/--
theorem `frobeniusEquiv_symm_apply_frobenius` / 定理 `frobeniusEquiv_symm_apply_frobenius`

English:
theorem frobeniusEquiv_symm_apply_frobenius
  given: (x : R)
  proof: (frobeniusEquiv R p).symm_apply_apply x

@[simp]

中文:
定理 frobeniusEquiv_symm_apply_frobenius
  条件: (x : R)
  证明: (frobeniusEquiv R p).symm_apply_apply x

@[simp]

Depends on / 依赖: frobeniusEquiv, symm_apply_apply
-/
theorem frobeniusEquiv_symm_apply_frobenius (x : R) :
    (frobeniusEquiv R p).symm (frobenius R p x) = x :=
  (frobeniusEquiv R p).symm_apply_apply x

@[simp]
/--
theorem `frobenius_apply_frobeniusEquiv_symm` / 定理 `frobenius_apply_frobeniusEquiv_symm`

English:
theorem frobenius_apply_frobeniusEquiv_symm
  given: (x : R)
  proof: (frobeniusEquiv R p).apply_symm_apply x

@[simp]

中文:
定理 frobenius_apply_frobeniusEquiv_symm
  条件: (x : R)
  证明: (frobeniusEquiv R p).apply_symm_apply x

@[simp]

Depends on / 依赖: apply_symm_apply, frobeniusEquiv
-/
theorem frobenius_apply_frobeniusEquiv_symm (x : R) :
    frobenius R p ((frobeniusEquiv R p).symm x) = x :=
  (frobeniusEquiv R p).apply_symm_apply x

@[simp]
/--
theorem `frobenius_comp_frobeniusEquiv_symm` / 定理 `frobenius_comp_frobeniusEquiv_symm`

English:
theorem frobenius_comp_frobeniusEquiv_symm
  proof: by
  ext; simp

@[simp]

中文:
定理 frobenius_comp_frobeniusEquiv_symm
  证明: by
  ext; simp

@[simp]
-/
theorem frobenius_comp_frobeniusEquiv_symm :
    (frobenius R p).comp (frobeniusEquiv R p).symm = RingHom.id R := by
  ext; simp

@[simp]
/--
theorem `frobeniusEquiv_symm_comp_frobenius` / 定理 `frobeniusEquiv_symm_comp_frobenius`

English:
theorem frobeniusEquiv_symm_comp_frobenius
  proof: by
  ext; simp

@[simp]

中文:
定理 frobeniusEquiv_symm_comp_frobenius
  证明: by
  ext; simp

@[simp]
-/
theorem frobeniusEquiv_symm_comp_frobenius :
    ((frobeniusEquiv R p).symm : R ->+* R).comp (frobenius R p) = RingHom.id R := by
  ext; simp

@[simp]
/--
theorem `coe_frobenius_comp_coe_frobeniusEquiv_symm` / 定理 `coe_frobenius_comp_coe_frobeniusEquiv_symm`

English:
theorem coe_frobenius_comp_coe_frobeniusEquiv_symm
  proof: by
  ext
  simp

@[simp]

中文:
定理 coe_frobenius_comp_coe_frobeniusEquiv_symm
  证明: by
  ext
  simp

@[simp]
-/
theorem coe_frobenius_comp_coe_frobeniusEquiv_symm :
    ⇑(frobenius R p) ∘ ⇑(frobeniusEquiv R p).symm = id := by
  ext
  simp

@[simp]
/--
theorem `coe_frobeniusEquiv_symm_comp_coe_frobenius` / 定理 `coe_frobeniusEquiv_symm_comp_coe_frobenius`

English:
theorem coe_frobeniusEquiv_symm_comp_coe_frobenius
  proof: by
  ext
  simp

@[simp]

中文:
定理 coe_frobeniusEquiv_symm_comp_coe_frobenius
  证明: by
  ext
  simp

@[simp]
-/
theorem coe_frobeniusEquiv_symm_comp_coe_frobenius :
    ⇑(frobeniusEquiv R p).symm ∘ ⇑(frobenius R p) = id := by
  ext
  simp

@[simp]
/--
theorem `frobeniusEquiv_symm_pow_p` / 定理 `frobeniusEquiv_symm_pow_p`

English:
theorem frobeniusEquiv_symm_pow_p
  given: (x : R)
  statement: ((frobeniusEquiv R p).symm x) ^ p = x
  proof: frobenius_apply_frobeniusEquiv_symm R p x

中文:
定理 frobeniusEquiv_symm_pow_p
  条件: (x : R)
  结论: ((frobeniusEquiv R p).symm x) ^ p = x
  证明: frobenius_apply_frobeniusEquiv_symm R p x

Depends on / 依赖: frobenius_apply_frobeniusEquiv_symm
-/
theorem frobeniusEquiv_symm_pow_p (x : R) : ((frobeniusEquiv R p).symm x) ^ p = x :=
  frobenius_apply_frobeniusEquiv_symm R p x

/--
lemma `frobeniusEquiv_symm_pow` / 引理 `frobeniusEquiv_symm_pow`

English:
lemma frobeniusEquiv_symm_pow
  given: (x : R)
  statement: (frobeniusEquiv R p).symm (x ^ p) = x
  proof: (frobeniusEquiv R p).symm_apply_apply x

@[simp]

中文:
引理 frobeniusEquiv_symm_pow
  条件: (x : R)
  结论: (frobeniusEquiv R p).symm (x ^ p) = x
  证明: (frobeniusEquiv R p).symm_apply_apply x

@[simp]

Depends on / 依赖: frobeniusEquiv, symm_apply_apply
-/
lemma frobeniusEquiv_symm_pow (x : R) : (frobeniusEquiv R p).symm (x ^ p) = x :=
  (frobeniusEquiv R p).symm_apply_apply x

@[simp]
/--
theorem `iterate_frobeniusEquiv_symm_pow_p_pow` / 定理 `iterate_frobeniusEquiv_symm_pow_p_pow`

English:
theorem iterate_frobeniusEquiv_symm_pow_p_pow
  given: (x : R) (n : Nat)
  proof: by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih]

中文:
定理 iterate_frobeniusEquiv_symm_pow_p_pow
  条件: (x : R) (n : 自然数)
  证明: by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih]

Depends on / 依赖: generalizing, pow_mul, pow_succ
-/
theorem iterate_frobeniusEquiv_symm_pow_p_pow (x : R) (n : Nat) :
    ((frobeniusEquiv R p).symm^[n]) x ^ (p ^ n) = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih]

section commute

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (p : Nat)
    [ExpChar R p] [PerfectRing R p] [ExpChar S p] [PerfectRing S p]

/--
theorem `MonoidHom.map_frobeniusEquiv_symm` / 定理 `MonoidHom.map_frobeniusEquiv_symm`

English:
theorem MonoidHom.map_frobeniusEquiv_symm
  given: (f : R ->* S) (x : R)
  proof: by
  apply_fun (frobeniusEquiv S p)
  simp [← MonoidHom.map_frobenius]

中文:
定理 幺半群态射.map_frobeniusEquiv_symm
  条件: (f : R ->* S) (x : R)
  证明: by
  apply_fun (frobeniusEquiv S p)
  simp [← MonoidHom.map_frobenius]

Depends on / 依赖: MonoidHom, MonoidHom.map_frobenius, apply_fun, frobeniusEquiv, map_frobenius
-/
theorem MonoidHom.map_frobeniusEquiv_symm (f : R ->* S) (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := by
  apply_fun (frobeniusEquiv S p)
  simp [← MonoidHom.map_frobenius]

/--
theorem `RingHom.map_frobeniusEquiv_symm` / 定理 `RingHom.map_frobeniusEquiv_symm`

English:
theorem RingHom.map_frobeniusEquiv_symm
  given: (f : R ->+* S) (x : R)
  proof: by
  apply_fun (frobeniusEquiv S p)
  simp [← RingHom.map_frobenius]

中文:
定理 环态射.map_frobeniusEquiv_symm
  条件: (f : R ->+* S) (x : R)
  证明: by
  apply_fun (frobeniusEquiv S p)
  simp [← RingHom.map_frobenius]

Depends on / 依赖: RingHom, RingHom.map_frobenius, apply_fun, frobeniusEquiv, map_frobenius
-/
theorem RingHom.map_frobeniusEquiv_symm (f : R ->+* S) (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := by
  apply_fun (frobeniusEquiv S p)
  simp [← RingHom.map_frobenius]

/--
theorem `MonoidHom.map_iterate_frobeniusEquiv_symm` / 定理 `MonoidHom.map_iterate_frobeniusEquiv_symm`

English:
theorem MonoidHom.map_iterate_frobeniusEquiv_symm
  given: (f : R ->* S) (n : Nat) (x : R)
  proof: by
  apply_fun (frobeniusEquiv S p)^[n]
  · simp only [coe_frobeniusEquiv, ← map_iterate_frobenius]
    · rw [← Function.comp_apply (f := (⇑(frobenius R p))^[n]),
          ← Function.comp_apply (f := (⇑(frobenius S p))^[n]),
          ← Function.Commute.comp_iterate, ← Function.Commute.comp_iterate

中文:
定理 幺半群态射.map_iterate_frobeniusEquiv_symm
  条件: (f : R ->* S) (n : 自然数) (x : R)
  证明: by
  apply_fun (frobeniusEquiv S p)^[n]
  · simp only [coe_frobeniusEquiv, ← map_iterate_frobenius]
    · rw [← Function.comp_apply (f := (⇑(frobenius R p))^[n]),
          ← Function.comp_apply (f := (⇑(frobenius S p))^[n]),
          ← Function.Commute.comp_iterate, ← Function.Commute.comp_iterate

Depends on / 依赖: Commute, Function, Function.Commute, Function.Commute.comp_iterate, Function.Injective.iterate, Function.Semiconj, Function.comp_apply, Injective, Semiconj, all_goals, apply_fun, coe_frobeniusEquiv, comp_apply, comp_iterate, frobenius, frobeniusEquiv, iterate, map_iterate_frobenius
-/
theorem MonoidHom.map_iterate_frobeniusEquiv_symm (f : R ->* S) (n : Nat) (x : R) :
    f (((frobeniusEquiv R p).symm^[n]) x) = ((frobeniusEquiv S p).symm^[n]) (f x) := by
  apply_fun (frobeniusEquiv S p)^[n]
  · simp only [coe_frobeniusEquiv, ← map_iterate_frobenius]
    · rw [← Function.comp_apply (f := (⇑(frobenius R p))^[n]),
          ← Function.comp_apply (f := (⇑(frobenius S p))^[n]),
          ← Function.Commute.comp_iterate, ← Function.Commute.comp_iterate]
      · simp
      all_goals rw [← coe_frobeniusEquiv]; simp [Function.Commute, Function.Semiconj]
  apply Function.Injective.iterate
  simp

/--
theorem `RingHom.map_iterate_frobeniusEquiv_symm` / 定理 `RingHom.map_iterate_frobeniusEquiv_symm`

English:
theorem RingHom.map_iterate_frobeniusEquiv_symm
  given: (f : R ->+* S) (n : Nat) (x : R)
  proof: MonoidHom.map_iterate_frobeniusEquiv_symm p (f.toMonoidHom) n x

中文:
定理 环态射.map_iterate_frobeniusEquiv_symm
  条件: (f : R ->+* S) (n : 自然数) (x : R)
  证明: MonoidHom.map_iterate_frobeniusEquiv_symm p (f.toMonoidHom) n x

Depends on / 依赖: MonoidHom, MonoidHom.map_iterate_frobeniusEquiv_symm, f.toMonoidHom, map_iterate_frobeniusEquiv_symm, toMonoidHom
-/
theorem RingHom.map_iterate_frobeniusEquiv_symm (f : R ->+* S) (n : Nat) (x : R) :
    f (((frobeniusEquiv R p).symm^[n]) x) = ((frobeniusEquiv S p).symm^[n]) (f x) :=
  MonoidHom.map_iterate_frobeniusEquiv_symm p (f.toMonoidHom) n x

end commute

/--
theorem `injective_pow_p` / 定理 `injective_pow_p`

English:
theorem injective_pow_p
  given: {x y : R} (h : x ^ p = y ^ p)
  statement: x = y
  proof: (frobeniusEquiv R p).injective h

中文:
定理 injective_pow_p
  条件: {x y : R} (h : x ^ p = y ^ p)
  结论: x = y
  证明: (frobeniusEquiv R p).injective h

Depends on / 依赖: frobeniusEquiv, injective
-/
theorem injective_pow_p {x y : R} (h : x ^ p = y ^ p) : x = y := (frobeniusEquiv R p).injective h

/--
lemma `polynomial_expand_eq` / 引理 `polynomial_expand_eq`

English:
lemma polynomial_expand_eq
  given: (f : R[X])
  proof: by
  rw [← (f.map (S := R) (frobeniusEquiv R p).symm).map_frobenius_expand p]; rw [map_expand]; rw [map_map]; rw [frobenius_comp_frobeniusEquiv_symm]; rw [map_id]

@[simp]

中文:
引理 polynomial_expand_eq
  条件: (f : R[X])
  证明: by
  rw [← (f.map (S := R) (frobeniusEquiv R p).symm).map_frobenius_expand p]; rw [map_expand]; rw [map_map]; rw [frobenius_comp_frobeniusEquiv_symm]; rw [map_id]

@[simp]

Depends on / 依赖: f.map, frobeniusEquiv, frobenius_comp_frobeniusEquiv_symm, map_expand, map_frobenius_expand, map_id, map_map
-/
lemma polynomial_expand_eq (f : R[X]) :
    expand R p f = (f.map (frobeniusEquiv R p).symm) ^ p := by
  rw [← (f.map (S := R) (frobeniusEquiv R p).symm).map_frobenius_expand p]; rw [map_expand]; rw [map_map]; rw [frobenius_comp_frobeniusEquiv_symm]; rw [map_id]

@[simp]
/--
theorem `not_irreducible_expand` / 定理 `not_irreducible_expand`

English:
theorem not_irreducible_expand
  statement: (R p) [CommSemiring R] [Fact p.Prime] [CharP R p] [PerfectRing R p]
  proof: by
  rw [polynomial_expand_eq]
  exact not_irreducible_pow (Fact.out : p.Prime).ne_one

中文:
定理 not_irreducible_expand
  结论: (R p) [交换半环 R] [Fact p.素] [特征p R p] [完美环 R p]
  证明: by
  rw [polynomial_expand_eq]
  exact not_irreducible_pow (Fact.out : p.Prime).ne_one

Depends on / 依赖: Fact.out, ne_one, not_irreducible_pow, p.Prime, polynomial_expand_eq
-/
theorem not_irreducible_expand (R p) [CommSemiring R] [Fact p.Prime] [CharP R p] [PerfectRing R p]
    (f : R[X]) : ¬ Irreducible (expand R p f) := by
  rw [polynomial_expand_eq]
  exact not_irreducible_pow (Fact.out : p.Prime).ne_one

/--
Instance `instPerfectRingProd` / 实例 `instPerfectRingProd`

English:
instance instPerfectRingProd
  signature: (S : Type*) [CommSemiring S] [ExpChar S p] [PerfectRing S p]
  body: (bijective_frobenius R p).prodMap (bijective_frobenius S p)

中文:
实例 instPerfectRingProd
  签名: (S : 类型) [交换半环 S] [ExpChar S p] [完美环 S p]
  定义体: (bijective_frobenius R p).prodMap (bijective_frobenius S p)

Depends on / 依赖: bijective_frobenius, prodMap
-/
instance instPerfectRingProd (S : Type*) [CommSemiring S] [ExpChar S p] [PerfectRing S p] :
    PerfectRing (R × S) p where
  bijective_frobenius := (bijective_frobenius R p).prodMap (bijective_frobenius S p)

end CommSemiring

end PerfectRing

/--
Definition of `PerfectField` / `PerfectField` 的定义

English:
class PerfectField
  parameters: (K : Type*) [Field K]
  axioms and operations (1):
    - separable_of_irreducible : forall {f : K[X]}, Irreducible f -> f.Separable

中文:
类 完美域
  参数: (K : 类型) [域 K]
  公理与运算 (1 个):
    - separable_of_irreducible : 对任意 {f : K[X]}, 不可约 f -> f.可分
-/
class PerfectField (K : Type*) [Field K] : Prop where
  /-- A field is perfect if every irreducible polynomial is separable. -/
  separable_of_irreducible : forall {f : K[X]}, Irreducible f -> f.Separable

/--
lemma `PerfectRing.toPerfectField` / 引理 `PerfectRing.toPerfectField`

English:
lemma PerfectRing.toPerfectField
  statement: (K : Type*) (p : Nat)
  proof: by
  obtain hp | ⟨hp⟩ := ‹ExpChar K p›
  · exact ⟨Irreducible.separable⟩
  refine PerfectField.mk fun hf => ?_
  rcases separable_or p hf with h | ⟨-, g, -, rfl⟩
  · assumption
  · exfalso; revert hf; have := Fact.mk hp; simp

中文:
引理 完美环.toPerfectField
  结论: (K : 类型) (p : 自然数)
  证明: by
  obtain hp | ⟨hp⟩ := ‹ExpChar K p›
  · exact ⟨Irreducible.separable⟩
  refine PerfectField.mk fun hf => ?_
  rcases separable_or p hf with h | ⟨-, g, -, rfl⟩
  · assumption
  · exfalso; revert hf; have := Fact.mk hp; simp

Depends on / 依赖: ExpChar, Fact.mk, Irreducible, Irreducible.separable, PerfectField, PerfectField.mk, revert, separable, separable_or
-/
lemma PerfectRing.toPerfectField (K : Type*) (p : Nat)
    [Field K] [ExpChar K p] [PerfectRing K p] : PerfectField K := by
  obtain hp | ⟨hp⟩ := ‹ExpChar K p›
  · exact ⟨Irreducible.separable⟩
  refine PerfectField.mk fun hf => ?_
  rcases separable_or p hf with h | ⟨-, g, -, rfl⟩
  · assumption
  · exfalso; revert hf; have := Fact.mk hp; simp

namespace PerfectField

variable {K : Type*} [Field K]

/--
Instance `ofCharZero` / 实例 `ofCharZero`

English:
instance ofCharZero
  signature: [CharZero K]
  body: ⟨Irreducible.separable⟩

中文:
实例 ofCharZero
  签名: [特征零 K]
  定义体: ⟨Irreducible.separable⟩

Depends on / 依赖: Irreducible, Irreducible.separable, separable
-/
instance ofCharZero [CharZero K] : PerfectField K := ⟨Irreducible.separable⟩

/--
Instance `ofFinite` / 实例 `ofFinite`

English:
instance ofFinite
  signature: [Finite K]
  body: by
  obtain ⟨p, _instP⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  exact PerfectRing.toPerfectField K p

中文:
实例 ofFinite
  签名: [有限 K]
  定义体: by
  obtain ⟨p, _instP⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  exact PerfectRing.toPerfectField K p

Depends on / 依赖: CharP.char_is_prime, CharP.exists, PerfectRing, PerfectRing.toPerfectField, _instP, char_is_prime, p.Prime, toPerfectField
-/
instance ofFinite [Finite K] : PerfectField K := by
  obtain ⟨p, _instP⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  exact PerfectRing.toPerfectField K p

variable [PerfectField K]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `toPerfectRing` / 实例 `toPerfectRing`

English:
instance toPerfectRing
  signature: (p : Nat) [hp : ExpChar K p]
  body: by
  refine PerfectRing.ofSurjective _ _ fun y => ?_
  rcases hp with _ | hp
  · simp [frobenius]
  rw [← not_forall_not]
  apply mt (X_pow_sub_C_irreducible_of_prime hp)
  apply mt separable_of_irreducible
  simp [separable_def, isCoprime_zero_right, isUnit_iff_degree_eq_zero,
    derivative_X_pow,

中文:
实例 toPerfectRing
  签名: (p : 自然数) [hp : ExpChar K p]
  定义体: by
  refine PerfectRing.ofSurjective _ _ fun y => ?_
  rcases hp with _ | hp
  · simp [frobenius]
  rw [← not_forall_not]
  apply mt (X_pow_sub_C_irreducible_of_prime hp)
  apply mt separable_of_irreducible
  simp [separable_def, isCoprime_zero_right, isUnit_iff_degree_eq_zero,
    derivative_X_pow,

Depends on / 依赖: PerfectRing, PerfectRing.ofSurjective, X_pow_sub_C_irreducible_of_prime, degree_X_pow_sub_C, derivative_X_pow, frobenius, hp.ne_zero, hp.pos, isCoprime_zero_right, isUnit_iff_degree_eq_zero, ne_zero, not_forall_not, ofSurjective, separable_def, separable_of_irreducible
-/
instance toPerfectRing (p : Nat) [hp : ExpChar K p] : PerfectRing K p := by
  refine PerfectRing.ofSurjective _ _ fun y => ?_
  rcases hp with _ | hp
  · simp [frobenius]
  rw [← not_forall_not]
  apply mt (X_pow_sub_C_irreducible_of_prime hp)
  apply mt separable_of_irreducible
  simp [separable_def, isCoprime_zero_right, isUnit_iff_degree_eq_zero,
    derivative_X_pow, degree_X_pow_sub_C hp.pos, hp.ne_zero]

/--
theorem `separable_iff_squarefree` / 定理 `separable_iff_squarefree`

English:
theorem separable_iff_squarefree
  given: {g : K[X]}
  statement: g.Separable ↔ Squarefree g
  proof: by
  refine ⟨Separable.squarefree, fun sqf => isCoprime_of_irreducible_dvd (sqf.ne_zero ·.1) ?_⟩
  rintro p (h : Irreducible p) ⟨q, rfl⟩ (dvd : p ∣ derivative (p * q))
  replace dvd : p ∣ q := by
    rw [derivative_mul]; rw [dvd_add_left (dvd_mul_right p _)] at dvd
    exact (separable_of_irreducibl

中文:
定理 separable_iff_squarefree
  条件: {g : K[X]}
  结论: g.可分 ↔ Squarefree g
  证明: by
  refine ⟨Separable.squarefree, fun sqf => isCoprime_of_irreducible_dvd (sqf.ne_zero ·.1) ?_⟩
  rintro p (h : Irreducible p) ⟨q, rfl⟩ (dvd : p ∣ derivative (p * q))
  replace dvd : p ∣ q := by
    rw [derivative_mul]; rw [dvd_add_left (dvd_mul_right p _)] at dvd
    exact (separable_of_irreducibl

Depends on / 依赖: Irreducible, IsUnit, Separable, Separable.squarefree, derivative, derivative_mul, dvd_add_left, dvd_mul_right, dvd_of_dvd_mul_left, isCoprime_of_irreducible_dvd, mul_dvd_mul_left, ne_zero, replace, separable_of_irreducible, sqf.ne_zero, squarefree
-/
theorem separable_iff_squarefree {g : K[X]} : g.Separable ↔ Squarefree g := by
  refine ⟨Separable.squarefree, fun sqf => isCoprime_of_irreducible_dvd (sqf.ne_zero ·.1) ?_⟩
  rintro p (h : Irreducible p) ⟨q, rfl⟩ (dvd : p ∣ derivative (p * q))
  replace dvd : p ∣ q := by
    rw [derivative_mul]; rw [dvd_add_left (dvd_mul_right p _)] at dvd
    exact (separable_of_irreducible h).dvd_of_dvd_mul_left dvd
  exact (h.1 : ¬ IsUnit p) (sqf _ <| mul_dvd_mul_left _ dvd)

end PerfectField

/--
Instance `Algebra.IsAlgebraic.isSeparable_of_perfectField` / 实例 `Algebra.IsAlgebraic.isSeparable_of_perfectField`

English:
instance Algebra.IsAlgebraic.isSeparable_of_perfectField
  signature: {K L : Type*} [Field K] [Field L]
  body: ⟨fun x => PerfectField.separable_of_irreducible
    minpoly.irreducible (Algebra.IsIntegral.isIntegral x)⟩

中文:
实例 代数.是代数.isSeparable_of_perfectField
  签名: {K L : 类型} [域 K] [域 L]
  定义体: ⟨fun x => PerfectField.separable_of_irreducible
    minpoly.irreducible (Algebra.IsIntegral.isIntegral x)⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, PerfectField, PerfectField.separable_of_irreducible, irreducible, isIntegral, minpoly, minpoly.irreducible, separable_of_irreducible
-/
instance Algebra.IsAlgebraic.isSeparable_of_perfectField {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] [PerfectField K] : Algebra.IsSeparable K L :=
⟨fun x => PerfectField.separable_of_irreducible
    minpoly.irreducible (Algebra.IsIntegral.isIntegral x)⟩

/--
theorem `Algebra.IsAlgebraic.perfectField` / 定理 `Algebra.IsAlgebraic.perfectField`

English:
theorem Algebra.IsAlgebraic.perfectField
  statement: (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
  proof: ⟨fun {f} hf => by
  obtain ⟨_, _, hi, h⟩ := hf.exists_dvd_monic_irreducible_of_isIntegral (K := K)
.of_dvd h⟩ exact (PerfectField.separable_of_irreducible hi).map

中文:
定理 代数.是代数.perfectField
  结论: (K : 类型) {L : 类型} [域 K] [域 L] [代数 K L]
  证明: ⟨fun {f} hf => by
  obtain ⟨_, _, hi, h⟩ := hf.exists_dvd_monic_irreducible_of_isIntegral (K := K)
.of_dvd h⟩ exact (PerfectField.separable_of_irreducible hi).map

Depends on / 依赖: PerfectField, PerfectField.separable_of_irreducible, exists_dvd_monic_irreducible_of_isIntegral, hf.exists_dvd_monic_irreducible_of_isIntegral, of_dvd, separable_of_irreducible
-/
theorem Algebra.IsAlgebraic.perfectField (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [PerfectField K] : PerfectField L := ⟨fun {f} hf => by
  obtain ⟨_, _, hi, h⟩ := hf.exists_dvd_monic_irreducible_of_isIntegral (K := K)
.of_dvd h⟩ exact (PerfectField.separable_of_irreducible hi).map

/--
theorem `PerfectField.of_ringEquiv` / 定理 `PerfectField.of_ringEquiv`

English:
theorem PerfectField.of_ringEquiv
  given: {K L : Type*} [Field K] [Field L] (h : K ≃+* L) [PerfectField K]
  proof: let := h.toRingHom.toAlgebra
  Algebra.IsAlgebraic.perfectField K

中文:
定理 完美域.of_ringEquiv
  条件: {K L : 类型} [域 K] [域 L] (h : K ≃+* L) [完美域 K]
  证明: let := h.toRingHom.toAlgebra
  Algebra.IsAlgebraic.perfectField K

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.perfectField, IsAlgebraic, h.toRingHom.toAlgebra, perfectField, toAlgebra, toRingHom
-/
theorem PerfectField.of_ringEquiv {K L : Type*} [Field K] [Field L] (h : K ≃+* L) [PerfectField K] :
    PerfectField L :=
  let := h.toRingHom.toAlgebra
  Algebra.IsAlgebraic.perfectField K

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] (p n : Nat) [ExpChar R p] (f : R[X])

open Multiset

/--
theorem `roots_expand_pow_map_iterateFrobenius_le` / 定理 `roots_expand_pow_map_iterateFrobenius_le`

English:
theorem roots_expand_pow_map_iterateFrobenius_le
  proof: by
  classical
  refine le_iff_count.2 fun r => ?_
  by_cases h : exists s, r = s ^ p ^ n
  · obtain ⟨s, rfl⟩ := h
    simp_rw [count_nsmul, count_roots, ← rootMultiplicity_expand_pow, ← count_roots, count_map,
      count_eq_card_filter_eq]
    exact card_le_card (monotone_filter_right _ fun _ h =>

中文:
定理 roots_expand_pow_map_iterateFrobenius_le
  证明: by
  classical
  refine le_iff_count.2 fun r => ?_
  by_cases h : exists s, r = s ^ p ^ n
  · obtain ⟨s, rfl⟩ := h
    simp_rw [count_nsmul, count_roots, ← rootMultiplicity_expand_pow, ← count_roots, count_map,
      count_eq_card_filter_eq]
    exact card_le_card (monotone_filter_right _ fun _ h =>

Depends on / 依赖: Nat.zero_le, card_eq_zero, card_le_card, classical, convert, count_eq_card_filter_eq, count_filter_of_neg, count_map, count_nsmul, count_roots, count_zero, iterateFrobenius_inj, le_iff_count, monotone_filter_right, rootMultiplicity_expand_pow, simp_rw, zero_le
-/
theorem roots_expand_pow_map_iterateFrobenius_le :
    (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) <= p ^ n • f.roots := by
  classical
  refine le_iff_count.2 fun r => ?_
  by_cases h : exists s, r = s ^ p ^ n
  · obtain ⟨s, rfl⟩ := h
    simp_rw [count_nsmul, count_roots, ← rootMultiplicity_expand_pow, ← count_roots, count_map,
      count_eq_card_filter_eq]
    exact card_le_card (monotone_filter_right _ fun _ h => iterateFrobenius_inj R p n h)
  convert! Nat.zero_le _
  simp_rw [count_map, card_eq_zero]
  exact ext' fun t => count_zero t ▸ count_filter_of_neg fun h' => h ⟨t, h'⟩

/--
theorem `roots_expand_map_frobenius_le` / 定理 `roots_expand_map_frobenius_le`

English:
theorem roots_expand_map_frobenius_le
  proof: by
  rw [← iterateFrobenius_one]
  convert! ← roots_expand_pow_map_iterateFrobenius_le p 1 f <;> apply pow_one

中文:
定理 roots_expand_map_frobenius_le
  证明: by
  rw [← iterateFrobenius_one]
  convert! ← roots_expand_pow_map_iterateFrobenius_le p 1 f <;> apply pow_one

Depends on / 依赖: convert, iterateFrobenius_one, pow_one, roots_expand_pow_map_iterateFrobenius_le
-/
theorem roots_expand_map_frobenius_le :
    (expand R p f).roots.map (frobenius R p) <= p • f.roots := by
  rw [← iterateFrobenius_one]
  convert! ← roots_expand_pow_map_iterateFrobenius_le p 1 f <;> apply pow_one

/--
theorem `roots_expand_pow_image_iterateFrobenius_subset` / 定理 `roots_expand_pow_image_iterateFrobenius_subset`

English:
theorem roots_expand_pow_image_iterateFrobenius_subset
  given: [DecidableEq R]
  proof: by
  rw [Finset.image_toFinset]; rw [← (roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne']; rw [toFinset_subset]
  exact subset_of_le (roots_expand_pow_map_iterateFrobenius_le p n f)

中文:
定理 roots_expand_pow_image_iterateFrobenius_subset
  条件: [DecidableEq R]
  证明: by
  rw [Finset.image_toFinset]; rw [← (roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne']; rw [toFinset_subset]
  exact subset_of_le (roots_expand_pow_map_iterateFrobenius_le p n f)

Depends on / 依赖: Finset, Finset.image_toFinset, expChar_pow_pos, image_toFinset, roots_expand_pow_map_iterateFrobenius_le, subset_of_le, toFinset_nsmul, toFinset_subset
-/
theorem roots_expand_pow_image_iterateFrobenius_subset [DecidableEq R] :
    (expand R (p ^ n) f).roots.toFinset.image (iterateFrobenius R p n) subseteq f.roots.toFinset := by
  rw [Finset.image_toFinset]; rw [← (roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne']; rw [toFinset_subset]
  exact subset_of_le (roots_expand_pow_map_iterateFrobenius_le p n f)

/--
theorem `roots_expand_image_frobenius_subset` / 定理 `roots_expand_image_frobenius_subset`

English:
theorem roots_expand_image_frobenius_subset
  given: [DecidableEq R]
  proof: by
  rw [← iterateFrobenius_one]
  convert! ← roots_expand_pow_image_iterateFrobenius_subset p 1 f
  apply pow_one

中文:
定理 roots_expand_image_frobenius_subset
  条件: [DecidableEq R]
  证明: by
  rw [← iterateFrobenius_one]
  convert! ← roots_expand_pow_image_iterateFrobenius_subset p 1 f
  apply pow_one

Depends on / 依赖: convert, iterateFrobenius_one, pow_one, roots_expand_pow_image_iterateFrobenius_subset
-/
theorem roots_expand_image_frobenius_subset [DecidableEq R] :
    (expand R p f).roots.toFinset.image (frobenius R p) subseteq f.roots.toFinset := by
  rw [← iterateFrobenius_one]
  convert! ← roots_expand_pow_image_iterateFrobenius_subset p 1 f
  apply pow_one

section PerfectRing
variable {p n f}
variable [PerfectRing R p]

/--
theorem `roots_expand_pow` / 定理 `roots_expand_pow`

English:
theorem roots_expand_pow
  proof: by
  classical
  refine ext' fun r => ?_
  rw [count_roots]; rw [rootMultiplicity_expand_pow]; rw [← count_roots]; rw [count_nsmul]; rw [count_map]; rw [count_eq_card_filter_eq]; congr; ext
  exact (iterateFrobeniusEquiv R p n).eq_symm_apply.symm

中文:
定理 roots_expand_pow
  证明: by
  classical
  refine ext' fun r => ?_
  rw [count_roots]; rw [rootMultiplicity_expand_pow]; rw [← count_roots]; rw [count_nsmul]; rw [count_map]; rw [count_eq_card_filter_eq]; congr; ext
  exact (iterateFrobeniusEquiv R p n).eq_symm_apply.symm

Depends on / 依赖: classical, count_eq_card_filter_eq, count_map, count_nsmul, count_roots, eq_symm_apply, eq_symm_apply.symm, iterateFrobeniusEquiv, rootMultiplicity_expand_pow
-/
theorem roots_expand_pow :
    (expand R (p ^ n) f).roots = p ^ n • f.roots.map (iterateFrobeniusEquiv R p n).symm := by
  classical
  refine ext' fun r => ?_
  rw [count_roots]; rw [rootMultiplicity_expand_pow]; rw [← count_roots]; rw [count_nsmul]; rw [count_map]; rw [count_eq_card_filter_eq]; congr; ext
  exact (iterateFrobeniusEquiv R p n).eq_symm_apply.symm

/--
theorem `roots_expand` / 定理 `roots_expand`

English:
theorem roots_expand
  statement: (expand R p f).roots = p • f.roots.map (frobeniusEquiv R p).symm
  proof: by
  conv_lhs => rw [← pow_one p, roots_expand_pow, iterateFrobeniusEquiv_eq_pow, pow_one]
  rfl

中文:
定理 roots_expand
  结论: (expand R p f).roots = p • f.roots.map (frobeniusEquiv R p).symm
  证明: by
  conv_lhs => rw [← pow_one p, roots_expand_pow, iterateFrobeniusEquiv_eq_pow, pow_one]
  rfl

Depends on / 依赖: conv_lhs, iterateFrobeniusEquiv_eq_pow, pow_one, roots_expand_pow
-/
theorem roots_expand : (expand R p f).roots = p • f.roots.map (frobeniusEquiv R p).symm := by
  conv_lhs => rw [← pow_one p, roots_expand_pow, iterateFrobeniusEquiv_eq_pow, pow_one]
  rfl

/--
theorem `roots_X_pow_char_pow_sub_C` / 定理 `roots_X_pow_char_pow_sub_C`

English:
theorem roots_X_pow_char_pow_sub_C
  given: {y : R}
  proof: by
  have H := roots_expand_pow (p := p) (n := n) (f := X - C y)
  rwa [roots_X_sub_C, Multiset.map_singleton, map_sub, expand_X, expand_C] at H

中文:
定理 roots_X_pow_char_pow_sub_C
  条件: {y : R}
  证明: by
  have H := roots_expand_pow (p := p) (n := n) (f := X - C y)
  rwa [roots_X_sub_C, Multiset.map_singleton, map_sub, expand_X, expand_C] at H

Depends on / 依赖: Multiset, Multiset.map_singleton, expand_C, expand_X, map_singleton, map_sub, roots_X_sub_C, roots_expand_pow
-/
theorem roots_X_pow_char_pow_sub_C {y : R} :
    (X ^ p ^ n - C y).roots = p ^ n • {(iterateFrobeniusEquiv R p n).symm y} := by
  have H := roots_expand_pow (p := p) (n := n) (f := X - C y)
  rwa [roots_X_sub_C, Multiset.map_singleton, map_sub, expand_X, expand_C] at H

/--
theorem `roots_X_pow_char_pow_sub_C_pow` / 定理 `roots_X_pow_char_pow_sub_C_pow`

English:
theorem roots_X_pow_char_pow_sub_C_pow
  given: {y : R} {m : Nat}
  proof: by
  rw [roots_pow]; rw [roots_X_pow_char_pow_sub_C]; rw [mul_smul]

中文:
定理 roots_X_pow_char_pow_sub_C_pow
  条件: {y : R} {m : 自然数}
  证明: by
  rw [roots_pow]; rw [roots_X_pow_char_pow_sub_C]; rw [mul_smul]

Depends on / 依赖: mul_smul, roots_X_pow_char_pow_sub_C, roots_pow
-/
theorem roots_X_pow_char_pow_sub_C_pow {y : R} {m : Nat} :
    ((X ^ p ^ n - C y) ^ m).roots = (m * p ^ n) • {(iterateFrobeniusEquiv R p n).symm y} := by
  rw [roots_pow]; rw [roots_X_pow_char_pow_sub_C]; rw [mul_smul]

/--
theorem `roots_X_pow_char_sub_C` / 定理 `roots_X_pow_char_sub_C`

English:
theorem roots_X_pow_char_sub_C
  given: {y : R}
  proof: by
  have H := roots_X_pow_char_pow_sub_C (p := p) (n := 1) (y := y)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H

中文:
定理 roots_X_pow_char_sub_C
  条件: {y : R}
  证明: by
  have H := roots_X_pow_char_pow_sub_C (p := p) (n := 1) (y := y)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H

Depends on / 依赖: iterateFrobeniusEquiv_one, pow_one, roots_X_pow_char_pow_sub_C
-/
theorem roots_X_pow_char_sub_C {y : R} :
    (X ^ p - C y).roots = p • {(frobeniusEquiv R p).symm y} := by
  have H := roots_X_pow_char_pow_sub_C (p := p) (n := 1) (y := y)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H

/--
theorem `roots_X_pow_char_sub_C_pow` / 定理 `roots_X_pow_char_sub_C_pow`

English:
theorem roots_X_pow_char_sub_C_pow
  given: {y : R} {m : Nat}
  proof: by
  have H := roots_X_pow_char_pow_sub_C_pow (p := p) (n := 1) (y := y) (m := m)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H

中文:
定理 roots_X_pow_char_sub_C_pow
  条件: {y : R} {m : 自然数}
  证明: by
  have H := roots_X_pow_char_pow_sub_C_pow (p := p) (n := 1) (y := y) (m := m)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H

Depends on / 依赖: iterateFrobeniusEquiv_one, pow_one, roots_X_pow_char_pow_sub_C_pow
-/
theorem roots_X_pow_char_sub_C_pow {y : R} {m : Nat} :
    ((X ^ p - C y) ^ m).roots = (m * p) • {(frobeniusEquiv R p).symm y} := by
  have H := roots_X_pow_char_pow_sub_C_pow (p := p) (n := 1) (y := y) (m := m)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H

/--
theorem `roots_expand_pow_map_iterateFrobenius` / 定理 `roots_expand_pow_map_iterateFrobenius`

English:
theorem roots_expand_pow_map_iterateFrobenius
  proof: by
  simp_rw [← coe_iterateFrobeniusEquiv, roots_expand_pow, Multiset.map_nsmul,
    Multiset.map_map, comp_apply, RingEquiv.apply_symm_apply, map_id']

中文:
定理 roots_expand_pow_map_iterateFrobenius
  证明: by
  simp_rw [← coe_iterateFrobeniusEquiv, roots_expand_pow, Multiset.map_nsmul,
    Multiset.map_map, comp_apply, RingEquiv.apply_symm_apply, map_id']

Depends on / 依赖: Multiset, Multiset.map_map, Multiset.map_nsmul, RingEquiv, RingEquiv.apply_symm_apply, apply_symm_apply, coe_iterateFrobeniusEquiv, comp_apply, map_id, map_map, map_nsmul, roots_expand_pow, simp_rw
-/
theorem roots_expand_pow_map_iterateFrobenius :
    (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) = p ^ n • f.roots := by
  simp_rw [← coe_iterateFrobeniusEquiv, roots_expand_pow, Multiset.map_nsmul,
    Multiset.map_map, comp_apply, RingEquiv.apply_symm_apply, map_id']

/--
theorem `roots_expand_map_frobenius` / 定理 `roots_expand_map_frobenius`

English:
theorem roots_expand_map_frobenius
  statement: (expand R p f).roots.map (frobenius R p) = p • f.roots
  proof: by
  simp [roots_expand, Multiset.map_nsmul]

中文:
定理 roots_expand_map_frobenius
  结论: (expand R p f).roots.map (frobenius R p) = p • f.roots
  证明: by
  simp [roots_expand, Multiset.map_nsmul]

Depends on / 依赖: Multiset, Multiset.map_nsmul, map_nsmul, roots_expand
-/
theorem roots_expand_map_frobenius : (expand R p f).roots.map (frobenius R p) = p • f.roots := by
  simp [roots_expand, Multiset.map_nsmul]

/--
theorem `roots_expand_image_iterateFrobenius` / 定理 `roots_expand_image_iterateFrobenius`

English:
theorem roots_expand_image_iterateFrobenius
  given: [DecidableEq R]
  proof: by
  rw [Finset.image_toFinset]; rw [roots_expand_pow_map_iterateFrobenius]; rw [(roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne']

中文:
定理 roots_expand_image_iterateFrobenius
  条件: [DecidableEq R]
  证明: by
  rw [Finset.image_toFinset]; rw [roots_expand_pow_map_iterateFrobenius]; rw [(roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne']

Depends on / 依赖: Finset, Finset.image_toFinset, expChar_pow_pos, image_toFinset, roots_expand_pow_map_iterateFrobenius, toFinset_nsmul
-/
theorem roots_expand_image_iterateFrobenius [DecidableEq R] :
    (expand R (p ^ n) f).roots.toFinset.image (iterateFrobenius R p n) = f.roots.toFinset := by
  rw [Finset.image_toFinset]; rw [roots_expand_pow_map_iterateFrobenius]; rw [(roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne']

/--
theorem `roots_expand_image_frobenius` / 定理 `roots_expand_image_frobenius`

English:
theorem roots_expand_image_frobenius
  given: [DecidableEq R]
  proof: by
  rw [Finset.image_toFinset]; rw [roots_expand_map_frobenius]; rw [(roots f).toFinset_nsmul _ (expChar_pos R p).ne']

中文:
定理 roots_expand_image_frobenius
  条件: [DecidableEq R]
  证明: by
  rw [Finset.image_toFinset]; rw [roots_expand_map_frobenius]; rw [(roots f).toFinset_nsmul _ (expChar_pos R p).ne']

Depends on / 依赖: Finset, Finset.image_toFinset, expChar_pos, image_toFinset, roots_expand_map_frobenius, toFinset_nsmul
-/
theorem roots_expand_image_frobenius [DecidableEq R] :
    (expand R p f).roots.toFinset.image (frobenius R p) = f.roots.toFinset := by
  rw [Finset.image_toFinset]; rw [roots_expand_map_frobenius]; rw [(roots f).toFinset_nsmul _ (expChar_pos R p).ne']

end PerfectRing

variable [DecidableEq R]

/--
Definition of `rootsExpandToRoots` / `rootsExpandToRoots` 的定义

English:
definition rootsExpandToRoots
  signature: : (expand R p f).roots.toFinset ↪ f.roots.toFinset where
  body: ⟨x ^ p, roots_expand_image_frobenius_subset p f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (frobenius_inj R p <| Subtype.ext_iff.1 h)

@[simp]

中文:
定义 rootsExpandToRoots
  签名: : (expand R p f).roots.toFinset ↪ f.roots.toFinset where
  定义体: ⟨x ^ p, roots_expand_image_frobenius_subset p f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (frobenius_inj R p <| Subtype.ext_iff.1 h)

@[simp]

Depends on / 依赖: Finset, Finset.mem_image_of_mem, mem_image_of_mem, roots_expand_image_frobenius_subset
-/
noncomputable def rootsExpandToRoots : (expand R p f).roots.toFinset ↪ f.roots.toFinset where
  toFun x := ⟨x ^ p, roots_expand_image_frobenius_subset p f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (frobenius_inj R p <| Subtype.ext_iff.1 h)

@[simp]
/--
theorem `rootsExpandToRoots_apply` / 定理 `rootsExpandToRoots_apply`

English:
theorem rootsExpandToRoots_apply
  given: (x)
  statement: (rootsExpandToRoots p f x : R) = x ^ p
  proof: rfl

中文:
定理 rootsExpandToRoots_apply
  条件: (x)
  结论: (rootsExpandToRoots p f x : R) = x ^ p
  证明: rfl
-/
theorem rootsExpandToRoots_apply (x) : (rootsExpandToRoots p f x : R) = x ^ p := rfl

/--
Definition of `rootsExpandPowToRoots` / `rootsExpandPowToRoots` 的定义

English:
definition rootsExpandPowToRoots
  signature: :
  body: ⟨x ^ p ^ n,
    roots_expand_pow_image_iterateFrobenius_subset p n f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (iterateFrobenius_inj R p n <| Subtype.ext_iff.1 h)

@[simp]

中文:
定义 rootsExpandPowToRoots
  签名: :
  定义体: ⟨x ^ p ^ n,
    roots_expand_pow_image_iterateFrobenius_subset p n f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (iterateFrobenius_inj R p n <| Subtype.ext_iff.1 h)

@[simp]
-/
noncomputable def rootsExpandPowToRoots :
    (expand R (p ^ n) f).roots.toFinset ↪ f.roots.toFinset where
  toFun x := ⟨x ^ p ^ n,
    roots_expand_pow_image_iterateFrobenius_subset p n f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (iterateFrobenius_inj R p n <| Subtype.ext_iff.1 h)

@[simp]
/--
theorem `rootsExpandPowToRoots_apply` / 定理 `rootsExpandPowToRoots_apply`

English:
theorem rootsExpandPowToRoots_apply
  given: (x)
  statement: (rootsExpandPowToRoots p n f x : R) = x ^ p ^ n
  proof: rfl

中文:
定理 rootsExpandPowToRoots_apply
  条件: (x)
  结论: (rootsExpandPowToRoots p n f x : R) = x ^ p ^ n
  证明: rfl
-/
theorem rootsExpandPowToRoots_apply (x) : (rootsExpandPowToRoots p n f x : R) = x ^ p ^ n := rfl

variable [PerfectRing R p]

/--
Definition of `rootsExpandEquivRoots` / `rootsExpandEquivRoots` 的定义

English:
definition rootsExpandEquivRoots
  signature: : (expand R p f).roots.toFinset ≃ f.roots.toFinset
  body: ((frobeniusEquiv R p).image _).trans .setCongr by
    rw [← roots_expand_image_frobenius (p := p) (f := f)]
    simp

@[simp]

中文:
定义 rootsExpandEquivRoots
  签名: : (expand R p f).roots.toFinset ≃ f.roots.toFinset
  定义体: ((frobeniusEquiv R p).image _).trans .setCongr by
    rw [← roots_expand_image_frobenius (p := p) (f := f)]
    simp

@[simp]

Depends on / 依赖: frobeniusEquiv, roots_expand_image_frobenius, setCongr
-/
noncomputable def rootsExpandEquivRoots : (expand R p f).roots.toFinset ≃ f.roots.toFinset :=
((frobeniusEquiv R p).image _).trans .setCongr by
    rw [← roots_expand_image_frobenius (p := p) (f := f)]
    simp

@[simp]
/--
theorem `rootsExpandEquivRoots_apply` / 定理 `rootsExpandEquivRoots_apply`

English:
theorem rootsExpandEquivRoots_apply
  given: (x)
  statement: (rootsExpandEquivRoots p f x : R) = x ^ p
  proof: rfl

中文:
定理 rootsExpandEquivRoots_apply
  条件: (x)
  结论: (rootsExpandEquivRoots p f x : R) = x ^ p
  证明: rfl
-/
theorem rootsExpandEquivRoots_apply (x) : (rootsExpandEquivRoots p f x : R) = x ^ p := rfl

/--
Definition of `rootsExpandPowEquivRoots` / `rootsExpandPowEquivRoots` 的定义

English:
definition rootsExpandPowEquivRoots
  signature: (n : Nat)
  body: ((iterateFrobeniusEquiv R p n).image _).trans .setCongr by
    rw [← roots_expand_image_iterateFrobenius (p := p) (f := f) (n := n)]
    simp

@[simp]

中文:
定义 rootsExpandPowEquivRoots
  签名: (n : 自然数)
  定义体: ((iterateFrobeniusEquiv R p n).image _).trans .setCongr by
    rw [← roots_expand_image_iterateFrobenius (p := p) (f := f) (n := n)]
    simp

@[simp]

Depends on / 依赖: iterateFrobeniusEquiv, roots_expand_image_iterateFrobenius, setCongr
-/
noncomputable def rootsExpandPowEquivRoots (n : Nat) :
    (expand R (p ^ n) f).roots.toFinset ≃ f.roots.toFinset :=
((iterateFrobeniusEquiv R p n).image _).trans .setCongr by
    rw [← roots_expand_image_iterateFrobenius (p := p) (f := f) (n := n)]
    simp

@[simp]
/--
theorem `rootsExpandPowEquivRoots_apply` / 定理 `rootsExpandPowEquivRoots_apply`

English:
theorem rootsExpandPowEquivRoots_apply
  given: (n : Nat) (x)
  proof: rfl

中文:
定理 rootsExpandPowEquivRoots_apply
  条件: (n : 自然数) (x)
  证明: rfl
-/
theorem rootsExpandPowEquivRoots_apply (n : Nat) (x) :
    (rootsExpandPowEquivRoots p f n x : R) = x ^ p ^ n := rfl

end Polynomial
