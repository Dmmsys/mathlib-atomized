/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! # Results about inverses in Clifford algebras

This contains some basic results about the inversion of vectors, related to the fact that
$ι(m)^{-1} = \frac{ι(m)}{Q(m)}$.
-/

@[expose] public section

variable {R M : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}

namespace CliffordAlgebra

variable (Q)

/-- If the quadratic form of a vector is invertible, then so is that vector. -/
@[instance_reducible]
/--
Definition of `invertibleιOfInvertible` / `invertibleιOfInvertible` 的定义

English:
definition invertibleιOfInvertible
  signature: (m : M) [Invertible (Q m)]
  body: ι Q (⅟(Q m) • m)
  invOf_mul_self := by
    rw [map_smul]; rw [smul_mul_assoc]; rw [ι_sq_scalar]; rw [Algebra.smul_def]; rw [← map_mul]; rw [invOf_mul_self]; rw [map_one]
  mul_invOf_self := by
    rw [map_smul]; rw [mul_smul_comm]; rw [ι_sq_scalar]; rw [Algebra.smul_def]; rw [← map_mul]; rw [invOf_

中文:
定义 invertibleιOfInvertible
  签名: (m : M) [可逆 (Q m)]
  定义体: ι Q (⅟(Q m) • m)
  invOf_mul_self := by
    rw [map_smul]; rw [smul_mul_assoc]; rw [ι_sq_scalar]; rw [Algebra.smul_def]; rw [← map_mul]; rw [invOf_mul_self]; rw [map_one]
  mul_invOf_self := by
    rw [map_smul]; rw [mul_smul_comm]; rw [ι_sq_scalar]; rw [Algebra.smul_def]; rw [← map_mul]; rw [invOf_
-/
def invertibleιOfInvertible (m : M) [Invertible (Q m)] : Invertible (ι Q m) where
  invOf := ι Q (⅟(Q m) • m)
  invOf_mul_self := by
    rw [map_smul]; rw [smul_mul_assoc]; rw [ι_sq_scalar]; rw [Algebra.smul_def]; rw [← map_mul]; rw [invOf_mul_self]; rw [map_one]
  mul_invOf_self := by
    rw [map_smul]; rw [mul_smul_comm]; rw [ι_sq_scalar]; rw [Algebra.smul_def]; rw [← map_mul]; rw [invOf_mul_self]; rw [map_one]

/--
theorem `invOf_ι` / 定理 `invOf_ι`

English:
theorem invOf_ι
  given: (m : M) [Invertible (Q m)] [Invertible (ι Q m)]
  proof: by
  let := invertibleιOfInvertible Q m
  convert! (rfl : ⅟(ι Q m) = _)

中文:
定理 invOf_ι
  条件: (m : M) [可逆 (Q m)] [可逆 (ι Q m)]
  证明: by
  let := invertibleιOfInvertible Q m
  convert! (rfl : ⅟(ι Q m) = _)

Depends on / 依赖: convert
-/
theorem invOf_ι (m : M) [Invertible (Q m)] [Invertible (ι Q m)] :
    ⅟(ι Q m) = ι Q (⅟(Q m) • m) := by
  let := invertibleιOfInvertible Q m
  convert! (rfl : ⅟(ι Q m) = _)

/--
theorem `isUnit_ι_of_isUnit` / 定理 `isUnit_ι_of_isUnit`

English:
theorem isUnit_ι_of_isUnit
  given: {m : M} (h : IsUnit (Q m))
  statement: IsUnit (ι Q m)
  proof: by
  cases h.nonempty_invertible
  let := invertibleιOfInvertible Q m
  exact isUnit_of_invertible (ι Q m)

中文:
定理 isUnit_ι_of_isUnit
  条件: {m : M} (h : 是单位 (Q m))
  结论: 是单位 (ι Q m)
  证明: by
  cases h.nonempty_invertible
  let := invertibleιOfInvertible Q m
  exact isUnit_of_invertible (ι Q m)

Depends on / 依赖: h.nonempty_invertible, isUnit_of_invertible, nonempty_invertible
-/
theorem isUnit_ι_of_isUnit {m : M} (h : IsUnit (Q m)) : IsUnit (ι Q m) := by
  cases h.nonempty_invertible
  let := invertibleιOfInvertible Q m
  exact isUnit_of_invertible (ι Q m)

/--
theorem `ι_mul_ι_mul_invOf_ι` / 定理 `ι_mul_ι_mul_invOf_ι`

English:
theorem ι_mul_ι_mul_invOf_ι
  given: (a b : M) [Invertible (ι Q a)] [Invertible (Q a)]
  proof: by
  rw [invOf_ι]; rw [map_smul]; rw [mul_smul_comm]; rw [ι_mul_ι_mul_ι]; rw [← map_smul]; rw [smul_sub]; rw [smul_smul]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]

中文:
定理 ι_mul_ι_mul_invOf_ι
  条件: (a b : M) [可逆 (ι Q a)] [可逆 (Q a)]
  证明: by
  rw [invOf_ι]; rw [map_smul]; rw [mul_smul_comm]; rw [ι_mul_ι_mul_ι]; rw [← map_smul]; rw [smul_sub]; rw [smul_smul]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]

Depends on / 依赖: invOf_mul_self, map_smul, mul_smul_comm, one_smul, smul_smul, smul_sub
-/
theorem ι_mul_ι_mul_invOf_ι (a b : M) [Invertible (ι Q a)] [Invertible (Q a)] :
    ι Q a * ι Q b * ⅟(ι Q a) = ι Q ((⅟(Q a) * QuadraticMap.polar Q a b) • a - b) := by
  rw [invOf_ι]; rw [map_smul]; rw [mul_smul_comm]; rw [ι_mul_ι_mul_ι]; rw [← map_smul]; rw [smul_sub]; rw [smul_smul]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]

/--
theorem `invOf_ι_mul_ι_mul_ι` / 定理 `invOf_ι_mul_ι_mul_ι`

English:
theorem invOf_ι_mul_ι_mul_ι
  given: (a b : M) [Invertible (ι Q a)] [Invertible (Q a)]
  proof: by
  rw [invOf_ι]; rw [map_smul]; rw [smul_mul_assoc]; rw [smul_mul_assoc]; rw [ι_mul_ι_mul_ι]; rw [← map_smul]; rw [smul_sub]; rw [smul_smul]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]

中文:
定理 invOf_ι_mul_ι_mul_ι
  条件: (a b : M) [可逆 (ι Q a)] [可逆 (Q a)]
  证明: by
  rw [invOf_ι]; rw [map_smul]; rw [smul_mul_assoc]; rw [smul_mul_assoc]; rw [ι_mul_ι_mul_ι]; rw [← map_smul]; rw [smul_sub]; rw [smul_smul]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]

Depends on / 依赖: invOf_mul_self, map_smul, one_smul, smul_mul_assoc, smul_smul, smul_sub
-/
theorem invOf_ι_mul_ι_mul_ι (a b : M) [Invertible (ι Q a)] [Invertible (Q a)] :
    ⅟(ι Q a) * ι Q b * ι Q a = ι Q ((⅟(Q a) * QuadraticMap.polar Q a b) • a - b) := by
  rw [invOf_ι]; rw [map_smul]; rw [smul_mul_assoc]; rw [smul_mul_assoc]; rw [ι_mul_ι_mul_ι]; rw [← map_smul]; rw [smul_sub]; rw [smul_smul]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]

section
variable [Invertible (2 : R)]

/-- Over a ring where `2` is invertible, `Q m` is invertible whenever `ι Q m`. -/
@[instance_reducible]
/--
Definition of `invertibleOfInvertibleι` / `invertibleOfInvertibleι` 的定义

English:
definition invertibleOfInvertibleι
  signature: (m : M) [Invertible (ι Q m)]
  body: ExteriorAlgebra.invertibleAlgebraMapEquiv M (Q m)
.algebraMapOfInvertibleAlgebraMap (equivExterior Q).toLinearMap (by simp)
      .copy (.mul ‹Invertible (ι Q m)› ‹Invertible (ι Q m)›) _ (ι_sq_scalar _ _).symm

中文:
定义 invertibleOfInvertibleι
  签名: (m : M) [可逆 (ι Q m)]
  定义体: ExteriorAlgebra.invertibleAlgebraMapEquiv M (Q m)
.algebraMapOfInvertibleAlgebraMap (equivExterior Q).toLinearMap (by simp)
      .copy (.mul ‹Invertible (ι Q m)› ‹Invertible (ι Q m)›) _ (ι_sq_scalar _ _).symm

Depends on / 依赖: ExteriorAlgebra, ExteriorAlgebra.invertibleAlgebraMapEquiv, Invertible, algebraMapOfInvertibleAlgebraMap, equivExterior, invertibleAlgebraMapEquiv, toLinearMap
-/
def invertibleOfInvertibleι (m : M) [Invertible (ι Q m)] : Invertible (Q m) :=
ExteriorAlgebra.invertibleAlgebraMapEquiv M (Q m)
.algebraMapOfInvertibleAlgebraMap (equivExterior Q).toLinearMap (by simp)
      .copy (.mul ‹Invertible (ι Q m)› ‹Invertible (ι Q m)›) _ (ι_sq_scalar _ _).symm

/--
theorem `isUnit_of_isUnit_ι` / 定理 `isUnit_of_isUnit_ι`

English:
theorem isUnit_of_isUnit_ι
  given: {m : M} (h : IsUnit (ι Q m))
  statement: IsUnit (Q m)
  proof: by
  cases h.nonempty_invertible
  let := invertibleOfInvertibleι Q m
  exact isUnit_of_invertible (Q m)

中文:
定理 isUnit_of_isUnit_ι
  条件: {m : M} (h : 是单位 (ι Q m))
  结论: 是单位 (Q m)
  证明: by
  cases h.nonempty_invertible
  let := invertibleOfInvertibleι Q m
  exact isUnit_of_invertible (Q m)

Depends on / 依赖: h.nonempty_invertible, isUnit_of_invertible, nonempty_invertible
-/
theorem isUnit_of_isUnit_ι {m : M} (h : IsUnit (ι Q m)) : IsUnit (Q m) := by
  cases h.nonempty_invertible
  let := invertibleOfInvertibleι Q m
  exact isUnit_of_invertible (Q m)

/--
theorem `isUnit_ι_iff` / 定理 `isUnit_ι_iff`

English:
theorem isUnit_ι_iff
  given: {m : M}
  statement: IsUnit (ι Q m) ↔ IsUnit (Q m)
  proof: ⟨isUnit_of_isUnit_ι Q, isUnit_ι_of_isUnit Q⟩

中文:
定理 isUnit_ι_iff
  条件: {m : M}
  结论: 是单位 (ι Q m) ↔ 是单位 (Q m)
  证明: ⟨isUnit_of_isUnit_ι Q, isUnit_ι_of_isUnit Q⟩
-/
@[simp] theorem isUnit_ι_iff {m : M} : IsUnit (ι Q m) ↔ IsUnit (Q m) :=
  ⟨isUnit_of_isUnit_ι Q, isUnit_ι_of_isUnit Q⟩

end

end CliffordAlgebra
