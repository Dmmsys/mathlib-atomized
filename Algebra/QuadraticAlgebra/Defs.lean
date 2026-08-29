/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Kenny Lau, Jiayang Hong
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic


/-!

# Quadratic Algebra

In this file we define the quadratic algebra `QuadraticAlgebra R a b` over a commutative ring `R`,
and define some algebraic structures on it.

## Main definitions

* `QuadraticAlgebra R a b`:
  [Bourbaki, *Algebra I*][bourbaki1989] with coefficients `a`, `b` in `R`.

## Tags

Quadratic algebra, quadratic extension

-/

@[expose] public section

universe u

/-- Quadratic algebra over a type with fixed coefficient where $i^2 = a + bi$, implemented as
a structure with two fields, `re` and `im`. When `R` is a commutative ring, this is isomorphic to
`R[X]/(X^2-b*X-a)`. -/
@[ext]
/--
Definition of `QuadraticAlgebra` / `QuadraticAlgebra` 的定义

English:
structure QuadraticAlgebra
  parameters: (R : Type u) (a b : R)
  axioms and operations (2):
    - re : R
    - im : R

中文:
结构 QuadraticAlgebra
  参数: (R : 类型u) (a b : R)
  公理与运算 (2 个):
    - re : R
    - im : R
-/
structure QuadraticAlgebra (R : Type u) (a b : R) : Type u where
  /-- Real part of an element in quadratic algebra -/
  re : R
  /-- Imaginary part of an element in quadratic algebra -/
  im : R
deriving DecidableEq

initialize_simps_projections QuadraticAlgebra (as_prefix re, as_prefix im)

variable {R : Type*}
namespace QuadraticAlgebra

/-- The equivalence between quadratic algebra over `R` and `R × R`. -/
@[simps symm_apply]
/--
Definition of `equivProd` / `equivProd` 的定义

English:
definition equivProd
  signature: (a b : R)
  body: (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩

@[simp]

中文:
定义 equivProd
  签名: (a b : R)
  定义体: (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩

@[simp]

Depends on / 依赖: z.im, z.re
-/
def equivProd (a b : R) : QuadraticAlgebra R a b ≃ R × R where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩

@[simp]
/--
theorem `mk_eta` / 定理 `mk_eta`

English:
theorem mk_eta
  given: {a b} (z : QuadraticAlgebra R a b)
  proof: rfl

中文:
定理 mk_eta
  条件: {a b} (z : QuadraticAlgebra R a b)
  证明: rfl
-/
theorem mk_eta {a b} (z : QuadraticAlgebra R a b) :
    mk z.re z.im = z := rfl

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: R] : Subsingleton (QuadraticAlgebra R a b)
  body: (equivProd a b).subsingleton

中文:
实例 [Subsingleton
  签名: R] : Subsingleton (QuadraticAlgebra R a b)
  定义体: (equivProd a b).subsingleton

Depends on / 依赖: equivProd, subsingleton
-/
instance [Subsingleton R] : Subsingleton (QuadraticAlgebra R a b) := (equivProd a b).subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (QuadraticAlgebra R a b)
  body: (equivProd a b).nontrivial

中文:
实例 [Nontrivial
  签名: R] : Nontrivial (QuadraticAlgebra R a b)
  定义体: (equivProd a b).nontrivial

Depends on / 依赖: equivProd, nontrivial
-/
instance [Nontrivial R] : Nontrivial (QuadraticAlgebra R a b) := (equivProd a b).nontrivial

section Zero
variable [Zero R]

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: (x : R)
  body: ⟨x, 0⟩

@[simp]

中文:
定义 C
  签名: (x : R)
  定义体: ⟨x, 0⟩

@[simp]
-/
protected def C (x : R) : QuadraticAlgebra R a b := ⟨x, 0⟩

@[simp]
/--
theorem `re_C` / 定理 `re_C`

English:
theorem re_C
  statement: (.C r : QuadraticAlgebra R a b).re = r
  proof: rfl

@[simp]

中文:
定理 re_C
  结论: (.C r : QuadraticAlgebra R a b).re = r
  证明: rfl

@[simp]
-/
theorem re_C : (.C r : QuadraticAlgebra R a b).re = r := rfl

@[simp]
/--
theorem `im_C` / 定理 `im_C`

English:
theorem im_C
  statement: (.C r : QuadraticAlgebra R a b).im = 0
  proof: rfl

中文:
定理 im_C
  结论: (.C r : QuadraticAlgebra R a b).im = 0
  证明: rfl
-/
theorem im_C : (.C r : QuadraticAlgebra R a b).im = 0 := rfl

/--
theorem `C_injective` / 定理 `C_injective`

English:
theorem C_injective
  statement: Function.Injective (.C : R -> QuadraticAlgebra R a b)
  proof: fun _ _ h => congr_arg re h

@[simp]

中文:
定理 C_injective
  结论: Function.Injective (.C : R -> QuadraticAlgebra R a b)
  证明: fun _ _ h => congr_arg re h

@[simp]

Depends on / 依赖: congr_arg
-/
theorem C_injective : Function.Injective (.C : R -> QuadraticAlgebra R a b) :=
  fun _ _ h => congr_arg re h

@[simp]
/--
theorem `C_inj` / 定理 `C_inj`

English:
theorem C_inj
  given: {x y : R}
  statement: (.C x : QuadraticAlgebra R a b) = .C y ↔ x = y
  proof: C_injective.eq_iff

中文:
定理 C_inj
  条件: {x y : R}
  结论: (.C x : QuadraticAlgebra R a b) = .C y ↔ x = y
  证明: C_injective.eq_iff

Depends on / 依赖: C_injective, C_injective.eq_iff, eq_iff
-/
theorem C_inj {x y : R} : (.C x : QuadraticAlgebra R a b) = .C y ↔ x = y :=
  C_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (QuadraticAlgebra R a b)
  body: ⟨⟨0, 0⟩⟩

中文:
实例 :
  签名: Zero (QuadraticAlgebra R a b)
  定义体: ⟨⟨0, 0⟩⟩
-/
instance : Zero (QuadraticAlgebra R a b) := ⟨⟨0, 0⟩⟩

/--
theorem `re_zero` / 定理 `re_zero`

English:
theorem re_zero
  statement: (0 : QuadraticAlgebra R a b).re = 0
  proof: rfl

中文:
定理 re_zero
  结论: (0 : QuadraticAlgebra R a b).re = 0
  证明: rfl
-/
@[simp] theorem re_zero : (0 : QuadraticAlgebra R a b).re = 0 := rfl

/--
theorem `im_zero` / 定理 `im_zero`

English:
theorem im_zero
  statement: (0 : QuadraticAlgebra R a b).im = 0
  proof: rfl

@[simp]

中文:
定理 im_zero
  结论: (0 : QuadraticAlgebra R a b).im = 0
  证明: rfl

@[simp]
-/
@[simp] theorem im_zero : (0 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp]
/--
theorem `C_zero` / 定理 `C_zero`

English:
theorem C_zero
  statement: (.C 0 : QuadraticAlgebra R a b) = 0
  proof: rfl

@[simp]

中文:
定理 C_zero
  结论: (.C 0 : QuadraticAlgebra R a b) = 0
  证明: rfl

@[simp]
-/
theorem C_zero : (.C 0 : QuadraticAlgebra R a b) = 0 := rfl

@[simp]
/--
theorem `C_eq_zero_iff` / 定理 `C_eq_zero_iff`

English:
theorem C_eq_zero_iff
  given: {r : R}
  statement: (.C r : QuadraticAlgebra R a b) = 0 ↔ r = 0
  proof: by
  rw [← C_zero]; rw [C_inj]

中文:
定理 C_eq_zero_iff
  条件: {r : R}
  结论: (.C r : QuadraticAlgebra R a b) = 0 ↔ r = 0
  证明: by
  rw [← C_zero]; rw [C_inj]

Depends on / 依赖: C_inj, C_zero
-/
theorem C_eq_zero_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 0 ↔ r = 0 := by
  rw [← C_zero]; rw [C_inj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (QuadraticAlgebra R a b)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (QuadraticAlgebra R a b)
  定义体: ⟨0⟩
-/
instance : Inhabited (QuadraticAlgebra R a b) := ⟨0⟩

section One
variable [One R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (QuadraticAlgebra R a b)
  body: ⟨⟨1, 0⟩⟩

中文:
实例 :
  签名: One (QuadraticAlgebra R a b)
  定义体: ⟨⟨1, 0⟩⟩
-/
instance : One (QuadraticAlgebra R a b) := ⟨⟨1, 0⟩⟩

/--
theorem `re_one` / 定理 `re_one`

English:
theorem re_one
  statement: (1 : QuadraticAlgebra R a b).re = 1
  proof: rfl

中文:
定理 re_one
  结论: (1 : QuadraticAlgebra R a b).re = 1
  证明: rfl
-/
@[scoped simp] theorem re_one : (1 : QuadraticAlgebra R a b).re = 1 := rfl

/--
theorem `im_one` / 定理 `im_one`

English:
theorem im_one
  statement: (1 : QuadraticAlgebra R a b).im = 0
  proof: rfl

@[simp]

中文:
定理 im_one
  结论: (1 : QuadraticAlgebra R a b).im = 0
  证明: rfl

@[simp]
-/
@[scoped simp] theorem im_one : (1 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp]
/--
theorem `C_one` / 定理 `C_one`

English:
theorem C_one
  statement: (.C 1 : QuadraticAlgebra R a b) = 1
  proof: rfl

@[simp]

中文:
定理 C_one
  结论: (.C 1 : QuadraticAlgebra R a b) = 1
  证明: rfl

@[simp]
-/
theorem C_one : (.C 1 : QuadraticAlgebra R a b) = 1 := rfl

@[simp]
/--
theorem `C_eq_one_iff` / 定理 `C_eq_one_iff`

English:
theorem C_eq_one_iff
  given: {r : R}
  statement: (.C r : QuadraticAlgebra R a b) = 1 ↔ r = 1
  proof: by
  rw [← C_one]; rw [C_inj]

中文:
定理 C_eq_one_iff
  条件: {r : R}
  结论: (.C r : QuadraticAlgebra R a b) = 1 ↔ r = 1
  证明: by
  rw [← C_one]; rw [C_inj]

Depends on / 依赖: C_inj, C_one
-/
theorem C_eq_one_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 1 ↔ r = 1 := by
  rw [← C_one]; rw [C_inj]

end One

end Zero

section Add
variable [Add R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (QuadraticAlgebra R a b)
  body: ⟨z.re + w.re, z.im + w.im⟩

中文:
实例 :
  签名: Add (QuadraticAlgebra R a b)
  定义体: ⟨z.re + w.re, z.im + w.im⟩

Depends on / 依赖: w.im, w.re, z.im, z.re
-/
instance : Add (QuadraticAlgebra R a b) where
  add z w := ⟨z.re + w.re, z.im + w.im⟩

/--
theorem `re_add` / 定理 `re_add`

English:
theorem re_add
  given: (z w : QuadraticAlgebra R a b)
  proof: rfl

中文:
定理 re_add
  条件: (z w : QuadraticAlgebra R a b)
  证明: rfl
-/
@[simp] theorem re_add (z w : QuadraticAlgebra R a b) :
    (z + w).re = z.re + w.re := rfl

/--
theorem `im_add` / 定理 `im_add`

English:
theorem im_add
  given: (z w : QuadraticAlgebra R a b)
  proof: rfl

@[simp]

中文:
定理 im_add
  条件: (z w : QuadraticAlgebra R a b)
  证明: rfl

@[simp]
-/
@[simp] theorem im_add (z w : QuadraticAlgebra R a b) :
    (z + w).im = z.im + w.im := rfl

@[simp]
/--
theorem `mk_add_mk` / 定理 `mk_add_mk`

English:
theorem mk_add_mk
  given: (z w : QuadraticAlgebra R a b)
  proof: rfl

中文:
定理 mk_add_mk
  条件: (z w : QuadraticAlgebra R a b)
  证明: rfl
-/
theorem mk_add_mk (z w : QuadraticAlgebra R a b) :
    mk z.re z.im + mk w.re w.im = (mk (z.re + w.re) (z.im + w.im) : QuadraticAlgebra R a b) := rfl

end Add

section AddZeroClass
variable [AddZeroClass R]

@[simp]
/--
theorem `C_add` / 定理 `C_add`

English:
theorem C_add
  given: (x y : R)
  statement: (.C (x + y) : QuadraticAlgebra R a b) = .C x + .C y
  proof: by
  ext <;> simp

中文:
定理 C_add
  条件: (x y : R)
  结论: (.C (x + y) : QuadraticAlgebra R a b) = .C x + .C y
  证明: by
  ext <;> simp
-/
theorem C_add (x y : R) : (.C (x + y) : QuadraticAlgebra R a b) = .C x + .C y := by
  ext <;> simp

end AddZeroClass

section Neg
variable [Neg R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (QuadraticAlgebra R a b)
  body: ⟨-z.re, -z.im⟩

中文:
实例 :
  签名: Neg (QuadraticAlgebra R a b)
  定义体: ⟨-z.re, -z.im⟩

Depends on / 依赖: z.im, z.re
-/
instance : Neg (QuadraticAlgebra R a b) where neg z := ⟨-z.re, -z.im⟩

/--
theorem `re_neg` / 定理 `re_neg`

English:
theorem re_neg
  given: (z : QuadraticAlgebra R a b)
  statement: (-z).re = -z.re
  proof: rfl

中文:
定理 re_neg
  条件: (z : QuadraticAlgebra R a b)
  结论: (-z).re = -z.re
  证明: rfl
-/
@[simp] theorem re_neg (z : QuadraticAlgebra R a b) : (-z).re = -z.re := rfl

/--
theorem `im_neg` / 定理 `im_neg`

English:
theorem im_neg
  given: (z : QuadraticAlgebra R a b)
  statement: (-z).im = -z.im
  proof: rfl

@[simp]

中文:
定理 im_neg
  条件: (z : QuadraticAlgebra R a b)
  结论: (-z).im = -z.im
  证明: rfl

@[simp]
-/
@[simp] theorem im_neg (z : QuadraticAlgebra R a b) : (-z).im = -z.im := rfl

@[simp]
/--
theorem `neg_mk` / 定理 `neg_mk`

English:
theorem neg_mk
  given: (x y : R)
  proof: rfl

中文:
定理 neg_mk
  条件: (x y : R)
  证明: rfl
-/
theorem neg_mk (x y : R) :
    -(mk x y : QuadraticAlgebra R a b) = ⟨-x, -y⟩ := rfl

end Neg

section AddGroup

@[simp]
/--
theorem `C_neg` / 定理 `C_neg`

English:
theorem C_neg
  given: [NegZeroClass R] (x : R)
  statement: (.C (-x) : QuadraticAlgebra R a b) = -.C x
  proof: by
  ext <;> simp

中文:
定理 C_neg
  条件: [NegZeroClass R] (x : R)
  结论: (.C (-x) : QuadraticAlgebra R a b) = -.C x
  证明: by
  ext <;> simp
-/
theorem C_neg [NegZeroClass R] (x : R) : (.C (-x) : QuadraticAlgebra R a b) = -.C x := by
  ext <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Sub
  signature: R] : Sub (QuadraticAlgebra R a b) where
  body: ⟨z.re - w.re, z.im - w.im⟩

中文:
实例 [Sub
  签名: R] : Sub (QuadraticAlgebra R a b) where
  定义体: ⟨z.re - w.re, z.im - w.im⟩

Depends on / 依赖: w.im, w.re, z.im, z.re
-/
instance [Sub R] : Sub (QuadraticAlgebra R a b) where
  sub z w := ⟨z.re - w.re, z.im - w.im⟩

/--
theorem `re_sub` / 定理 `re_sub`

English:
theorem re_sub
  given: [Sub R] (z w : QuadraticAlgebra R a b)
  proof: rfl

中文:
定理 re_sub
  条件: [Sub R] (z w : QuadraticAlgebra R a b)
  证明: rfl
-/
@[simp] theorem re_sub [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).re = z.re - w.re := rfl

/--
theorem `im_sub` / 定理 `im_sub`

English:
theorem im_sub
  given: [Sub R] (z w : QuadraticAlgebra R a b)
  proof: rfl

@[simp]

中文:
定理 im_sub
  条件: [Sub R] (z w : QuadraticAlgebra R a b)
  证明: rfl

@[simp]
-/
@[simp] theorem im_sub [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).im = z.im - w.im := rfl

@[simp]
/--
theorem `mk_sub_mk` / 定理 `mk_sub_mk`

English:
theorem mk_sub_mk
  given: [Sub R] (x1 y1 x2 y2 : R)
  proof: rfl

@[simp]

中文:
定理 mk_sub_mk
  条件: [Sub R] (x1 y1 x2 y2 : R)
  证明: rfl

@[simp]
-/
theorem mk_sub_mk [Sub R] (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) - mk x2 y2 = mk (x1 - x2) (y1 - y2) := rfl

@[simp]
/--
theorem `C_sub` / 定理 `C_sub`

English:
theorem C_sub
  given: (r1 r2 : R) [SubNegZeroMonoid R]
  proof: QuadraticAlgebra.ext rfl zero_sub_zero.symm

中文:
定理 C_sub
  条件: (r1 r2 : R) [SubNegZeroMonoid R]
  证明: QuadraticAlgebra.ext rfl zero_sub_zero.symm

Depends on / 依赖: QuadraticAlgebra, QuadraticAlgebra.ext, zero_sub_zero, zero_sub_zero.symm
-/
theorem C_sub (r1 r2 : R) [SubNegZeroMonoid R] :
    (.C (r1 - r2) : QuadraticAlgebra R a b) = .C r1 - .C r2 :=
  QuadraticAlgebra.ext rfl zero_sub_zero.symm

end AddGroup

section Mul
variable [Mul R] [Add R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (QuadraticAlgebra R a b)
  body: ⟨z.1 * w.1 + a * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + b * z.2 * w.2⟩

中文:
实例 :
  签名: Mul (QuadraticAlgebra R a b)
  定义体: ⟨z.1 * w.1 + a * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + b * z.2 * w.2⟩
-/
instance : Mul (QuadraticAlgebra R a b) where
  mul z w := ⟨z.1 * w.1 + a * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + b * z.2 * w.2⟩

/--
theorem `re_mul` / 定理 `re_mul`

English:
theorem re_mul
  given: (z w : QuadraticAlgebra R a b)
  proof: rfl

中文:
定理 re_mul
  条件: (z w : QuadraticAlgebra R a b)
  证明: rfl
-/
@[simp] theorem re_mul (z w : QuadraticAlgebra R a b) :
    (z * w).re = z.re * w.re + a * z.im * w.im := rfl

/--
theorem `im_mul` / 定理 `im_mul`

English:
theorem im_mul
  given: (z w : QuadraticAlgebra R a b)
  proof: rfl

@[simp]

中文:
定理 im_mul
  条件: (z w : QuadraticAlgebra R a b)
  证明: rfl

@[simp]
-/
@[simp] theorem im_mul (z w : QuadraticAlgebra R a b) :
    (z * w).im = z.re * w.im + z.im * w.re + b * z.im * w.im := rfl

@[simp]
/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: (x1 y1 x2 y2 : R)
  proof: rfl

中文:
定理 mk_mul_mk
  条件: (x1 y1 x2 y2 : R)
  证明: rfl
-/
theorem mk_mul_mk (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) * mk x2 y2 =
    mk (x1 * x2 + a * y1 * y2) (x1 * y2 + y1 * x2 + b * y1 * y2) := rfl

end Mul

section SMul
variable [SMul S R] [SMul T R] (s : S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S (QuadraticAlgebra R a b)
  body: ⟨s • z.re, s • z.im⟩

中文:
实例 :
  签名: SMul S (QuadraticAlgebra R a b)
  定义体: ⟨s • z.re, s • z.im⟩

Depends on / 依赖: z.im, z.re
-/
instance : SMul S (QuadraticAlgebra R a b) where smul s z := ⟨s • z.re, s • z.im⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticAlgebra R a b) where
  body: by ext <;> exact smul_assoc _ _ _

中文:
实例 [SMul
  签名: S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticAlgebra R a b) where
  定义体: by ext <;> exact smul_assoc _ _ _

Depends on / 依赖: smul_assoc
-/
instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticAlgebra R a b) where
  smul_assoc s t z := by ext <;> exact smul_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: S T R] : SMulCommClass S T (QuadraticAlgebra R a b) where
  body: by ext <;> exact smul_comm _ _ _

中文:
实例 [SMulCommClass
  签名: S T R] : SMulCommClass S T (QuadraticAlgebra R a b) where
  定义体: by ext <;> exact smul_comm _ _ _

Depends on / 依赖: smul_comm
-/
instance [SMulCommClass S T R] : SMulCommClass S T (QuadraticAlgebra R a b) where
  smul_comm s t z := by ext <;> exact smul_comm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: Sᵐᵒᵖ R] [IsCentralScalar S R] : IsCentralScalar S (QuadraticAlgebra R a b) where
  body: by ext <;> exact op_smul_eq_smul _ _

中文:
实例 [SMul
  签名: Sᵐᵒᵖ R] [IsCentralScalar S R] : IsCentralScalar S (QuadraticAlgebra R a b) where
  定义体: by ext <;> exact op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance [SMul Sᵐᵒᵖ R] [IsCentralScalar S R] : IsCentralScalar S (QuadraticAlgebra R a b) where
  op_smul_eq_smul s z := by ext <;> exact op_smul_eq_smul _ _

/--
theorem `re_smul` / 定理 `re_smul`

English:
theorem re_smul
  given: (s : S) (z : QuadraticAlgebra R a b)
  statement: (s • z).re = s • z.re
  proof: rfl

中文:
定理 re_smul
  条件: (s : S) (z : QuadraticAlgebra R a b)
  结论: (s • z).re = s • z.re
  证明: rfl
-/
@[simp] theorem re_smul (s : S) (z : QuadraticAlgebra R a b) : (s • z).re = s • z.re := rfl

/--
theorem `im_smul` / 定理 `im_smul`

English:
theorem im_smul
  given: (s : S) (z : QuadraticAlgebra R a b)
  statement: (s • z).im = s • z.im
  proof: rfl

@[simp]

中文:
定理 im_smul
  条件: (s : S) (z : QuadraticAlgebra R a b)
  结论: (s • z).im = s • z.im
  证明: rfl

@[simp]
-/
@[simp] theorem im_smul (s : S) (z : QuadraticAlgebra R a b) : (s • z).im = s • z.im := rfl

@[simp]
/--
theorem `smul_mk` / 定理 `smul_mk`

English:
theorem smul_mk
  given: (s : S) (x y : R)
  proof: rfl

中文:
定理 smul_mk
  条件: (s : S) (x y : R)
  证明: rfl
-/
theorem smul_mk (s : S) (x y : R) :
    s • (mk x y : QuadraticAlgebra R a b) = mk (s • x) (s • y) := rfl

end SMul

section MulAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [MulAction S R] : MulAction S (QuadraticAlgebra R a b) where
  body: by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp [mul_smul]

中文:
实例 [Monoid
  签名: S] [MulAction S R] : MulAction S (QuadraticAlgebra R a b) where
  定义体: by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp [mul_smul]

Depends on / 依赖: mul_smul
-/
instance [Monoid S] [MulAction S R] : MulAction S (QuadraticAlgebra R a b) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp [mul_smul]

end MulAction

@[simp]
/--
theorem `C_smul` / 定理 `C_smul`

English:
theorem C_smul
  given: [Zero R] [SMulZeroClass S R] (s : S) (r : R)
  proof: QuadraticAlgebra.ext rfl (smul_zero _).symm

中文:
定理 C_smul
  条件: [Zero R] [SMulZeroClass S R] (s : S) (r : R)
  证明: QuadraticAlgebra.ext rfl (smul_zero _).symm

Depends on / 依赖: QuadraticAlgebra, QuadraticAlgebra.ext, smul_zero
-/
theorem C_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (.C (s • r) : QuadraticAlgebra R a b) = s • .C r :=
  QuadraticAlgebra.ext rfl (smul_zero _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: R] : AddMonoid (QuadraticAlgebra R a b)
  body: fast_instance% by
  refine (equivProd a b).injective.addMonoid _ rfl ?_ ?_ <;> intros <;> rfl

中文:
实例 [AddMonoid
  签名: R] : AddMonoid (QuadraticAlgebra R a b)
  定义体: fast_instance% by
  refine (equivProd a b).injective.addMonoid _ rfl ?_ ?_ <;> intros <;> rfl

Depends on / 依赖: addMonoid, equivProd, fast_instance, injective, injective.addMonoid, intros
-/
instance [AddMonoid R] : AddMonoid (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addMonoid _ rfl ?_ ?_ <;> intros <;> rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [AddMonoid R] [DistribMulAction S R] :
  body: by ext <;> simp
  smul_add _ _ _ := by ext <;> simp

中文:
实例 [Monoid
  签名: S] [AddMonoid R] [DistribMulAction S R] :
  定义体: by ext <;> simp
  smul_add _ _ _ := by ext <;> simp

Depends on / 依赖: smul_add
-/
instance [Monoid S] [AddMonoid R] [DistribMulAction S R] :
    DistribMulAction S (QuadraticAlgebra R a b) where
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: R] : AddCommMonoid (QuadraticAlgebra R a b)
  body: fast_instance% by
  refine (equivProd a b).injective.addCommMonoid _ rfl ?_ ?_ <;> intros <;> rfl

中文:
实例 [AddCommMonoid
  签名: R] : AddCommMonoid (QuadraticAlgebra R a b)
  定义体: fast_instance% by
  refine (equivProd a b).injective.addCommMonoid _ rfl ?_ ?_ <;> intros <;> rfl

Depends on / 依赖: addCommMonoid, equivProd, fast_instance, injective, injective.addCommMonoid, intros
-/
instance [AddCommMonoid R] : AddCommMonoid (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addCommMonoid _ rfl ?_ ?_ <;> intros <;> rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [AddCommMonoid R] [Module S R] : Module S (QuadraticAlgebra R a b) where
  body: by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

中文:
实例 [Semiring
  签名: S] [AddCommMonoid R] [Module S R] : Module S (QuadraticAlgebra R a b) where
  定义体: by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

Depends on / 依赖: add_smul, zero_smul
-/
instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S (QuadraticAlgebra R a b) where
  add_smul r s x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: R] : AddGroup (QuadraticAlgebra R a b)
  body: fast_instance% by
  refine (equivProd a b).injective.addGroup _ rfl ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

中文:
实例 [AddGroup
  签名: R] : AddGroup (QuadraticAlgebra R a b)
  定义体: fast_instance% by
  refine (equivProd a b).injective.addGroup _ rfl ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

Depends on / 依赖: addGroup, equivProd, fast_instance, injective, injective.addGroup, intros
-/
instance [AddGroup R] : AddGroup (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addGroup _ rfl ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: R] : AddCommGroup (QuadraticAlgebra R a b) where

中文:
实例 [AddCommGroup
  签名: R] : AddCommGroup (QuadraticAlgebra R a b) where
-/
instance [AddCommGroup R] : AddCommGroup (QuadraticAlgebra R a b) where

section AddCommMonoidWithOne
variable [AddCommMonoidWithOne R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoidWithOne (QuadraticAlgebra R a b)
  body: .C n
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp

@[simp]

中文:
实例 :
  签名: AddCommMonoidWithOne (QuadraticAlgebra R a b)
  定义体: .C n
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp

@[simp]
-/
instance : AddCommMonoidWithOne (QuadraticAlgebra R a b) where
  natCast n := .C n
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp

@[simp]
/--
theorem `C_ofNat` / 定理 `C_ofNat`

English:
theorem C_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: by
  ext <;> rfl

@[simp, norm_cast]

中文:
定理 C_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: by
  ext <;> rfl

@[simp, norm_cast]
-/
theorem C_ofNat (n : Nat) [n.AtLeastTwo] :
    (.C (ofNat(n) : R) : QuadraticAlgebra R a b) = ofNat(n) := by
  ext <;> rfl

@[simp, norm_cast]
/--
theorem `re_natCast` / 定理 `re_natCast`

English:
theorem re_natCast
  given: (n : Nat)
  statement: (n : QuadraticAlgebra R a b).re = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_natCast
  条件: (n : 自然数)
  结论: (n : QuadraticAlgebra R a b).re = n
  证明: rfl

@[simp, norm_cast]
-/
theorem re_natCast (n : Nat) : (n : QuadraticAlgebra R a b).re = n := rfl

@[simp, norm_cast]
/--
theorem `im_natCast` / 定理 `im_natCast`

English:
theorem im_natCast
  given: (n : Nat)
  statement: (n : QuadraticAlgebra R a b).im = 0
  proof: rfl

中文:
定理 im_natCast
  条件: (n : 自然数)
  结论: (n : QuadraticAlgebra R a b).im = 0
  证明: rfl
-/
theorem im_natCast (n : Nat) : (n : QuadraticAlgebra R a b).im = 0 := rfl

/--
theorem `C_natCast` / 定理 `C_natCast`

English:
theorem C_natCast
  given: (n : Nat)
  statement: .C (n : R) = (↑n : QuadraticAlgebra R a b)
  proof: rfl

@[scoped simp]

中文:
定理 C_natCast
  条件: (n : 自然数)
  结论: .C (n : R) = (↑n : QuadraticAlgebra R a b)
  证明: rfl

@[scoped simp]
-/
theorem C_natCast (n : Nat) : .C (n : R) = (↑n : QuadraticAlgebra R a b) := rfl

@[scoped simp]
/--
theorem `re_ofNat` / 定理 `re_ofNat`

English:
theorem re_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : QuadraticAlgebra R a b).re = ofNat(n)
  proof: rfl

@[scoped simp]

中文:
定理 re_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : QuadraticAlgebra R a b).re = of自然数(n)
  证明: rfl

@[scoped simp]
-/
theorem re_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).re = ofNat(n) := rfl

@[scoped simp]
/--
theorem `im_ofNat` / 定理 `im_ofNat`

English:
theorem im_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : QuadraticAlgebra R a b).im = 0
  proof: rfl

中文:
定理 im_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : QuadraticAlgebra R a b).im = 0
  证明: rfl
-/
theorem im_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).im = 0 := rfl

end AddCommMonoidWithOne

section AddCommGroupWithOne
variable [AddCommGroupWithOne R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroupWithOne (QuadraticAlgebra R a b)
  body: .C n
  intCast_ofNat n := by norm_cast
  intCast_negSucc n := by rw [Int.negSucc_eq, Int.cast_neg, C_neg]; norm_cast

@[simp, norm_cast]

中文:
实例 :
  签名: AddCommGroupWithOne (QuadraticAlgebra R a b)
  定义体: .C n
  intCast_ofNat n := by norm_cast
  intCast_negSucc n := by rw [Int.negSucc_eq, Int.cast_neg, C_neg]; norm_cast

@[simp, norm_cast]
-/
instance : AddCommGroupWithOne (QuadraticAlgebra R a b) where
  intCast n := .C n
  intCast_ofNat n := by norm_cast
  intCast_negSucc n := by rw [Int.negSucc_eq, Int.cast_neg, C_neg]; norm_cast

@[simp, norm_cast]
/--
theorem `re_intCast` / 定理 `re_intCast`

English:
theorem re_intCast
  given: (n : Int)
  statement: (n : QuadraticAlgebra R a b).re = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_intCast
  条件: (n : 整数)
  结论: (n : QuadraticAlgebra R a b).re = n
  证明: rfl

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_mem, coe_mem, isStarNormal_of_mem
-/
theorem re_intCast (n : Int) : (n : QuadraticAlgebra R a b).re = n := rfl

@[simp, norm_cast]
/--
theorem `im_intCast` / 定理 `im_intCast`

English:
theorem im_intCast
  given: (n : Int)
  statement: (n : QuadraticAlgebra R a b).im = 0
  proof: rfl

中文:
定理 im_intCast
  条件: (n : 整数)
  结论: (n : QuadraticAlgebra R a b).im = 0
  证明: rfl
-/
theorem im_intCast (n : Int) : (n : QuadraticAlgebra R a b).im = 0 := rfl

/--
theorem `C_intCast` / 定理 `C_intCast`

English:
theorem C_intCast
  given: (n : Int)
  statement: .C (n : R) = (n : QuadraticAlgebra R a b)
  proof: rfl

中文:
定理 C_intCast
  条件: (n : 整数)
  结论: .C (n : R) = (n : QuadraticAlgebra R a b)
  证明: rfl
-/
theorem C_intCast (n : Int) : .C (n : R) = (n : QuadraticAlgebra R a b) := rfl

end AddCommGroupWithOne

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: : NonUnitalNonAssocSemiring (QuadraticAlgebra R a b) where
  body: by ext <;> simp [mul_add] <;> abel
  right_distrib _ _ _ := by ext <;> simp [mul_add, add_mul] <;> abel
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp

中文:
实例 instNonUnitalNonAssocSemiring
  签名: : NonUnitalNonAssocSemiring (QuadraticAlgebra R a b) where
  定义体: by ext <;> simp [mul_add] <;> abel
  right_distrib _ _ _ := by ext <;> simp [mul_add, add_mul] <;> abel
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp

Depends on / 依赖: add_mul, mul_add, mul_zero, right_distrib, zero_mul
-/
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (QuadraticAlgebra R a b) where
  left_distrib _ _ _ := by ext <;> simp [mul_add] <;> abel
  right_distrib _ _ _ := by ext <;> simp [mul_add, add_mul] <;> abel
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp

/--
theorem `C_mul_eq_smul` / 定理 `C_mul_eq_smul`

English:
theorem C_mul_eq_smul
  given: (r : R) (x : QuadraticAlgebra R a b)
  proof: by
  ext <;> simp

@[simp]

中文:
定理 C_mul_eq_smul
  条件: (r : R) (x : QuadraticAlgebra R a b)
  证明: by
  ext <;> simp

@[simp]
-/
theorem C_mul_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (.C r * x : QuadraticAlgebra R a b) = r • x := by
  ext <;> simp

@[simp]
/--
theorem `C_mul` / 定理 `C_mul`

English:
theorem C_mul
  given: (x y : R)
  statement: .C (x * y) = (.C x * .C y : QuadraticAlgebra R a b)
  proof: by
  ext <;> simp

中文:
定理 C_mul
  条件: (x y : R)
  结论: .C (x * y) = (.C x * .C y : QuadraticAlgebra R a b)
  证明: by
  ext <;> simp
-/
theorem C_mul (x y : R) : .C (x * y) = (.C x * .C y : QuadraticAlgebra R a b) := by
  ext <;> simp

end NonUnitalNonAssocSemiring

section NonAssocSemiring
variable [NonAssocSemiring R]

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: : NonAssocSemiring (QuadraticAlgebra R a b) where
  body: by ext <;> simp
  mul_one _ := by ext <;> simp

@[simp]

中文:
实例 instNonAssocSemiring
  签名: : NonAssocSemiring (QuadraticAlgebra R a b) where
  定义体: by ext <;> simp
  mul_one _ := by ext <;> simp

@[simp]

Depends on / 依赖: mul_one
-/
instance instNonAssocSemiring : NonAssocSemiring (QuadraticAlgebra R a b) where
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

@[simp]
/--
theorem `nsmul_mk` / 定理 `nsmul_mk`

English:
theorem nsmul_mk
  given: (n : Nat) (x y : R)
  proof: by
  ext <;> simp

中文:
定理 nsmul_mk
  条件: (n : 自然数) (x y : R)
  证明: by
  ext <;> simp
-/
theorem nsmul_mk (n : Nat) (x y : R) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

end NonAssocSemiring

section Semiring
variable (a b) [Semiring R]

/-- `QuadraticAlgebra.re` as a `LinearMap` -/
@[simps]
/--
Definition of `reₗ` / `reₗ` 的定义

English:
definition reₗ
  signature: : QuadraticAlgebra R a b ->ₗ[R] R where
  body: re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 reₗ
  签名: : QuadraticAlgebra R a b ->ₗ[R] R where
  定义体: re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: StarMul, TrivialStar, TrivialStar.isStarNormal, isStarNormal
-/
def reₗ : QuadraticAlgebra R a b ->ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuadraticAlgebra.im` as a `LinearMap` -/
@[simps]
/--
Definition of `imₗ` / `imₗ` 的定义

English:
definition imₗ
  signature: : QuadraticAlgebra R a b ->ₗ[R] R where
  body: im
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 imₗ
  签名: : QuadraticAlgebra R a b ->ₗ[R] R where
  定义体: im
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: CommMonoid, CommMonoid.isStarNormal, StarMul, isStarNormal
-/
def imₗ : QuadraticAlgebra R a b ->ₗ[R] R where
  toFun := im
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
Definition of `linearEquivTuple` / `linearEquivTuple` 的定义

English:
definition linearEquivTuple
  signature: : QuadraticAlgebra R a b ≃ₗ[R] (Fin 2 -> R) where
  body: equivProd a b
map_add' _ _ := funext Fin.forall_fin_two.2 ⟨rfl, rfl⟩
map_smul' _ _ := funext Fin.forall_fin_two.2 ⟨rfl, rfl⟩

@[simp]

中文:
定义 linearEquivTuple
  签名: : QuadraticAlgebra R a b ≃ₗ[R] (Fin 2 -> R) where
  定义体: equivProd a b
map_add' _ _ := funext Fin.forall_fin_two.2 ⟨rfl, rfl⟩
map_smul' _ _ := funext Fin.forall_fin_two.2 ⟨rfl, rfl⟩

@[simp]

Depends on / 依赖: equivProd
-/
def linearEquivTuple : QuadraticAlgebra R a b ≃ₗ[R] (Fin 2 -> R) where
.trans .symm finTwoArrowEquiv _ __ := equivProd a b
map_add' _ _ := funext Fin.forall_fin_two.2 ⟨rfl, rfl⟩
map_smul' _ _ := funext Fin.forall_fin_two.2 ⟨rfl, rfl⟩

@[simp]
/--
lemma `linearEquivTuple_apply` / 引理 `linearEquivTuple_apply`

English:
lemma linearEquivTuple_apply
  given: (z : QuadraticAlgebra R a b)
  proof: rfl

@[simp]

中文:
引理 linearEquivTuple_apply
  条件: (z : QuadraticAlgebra R a b)
  证明: rfl

@[simp]
-/
lemma linearEquivTuple_apply (z : QuadraticAlgebra R a b) :
    (linearEquivTuple a b) z = ![z.re, z.im] := rfl

@[simp]
/--
lemma `linearEquivTuple_symm_apply` / 引理 `linearEquivTuple_symm_apply`

English:
lemma linearEquivTuple_symm_apply
  given: (x : Fin 2 -> R)
  proof: rfl

中文:
引理 linearEquivTuple_symm_apply
  条件: (x : Fin 2 -> R)
  证明: rfl
-/
lemma linearEquivTuple_symm_apply (x : Fin 2 -> R) :
    (linearEquivTuple a b).symm x = ⟨x 0, x 1⟩ := rfl

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: : Module.Basis (Fin 2) R (QuadraticAlgebra R a b)
  body: .ofEquivFun linearEquivTuple a b

@[simp]

中文:
定义 basis
  签名: : Module.Basis (Fin 2) R (QuadraticAlgebra R a b)
  定义体: .ofEquivFun linearEquivTuple a b

@[simp]

Depends on / 依赖: linearEquivTuple, ofEquivFun
-/
noncomputable def basis : Module.Basis (Fin 2) R (QuadraticAlgebra R a b) :=
.ofEquivFun linearEquivTuple a b

@[simp]
/--
theorem `basis_repr_apply` / 定理 `basis_repr_apply`

English:
theorem basis_repr_apply
  given: (x : QuadraticAlgebra R a b)
  proof: rfl

中文:
定理 basis_repr_apply
  条件: (x : QuadraticAlgebra R a b)
  证明: rfl
-/
theorem basis_repr_apply (x : QuadraticAlgebra R a b) :
    (basis a b).repr x = ![x.re, x.im] := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite R (QuadraticAlgebra R a b)
  body: .of_basis (basis a b)

中文:
实例 :
  签名: Module.Finite R (QuadraticAlgebra R a b)
  定义体: .of_basis (basis a b)

Depends on / 依赖: of_basis
-/
instance : Module.Finite R (QuadraticAlgebra R a b) := .of_basis (basis a b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R (QuadraticAlgebra R a b)
  body: .of_basis (basis a b)

中文:
实例 :
  签名: Module.Free R (QuadraticAlgebra R a b)
  定义体: .of_basis (basis a b)

Depends on / 依赖: of_basis
-/
instance : Module.Free R (QuadraticAlgebra R a b) := .of_basis (basis a b)

/--
theorem `rank_eq_two` / 定理 `rank_eq_two`

English:
theorem rank_eq_two
  given: [StrongRankCondition R]
  statement: Module.rank R (QuadraticAlgebra R a b) = 2
  proof: by
  simp [rank_eq_card_basis (basis a b)]

中文:
定理 rank_eq_two
  条件: [StrongRankCondition R]
  结论: Module.rank R (QuadraticAlgebra R a b) = 2
  证明: by
  simp [rank_eq_card_basis (basis a b)]

Depends on / 依赖: rank_eq_card_basis
-/
theorem rank_eq_two [StrongRankCondition R] : Module.rank R (QuadraticAlgebra R a b) = 2 := by
  simp [rank_eq_card_basis (basis a b)]

/--
theorem `finrank_eq_two` / 定理 `finrank_eq_two`

English:
theorem finrank_eq_two
  given: [StrongRankCondition R]
  proof: by
  simp [Module.finrank, rank_eq_two]

中文:
定理 finrank_eq_two
  条件: [StrongRankCondition R]
  证明: by
  simp [Module.finrank, rank_eq_two]

Depends on / 依赖: Module, Module.finrank, finrank, rank_eq_two
-/
theorem finrank_eq_two [StrongRankCondition R] :
    Module.finrank R (QuadraticAlgebra R a b) = 2 := by
  simp [Module.finrank, rank_eq_two]

end Semiring

section CommSemiring
variable [CommSemiring R]

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: : CommSemiring (QuadraticAlgebra R a b) where
  body: by ext <;> simp <;> ring
  mul_comm _ _ := by ext <;> simp <;> ring

中文:
实例 instCommSemiring
  签名: : CommSemiring (QuadraticAlgebra R a b) where
  定义体: by ext <;> simp <;> ring
  mul_comm _ _ := by ext <;> simp <;> ring

Depends on / 依赖: mul_comm
-/
instance instCommSemiring : CommSemiring (QuadraticAlgebra R a b) where
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  mul_comm _ _ := by ext <;> simp <;> ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: S] [Algebra S R] : Algebra S (QuadraticAlgebra R a b) where
  body: .C (algebraMap S R s)
  algebraMap.map_one' := by ext <;> simp
  algebraMap.map_mul' x y := by ext <;> simp
  algebraMap.map_zero' := by ext <;> simp
  algebraMap.map_add' x y := by ext <;> simp
  commutes' s z := by ext <;> simp [Algebra.commutes]
  smul_def' s x := by ext <;> simp [Algebra.smul_de

中文:
实例 [CommSemiring
  签名: S] [Algebra S R] : Algebra S (QuadraticAlgebra R a b) where
  定义体: .C (algebraMap S R s)
  algebraMap.map_one' := by ext <;> simp
  algebraMap.map_mul' x y := by ext <;> simp
  algebraMap.map_zero' := by ext <;> simp
  algebraMap.map_add' x y := by ext <;> simp
  commutes' s z := by ext <;> simp [Algebra.commutes]
  smul_def' s x := by ext <;> simp [Algebra.smul_de

Depends on / 依赖: algebraMap
-/
instance [CommSemiring S] [Algebra S R] : Algebra S (QuadraticAlgebra R a b) where
  algebraMap.toFun s := .C (algebraMap S R s)
  algebraMap.map_one' := by ext <;> simp
  algebraMap.map_mul' x y := by ext <;> simp
  algebraMap.map_zero' := by ext <;> simp
  algebraMap.map_add' x y := by ext <;> simp
  commutes' s z := by ext <;> simp [Algebra.commutes]
  smul_def' s x := by ext <;> simp [Algebra.smul_def]

/--
theorem `algebraMap_eq` / 定理 `algebraMap_eq`

English:
theorem algebraMap_eq
  given: (r : R)
  statement: algebraMap R (QuadraticAlgebra R a b) r = ⟨r, 0⟩
  proof: rfl

中文:
定理 algebraMap_eq
  条件: (r : R)
  结论: algebraMap R (QuadraticAlgebra R a b) r = ⟨r, 0⟩
  证明: rfl
-/
theorem algebraMap_eq (r : R) : algebraMap R (QuadraticAlgebra R a b) r = ⟨r, 0⟩ := rfl

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  statement: (algebraMap R (QuadraticAlgebra R a b) : _ -> _).Injective
  proof: fun _ _ => by simp [algebraMap_eq]

@[simp]

中文:
定理 algebraMap_injective
  结论: (algebraMap R (QuadraticAlgebra R a b) : _ -> _).Injective
  证明: fun _ _ => by simp [algebraMap_eq]

@[simp]

Depends on / 依赖: algebraMap_eq
-/
theorem algebraMap_injective : (algebraMap R (QuadraticAlgebra R a b) : _ -> _).Injective :=
  fun _ _ => by simp [algebraMap_eq]

@[simp]
/--
theorem `algebraMap_inj` / 定理 `algebraMap_inj`

English:
theorem algebraMap_inj
  given: {x y : R}
  proof: algebraMap_injective.eq_iff

@[simp]

中文:
定理 algebraMap_inj
  条件: {x y : R}
  证明: algebraMap_injective.eq_iff

@[simp]

Depends on / 依赖: algebraMap_injective, algebraMap_injective.eq_iff, eq_iff
-/
theorem algebraMap_inj {x y : R} :
    algebraMap R (QuadraticAlgebra R a b) x = algebraMap _ _ y ↔ x = y :=
  algebraMap_injective.eq_iff

@[simp]
/--
theorem `algebraMap_re` / 定理 `algebraMap_re`

English:
theorem algebraMap_re
  statement: (algebraMap R (QuadraticAlgebra R a b) r).re = r
  proof: rfl

@[simp]

中文:
定理 algebraMap_re
  结论: (algebraMap R (QuadraticAlgebra R a b) r).re = r
  证明: rfl

@[simp]
-/
theorem algebraMap_re : (algebraMap R (QuadraticAlgebra R a b) r).re = r := rfl

@[simp]
/--
theorem `algebraMap_im` / 定理 `algebraMap_im`

English:
theorem algebraMap_im
  statement: (algebraMap R (QuadraticAlgebra R a b) r).im = 0
  proof: rfl

中文:
定理 algebraMap_im
  结论: (algebraMap R (QuadraticAlgebra R a b) r).im = 0
  证明: rfl
-/
theorem algebraMap_im : (algebraMap R (QuadraticAlgebra R a b) r).im = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [Module S R] [Module.IsTorsionFree S R] :
  body: (linearEquivTuple ..).injective.moduleIsTorsionFree _ (by simp)

@[simp]

中文:
实例 [Semiring
  签名: S] [Module S R] [Module.IsTorsionFree S R] :
  定义体: (linearEquivTuple ..).injective.moduleIsTorsionFree _ (by simp)

@[simp]

Depends on / 依赖: injective, injective.moduleIsTorsionFree, linearEquivTuple, moduleIsTorsionFree
-/
instance [Semiring S] [Module S R] [Module.IsTorsionFree S R] :
    Module.IsTorsionFree S (QuadraticAlgebra R a b) :=
  (linearEquivTuple ..).injective.moduleIsTorsionFree _ (by simp)

@[simp]
/--
theorem `C_pow` / 定理 `C_pow`

English:
theorem C_pow
  given: (n : Nat) (r : R)
  statement: (.C (r ^ n : R) : QuadraticAlgebra R a b) = (.C r) ^ n
  proof: (algebraMap R (QuadraticAlgebra R a b)).map_pow r n

中文:
定理 C_pow
  条件: (n : 自然数) (r : R)
  结论: (.C (r ^ n : R) : QuadraticAlgebra R a b) = (.C r) ^ n
  证明: (algebraMap R (QuadraticAlgebra R a b)).map_pow r n

Depends on / 依赖: QuadraticAlgebra, algebraMap, map_pow
-/
theorem C_pow (n : Nat) (r : R) : (.C (r ^ n : R) : QuadraticAlgebra R a b) = (.C r) ^ n :=
  (algebraMap R (QuadraticAlgebra R a b)).map_pow r n

/--
theorem `mul_C_eq_smul` / 定理 `mul_C_eq_smul`

English:
theorem mul_C_eq_smul
  given: (r : R) (x : QuadraticAlgebra R a b)
  proof: by
  rw [mul_comm]; rw [C_mul_eq_smul r x]

@[simp]

中文:
定理 mul_C_eq_smul
  条件: (r : R) (x : QuadraticAlgebra R a b)
  证明: by
  rw [mul_comm]; rw [C_mul_eq_smul r x]

@[simp]

Depends on / 依赖: C_mul_eq_smul, mul_comm
-/
theorem mul_C_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (x * .C r : QuadraticAlgebra R a b) = r • x := by
  rw [mul_comm]; rw [C_mul_eq_smul r x]

@[simp]
/--
theorem `C_eq_algebraMap` / 定理 `C_eq_algebraMap`

English:
theorem C_eq_algebraMap
  statement: QuadraticAlgebra.C = (algebraMap R (QuadraticAlgebra R a b))
  proof: rfl

中文:
定理 C_eq_algebraMap
  结论: QuadraticAlgebra.C = (algebraMap R (QuadraticAlgebra R a b))
  证明: rfl
-/
theorem C_eq_algebraMap : QuadraticAlgebra.C = (algebraMap R (QuadraticAlgebra R a b)) := rfl

/--
theorem `smul_C` / 定理 `smul_C`

English:
theorem smul_C
  given: (r1 r2 : R)
  proof: by rw [C_mul, C_mul_eq_smul]

中文:
定理 smul_C
  条件: (r1 r2 : R)
  证明: by rw [C_mul, C_mul_eq_smul]

Depends on / 依赖: C_mul, C_mul_eq_smul
-/
theorem smul_C (r1 r2 : R) :
    r1 • (.C r2 : QuadraticAlgebra R a b) = .C (r1 * r2) := by rw [C_mul, C_mul_eq_smul]

/--
theorem `algebraMap_dvd_iff` / 定理 `algebraMap_dvd_iff`

English:
theorem algebraMap_dvd_iff
  given: {r : R} {z : QuadraticAlgebra R a b}
  proof: by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    simp [QuadraticAlgebra.ext_iff, hr, hi, ← C_eq_algebraMap]

@[simp]

中文:
定理 algebraMap_dvd_iff
  条件: {r : R} {z : QuadraticAlgebra R a b}
  证明: by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    simp [QuadraticAlgebra.ext_iff, hr, hi, ← C_eq_algebraMap]

@[simp]

Depends on / 依赖: C_eq_algebraMap, QuadraticAlgebra, QuadraticAlgebra.ext_iff, ext_iff
-/
theorem algebraMap_dvd_iff {r : R} {z : QuadraticAlgebra R a b} :
    (algebraMap R (QuadraticAlgebra R a b) r) ∣ z ↔ r ∣ z.re ∧ r ∣ z.im := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    simp [QuadraticAlgebra.ext_iff, hr, hi, ← C_eq_algebraMap]

@[simp]
/--
theorem `algebraMap_dvd_iff_dvd` / 定理 `algebraMap_dvd_iff_dvd`

English:
theorem algebraMap_dvd_iff_dvd
  given: {z w : R}
  proof: by
  rw [algebraMap_dvd_iff]
  simp

中文:
定理 algebraMap_dvd_iff_dvd
  条件: {z w : R}
  证明: by
  rw [algebraMap_dvd_iff]
  simp

Depends on / 依赖: algebraMap_dvd_iff
-/
theorem algebraMap_dvd_iff_dvd {z w : R} :
    algebraMap R (QuadraticAlgebra R a b) z ∣ algebraMap R (QuadraticAlgebra R a b) w ↔ z ∣ w := by
  rw [algebraMap_dvd_iff]
  simp

end CommSemiring

section CommRing

variable [CommRing R]

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing (QuadraticAlgebra R a b) where

中文:
实例 instCommRing
  签名: : CommRing (QuadraticAlgebra R a b) where
-/
instance instCommRing : CommRing (QuadraticAlgebra R a b) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CharZero
  signature: R] : CharZero (QuadraticAlgebra R a b) where
  body: by
    simp [QuadraticAlgebra.ext_iff]

@[simp]

中文:
实例 [CharZero
  签名: R] : CharZero (QuadraticAlgebra R a b) where
  定义体: by
    simp [QuadraticAlgebra.ext_iff]

@[simp]

Depends on / 依赖: QuadraticAlgebra, QuadraticAlgebra.ext_iff, ext_iff
-/
instance [CharZero R] : CharZero (QuadraticAlgebra R a b) where
  cast_injective m n := by
    simp [QuadraticAlgebra.ext_iff]

@[simp]
/--
theorem `zsmul_val` / 定理 `zsmul_val`

English:
theorem zsmul_val
  given: (n : Int) (x y : R)
  proof: by
  ext <;> simp

中文:
定理 zsmul_val
  条件: (n : 整数) (x y : R)
  证明: by
  ext <;> simp
-/
theorem zsmul_val (n : Int) (x y : R) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

end CommRing

end QuadraticAlgebra
