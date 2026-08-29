/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-!

# Basis of a polynomial ring

-/

@[expose] public noncomputable section

open Module

universe u

variable (R : Type u) [Semiring R]

namespace Polynomial

/--
Definition of `basisMonomials` / `basisMonomials` 的定义

English:
definition basisMonomials
  signature: : Basis Nat R R[X]
  body: .ofRepr (toFinsuppIsoLinear R).trans AddMonoidAlgebra.coeffLinearEquiv _

@[simp]

中文:
定义 basisMonomials
  签名: : 基 自然数 R R[X]
  定义体: .ofRepr (toFinsuppIsoLinear R).trans AddMonoidAlgebra.coeffLinearEquiv _

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeffLinearEquiv, coeffLinearEquiv, ofRepr, toFinsuppIsoLinear
-/
def basisMonomials : Basis Nat R R[X] :=
.ofRepr (toFinsuppIsoLinear R).trans AddMonoidAlgebra.coeffLinearEquiv _

@[simp]
/--
theorem `coe_basisMonomials` / 定理 `coe_basisMonomials`

English:
theorem coe_basisMonomials
  statement: (basisMonomials R : Nat -> R[X]) = fun s => monomial s 1
  proof: funext fun _ => ofFinsupp_single _ _

中文:
定理 coe_basisMonomials
  结论: (basisMonomials R : 自然数 -> R[X]) = fun s => monomial s 1
  证明: funext fun _ => ofFinsupp_single _ _

Depends on / 依赖: ofFinsupp_single
-/
theorem coe_basisMonomials : (basisMonomials R : Nat -> R[X]) = fun s => monomial s 1 :=
  funext fun _ => ofFinsupp_single _ _

end Polynomial
