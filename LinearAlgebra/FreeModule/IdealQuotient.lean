/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-! # Ideals in free modules over PIDs

## Main results

- `Ideal.quotientEquivPiSpan`: `S ⧸ I`, if `S` is finite free as a module over a PID `R`,
  can be written as a product of quotients of `R` by principal ideals.

-/

@[expose] public section

open Module
open scoped DirectSum

namespace Ideal


variable {ι R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsPrincipalIdealRing R] [IsDomain S] [Finite ι]

/--
Definition of `quotientEquivPiSpan` / `quotientEquivPiSpan` 的定义

English:
definition quotientEquivPiSpan
  signature: (I : Ideal S) (b : Basis ι R S) (hI : I != ⊥)
  body: Submodule.quotientEquivPiSpan (I.restrictScalars R) b finrank_eq_finrank b I hI

中文:
定义 quotientEquivPiSpan
  签名: (I : 理想 S) (b : 基 ι R S) (hI : I != ⊥)
  定义体: Submodule.quotientEquivPiSpan (I.restrictScalars R) b finrank_eq_finrank b I hI

Depends on / 依赖: I.restrictScalars, Submodule, Submodule.quotientEquivPiSpan, finrank_eq_finrank, quotientEquivPiSpan, restrictScalars
-/
noncomputable def quotientEquivPiSpan (I : Ideal S) (b : Basis ι R S) (hI : I != ⊥) :
    (S ⧸ I) ≃ₗ[R] forall i, R ⧸ span ({I.smithCoeffs b hI i} : Set R) :=
Submodule.quotientEquivPiSpan (I.restrictScalars R) b finrank_eq_finrank b I hI

/--
Definition of `quotientEquivPiZMod` / `quotientEquivPiZMod` 的定义

English:
definition quotientEquivPiZMod
  signature: (I : Ideal S) (b : Basis ι Int S) (hI : I != ⊥)
  body: Submodule.quotientEquivPiZMod (I.restrictScalars Int) b finrank_eq_finrank b I hI

中文:
定义 quotientEquivPiZMod
  签名: (I : 理想 S) (b : 基 ι 整数 S) (hI : I != ⊥)
  定义体: Submodule.quotientEquivPiZMod (I.restrictScalars Int) b finrank_eq_finrank b I hI

Depends on / 依赖: I.restrictScalars, Submodule, Submodule.quotientEquivPiZMod, finrank_eq_finrank, quotientEquivPiZMod, restrictScalars
-/
noncomputable def quotientEquivPiZMod (I : Ideal S) (b : Basis ι Int S) (hI : I != ⊥) :
    S ⧸ I ≃+ forall i, ZMod (I.smithCoeffs b hI i).natAbs :=
Submodule.quotientEquivPiZMod (I.restrictScalars Int) b finrank_eq_finrank b I hI

/--
theorem `finiteQuotientOfFreeOfNeBot` / 定理 `finiteQuotientOfFreeOfNeBot`

English:
theorem finiteQuotientOfFreeOfNeBot
  statement: [Module.Free Int S] [Module.Finite Int S]
  proof: let b := Module.Free.chooseBasis Int S
Submodule.finiteQuotientOfFreeOfRankEq (I.restrictScalars Int) finrank_eq_finrank b I hI

中文:
定理 finiteQuotientOfFreeOfNeBot
  结论: [模.自由 整数 S] [模.有限 整数 S]
  证明: let b := Module.Free.chooseBasis Int S
Submodule.finiteQuotientOfFreeOfRankEq (I.restrictScalars Int) finrank_eq_finrank b I hI

Depends on / 依赖: I.restrictScalars, Module, Module.Free.chooseBasis, Submodule, Submodule.finiteQuotientOfFreeOfRankEq, chooseBasis, finiteQuotientOfFreeOfRankEq, finrank_eq_finrank, restrictScalars
-/
theorem finiteQuotientOfFreeOfNeBot [Module.Free Int S] [Module.Finite Int S]
    (I : Ideal S) (hI : I != ⊥) : Finite (S ⧸ I) :=
  let b := Module.Free.chooseBasis Int S
Submodule.finiteQuotientOfFreeOfRankEq (I.restrictScalars Int) finrank_eq_finrank b I hI

variable (F : Type*) [CommRing F] [Algebra F R] [Algebra F S] [IsScalarTower F R S]
  (b : Basis ι R S) {I : Ideal S} (hI : I != ⊥)

/--
Definition of `quotientEquivDirectSum` / `quotientEquivDirectSum` 的定义

English:
definition quotientEquivDirectSum
  signature: :
  body: Submodule.quotientEquivDirectSum F b (N := (I.restrictScalars R)) finrank_eq_finrank b I hI

中文:
定义 quotientEquivDirectSum
  签名: :
  定义体: Submodule.quotientEquivDirectSum F b (N := (I.restrictScalars R)) finrank_eq_finrank b I hI

Depends on / 依赖: I.restrictScalars, Submodule, Submodule.quotientEquivDirectSum, finrank_eq_finrank, quotientEquivDirectSum, restrictScalars
-/
noncomputable def quotientEquivDirectSum :
    (S ⧸ I) ≃ₗ[F] ⨁ i, R ⧸ span ({I.smithCoeffs b hI i} : Set R) :=
Submodule.quotientEquivDirectSum F b (N := (I.restrictScalars R)) finrank_eq_finrank b I hI

/--
theorem `finrank_quotient_eq_sum` / 定理 `finrank_quotient_eq_sum`

English:
theorem finrank_quotient_eq_sum
  statement: {ι} [Fintype ι] (b : Basis ι R S) [Nontrivial F]
  proof: by
  -- slow, and dot notation doesn't work
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b hI]; rw [Module.finrank_directSum]

中文:
定理 finrank_quotient_eq_sum
  结论: {ι} [有限类型 ι] (b : 基 ι R S) [非平凡 F]
  证明: by
  -- slow, and dot notation doesn't work
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b hI]; rw [Module.finrank_directSum]
-/
theorem finrank_quotient_eq_sum {ι} [Fintype ι] (b : Basis ι R S) [Nontrivial F]
    [forall i, Module.Free F (R ⧸ span ({I.smithCoeffs b hI i} : Set R))]
    [forall i, Module.Finite F (R ⧸ span ({I.smithCoeffs b hI i} : Set R))] :
    Module.finrank F (S ⧸ I) =
      ∑ i, Module.finrank F (R ⧸ span ({I.smithCoeffs b hI i} : Set R)) := by
  -- slow, and dot notation doesn't work
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b hI]; rw [Module.finrank_directSum]

end Ideal
