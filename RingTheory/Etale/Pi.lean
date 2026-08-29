/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Smooth.Pi
public import Mathlib.RingTheory.Unramified.Pi
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-!

# Formal-étaleness of finite products of rings

## Main result

- `Algebra.FormallyEtale.pi_iff`: If `I` is finite, `Π i : I, A i` is `R`-formally-étale
  if and only if each `A i` is `R`-formally-étale.

-/

public section

namespace Algebra.FormallyEtale

variable {R : Type*} {I : Type*} (A : I -> Type*)
variable [CommRing R] [forall i, CommRing (A i)] [forall i, Algebra R (A i)]

/--
theorem `pi_iff` / 定理 `pi_iff`

English:
theorem pi_iff
  given: [Finite I]
  proof: by
  simp_rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth, forall_and]
  rw [FormallyUnramified.pi_iff A]; rw [FormallySmooth.pi_iff A]

中文:
定理 pi_iff
  条件: [Finite I]
  证明: by
  simp_rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth, forall_and]
  rw [FormallyUnramified.pi_iff A]; rw [FormallySmooth.pi_iff A]

Depends on / 依赖: FormallyEtale, FormallyEtale.iff_formallyUnramified_and_formallySmooth, FormallySmooth, FormallySmooth.pi_iff, FormallyUnramified, FormallyUnramified.pi_iff, forall_and, iff_formallyUnramified_and_formallySmooth, pi_iff, simp_rw
-/
theorem pi_iff [Finite I] :
    FormallyEtale R (Π i, A i) ↔ forall i, FormallyEtale R (A i) := by
  simp_rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth, forall_and]
  rw [FormallyUnramified.pi_iff A]; rw [FormallySmooth.pi_iff A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: I] [forall i, FormallyEtale R (A i)] : FormallyEtale R (Π i, A i)
  body: .of_formallyUnramified_and_formallySmooth

中文:
实例 [Finite
  签名: I] [对任意 i, FormallyEtale R (A i)] : FormallyEtale R (Π i, A i)
  定义体: .of_formallyUnramified_and_formallySmooth

Depends on / 依赖: of_formallyUnramified_and_formallySmooth
-/
instance [Finite I] [forall i, FormallyEtale R (A i)] : FormallyEtale R (Π i, A i) :=
  .of_formallyUnramified_and_formallySmooth

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: I] [forall i, Etale R (A i)] : Etale R (Π i, A i) where

中文:
实例 [Finite
  签名: I] [对任意 i, Etale R (A i)] : Etale R (Π i, A i) where
-/
instance [Finite I] [forall i, Etale R (A i)] : Etale R (Π i, A i) where

end Algebra.FormallyEtale
