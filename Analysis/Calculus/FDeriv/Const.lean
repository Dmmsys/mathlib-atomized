/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Fréchet derivative of constant functions

This file contains the usual formulas (and existence assertions) for the derivative of constant
functions, including various special cases such as the functions `0`, `1`, `Nat.cast n`,
`Int.cast z`, and other numerals.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Asymptotics Function Filter Set Metric
open scoped Topology NNReal ENNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f : E -> F} {x : E} {s : Set E}

section Const

/--
theorem `hasFDerivAtFilter_const` / 定理 `hasFDerivAtFilter_const`

English:
theorem hasFDerivAtFilter_const
  given: (c : F) (L : Filter (E × E))
  proof: .of_isLittleOTVS (IsLittleOTVS.zero _ _).congr_left fun _ => by simp

中文:
定理 hasFDerivAtFilter_const
  条件: (c : F) (L : Filter (E × E))
  证明: .of_isLittleOTVS (IsLittleOTVS.zero _ _).congr_left fun _ => by simp

Depends on / 依赖: IsLittleOTVS, IsLittleOTVS.zero, congr_left, of_isLittleOTVS
-/
theorem hasFDerivAtFilter_const (c : F) (L : Filter (E × E)) :
    HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L :=
.of_isLittleOTVS (IsLittleOTVS.zero _ _).congr_left fun _ => by simp

/--
theorem `hasFDerivAtFilter_zero` / 定理 `hasFDerivAtFilter_zero`

English:
theorem hasFDerivAtFilter_zero
  given: (L : Filter (E × E))
  proof: hasFDerivAtFilter_const _ _

中文:
定理 hasFDerivAtFilter_zero
  条件: (L : Filter (E × E))
  证明: hasFDerivAtFilter_const _ _

Depends on / 依赖: hasFDerivAtFilter_const
-/
theorem hasFDerivAtFilter_zero (L : Filter (E × E)) :
    HasFDerivAtFilter (0 : E -> F) (0 : E ->L[𝕜] F) L := hasFDerivAtFilter_const _ _

/--
theorem `hasFDerivAtFilter_one` / 定理 `hasFDerivAtFilter_one`

English:
theorem hasFDerivAtFilter_one
  given: [One F] (L : Filter (E × E))
  proof: hasFDerivAtFilter_const _ _

中文:
定理 hasFDerivAtFilter_one
  条件: [One F] (L : Filter (E × E))
  证明: hasFDerivAtFilter_const _ _

Depends on / 依赖: hasFDerivAtFilter_const
-/
theorem hasFDerivAtFilter_one [One F] (L : Filter (E × E)) :
    HasFDerivAtFilter (1 : E -> F) (0 : E ->L[𝕜] F) L := hasFDerivAtFilter_const _ _

/--
theorem `hasFDerivAtFilter_natCast` / 定理 `hasFDerivAtFilter_natCast`

English:
theorem hasFDerivAtFilter_natCast
  given: [NatCast F] (n : Nat) (L : Filter (E × E))
  proof: hasFDerivAtFilter_const _ _

中文:
定理 hasFDerivAtFilter_natCast
  条件: [自然数Cast F] (n : 自然数) (L : Filter (E × E))
  证明: hasFDerivAtFilter_const _ _

Depends on / 依赖: hasFDerivAtFilter_const
-/
theorem hasFDerivAtFilter_natCast [NatCast F] (n : Nat) (L : Filter (E × E)) :
    HasFDerivAtFilter (n : E -> F) (0 : E ->L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _

/--
theorem `hasFDerivAtFilter_intCast` / 定理 `hasFDerivAtFilter_intCast`

English:
theorem hasFDerivAtFilter_intCast
  given: [IntCast F] (z : Int) (L : Filter (E × E))
  proof: hasFDerivAtFilter_const _ _

中文:
定理 hasFDerivAtFilter_intCast
  条件: [整数Cast F] (z : 整数) (L : Filter (E × E))
  证明: hasFDerivAtFilter_const _ _

Depends on / 依赖: hasFDerivAtFilter_const
-/
theorem hasFDerivAtFilter_intCast [IntCast F] (z : Int) (L : Filter (E × E)) :
    HasFDerivAtFilter (z : E -> F) (0 : E ->L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _

/--
theorem `hasFDerivAtFilter_ofNat` / 定理 `hasFDerivAtFilter_ofNat`

English:
theorem hasFDerivAtFilter_ofNat
  given: (n : Nat) [OfNat F n] (L : Filter (E × E))
  proof: hasFDerivAtFilter_const _ _

@[fun_prop]

中文:
定理 hasFDerivAtFilter_ofNat
  条件: (n : 自然数) [Of自然数 F n] (L : Filter (E × E))
  证明: hasFDerivAtFilter_const _ _

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_const
-/
theorem hasFDerivAtFilter_ofNat (n : Nat) [OfNat F n] (L : Filter (E × E)) :
    HasFDerivAtFilter (ofNat(n) : E -> F) (0 : E ->L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _

@[fun_prop]
/--
theorem `hasStrictFDerivAt_const` / 定理 `hasStrictFDerivAt_const`

English:
theorem hasStrictFDerivAt_const
  given: (c : F) (x : E)
  proof: hasFDerivAtFilter_const _ _

@[fun_prop]

中文:
定理 hasStrictFDerivAt_const
  条件: (c : F) (x : E)
  证明: hasFDerivAtFilter_const _ _

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_const
-/
theorem hasStrictFDerivAt_const (c : F) (x : E) :
    HasStrictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x :=
  hasFDerivAtFilter_const _ _

@[fun_prop]
/--
theorem `hasStrictFDerivAt_zero` / 定理 `hasStrictFDerivAt_zero`

English:
theorem hasStrictFDerivAt_zero
  given: (x : E)
  proof: hasStrictFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasStrictFDerivAt_zero
  条件: (x : E)
  证明: hasStrictFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_const
-/
theorem hasStrictFDerivAt_zero (x : E) :
    HasStrictFDerivAt (0 : E -> F) (0 : E ->L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasStrictFDerivAt_one` / 定理 `hasStrictFDerivAt_one`

English:
theorem hasStrictFDerivAt_one
  given: [One F] (x : E)
  proof: hasStrictFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasStrictFDerivAt_one
  条件: [One F] (x : E)
  证明: hasStrictFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_const
-/
theorem hasStrictFDerivAt_one [One F] (x : E) :
    HasStrictFDerivAt (1 : E -> F) (0 : E ->L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasStrictFDerivAt_natCast` / 定理 `hasStrictFDerivAt_natCast`

English:
theorem hasStrictFDerivAt_natCast
  given: [NatCast F] (n : Nat) (x : E)
  proof: hasStrictFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasStrictFDerivAt_natCast
  条件: [自然数Cast F] (n : 自然数) (x : E)
  证明: hasStrictFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_const
-/
theorem hasStrictFDerivAt_natCast [NatCast F] (n : Nat) (x : E) :
    HasStrictFDerivAt (n : E -> F) (0 : E ->L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasStrictFDerivAt_intCast` / 定理 `hasStrictFDerivAt_intCast`

English:
theorem hasStrictFDerivAt_intCast
  given: [IntCast F] (z : Int) (x : E)
  proof: hasStrictFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasStrictFDerivAt_intCast
  条件: [整数Cast F] (z : 整数) (x : E)
  证明: hasStrictFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_const
-/
theorem hasStrictFDerivAt_intCast [IntCast F] (z : Int) (x : E) :
    HasStrictFDerivAt (z : E -> F) (0 : E ->L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasStrictFDerivAt_ofNat` / 定理 `hasStrictFDerivAt_ofNat`

English:
theorem hasStrictFDerivAt_ofNat
  given: (n : Nat) [OfNat F n] (x : E)
  proof: hasStrictFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasStrictFDerivAt_ofNat
  条件: (n : 自然数) [Of自然数 F n] (x : E)
  证明: hasStrictFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_const
-/
theorem hasStrictFDerivAt_ofNat (n : Nat) [OfNat F n] (x : E) :
    HasStrictFDerivAt (ofNat(n) : E -> F) (0 : E ->L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasFDerivWithinAt_const` / 定理 `hasFDerivWithinAt_const`

English:
theorem hasFDerivWithinAt_const
  given: (c : F) (x : E) (s : Set E)
  proof: hasFDerivAtFilter_const _ _

@[fun_prop]

中文:
定理 hasFDerivWithinAt_const
  条件: (c : F) (x : E) (s : Set E)
  证明: hasFDerivAtFilter_const _ _

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_const
-/
theorem hasFDerivWithinAt_const (c : F) (x : E) (s : Set E) :
    HasFDerivWithinAt (fun _ => c) (0 : E ->L[𝕜] F) s x :=
  hasFDerivAtFilter_const _ _

@[fun_prop]
/--
theorem `hasFDerivWithinAt_zero` / 定理 `hasFDerivWithinAt_zero`

English:
theorem hasFDerivWithinAt_zero
  given: (x : E) (s : Set E)
  proof: hasFDerivWithinAt_const _ _ _

@[fun_prop]

中文:
定理 hasFDerivWithinAt_zero
  条件: (x : E) (s : Set E)
  证明: hasFDerivWithinAt_const _ _ _

@[fun_prop]

Depends on / 依赖: hasFDerivWithinAt_const
-/
theorem hasFDerivWithinAt_zero (x : E) (s : Set E) :
    HasFDerivWithinAt (0 : E -> F) (0 : E ->L[𝕜] F) s x := hasFDerivWithinAt_const _ _ _

@[fun_prop]
/--
theorem `hasFDerivWithinAt_one` / 定理 `hasFDerivWithinAt_one`

English:
theorem hasFDerivWithinAt_one
  given: [One F] (x : E) (s : Set E)
  proof: hasFDerivWithinAt_const _ _ _

@[fun_prop]

中文:
定理 hasFDerivWithinAt_one
  条件: [One F] (x : E) (s : Set E)
  证明: hasFDerivWithinAt_const _ _ _

@[fun_prop]

Depends on / 依赖: hasFDerivWithinAt_const
-/
theorem hasFDerivWithinAt_one [One F] (x : E) (s : Set E) :
    HasFDerivWithinAt (1 : E -> F) (0 : E ->L[𝕜] F) s x := hasFDerivWithinAt_const _ _ _

@[fun_prop]
/--
theorem `hasFDerivWithinAt_natCast` / 定理 `hasFDerivWithinAt_natCast`

English:
theorem hasFDerivWithinAt_natCast
  given: [NatCast F] (n : Nat) (x : E) (s : Set E)
  proof: hasFDerivWithinAt_const _ _ _

@[fun_prop]

中文:
定理 hasFDerivWithinAt_natCast
  条件: [自然数Cast F] (n : 自然数) (x : E) (s : Set E)
  证明: hasFDerivWithinAt_const _ _ _

@[fun_prop]

Depends on / 依赖: hasFDerivWithinAt_const
-/
theorem hasFDerivWithinAt_natCast [NatCast F] (n : Nat) (x : E) (s : Set E) :
    HasFDerivWithinAt (n : E -> F) (0 : E ->L[𝕜] F) s x :=
  hasFDerivWithinAt_const _ _ _

@[fun_prop]
/--
theorem `hasFDerivWithinAt_intCast` / 定理 `hasFDerivWithinAt_intCast`

English:
theorem hasFDerivWithinAt_intCast
  given: [IntCast F] (z : Int) (x : E) (s : Set E)
  proof: hasFDerivWithinAt_const _ _ _

@[fun_prop]

中文:
定理 hasFDerivWithinAt_intCast
  条件: [整数Cast F] (z : 整数) (x : E) (s : Set E)
  证明: hasFDerivWithinAt_const _ _ _

@[fun_prop]

Depends on / 依赖: hasFDerivWithinAt_const
-/
theorem hasFDerivWithinAt_intCast [IntCast F] (z : Int) (x : E) (s : Set E) :
    HasFDerivWithinAt (z : E -> F) (0 : E ->L[𝕜] F) s x :=
  hasFDerivWithinAt_const _ _ _

@[fun_prop]
/--
theorem `hasFDerivWithinAt_ofNat` / 定理 `hasFDerivWithinAt_ofNat`

English:
theorem hasFDerivWithinAt_ofNat
  given: (n : Nat) [OfNat F n] (x : E) (s : Set E)
  proof: hasFDerivWithinAt_const _ _ _

@[fun_prop]

中文:
定理 hasFDerivWithinAt_ofNat
  条件: (n : 自然数) [Of自然数 F n] (x : E) (s : Set E)
  证明: hasFDerivWithinAt_const _ _ _

@[fun_prop]

Depends on / 依赖: hasFDerivWithinAt_const
-/
theorem hasFDerivWithinAt_ofNat (n : Nat) [OfNat F n] (x : E) (s : Set E) :
    HasFDerivWithinAt (ofNat(n) : E -> F) (0 : E ->L[𝕜] F) s x :=
  hasFDerivWithinAt_const _ _ _

@[fun_prop]
/--
theorem `hasFDerivAt_const` / 定理 `hasFDerivAt_const`

English:
theorem hasFDerivAt_const
  given: (c : F) (x : E)
  statement: HasFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
  proof: hasFDerivAtFilter_const _ _

@[fun_prop]

中文:
定理 hasFDerivAt_const
  条件: (c : F) (x : E)
  结论: HasFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
  证明: hasFDerivAtFilter_const _ _

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_const
-/
theorem hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x :=
  hasFDerivAtFilter_const _ _

@[fun_prop]
/--
theorem `hasFDerivAt_zero` / 定理 `hasFDerivAt_zero`

English:
theorem hasFDerivAt_zero
  given: (x : E)
  proof: hasFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasFDerivAt_zero
  条件: (x : E)
  证明: hasFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: hasFDerivAt_const
-/
theorem hasFDerivAt_zero (x : E) :
    HasFDerivAt (0 : E -> F) (0 : E ->L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasFDerivAt_one` / 定理 `hasFDerivAt_one`

English:
theorem hasFDerivAt_one
  given: [One F] (x : E)
  proof: hasFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasFDerivAt_one
  条件: [One F] (x : E)
  证明: hasFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: hasFDerivAt_const
-/
theorem hasFDerivAt_one [One F] (x : E) :
    HasFDerivAt (1 : E -> F) (0 : E ->L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasFDerivAt_natCast` / 定理 `hasFDerivAt_natCast`

English:
theorem hasFDerivAt_natCast
  given: [NatCast F] (n : Nat) (x : E)
  proof: hasFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasFDerivAt_natCast
  条件: [自然数Cast F] (n : 自然数) (x : E)
  证明: hasFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: hasFDerivAt_const
-/
theorem hasFDerivAt_natCast [NatCast F] (n : Nat) (x : E) :
    HasFDerivAt (n : E -> F) (0 : E ->L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasFDerivAt_intCast` / 定理 `hasFDerivAt_intCast`

English:
theorem hasFDerivAt_intCast
  given: [IntCast F] (z : Int) (x : E)
  proof: hasFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasFDerivAt_intCast
  条件: [整数Cast F] (z : 整数) (x : E)
  证明: hasFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: hasFDerivAt_const
-/
theorem hasFDerivAt_intCast [IntCast F] (z : Int) (x : E) :
    HasFDerivAt (z : E -> F) (0 : E ->L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasFDerivAt_ofNat` / 定理 `hasFDerivAt_ofNat`

English:
theorem hasFDerivAt_ofNat
  given: (n : Nat) [OfNat F n] (x : E)
  proof: hasFDerivAt_const _ _

@[simp, fun_prop]

中文:
定理 hasFDerivAt_ofNat
  条件: (n : 自然数) [Of自然数 F n] (x : E)
  证明: hasFDerivAt_const _ _

@[simp, fun_prop]

Depends on / 依赖: hasFDerivAt_const
-/
theorem hasFDerivAt_ofNat (n : Nat) [OfNat F n] (x : E) :
    HasFDerivAt (ofNat(n) : E -> F) (0 : E ->L[𝕜] F) x := hasFDerivAt_const _ _

@[simp, fun_prop]
/--
theorem `differentiableAt_const` / 定理 `differentiableAt_const`

English:
theorem differentiableAt_const
  given: (c : F)
  statement: DifferentiableAt 𝕜 (fun _ => c) x
  proof: ⟨0, hasFDerivAt_const c x⟩

@[simp, fun_prop]

中文:
定理 differentiableAt_const
  条件: (c : F)
  结论: DifferentiableAt 𝕜 (fun _ => c) x
  证明: ⟨0, hasFDerivAt_const c x⟩

@[simp, fun_prop]

Depends on / 依赖: hasFDerivAt_const
-/
theorem differentiableAt_const (c : F) : DifferentiableAt 𝕜 (fun _ => c) x :=
  ⟨0, hasFDerivAt_const c x⟩

@[simp, fun_prop]
/--
theorem `differentiableAt_zero` / 定理 `differentiableAt_zero`

English:
theorem differentiableAt_zero
  given: (x : E)
  proof: differentiableAt_const _

@[simp, fun_prop]

中文:
定理 differentiableAt_zero
  条件: (x : E)
  证明: differentiableAt_const _

@[simp, fun_prop]

Depends on / 依赖: differentiableAt_const
-/
theorem differentiableAt_zero (x : E) :
    DifferentiableAt 𝕜 (0 : E -> F) x := differentiableAt_const _

@[simp, fun_prop]
/--
theorem `differentiableAt_one` / 定理 `differentiableAt_one`

English:
theorem differentiableAt_one
  given: [One F] (x : E)
  proof: differentiableAt_const _

@[simp, fun_prop]

中文:
定理 differentiableAt_one
  条件: [One F] (x : E)
  证明: differentiableAt_const _

@[simp, fun_prop]

Depends on / 依赖: differentiableAt_const
-/
theorem differentiableAt_one [One F] (x : E) :
    DifferentiableAt 𝕜 (1 : E -> F) x := differentiableAt_const _

@[simp, fun_prop]
/--
theorem `differentiableAt_natCast` / 定理 `differentiableAt_natCast`

English:
theorem differentiableAt_natCast
  given: [NatCast F] (n : Nat) (x : E)
  proof: differentiableAt_const _

@[simp, fun_prop]

中文:
定理 differentiableAt_natCast
  条件: [自然数Cast F] (n : 自然数) (x : E)
  证明: differentiableAt_const _

@[simp, fun_prop]

Depends on / 依赖: differentiableAt_const
-/
theorem differentiableAt_natCast [NatCast F] (n : Nat) (x : E) :
    DifferentiableAt 𝕜 (n : E -> F) x := differentiableAt_const _

@[simp, fun_prop]
/--
theorem `differentiableAt_intCast` / 定理 `differentiableAt_intCast`

English:
theorem differentiableAt_intCast
  given: [IntCast F] (z : Int) (x : E)
  proof: differentiableAt_const _

@[simp low, fun_prop]

中文:
定理 differentiableAt_intCast
  条件: [整数Cast F] (z : 整数) (x : E)
  证明: differentiableAt_const _

@[simp low, fun_prop]

Depends on / 依赖: differentiableAt_const
-/
theorem differentiableAt_intCast [IntCast F] (z : Int) (x : E) :
    DifferentiableAt 𝕜 (z : E -> F) x := differentiableAt_const _

@[simp low, fun_prop]
/--
theorem `differentiableAt_ofNat` / 定理 `differentiableAt_ofNat`

English:
theorem differentiableAt_ofNat
  given: (n : Nat) [OfNat F n] (x : E)
  proof: differentiableAt_const _

@[fun_prop]

中文:
定理 differentiableAt_ofNat
  条件: (n : 自然数) [Of自然数 F n] (x : E)
  证明: differentiableAt_const _

@[fun_prop]

Depends on / 依赖: differentiableAt_const
-/
theorem differentiableAt_ofNat (n : Nat) [OfNat F n] (x : E) :
    DifferentiableAt 𝕜 (ofNat(n) : E -> F) x := differentiableAt_const _

@[fun_prop]
/--
theorem `differentiableWithinAt_const` / 定理 `differentiableWithinAt_const`

English:
theorem differentiableWithinAt_const
  given: (c : F)
  statement: DifferentiableWithinAt 𝕜 (fun _ => c) s x
  proof: DifferentiableAt.differentiableWithinAt (differentiableAt_const _)

@[fun_prop]

中文:
定理 differentiableWithinAt_const
  条件: (c : F)
  结论: DifferentiableWithinAt 𝕜 (fun _ => c) s x
  证明: DifferentiableAt.differentiableWithinAt (differentiableAt_const _)

@[fun_prop]

Depends on / 依赖: DifferentiableAt, DifferentiableAt.differentiableWithinAt, differentiableAt_const, differentiableWithinAt
-/
theorem differentiableWithinAt_const (c : F) : DifferentiableWithinAt 𝕜 (fun _ => c) s x :=
  DifferentiableAt.differentiableWithinAt (differentiableAt_const _)

@[fun_prop]
/--
theorem `differentiableWithinAt_zero` / 定理 `differentiableWithinAt_zero`

English:
theorem differentiableWithinAt_zero
  proof: differentiableWithinAt_const _

@[fun_prop]

中文:
定理 differentiableWithinAt_zero
  证明: differentiableWithinAt_const _

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_const
-/
theorem differentiableWithinAt_zero :
    DifferentiableWithinAt 𝕜 (0 : E -> F) s x := differentiableWithinAt_const _

@[fun_prop]
/--
theorem `differentiableWithinAt_one` / 定理 `differentiableWithinAt_one`

English:
theorem differentiableWithinAt_one
  given: [One F]
  proof: differentiableWithinAt_const _

@[fun_prop]

中文:
定理 differentiableWithinAt_one
  条件: [One F]
  证明: differentiableWithinAt_const _

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_const
-/
theorem differentiableWithinAt_one [One F] :
    DifferentiableWithinAt 𝕜 (1 : E -> F) s x := differentiableWithinAt_const _

@[fun_prop]
/--
theorem `differentiableWithinAt_natCast` / 定理 `differentiableWithinAt_natCast`

English:
theorem differentiableWithinAt_natCast
  given: [NatCast F] (n : Nat)
  proof: differentiableWithinAt_const _

@[fun_prop]

中文:
定理 differentiableWithinAt_natCast
  条件: [自然数Cast F] (n : 自然数)
  证明: differentiableWithinAt_const _

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_const
-/
theorem differentiableWithinAt_natCast [NatCast F] (n : Nat) :
    DifferentiableWithinAt 𝕜 (n : E -> F) s x := differentiableWithinAt_const _

@[fun_prop]
/--
theorem `differentiableWithinAt_intCast` / 定理 `differentiableWithinAt_intCast`

English:
theorem differentiableWithinAt_intCast
  given: [IntCast F] (z : Int)
  proof: differentiableWithinAt_const _

@[fun_prop]

中文:
定理 differentiableWithinAt_intCast
  条件: [整数Cast F] (z : 整数)
  证明: differentiableWithinAt_const _

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_const
-/
theorem differentiableWithinAt_intCast [IntCast F] (z : Int) :
    DifferentiableWithinAt 𝕜 (z : E -> F) s x := differentiableWithinAt_const _

@[fun_prop]
/--
theorem `differentiableWithinAt_ofNat` / 定理 `differentiableWithinAt_ofNat`

English:
theorem differentiableWithinAt_ofNat
  given: (n : Nat) [OfNat F n]
  proof: differentiableWithinAt_const _

中文:
定理 differentiableWithinAt_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  证明: differentiableWithinAt_const _

Depends on / 依赖: differentiableWithinAt_const
-/
theorem differentiableWithinAt_ofNat (n : Nat) [OfNat F n] :
    DifferentiableWithinAt 𝕜 (ofNat(n) : E -> F) s x := differentiableWithinAt_const _

/--
theorem `fderivWithin_const_apply` / 定理 `fderivWithin_const_apply`

English:
theorem fderivWithin_const_apply
  given: (c : F)
  statement: fderivWithin 𝕜 (fun _ => c) s x = 0
  proof: by
  rw [fderivWithin]; rw [if_pos]
  apply hasFDerivWithinAt_const

@[simp]

中文:
定理 fderivWithin_const_apply
  条件: (c : F)
  结论: fderivWithin 𝕜 (fun _ => c) s x = 0
  证明: by
  rw [fderivWithin]; rw [if_pos]
  apply hasFDerivWithinAt_const

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt_const, if_pos
-/
theorem fderivWithin_const_apply (c : F) : fderivWithin 𝕜 (fun _ => c) s x = 0 := by
  rw [fderivWithin]; rw [if_pos]
  apply hasFDerivWithinAt_const

@[simp]
/--
theorem `fderivWithin_fun_const` / 定理 `fderivWithin_fun_const`

English:
theorem fderivWithin_fun_const
  given: (c : F)
  statement: fderivWithin 𝕜 (fun _ => c) s = 0
  proof: by
  ext
  rw [fderivWithin_const_apply]; rw [Pi.zero_apply]

@[simp]

中文:
定理 fderivWithin_fun_const
  条件: (c : F)
  结论: fderivWithin 𝕜 (fun _ => c) s = 0
  证明: by
  ext
  rw [fderivWithin_const_apply]; rw [Pi.zero_apply]

@[simp]

Depends on / 依赖: Pi.zero_apply, fderivWithin_const_apply, zero_apply
-/
theorem fderivWithin_fun_const (c : F) : fderivWithin 𝕜 (fun _ => c) s = 0 := by
  ext
  rw [fderivWithin_const_apply]; rw [Pi.zero_apply]

@[simp]
/--
theorem `fderivWithin_const` / 定理 `fderivWithin_const`

English:
theorem fderivWithin_const
  given: (c : F)
  statement: fderivWithin 𝕜 (Function.const E c) s = 0
  proof: fderivWithin_fun_const c

@[simp]

中文:
定理 fderivWithin_const
  条件: (c : F)
  结论: fderivWithin 𝕜 (Function.const E c) s = 0
  证明: fderivWithin_fun_const c

@[simp]

Depends on / 依赖: fderivWithin_fun_const
-/
theorem fderivWithin_const (c : F) : fderivWithin 𝕜 (Function.const E c) s = 0 :=
  fderivWithin_fun_const c

@[simp]
/--
theorem `fderivWithin_zero` / 定理 `fderivWithin_zero`

English:
theorem fderivWithin_zero
  statement: fderivWithin 𝕜 (0 : E -> F) s = 0
  proof: fderivWithin_const _

@[simp]

中文:
定理 fderivWithin_zero
  结论: fderivWithin 𝕜 (0 : E -> F) s = 0
  证明: fderivWithin_const _

@[simp]

Depends on / 依赖: fderivWithin_const
-/
theorem fderivWithin_zero : fderivWithin 𝕜 (0 : E -> F) s = 0 := fderivWithin_const _

@[simp]
/--
theorem `fderivWithin_one` / 定理 `fderivWithin_one`

English:
theorem fderivWithin_one
  given: [One F]
  statement: fderivWithin 𝕜 (1 : E -> F) s = 0
  proof: fderivWithin_const _

@[simp]

中文:
定理 fderivWithin_one
  条件: [One F]
  结论: fderivWithin 𝕜 (1 : E -> F) s = 0
  证明: fderivWithin_const _

@[simp]

Depends on / 依赖: fderivWithin_const
-/
theorem fderivWithin_one [One F] : fderivWithin 𝕜 (1 : E -> F) s = 0 := fderivWithin_const _

@[simp]
/--
theorem `fderivWithin_natCast` / 定理 `fderivWithin_natCast`

English:
theorem fderivWithin_natCast
  given: [NatCast F] (n : Nat)
  statement: fderivWithin 𝕜 (n : E -> F) s = 0
  proof: fderivWithin_const _

@[simp]

中文:
定理 fderivWithin_natCast
  条件: [自然数Cast F] (n : 自然数)
  结论: fderivWithin 𝕜 (n : E -> F) s = 0
  证明: fderivWithin_const _

@[simp]

Depends on / 依赖: fderivWithin_const
-/
theorem fderivWithin_natCast [NatCast F] (n : Nat) : fderivWithin 𝕜 (n : E -> F) s = 0 :=
  fderivWithin_const _

@[simp]
/--
theorem `fderivWithin_intCast` / 定理 `fderivWithin_intCast`

English:
theorem fderivWithin_intCast
  given: [IntCast F] (z : Int)
  statement: fderivWithin 𝕜 (z : E -> F) s = 0
  proof: fderivWithin_const _

@[simp low]

中文:
定理 fderivWithin_intCast
  条件: [整数Cast F] (z : 整数)
  结论: fderivWithin 𝕜 (z : E -> F) s = 0
  证明: fderivWithin_const _

@[simp low]

Depends on / 依赖: fderivWithin_const
-/
theorem fderivWithin_intCast [IntCast F] (z : Int) : fderivWithin 𝕜 (z : E -> F) s = 0 :=
  fderivWithin_const _

@[simp low]
/--
theorem `fderivWithin_ofNat` / 定理 `fderivWithin_ofNat`

English:
theorem fderivWithin_ofNat
  given: (n : Nat) [OfNat F n]
  statement: fderivWithin 𝕜 (ofNat(n) : E -> F) s = 0
  proof: fderivWithin_const _

中文:
定理 fderivWithin_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  结论: fderivWithin 𝕜 (of自然数(n) : E -> F) s = 0
  证明: fderivWithin_const _

Depends on / 依赖: fderivWithin_const
-/
theorem fderivWithin_ofNat (n : Nat) [OfNat F n] : fderivWithin 𝕜 (ofNat(n) : E -> F) s = 0 :=
  fderivWithin_const _

/--
theorem `fderiv_const_apply` / 定理 `fderiv_const_apply`

English:
theorem fderiv_const_apply
  given: (c : F)
  statement: fderiv 𝕜 (fun _ => c) x = 0
  proof: by
  rw [fderiv]; rw [fderivWithin_const_apply]

@[simp]

中文:
定理 fderiv_const_apply
  条件: (c : F)
  结论: fderiv 𝕜 (fun _ => c) x = 0
  证明: by
  rw [fderiv]; rw [fderivWithin_const_apply]

@[simp]

Depends on / 依赖: fderiv, fderivWithin_const_apply
-/
theorem fderiv_const_apply (c : F) : fderiv 𝕜 (fun _ => c) x = 0 := by
  rw [fderiv]; rw [fderivWithin_const_apply]

@[simp]
/--
theorem `fderiv_fun_const` / 定理 `fderiv_fun_const`

English:
theorem fderiv_fun_const
  given: (c : F)
  statement: fderiv 𝕜 (fun _ : E => c) = 0
  proof: by
  rw [← fderivWithin_univ]; rw [fderivWithin_fun_const]

@[simp]

中文:
定理 fderiv_fun_const
  条件: (c : F)
  结论: fderiv 𝕜 (fun _ : E => c) = 0
  证明: by
  rw [← fderivWithin_univ]; rw [fderivWithin_fun_const]

@[simp]

Depends on / 依赖: fderivWithin_fun_const, fderivWithin_univ
-/
theorem fderiv_fun_const (c : F) : fderiv 𝕜 (fun _ : E => c) = 0 := by
  rw [← fderivWithin_univ]; rw [fderivWithin_fun_const]

@[simp]
/--
theorem `fderiv_const` / 定理 `fderiv_const`

English:
theorem fderiv_const
  given: (c : F)
  statement: fderiv 𝕜 (Function.const E c) = 0
  proof: fderiv_fun_const c

@[simp]

中文:
定理 fderiv_const
  条件: (c : F)
  结论: fderiv 𝕜 (Function.const E c) = 0
  证明: fderiv_fun_const c

@[simp]

Depends on / 依赖: fderiv_fun_const
-/
theorem fderiv_const (c : F) : fderiv 𝕜 (Function.const E c) = 0 :=
  fderiv_fun_const c

@[simp]
/--
theorem `fderiv_zero` / 定理 `fderiv_zero`

English:
theorem fderiv_zero
  statement: fderiv 𝕜 (0 : E -> F) = 0
  proof: fderiv_const _

@[simp]

中文:
定理 fderiv_zero
  结论: fderiv 𝕜 (0 : E -> F) = 0
  证明: fderiv_const _

@[simp]

Depends on / 依赖: fderiv_const
-/
theorem fderiv_zero : fderiv 𝕜 (0 : E -> F) = 0 := fderiv_const _

@[simp]
/--
theorem `fderiv_one` / 定理 `fderiv_one`

English:
theorem fderiv_one
  given: [One F]
  statement: fderiv 𝕜 (1 : E -> F) = 0
  proof: fderiv_const _

@[simp]

中文:
定理 fderiv_one
  条件: [One F]
  结论: fderiv 𝕜 (1 : E -> F) = 0
  证明: fderiv_const _

@[simp]

Depends on / 依赖: fderiv_const
-/
theorem fderiv_one [One F] : fderiv 𝕜 (1 : E -> F) = 0 := fderiv_const _

@[simp]
/--
theorem `fderiv_natCast` / 定理 `fderiv_natCast`

English:
theorem fderiv_natCast
  given: [NatCast F] (n : Nat)
  statement: fderiv 𝕜 (n : E -> F) = 0
  proof: fderiv_const _

@[simp]

中文:
定理 fderiv_natCast
  条件: [自然数Cast F] (n : 自然数)
  结论: fderiv 𝕜 (n : E -> F) = 0
  证明: fderiv_const _

@[simp]

Depends on / 依赖: fderiv_const
-/
theorem fderiv_natCast [NatCast F] (n : Nat) : fderiv 𝕜 (n : E -> F) = 0 := fderiv_const _

@[simp]
/--
theorem `fderiv_intCast` / 定理 `fderiv_intCast`

English:
theorem fderiv_intCast
  given: [IntCast F] (z : Int)
  statement: fderiv 𝕜 (z : E -> F) = 0
  proof: fderiv_const _

@[simp low]

中文:
定理 fderiv_intCast
  条件: [整数Cast F] (z : 整数)
  结论: fderiv 𝕜 (z : E -> F) = 0
  证明: fderiv_const _

@[simp low]

Depends on / 依赖: fderiv_const
-/
theorem fderiv_intCast [IntCast F] (z : Int) : fderiv 𝕜 (z : E -> F) = 0 := fderiv_const _

@[simp low]
/--
theorem `fderiv_ofNat` / 定理 `fderiv_ofNat`

English:
theorem fderiv_ofNat
  given: (n : Nat) [OfNat F n]
  statement: fderiv 𝕜 (ofNat(n) : E -> F) = 0
  proof: fderiv_const _

@[simp, fun_prop]

中文:
定理 fderiv_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  结论: fderiv 𝕜 (of自然数(n) : E -> F) = 0
  证明: fderiv_const _

@[simp, fun_prop]

Depends on / 依赖: fderiv_const
-/
theorem fderiv_ofNat (n : Nat) [OfNat F n] : fderiv 𝕜 (ofNat(n) : E -> F) = 0 := fderiv_const _

@[simp, fun_prop]
/--
theorem `differentiable_const` / 定理 `differentiable_const`

English:
theorem differentiable_const
  given: (c : F)
  statement: Differentiable 𝕜 fun _ : E => c
  proof: fun _ =>
  differentiableAt_const _

@[simp, fun_prop]

中文:
定理 differentiable_const
  条件: (c : F)
  结论: Differentiable 𝕜 fun _ : E => c
  证明: fun _ =>
  differentiableAt_const _

@[simp, fun_prop]
-/
theorem differentiable_const (c : F) : Differentiable 𝕜 fun _ : E => c := fun _ =>
  differentiableAt_const _

@[simp, fun_prop]
/--
theorem `differentiable_zero` / 定理 `differentiable_zero`

English:
theorem differentiable_zero
  proof: differentiable_const _

@[simp, fun_prop]

中文:
定理 differentiable_zero
  证明: differentiable_const _

@[simp, fun_prop]

Depends on / 依赖: differentiable_const
-/
theorem differentiable_zero :
    Differentiable 𝕜 (0 : E -> F) := differentiable_const _

@[simp, fun_prop]
/--
theorem `differentiable_one` / 定理 `differentiable_one`

English:
theorem differentiable_one
  given: [One F]
  proof: differentiable_const _

@[simp, fun_prop]

中文:
定理 differentiable_one
  条件: [One F]
  证明: differentiable_const _

@[simp, fun_prop]

Depends on / 依赖: differentiable_const
-/
theorem differentiable_one [One F] :
    Differentiable 𝕜 (1 : E -> F) := differentiable_const _

@[simp, fun_prop]
/--
theorem `differentiable_natCast` / 定理 `differentiable_natCast`

English:
theorem differentiable_natCast
  given: [NatCast F] (n : Nat)
  proof: differentiable_const _

@[simp, fun_prop]

中文:
定理 differentiable_natCast
  条件: [自然数Cast F] (n : 自然数)
  证明: differentiable_const _

@[simp, fun_prop]

Depends on / 依赖: differentiable_const
-/
theorem differentiable_natCast [NatCast F] (n : Nat) :
    Differentiable 𝕜 (n : E -> F) := differentiable_const _

@[simp, fun_prop]
/--
theorem `differentiable_intCast` / 定理 `differentiable_intCast`

English:
theorem differentiable_intCast
  given: [IntCast F] (z : Int)
  proof: differentiable_const _

@[simp low, fun_prop]

中文:
定理 differentiable_intCast
  条件: [整数Cast F] (z : 整数)
  证明: differentiable_const _

@[simp low, fun_prop]

Depends on / 依赖: differentiable_const
-/
theorem differentiable_intCast [IntCast F] (z : Int) :
    Differentiable 𝕜 (z : E -> F) := differentiable_const _

@[simp low, fun_prop]
/--
theorem `differentiable_ofNat` / 定理 `differentiable_ofNat`

English:
theorem differentiable_ofNat
  given: (n : Nat) [OfNat F n]
  proof: differentiable_const _

@[simp, fun_prop]

中文:
定理 differentiable_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  证明: differentiable_const _

@[simp, fun_prop]

Depends on / 依赖: differentiable_const
-/
theorem differentiable_ofNat (n : Nat) [OfNat F n] :
    Differentiable 𝕜 (ofNat(n) : E -> F) := differentiable_const _

@[simp, fun_prop]
/--
theorem `differentiableOn_const` / 定理 `differentiableOn_const`

English:
theorem differentiableOn_const
  given: (c : F)
  statement: DifferentiableOn 𝕜 (fun _ => c) s
  proof: (differentiable_const _).differentiableOn

@[simp, fun_prop]

中文:
定理 differentiableOn_const
  条件: (c : F)
  结论: DifferentiableOn 𝕜 (fun _ => c) s
  证明: (differentiable_const _).differentiableOn

@[simp, fun_prop]

Depends on / 依赖: differentiableOn, differentiable_const
-/
theorem differentiableOn_const (c : F) : DifferentiableOn 𝕜 (fun _ => c) s :=
  (differentiable_const _).differentiableOn

@[simp, fun_prop]
/--
theorem `differentiableOn_zero` / 定理 `differentiableOn_zero`

English:
theorem differentiableOn_zero
  proof: differentiableOn_const _

@[simp, fun_prop]

中文:
定理 differentiableOn_zero
  证明: differentiableOn_const _

@[simp, fun_prop]

Depends on / 依赖: differentiableOn_const
-/
theorem differentiableOn_zero :
    DifferentiableOn 𝕜 (0 : E -> F) s := differentiableOn_const _

@[simp, fun_prop]
/--
theorem `differentiableOn_one` / 定理 `differentiableOn_one`

English:
theorem differentiableOn_one
  given: [One F]
  proof: differentiableOn_const _

@[simp, fun_prop]

中文:
定理 differentiableOn_one
  条件: [One F]
  证明: differentiableOn_const _

@[simp, fun_prop]

Depends on / 依赖: differentiableOn_const
-/
theorem differentiableOn_one [One F] :
    DifferentiableOn 𝕜 (1 : E -> F) s := differentiableOn_const _

@[simp, fun_prop]
/--
theorem `differentiableOn_natCast` / 定理 `differentiableOn_natCast`

English:
theorem differentiableOn_natCast
  given: [NatCast F] (n : Nat)
  proof: differentiableOn_const _

@[simp, fun_prop]

中文:
定理 differentiableOn_natCast
  条件: [自然数Cast F] (n : 自然数)
  证明: differentiableOn_const _

@[simp, fun_prop]

Depends on / 依赖: differentiableOn_const
-/
theorem differentiableOn_natCast [NatCast F] (n : Nat) :
    DifferentiableOn 𝕜 (n : E -> F) s := differentiableOn_const _

@[simp, fun_prop]
/--
theorem `differentiableOn_intCast` / 定理 `differentiableOn_intCast`

English:
theorem differentiableOn_intCast
  given: [IntCast F] (z : Int)
  proof: differentiableOn_const _

@[simp low, fun_prop]

中文:
定理 differentiableOn_intCast
  条件: [整数Cast F] (z : 整数)
  证明: differentiableOn_const _

@[simp low, fun_prop]

Depends on / 依赖: differentiableOn_const
-/
theorem differentiableOn_intCast [IntCast F] (z : Int) :
    DifferentiableOn 𝕜 (z : E -> F) s := differentiableOn_const _

@[simp low, fun_prop]
/--
theorem `differentiableOn_ofNat` / 定理 `differentiableOn_ofNat`

English:
theorem differentiableOn_ofNat
  given: (n : Nat) [OfNat F n]
  proof: differentiableOn_const _

@[fun_prop]

中文:
定理 differentiableOn_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  证明: differentiableOn_const _

@[fun_prop]

Depends on / 依赖: differentiableOn_const
-/
theorem differentiableOn_ofNat (n : Nat) [OfNat F n] :
    DifferentiableOn 𝕜 (ofNat(n) : E -> F) s := differentiableOn_const _

@[fun_prop]
/--
theorem `hasFDerivWithinAt_singleton` / 定理 `hasFDerivWithinAt_singleton`

English:
theorem hasFDerivWithinAt_singleton
  given: (f : E -> F) (x : E)
  proof: by
  refine .of_not_accPt ?_
  rw [accPt_iff_clusterPt]; rw [inf_principal]
  simp [ClusterPt]

@[fun_prop, nontriviality]

中文:
定理 hasFDerivWithinAt_singleton
  条件: (f : E -> F) (x : E)
  证明: by
  refine .of_not_accPt ?_
  rw [accPt_iff_clusterPt]; rw [inf_principal]
  simp [ClusterPt]

@[fun_prop, nontriviality]

Depends on / 依赖: ClusterPt, accPt_iff_clusterPt, inf_principal, of_not_accPt
-/
theorem hasFDerivWithinAt_singleton (f : E -> F) (x : E) :
    HasFDerivWithinAt f (0 : E ->L[𝕜] F) {x} x := by
  refine .of_not_accPt ?_
  rw [accPt_iff_clusterPt]; rw [inf_principal]
  simp [ClusterPt]

@[fun_prop, nontriviality]
/--
theorem `hasFDerivWithinAt_of_subsingleton` / 定理 `hasFDerivWithinAt_of_subsingleton`

English:
theorem hasFDerivWithinAt_of_subsingleton
  given: [h : Subsingleton E] (f : E -> F) (s : Set E) (x : E)
  proof: by
  obtain rfl | ⟨a, rfl⟩ := s.eq_empty_or_singleton_of_subsingleton
  · simp
  · exact HasFDerivWithinAt.singleton

@[fun_prop, nontriviality]

中文:
定理 hasFDerivWithinAt_of_subsingleton
  条件: [h : Subsingleton E] (f : E -> F) (s : Set E) (x : E)
  证明: by
  obtain rfl | ⟨a, rfl⟩ := s.eq_empty_or_singleton_of_subsingleton
  · simp
  · exact HasFDerivWithinAt.singleton

@[fun_prop, nontriviality]

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.singleton, eq_empty_or_singleton_of_subsingleton, s.eq_empty_or_singleton_of_subsingleton, singleton
-/
theorem hasFDerivWithinAt_of_subsingleton [h : Subsingleton E] (f : E -> F) (s : Set E) (x : E) :
    HasFDerivWithinAt f (0 : E ->L[𝕜] F) s x := by
  obtain rfl | ⟨a, rfl⟩ := s.eq_empty_or_singleton_of_subsingleton
  · simp
  · exact HasFDerivWithinAt.singleton

@[fun_prop, nontriviality]
/--
theorem `hasFDerivAt_of_subsingleton` / 定理 `hasFDerivAt_of_subsingleton`

English:
theorem hasFDerivAt_of_subsingleton
  given: [h : Subsingleton E] (f : E -> F) (x : E)
  proof: by
  rw [← hasFDerivWithinAt_univ]; rw [subsingleton_univ.eq_singleton_of_mem (mem_univ x)]
  exact hasFDerivWithinAt_singleton f x

@[nontriviality]

中文:
定理 hasFDerivAt_of_subsingleton
  条件: [h : Subsingleton E] (f : E -> F) (x : E)
  证明: by
  rw [← hasFDerivWithinAt_univ]; rw [subsingleton_univ.eq_singleton_of_mem (mem_univ x)]
  exact hasFDerivWithinAt_singleton f x

@[nontriviality]

Depends on / 依赖: eq_singleton_of_mem, hasFDerivWithinAt_singleton, hasFDerivWithinAt_univ, mem_univ, subsingleton_univ, subsingleton_univ.eq_singleton_of_mem
-/
theorem hasFDerivAt_of_subsingleton [h : Subsingleton E] (f : E -> F) (x : E) :
    HasFDerivAt f (0 : E ->L[𝕜] F) x := by
  rw [← hasFDerivWithinAt_univ]; rw [subsingleton_univ.eq_singleton_of_mem (mem_univ x)]
  exact hasFDerivWithinAt_singleton f x

@[nontriviality]
/--
theorem `differentiable_of_subsingleton` / 定理 `differentiable_of_subsingleton`

English:
theorem differentiable_of_subsingleton
  given: [Subsingleton E] {f : E -> F}
  statement: Differentiable 𝕜 f
  proof: fun x => (hasFDerivAt_of_subsingleton f x (𝕜 := 𝕜)).differentiableAt

@[nontriviality]

中文:
定理 differentiable_of_subsingleton
  条件: [Subsingleton E] {f : E -> F}
  结论: Differentiable 𝕜 f
  证明: fun x => (hasFDerivAt_of_subsingleton f x (𝕜 := 𝕜)).differentiableAt

@[nontriviality]

Depends on / 依赖: differentiableAt, hasFDerivAt_of_subsingleton
-/
theorem differentiable_of_subsingleton [Subsingleton E] {f : E -> F} : Differentiable 𝕜 f :=
  fun x => (hasFDerivAt_of_subsingleton f x (𝕜 := 𝕜)).differentiableAt

@[nontriviality]
/--
theorem `differentiableWithinAt_of_subsingleton` / 定理 `differentiableWithinAt_of_subsingleton`

English:
theorem differentiableWithinAt_of_subsingleton
  given: [Subsingleton E]
  proof: (differentiable_of_subsingleton x).differentiableWithinAt

@[fun_prop]

中文:
定理 differentiableWithinAt_of_subsingleton
  条件: [Subsingleton E]
  证明: (differentiable_of_subsingleton x).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableWithinAt, differentiable_of_subsingleton
-/
theorem differentiableWithinAt_of_subsingleton [Subsingleton E] :
    DifferentiableWithinAt 𝕜 f s x :=
  (differentiable_of_subsingleton x).differentiableWithinAt

@[fun_prop]
/--
theorem `differentiableOn_singleton` / 定理 `differentiableOn_singleton`

English:
theorem differentiableOn_singleton
  statement: DifferentiableOn 𝕜 f {x}
  proof: forall_eq.2 (hasFDerivWithinAt_singleton f x).differentiableWithinAt

@[fun_prop]

中文:
定理 differentiableOn_singleton
  结论: DifferentiableOn 𝕜 f {x}
  证明: forall_eq.2 (hasFDerivWithinAt_singleton f x).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableWithinAt, forall_eq, hasFDerivWithinAt_singleton
-/
theorem differentiableOn_singleton : DifferentiableOn 𝕜 f {x} :=
  forall_eq.2 (hasFDerivWithinAt_singleton f x).differentiableWithinAt

@[fun_prop]
/--
theorem `Set.Subsingleton.differentiableOn` / 定理 `Set.Subsingleton.differentiableOn`

English:
theorem Set.Subsingleton.differentiableOn
  given: (hs : s.Subsingleton)
  statement: DifferentiableOn 𝕜 f s
  proof: hs.induction_on differentiableOn_empty fun _ => differentiableOn_singleton

中文:
定理 Set.Subsingleton.differentiableOn
  条件: (hs : s.Subsingleton)
  结论: DifferentiableOn 𝕜 f s
  证明: hs.induction_on differentiableOn_empty fun _ => differentiableOn_singleton

Depends on / 依赖: differentiableOn_empty, differentiableOn_singleton, hs.induction_on, induction_on
-/
theorem Set.Subsingleton.differentiableOn (hs : s.Subsingleton) : DifferentiableOn 𝕜 f s :=
  hs.induction_on differentiableOn_empty fun _ => differentiableOn_singleton

/--
theorem `hasFDerivAt_zero_of_eventually_const` / 定理 `hasFDerivAt_zero_of_eventually_const`

English:
theorem hasFDerivAt_zero_of_eventually_const
  given: (c : F) (hf : f =ᶠ[𝓝 x] fun _ => c)
  proof: (hasFDerivAt_const _ _).congr_of_eventuallyEq hf

中文:
定理 hasFDerivAt_zero_of_eventually_const
  条件: (c : F) (hf : f =ᶠ[𝓝 x] fun _ => c)
  证明: (hasFDerivAt_const _ _).congr_of_eventuallyEq hf

Depends on / 依赖: congr_of_eventuallyEq, hasFDerivAt_const
-/
theorem hasFDerivAt_zero_of_eventually_const (c : F) (hf : f =ᶠ[𝓝 x] fun _ => c) :
    HasFDerivAt f (0 : E ->L[𝕜] F) x :=
  (hasFDerivAt_const _ _).congr_of_eventuallyEq hf

end Const

/--
lemma `differentiableWithinAt_of_fderivWithin_injective` / 引理 `differentiableWithinAt_of_fderivWithin_injective`

English:
lemma differentiableWithinAt_of_fderivWithin_injective
  given: (hf : Injective (fderivWithin 𝕜 f s x))
  proof: by
  nontriviality E
  contrapose hf
  rw [fderivWithin_zero_of_not_differentiableWithinAt hf]
  exact not_injective_const

中文:
引理 differentiableWithinAt_of_fderivWithin_injective
  条件: (hf : Injective (fderivWithin 𝕜 f s x))
  证明: by
  nontriviality E
  contrapose hf
  rw [fderivWithin_zero_of_not_differentiableWithinAt hf]
  exact not_injective_const

Depends on / 依赖: contrapose, fderivWithin_zero_of_not_differentiableWithinAt, nontriviality, not_injective_const
-/
lemma differentiableWithinAt_of_fderivWithin_injective (hf : Injective (fderivWithin 𝕜 f s x)) :
    DifferentiableWithinAt 𝕜 f s x := by
  nontriviality E
  contrapose hf
  rw [fderivWithin_zero_of_not_differentiableWithinAt hf]
  exact not_injective_const

/--
lemma `differentiableAt_of_fderiv_injective` / 引理 `differentiableAt_of_fderiv_injective`

English:
lemma differentiableAt_of_fderiv_injective
  given: (hf : Injective (fderiv 𝕜 f x))
  proof: by
  simp only [← differentiableWithinAt_univ, ← fderivWithin_univ] at hf ⊢
  exact differentiableWithinAt_of_fderivWithin_injective hf

中文:
引理 differentiableAt_of_fderiv_injective
  条件: (hf : Injective (fderiv 𝕜 f x))
  证明: by
  simp only [← differentiableWithinAt_univ, ← fderivWithin_univ] at hf ⊢
  exact differentiableWithinAt_of_fderivWithin_injective hf

Depends on / 依赖: differentiableWithinAt_of_fderivWithin_injective, differentiableWithinAt_univ, fderivWithin_univ
-/
lemma differentiableAt_of_fderiv_injective (hf : Injective (fderiv 𝕜 f x)) :
    DifferentiableAt 𝕜 f x := by
  simp only [← differentiableWithinAt_univ, ← fderivWithin_univ] at hf ⊢
  exact differentiableWithinAt_of_fderivWithin_injective hf

/--
theorem `differentiableWithinAt_of_isInvertible_fderivWithin` / 定理 `differentiableWithinAt_of_isInvertible_fderivWithin`

English:
theorem differentiableWithinAt_of_isInvertible_fderivWithin
  proof: differentiableWithinAt_of_fderivWithin_injective hf.injective

中文:
定理 differentiableWithinAt_of_isInvertible_fderivWithin
  证明: differentiableWithinAt_of_fderivWithin_injective hf.injective

Depends on / 依赖: differentiableWithinAt_of_fderivWithin_injective, hf.injective, injective
-/
theorem differentiableWithinAt_of_isInvertible_fderivWithin
    (hf : (fderivWithin 𝕜 f s x).IsInvertible) : DifferentiableWithinAt 𝕜 f s x :=
  differentiableWithinAt_of_fderivWithin_injective hf.injective

/--
theorem `differentiableAt_of_isInvertible_fderiv` / 定理 `differentiableAt_of_isInvertible_fderiv`

English:
theorem differentiableAt_of_isInvertible_fderiv
  proof: differentiableAt_of_fderiv_injective hf.injective

中文:
定理 differentiableAt_of_isInvertible_fderiv
  证明: differentiableAt_of_fderiv_injective hf.injective

Depends on / 依赖: differentiableAt_of_fderiv_injective, hf.injective, injective
-/
theorem differentiableAt_of_isInvertible_fderiv
    (hf : (fderiv 𝕜 f x).IsInvertible) : DifferentiableAt 𝕜 f x :=
  differentiableAt_of_fderiv_injective hf.injective

/-! ### Support of derivatives -/

section Support
variable (𝕜)

/--
theorem `HasStrictFDerivAt.of_notMem_tsupport` / 定理 `HasStrictFDerivAt.of_notMem_tsupport`

English:
theorem HasStrictFDerivAt.of_notMem_tsupport
  given: (h : x ∉ tsupport f)
  proof: by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictFDerivAt_const (0 : F) x).congr_of_eventuallyEq h.symm

中文:
定理 HasStrictFDerivAt.of_notMem_tsupport
  条件: (h : x ∉ tsupport f)
  证明: by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictFDerivAt_const (0 : F) x).congr_of_eventuallyEq h.symm

Depends on / 依赖: congr_of_eventuallyEq, h.symm, hasStrictFDerivAt_const, notMem_tsupport_iff_eventuallyEq
-/
theorem HasStrictFDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) :
    HasStrictFDerivAt f (0 : E ->L[𝕜] F) x := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictFDerivAt_const (0 : F) x).congr_of_eventuallyEq h.symm

/--
theorem `HasFDerivAt.of_notMem_tsupport` / 定理 `HasFDerivAt.of_notMem_tsupport`

English:
theorem HasFDerivAt.of_notMem_tsupport
  given: (h : x ∉ tsupport f)
  proof: (HasStrictFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivAt

中文:
定理 HasFDerivAt.of_notMem_tsupport
  条件: (h : x ∉ tsupport f)
  证明: (HasStrictFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivAt

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.of_notMem_tsupport, hasFDerivAt, of_notMem_tsupport
-/
theorem HasFDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) :
    HasFDerivAt f (0 : E ->L[𝕜] F) x :=
  (HasStrictFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivAt

/--
theorem `HasFDerivWithinAt.of_notMem_tsupport` / 定理 `HasFDerivWithinAt.of_notMem_tsupport`

English:
theorem HasFDerivWithinAt.of_notMem_tsupport
  given: {s : Set E} {x : E} (h : x ∉ tsupport f)
  proof: (HasFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivWithinAt

中文:
定理 HasFDerivWithinAt.of_notMem_tsupport
  条件: {s : Set E} {x : E} (h : x ∉ tsupport f)
  证明: (HasFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivWithinAt

Depends on / 依赖: HasFDerivAt, HasFDerivAt.of_notMem_tsupport, hasFDerivWithinAt, of_notMem_tsupport
-/
theorem HasFDerivWithinAt.of_notMem_tsupport {s : Set E} {x : E} (h : x ∉ tsupport f) :
    HasFDerivWithinAt f (0 : E ->L[𝕜] F) s x :=
  (HasFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivWithinAt

/--
theorem `fderiv_of_notMem_tsupport` / 定理 `fderiv_of_notMem_tsupport`

English:
theorem fderiv_of_notMem_tsupport
  given: (h : x ∉ tsupport f)
  statement: fderiv 𝕜 f x = 0
  proof: by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.fderiv_eq]

中文:
定理 fderiv_of_notMem_tsupport
  条件: (h : x ∉ tsupport f)
  结论: fderiv 𝕜 f x = 0
  证明: by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.fderiv_eq]

Depends on / 依赖: fderiv_eq, h.fderiv_eq, notMem_tsupport_iff_eventuallyEq
-/
theorem fderiv_of_notMem_tsupport (h : x ∉ tsupport f) : fderiv 𝕜 f x = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.fderiv_eq]

/--
theorem `support_fderiv_subset` / 定理 `support_fderiv_subset`

English:
theorem support_fderiv_subset
  statement: support (fderiv 𝕜 f) subseteq tsupport f
  proof: fun x => by
  rw [← not_imp_not]; rw [notMem_support]
  exact fderiv_of_notMem_tsupport _

中文:
定理 support_fderiv_subset
  结论: support (fderiv 𝕜 f) subseteq tsupport f
  证明: fun x => by
  rw [← not_imp_not]; rw [notMem_support]
  exact fderiv_of_notMem_tsupport _

Depends on / 依赖: fderiv_of_notMem_tsupport, notMem_support, not_imp_not
-/
theorem support_fderiv_subset : support (fderiv 𝕜 f) subseteq tsupport f := fun x => by
  rw [← not_imp_not]; rw [notMem_support]
  exact fderiv_of_notMem_tsupport _

/--
theorem `tsupport_fderiv_subset` / 定理 `tsupport_fderiv_subset`

English:
theorem tsupport_fderiv_subset
  statement: tsupport (fderiv 𝕜 f) subseteq tsupport f
  proof: closure_minimal (support_fderiv_subset 𝕜) isClosed_closure

中文:
定理 tsupport_fderiv_subset
  结论: tsupport (fderiv 𝕜 f) subseteq tsupport f
  证明: closure_minimal (support_fderiv_subset 𝕜) isClosed_closure

Depends on / 依赖: closure_minimal, isClosed_closure, support_fderiv_subset
-/
theorem tsupport_fderiv_subset : tsupport (fderiv 𝕜 f) subseteq tsupport f :=
  closure_minimal (support_fderiv_subset 𝕜) isClosed_closure

/--
theorem `tsupport_fderiv_apply_subset` / 定理 `tsupport_fderiv_apply_subset`

English:
theorem tsupport_fderiv_apply_subset
  given: (v : E)
  statement: tsupport (fderiv 𝕜 f · v) subseteq tsupport f
  proof: (tsupport_comp_subset (g := fun L : E ->L[𝕜] F => L v) rfl _).trans (tsupport_fderiv_subset 𝕜)

中文:
定理 tsupport_fderiv_apply_subset
  条件: (v : E)
  结论: tsupport (fderiv 𝕜 f · v) subseteq tsupport f
  证明: (tsupport_comp_subset (g := fun L : E ->L[𝕜] F => L v) rfl _).trans (tsupport_fderiv_subset 𝕜)

Depends on / 依赖: tsupport_comp_subset, tsupport_fderiv_subset
-/
theorem tsupport_fderiv_apply_subset (v : E) : tsupport (fderiv 𝕜 f · v) subseteq tsupport f :=
  (tsupport_comp_subset (g := fun L : E ->L[𝕜] F => L v) rfl _).trans (tsupport_fderiv_subset 𝕜)

/--
theorem `HasCompactSupport.fderiv` / 定理 `HasCompactSupport.fderiv`

English:
theorem HasCompactSupport.fderiv
  given: (hf : HasCompactSupport f)
  proof: hf.mono' support_fderiv_subset 𝕜

中文:
定理 HasCompactSupport.fderiv
  条件: (hf : HasCompactSupport f)
  证明: hf.mono' support_fderiv_subset 𝕜
-/
protected theorem HasCompactSupport.fderiv (hf : HasCompactSupport f) :
    HasCompactSupport (fderiv 𝕜 f) :=
hf.mono' support_fderiv_subset 𝕜

/--
theorem `HasCompactSupport.fderiv_apply` / 定理 `HasCompactSupport.fderiv_apply`

English:
theorem HasCompactSupport.fderiv_apply
  given: (hf : HasCompactSupport f) (v : E)
  proof: hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset 𝕜 v)

中文:
定理 HasCompactSupport.fderiv_apply
  条件: (hf : HasCompactSupport f) (v : E)
  证明: hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset 𝕜 v)
-/
protected theorem HasCompactSupport.fderiv_apply (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (fderiv 𝕜 f · v) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset 𝕜 v)

end Support


end
