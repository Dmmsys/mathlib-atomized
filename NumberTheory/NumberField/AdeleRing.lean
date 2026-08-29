/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# The adele ring of a number field

This file contains the formalisation of the adele ring of a number field as the
direct product of the infinite adele ring and the finite adele ring.

## Main definitions

- `NumberField.AdeleRing K` is the adele ring of a number field `K`.
- `NumberField.AdeleRing.principalSubgroup K` is the subgroup of principal adeles `(x)ᵥ`.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
adele ring, number field
-/

@[expose] public section

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The adele ring -/

/--
Definition of `AdeleRing` / `AdeleRing` 的定义

English:
definition AdeleRing
  signature: (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  body: InfiniteAdeleRing K × FiniteAdeleRing R K
deriving CommRing, TopologicalSpace, IsTopologicalRing, Algebra K

中文:
定义 AdeleRing
  签名: (R K : 类型) [CommRing R] [IsDedekindDomain R] [Field K]
  定义体: InfiniteAdeleRing K × FiniteAdeleRing R K
deriving CommRing, TopologicalSpace, IsTopologicalRing, Algebra K

Depends on / 依赖: FiniteAdeleRing, InfiniteAdeleRing
-/
def AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] := InfiniteAdeleRing K × FiniteAdeleRing R K
deriving CommRing, TopologicalSpace, IsTopologicalRing, Algebra K

namespace AdeleRing

/-- `𝔸ᶠ[K]` is notation for `IsDedekindDomain.FiniteAdeleRing (𝓞 K) K`. -/
scoped notation:max "𝔸ᶠ[" K "]" => FiniteAdeleRing (𝓞 K) K
/-- `𝔸[R, K]` is notation for `NumberField.AdeleRing R K`. -/
scoped notation:max "𝔸[" R ", " K "]" => AdeleRing R K
/-- `𝔸[K]` is notation for `NumberField.AdeleRing (𝓞 K) K`. -/
scoped notation:max "𝔸[" K "]" => AdeleRing (𝓞 K) K

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited 𝔸[R, K]
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: Inhabited 𝔸[R, K]
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited 𝔸[R, K] := ⟨0⟩

@[simp]
/--
theorem `algebraMap_fst_apply` / 定理 `algebraMap_fst_apply`

English:
theorem algebraMap_fst_apply
  given: (x : K) (v : InfinitePlace K)
  proof: rfl

@[simp]

中文:
定理 algebraMap_fst_apply
  条件: (x : K) (v : InfinitePlace K)
  证明: rfl

@[simp]
-/
theorem algebraMap_fst_apply (x : K) (v : InfinitePlace K) :
    (algebraMap K 𝔸[R, K] x).1 v = x := rfl

@[simp]
/--
theorem `algebraMap_snd_apply` / 定理 `algebraMap_snd_apply`

English:
theorem algebraMap_snd_apply
  given: (x : K) (v : HeightOneSpectrum R)
  proof: rfl

中文:
定理 algebraMap_snd_apply
  条件: (x : K) (v : HeightOneSpectrum R)
  证明: rfl
-/
theorem algebraMap_snd_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K 𝔸[R, K] x).2 v = x := rfl

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  given: [NumberField K]
  statement: Function.Injective (algebraMap K 𝔸[R, K])
  proof: fun _ _ hxy => (algebraMap K K∞).injective (Prod.ext_iff.1 hxy).1

中文:
定理 algebraMap_injective
  条件: [NumberField K]
  结论: Function.Injective (algebraMap K 𝔸[R, K])
  证明: fun _ _ hxy => (algebraMap K K∞).injective (Prod.ext_iff.1 hxy).1

Depends on / 依赖: Prod.ext_iff, algebraMap, ext_iff, injective
-/
theorem algebraMap_injective [NumberField K] : Function.Injective (algebraMap K 𝔸[R, K]) :=
  fun _ _ hxy => (algebraMap K K∞).injective (Prod.ext_iff.1 hxy).1

/--
Definition of `principalSubgroup` / `principalSubgroup` 的定义

English:
abbreviation principalSubgroup
  signature: : AddSubgroup 𝔸[R, K]
  body: (algebraMap K 𝔸[R, K]).range.toAddSubgroup

中文:
缩写 principalSubgroup
  签名: : AddSubgroup 𝔸[R, K]
  定义体: (algebraMap K 𝔸[R, K]).range.toAddSubgroup

Depends on / 依赖: algebraMap, range.toAddSubgroup, toAddSubgroup
-/
abbrev principalSubgroup : AddSubgroup 𝔸[R, K] := (algebraMap K 𝔸[R, K]).range.toAddSubgroup

end AdeleRing

end NumberField
