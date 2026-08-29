/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# The infinite adele ring of a number field

This file contains the formalisation of the infinite adele ring of a number field as the
finite product of completions over its infinite places.

## Main definitions

- `NumberField.InfiniteAdeleRing` of a number field `K` is defined as the product of
  the completions of `K` over its infinite places.
- `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` is the ring isomorphism between
  the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of `K`.

## Main results
- `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
  locally compact space.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

@[expose] public section

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The infinite adele ring

The infinite adele ring is the finite product of completions of a number field over its
infinite places. See `NumberField.InfinitePlace` for the definition of an infinite place and
`NumberField.InfinitePlace.Completion` for the associated completion.
-/

/--
Definition of `InfiniteAdeleRing` / `InfiniteAdeleRing` 的定义

English:
definition InfiniteAdeleRing
  signature: (K : Type*) [Field K]
  body: (v : InfinitePlace K) -> v.Completion
deriving CommRing, Inhabited, TopologicalSpace, IsTopologicalRing, Algebra K

中文:
定义 InfiniteAdeleRing
  签名: (K : 类型) [域 K]
  定义体: (v : InfinitePlace K) -> v.Completion
deriving CommRing, Inhabited, TopologicalSpace, IsTopologicalRing, Algebra K

Depends on / 依赖: Completion, InfinitePlace, v.Completion
-/
def InfiniteAdeleRing (K : Type*) [Field K] := (v : InfinitePlace K) -> v.Completion
deriving CommRing, Inhabited, TopologicalSpace, IsTopologicalRing, Algebra K

namespace InfiniteAdeleRing

/-- `K∞` is notation for `NumberField.InfiniteAdeleRing K`. -/
scoped[NumberField.AdeleRing] notation:max K "∞" => InfiniteAdeleRing K

open scoped AdeleRing

variable (K : Type*) [Field K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NumberField
  signature: K] : Nontrivial K∞
  body: (inferInstance : Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

中文:
实例 [数域
  签名: K] : 非平凡 K∞
  定义体: (inferInstance : Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

Depends on / 依赖: InfinitePlace, Nonempty, Pi.nontrivial_at, nontrivial_at
-/
instance [NumberField K] : Nontrivial K∞ :=
  (inferInstance : Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (x : K) (v : InfinitePlace K)
  statement: algebraMap K K∞ x v = x
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (x : K) (v : InfinitePlace K)
  结论: algebraMap K K∞ x v = x
  证明: rfl
-/
@[simp] theorem algebraMap_apply (x : K) (v : InfinitePlace K) : algebraMap K K∞ x v = x := rfl

/--
Instance `locallyCompactSpace` / 实例 `locallyCompactSpace`

English:
instance locallyCompactSpace
  signature: [NumberField K]
  body: Pi.locallyCompactSpace_of_finite

中文:
实例 locallyCompactSpace
  签名: [数域 K]
  定义体: Pi.locallyCompactSpace_of_finite

Depends on / 依赖: Pi.locallyCompactSpace_of_finite, locallyCompactSpace_of_finite
-/
instance locallyCompactSpace [NumberField K] : LocallyCompactSpace K∞ :=
  Pi.locallyCompactSpace_of_finite

open scoped Classical in
/--
Definition of `ringEquiv_mixedSpace` / `ringEquiv_mixedSpace` 的定义

English:
abbreviation ringEquiv_mixedSpace
  signature: : K∞ ≃+* mixedEmbedding.mixedSpace K
  body: RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.Completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.ringEquivRealOfIsReal hv))
      (RingEquiv.trans
        (RingEquiv.piCong

中文:
缩写 ringEquiv_mixedSpace
  签名: : K∞ ≃+* mixedEmbedding.mixedSpace K
  定义体: RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.Completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.ringEquivRealOfIsReal hv))
      (RingEquiv.trans
        (RingEquiv.piCong

Depends on / 依赖: Completion, Completion.ringEquivComplexOfIsComplex, Completion.ringEquivRealOfIsReal, Equiv.subtypeEquivRight, InfinitePlace, IsReal, RingEquiv, RingEquiv.piCongrLeft, RingEquiv.piCongrRight, RingEquiv.piEquivPiSubtypeProd, RingEquiv.prodCongr, RingEquiv.trans, not_isReal_iff_isComplex, piCongrLeft, piCongrRight, piEquivPiSubtypeProd, prodCongr, ringEquivComplexOfIsComplex, ringEquivRealOfIsReal, subtypeEquivRight
-/
abbrev ringEquiv_mixedSpace : K∞ ≃+* mixedEmbedding.mixedSpace K :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.Completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.ringEquivRealOfIsReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.ringEquivComplexOfIsComplex
          ((not_isReal_iff_isComplex.1 v.2))))
        (RingEquiv.piCongrLeft (fun _ => Complex) <|
          Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))

@[simp]
/--
theorem `ringEquiv_mixedSpace_apply` / 定理 `ringEquiv_mixedSpace_apply`

English:
theorem ringEquiv_mixedSpace_apply
  given: (x : K∞)
  proof: rfl

中文:
定理 ringEquiv_mixedSpace_apply
  条件: (x : K∞)
  证明: rfl
-/
theorem ringEquiv_mixedSpace_apply (x : K∞) :
    ringEquiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) => extensionEmbeddingOfIsReal v.2 (x v),
       fun (v : {w : InfinitePlace K // IsComplex w}) => extensionEmbedding v.1 (x v)) := rfl

/--
theorem `mixedEmbedding_eq_algebraMap_comp` / 定理 `mixedEmbedding_eq_algebraMap_comp`

English:
theorem mixedEmbedding_eq_algebraMap_comp
  given: {x : K}
  proof: by
  ext v <;> simp

中文:
定理 mixedEmbedding_eq_algebraMap_comp
  条件: {x : K}
  证明: by
  ext v <;> simp
-/
theorem mixedEmbedding_eq_algebraMap_comp {x : K} :
    mixedEmbedding K x = ringEquiv_mixedSpace K (algebraMap K K∞ x) := by
  ext v <;> simp

/--
theorem `denseRange_algebraMap` / 定理 `denseRange_algebraMap`

English:
theorem denseRange_algebraMap
  given: [NumberField K]
  statement: DenseRange algebraMap K K∞
  proof: (DenseRange.piMap fun v => Completion.denseRange_coe v).comp
    (InfinitePlace.denseRange_algebraMap_pi K) (.piMap fun v => Completion.continuous_coe v)

中文:
定理 denseRange_algebraMap
  条件: [数域 K]
  结论: DenseRange algebraMap K K∞
  证明: (DenseRange.piMap fun v => Completion.denseRange_coe v).comp
    (InfinitePlace.denseRange_algebraMap_pi K) (.piMap fun v => Completion.continuous_coe v)

Depends on / 依赖: Completion, Completion.continuous_coe, Completion.denseRange_coe, DenseRange, DenseRange.piMap, InfinitePlace, InfinitePlace.denseRange_algebraMap_pi, continuous_coe, denseRange_algebraMap_pi, denseRange_coe
-/
theorem denseRange_algebraMap [NumberField K] : DenseRange algebraMap K K∞ :=
  (DenseRange.piMap fun v => Completion.denseRange_coe v).comp
    (InfinitePlace.denseRange_algebraMap_pi K) (.piMap fun v => Completion.continuous_coe v)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NumberField
  signature: K] : Norm K∞ where norm x
  body: ∏ v, ‖x v‖ ^ v.mult

中文:
实例 [数域
  签名: K] : 范数 K∞ where norm x
  定义体: ∏ v, ‖x v‖ ^ v.mult

Depends on / 依赖: v.mult
-/
instance [NumberField K] : Norm K∞ where norm x := ∏ v, ‖x v‖ ^ v.mult

variable {K}

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: [NumberField K] (x : K∞)
  statement: ‖x‖ = ∏ v, ‖x v‖ ^ v.mult
  proof: rfl

中文:
定理 norm_def
  条件: [数域 K] (x : K∞)
  结论: ‖x‖ = ∏ v, ‖x v‖ ^ v.mult
  证明: rfl
-/
theorem norm_def [NumberField K] (x : K∞) : ‖x‖ = ∏ v, ‖x v‖ ^ v.mult := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `norm_eq_zero_of_not_isUnit` / 定理 `norm_eq_zero_of_not_isUnit`

English:
theorem norm_eq_zero_of_not_isUnit
  given: [NumberField K] {x : K∞} (hx : ¬IsUnit x)
  proof: by
  rw [Pi.isUnit_iff]; rw [not_forall] at hx
  obtain ⟨v, hv⟩ := hx
  exact Finset.prod_eq_zero_iff.2 ⟨v, Finset.mem_univ v, by simpa [isUnit_iff_ne_zero] using hv⟩

中文:
定理 norm_eq_zero_of_not_isUnit
  条件: [数域 K] {x : K∞} (hx : ¬是单位 x)
  证明: by
  rw [Pi.isUnit_iff]; rw [not_forall] at hx
  obtain ⟨v, hv⟩ := hx
  exact Finset.prod_eq_zero_iff.2 ⟨v, Finset.mem_univ v, by simpa [isUnit_iff_ne_zero] using hv⟩

Depends on / 依赖: Finset, Finset.mem_univ, Finset.prod_eq_zero_iff, Pi.isUnit_iff, isUnit_iff, isUnit_iff_ne_zero, mem_univ, not_forall, prod_eq_zero_iff
-/
theorem norm_eq_zero_of_not_isUnit [NumberField K] {x : K∞} (hx : ¬IsUnit x) :
    ‖x‖ = 0 := by
  rw [Pi.isUnit_iff]; rw [not_forall] at hx
  obtain ⟨v, hv⟩ := hx
  exact Finset.prod_eq_zero_iff.2 ⟨v, Finset.mem_univ v, by simpa [isUnit_iff_ne_zero] using hv⟩

/--
theorem `coe_norm_eq_abs_norm` / 定理 `coe_norm_eq_abs_norm`

English:
theorem coe_norm_eq_abs_norm
  given: [NumberField K] (x : K)
  proof: by
  simpa [-Rat.cast_abs, norm_def] using! InfinitePlace.prod_eq_abs_norm x

中文:
定理 coe_norm_eq_abs_norm
  条件: [数域 K] (x : K)
  证明: by
  simpa [-Rat.cast_abs, norm_def] using! InfinitePlace.prod_eq_abs_norm x

Depends on / 依赖: InfinitePlace, InfinitePlace.prod_eq_abs_norm, Rat.cast_abs, cast_abs, norm_def, prod_eq_abs_norm
-/
theorem coe_norm_eq_abs_norm [NumberField K] (x : K) :
    ‖algebraMap K K∞ x‖ = |Algebra.norm Rat x| := by
  simpa [-Rat.cast_abs, norm_def] using! InfinitePlace.prod_eq_abs_norm x

end InfiniteAdeleRing

end NumberField
