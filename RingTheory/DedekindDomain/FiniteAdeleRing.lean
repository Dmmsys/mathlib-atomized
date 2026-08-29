/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-!
# The finite adèle ring of a Dedekind domain

We define the ring of finite adèles of a Dedekind domain `R`.

## Main definitions
- `IsDedekindDomain.FiniteAdeleRing` : The finite adèle ring of `R`, defined as the
  restricted product `Πʳ_v K_v`. We give this ring a `K`-algebra structure.

## Implementation notes
We are only interested on Dedekind domains of Krull dimension 1 (i.e., not fields). If `R` is a
field, its finite adèle ring is just defined to be the trivial ring.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite adèle ring, dedekind domain
-/

@[expose] public section

variable (R : Type*) [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K]

namespace IsDedekindDomain

/--
Definition of `HeightOneSpectrum.Support` / `HeightOneSpectrum.Support` 的定义

English:
definition HeightOneSpectrum.Support
  signature: (k : K)
  body: {v : HeightOneSpectrum R | 1 < v.valuation K k}

中文:
定义 高一谱.Support
  签名: (k : K)
  定义体: {v : HeightOneSpectrum R | 1 < v.valuation K k}

Depends on / 依赖: HeightOneSpectrum, v.valuation, valuation
-/
def HeightOneSpectrum.Support (k : K) : Set (HeightOneSpectrum R) :=
    {v : HeightOneSpectrum R | 1 < v.valuation K k}

/--
lemma `HeightOneSpectrum.Support.finite` / 引理 `HeightOneSpectrum.Support.finite`

English:
lemma HeightOneSpectrum.Support.finite
  given: (k : K)
  statement: (Support R k).Finite
  proof: by
  -- We write k=n/d.
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
  have hd' : d != 0 := nonZeroDivisors.ne_zero hd
  suffices {v : HeightOneSpectrum R | v.valuation K (algebraMap R K d) < 1}.Finite by
    apply Set.Finite.subset this
    intro v hv
    apply_fun v.valuation K at hk
    simp only [Valuation.map_mul, valuation_of_algebraMap] at hk
    rw [Set.mem_ofPred_eq]; rw [valuation_of_algebraMap]
    have := intValuation_le_one v n
    contrapose! this
    rw [← hk]; rw [mul_comm]
exact (lt_mul_of_one_lt_right (by simp) hv).trans_le
      mul_le_mul_of_nonneg_right this (by simp)
  simp_rw [valuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]

中文:
引理 高一谱.Support.finite
  条件: (k : K)
  结论: (Support R k).有限
  证明: by
  -- We write k=n/d.
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
  have hd' : d != 0 := nonZeroDivisors.ne_zero hd
  suffices {v : HeightOneSpectrum R | v.valuation K (algebraMap R K d) < 1}.Finite by
    apply Set.Finite.subset this
    intro v hv
    apply_fun v.valuation K at hk
    simp only [Valuation.map_mul, valuation_of_algebraMap] at hk
    rw [Set.mem_ofPred_eq]; rw [valuation_of_algebraMap]
    have := intValuation_le_one v n
    contrapose! this
    rw [← hk]; rw [mul_comm]
exact (lt_mul_of_one_lt_right (by simp) hv).trans_le
      mul_le_mul_of_nonneg_right this (by simp)
  simp_rw [valuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
-/
lemma HeightOneSpectrum.Support.finite (k : K) : (Support R k).Finite := by
  -- We write k=n/d.
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
  have hd' : d != 0 := nonZeroDivisors.ne_zero hd
  suffices {v : HeightOneSpectrum R | v.valuation K (algebraMap R K d) < 1}.Finite by
    apply Set.Finite.subset this
    intro v hv
    apply_fun v.valuation K at hk
    simp only [Valuation.map_mul, valuation_of_algebraMap] at hk
    rw [Set.mem_ofPred_eq]; rw [valuation_of_algebraMap]
    have := intValuation_le_one v n
    contrapose! this
    rw [← hk]; rw [mul_comm]
exact (lt_mul_of_one_lt_right (by simp) hv).trans_le
      mul_le_mul_of_nonneg_right this (by simp)
  simp_rw [valuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]

end IsDedekindDomain

noncomputable section

open Function Set IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

variable (K)

open scoped RestrictedProduct

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adicCompletion` with respect to `adicCompletionIntegers`. We prove that it is a commutative
ring. -/

/--
Definition of `FiniteAdeleRing` / `FiniteAdeleRing` 的定义

English:
definition FiniteAdeleRing
  signature: : Type _
  body: Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

中文:
定义 FiniteAdeleRing
  签名: : 类型 _
  定义体: Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

Depends on / 依赖: HeightOneSpectrum, adicCompletion, adicCompletionIntegers, v.adicCompletion, v.adicCompletionIntegers
-/
def FiniteAdeleRing : Type _ :=
  Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (FiniteAdeleRing R K)
  body: inferInstanceAs
CommRing Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

中文:
实例 :
  签名: 交换环 (FiniteAdeleRing R K)
  定义体: inferInstanceAs
CommRing Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
-/
instance : CommRing (FiniteAdeleRing R K) := inferInstanceAs
CommRing Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (FiniteAdeleRing R K)
  body: inferInstanceAs
TopologicalSpace Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

中文:
实例 :
  签名: 拓扑空间 (FiniteAdeleRing R K)
  定义体: inferInstanceAs
TopologicalSpace Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
-/
instance : TopologicalSpace (FiniteAdeleRing R K) := inferInstanceAs
TopologicalSpace Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DFunLike (FiniteAdeleRing R K) (HeightOneSpectrum R) (adicCompletion K)
  body: a.1
  coe_injective _ _ := Subtype.ext

中文:
实例 :
  签名: 依赖函数状 (FiniteAdeleRing R K) (高一谱 R) (adicCompletion K)
  定义体: a.1
  coe_injective _ _ := Subtype.ext
-/
instance : DFunLike (FiniteAdeleRing R K) (HeightOneSpectrum R) (adicCompletion K) where
  coe a := a.1
  coe_injective _ _ := Subtype.ext

namespace FiniteAdeleRing

/-- `𝔸ᶠ[R, K]` is notation for `IsDedekindDomain.FiniteAdeleRing R K`. -/
scoped notation:max "𝔸ᶠ[" R ", " K "]" => FiniteAdeleRing R K

/--
Definition of `algebraMap` / `algebraMap` 的定义

English:
definition algebraMap
  signature: : K ->+* 𝔸ᶠ[R, K] where
  body: ⟨fun i => k, by
    simp only [Filter.eventually_cofinite, SetLike.mem_coe, mem_adicCompletionIntegers R K,
     valuedAdicCompletion_eq_valuation', not_le]
    exact HeightOneSpectrum.Support.finite R k⟩
map_one' := Subtype.ext funext fun _ => adicCompletion.coe_one ..
map_mul' x y := Subtype.ext funext fun _ => adicCompletion.coe_mul ..
map_zero' := Subtype.ext funext fun _ => adicCompletion.coe_zero ..
map_add' x y := Subtype.ext funext fun _ => adicCompletion.coe_add ..

中文:
定义 algebraMap
  签名: : K ->+* 𝔸ᶠ[R, K] where
  定义体: ⟨fun i => k, by
    simp only [Filter.eventually_cofinite, SetLike.mem_coe, mem_adicCompletionIntegers R K,
     valuedAdicCompletion_eq_valuation', not_le]
    exact HeightOneSpectrum.Support.finite R k⟩
map_one' := Subtype.ext funext fun _ => adicCompletion.coe_one ..
map_mul' x y := Subtype.ext funext fun _ => adicCompletion.coe_mul ..
map_zero' := Subtype.ext funext fun _ => adicCompletion.coe_zero ..
map_add' x y := Subtype.ext funext fun _ => adicCompletion.coe_add ..
-/
protected def algebraMap : K ->+* 𝔸ᶠ[R, K] where
  toFun k := ⟨fun i => k, by
    simp only [Filter.eventually_cofinite, SetLike.mem_coe, mem_adicCompletionIntegers R K,
     valuedAdicCompletion_eq_valuation', not_le]
    exact HeightOneSpectrum.Support.finite R k⟩
map_one' := Subtype.ext funext fun _ => adicCompletion.coe_one ..
map_mul' x y := Subtype.ext funext fun _ => adicCompletion.coe_mul ..
map_zero' := Subtype.ext funext fun _ => adicCompletion.coe_zero ..
map_add' x y := Subtype.ext funext fun _ => adicCompletion.coe_add ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra K 𝔸ᶠ[R, K]
  body: (FiniteAdeleRing.algebraMap R K).toAlgebra

@[simp]

中文:
实例 :
  签名: 代数 K 𝔸ᶠ[R, K]
  定义体: (FiniteAdeleRing.algebraMap R K).toAlgebra

@[simp]

Depends on / 依赖: FiniteAdeleRing, FiniteAdeleRing.algebraMap, algebraMap, toAlgebra
-/
instance : Algebra K 𝔸ᶠ[R, K] := (FiniteAdeleRing.algebraMap R K).toAlgebra

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (k : K) (v : HeightOneSpectrum R)
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (k : K) (v : 高一谱 R)
  证明: rfl
-/
theorem algebraMap_apply (k : K) (v : HeightOneSpectrum R) :
    algebraMap K 𝔸ᶠ[R, K] k v = k := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R 𝔸ᶠ[R, K]
  body: Algebra.compHom _ (algebraMap R K)

中文:
实例 :
  签名: 代数 R 𝔸ᶠ[R, K]
  定义体: Algebra.compHom _ (algebraMap R K)

Depends on / 依赖: Algebra, Algebra.compHom, algebraMap, compHom
-/
instance : Algebra R 𝔸ᶠ[R, K] := Algebra.compHom _ (algebraMap R K)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R K 𝔸ᶠ[R, K]
  body: IsScalarTower.of_algebraMap_eq' rfl

中文:
实例 :
  签名: 标量塔 R K 𝔸ᶠ[R, K]
  定义体: IsScalarTower.of_algebraMap_eq' rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance : IsScalarTower R K 𝔸ᶠ[R, K] :=
  IsScalarTower.of_algebraMap_eq' rfl

variable {R} in
@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {a₁ a₂ : 𝔸ᶠ[R, K]} (h : forall v, a₁ v = a₂ v)
  statement: a₁ = a₂
  proof: Subtype.ext funext h

中文:
引理 ext
  条件: {a₁ a₂ : 𝔸ᶠ[R, K]} (h : 对任意 v, a₁ v = a₂ v)
  结论: a₁ = a₂
  证明: Subtype.ext funext h

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma ext {a₁ a₂ : 𝔸ᶠ[R, K]} (h : forall v, a₁ v = a₂ v) : a₁ = a₂ :=
Subtype.ext funext h

section Topology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalRing 𝔸ᶠ[R, K]
  body: haveI : Fact (forall v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ => Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing (fun (v : HeightOneSpectrum R) => v.adicCompletion K)

中文:
实例 :
  签名: 是拓扑环 𝔸ᶠ[R, K]
  定义体: haveI : Fact (forall v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ => Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing (fun (v : HeightOneSpectrum R) => v.adicCompletion K)

Depends on / 依赖: HeightOneSpectrum, IsOpen, RestrictedProduct, RestrictedProduct.isTopologicalRing, Valued, Valued.isOpen_valuationSubring, adicCompletion, adicCompletionIntegers, isOpen_valuationSubring, isTopologicalRing, v.adicCompletion, v.adicCompletionIntegers
-/
instance : IsTopologicalRing 𝔸ᶠ[R, K] :=
  haveI : Fact (forall v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ => Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing (fun (v : HeightOneSpectrum R) => v.adicCompletion K)

end Topology

section Units

variable {R K}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  given: {a : 𝔸ᶠ[R, K]}
  proof: by
  rw [RestrictedProduct.isUnit_iff]
  simp only [isUnit_iff_ne_zero, adicCompletionIntegers.isUnit_iff_valued_eq_one, exists_prop,
    Filter.eventually_cofinite, not_and_or, Set.ofPred_or]
  simpa using! fun _ _ => a.2

中文:
定理 isUnit_iff
  条件: {a : 𝔸ᶠ[R, K]}
  证明: by
  rw [RestrictedProduct.isUnit_iff]
  simp only [isUnit_iff_ne_zero, adicCompletionIntegers.isUnit_iff_valued_eq_one, exists_prop,
    Filter.eventually_cofinite, not_and_or, Set.ofPred_or]
  simpa using! fun _ _ => a.2

Depends on / 依赖: Filter, Filter.eventually_cofinite, RestrictedProduct, RestrictedProduct.isUnit_iff, Set.ofPred_or, adicCompletionIntegers, adicCompletionIntegers.isUnit_iff_valued_eq_one, eventually_cofinite, exists_prop, isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_valued_eq_one, not_and_or, ofPred_or
-/
theorem isUnit_iff {a : 𝔸ᶠ[R, K]} :
    IsUnit a ↔ (forall v, a v != 0) ∧ forallᶠ v in Filter.cofinite, Valued.v (a v) = 1 := by
  rw [RestrictedProduct.isUnit_iff]
  simp only [isUnit_iff_ne_zero, adicCompletionIntegers.isUnit_iff_valued_eq_one, exists_prop,
    Filter.eventually_cofinite, not_and_or, Set.ofPred_or]
  simpa using! fun _ _ => a.2

/--
theorem `unitsEquiv_finite_valued_eq_one` / 定理 `unitsEquiv_finite_valued_eq_one`

English:
theorem unitsEquiv_finite_valued_eq_one
  given: (a : 𝔸ᶠ[R, K]ˣ)
  proof: by
  filter_upwards [(RestrictedProduct.unitsEquiv _ a).2] using fun _ h =>
    adicCompletionIntegers.mem_units_iff_valued_eq_one.1 h

中文:
定理 unitsEquiv_finite_valued_eq_one
  条件: (a : 𝔸ᶠ[R, K]ˣ)
  证明: by
  filter_upwards [(RestrictedProduct.unitsEquiv _ a).2] using fun _ h =>
    adicCompletionIntegers.mem_units_iff_valued_eq_one.1 h

Depends on / 依赖: RestrictedProduct, RestrictedProduct.unitsEquiv, adicCompletionIntegers, adicCompletionIntegers.mem_units_iff_valued_eq_one, filter_upwards, mem_units_iff_valued_eq_one, unitsEquiv
-/
theorem unitsEquiv_finite_valued_eq_one (a : 𝔸ᶠ[R, K]ˣ) :
    forallᶠ v in Filter.cofinite, Valued.v (RestrictedProduct.unitsEquiv _ a v).1 = 1 := by
  filter_upwards [(RestrictedProduct.unitsEquiv _ a).2] using fun _ h =>
    adicCompletionIntegers.mem_units_iff_valued_eq_one.1 h

/--
theorem `infinite_valued_ne_one_of_not_isUnit` / 定理 `infinite_valued_ne_one_of_not_isUnit`

English:
theorem infinite_valued_ne_one_of_not_isUnit
  statement: {a : 𝔸ᶠ[R, K]} (ha₀ : forall v, a v != 0)
  proof: by
  contrapose! ha
  rw [isUnit_iff]
  exact ⟨ha₀, ha⟩

中文:
定理 infinite_valued_ne_one_of_not_isUnit
  结论: {a : 𝔸ᶠ[R, K]} (ha₀ : 对任意 v, a v != 0)
  证明: by
  contrapose! ha
  rw [isUnit_iff]
  exact ⟨ha₀, ha⟩

Depends on / 依赖: contrapose, isUnit_iff
-/
theorem infinite_valued_ne_one_of_not_isUnit {a : 𝔸ᶠ[R, K]} (ha₀ : forall v, a v != 0)
    (ha : ¬IsUnit a) : {v | Valued.v (a v) != 1}.Infinite := by
  contrapose! ha
  rw [isUnit_iff]
  exact ⟨ha₀, ha⟩

variable (R)

variable (K) in
/--
Definition of `unitEmbedding` / `unitEmbedding` 的定义

English:
definition unitEmbedding
  signature: : Kˣ ->* 𝔸ᶠ[R, K]ˣ
  body: Units.map (algebraMap K 𝔸ᶠ[R, K])

中文:
定义 unitEmbedding
  签名: : Kˣ ->* 𝔸ᶠ[R, K]ˣ
  定义体: Units.map (algebraMap K 𝔸ᶠ[R, K])

Depends on / 依赖: Units.map, algebraMap
-/
def unitEmbedding : Kˣ ->* 𝔸ᶠ[R, K]ˣ := Units.map (algebraMap K 𝔸ᶠ[R, K])

/--
theorem `unitEmbedding_apply` / 定理 `unitEmbedding_apply`

English:
theorem unitEmbedding_apply
  given: (k : Kˣ)
  statement: unitEmbedding R K k = algebraMap K 𝔸ᶠ[R, K] k
  proof: rfl

中文:
定理 unitEmbedding_apply
  条件: (k : Kˣ)
  结论: unitEmbedding R K k = algebraMap K 𝔸ᶠ[R, K] k
  证明: rfl
-/
@[simp] theorem unitEmbedding_apply (k : Kˣ) : unitEmbedding R K k = algebraMap K 𝔸ᶠ[R, K] k := rfl

end Units

end FiniteAdeleRing

end IsDedekindDomain
