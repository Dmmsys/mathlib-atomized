/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Field.Dense
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# The field `ℂ_[p]` of `p`-adic complex numbers.

In this file we define the field `ℂ_[p]` of `p`-adic complex numbers as the `p`-adic completion of
an algebraic closure of `ℚ_[p]`. We endow `ℂ_[p]` with both a normed field and a valued field
structure, induced by the unique extension of the `p`-adic norm to `ℂ_[p]`.

## Main Definitions
* `PadicAlgCl p` : the algebraic closure of `ℚ_[p]`.
* `PadicComplex p` : the type of `p`-adic complex numbers, denoted by `ℂ_[p]`.
* `PadicComplexInt p` : the ring of integers of `ℂ_[p]`.

## Main Results

* `PadicComplex.norm_extends` : the norm on `ℂ_[p]` extends the norm on `PadicAlgCl p`, and hence
  the norm on `ℚ_[p]`.
* `PadicComplex.isNonarchimedean` : The norm on `ℂ_[p]` is nonarchimedean.
* `PadicComplex.isAlgClosed` : `ℂ_[p]` is algebraically closed.

## Notation

We introduce the notation `ℂ_[p]` for the `p`-adic complex numbers, and `𝓞_ℂ_[p]` for its ring of
integers.

## Tags

p-adic, p adic, padic, norm, valuation, Cauchy, completion, p-adic completion
-/

@[expose] public section

noncomputable section

open Valuation

open scoped NNReal

variable (p : Nat) [hp : Fact (Nat.Prime p)]

/--
Definition of `PadicAlgCl` / `PadicAlgCl` 的定义

English:
abbreviation PadicAlgCl
  body: AlgebraicClosure Rat_[p]

中文:
缩写 PadicAlgCl
  定义体: AlgebraicClosure Rat_[p]

Depends on / 依赖: AlgebraicClosure, Rat_
-/
abbrev PadicAlgCl := AlgebraicClosure Rat_[p]

namespace PadicAlgCl

/--
Instance `isAlgebraic` / 实例 `isAlgebraic`

English:
instance isAlgebraic
  signature: : Algebra.IsAlgebraic Rat_[p] (PadicAlgCl p)
  body: AlgebraicClosure.isAlgebraic _

中文:
实例 isAlgebraic
  签名: : 代数.是代数 Rat_[p] (PadicAlgCl p)
  定义体: AlgebraicClosure.isAlgebraic _

Depends on / 依赖: AlgebraicClosure, AlgebraicClosure.isAlgebraic, isAlgebraic
-/
instance isAlgebraic : Algebra.IsAlgebraic Rat_[p] (PadicAlgCl p) := AlgebraicClosure.isAlgebraic _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Rat_[p] (PadicAlgCl p)
  body: ⟨algebraMap Rat_[p] (PadicAlgCl p)⟩

中文:
实例 :
  签名: Coe Rat_[p] (PadicAlgCl p)
  定义体: ⟨algebraMap Rat_[p] (PadicAlgCl p)⟩

Depends on / 依赖: PadicAlgCl, Rat_, algebraMap
-/
instance : Coe Rat_[p] (PadicAlgCl p) := ⟨algebraMap Rat_[p] (PadicAlgCl p)⟩

/--
theorem `coe_eq` / 定理 `coe_eq`

English:
theorem coe_eq
  statement: (Coe.coe : Rat_[p] -> PadicAlgCl p) = algebraMap Rat_[p] (PadicAlgCl p)
  proof: rfl

中文:
定理 coe_eq
  结论: (Coe.coe : Rat_[p] -> PadicAlgCl p) = algebraMap Rat_[p] (PadicAlgCl p)
  证明: rfl
-/
theorem coe_eq : (Coe.coe : Rat_[p] -> PadicAlgCl p) = algebraMap Rat_[p] (PadicAlgCl p) := rfl

/--
Instance `normedField` / 实例 `normedField`

English:
instance normedField
  signature: : NormedField (PadicAlgCl p)
  body: spectralNorm.normedField Rat_[p] (PadicAlgCl p)

中文:
实例 normedField
  签名: : 赋范域 (PadicAlgCl p)
  定义体: spectralNorm.normedField Rat_[p] (PadicAlgCl p)

Depends on / 依赖: PadicAlgCl, Rat_, normedField, spectralNorm, spectralNorm.normedField
-/
instance normedField : NormedField (PadicAlgCl p) := spectralNorm.normedField Rat_[p] (PadicAlgCl p)

/--
theorem `isNonarchimedean` / 定理 `isNonarchimedean`

English:
theorem isNonarchimedean
  statement: IsNonarchimedean (norm : PadicAlgCl p -> Real)
  proof: isNonarchimedean_spectralNorm (K := Rat_[p]) (L := PadicAlgCl p)

中文:
定理 isNonarchimedean
  结论: IsNonarchimedean (norm : PadicAlgCl p -> 实数)
  证明: isNonarchimedean_spectralNorm (K := Rat_[p]) (L := PadicAlgCl p)

Depends on / 依赖: PadicAlgCl, Rat_, isNonarchimedean_spectralNorm
-/
theorem isNonarchimedean : IsNonarchimedean (norm : PadicAlgCl p -> Real) :=
  isNonarchimedean_spectralNorm (K := Rat_[p]) (L := PadicAlgCl p)

/--
Instance `normedAlgebra` / 实例 `normedAlgebra`

English:
instance normedAlgebra
  signature: : NormedAlgebra Rat_[p] (PadicAlgCl p)
  body: spectralNorm.normedAlgebra _ _

中文:
实例 normedAlgebra
  签名: : 赋范代数 Rat_[p] (PadicAlgCl p)
  定义体: spectralNorm.normedAlgebra _ _

Depends on / 依赖: normedAlgebra, spectralNorm, spectralNorm.normedAlgebra
-/
instance normedAlgebra : NormedAlgebra Rat_[p] (PadicAlgCl p) := spectralNorm.normedAlgebra _ _

/-- The norm on `PadicAlgCl p` is the spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
@[simp]
/--
theorem `spectralNorm_eq` / 定理 `spectralNorm_eq`

English:
theorem spectralNorm_eq
  given: (x : PadicAlgCl p)
  statement: spectralNorm Rat_[p] (PadicAlgCl p) x = ‖x‖
  proof: rfl

中文:
定理 spectralNorm_eq
  条件: (x : PadicAlgCl p)
  结论: spectralNorm Rat_[p] (PadicAlgCl p) x = ‖x‖
  证明: rfl
-/
theorem spectralNorm_eq (x : PadicAlgCl p) : spectralNorm Rat_[p] (PadicAlgCl p) x = ‖x‖ := rfl

/--
theorem `norm_extends` / 定理 `norm_extends`

English:
theorem norm_extends
  given: (x : Rat_[p])
  statement: ‖(x : PadicAlgCl p)‖ = ‖x‖
  proof: by
  simp

中文:
定理 norm_extends
  条件: (x : Rat_[p])
  结论: ‖(x : PadicAlgCl p)‖ = ‖x‖
  证明: by
  simp
-/
theorem norm_extends (x : Rat_[p]) : ‖(x : PadicAlgCl p)‖ = ‖x‖ := by
  simp

/--
Instance `isUltrametricDist` / 实例 `isUltrametricDist`

English:
instance isUltrametricDist
  signature: : IsUltrametricDist (PadicAlgCl p)
  body: IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (PadicAlgCl.isNonarchimedean p)

中文:
实例 isUltrametricDist
  签名: : 是UltrametricDist (PadicAlgCl p)
  定义体: IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (PadicAlgCl.isNonarchimedean p)

Depends on / 依赖: IsUltrametricDist, IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm, PadicAlgCl, PadicAlgCl.isNonarchimedean, isNonarchimedean, isUltrametricDist_of_forall_norm_add_le_max_norm
-/
instance isUltrametricDist : IsUltrametricDist (PadicAlgCl p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (PadicAlgCl.isNonarchimedean p)

/--
Instance `valued` / 实例 `valued`

English:
instance valued
  signature: : Valued (PadicAlgCl p) Real>=0
  body: NormedField.toValued

中文:
实例 valued
  签名: : 赋值 (PadicAlgCl p) 实数>=0
  定义体: NormedField.toValued

Depends on / 依赖: NormedField, NormedField.toValued, toValued
-/
instance valued : Valued (PadicAlgCl p) Real>=0 := NormedField.toValued

/--
theorem `valuation_def` / 定理 `valuation_def`

English:
theorem valuation_def
  given: (x : PadicAlgCl p)
  statement: Valued.v x = ‖x‖₊
  proof: rfl

中文:
定理 valuation_def
  条件: (x : PadicAlgCl p)
  结论: 赋值.v x = ‖x‖₊
  证明: rfl
-/
theorem valuation_def (x : PadicAlgCl p) : Valued.v x = ‖x‖₊ := rfl

/--
theorem `valuation_coe` / 定理 `valuation_coe`

English:
theorem valuation_coe
  given: (x : PadicAlgCl p)
  statement: ((Valued.v x : Real>=0) : Real) = ‖x‖
  proof: rfl

中文:
定理 valuation_coe
  条件: (x : PadicAlgCl p)
  结论: ((赋值.v x : 实数>=0) : 实数) = ‖x‖
  证明: rfl
-/
theorem valuation_coe (x : PadicAlgCl p) : ((Valued.v x : Real>=0) : Real) = ‖x‖ := rfl

/--
theorem `valuation_p` / 定理 `valuation_p`

English:
theorem valuation_p
  given: (p : Nat) [Fact p.Prime]
  statement: Valued.v (p : PadicAlgCl p) = 1 / (p : Real>=0)
  proof: by
  rw [← map_natCast (algebraMap Rat_[p] (PadicAlgCl p))]
  ext
  rw [valuation_coe]; rw [norm_extends]; rw [Padic.norm_p]; rw [one_div]; rw [NNReal.coe_inv]; rw [NNReal.coe_natCast]

中文:
定理 valuation_p
  条件: (p : 自然数) [Fact p.素]
  结论: 赋值.v (p : PadicAlgCl p) = 1 / (p : 实数>=0)
  证明: by
  rw [← map_natCast (algebraMap Rat_[p] (PadicAlgCl p))]
  ext
  rw [valuation_coe]; rw [norm_extends]; rw [Padic.norm_p]; rw [one_div]; rw [NNReal.coe_inv]; rw [NNReal.coe_natCast]

Depends on / 依赖: NNReal, NNReal.coe_inv, NNReal.coe_natCast, Padic.norm_p, PadicAlgCl, Rat_, algebraMap, coe_inv, coe_natCast, map_natCast, norm_extends, norm_p, one_div, valuation_coe
-/
theorem valuation_p (p : Nat) [Fact p.Prime] : Valued.v (p : PadicAlgCl p) = 1 / (p : Real>=0) := by
  rw [← map_natCast (algebraMap Rat_[p] (PadicAlgCl p))]
  ext
  rw [valuation_coe]; rw [norm_extends]; rw [Padic.norm_p]; rw [one_div]; rw [NNReal.coe_inv]; rw [NNReal.coe_natCast]

open MonoidWithZeroHom.ValueGroup₀

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RankOne (PadicAlgCl.valued p).v
  body: embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

中文:
实例 :
  签名: 秩一 (PadicAlgCl.valued p).v
  定义体: embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

Depends on / 依赖: embedding
-/
instance : RankOne (PadicAlgCl.valued p).v where
  hom' := embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformContinuousConstSMul Rat_[p] (PadicAlgCl p)
  body: uniformContinuousConstSMul_of_continuousConstSMul Rat_[p] (PadicAlgCl p)

中文:
实例 :
  签名: 一致连续常数标量乘法 Rat_[p] (PadicAlgCl p)
  定义体: uniformContinuousConstSMul_of_continuousConstSMul Rat_[p] (PadicAlgCl p)

Depends on / 依赖: PadicAlgCl, Rat_, uniformContinuousConstSMul_of_continuousConstSMul
-/
instance : UniformContinuousConstSMul Rat_[p] (PadicAlgCl p) :=
  uniformContinuousConstSMul_of_continuousConstSMul Rat_[p] (PadicAlgCl p)

/--
Instance `nontriviallyNormedField` / 实例 `nontriviallyNormedField`

English:
instance nontriviallyNormedField
  signature: : NontriviallyNormedField (PadicAlgCl p) where
  body: by
    choose x hx using NontriviallyNormedField.non_trivial (α := Rat_[p])
    use x
    rw [PadicAlgCl.norm_extends]
    exact hx

中文:
实例 nontriviallyNormedField
  签名: : NontriviallyNormedField (PadicAlgCl p) where
  定义体: by
    choose x hx using NontriviallyNormedField.non_trivial (α := Rat_[p])
    use x
    rw [PadicAlgCl.norm_extends]
    exact hx

Depends on / 依赖: NontriviallyNormedField, NontriviallyNormedField.non_trivial, PadicAlgCl, PadicAlgCl.norm_extends, Rat_, non_trivial, norm_extends
-/
instance nontriviallyNormedField : NontriviallyNormedField (PadicAlgCl p) where
  non_trivial := by
    choose x hx using NontriviallyNormedField.non_trivial (α := Rat_[p])
    use x
    rw [PadicAlgCl.norm_extends]
    exact hx

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: : CharZero (PadicAlgCl p)
  body: (RingHom.charZero_iff (algebraMap Rat_[p] (PadicAlgCl p)).injective).mp inferInstance

中文:
实例 charZero
  签名: : 特征零 (PadicAlgCl p)
  定义体: (RingHom.charZero_iff (algebraMap Rat_[p] (PadicAlgCl p)).injective).mp inferInstance

Depends on / 依赖: PadicAlgCl, Rat_, RingHom, RingHom.charZero_iff, algebraMap, charZero_iff, injective
-/
instance charZero : CharZero (PadicAlgCl p) :=
  (RingHom.charZero_iff (algebraMap Rat_[p] (PadicAlgCl p)).injective).mp inferInstance

end PadicAlgCl

/--
Definition of `PadicComplex` / `PadicComplex` 的定义

English:
abbreviation PadicComplex
  body: UniformSpace.Completion (PadicAlgCl p)

中文:
缩写 PadicComplex
  定义体: UniformSpace.Completion (PadicAlgCl p)

Depends on / 依赖: Completion, PadicAlgCl, UniformSpace, UniformSpace.Completion
-/
abbrev PadicComplex := UniformSpace.Completion (PadicAlgCl p)

/-- `ℂ_[p]` is the field of `p`-adic complex numbers. -/
notation "Complex_[" p "]" => PadicComplex p

namespace PadicComplex

/--
Instance `valued` / 实例 `valued`

English:
instance valued
  signature: : Valued Complex_[p] Real>=0
  body: Valued.valuedCompletion

中文:
实例 valued
  签名: : 赋值 Complex_[p] 实数>=0
  定义体: Valued.valuedCompletion

Depends on / 依赖: Valued, Valued.valuedCompletion, valuedCompletion
-/
instance valued : Valued Complex_[p] Real>=0 := Valued.valuedCompletion

/--
theorem `valuation_extends` / 定理 `valuation_extends`

English:
theorem valuation_extends
  given: (x : PadicAlgCl p)
  statement: Valued.v (x : Complex_[p]) = Valued.v x
  proof: Valued.extensionValuation_apply_coe _

中文:
定理 valuation_extends
  条件: (x : PadicAlgCl p)
  结论: 赋值.v (x : Complex_[p]) = 赋值.v x
  证明: Valued.extensionValuation_apply_coe _

Depends on / 依赖: Valued, Valued.extensionValuation_apply_coe, extensionValuation_apply_coe
-/
theorem valuation_extends (x : PadicAlgCl p) : Valued.v (x : Complex_[p]) = Valued.v x :=
  Valued.extensionValuation_apply_coe _

/--
theorem `coe_eq` / 定理 `coe_eq`

English:
theorem coe_eq
  given: (x : PadicAlgCl p)
  statement: (x : Complex_[p]) = algebraMap (PadicAlgCl p) Complex_[p] x
  proof: rfl

中文:
定理 coe_eq
  条件: (x : PadicAlgCl p)
  结论: (x : Complex_[p]) = algebraMap (PadicAlgCl p) Complex_[p] x
  证明: rfl
-/
theorem coe_eq (x : PadicAlgCl p) : (x : Complex_[p]) = algebraMap (PadicAlgCl p) Complex_[p] x := rfl

/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : PadicAlgCl p) : Complex_[p]) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : PadicAlgCl p) : Complex_[p]) = 0
  证明: rfl
-/
@[simp] theorem coe_zero : ((0 : PadicAlgCl p) : Complex_[p]) = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower Rat_[p] (PadicAlgCl p) Complex_[p]
  body: IsScalarTower.of_algebraMap_eq (congrFun rfl)

@[simp, norm_cast]

中文:
实例 :
  签名: 标量塔 Rat_[p] (PadicAlgCl p) Complex_[p]
  定义体: IsScalarTower.of_algebraMap_eq (congrFun rfl)

@[simp, norm_cast]

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance : IsScalarTower Rat_[p] (PadicAlgCl p) Complex_[p] := IsScalarTower.of_algebraMap_eq (congrFun rfl)

@[simp, norm_cast]
/--
lemma `coe_natCast` / 引理 `coe_natCast`

English:
lemma coe_natCast
  given: (n : Nat)
  statement: ((n : PadicAlgCl p) : Complex_[p]) = (n : Complex_[p])
  proof: by
  rw [← map_natCast (algebraMap (PadicAlgCl p) Complex_[p]) n, coe_eq]

中文:
引理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : PadicAlgCl p) : Complex_[p]) = (n : Complex_[p])
  证明: by
  rw [← map_natCast (algebraMap (PadicAlgCl p) Complex_[p]) n, coe_eq]

Depends on / 依赖: Complex_, PadicAlgCl, algebraMap, coe_eq, map_natCast
-/
lemma coe_natCast (n : Nat) : ((n : PadicAlgCl p) : Complex_[p]) = (n : Complex_[p]) := by
  rw [← map_natCast (algebraMap (PadicAlgCl p) Complex_[p]) n, coe_eq]

/--
theorem `valuation_p` / 定理 `valuation_p`

English:
theorem valuation_p
  statement: Valued.v (p : Complex_[p]) = 1 / (p : Real>=0)
  proof: by
  rw [← map_natCast (algebraMap (PadicAlgCl p) Complex_[p]), ← coe_eq, valuation_extends,
    PadicAlgCl.valuation_p]

中文:
定理 valuation_p
  结论: 赋值.v (p : Complex_[p]) = 1 / (p : 实数>=0)
  证明: by
  rw [← map_natCast (algebraMap (PadicAlgCl p) Complex_[p]), ← coe_eq, valuation_extends,
    PadicAlgCl.valuation_p]

Depends on / 依赖: Complex_, PadicAlgCl, PadicAlgCl.valuation_p, algebraMap, coe_eq, map_natCast, valuation_extends, valuation_p
-/
theorem valuation_p : Valued.v (p : Complex_[p]) = 1 / (p : Real>=0) := by
  rw [← map_natCast (algebraMap (PadicAlgCl p) Complex_[p]), ← coe_eq, valuation_extends,
    PadicAlgCl.valuation_p]

open MonoidWithZeroHom.ValueGroup₀

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RankOne (PadicComplex.valued p).v
  body: embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

@[simp]

中文:
实例 :
  签名: 秩一 (PadicComplex.valued p).v
  定义体: embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

@[simp]

Depends on / 依赖: embedding
-/
instance : RankOne (PadicComplex.valued p).v where
  hom' := embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

@[simp]
/--
theorem `RankOne.hom_eq_embedding` / 定理 `RankOne.hom_eq_embedding`

English:
theorem RankOne.hom_eq_embedding
  statement: RankOne.hom (PadicComplex.valued p).v = embedding
  proof: rfl

中文:
定理 秩一.hom_eq_embedding
  结论: 秩一.hom (PadicComplex.valued p).v = embedding
  证明: rfl
-/
theorem RankOne.hom_eq_embedding : RankOne.hom (PadicComplex.valued p).v = embedding := rfl

/--
Instance `normedField` / 实例 `normedField`

English:
instance normedField
  signature: : NormedField Complex_[p]
  body: inferInstance

中文:
实例 normedField
  签名: : 赋范域 Complex_[p]
  定义体: inferInstance
-/
instance normedField : NormedField Complex_[p] := inferInstance

-- Ensure that the norm instance on `ℂ_[p]` is extended from `PadicAlgCl p`.
example : (‖·‖ : Complex_[p] -> Real) = (UniformSpace.Completion.instNorm (PadicAlgCl p)).norm := by
  with_reducible_and_instances rfl

/--
theorem `norm_extends` / 定理 `norm_extends`

English:
theorem norm_extends
  given: (x : PadicAlgCl p)
  statement: ‖(x : Complex_[p])‖ = ‖x‖
  proof: by
  simp

中文:
定理 norm_extends
  条件: (x : PadicAlgCl p)
  结论: ‖(x : Complex_[p])‖ = ‖x‖
  证明: by
  simp
-/
theorem norm_extends (x : PadicAlgCl p) : ‖(x : Complex_[p])‖ = ‖x‖ := by
  simp

/--
theorem `norm_extends'` / 定理 `norm_extends'`

English:
theorem norm_extends'
  given: (x : Rat_[p])
  statement: ‖(x : Complex_[p])‖ = ‖x‖
  proof: by
  simp

中文:
定理 norm_extends'
  条件: (x : Rat_[p])
  结论: ‖(x : Complex_[p])‖ = ‖x‖
  证明: by
  simp
-/
theorem norm_extends' (x : Rat_[p]) : ‖(x : Complex_[p])‖ = ‖x‖ := by
  simp

/--
Instance `isUltrametricDist` / 实例 `isUltrametricDist`

English:
instance isUltrametricDist
  signature: : IsUltrametricDist Complex_[p]
  body: IsUltrametricDist.of_normedAlgebra Rat_[p]

中文:
实例 isUltrametricDist
  签名: : 是UltrametricDist Complex_[p]
  定义体: IsUltrametricDist.of_normedAlgebra Rat_[p]

Depends on / 依赖: IsUltrametricDist, IsUltrametricDist.of_normedAlgebra, Rat_, of_normedAlgebra
-/
instance isUltrametricDist : IsUltrametricDist Complex_[p] := IsUltrametricDist.of_normedAlgebra Rat_[p]

/--
theorem `isNonarchimedean` / 定理 `isNonarchimedean`

English:
theorem isNonarchimedean
  statement: IsNonarchimedean (Norm.norm : Complex_[p] -> Real)
  proof: IsUltrametricDist.norm_add_le_max

中文:
定理 isNonarchimedean
  结论: IsNonarchimedean (范数.norm : Complex_[p] -> 实数)
  证明: IsUltrametricDist.norm_add_le_max

Depends on / 依赖: IsUltrametricDist, IsUltrametricDist.norm_add_le_max, norm_add_le_max
-/
theorem isNonarchimedean : IsNonarchimedean (Norm.norm : Complex_[p] -> Real) :=
  IsUltrametricDist.norm_add_le_max

/--
theorem `norm_eq_norm'` / 定理 `norm_eq_norm'`

English:
theorem norm_eq_norm'
  statement: (‖·‖ : Complex_[p] -> Real) = Valued.v.norm
  proof: by
  apply UniformSpace.Completion.extension_unique (f := @norm (PadicAlgCl p) _) (g := Valued.v.norm)
  · exact uniformContinuous_norm
  · let S := (Valued.toNormedField Complex_[p] NNReal).toNormedCommRing.toNormedRing.toSeminormedRing
    let := S.toNonUnitalSeminormedRing.toSeminormedAddCommGroup.toSeminormedAddGroup
    exact @uniformContinuous_norm Complex_[p] this
  · intro x
    simp only [Valued.v.norm_def, RankOne.hom_eq_embedding]
    rw [embedding_restrict (PadicComplex.valued p).v x]; rw [valuation_extends]; rw [← PadicAlgCl.valuation_coe]

中文:
定理 norm_eq_norm'
  结论: (‖·‖ : Complex_[p] -> 实数) = 赋值.v.norm
  证明: by
  apply UniformSpace.Completion.extension_unique (f := @norm (PadicAlgCl p) _) (g := Valued.v.norm)
  · exact uniformContinuous_norm
  · let S := (Valued.toNormedField Complex_[p] NNReal).toNormedCommRing.toNormedRing.toSeminormedRing
    let := S.toNonUnitalSeminormedRing.toSeminormedAddCommGroup.toSeminormedAddGroup
    exact @uniformContinuous_norm Complex_[p] this
  · intro x
    simp only [Valued.v.norm_def, RankOne.hom_eq_embedding]
    rw [embedding_restrict (PadicComplex.valued p).v x]; rw [valuation_extends]; rw [← PadicAlgCl.valuation_coe]

Depends on / 依赖: Completion, Complex_, NNReal, PadicAlgCl, PadicComplex, PadicComplex.valued, RankOne, RankOne.hom_eq_embedding, S.toNonUnitalSeminormedRing.toSeminormedAddCommGroup.toSeminormedAddGroup, UniformSpace, UniformSpace.Completion.extension_unique, Valued, Valued.toNormedField, Valued.v.norm, Valued.v.norm_def, embedding_restrict, extension_unique, hom_eq_embedding, norm_def, toNonUnitalSeminormedRing
-/
theorem norm_eq_norm' : (‖·‖ : Complex_[p] -> Real) = Valued.v.norm := by
  apply UniformSpace.Completion.extension_unique (f := @norm (PadicAlgCl p) _) (g := Valued.v.norm)
  · exact uniformContinuous_norm
  · let S := (Valued.toNormedField Complex_[p] NNReal).toNormedCommRing.toNormedRing.toSeminormedRing
    let := S.toNonUnitalSeminormedRing.toSeminormedAddCommGroup.toSeminormedAddGroup
    exact @uniformContinuous_norm Complex_[p] this
  · intro x
    simp only [Valued.v.norm_def, RankOne.hom_eq_embedding]
    rw [embedding_restrict (PadicComplex.valued p).v x]; rw [valuation_extends]; rw [← PadicAlgCl.valuation_coe]

/--
theorem `norm_eq_norm` / 定理 `norm_eq_norm`

English:
theorem norm_eq_norm
  given: (x : Complex_[p])
  statement: ‖x‖ = Valued.v.norm x
  proof: by
  congr!
  exact norm_eq_norm' p

中文:
定理 norm_eq_norm
  条件: (x : Complex_[p])
  结论: ‖x‖ = 赋值.v.norm x
  证明: by
  congr!
  exact norm_eq_norm' p

Depends on / 依赖: norm_eq_norm
-/
theorem norm_eq_norm (x : Complex_[p]) : ‖x‖ = Valued.v.norm x := by
  congr!
  exact norm_eq_norm' p

/--
theorem `nnnorm_extends` / 定理 `nnnorm_extends`

English:
theorem nnnorm_extends
  given: (x : PadicAlgCl p)
  statement: ‖(x : Complex_[p])‖₊ = ‖x‖₊
  proof: by
  ext
  exact norm_extends p x

中文:
定理 nnnorm_extends
  条件: (x : PadicAlgCl p)
  结论: ‖(x : Complex_[p])‖₊ = ‖x‖₊
  证明: by
  ext
  exact norm_extends p x

Depends on / 依赖: norm_extends
-/
theorem nnnorm_extends (x : PadicAlgCl p) : ‖(x : Complex_[p])‖₊ = ‖x‖₊ := by
  ext
  exact norm_extends p x

/--
theorem `nnnorm_extends'` / 定理 `nnnorm_extends'`

English:
theorem nnnorm_extends'
  given: (x : Rat_[p])
  statement: ‖(x : Complex_[p])‖₊ = ‖x‖₊
  proof: by
  ext
  simp

中文:
定理 nnnorm_extends'
  条件: (x : Rat_[p])
  结论: ‖(x : Complex_[p])‖₊ = ‖x‖₊
  证明: by
  ext
  simp
-/
theorem nnnorm_extends' (x : Rat_[p]) : ‖(x : Complex_[p])‖₊ = ‖x‖₊ := by
  ext
  simp

/--
Instance `nontriviallyNormedField` / 实例 `nontriviallyNormedField`

English:
instance nontriviallyNormedField
  signature: : NontriviallyNormedField Complex_[p] where
  body: by
    choose x hx using NontriviallyNormedField.non_trivial (α := Rat_[p])
    use x
    simpa only [norm_extends']

中文:
实例 nontriviallyNormedField
  签名: : NontriviallyNormedField Complex_[p] where
  定义体: by
    choose x hx using NontriviallyNormedField.non_trivial (α := Rat_[p])
    use x
    simpa only [norm_extends']

Depends on / 依赖: NontriviallyNormedField, NontriviallyNormedField.non_trivial, Rat_, non_trivial, norm_extends
-/
instance nontriviallyNormedField : NontriviallyNormedField Complex_[p] where
  non_trivial := by
    choose x hx using NontriviallyNormedField.non_trivial (α := Rat_[p])
    use x
    simpa only [norm_extends']

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: : CharZero Complex_[p]
  body: (RingHom.charZero_iff (algebraMap Rat_[p] Complex_[p]).injective).mp inferInstance

中文:
实例 charZero
  签名: : 特征零 Complex_[p]
  定义体: (RingHom.charZero_iff (algebraMap Rat_[p] Complex_[p]).injective).mp inferInstance

Depends on / 依赖: Complex_, Rat_, RingHom, RingHom.charZero_iff, algebraMap, charZero_iff, injective
-/
instance charZero : CharZero Complex_[p] :=
  (RingHom.charZero_iff (algebraMap Rat_[p] Complex_[p]).injective).mp inferInstance

/--
Instance `isAlgClosed` / 实例 `isAlgClosed`

English:
instance isAlgClosed
  signature: : IsAlgClosed Complex_[p]
  body: IsAlgClosed.of_denseRange UniformSpace.Completion.denseRange_coe

中文:
实例 isAlgClosed
  签名: : 是代数闭 Complex_[p]
  定义体: IsAlgClosed.of_denseRange UniformSpace.Completion.denseRange_coe

Depends on / 依赖: Completion, IsAlgClosed, IsAlgClosed.of_denseRange, UniformSpace, UniformSpace.Completion.denseRange_coe, denseRange_coe, of_denseRange
-/
instance isAlgClosed : IsAlgClosed Complex_[p] :=
  IsAlgClosed.of_denseRange UniformSpace.Completion.denseRange_coe

end PadicComplex

/--
Definition of `PadicComplexInt` / `PadicComplexInt` 的定义

English:
definition PadicComplexInt
  signature: : ValuationSubring Complex_[p]
  body: (PadicComplex.valued p).v.valuationSubring

中文:
定义 PadicComplex整数
  签名: : 赋值子环 Complex_[p]
  定义体: (PadicComplex.valued p).v.valuationSubring

Depends on / 依赖: PadicComplex, PadicComplex.valued, v.valuationSubring, valuationSubring, valued
-/
def PadicComplexInt : ValuationSubring Complex_[p] := (PadicComplex.valued p).v.valuationSubring

/-- We define `𝓞_ℂ_[p]` as the subring of elements of `ℂ_[p]` with valuation `≤ 1`. -/
notation "𝓞_Complex_[" p "]" => PadicComplexInt p

/--
theorem `PadicComplexInt.integers` / 定理 `PadicComplexInt.integers`

English:
theorem PadicComplexInt.integers
  statement: Valuation.Integers (PadicComplex.valued p).v 𝓞_Complex_[p]
  proof: Valuation.integer.integers _

中文:
定理 PadicComplex整数.integers
  结论: 赋值.整数egers (PadicComplex.valued p).v 𝓞_Complex_[p]
  证明: Valuation.integer.integers _

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers
-/
theorem PadicComplexInt.integers : Valuation.Integers (PadicComplex.valued p).v 𝓞_Complex_[p] :=
  Valuation.integer.integers _
