/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.Archimedean.Submonoid
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Valuation.Archimedean
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.Valued.NormedValued

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Finite places of number fields

This file defines finite places of a number field `K` as absolute values coming from an embedding
into a completion of `K` associated to a non-zero prime ideal of `𝓞 K`.

Many of the results in this file are expressed in the generality of: `R` is a Dedekind domain
with field of fractions `K` such that `Module.Finite ℤ R` and `Module.Free ℤ R`. If `K` is
a number field, then this characterises `R` as being isomorphic to `𝓞 K` without explicitly
requiring `𝓞 K`. This is so that `ℤ` and `𝓞 ℚ` can be used interchangeably.

## Main Definitions and Results
* `NumberField.adicAbv`: a `v`-adic absolute value on `K`.
* `NumberField.FinitePlace`: the type of finite places of a number field `K`.
* `NumberField.FinitePlace.embedding`: the canonical embedding of a number field `K` to the
  `v`-adic completion `v.adicCompletion K` of `K`, where `v` is a non-zero prime ideal of `𝓞 K`
* `NumberField.FinitePlace.norm_embedding`: the norm of `embedding v x` is the same as the `v`-adic
  absolute value of `x`. See also `NumberField.FinitePlace.norm_embedding'` and
  `NumberField.FinitePlace.norm_embedding_int` for versions where the `v`-adic absolute value is
  unfolded.
* `NumberField.FinitePlace.hasFiniteMulSupport`: the `v`-adic absolute value of a non-zero element
  of `K` is different from 1 for at most finitely many `v`.
*  The valuation subrings of the field at the `v`-valuation and it's adic completion are
   discrete valuation rings.

## Tags
number field, places, finite places
-/

@[expose] public section

open Ideal IsDedekindDomain HeightOneSpectrum WithZeroMulInt WithZero

open scoped WithZero NNReal

section DVR

variable (A : Type*) [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (v : HeightOneSpectrum A) (hv : Finite (A ⧸ v.asIdeal))

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPrincipalIdealRing (v.valuation K).integer := by
  rw [(Valuation.integer.integers (v.valuation K)).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using (v.valuation K).toMonoidWithZeroHom.range_nontrivial
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDiscreteValuationRing (v.valuation K).integer :=
  (v.valuation K).valuationSubring_isDiscreteValuationRing
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  unfold HeightOneSpectrum.adicCompletionIntegers
  rw [(Valuation.valuationSubring.integers (Valued.v)).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using Valued.v.range_nontrivial

-- TODO: make this inferred from `IsRankOneDiscrete`, or
-- develop the API for a completion of a base `IsDVR` ring
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    unfold HeightOneSpectrum.adicCompletionIntegers
    simp only [ne_eq, Ideal.ext_iff, Valuation.mem_maximalIdeal_iff, Ideal.mem_bot, Subtype.ext_iff,
      ZeroMemClass.coe_zero, Subtype.forall, Valuation.mem_valuationSubring_iff, not_forall,
      exists_prop]
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    use (WithVal.equiv (v.valuation K)).symm π
    simp [hπ, ← exp_zero, -exp_neg,
      ← (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_eq_zero_iff]

end DVR

namespace NumberField

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K] [IsDedekindDomain R]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The embedding of a field inside its `adicCompletion` with respect to `v`. -/
/-
**NumberField.FinitePlace.embedding** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Finit
ePlace`。
形式化陈述：{K : Type u_1} →   [inst : Field K] →     {R : Type u_2} →       [inst_1 :
 CommRing R] →         [inst_2 : Algebra R K] →           [inst_3 : IsDedekindDo
main R] →             [inst_4 : IsFractionRing R K] →               (v : IsDedek
indDomain.HeightOneSpectrum R) → K →+* IsDedekindDomain.HeightOneSpectrum.adicCo
mpletion K v
参数：v : IsDedekindDomain.HeightOneSpectrum R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of a field inside its `adicCompletion` with respect to `v`.
-/
noncomputable def FinitePlace.embedding : K →+* adicCompletion K v :=
  (adicCompletion.equiv K v).symm.toRingHom.comp
    (UniformSpace.Completion.coeRingHom.comp (WithVal.equiv (v.valuation K)).symm)
/-
**NumberField.FinitePlace.embedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.FinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R) (x : K),   (NumberField.FinitePlace
.embedding v) x =     { toCompletion := ↑((WithVal.equiv (IsDedekindDomain.Heigh
tOneSpectrum.valuation K v)).symm x) }
参数：v : IsDedekindDomain.HeightOneSpectrum R；x : K；NumberField.FinitePlace.embedd
ing v；(WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FinitePlace.embedding_apply (x : K) : embedding v x = ↑x := rfl

section AbsoluteValue

/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

section FiniteFree

/-! In this section we assume further that `Module.Finite ℤ R` and `Module.Free ℤ R`.
This characterises `R` as being isomorphic to `𝓞 K` without explicitly requiring that type.
As a result, if `F = ℚ`, then we can use `ℤ` and `𝓞 ℚ` interchangeably. -/

variable [Module.Finite ℤ R] [Module.Free ℤ R]

namespace HeightOneSpectrum

/-- The norm of a maximal ideal is `> 1` -/
/-
**NumberField.HeightOneSpectrum.one_lt_absNorm** 是 Mathlib 中的一个引理，位于命名空间 `Number
Field.HeightOneSpectrum`。
形式化陈述：one_lt_absNorm : 1 < absNorm v.asIdeal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.absNorm_eq_one_iff`：absNorm_eq_one_iff {I : Ideal S} : absNorm I =
 1 ↔ I = ⊤
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Ideal.absNorm_ne_zero_iff`：absNorm_ne_zero_iff (I : Ideal S) : Ideal.abs
Norm I != 0 ↔ Finite (S ⧸ I)
· 使用定理 `Ideal.finiteQuotientOfFreeOfNeBot`：finiteQuotientOfFreeOfNeBot [Module.F
ree Int S] [Module.Finite Int S] (I : Ideal S) (hI : I != ⊥) : Finite (S ⧸ I)
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥

--- 原说明 ---
The norm of a maximal ideal is `> 1`
-/
lemma one_lt_absNorm : 1 < absNorm v.asIdeal := by
  by_contra! h
  apply IsPrime.ne_top v.isPrime
  rw [← absNorm_eq_one_iff]
  have : 0 < absNorm v.asIdeal := by
    rw [Nat.pos_iff_ne_zero, absNorm_ne_zero_iff]
    exact v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  lia

/-- The norm of a maximal ideal as an element of `ℝ≥0` is `> 1` -/
/-
**NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal** 是 Mathlib 中的一个引理，位于命名空间 
`NumberField.HeightOneSpectrum`。
形式化陈述：one_lt_absNorm_nnreal : 1 < (absNorm v.asIdeal : Real>=0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `NumberField.HeightOneSpectrum.one_lt_absNorm`：one_lt_absNorm : 1 < absNo
rm v.asIdeal

--- 原说明 ---
The norm of a maximal ideal as an element of `ℝ≥0` is `> 1`
-/
lemma one_lt_absNorm_nnreal : 1 < (absNorm v.asIdeal : ℝ≥0) := mod_cast one_lt_absNorm v

/-- The norm of a maximal ideal as an element of `ℝ≥0` is `≠ 0` -/
/-
**NumberField.HeightOneSpectrum.absNorm_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Numbe
rField.HeightOneSpectrum`。
形式化陈述：absNorm_ne_zero : (absNorm v.asIdeal : Real>=0) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal`：one_lt_absNorm_nnre
al : 1 < (absNorm v.asIdeal : Real>=0)

--- 原说明 ---
The norm of a maximal ideal as an element of `ℝ≥0` is `≠ 0`
-/
lemma absNorm_ne_zero : (absNorm v.asIdeal : ℝ≥0) ≠ 0 :=
  ne_zero_of_lt (one_lt_absNorm_nnreal v)

variable (K)

/-- The `v`-adic absolute value on `K` defined as the norm of `v` raised to negative `v`-adic
valuation -/
/-
**NumberField.HeightOneSpectrum.adicAbv** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.H
eightOneSpectrum`。
形式化陈述：adicAbv : AbsoluteValue K Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal`：one_lt_absNorm_nnre
al : 1 < (absNorm v.asIdeal : Real>=0)

--- 原说明 ---
The `v`-adic absolute value on `K` defined as the norm of `v` raised to negative
 `v`-adic
valuation
-/
noncomputable def adicAbv : AbsoluteValue K ℝ := v.adicAbv <| one_lt_absNorm_nnreal v
/-
**NumberField.HeightOneSpectrum.adicAbv_def** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.HeightOneSpectrum`。
形式化陈述：adicAbv_def {x : K} : adicAbv K v x = toNNReal (absNorm_ne_zero v) (v.valu
ation K x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adicAbv_def {x : K} : adicAbv K v x = toNNReal (absNorm_ne_zero v) (v.valuation K x) := rfl

/-- The `v`-adic absolute value is nonarchimedean -/
/-
**NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.HeightOneSpectrum`。
形式化陈述：isNonarchimedean_adicAbv : IsNonarchimedean (adicAbv K v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isNonarchimedean_adicAbv`：isNonarchim
edean_adicAbv : IsNonarchimedean (α
· 使用引理 `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal`：one_lt_absNorm_nnre
al : 1 < (absNorm v.asIdeal : Real>=0)

--- 原说明 ---
The `v`-adic absolute value is nonarchimedean
-/
theorem isNonarchimedean_adicAbv : IsNonarchimedean (adicAbv K v) :=
  v.isNonarchimedean_adicAbv <| one_lt_absNorm_nnreal v

open Valuation.IsRankOneDiscrete
/-
**NumberField.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.HeightOn
eSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (v.valuation K).RankOne :=
  rankOne (v.valuation K) (one_lt_absNorm_nnreal v)
/-
**NumberField.HeightOneSpectrum.instRankOneAdicCompletion** 是 Mathlib 中的一个实例，位于命
名空间 `NumberField.HeightOneSpectrum`。
形式化陈述：instRankOneAdicCompletion : (Valued.v : Valuation (v.adicCompletion K) Int
ᵐ⁰).RankOne
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletion
V`：∀ {K : Type u_1} [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [inst_
2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFr…
· 使用引理 `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal`：one_lt_absNorm_nnre
al : 1 < (absNorm v.asIdeal : Real>=0)
-/
noncomputable instance instRankOneAdicCompletion :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).RankOne :=
  rankOne (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (one_lt_absNorm_nnreal v)
/-
**NumberField.HeightOneSpectrum.rankOne_hom'_def** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.HeightOneSpectrum`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   [inst_5 : Module.Finite ℤ R] [ins
t_6 : Module.Free ℤ R],   Valuation.RankLeOne.hom' Valued.v =     (WithZeroMulIn
t.toNNReal ⋯).comp       (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZero
MulInt Valued.v).toMonoidWithZeroHom
参数：K : Type u_1；v : IsDedekindDomain.HeightOneSpectrum R；WithZeroMulInt.toNNReal
 ⋯；Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt Valued.v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
lemma rankOne_hom'_def :
    (instRankOneAdicCompletion K v).hom' = (toNNReal (absNorm_ne_zero v)).comp
      (valueGroup₀_equiv_withZeroMulInt Valued.v).toMonoidWithZeroHom := rfl

/-- The `v`-adic completion of `K` is a normed field. -/
/-
**NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion** 是 Mathlib 
中的一个实例，位于命名空间 `NumberField.HeightOneSpectrum`。
形式化陈述：instNormedFieldValuedAdicCompletion : NormedField (adicCompletion K v)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `v`-adic completion of `K` is a normed field.
-/
noncomputable instance instNormedFieldValuedAdicCompletion : NormedField (adicCompletion K v) :=
  Valued.toNormedField (adicCompletion K v) ℤᵐ⁰
/-
**NumberField.HeightOneSpectrum.toNNReal_valued_eq_adicAbv** 是 Mathlib 中的一个引理，位于
命名空间 `NumberField.HeightOneSpectrum`。
形式化陈述：toNNReal_valued_eq_adicAbv (x : WithVal (v.valuation K)) : toNNReal (absNo
rm_ne_zero v) (Valued.v x) = adicAbv K v (WithVal.equiv _ x)
参数：x : WithVal (v.valuation K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.HeightOneSpectrum.absNorm_ne_zero`：absNorm_ne_zero : (absNor
m v.asIdeal : Real>=0) != 0
-/
lemma toNNReal_valued_eq_adicAbv (x : WithVal (v.valuation K)) :
    toNNReal (absNorm_ne_zero v) (Valued.v x) = adicAbv K v (WithVal.equiv _ x) := rfl

/-- The `v`-adic absolute value satisfies the ultrametric inequality. -/
/-
**NumberField.HeightOneSpectrum.adicAbv_add_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.HeightOneSpectrum`。
形式化陈述：adicAbv_add_le_max (x y : K) : adicAbv K v (x + y) <= (adicAbv K v x) ⊔ (a
dicAbv K v y)
参数：x y : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv`：isNonarchimedean
_adicAbv : IsNonarchimedean (adicAbv K v)

--- 原说明 ---
The `v`-adic absolute value satisfies the ultrametric inequality.
-/
theorem adicAbv_add_le_max (x y : K) :
    adicAbv K v (x + y) ≤ (adicAbv K v x) ⊔ (adicAbv K v y) := isNonarchimedean_adicAbv K v x y

/-- The `v`-adic absolute value of a natural number is `≤ 1`. -/
/-
**NumberField.HeightOneSpectrum.adicAbv_natCast_le_one** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.HeightOneSpectrum`。
形式化陈述：adicAbv_natCast_le_one (n : Nat) : adicAbv K v n <= 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsNonarchimedean.apply_natCast_le_one`：apply_natCast_le_one {F α : Type*
} [AddMonoidWithOne α] [FunLike F α R] [ZeroHomClass F α R] [NonnegHomClass F α 
R] [OneHomClass F α R] {f :…
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv`：isNonarchimedean
_adicAbv : IsNonarchimedean (adicAbv K v)

--- 原说明 ---
The `v`-adic absolute value of a natural number is `≤ 1`.
-/
theorem adicAbv_natCast_le_one (n : ℕ) : adicAbv K v n ≤ 1 :=
  (isNonarchimedean_adicAbv K v).apply_natCast_le_one

/-- The `v`-adic absolute value of an integer is `≤ 1`. -/
/-
**NumberField.HeightOneSpectrum.adicAbv_intCast_le_one** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.HeightOneSpectrum`。
形式化陈述：adicAbv_intCast_le_one (n : Int) : adicAbv K v n <= 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNonarchimedean.apply_intCast_le_one`：apply_intCast_le_one [IsStrictOrd
eredRing R] {F α : Type*} [AddGroupWithOne α] [FunLike F α R] [AddGroupSeminormC
lass F α R] [OneHomClass F …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv`：isNonarchimedean
_adicAbv : IsNonarchimedean (adicAbv K v)

--- 原说明 ---
The `v`-adic absolute value of an integer is `≤ 1`.
-/
theorem adicAbv_intCast_le_one (n : ℤ) : adicAbv K v n ≤ 1 :=
  (isNonarchimedean_adicAbv K v).apply_intCast_le_one

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm := one_lt_absNorm
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm := one_lt_absNorm
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm_nnreal := one_lt_absNorm_nnreal
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm_nnreal :=
  one_lt_absNorm_nnreal
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero := absNorm_ne_zero
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero := absNorm_ne_zero
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv := adicAbv
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv := adicAbv
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_def := adicAbv_def
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_def := adicAbv_def
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.isNonarchimedean_adicAbv :=
  isNonarchimedean_adicAbv
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.isNonarchimedean_adicAbv :=
  isNonarchimedean_adicAbv
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.instRankOneAdicCompletion := instRankOneAdicCompletion
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.instRankOneAdicCompletion := instRankOneAdicCompletion
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.instNormedFieldValuedAdicCompletion := instNormedFieldValuedAdicCompletion
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.instNormedFieldValuedAdicCompletion := instNormedFieldValuedAdicCompletion
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.rankOne_hom'_def := rankOne_hom'_def
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.rankOne_hom'_def := rankOne_hom'_def
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.toNNReal_valued_eq_adicAbv := toNNReal_valued_eq_adicAbv
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.toNNReal_valued_eq_adicAbv := toNNReal_valued_eq_adicAbv
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_add_le_max := adicAbv_add_le_max
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_add_le_max := adicAbv_add_le_max
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_natCast_le_one := adicAbv_natCast_le_one
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_natCast_le_one :=
  adicAbv_natCast_le_one
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_intCast_le_one := adicAbv_intCast_le_one
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_intCast_le_one :=
  adicAbv_intCast_le_one

end HeightOneSpectrum

open HeightOneSpectrum Valuation.IsRankOneDiscrete

set_option backward.isDefEq.respectTransparency.types false in
/-- The norm of an element in the `v`-adic completion of `K`. See `FinitePlace.norm_embedding`
for the equality involving `‖embedding v x‖` on the LHS. -/
/-
**NumberField.FinitePlace.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Finite
Place`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   [inst_5 : Module.Finite ℤ R] [ins
t_6 : Module.Free ℤ R] (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K 
v),   ‖x‖ = ↑((WithZeroMulInt.toNNReal ⋯) (Valued.v x))
参数：v : IsDedekindDomain.HeightOneSpectrum R；x : IsDedekindDomain.HeightOneSpectr
um.adicCompletion K v；(WithZeroMulInt.toNNReal ⋯) (Valued.v x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `NumberField.HeightOneSpectrum.absNorm_ne_zero`：absNorm_ne_zero : (absNor
m v.asIdeal : Real>=0) != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletion
V`：∀ {K : Type u_1} [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [inst_
2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFr…
· 使用引理 `Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_ap
ply_of_surjective`：valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
 (hsurj : Function.Surjective v) (x : R) : (valueGroup₀_equiv_withZeroMulInt v)…
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective`：valu
edAdicCompletion_surjective : Function.Surjective (Valued.v : (v.adicCompletion 
K) -> Intᵐ⁰)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The norm of an element in the `v`-adic completion of `K`. See `FinitePlace.norm_
embedding`
for the equality involving `‖embedding v x‖` on the LHS.
-/
theorem FinitePlace.norm_def (x : v.adicCompletion K) :
    ‖x‖ = toNNReal (absNorm_ne_zero v) (Valued.v x) := by
  simp [Valued.toNormedField.norm_def, Valuation.RankOne.hom, HeightOneSpectrum.rankOne_hom'_def,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (valuedAdicCompletion_surjective K v)]

/-- The norm of the image after the embedding associated to `v` is equal to the `v`-adic absolute
value. -/
/-
**NumberField.FinitePlace.norm_embedding** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
FinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   [inst_5 : Module.Finite ℤ R] [ins
t_6 : Module.Free ℤ R] (x : K),   ‖(NumberField.FinitePlace.embedding v) x‖ = (N
umberField.HeightOneSpectrum.adicAbv K v) x
参数：v : IsDedekindDomain.HeightOneSpectrum R；x : K；NumberField.FinitePlace.embedd
ing v；NumberField.HeightOneSpectrum.adicAbv K v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `NumberField.HeightOneSpectrum.absNorm_ne_zero`：absNorm_ne_zero : (absNor
m v.asIdeal : Real>=0) != 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `NumberField.FinitePlace.norm_def`：∀ {K : Type u_1} [inst : Field K] {R :
 Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R K]   [inst_3 : IsDedekindDo
main R] [inst_4 : IsFr…
· 使用定理 `Valued.valuedCompletion_apply`：valuedCompletion_apply (x : K) : Valued.v
 (x : hat K) = v x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The norm of the image after the embedding associated to `v` is equal to the `v`-
adic absolute
value.
-/
theorem FinitePlace.norm_embedding (x : K) : ‖embedding v x‖ = adicAbv K v x := by
  simp [norm_def, embedding_apply, adicAbv_def]

/-- The norm of the image after the embedding associated to `v` is equal to the norm of `v` raised
to the power of the `v`-adic valuation. -/
/-
**NumberField.FinitePlace.norm_embedding'** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.FinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   [inst_5 : Module.Finite ℤ R] [ins
t_6 : Module.Free ℤ R] (x : K),   ‖(NumberField.FinitePlace.embedding v) x‖ =   
  ↑((WithZeroMulInt.toNNReal ⋯) ((IsDedekindDomain.HeightOneSpectrum.valuation K
 v) x))
参数：v : IsDedekindDomain.HeightOneSpectrum R；x : K；NumberField.FinitePlace.embedd
ing v；(WithZeroMulInt.toNNReal ⋯) ((IsDedekindDomain.HeightOneSpectrum.valuation
 K v) x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.HeightOneSpectrum.absNorm_ne_zero`：absNorm_ne_zero : (absNor
m v.asIdeal : Real>=0) != 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.FinitePlace.norm_embedding`：∀ {K : Type u_1} [inst : Field K
] {R : Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R K]   [inst_3 : IsDede
kindDomain R] [inst_4 : IsFr…
· 使用定理 `NumberField.HeightOneSpectrum.adicAbv_def`：adicAbv_def {x : K} : adicAbv
 K v x = toNNReal (absNorm_ne_zero v) (v.valuation K x)

--- 原说明 ---
The norm of the image after the embedding associated to `v` is equal to the norm
 of `v` raised
to the power of the `v`-adic valuation.
-/
theorem FinitePlace.norm_embedding' (x : K) :
    ‖embedding v x‖ = toNNReal (absNorm_ne_zero v) (v.valuation K x) := by
  rw [norm_embedding, adicAbv_def]

variable (K)

/-- The norm of the image after the embedding associated to `v` is equal to the norm of `v` raised
to the power of the `v`-adic valuation for integers. -/
/-
**NumberField.FinitePlace.norm_embedding_int** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.FinitePlace`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   [inst_5 : Module.Finite ℤ R] [ins
t_6 : Module.Free ℤ R] (x : R),   ‖(NumberField.FinitePlace.embedding v) ((algeb
raMap R K) x)‖ = ↑((WithZeroMulInt.toNNReal ⋯) (v.intValuation x))
参数：K : Type u_1；v : IsDedekindDomain.HeightOneSpectrum R；x : R；NumberField.Finit
ePlace.embedding v；(algebraMap R K) x；(WithZeroMulInt.toNNReal ⋯) (v.intValuatio
n x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `NumberField.HeightOneSpectrum.absNorm_ne_zero`：absNorm_ne_zero : (absNor
m v.asIdeal : Real>=0) != 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.FinitePlace.norm_embedding`：∀ {K : Type u_1} [inst : Field K
] {R : Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R K]   [inst_3 : IsDede
kindDomain R] [inst_4 : IsFr…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The norm of the image after the embedding associated to `v` is equal to the norm
 of `v` raised
to the power of the `v`-adic valuation for integers.
-/
theorem FinitePlace.norm_embedding_int (x : R) :
    ‖embedding v (algebraMap _ K x)‖ = toNNReal (absNorm_ne_zero v) (v.intValuation x) := by
  simp [norm_embedding, adicAbv_def, valuation_of_algebraMap]

@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def' := FinitePlace.norm_embedding'
@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def_int :=
  FinitePlace.norm_embedding_int

open FinitePlace

/-- The `v`-adic norm of an integer is at most 1. -/
/-
**NumberField.FinitePlace.norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Fin
itePlace`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   [inst_5 : Module.Finite ℤ R] [ins
t_6 : Module.Free ℤ R] (x : R),   ‖(NumberField.FinitePlace.embedding v) ((algeb
raMap R K) x)‖ ≤ 1
参数：K : Type u_1；v : IsDedekindDomain.HeightOneSpectrum R；x : R；NumberField.Finit
ePlace.embedding v；(algebraMap R K) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.FinitePlace.norm_embedding`：∀ {K : Type u_1} [inst : Field K
] {R : Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R K]   [inst_3 : IsDede
kindDomain R] [inst_4 : IsFr…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one`：adicAbv_coe_le_on
e : v.adicAbv hb (algebraMap R K r) <= 1
· 使用引理 `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal`：one_lt_absNorm_nnre
al : 1 < (absNorm v.asIdeal : Real>=0)

--- 原说明 ---
The `v`-adic norm of an integer is at most 1.
-/
theorem FinitePlace.norm_le_one (x : R) : ‖embedding v (algebraMap _ K x)‖ ≤ 1 := by
  rw [norm_embedding]
  exact v.adicAbv_coe_le_one (one_lt_absNorm_nnreal v) x

/-- The `v`-adic norm of an integer is 1 if and only if it is not in the ideal. -/
/-
**NumberField.FinitePlace.norm_eq_one_iff_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.FinitePlace`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   [inst_5 : Module.Finite ℤ R] [ins
t_6 : Module.Free ℤ R] (x : R),   ‖(NumberField.FinitePlace.embedding v) ((algeb
raMap R K) x)‖ = 1 ↔ x ∉ v.asIdeal
参数：K : Type u_1；v : IsDedekindDomain.HeightOneSpectrum R；x : R；NumberField.Finit
ePlace.embedding v；(algebraMap R K) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.FinitePlace.norm_embedding`：∀ {K : Type u_1} [inst : Field K
] {R : Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R K]   [inst_3 : IsDede
kindDomain R] [inst_4 : IsFr…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff`：adicAbv_coe_e
q_one_iff : v.adicAbv hb (algebraMap R K r) = 1 ↔ r ∉ v.asIdeal
· 使用引理 `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal`：one_lt_absNorm_nnre
al : 1 < (absNorm v.asIdeal : Real>=0)

--- 原说明 ---
The `v`-adic norm of an integer is 1 if and only if it is not in the ideal.
-/
theorem FinitePlace.norm_eq_one_iff_notMem (x : R) :
    ‖embedding v (algebraMap _ K x)‖ = 1 ↔ x ∉ v.asIdeal := by
  rw [norm_embedding]
  exact v.adicAbv_coe_eq_one_iff (one_lt_absNorm_nnreal v) x

/-- The `v`-adic norm of an integer is less than 1 if and only if it is in the ideal. -/
/-
**NumberField.FinitePlace.norm_lt_one_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.FinitePlace`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   [inst_5 : Module.Finite ℤ R] [ins
t_6 : Module.Free ℤ R] (x : R),   ‖(NumberField.FinitePlace.embedding v) ((algeb
raMap R K) x)‖ < 1 ↔ x ∈ v.asIdeal
参数：K : Type u_1；v : IsDedekindDomain.HeightOneSpectrum R；x : R；NumberField.Finit
ePlace.embedding v；(algebraMap R K) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.FinitePlace.norm_embedding`：∀ {K : Type u_1} [inst : Field K
] {R : Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R K]   [inst_3 : IsDede
kindDomain R] [inst_4 : IsFr…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff`：adicAbv_coe_l
t_one_iff : v.adicAbv hb (algebraMap R K r) < 1 ↔ r in v.asIdeal
· 使用引理 `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal`：one_lt_absNorm_nnre
al : 1 < (absNorm v.asIdeal : Real>=0)

--- 原说明 ---
The `v`-adic norm of an integer is less than 1 if and only if it is in the ideal
.
-/
theorem FinitePlace.norm_lt_one_iff_mem (x : R) :
    ‖embedding v (algebraMap _ K x)‖ < 1 ↔ x ∈ v.asIdeal := by
  rw [norm_embedding]
  exact v.adicAbv_coe_lt_one_iff (one_lt_absNorm_nnreal v) x

set_option backward.isDefEq.respectTransparency false in
/-
**NumberField.HeightOneSpectrum.embedding_mul_absNorm** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.HeightOneSpectrum`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [in
st_2 : Algebra R K]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   [inst_5 : Module.Finite ℤ R] [ins
t_6 : Module.Free ℤ R] {x : R},   x ≠ 0 →     ‖(NumberField.FinitePlace.embeddin
g v) ((algebraMap R K) x)‖ *         ↑(Ideal.absNorm (v.maxPowDividing (Ideal.sp
an {x}))) =       1
参数：K : Type u_1；v : IsDedekindDomain.HeightOneSpectrum R；NumberField.FinitePlace
.embedding v；(algebraMap R K) x；Ideal.absNorm (v.maxPowDividing (Ideal.span {x})
)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.maxPowDividing.eq_1`：∀ {R : Type u_1}
 [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomain.HeightO
neSpectrum R)   (I : Ideal R), v.maxPowDivid…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `NumberField.FinitePlace.norm_embedding`：∀ {K : Type u_1} [inst : Field K
] {R : Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R K]   [inst_3 : IsDede
kindDomain R] [inst_4 : IsFr…
· 使用引理 `NumberField.HeightOneSpectrum.absNorm_ne_zero`：absNorm_ne_zero : (absNor
m v.asIdeal : Real>=0) != 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NumberField.HeightOneSpectrum.adicAbv_def`：adicAbv_def {x : K} : adicAbv
 K v x = toNNReal (absNorm_ne_zero v) (v.valuation K x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `FaithfulSMul.algebraMap_eq_zero_iff`：algebraMap_eq_zero_iff {r : R} : al
gebraMap R A r = 0 ↔ r = 0
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `WithZeroMulInt.toNNReal_neg_apply`：toNNReal_neg_apply {e : Real>=0} (he 
: e != 0) {x : Intᵐ⁰} (hx : x != 0) : toNNReal he x = e ^ (WithZero.unzero hx).t
oAdd
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用引理 `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal`：one_lt_absNorm_nnre
al : 1 < (absNorm v.asIdeal : Real>=0)
（共 48 条，此处仅展示前 30 条）
-/
lemma HeightOneSpectrum.embedding_mul_absNorm {x : R} (h_x_nezero : x ≠ 0) :
    ‖embedding v (algebraMap _ K x)‖ * absNorm (v.maxPowDividing (span {x})) = 1 := by
  rw [maxPowDividing, map_pow, Nat.cast_pow, norm_embedding, adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ ((v.valuation K).ne_zero_iff.mpr
      ((FaithfulSMul.algebraMap_eq_zero_iff R K).not.2 h_x_nezero))]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ <| mod_cast (zero_lt_one.trans (one_lt_absNorm_nnreal v)).ne']
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' _) (mod_cast (one_lt_absNorm_nnreal v).ne')]
  simp [valuation_of_algebraMap, intValuation_if_neg, h_x_nezero]

end FiniteFree

end AbsoluteValue

open HeightOneSpectrum

/-- A finite place of a number field `K` is a place associated to an embedding into a completion
with respect to a maximal ideal. -/
/-
**NumberField.FinitePlace** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：FinitePlace (K : Type*) [Field K] [NumberField K]
参数：K : Type*。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
A finite place of a number field `K` is a place associated to an embedding into 
a completion
with respect to a maximal ideal.
-/
def FinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : AbsoluteValue K ℝ // ∃ v : HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w}

/-- Return the finite place defined by a maximal ideal `v`. -/
/-
**NumberField.FinitePlace.mk** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.FinitePlace`
。
形式化陈述：{K : Type u_1} →   [inst : Field K] →     [inst_1 : NumberField K] →      
 IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → NumberField
.FinitePlace K
参数：NumberField.RingOfIntegers K。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
Return the finite place defined by a maximal ideal `v`.
-/
noncomputable def FinitePlace.mk [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : FinitePlace K :=
  ⟨place (embedding v), ⟨v, rfl⟩⟩

/-- A predicate singling out finite places among the absolute values on a number field `K`. -/
/-
**NumberField.IsFinitePlace** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：IsFinitePlace [NumberField K] (w : AbsoluteValue K Real) : Prop
参数：w : AbsoluteValue K Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
A predicate singling out finite places among the absolute values on a number fie
ld `K`.
-/
def IsFinitePlace [NumberField K] (w : AbsoluteValue K ℝ) : Prop :=
  ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w
/-
**NumberField.FinitePlace.isFinitePlace** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.F
initePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (v : NumberFiel
d.FinitePlace K), NumberField.IsFinitePlace ↑v
参数：v : NumberField.FinitePlace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
-/
lemma FinitePlace.isFinitePlace [NumberField K] (v : FinitePlace K) : IsFinitePlace v.val := by
  simp [IsFinitePlace, v.prop]
/-
**NumberField.isFinitePlace_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：isFinitePlace_iff [NumberField K] (v : AbsoluteValue K Real) : IsFinitePla
ce v ↔ exists w : FinitePlace K, w.val = v
参数：v : AbsoluteValue K Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.FinitePlace.isFinitePlace`：∀ {K : Type u_1} [inst : Field K]
 [inst_1 : NumberField K] (v : NumberField.FinitePlace K), NumberField.IsFiniteP
lace ↑v
-/
lemma isFinitePlace_iff [NumberField K] (v : AbsoluteValue K ℝ) :
    IsFinitePlace v ↔ ∃ w : FinitePlace K, w.val = v :=
  ⟨fun H ↦ ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ ↦ hw ▸ w.isFinitePlace⟩

namespace FinitePlace

variable [NumberField K]

/-
**NumberField.FinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.FinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (FinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext <| congr_fun h)
/-
**NumberField.FinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.FinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidWithZeroHomClass (FinitePlace K) K ℝ where
  map_mul w := w.1.map_mul
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero
/-
**NumberField.FinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.FinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonnegHomClass (FinitePlace K) K ℝ where
  apply_nonneg w := w.1.nonneg

@[simp]
/-
**NumberField.FinitePlace.mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Finite
Place`。
形式化陈述：mk_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) : mk v x = ‖embedding v x‖
参数：v : HeightOneSpectrum (𝓞 K)；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) : mk v x = ‖embedding v x‖ := rfl
/-
**NumberField.FinitePlace.coe_apply** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.Finit
ePlace`。
形式化陈述：coe_apply (v : FinitePlace K) (x : K) : v x = v.val x
参数：v : FinitePlace K；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_apply (v : FinitePlace K) (x : K) : v x = v.val x := rfl
/-
**NumberField.FinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.FinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulRingNormClass (FinitePlace K) K ℝ where
  map_add_le_add v x y := by simpa [coe_apply] using IsAbsoluteValue.abv_add' x y
  map_neg_eq_map v x := by simp [coe_apply]
  eq_zero_of_map_eq_zero v := by simp

/-- For a finite place `w`, return a maximal ideal `v` such that `w = finite_place v` . -/
/-
**NumberField.FinitePlace.maximalIdeal** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Fi
nitePlace`。
形式化陈述：maximalIdeal (w : FinitePlace K) : HeightOneSpectrum (𝓞 K)
参数：w : FinitePlace K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
For a finite place `w`, return a maximal ideal `v` such that `w = finite_place v
` .
-/
noncomputable def maximalIdeal (w : FinitePlace K) : HeightOneSpectrum (𝓞 K) := w.2.choose

@[simp]
/-
**NumberField.FinitePlace.mk_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.FinitePlace`。
形式化陈述：mk_maximalIdeal (w : FinitePlace K) : mk (maximalIdeal w) = w
参数：w : FinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mk_maximalIdeal (w : FinitePlace K) : mk (maximalIdeal w) = w := Subtype.ext w.2.choose_spec

@[simp]
/-
**NumberField.FinitePlace.norm_embedding_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.FinitePlace`。
形式化陈述：norm_embedding_eq (w : FinitePlace K) (x : K) : ‖embedding (maximalIdeal w
) x‖ = w x
参数：w : FinitePlace K；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.FinitePlace.mk_maximalIdeal`：mk_maximalIdeal (w : FinitePlac
e K) : mk (maximalIdeal w) = w
· 使用定理 `NumberField.FinitePlace.mk_apply`：mk_apply (v : HeightOneSpectrum (𝓞 K))
 (x : K) : mk v x = ‖embedding v x‖
-/
theorem norm_embedding_eq (w : FinitePlace K) (x : K) :
    ‖embedding (maximalIdeal w) x‖ = w x := by
  conv_rhs => rw [← mk_maximalIdeal w, mk_apply]
/-
**NumberField.FinitePlace.pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.FiniteP
lace`。
形式化陈述：pos_iff {w : FinitePlace K} {x : K} : 0 < w x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.pos_iff`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, 0 <…
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
-/
theorem pos_iff {w : FinitePlace K} {x : K} : 0 < w x ↔ x ≠ 0 := w.1.pos_iff

@[simp]
/-
**NumberField.FinitePlace.mk_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Finit
ePlace`。
形式化陈述：mk_eq_iff {v₁ v₂ : HeightOneSpectrum (𝓞 K)} : mk v₁ = mk v₂ ↔ v₁ = v₂
参数：𝓞 K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ext_iff`：∀ {R : Type u_1} {inst : Com
mRing R} {x y : IsDedekindDomain.HeightOneSpectrum R}, x = y ↔ x.asIdeal = y.asI
deal
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 55 条，此处仅展示前 30 条）
-/
theorem mk_eq_iff {v₁ v₂ : HeightOneSpectrum (𝓞 K)} : mk v₁ = mk v₂ ↔ v₁ = v₂ := by
  refine ⟨?_, fun a ↦ by rw [a]⟩
  contrapose!
  intro h
  rw [DFunLike.ne_iff]
  have ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact h <| HeightOneSpectrum.ext_iff.mpr <| IsMaximal.eq_of_le (isMaximal v₁) IsPrime.ne_top' H
  use x
  simp only [mk_apply]
  rw [← norm_lt_one_iff_mem K] at hx1
  rw [← norm_eq_one_iff_notMem K] at hx2
  linarith
/-
**NumberField.FinitePlace.maximalIdeal_mk** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.FinitePlace`。
形式化陈述：maximalIdeal_mk (v : HeightOneSpectrum (𝓞 K)) : maximalIdeal (mk v) = v
参数：v : HeightOneSpectrum (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.FinitePlace.mk_eq_iff`：mk_eq_iff {v₁ v₂ : HeightOneSpectrum 
(𝓞 K)} : mk v₁ = mk v₂ ↔ v₁ = v₂
· 使用定理 `NumberField.FinitePlace.mk_maximalIdeal`：mk_maximalIdeal (w : FinitePlac
e K) : mk (maximalIdeal w) = w
-/
theorem maximalIdeal_mk (v : HeightOneSpectrum (𝓞 K)) : maximalIdeal (mk v) = v := by
  rw [← mk_eq_iff, mk_maximalIdeal]

/-- The equivalence between finite places and maximal ideals. -/
@[simps apply]
/-
**NumberField.FinitePlace.equivHeightOneSpectrum** 是 Mathlib 中的一个定义，位于命名空间 `Numb
erField.FinitePlace`。
形式化陈述：equivHeightOneSpectrum : FinitePlace K ≃ HeightOneSpectrum (𝓞 K) where toF
un
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.FinitePlace.mk_maximalIdeal`：mk_maximalIdeal (w : FinitePlac
e K) : mk (maximalIdeal w) = w
· 使用定理 `NumberField.FinitePlace.maximalIdeal_mk`：maximalIdeal_mk (v : HeightOneS
pectrum (𝓞 K)) : maximalIdeal (mk v) = v

--- 原说明 ---
The equivalence between finite places and maximal ideals.
-/
noncomputable def equivHeightOneSpectrum :
    FinitePlace K ≃ HeightOneSpectrum (𝓞 K) where
  toFun := maximalIdeal
  invFun := mk
  left_inv := mk_maximalIdeal
  right_inv := maximalIdeal_mk
/-
**NumberField.FinitePlace.maximalIdeal_injective** 是 Mathlib 中的一个引理，位于命名空间 `Numb
erField.FinitePlace`。
形式化陈述：maximalIdeal_injective : (fun w : FinitePlace K => maximalIdeal w).Injecti
ve
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma maximalIdeal_injective : (fun w : FinitePlace K ↦ maximalIdeal w).Injective :=
  equivHeightOneSpectrum.injective
/-
**NumberField.FinitePlace.maximalIdeal_inj** 是 Mathlib 中的一个引理，位于命名空间 `NumberFiel
d.FinitePlace`。
形式化陈述：maximalIdeal_inj (w₁ w₂ : FinitePlace K) : maximalIdeal w₁ = maximalIdeal 
w₂ ↔ w₁ = w₂
参数：w₁ w₂ : FinitePlace K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma maximalIdeal_inj (w₁ w₂ : FinitePlace K) : maximalIdeal w₁ = maximalIdeal w₂ ↔ w₁ = w₂ :=
  equivHeightOneSpectrum.injective.eq_iff

@[fun_prop]
/-
**NumberField.FinitePlace.hasFiniteMulSupport_int** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.FinitePlace`。
形式化陈述：hasFiniteMulSupport_int {x : 𝓞 K} (h_x_nezero : x != 0) : (fun w : FiniteP
lace K => w x).HasFiniteMulSupport
参数：h_x_nezero : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ne_iff_lt_iff_le`：ne_iff_lt_iff_le : (a != b ↔ a < b) ↔ a <= b
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.FinitePlace.norm_le_one`：∀ (K : Type u_1) [inst : Field K] {
R : Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R K]   [inst_3 : IsDedekin
dDomain R] [inst_4 : IsFr…
· 使用定理 `NumberField.FinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Finite
Place K) (x : K) : ‖embedding (maximalIdeal w) x‖ = w x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.finite_factors`：Ideal.finite_factors {I : Ideal R} (hI : I != 0) :
 {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `NumberField.FinitePlace.maximalIdeal_injective`：maximalIdeal_injective :
 (fun w : FinitePlace K => maximalIdeal w).Injective
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem hasFiniteMulSupport_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (fun w : FinitePlace K ↦ w x).HasFiniteMulSupport := by
  have (w : FinitePlace K) : w x ≠ 1 ↔ w x < 1 :=
    ne_iff_lt_iff_le.mpr <| norm_embedding_eq w x ▸ norm_le_one K w.maximalIdeal x
  simp_rw [Function.HasFiniteMulSupport, Function.mulSupport, this, ← norm_embedding_eq,
    norm_lt_one_iff_mem, ← Ideal.dvd_span_singleton]
  have h : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}}.Finite := by
    apply Ideal.finite_factors
    simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, h_x_nezero, not_false_eq_true]
  have h_inj : Set.InjOn FinitePlace.maximalIdeal {w | w.maximalIdeal.asIdeal ∣ span {x}} :=
    Function.Injective.injOn maximalIdeal_injective
  refine (h.subset ?_).of_finite_image h_inj
  simp only [dvd_span_singleton, Set.image_subset_iff, Set.preimage_ofPred_eq, subset_refl]

@[deprecated (since := "2026-03-03")] alias mulSupport_finite_int := hasFiniteMulSupport_int

@[fun_prop]
/-
**NumberField.FinitePlace.hasFiniteMulSupport** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.FinitePlace`。
形式化陈述：hasFiniteMulSupport {x : K} (h_x_nezero : x != 0) : (fun w : FinitePlace K
 => w x).HasFiniteMulSupport
参数：h_x_nezero : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `NumberField.FinitePlace.instMonoidWithZeroHomClassReal`：∀ {K : Type u_1}
 [inst : Field K] [inst_1 : NumberField K], MonoidWithZeroHomClass (NumberField.
FinitePlace K) K ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree_2`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   Module.IsT
orsionFree (NumberField.RingOfIntege…
· 使用定理 `Function.HasFiniteMulSupport.fun_div`：∀ {α : Type u_1} {M : Type u_3} [i
nst : DivisionMonoid M] {f g : α → M},   Function.HasFiniteMulSupport f → Functi
on.HasFiniteMulSupport g →…
· 使用定理 `NumberField.FinitePlace.hasFiniteMulSupport_int`：hasFiniteMulSupport_int
 {x : 𝓞 K} (h_x_nezero : x != 0) : (fun w : FinitePlace K => w x).HasFiniteMulSu
pport
-/
theorem hasFiniteMulSupport {x : K} (h_x_nezero : x ≠ 0) :
    (fun w : FinitePlace K ↦ w x).HasFiniteMulSupport := by
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨a, b, hb, rfl⟩
  simp_all only [ne_eq, div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or, map_div₀]
  obtain ⟨ha, hb⟩ := h_x_nezero
  simp_rw [← RingOfIntegers.coe_eq_algebraMap]
  fun_prop

@[deprecated (since := "2026-03-03")] alias mulSupport_finite := hasFiniteMulSupport
/-
**NumberField.FinitePlace.hasFiniteMulSupport_fun_pow_multiplicity** 是 Mathlib 中
的一个引理，位于命名空间 `NumberField.FinitePlace`。
形式化陈述：hasFiniteMulSupport_fun_pow_multiplicity {M : Type*} [CommMonoid M] {I : I
deal (𝓞 K)} (hI : I != ⊥) (f : Ideal (𝓞 K) -> M) : (fun v : FinitePlace K => f v
.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I).HasFiniteMulSuppo
rt
参数：𝓞 K；hI : I != ⊥；f : Ideal (𝓞 K) -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity`：hasF
initeMulSupport_fun_pow_multiplicity {α M : Type*} [CommMonoid M] [Subsingleton 
Rˣ] (f : α -> M) {g : α -> R} (hgi : g.Injective) (hg : …
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.asIdeal_injective`：asIdeal_injective 
: (HeightOneSpectrum.asIdeal (R
· 使用引理 `NumberField.FinitePlace.maximalIdeal_injective`：maximalIdeal_injective :
 (fun w : FinitePlace K => maximalIdeal w).Injective
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
-/
lemma hasFiniteMulSupport_fun_pow_multiplicity {M : Type*} [CommMonoid M] {I : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) (f : Ideal (𝓞 K) → M) :
    (fun v : FinitePlace K ↦
      f v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I).HasFiniteMulSupport :=
  UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity _
    (asIdeal_injective.comp maximalIdeal_injective) (fun v ↦ v.maximalIdeal.irreducible) hI

protected
/-
**NumberField.FinitePlace.add_le** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.FinitePl
ace`。
形式化陈述：add_le (v : FinitePlace K) (x y : K) : v (x + y) <= max (v x) (v y)
参数：v : FinitePlace K；x y : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.HeightOneSpectrum.adicAbv_add_le_max`：adicAbv_add_le_max (x 
y : K) : adicAbv K v (x + y) <= (adicAbv K v x) ⊔ (adicAbv K v y)
-/
lemma add_le (v : FinitePlace K) (x y : K) :
    v (x + y) ≤ max (v x) (v y) := by
  obtain ⟨w, hw⟩ := v.prop
  have H x : v x = NumberField.HeightOneSpectrum.adicAbv K w x := by
    rw [show v x = v.val x from rfl]
    grind only [place_apply, norm_embedding]
  simpa only [H] using adicAbv_add_le_max K w x y
/-
**NumberField.FinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.FinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonarchimedeanHomClass (FinitePlace K) K ℝ where
  map_add_le_max v a b := FinitePlace.add_le v a b
/-
**NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply** 是 Mathlib 中的一个引理，位
于命名空间 `NumberField.FinitePlace`。
形式化陈述：equivHeightOneSpectrum_symm_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) : 
(equivHeightOneSpectrum.symm v) x = ‖embedding v x‖
参数：v : HeightOneSpectrum (𝓞 K)；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma equivHeightOneSpectrum_symm_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (equivHeightOneSpectrum.symm v) x = ‖embedding v x‖ := rfl

@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.equivHeightOneSpectrum_symm_apply :=
  equivHeightOneSpectrum_symm_apply
@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm := embedding_mul_absNorm
/-
**NumberField.FinitePlace.finprod_finitePlace_pow_multiplicity** 是 Mathlib 中的一个引
理，位于命名空间 `NumberField.FinitePlace`。
形式化陈述：finprod_finitePlace_pow_multiplicity {I : Ideal (𝓞 K)} (hI : I != ⊥) : ∏ᶠ 
v : FinitePlace K, v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal 
I = I
参数：𝓞 K；hI : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.finprod_heightOneSpectrum_pow_multiplicity`：Ideal.finprod_heightOn
eSpectrum_pow_multiplicity {I : Ideal R} (hI : I != ⊥) : ∏ᶠ p : HeightOneSpectru
m R, p.asIdeal ^ multiplicity p.asIdea…
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `finprod_comp_equiv`：finprod_comp_equiv (e : α ≃ β) {f : β -> M} : (∏ᶠ i,
 f (e i)) = ∏ᶠ i', f i'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.FinitePlace.equivHeightOneSpectrum_apply`：∀ {K : Type u_1} [
inst : Field K] [inst_1 : NumberField K] (w : NumberField.FinitePlace K),   Numb
erField.FinitePlace.equivHeightOneSpectrum…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finprod_finitePlace_pow_multiplicity {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∏ᶠ v : FinitePlace K, v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I = I := by
  conv_rhs => rw [← finprod_heightOneSpectrum_pow_multiplicity hI]
  simp only [← finprod_comp_equiv (equivHeightOneSpectrum (K := K)), equivHeightOneSpectrum_apply]
/-
**NumberField.FinitePlace.apply_mul_absNorm_pow_eq_one** 是 Mathlib 中的一个引理，位于命名空间
 `NumberField.FinitePlace`。
形式化陈述：apply_mul_absNorm_pow_eq_one (v : FinitePlace K) {x : 𝓞 K} (hx : x != 0) :
 v x * v.maximalIdeal.asIdeal.absNorm ^ multiplicity v.maximalIdeal.asIdeal (spa
n {x}) = 1
参数：v : FinitePlace K；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.span_singleton_eq_bot`：span_singleton_eq_bot : R ∙ x = ⊥ ↔ x =
 0
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.FinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Finite
Place K) (x : K) : ‖embedding (maximalIdeal w) x‖ = w x
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity`：m
axPowDividing_eq_pow_multiplicity : p.maxPowDividing I = p.asIdeal ^ multiplicit
y p.asIdeal I
· 使用定理 `NumberField.HeightOneSpectrum.embedding_mul_absNorm`：∀ (K : Type u_1) [i
nst : Field K] {R : Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R K]   [in
st_3 : IsDedekindDomain R] [inst_4 : IsFr…
-/
lemma apply_mul_absNorm_pow_eq_one (v : FinitePlace K) {x : 𝓞 K} (hx : x ≠ 0) :
    v x * v.maximalIdeal.asIdeal.absNorm ^ multiplicity v.maximalIdeal.asIdeal (span {x}) = 1 := by
  have hnz : span {x} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  rw [← norm_embedding_eq v x, ← Nat.cast_pow, ← map_pow, ← maxPowDividing_eq_pow_multiplicity hnz]
  exact HeightOneSpectrum.embedding_mul_absNorm K v.maximalIdeal hx

end FinitePlace

section LiesOver

namespace HeightOneSpectrum

variable {L : Type*} [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

local notation "Kv" => v.adicCompletion K
local notation "Lw" => w.adicCompletion L

open scoped TensorProduct Valued in
/-
**NumberField.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.HeightOn
eSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite Kv Lw :=
  let Φ : Kv ⊗[K] L →ₗ[Kv] Lw := Algebra.TensorProduct.lift (Algebra.algHom Kv Kv Lw)
    (Algebra.algHom K L Lw) (fun _ _ ↦ mul_comm ..) |>.toLinearMap
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, Algebra.algHom]⟩
  .of_surjective Φ (by
    rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range)

end HeightOneSpectrum

end LiesOver

end NumberField

