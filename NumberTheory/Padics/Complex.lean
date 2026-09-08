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

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- `PadicAlgCl p` is a fixed algebraic closure of `ℚ_[p]`. -/
/-
**PadicAlgCl** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PadicAlgCl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PadicAlgCl p` is a fixed algebraic closure of `ℚ_[p]`.
-/
abbrev PadicAlgCl := AlgebraicClosure ℚ_[p]

namespace PadicAlgCl

/-- `PadicAlgCl p` is an algebraic extension of `ℚ_[p]`. -/
/-
**PadicAlgCl.isAlgebraic** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
形式化陈述：isAlgebraic : Algebra.IsAlgebraic Rat_[p] (PadicAlgCl p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PadicAlgCl p` is an algebraic extension of `ℚ_[p]`.
-/
instance isAlgebraic : Algebra.IsAlgebraic ℚ_[p] (PadicAlgCl p) := AlgebraicClosure.isAlgebraic _
/-
**PadicAlgCl.** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe ℚ_[p] (PadicAlgCl p) := ⟨algebraMap ℚ_[p] (PadicAlgCl p)⟩
/-
**PadicAlgCl.coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `PadicAlgCl`。
形式化陈述：coe_eq : (Coe.coe : Rat_[p] -> PadicAlgCl p) = algebraMap Rat_[p] (PadicAl
gCl p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eq : (Coe.coe : ℚ_[p] → PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) := rfl

/-- `PadicAlgCl p` is a normed field, where the norm is the `p`-adic norm, that is, the
spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
/-
**PadicAlgCl.normedField** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
形式化陈述：normedField : NormedField (PadicAlgCl p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.instIsUltrametricDist`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], IsUl
trametricDist ℚ_[p]
· 使用定理 `Padic.instCompleteSpace`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], CompleteSp
ace ℚ_[p]

--- 原说明 ---
`PadicAlgCl p` is a normed field, where the norm is the `p`-adic norm, that is, 
the
spectral norm induced by the `p`-adic norm on `ℚ_[p]`.
-/
instance normedField : NormedField (PadicAlgCl p) := spectralNorm.normedField ℚ_[p] (PadicAlgCl p)

/-- The norm on `PadicAlgCl p` is nonarchimedean. -/
/-
**PadicAlgCl.isNonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `PadicAlgCl`。
形式化陈述：isNonarchimedean : IsNonarchimedean (norm : PadicAlgCl p -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNonarchimedean_spectralNorm`：isNonarchimedean_spectralNorm : IsNonarch
imedean (spectralNorm K L)
· 使用定理 `Padic.instIsUltrametricDist`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], IsUl
trametricDist ℚ_[p]

--- 原说明 ---
The norm on `PadicAlgCl p` is nonarchimedean.
-/
theorem isNonarchimedean : IsNonarchimedean (norm : PadicAlgCl p → ℝ) :=
  isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := PadicAlgCl p)

/-- `PadicAlgCl p` is a normed algebra over `ℚ_[p]`. -/
/-
**PadicAlgCl.normedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
形式化陈述：normedAlgebra : NormedAlgebra Rat_[p] (PadicAlgCl p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.instIsUltrametricDist`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], IsUl
trametricDist ℚ_[p]
· 使用定理 `Padic.instCompleteSpace`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], CompleteSp
ace ℚ_[p]

--- 原说明 ---
`PadicAlgCl p` is a normed algebra over `ℚ_[p]`.
-/
instance normedAlgebra : NormedAlgebra ℚ_[p] (PadicAlgCl p) := spectralNorm.normedAlgebra _ _

/-- The norm on `PadicAlgCl p` is the spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
@[simp]
/-
**PadicAlgCl.spectralNorm_eq** 是 Mathlib 中的一个定理，位于命名空间 `PadicAlgCl`。
形式化陈述：spectralNorm_eq (x : PadicAlgCl p) : spectralNorm Rat_[p] (PadicAlgCl p) x
 = ‖x‖
参数：x : PadicAlgCl p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm on `PadicAlgCl p` is the spectral norm induced by the `p`-adic norm on 
`ℚ_[p]`.
-/
theorem spectralNorm_eq (x : PadicAlgCl p) : spectralNorm ℚ_[p] (PadicAlgCl p) x = ‖x‖ := rfl

/-- The norm on `PadicAlgCl p` extends the `p`-adic norm on `ℚ_[p]`. -/
/-
**PadicAlgCl.norm_extends** 是 Mathlib 中的一个定理，位于命名空间 `PadicAlgCl`。
形式化陈述：norm_extends (x : Rat_[p]) : ‖(x : PadicAlgCl p)‖ = ‖x‖
参数：x : Rat_[p]。
该定理/引理给出了一组等式。
继承自：(x : Rat_[p]) : ‖(x : PadicAlgCl p)‖ = ‖x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The norm on `PadicAlgCl p` extends the `p`-adic norm on `ℚ_[p]`.
-/
theorem norm_extends (x : ℚ_[p]) : ‖(x : PadicAlgCl p)‖ = ‖x‖ := by
  simp

/-- The underlying metric space of `PadicAlgCl p` is ultrametric. -/
/-
**PadicAlgCl.isUltrametricDist** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
形式化陈述：isUltrametricDist : IsUltrametricDist (PadicAlgCl p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm`：∀ {S
' : Type u_2} [inst : SeminormedAddGroup S'], (∀ (x y : S'), ‖x + y‖ ≤ max ‖x‖ ‖
y‖) → IsUltrametricDist S'
· 使用定理 `PadicAlgCl.isNonarchimedean`：isNonarchimedean : IsNonarchimedean (norm :
 PadicAlgCl p -> Real)

--- 原说明 ---
The underlying metric space of `PadicAlgCl p` is ultrametric.
-/
instance isUltrametricDist : IsUltrametricDist (PadicAlgCl p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (PadicAlgCl.isNonarchimedean p)

/-- `PadicAlgCl p` is a valued field, with the valuation corresponding to the `p`-adic norm. -/
/-
**PadicAlgCl.valued** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
形式化陈述：valued : Valued (PadicAlgCl p) Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PadicAlgCl p` is a valued field, with the valuation corresponding to the `p`-ad
ic norm.
-/
instance valued : Valued (PadicAlgCl p) ℝ≥0 := NormedField.toValued

/-- The valuation of `x : PadicAlgCl p` agrees with its `ℝ≥0`-valued norm. -/
/-
**PadicAlgCl.valuation_def** 是 Mathlib 中的一个定理，位于命名空间 `PadicAlgCl`。
形式化陈述：valuation_def (x : PadicAlgCl p) : Valued.v x = ‖x‖₊
参数：x : PadicAlgCl p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation of `x : PadicAlgCl p` agrees with its `ℝ≥0`-valued norm.
-/
theorem valuation_def (x : PadicAlgCl p) : Valued.v x = ‖x‖₊ := rfl

/-- The coercion of the valuation of `x : PadicAlgCl p` to `ℝ` agrees with its norm. -/
/-
**PadicAlgCl.valuation_coe** 是 Mathlib 中的一个定理，位于命名空间 `PadicAlgCl`。
形式化陈述：valuation_coe (x : PadicAlgCl p) : ((Valued.v x : Real>=0) : Real) = ‖x‖
参数：x : PadicAlgCl p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion of the valuation of `x : PadicAlgCl p` to `ℝ` agrees with its norm.
-/
theorem valuation_coe (x : PadicAlgCl p) : ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := rfl

/-- The valuation of `p : PadicAlgCl p` is `1/p`. -/
/-
**PadicAlgCl.valuation_p** 是 Mathlib 中的一个定理，位于命名空间 `PadicAlgCl`。
形式化陈述：valuation_p (p : Nat) [Fact p.Prime] : Valued.v (p : PadicAlgCl p) = 1 / (
p : Real>=0)
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `PadicAlgCl.valuation_coe`：valuation_coe (x : PadicAlgCl p) : ((Valued.v 
x : Real>=0) : Real) = ‖x‖
· 使用定理 `PadicAlgCl.norm_extends`：norm_extends (x : Rat_[p]) : ‖(x : PadicAlgCl p
)‖ = ‖x‖
· 使用定理 `Padic.norm_p`：norm_p : ‖(p : Rat_[p])‖ = (p : Real)⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.coe_inv`：∀ (r : NNReal), ↑r⁻¹ = (↑r)⁻¹
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n

--- 原说明 ---
The valuation of `p : PadicAlgCl p` is `1/p`.
-/
theorem valuation_p (p : ℕ) [Fact p.Prime] : Valued.v (p : PadicAlgCl p) = 1 / (p : ℝ≥0) := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]
  ext
  rw [valuation_coe, norm_extends, Padic.norm_p, one_div, NNReal.coe_inv,
    NNReal.coe_natCast]

open MonoidWithZeroHom.ValueGroup₀

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The valuation on `PadicAlgCl p` has rank one. -/
/-
**PadicAlgCl.** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation on `PadicAlgCl p` has rank one.
-/
instance : RankOne (PadicAlgCl.valued p).v where
  hom'        := embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩
/-
**PadicAlgCl.** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformContinuousConstSMul ℚ_[p] (PadicAlgCl p) :=
  uniformContinuousConstSMul_of_continuousConstSMul ℚ_[p] (PadicAlgCl p)

/-- The norm on `PadicAlgCl p` is nontrivial. -/
/-
**PadicAlgCl.nontriviallyNormedField** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
形式化陈述：nontriviallyNormedField : NontriviallyNormedField (PadicAlgCl p) where non
_trivial
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm on `PadicAlgCl p` is nontrivial.
-/
instance nontriviallyNormedField : NontriviallyNormedField (PadicAlgCl p) where
  non_trivial := by
    choose x hx using NontriviallyNormedField.non_trivial (α := ℚ_[p])
    use x
    rw [PadicAlgCl.norm_extends]
    exact hx

/-- `PadicAlgCl p` has characteristic zero. -/
/-
**PadicAlgCl.charZero** 是 Mathlib 中的一个实例，位于命名空间 `PadicAlgCl`。
形式化陈述：charZero : CharZero (PadicAlgCl p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.charZero_iff`：charZero_iff {ϕ : R ->+* S} (hϕ : Injective ϕ) : C
harZero R ↔ CharZero S
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]

--- 原说明 ---
`PadicAlgCl p` has characteristic zero.
-/
instance charZero : CharZero (PadicAlgCl p) :=
  (RingHom.charZero_iff (algebraMap ℚ_[p] (PadicAlgCl p)).injective).mp inferInstance

end PadicAlgCl

/-- `ℂ_[p]` is the field of `p`-adic complex numbers, that is, the completion of `PadicAlgCl p` with
respect to the `p`-adic norm. -/
/-
**PadicComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PadicComplex
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℂ_[p]` is the field of `p`-adic complex numbers, that is, the completion of `Pa
dicAlgCl p` with
respect to the `p`-adic norm.
-/
abbrev PadicComplex := UniformSpace.Completion (PadicAlgCl p)

/-- `ℂ_[p]` is the field of `p`-adic complex numbers. -/
notation "ℂ_[" p "]" => PadicComplex p

namespace PadicComplex

/-- `ℂ_[p]` is a valued field, where the valuation is the one extending that on `PadicAlgCl p`. -/
/-
**PadicComplex.valued** 是 Mathlib 中的一个实例，位于命名空间 `PadicComplex`。
形式化陈述：valued : Valued Complex_[p] Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℂ_[p]` is a valued field, where the valuation is the one extending that on `Pad
icAlgCl p`.
-/
instance valued : Valued ℂ_[p] ℝ≥0 := Valued.valuedCompletion

/-- The valuation on `ℂ_[p]` extends the valuation on `PadicAlgCl p`. -/
/-
**PadicComplex.valuation_extends** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：valuation_extends (x : PadicAlgCl p) : Valued.v (x : Complex_[p]) = Valued
.v x
参数：x : PadicAlgCl p。
该定理/引理给出了一组等式。
继承自：(x : PadicAlgCl p) : Valued.v (x : Complex_[p]) = Valued.v x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valued.extensionValuation_apply_coe`：extensionValuation_apply_coe (x : K
) : Valued.extensionValuation (x : hat K) = v x

--- 原说明 ---
The valuation on `ℂ_[p]` extends the valuation on `PadicAlgCl p`.
-/
theorem valuation_extends (x : PadicAlgCl p) : Valued.v (x : ℂ_[p]) = Valued.v x :=
  Valued.extensionValuation_apply_coe _
/-
**PadicComplex.coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：coe_eq (x : PadicAlgCl p) : (x : Complex_[p]) = algebraMap (PadicAlgCl p) 
Complex_[p] x
参数：x : PadicAlgCl p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eq (x : PadicAlgCl p) : (x : ℂ_[p]) = algebraMap (PadicAlgCl p) ℂ_[p] x := rfl
/-
**PadicComplex.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], ↑0 = 0
参数：p : ℕ；Nat.Prime p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_zero : ((0 : PadicAlgCl p) : ℂ_[p]) = 0 := rfl
/-
**PadicComplex.** 是 Mathlib 中的一个实例，位于命名空间 `PadicComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower ℚ_[p] (PadicAlgCl p) ℂ_[p] := IsScalarTower.of_algebraMap_eq (congrFun rfl)

@[simp, norm_cast]
/-
**PadicComplex.coe_natCast** 是 Mathlib 中的一个引理，位于命名空间 `PadicComplex`。
形式化陈述：coe_natCast (n : Nat) : ((n : PadicAlgCl p) : Complex_[p]) = (n : Complex_
[p])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `PadicComplex.coe_eq`：coe_eq (x : PadicAlgCl p) : (x : Complex_[p]) = alg
ebraMap (PadicAlgCl p) Complex_[p] x
-/
lemma coe_natCast (n : ℕ) : ((n : PadicAlgCl p) : ℂ_[p]) = (n : ℂ_[p]) := by
  rw [← map_natCast (algebraMap (PadicAlgCl p) ℂ_[p]) n, coe_eq]

/-- The valuation of `p : ℂ_[p]` is `1/p`. -/
/-
**PadicComplex.valuation_p** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：valuation_p : Valued.v (p : Complex_[p]) = 1 / (p : Real>=0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `PadicComplex.coe_eq`：coe_eq (x : PadicAlgCl p) : (x : Complex_[p]) = alg
ebraMap (PadicAlgCl p) Complex_[p] x
· 使用定理 `PadicComplex.valuation_extends`：valuation_extends (x : PadicAlgCl p) : V
alued.v (x : Complex_[p]) = Valued.v x
· 使用定理 `PadicAlgCl.valuation_p`：valuation_p (p : Nat) [Fact p.Prime] : Valued.v 
(p : PadicAlgCl p) = 1 / (p : Real>=0)

--- 原说明 ---
The valuation of `p : ℂ_[p]` is `1/p`.
-/
theorem valuation_p : Valued.v (p : ℂ_[p]) = 1 / (p : ℝ≥0) := by
  rw [← map_natCast (algebraMap (PadicAlgCl p) ℂ_[p]), ← coe_eq, valuation_extends,
    PadicAlgCl.valuation_p]

open MonoidWithZeroHom.ValueGroup₀

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The valuation on `ℂ_[p]` has rank one. -/
/-
**PadicComplex.** 是 Mathlib 中的一个实例，位于命名空间 `PadicComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation on `ℂ_[p]` has rank one.
-/
instance : RankOne (PadicComplex.valued p).v where
  hom'        := embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

@[simp]
/-
**PadicComplex.RankOne.hom_eq_embedding** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex.
RankOne`。
形式化陈述：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Valuation.RankOne.hom Valued.v = Mono
idWithZeroHom.ValueGroup₀.embedding
参数：p : ℕ；Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
theorem RankOne.hom_eq_embedding : RankOne.hom (PadicComplex.valued p).v = embedding := rfl

/-- `ℂ_[p]` is a normed field, where the norm extends from `PadicAlgCl` along completion. -/
/-
**PadicComplex.normedField** 是 Mathlib 中的一个实例，位于命名空间 `PadicComplex`。
形式化陈述：normedField : NormedField Complex_[p]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℂ_[p]` is a normed field, where the norm extends from `PadicAlgCl` along comple
tion.
-/
instance normedField : NormedField ℂ_[p] := inferInstance

-- Ensure that the norm instance on `ℂ_[p]` is extended from `PadicAlgCl p`.
/-
**PadicComplex.** 是 Mathlib 中的一个示例，位于命名空间 `PadicComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (‖·‖ : ℂ_[p] → ℝ) = (UniformSpace.Completion.instNorm (PadicAlgCl p)).norm := by
  with_reducible_and_instances rfl

/-- The norm on `ℂ_[p]` extends the norm on `PadicAlgCl p`. -/
/-
**PadicComplex.norm_extends** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：norm_extends (x : PadicAlgCl p) : ‖(x : Complex_[p])‖ = ‖x‖
参数：x : PadicAlgCl p。
该定理/引理给出了一组等式。
继承自：(x : PadicAlgCl p) : ‖(x : Complex_[p])‖ = ‖x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The norm on `ℂ_[p]` extends the norm on `PadicAlgCl p`.
-/
theorem norm_extends (x : PadicAlgCl p) : ‖(x : ℂ_[p])‖ = ‖x‖ := by
  simp

/-- The norm on `ℂ_[p]` extends the norm on `ℚ_[p]`. -/
/-
**PadicComplex.norm_extends'** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：norm_extends' (x : Rat_[p]) : ‖(x : Complex_[p])‖ = ‖x‖
参数：x : Rat_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The norm on `ℂ_[p]` extends the norm on `ℚ_[p]`.
-/
theorem norm_extends' (x : ℚ_[p]) : ‖(x : ℂ_[p])‖ = ‖x‖ := by
  simp

/-- The underlying metric space of `ℂ_[p]` is ultrametric. -/
/-
**PadicComplex.isUltrametricDist** 是 Mathlib 中的一个实例，位于命名空间 `PadicComplex`。
形式化陈述：isUltrametricDist : IsUltrametricDist Complex_[p]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUltrametricDist.of_normedAlgebra`：IsUltrametricDist.of_normedAlgebra [
NormedDivisionRing L] [NormedAlgebra K L] [h : IsUltrametricDist K] : IsUltramet
ricDist L
· 使用定理 `Padic.instIsUltrametricDist`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], IsUl
trametricDist ℚ_[p]

--- 原说明 ---
The underlying metric space of `ℂ_[p]` is ultrametric.
-/
instance isUltrametricDist : IsUltrametricDist ℂ_[p] := IsUltrametricDist.of_normedAlgebra ℚ_[p]

/-- The norm on `ℂ_[p]` is nonarchimedean. -/
/-
**PadicComplex.isNonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：isNonarchimedean : IsNonarchimedean (Norm.norm : Complex_[p] -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUltrametricDist.norm_add_le_max`：∀ {S : Type u_1} [inst : SeminormedAd
dGroup S] [IsUltrametricDist S] (x y : S), ‖x + y‖ ≤ max ‖x‖ ‖y‖

--- 原说明 ---
The norm on `ℂ_[p]` is nonarchimedean.
-/
theorem isNonarchimedean : IsNonarchimedean (Norm.norm : ℂ_[p] → ℝ) :=
  IsUltrametricDist.norm_add_le_max

/-- The norm on `ℂ_[p]` is compatible with the valuation. -/
/-
**PadicComplex.norm_eq_norm'** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：norm_eq_norm' : (‖·‖ : Complex_[p] -> Real) = Valued.v.norm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.extension_unique`：extension_unique (hf : Uniform
Continuous f) {g : Completion α -> β} (hg : UniformContinuous g) (h : forall a :
 α, f a = g (a : Completion α)…
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `uniformContinuous_norm`：∀ {E : Type u_2} [inst : SeminormedAddGroup E], 
UniformContinuous norm
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.norm_def`：norm_def {x : L} : v.norm x = hv.hom _ (v.restrict x
)
· 使用引理 `Valuation.embedding_restrict`：embedding_restrict (x : R) : embedding (v.
restrict x) = v x
· 使用定理 `PadicComplex.valuation_extends`：valuation_extends (x : PadicAlgCl p) : V
alued.v (x : Complex_[p]) = Valued.v x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PadicAlgCl.valuation_coe`：valuation_coe (x : PadicAlgCl p) : ((Valued.v 
x : Real>=0) : Real) = ‖x‖

--- 原说明 ---
The norm on `ℂ_[p]` is compatible with the valuation.
-/
theorem norm_eq_norm' : (‖·‖ : ℂ_[p] → ℝ) = Valued.v.norm := by
  apply UniformSpace.Completion.extension_unique (f := @norm (PadicAlgCl p) _) (g := Valued.v.norm)
  · exact uniformContinuous_norm
  · let S := (Valued.toNormedField ℂ_[p] NNReal).toNormedCommRing.toNormedRing.toSeminormedRing
    let := S.toNonUnitalSeminormedRing.toSeminormedAddCommGroup.toSeminormedAddGroup
    exact @uniformContinuous_norm ℂ_[p] this
  · intro x
    simp only [Valued.v.norm_def, RankOne.hom_eq_embedding]
    rw [embedding_restrict (PadicComplex.valued p).v x, valuation_extends,
      ← PadicAlgCl.valuation_coe]

/-- The norm on `ℂ_[p]` is compatible with the valuation. -/
/-
**PadicComplex.norm_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：norm_eq_norm (x : Complex_[p]) : ‖x‖ = Valued.v.norm x
参数：x : Complex_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PadicComplex.norm_eq_norm'`：norm_eq_norm' : (‖·‖ : Complex_[p] -> Real) 
= Valued.v.norm

--- 原说明 ---
The norm on `ℂ_[p]` is compatible with the valuation.
-/
theorem norm_eq_norm (x : ℂ_[p]) : ‖x‖ = Valued.v.norm x := by
  congr!
  exact norm_eq_norm' p

/-- The `ℝ≥0`-valued norm on `ℂ_[p]` extends that on `PadicAlgCl p`. -/
/-
**PadicComplex.nnnorm_extends** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：nnnorm_extends (x : PadicAlgCl p) : ‖(x : Complex_[p])‖₊ = ‖x‖₊
参数：x : PadicAlgCl p。
该定理/引理给出了一组等式。
继承自：(x : PadicAlgCl p) : ‖(x : Complex_[p])‖₊ = ‖x‖₊。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `PadicComplex.norm_extends`：norm_extends (x : PadicAlgCl p) : ‖(x : Compl
ex_[p])‖ = ‖x‖

--- 原说明 ---
The `ℝ≥0`-valued norm on `ℂ_[p]` extends that on `PadicAlgCl p`.
-/
theorem nnnorm_extends (x : PadicAlgCl p) : ‖(x : ℂ_[p])‖₊ = ‖x‖₊ := by
  ext
  exact norm_extends p x

/-- The `ℝ≥0`-valued norm on `ℂ_[p]` extends the norm on `ℚ_[p]`. -/
/-
**PadicComplex.nnnorm_extends'** 是 Mathlib 中的一个定理，位于命名空间 `PadicComplex`。
形式化陈述：nnnorm_extends' (x : Rat_[p]) : ‖(x : Complex_[p])‖₊ = ‖x‖₊
参数：x : Rat_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.nnnorm_coe`：nnnorm_coe {E} [SeminormedAddCommGro
up E] (x : E) : ‖(x : Completion E)‖₊ = ‖x‖₊
· 使用定理 `nnnorm_algebraMap'`：nnnorm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖alge
braMap 𝕜 𝕜' x‖₊ = ‖x‖₊
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `ℝ≥0`-valued norm on `ℂ_[p]` extends the norm on `ℚ_[p]`.
-/
theorem nnnorm_extends' (x : ℚ_[p]) : ‖(x : ℂ_[p])‖₊ = ‖x‖₊ := by
  ext
  simp

/-- The norm on `ℂ_[p]` is nontrivial. -/
/-
**PadicComplex.nontriviallyNormedField** 是 Mathlib 中的一个实例，位于命名空间 `PadicComplex`。
形式化陈述：nontriviallyNormedField : NontriviallyNormedField Complex_[p] where non_tr
ivial
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm on `ℂ_[p]` is nontrivial.
-/
instance nontriviallyNormedField : NontriviallyNormedField ℂ_[p] where
  non_trivial := by
    choose x hx using NontriviallyNormedField.non_trivial (α := ℚ_[p])
    use x
    simpa only [norm_extends']

/-- `ℂ_[p]` has characteristic zero. -/
/-
**PadicComplex.charZero** 是 Mathlib 中的一个实例，位于命名空间 `PadicComplex`。
形式化陈述：charZero : CharZero Complex_[p]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用引理 `RingHom.charZero_iff`：charZero_iff {ϕ : R ->+* S} (hϕ : Injective ϕ) : C
harZero R ↔ CharZero S
· 使用定理 `PadicAlgCl.instUniformContinuousConstSMulPadic`：∀ (p : ℕ) [hp : Fact (Na
t.Prime p)], UniformContinuousConstSMul ℚ_[p] (PadicAlgCl p)
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]

--- 原说明 ---
`ℂ_[p]` has characteristic zero.
-/
instance charZero : CharZero ℂ_[p] :=
  (RingHom.charZero_iff (algebraMap ℚ_[p] ℂ_[p]).injective).mp inferInstance

/-- `ℂ_[p]` is algebraically closed. -/
/-
**PadicComplex.isAlgClosed** 是 Mathlib 中的一个实例，位于命名空间 `PadicComplex`。
形式化陈述：isAlgClosed : IsAlgClosed Complex_[p]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.of_denseRange`：IsAlgClosed.of_denseRange {K L : Type*} [Fiel
d K] [NontriviallyNormedField L] [CompleteSpace L] [CharZero L] [IsUltrametricDi
st L] [Algebra …
· 使用定理 `UniformSpace.Completion.denseRange_coe`：denseRange_coe : DenseRange ((↑)
 : α -> Completion α)

--- 原说明 ---
`ℂ_[p]` is algebraically closed.
-/
instance isAlgClosed : IsAlgClosed ℂ_[p] :=
  IsAlgClosed.of_denseRange UniformSpace.Completion.denseRange_coe

end PadicComplex

/-- We define `𝓞_ℂ_[p]` as the valuation subring of `ℂ_[p]`, consisting of those elements with
  valuation `≤ 1`. -/
/-
**PadicComplexInt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PadicComplexInt : ValuationSubring Complex_[p]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `𝓞_ℂ_[p]` as the valuation subring of `ℂ_[p]`, consisting of those ele
ments with
  valuation `≤ 1`.
-/
def PadicComplexInt : ValuationSubring ℂ_[p] := (PadicComplex.valued p).v.valuationSubring

/-- We define `𝓞_ℂ_[p]` as the subring of elements of `ℂ_[p]` with valuation `≤ 1`. -/
notation "𝓞_ℂ_[" p "]" => PadicComplexInt p

/-- `𝓞_ℂ_[p]` is the ring of integers of `ℂ_[p]`. -/
/-
**PadicComplexInt.integers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PadicComplexInt.integers : Valuation.Integers (PadicComplex.valued p).v 𝓞_
Complex_[p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…

--- 原说明 ---
`𝓞_ℂ_[p]` is the ring of integers of `ℂ_[p]`.
-/
theorem PadicComplexInt.integers : Valuation.Integers (PadicComplex.valued p).v 𝓞_ℂ_[p] :=
  Valuation.integer.integers _
