/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Instances.RealVectorSpace

/-!

# Normed space structure on `ℂ`.

This file gathers basic facts of analytic nature on the complex numbers.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives tools
on the real vector space structure of `ℂ`. Notably, it defines the following functions in the
namespace `Complex`.

|Name              |Type         |Description                                             |
|------------------|-------------|--------------------------------------------------------|
|`equivRealProdCLM`|ℂ ≃L[ℝ] ℝ × ℝ|The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ` |
|`reCLM`           |ℂ →L[ℝ] ℝ    |Real part function as a `ContinuousLinearMap`           |
|`imCLM`           |ℂ →L[ℝ] ℝ    |Imaginary part function as a `ContinuousLinearMap`      |
|`ofRealCLM`       |ℝ →L[ℝ] ℂ    |Embedding of the reals as a `ContinuousLinearMap`       |
|`ofRealLI`        |ℝ →ₗᵢ[ℝ] ℂ   |Embedding of the reals as a `LinearIsometry`            |
|`conjCLE`         |ℂ ≃L[ℝ] ℂ    |Complex conjugation as a `ContinuousLinearEquiv`        |
|`conjLIE`         |ℂ ≃ₗᵢ[ℝ] ℂ   |Complex conjugation as a `LinearIsometryEquiv`          |

We also register the fact that `ℂ` is an `RCLike` field.

-/

@[expose] public section


assert_not_exists Absorbs

namespace Complex

/-- A shortcut instance to ensure computability; otherwise we get the noncomputable instance
`Complex.instNormedField.toNormedModule.toModule`. -/
/-
**Complex.instModuleSelf** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：_root_.Module ℂ ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shortcut instance to ensure computability; otherwise we get the noncomputable 
instance
`Complex.instNormedField.toNormedModule.toModule`.
-/
instance instModuleSelf : Module ℂ ℂ := delta% inferInstance

end Complex

noncomputable section

namespace Complex
variable {z : ℂ}

open ComplexConjugate Topology Filter

/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedField ℂ where
  dist_eq _ _ := rfl
  norm_mul := Complex.norm_mul
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DenselyNormedField ℂ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [norm_real, Real.norm_of_nonneg (h₀.trans_lt h.1).le]⟩
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [NormedField R] [NormedAlgebra R ℝ] : NormedAlgebra R ℂ where
  norm_smul_le r x := by
    rw [← algebraMap_smul ℝ r x, real_smul, norm_mul, norm_real, norm_algebraMap']

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

-- see Note [lower instance priority]
/-- The module structure from `Module.complexToReal` is a normed space. -/
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The module structure from `Module.complexToReal` is a normed space.
-/
instance (priority := 900) _root_.NormedSpace.complexToReal : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E

-- see Note [lower instance priority]
/-- The algebra structure from `Algebra.complexToReal` is a normed algebra. -/
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra structure from `Algebra.complexToReal` is a normed algebra.
-/
instance (priority := 900) _root_.NormedAlgebra.complexToReal {A : Type*} [SeminormedRing A]
    [NormedAlgebra ℂ A] : NormedAlgebra ℝ A :=
  NormedAlgebra.restrictScalars ℝ ℂ A

-- This result cannot be moved to `Data/Complex/Norm` since `ℤ` gets its norm from its
-- normed ring structure and that file does not know about rings
/-
**Complex.nnnorm_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℤ), ‖↑n‖₊ = ‖n‖₊
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Complex.norm_intCast`：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : R
eal)|
-/
@[simp 1100, norm_cast] lemma nnnorm_intCast (n : ℤ) : ‖(n : ℂ)‖₊ = ‖n‖₊ := by
  ext; exact norm_intCast n

@[continuity, fun_prop]
/-
**Complex.continuous_normSq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Continuous ⇑Complex.normSq
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
-/
theorem continuous_normSq : Continuous normSq := by
  simpa [← Complex.normSq_eq_norm_sq] using continuous_norm (E := ℂ).fun_pow 2
/-
**Complex.nnnorm_eq_one_of_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ζ : ℂ} {n : ℕ}, ζ ^ n = 1 → n ≠ 0 → ‖ζ‖₊ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `pow_left_inj₀`：pow_left_inj₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b)
 (hn : n != 0) : a ^ n = b ^ n ↔ a = b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nnnorm_pow`：nnnorm_pow (a : α) (n : Nat) : ‖a ^ n‖₊ = ‖a‖₊ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem nnnorm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖₊ = 1 :=
  (pow_left_inj₀ zero_le zero_le hn).1 <| by rw [← nnnorm_pow, h, nnnorm_one, one_pow]
/-
**Complex.norm_eq_one_of_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ζ : ℂ} {n : ℕ}, ζ ^ n = 1 → n ≠ 0 → ‖ζ‖ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Complex.nnnorm_eq_one_of_pow_eq_one`：∀ {ζ : ℂ} {n : ℕ}, ζ ^ n = 1 → n ≠ 
0 → ‖ζ‖₊ = 1
-/
theorem norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖ = 1 :=
  congr_arg Subtype.val (nnnorm_eq_one_of_pow_eq_one h hn)
/-
**Complex.le_of_eq_sum_of_eq_sum_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ι : Type u_2} {a b : ℝ} (f : ι → ℂ) (s : Finset ι), 0 ≤ a → ↑a = ∑ i ∈ 
s, f i → ↑b = ∑ i ∈ s, ↑‖f i‖ → a ≤ b
参数：f : ι → ℂ；s : Finset ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
-/
lemma le_of_eq_sum_of_eq_sum_norm {ι : Type*} {a b : ℝ} (f : ι → ℂ) (s : Finset ι) (ha₀ : 0 ≤ a)
    (ha : a = ∑ i ∈ s, f i) (hb : b = ∑ i ∈ s, (‖f i‖ : ℂ)) : a ≤ b := by
  norm_cast at hb; rw [← Complex.norm_of_nonneg ha₀, ha, hb]; exact norm_sum_le s f
/-
**Complex.equivRealProd_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), ‖Complex.equivRealProd z‖ ≤ ‖z‖
参数：z : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.equivRealProd_apply`：∀ (z : ℂ), Complex.equivRealProd z = (z.re,
 z.im)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem equivRealProd_apply_le (z : ℂ) : ‖equivRealProd z‖ ≤ ‖z‖ := by
  simp [Prod.norm_def, abs_re_le_norm, abs_im_le_norm]
/-
**Complex.equivRealProd_apply_le'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), ‖Complex.equivRealProd z‖ ≤ 1 * ‖z‖
参数：z : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.equivRealProd_apply`：∀ (z : ℂ), Complex.equivRealProd z = (z.re,
 z.im)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.equivRealProd_apply_le`：∀ (z : ℂ), ‖Complex.equivRealProd z‖ ≤ ‖
z‖
-/
theorem equivRealProd_apply_le' (z : ℂ) : ‖equivRealProd z‖ ≤ 1 * ‖z‖ := by
  simpa using equivRealProd_apply_le z
/-
**Complex.lipschitz_equivRealProd** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：LipschitzWith 1 ⇑Complex.equivRealProd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_one`：toNNReal_one : Real.toNNReal 1 = 1
· 使用定理 `AddMonoidHomClass.lipschitz_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [in
st_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Complex.equivRealProd_apply_le'`：∀ (z : ℂ), ‖Complex.equivRealProd z‖ ≤ 
1 * ‖z‖
-/
theorem lipschitz_equivRealProd : LipschitzWith 1 equivRealProd := by
  simpa using! AddMonoidHomClass.lipschitz_of_bound equivRealProdLm 1 equivRealProd_apply_le'
/-
**Complex.antilipschitz_equivRealProd** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：AntilipschitzWith (NNReal.sqrt 2) ⇑Complex.equivRealProd
参数：NNReal.sqrt 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.antilipschitz_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]  
 [inst_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
· 使用定理 `Complex.norm_le_sqrt_two_mul_max`：norm_le_sqrt_two_mul_max (z : Complex)
 : ‖z‖ <= √2 * max |z.re| |z.im|
-/
theorem antilipschitz_equivRealProd : AntilipschitzWith (NNReal.sqrt 2) equivRealProd :=
  AddMonoidHomClass.antilipschitz_of_bound equivRealProdLm fun z ↦ by
    simpa only [Real.coe_sqrt, NNReal.coe_ofNat] using! norm_le_sqrt_two_mul_max z

@[fun_prop]
/-
**Complex.isUniformEmbedding_equivRealProd** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：IsUniformEmbedding ⇑Complex.equivRealProd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntilipschitzWith.isUniformEmbedding`：isUniformEmbedding {α β : Type*} [
EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β} (hf : Antilips
chitzWith K f) (hfc : Unif…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.antilipschitz_equivRealProd`：AntilipschitzWith (NNReal.sqrt 2) ⇑
Complex.equivRealProd
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Complex.lipschitz_equivRealProd`：LipschitzWith 1 ⇑Complex.equivRealProd
-/
theorem isUniformEmbedding_equivRealProd : IsUniformEmbedding equivRealProd :=
  antilipschitz_equivRealProd.isUniformEmbedding lipschitz_equivRealProd.uniformContinuous
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSpace ℂ :=
  (completeSpace_congr isUniformEmbedding_equivRealProd).mpr inferInstance
/-
**Complex.instT2Space** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：T2Space ℂ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
instance instT2Space : T2Space ℂ := TopologicalSpace.t2Space_of_metrizableSpace

/-- The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
/-
**Complex.equivRealProdCLM** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℂ ≃L[ℝ] ℝ × ℝ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.equivRealProd_apply_le'`：∀ (z : ℂ), ‖Complex.equivRealProd z‖ ≤ 
1 * ‖z‖

--- 原说明 ---
The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ`.
-/
def equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ :=
  equivRealProdLm.toContinuousLinearEquivOfBounds 1 (√2) equivRealProd_apply_le' fun p =>
    norm_le_sqrt_two_mul_max (equivRealProd.symm p)
/-
**Complex.equivRealProdCLM_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (p : ℝ × ℝ), Complex.equivRealProdCLM.symm p = ↑p.1 + ↑p.2 * Complex.I
参数：p : ℝ × ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.equivRealProd_symm_apply`：equivRealProd_symm_apply (p : Real × R
eal) : equivRealProd.symm p = p.1 + p.2 * I
-/
theorem equivRealProdCLM_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ProperSpace ℂ := lipschitz_equivRealProd.properSpace
  equivRealProdCLM.toHomeomorph.isProperMap

/-- The `normSq` function on `ℂ` is proper. -/
/-
**Complex.tendsto_normSq_cocompact_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Filter.Tendsto (⇑Complex.normSq) (Filter.cocompact ℂ) Filter.atTop
参数：⇑Complex.normSq；Filter.cocompact ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.norm_mul_self_eq_normSq`：norm_mul_self_eq_normSq (z : Complex) :
 ‖z‖ * ‖z‖ = normSq z
· 使用定理 `Filter.Tendsto.atTop_mul_atTop₀`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Semiring α] [inst_1 : PartialOrder α] [IsOrderedRing α] {l : Filter β}   {f g :
 β → α},   Filter.Ten…
· 使用定理 `tendsto_norm_cocompact_atTop`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] [ProperSpace E], Filter.Tendsto norm (Filter.cocompact E) Filter.atTop
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ

--- 原说明 ---
The `normSq` function on `ℂ` is proper.
-/
theorem tendsto_normSq_cocompact_atTop : Tendsto normSq (cocompact ℂ) atTop := by
  simpa [norm_mul_self_eq_normSq]
    using tendsto_norm_cocompact_atTop.atTop_mul_atTop₀ (tendsto_norm_cocompact_atTop (E := ℂ))

open ContinuousLinearMap

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
/-
**Complex.reCLM** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℂ →L[ℝ] ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear map version of the real part function, from `ℂ` to `ℝ`.
-/
def reCLM : ℂ →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by simp [abs_re_le_norm]

@[continuity, fun_prop]
/-
**Complex.continuous_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Continuous Complex.re
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem continuous_re : Continuous re :=
  reCLM.continuous

@[fun_prop]
/-
**Complex.uniformContinuous_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：UniformContinuous Complex.re
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
-/
lemma uniformContinuous_re : UniformContinuous re :=
  reCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_re :=
  uniformContinuous_re

@[simp]
/-
**Complex.reCLM_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：↑Complex.reCLM = Complex.reLm
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reCLM_coe : (reCLM : ℂ →ₗ[ℝ] ℝ) = reLm :=
  rfl

@[simp]
/-
**Complex.reCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), Complex.reCLM z = z.re
参数：z : ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reCLM_apply (z : ℂ) : (reCLM : ℂ → ℝ) z = z.re :=
  rfl

/-- Continuous linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
/-
**Complex.imCLM** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℂ →L[ℝ] ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear map version of the imaginary part function, from `ℂ` to `ℝ`.
-/
def imCLM : ℂ →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by simp [abs_im_le_norm]

@[continuity, fun_prop]
/-
**Complex.continuous_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Continuous Complex.im
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem continuous_im : Continuous im :=
  imCLM.continuous

@[fun_prop]
/-
**Complex.uniformContinuous_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：UniformContinuous Complex.im
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
-/
lemma uniformContinuous_im : UniformContinuous im :=
  imCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_im :=
  uniformContinuous_im

@[simp]
/-
**Complex.imCLM_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：↑Complex.imCLM = Complex.imLm
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imCLM_coe : (imCLM : ℂ →ₗ[ℝ] ℝ) = imLm :=
  rfl

@[simp]
/-
**Complex.imCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), Complex.imCLM z = z.im
参数：z : ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imCLM_apply (z : ℂ) : (imCLM : ℂ → ℝ) z = z.im :=
  rfl
/-
**Complex.restrictScalars_toSpanSingleton'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] [inst_1 : NormedSpace ℂ
 E] (x : E),   ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpan
Singleton ℂ x) =     Complex.reCLM.smulRight x + Complex.I • Complex.imCLM.smulR
ight x
参数：x : E；ContinuousLinearMap.toSpanSingleton ℂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mk_eq_add_mul_I`：mk_eq_add_mul_I (a b : Real) : Complex.mk a b =
 a + b * I
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
（共 33 条，此处仅展示前 30 条）
-/
theorem restrictScalars_toSpanSingleton' (x : E) :
    ContinuousLinearMap.restrictScalars ℝ (toSpanSingleton ℂ x : ℂ →L[ℂ] E) =
      reCLM.smulRight x + I • imCLM.smulRight x := by
  ext ⟨a, b⟩
  simp [map_add, mk_eq_add_mul_I, mul_smul, smul_comm I b x]
/-
**Complex.restrictScalars_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (x : ℂ), ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSp
anSingleton ℂ x) = x • 1
参数：x : ℂ；ContinuousLinearMap.toSpanSingleton ℂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem restrictScalars_toSpanSingleton (x : ℂ) :
    ContinuousLinearMap.restrictScalars ℝ (toSpanSingleton ℂ x : ℂ →L[ℂ] ℂ) =
    x • (1 : ℂ →L[ℝ] ℂ) := by
  ext1 z
  dsimp
  apply mul_comm

/-- The complex-conjugation function from `ℂ` to itself is an isometric linear equivalence. -/
/-
**Complex.conjLIE** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℂ ≃ₗᵢ[ℝ] ℂ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.norm_conj`：norm_conj (z : Complex) : ‖conj z‖ = ‖z‖

--- 原说明 ---
The complex-conjugation function from `ℂ` to itself is an isometric linear equiv
alence.
-/
def conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp]
/-
**Complex.conjLIE_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), Complex.conjLIE z = (starRingEnd ℂ) z
参数：z : ℂ；starRingEnd ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjLIE_apply (z : ℂ) : conjLIE z = conj z :=
  rfl

@[simp]
/-
**Complex.conjLIE_symm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.conjLIE.symm = Complex.conjLIE
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjLIE_symm : conjLIE.symm = conjLIE :=
  rfl
/-
**Complex.isometry_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Isometry ⇑(starRingEnd ℂ)
参数：starRingEnd ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
theorem isometry_conj : Isometry (conj : ℂ → ℂ) :=
  conjLIE.isometry

@[simp]
/-
**Complex.dist_conj_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z w : ℂ), dist ((starRingEnd ℂ) z) ((starRingEnd ℂ) w) = dist z w
参数：z w : ℂ；(starRingEnd ℂ) z；(starRingEnd ℂ) w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `Complex.isometry_conj`：Isometry ⇑(starRingEnd ℂ)
-/
theorem dist_conj_conj (z w : ℂ) : dist (conj z) (conj w) = dist z w :=
  isometry_conj.dist_eq z w

@[simp]
/-
**Complex.nndist_conj_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z w : ℂ), nndist ((starRingEnd ℂ) z) ((starRingEnd ℂ) w) = nndist z w
参数：z w : ℂ；(starRingEnd ℂ) z；(starRingEnd ℂ) w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.nndist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpac
e α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), nnd
ist (f x…
· 使用定理 `Complex.isometry_conj`：Isometry ⇑(starRingEnd ℂ)
-/
theorem nndist_conj_conj (z w : ℂ) : nndist (conj z) (conj w) = nndist z w :=
  isometry_conj.nndist_eq z w
/-
**Complex.dist_conj_comm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z w : ℂ), dist ((starRingEnd ℂ) z) w = dist z ((starRingEnd ℂ) w)
参数：z w : ℂ；(starRingEnd ℂ) z；(starRingEnd ℂ) w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.dist_conj_conj`：∀ (z w : ℂ), dist ((starRingEnd ℂ) z) ((starRing
End ℂ) w) = dist z w
· 使用定理 `Complex.conj_conj`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : Star
Ring R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
-/
theorem dist_conj_comm (z w : ℂ) : dist (conj z) w = dist z (conj w) := by
  rw [← dist_conj_conj, conj_conj]
/-
**Complex.nndist_conj_comm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z w : ℂ), nndist ((starRingEnd ℂ) z) w = nndist z ((starRingEnd ℂ) w)
参数：z w : ℂ；(starRingEnd ℂ) z；(starRingEnd ℂ) w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Complex.dist_conj_comm`：∀ (z w : ℂ), dist ((starRingEnd ℂ) z) w = dist z
 ((starRingEnd ℂ) w)
-/
theorem nndist_conj_comm (z w : ℂ) : nndist (conj z) w = nndist z (conj w) :=
  Subtype.ext <| dist_conj_comm _ _
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousStar ℂ :=
  ⟨conjLIE.continuous⟩

@[continuity, fun_prop]
/-
**Complex.continuous_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Continuous ⇑(starRingEnd ℂ)
参数：starRingEnd ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
-/
theorem continuous_conj : Continuous (conj : ℂ → ℂ) :=
  continuous_star

/-- The only continuous ring homomorphisms from `ℂ` to `ℂ` are the identity and the complex
conjugation. -/
/-
**Complex.ringHom_eq_id_or_conj_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：∀ {f : ℂ →+* ℂ}, Continuous ⇑f → f = RingHom.id ℂ ∨ f = starRingEnd ℂ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_real_smul`：map_real_smul {G} [FunLike G E F] [AddMonoidHomClass G E 
F] (f : G) (hf : Continuous f) (c : Real) (x : E) : f (c • x) = c • f x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `Complex.real_algHom_eq_id_or_conj`：real_algHom_eq_id_or_conj (f : Comple
x ->ₐ[Real] Complex) : f = AlgHom.id Real Complex ∨ f = conjAe

--- 原说明 ---
The only continuous ring homomorphisms from `ℂ` to `ℂ` are the identity and the 
complex
conjugation.
-/
theorem ringHom_eq_id_or_conj_of_continuous {f : ℂ →+* ℂ} (hf : Continuous f) :
    f = RingHom.id ℂ ∨ f = conj := by
  simpa only [DFunLike.ext_iff] using! real_algHom_eq_id_or_conj (AlgHom.mk' f (map_real_smul f hf))

/-- The complex-conjugation function from `ℂ` to itself is a continuous `ℝ`-algebra isomorphism. -/
/-
**Complex.conjCAE** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℂ ≃A[ℝ] ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complex-conjugation function from `ℂ` to itself is a continuous `ℝ`-algebra 
isomorphism.
-/
def conjCAE : ℂ ≃A[ℝ] ℂ := { conjAe, conjLIE.toContinuousLinearEquiv with }

/-- Continuous linear equiv version of the conj function, from `ℂ` to `ℂ`.

This is an abbreviation for `conjCAE` coerced to a continuous linear map. -/
/-
**Complex.conjCLE** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℂ ≃L[ℝ] ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear equiv version of the conj function, from `ℂ` to `ℂ`.

This is an abbreviation for `conjCAE` coerced to a continuous linear map.
-/
abbrev conjCLE : ℂ ≃L[ℝ] ℂ := conjCAE.toContinuousLinearEquiv
/-
**Complex.conjLIE_toCLE** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：↑Complex.conjLIE = Complex.conjCLE
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma conjLIE_toCLE : conjLIE.toContinuousLinearEquiv = conjCLE := rfl

@[simp]
/-
**Complex.conjCAE_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.conjCAE.toAlgEquiv = Complex.conjAe
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjCAE_toAlgEquiv : conjCAE.toAlgEquiv = conjAe :=
  rfl
/-
**Complex.conjCLE_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：↑Complex.conjCLE = ↑Complex.conjAe
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem conjCLE_toLinearEquiv : conjCLE.toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[deprecated "Now provable by simp" (since := "2026-04-13")]
/-
**Complex.conjCLE_coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：↑↑Complex.conjCLE = Complex.conjAe.toLinearMap
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conjCLE_coe_toLinearMap : (conjCLE : ℂ →ₗ[ℝ] ℂ) = conjAe.toLinearMap := by simp

@[simp]
/-
**Complex.conjCAE_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), Complex.conjCAE z = (starRingEnd ℂ) z
参数：z : ℂ；starRingEnd ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjCAE_apply (z : ℂ) : conjCAE z = conj z :=
  rfl

-- simp tag not needed because conjCLE is `abbrev`
/-
**Complex.conjCLE_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), Complex.conjCLE z = (starRingEnd ℂ) z
参数：z : ℂ；starRingEnd ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjCLE_apply (z : ℂ) : conjCLE z = conj z :=
  rfl
/-
**Complex.conjCAE_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.conjCAE.toLinearMap = Complex.conjAe.toLinearMap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma conjCAE_toLinearMap : conjCAE.toLinearMap = conjAe.toLinearMap := rfl

/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
/-
**Complex.ofRealLI** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℝ →ₗᵢ[ℝ] ℂ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖

--- 原说明 ---
Linear isometry version of the canonical embedding of `ℝ` in `ℂ`.
-/
def ofRealLI : ℝ →ₗᵢ[ℝ] ℂ :=
  ⟨ofRealAm.toLinearMap, norm_real⟩

@[simp]
/-
**Complex.ofRealLI_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (x : ℝ), Complex.ofRealLI x = ↑x
参数：x : ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRealLI_apply (x : ℝ) : ofRealLI x = x := rfl
/-
**Complex.isometry_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Isometry Complex.ofReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem isometry_ofReal : Isometry ((↑) : ℝ → ℂ) :=
  ofRealLI.isometry

@[continuity, fun_prop]
/-
**Complex.continuous_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Continuous Complex.ofReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_
5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂}
 [inst_2 : Semi…
-/
theorem continuous_ofReal : Continuous ((↑) : ℝ → ℂ) :=
  ofRealLI.continuous
/-
**Complex.isUniformEmbedding_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：IsUniformEmbedding Complex.ofReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Isometry.isUniformEmbedding`：isUniformEmbedding (hf : Isometry f) : IsUn
iformEmbedding f
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem isUniformEmbedding_ofReal : IsUniformEmbedding ((↑) : ℝ → ℂ) :=
  ofRealLI.isometry.isUniformEmbedding
/-
**Complex._root_.RCLike.isUniformEmbedding_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `Com
plex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.RCLike.isUniformEmbedding_ofReal {𝕜 : Type*} [RCLike 𝕜] :
    IsUniformEmbedding ((↑) : ℝ → 𝕜) :=
  RCLike.ofRealLI.isometry.isUniformEmbedding
/-
**Complex._root_.Filter.tendsto_ofReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.tendsto_ofReal_iff {α : Type*} {l : Filter α} {f : α → ℝ} {x : ℝ} :
    Tendsto (fun x ↦ (f x : ℂ)) l (𝓝 (x : ℂ)) ↔ Tendsto f l (𝓝 x) :=
  isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm
/-
**Complex._root_.Filter.tendsto_ofReal_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Filter.tendsto_ofReal_iff' {α 𝕜 : Type*} [RCLike 𝕜]
    {l : Filter α} {f : α → ℝ} {x : ℝ} :
    Tendsto (fun x ↦ (f x : 𝕜)) l (𝓝 (x : 𝕜)) ↔ Tendsto f l (𝓝 x) :=
  RCLike.isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm
/-
**Complex._root_.Filter.Tendsto.ofReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Filter.Tendsto.ofReal {α : Type*} {l : Filter α} {f : α → ℝ} {x : ℝ}
    (hf : Tendsto f l (𝓝 x)) : Tendsto (fun x ↦ (f x : ℂ)) l (𝓝 (x : ℂ)) :=
  tendsto_ofReal_iff.mpr hf

/-- The only continuous ring homomorphism from `ℝ` to `ℂ` is the identity. -/
/-
**Complex.ringHom_eq_ofReal_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {f : ℝ →+* ℂ}, Continuous ⇑f → f = Complex.ofRealHom
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_real_smul`：map_real_smul {G} [FunLike G E F] [AddMonoidHomClass G E 
F] (f : G) (hf : Continuous f) (c : Real) (x : E) : f (c • x) = c • f x
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `AlgHom.subsingleton`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
The only continuous ring homomorphism from `ℝ` to `ℂ` is the identity.
-/
theorem ringHom_eq_ofReal_of_continuous {f : ℝ →+* ℂ} (h : Continuous f) : f = ofRealHom := by
  convert!
    congr_arg AlgHom.toRingHom <|
      Subsingleton.elim (AlgHom.mk' f <| map_real_smul f h) (Algebra.ofId ℝ ℂ)

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
/-
**Complex.ofRealCLM** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ℝ →L[ℝ] ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`.
-/
def ofRealCLM : ℝ →L[ℝ] ℂ :=
  ofRealLI.toContinuousLinearMap

@[simp]
/-
**Complex.ofRealCLM_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：↑Complex.ofRealCLM = Complex.ofRealAm.toLinearMap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRealCLM_coe : (ofRealCLM : ℝ →ₗ[ℝ] ℂ) = ofRealAm.toLinearMap :=
  rfl

@[simp]
/-
**Complex.ofRealCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (x : ℝ), Complex.ofRealCLM x = ↑x
参数：x : ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRealCLM_apply (x : ℝ) : ofRealCLM x = x :=
  rfl
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : RCLike ℂ where
  re := ⟨⟨Complex.re, Complex.zero_re⟩, Complex.add_re⟩
  im := ⟨⟨Complex.im, Complex.zero_im⟩, Complex.add_im⟩
  I := Complex.I
  I_re_ax := I_re
  I_mul_I_ax := .inr Complex.I_mul_I
  re_add_im_ax := re_add_im
  ofReal_re_ax := ofReal_re
  ofReal_im_ax := ofReal_im
  mul_re_ax := mul_re
  mul_im_ax := mul_im
  conj_re_ax _ := rfl
  conj_im_ax _ := rfl
  conj_I_ax := conj_I
  norm_sq_eq_def_ax z := (normSq_eq_norm_sq z).symm
  mul_im_I_ax _ := mul_one _
  toPartialOrder := Complex.partialOrder
  le_iff_re_im := Iff.rfl
/-
**Complex._root_.RCLike.re_eq_complex_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RCLike.re_eq_complex_re : ⇑(RCLike.re : ℂ →+ ℝ) = Complex.re :=
  rfl
/-
**Complex._root_.RCLike.im_eq_complex_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RCLike.im_eq_complex_im : ⇑(RCLike.im : ℂ →+ ℝ) = Complex.im :=
  rfl
/-
**Complex._root_.RCLike.ofReal_eq_complex_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RCLike.ofReal_eq_complex_ofReal : (RCLike.ofReal : ℝ → ℂ) = Complex.ofReal := rfl

-- TODO: Replace `mul_conj` and `conj_mul` once `norm` has replaced `abs`
/-
**Complex.mul_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), z * (starRingEnd ℂ) z = ↑‖z‖ ^ 2
参数：z : ℂ；starRingEnd ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.mul_conj`：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
-/
lemma mul_conj' (z : ℂ) : z * conj z = ‖z‖ ^ 2 := RCLike.mul_conj z
/-
**Complex.conj_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), (starRingEnd ℂ) z * z = ↑‖z‖ ^ 2
参数：z : ℂ；starRingEnd ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.conj_mul`：conj_mul (z : K) : conj z * z = ‖z‖ ^ 2
-/
lemma conj_mul' (z : ℂ) : conj z * z = ‖z‖ ^ 2 := RCLike.conj_mul z
/-
**Complex.inv_eq_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {z : ℂ}, ‖z‖ = 1 → z⁻¹ = (starRingEnd ℂ) z
参数：starRingEnd ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.inv_eq_conj`：inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z
-/
lemma inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z := RCLike.inv_eq_conj hz
/-
**Complex.exists_norm_eq_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), ∃ c, ‖c‖ = 1 ∧ ↑‖z‖ = c * z
参数：z : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.exists_norm_eq_mul_self`：exists_norm_eq_mul_self (x : K) : exists
 c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x
-/
lemma exists_norm_eq_mul_self (z : ℂ) : ∃ c, ‖c‖ = 1 ∧ ‖z‖ = c * z :=
  RCLike.exists_norm_eq_mul_self _
/-
**Complex.exists_norm_mul_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), ∃ c, ‖c‖ = 1 ∧ c * ↑‖z‖ = z
参数：z : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.exists_norm_mul_eq_self`：exists_norm_mul_eq_self (x : K) : exists
 c, ‖c‖ = 1 ∧ c * ‖x‖ = x
-/
lemma exists_norm_mul_eq_self (z : ℂ) : ∃ c, ‖c‖ = 1 ∧ c * ‖z‖ = z :=
  RCLike.exists_norm_mul_eq_self _
/-
**Complex.im_eq_zero_iff_isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (x : ℂ), x.im = 0 ↔ IsSelfAdjoint x
参数：x : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.im_eq_complex_im`：⇑RCLike.im = Complex.im
· 使用引理 `RCLike.im_eq_zero_iff_isSelfAdjoint`：im_eq_zero_iff_isSelfAdjoint {x : K
} : im x = 0 ↔ IsSelfAdjoint x
-/
lemma im_eq_zero_iff_isSelfAdjoint (x : ℂ) : Complex.im x = 0 ↔ IsSelfAdjoint x := by
  rw [← RCLike.im_eq_complex_im]
  exact RCLike.im_eq_zero_iff_isSelfAdjoint
/-
**Complex.re_eq_ofReal_of_isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {x : ℂ} {y : ℝ}, IsSelfAdjoint x → (x.re = y ↔ x = ↑y)
参数：x.re = y ↔ x = ↑y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_eq_complex_re`：⇑RCLike.re = Complex.re
· 使用引理 `RCLike.re_eq_ofReal_of_isSelfAdjoint`：re_eq_ofReal_of_isSelfAdjoint {x :
 K} {y : Real} (hx : IsSelfAdjoint x) : re x = y ↔ x = y
-/
lemma re_eq_ofReal_of_isSelfAdjoint {x : ℂ} {y : ℝ} (hx : IsSelfAdjoint x) :
    Complex.re x = y ↔ x = y := by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_eq_ofReal_of_isSelfAdjoint hx
/-
**Complex.ofReal_eq_re_of_isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {x : ℂ} {y : ℝ}, IsSelfAdjoint x → (y = x.re ↔ ↑y = x)
参数：y = x.re ↔ ↑y = x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_eq_complex_re`：⇑RCLike.re = Complex.re
· 使用引理 `RCLike.ofReal_eq_re_of_isSelfAdjoint`：ofReal_eq_re_of_isSelfAdjoint {x :
 K} {y : Real} (hx : IsSelfAdjoint x) : y = re x ↔ y = x
-/
lemma ofReal_eq_re_of_isSelfAdjoint {x : ℂ} {y : ℝ} (hx : IsSelfAdjoint x) :
    y = Complex.re x ↔ y = x := by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.ofReal_eq_re_of_isSelfAdjoint hx

/-- The natural isomorphism between `𝕜` satisfying `RCLike 𝕜` and `ℂ` when
`RCLike.im RCLike.I = 1`. -/
@[simps]
/-
**Complex._root_.RCLike.complexRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between `𝕜` satisfying `RCLike 𝕜` and `ℂ` when
`RCLike.im RCLike.I = 1`.
-/
def _root_.RCLike.complexRingEquiv {𝕜 : Type*} [RCLike 𝕜]
    (h : RCLike.im (RCLike.I : 𝕜) = 1) : 𝕜 ≃+* ℂ where
  toFun x := RCLike.re x + RCLike.im x * I
  invFun x := re x + im x * RCLike.I
  left_inv x := by simp
  right_inv x := by simp [h]
  map_add' x y := by simp only [map_add, ofReal_add]; ring
  map_mul' x y := by
    simp only [RCLike.mul_re, ofReal_sub, ofReal_mul, RCLike.mul_im, ofReal_add]
    ring_nf
    rw [I_sq]
    ring

open scoped ComplexOrder in
/-
**Complex._root_.RCLike.map_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RCLike.map_nonneg_iff {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']
    (h : RCLike.im (RCLike.I : 𝕜') = 1) {a : 𝕜} :
    0 ≤ RCLike.map 𝕜 𝕜' a ↔ 0 ≤ a := by
  rw [RCLike.nonneg_iff, RCLike.nonneg_iff (K := 𝕜)]
  simp [h]

open scoped ComplexOrder in
/-
**Complex._root_.RCLike.to_complex_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.RCLike.to_complex_nonneg_iff {𝕜 : Type*} [RCLike 𝕜] {a : 𝕜} :
    0 ≤ RCLike.re a + RCLike.im a * Complex.I ↔ 0 ≤ a := RCLike.map_nonneg_iff I_im

/-- The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` and `ℂ` when
`RCLike.im RCLike.I = 1`. -/
@[simps]
/-
**Complex._root_.RCLike.complexLinearIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Co
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` an
d `ℂ` when
`RCLike.im RCLike.I = 1`.
-/
def _root_.RCLike.complexLinearIsometryEquiv {𝕜 : Type*} [RCLike 𝕜]
    (h : RCLike.im (RCLike.I : 𝕜) = 1) : 𝕜 ≃ₗᵢ[ℝ] ℂ where
  map_smul' _ _ := by simp [RCLike.smul_re, RCLike.smul_im, ofReal_mul]; ring
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity), ← normSq_eq_norm_sq, ← RCLike.normSq_eq_def',
      RCLike.normSq_apply]
    simp [normSq_add]
  __ := RCLike.complexRingEquiv h
/-
**Complex._root_.RCLike.toContinuousLinearMap_complexLinearIsometryEquiv** 是 Mat
hlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.RCLike.toContinuousLinearMap_complexLinearIsometryEquiv
    {𝕜 : Type*} [RCLike 𝕜] (h : RCLike.im (RCLike.I : 𝕜) = 1) :
    (RCLike.complexLinearIsometryEquiv h : 𝕜 →L[ℝ] ℂ) = RCLike.map 𝕜 ℂ := rfl
/-
**Complex._root_.RCLike.norm_to_complex** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.RCLike.norm_to_complex {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜) :
    ‖RCLike.re a + RCLike.im a * Complex.I‖ = ‖a‖ := by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← RCLike.re_add_im a, RCLike.im_eq_zero h]
    simp
  exact (RCLike.complexLinearIsometryEquiv h).norm_map a
/-
**Complex.isometry_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Isometry Int.cast
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `Complex.isometry_ofReal`：Isometry Complex.ofReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isometry_intCast : Isometry ((↑) : ℤ → ℂ) :=
  Isometry.of_dist_eq <| by simp_rw [← Complex.ofReal_intCast,
    Complex.isometry_ofReal.dist_eq, Int.dist_cast_real, implies_true]
/-
**Complex.isClosedEmbedding_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Topology.IsClosedEmbedding Int.cast
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `Complex.isometry_intCast`：Isometry Int.cast
-/
theorem isClosedEmbedding_intCast : IsClosedEmbedding ((↑) : ℤ → ℂ) :=
  isometry_intCast.isClosedEmbedding

@[deprecated (since := "2026-04-15")] alias closedEmbedding_intCast := isClosedEmbedding_intCast
/-
**Complex.isClosed_range_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：IsClosed (Set.range Int.cast)
参数：Set.range Int.cast。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Complex.isClosedEmbedding_intCast`：Topology.IsClosedEmbedding Int.cast
-/
lemma isClosed_range_intCast : IsClosed (Set.range ((↑) : ℤ → ℂ)) :=
  Complex.isClosedEmbedding_intCast.isClosed_range
/-
**Complex.isOpen_compl_range_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：IsOpen (Set.range Int.cast)ᶜ
参数：Set.range Int.cast。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Complex.isClosed_range_intCast`：IsClosed (Set.range Int.cast)
-/
lemma isOpen_compl_range_intCast : IsOpen (Set.range ((↑) : ℤ → ℂ))ᶜ :=
  Complex.isClosed_range_intCast.isOpen_compl

section ComplexOrder

open ComplexOrder

/-
**Complex.eq_coe_norm_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {z : ℂ}, 0 ≤ z → z = ↑‖z‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem eq_coe_norm_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = ↑‖z‖ := by
  lift z to ℝ using hz.2.symm
  rw [norm_real, Real.norm_of_nonneg (id hz.1 : 0 ≤ z)]

/-- We show that the partial order and the topology on `ℂ` are compatible.
We turn this into an instance scoped to `ComplexOrder`. -/
/-
**Complex.orderClosedTopology** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：OrderClosedTopology ℂ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.instOrderClosedTopology`：instOrderClosedTopology : OrderClosedTop
ology K where isClosed_le'

--- 原说明 ---
We show that the partial order and the topology on `ℂ` are compatible.
We turn this into an instance scoped to `ComplexOrder`.
-/
lemma orderClosedTopology : OrderClosedTopology ℂ := RCLike.instOrderClosedTopology

scoped[ComplexOrder] attribute [instance] Complex.orderClosedTopology
/-
**Complex.norm_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {x : ℂ}, 0 ≤ x → ↑‖x‖ = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_eq_complex_ofReal`：RCLike.ofReal = Complex.ofReal
· 使用引理 `RCLike.norm_of_nonneg'`：norm_of_nonneg' {x : K} (hx : 0 <= x) : ‖x‖ = x
-/
theorem norm_of_nonneg' {x : ℂ} (hx : 0 ≤ x) : ‖x‖ = x := by
  rw [← RCLike.ofReal_eq_complex_ofReal]
  exact RCLike.norm_of_nonneg' hx
/-
**Complex.re_nonneg_iff_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {x : ℂ}, IsSelfAdjoint x → (0 ≤ x.re ↔ 0 ≤ x)
参数：0 ≤ x.re ↔ 0 ≤ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_eq_complex_re`：⇑RCLike.re = Complex.re
· 使用引理 `RCLike.re_nonneg_of_nonneg`：re_nonneg_of_nonneg {x : K} (hx : IsSelfAdjo
int x) : 0 <= re x ↔ 0 <= x
-/
lemma re_nonneg_iff_nonneg {x : ℂ} (hx : IsSelfAdjoint x) : 0 ≤ re x ↔ 0 ≤ x := by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_nonneg_of_nonneg hx

@[gcongr]
/-
**Complex.re_le_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {x y : ℂ}, x ≤ y → x.re ≤ y.re
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
-/
lemma re_le_re {x y : ℂ} (h : x ≤ y) : re x ≤ re y := by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

end ComplexOrder

end Complex

namespace RCLike

open ComplexConjugate

local notation "reC" => @RCLike.re ℂ _
local notation "imC" => @RCLike.im ℂ _
local notation "IC" => @RCLike.I ℂ _
local notation "norm_sqC" => @RCLike.normSq ℂ _

@[simp]
/-
**RCLike.re_to_complex** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {x : ℂ}, RCLike.re x = x.re
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_to_complex {x : ℂ} : reC x = x.re :=
  rfl

@[simp]
/-
**RCLike.im_to_complex** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {x : ℂ}, RCLike.im x = x.im
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_to_complex {x : ℂ} : imC x = x.im :=
  rfl

@[simp]
/-
**RCLike.I_to_complex** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：RCLike.I = Complex.I
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem I_to_complex : IC = Complex.I :=
  rfl

@[simp]
/-
**RCLike.normSq_to_complex** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {x : ℂ}, RCLike.normSq x = Complex.normSq x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normSq_to_complex {x : ℂ} : norm_sqC x = Complex.normSq x :=
  rfl

section tsum

variable {α : Type*} (𝕜 : Type*) [RCLike 𝕜] {L : SummationFilter α}

@[simp]
/-
**RCLike.hasSum_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
{f : α → 𝕜} {x : 𝕜},   HasSum (fun x => (starRingEnd 𝕜) (f x)) x L ↔ HasSum f ((
starRingEnd 𝕜) x) L
参数：𝕜 : Type u_2；fun x => (starRingEnd 𝕜) (f x)；(starRingEnd 𝕜) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type
 u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R
₂] [inst_2 : AddCo…
-/
theorem hasSum_conj {f : α → 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L :=
  conjCLE.hasSum
/-
**RCLike.hasSum_conj'** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
{f : α → 𝕜} {x : 𝕜},   HasSum (fun x => (starRingEnd 𝕜) (f x)) ((starRingEnd 𝕜) 
x) L ↔ HasSum f x L
参数：𝕜 : Type u_2；fun x => (starRingEnd 𝕜) (f x)；(starRingEnd 𝕜) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.hasSum'`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Typ
e u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring 
R₂] [inst_2 : AddCo…
-/
theorem hasSum_conj' {f : α → 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L :=
  conjCLE.hasSum'

@[simp]
/-
**RCLike.summable_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
{f : α → 𝕜},   Summable (fun x => (starRingEnd 𝕜) (f x)) L ↔ Summable f L
参数：𝕜 : Type u_2；fun x => (starRingEnd 𝕜) (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_star_iff`：summable_star_iff : Summable (fun b => star (f b)) L 
↔ Summable f L
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
-/
theorem summable_conj {f : α → 𝕜} : Summable (fun x => conj (f x)) L ↔ Summable f L :=
  summable_star_iff

variable {𝕜} in
/-
**RCLike.conj_tsum** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {L : SummationFilter α} 
(f : α → 𝕜),   (starRingEnd 𝕜) (∑'[L] (a : α), f a) = ∑'[L] (a : α), (starRingEn
d 𝕜) (f a)
参数：f : α → 𝕜；starRingEnd 𝕜；∑'[L] (a : α), f a；a : α；starRingEnd 𝕜；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_star`：tsum_star [T2Space α] : star (∑'[L] b, f b) = ∑'[L] b, star (
f b)
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem conj_tsum (f : α → 𝕜) : conj (∑'[L] a, f a) = ∑'[L] a, conj (f a) :=
  tsum_star

@[simp, norm_cast]
/-
**RCLike.hasSum_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
{f : α → ℝ} {x : ℝ},   HasSum (fun x => ↑(f x)) (↑x) L ↔ HasSum f x L
参数：𝕜 : Type u_2；fun x => ↑(f x)；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
-/
theorem hasSum_ofReal {f : α → ℝ} {x : ℝ} : HasSum (fun x => (f x : 𝕜)) x L ↔ HasSum f x L :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.hasSum h,
    ofRealCLM.hasSum⟩

@[simp, norm_cast]
/-
**RCLike.summable_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
{f : α → ℝ},   Summable (fun x => ↑(f x)) L ↔ Summable f L
参数：𝕜 : Type u_2；fun x => ↑(f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `ContinuousLinearMap.summable`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type
 u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R
₂] [inst_2 : AddCo…
-/
theorem summable_ofReal {f : α → ℝ} : Summable (fun x => (f x : 𝕜)) L ↔ Summable f L :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.summable h,
    ofRealCLM.summable⟩

@[norm_cast]
/-
**RCLike.ofReal_tsum** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
(f : α → ℝ),   ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
参数：𝕜 : Type u_2；f : α → ℝ；∑'[L] (a : α), f a；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFil
ter β} {G : Type u_…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `RCLike.continuous_re`：continuous_re : Continuous (re : K -> Real)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofReal_tsum (f : α → ℝ) : (↑(∑'[L] a, f a) : 𝕜) = ∑'[L] a, (f a : 𝕜) :=
  Function.LeftInverse.map_tsum f ofRealCLM.continuous continuous_re (fun _ ↦ by simp)
/-
**RCLike.hasSum_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
{f : α → 𝕜} {x : 𝕜},   HasSum f x L → HasSum (fun x => RCLike.re (f x)) (RCLike.
re x) L
参数：𝕜 : Type u_2；fun x => RCLike.re (f x)；RCLike.re x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
-/
theorem hasSum_re {f : α → 𝕜} {x : 𝕜} (h : HasSum f x L) : HasSum (fun x => re (f x)) (re x) L :=
  reCLM.hasSum h
/-
**RCLike.hasSum_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
{f : α → 𝕜} {x : 𝕜},   HasSum f x L → HasSum (fun x => RCLike.im (f x)) (RCLike.
im x) L
参数：𝕜 : Type u_2；fun x => RCLike.im (f x)；RCLike.im x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
-/
theorem hasSum_im {f : α → 𝕜} {x : 𝕜} (h : HasSum f x L) : HasSum (fun x => im (f x)) (im x) L :=
  imCLM.hasSum h
/-
**RCLike.re_tsum** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
[L.NeBot] {f : α → 𝕜},   Summable f L → RCLike.re (∑'[L] (a : α), f a) = ∑'[L] (
a : α), RCLike.re (f a)
参数：𝕜 : Type u_2；∑'[L] (a : α), f a；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_tsum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type
 u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R
₂] [inst_2 : AddCo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem re_tsum [L.NeBot] {f : α → 𝕜} (h : Summable f L) : re (∑'[L] a, f a) = ∑'[L] a, re (f a) :=
  reCLM.map_tsum h
/-
**RCLike.im_tsum** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : SummationFilter α} 
[L.NeBot] {f : α → 𝕜},   Summable f L → RCLike.im (∑'[L] (a : α), f a) = ∑'[L] (
a : α), RCLike.im (f a)
参数：𝕜 : Type u_2；∑'[L] (a : α), f a；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_tsum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type
 u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R
₂] [inst_2 : AddCo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem im_tsum [L.NeBot] {f : α → 𝕜} (h : Summable f L) : im (∑'[L] a, f a) = ∑'[L] a, im (f a) :=
  imCLM.map_tsum h

variable {𝕜}
/-
**RCLike.hasSum_iff** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {L : SummationFilter α} 
(f : α → 𝕜) (c : 𝕜),   HasSum f c L ↔ HasSum (fun x => RCLike.re (f x)) (RCLike.
re c) L ∧ HasSum (fun x => RCLike.im (f x)) (RCLike.im c) L
参数：f : α → 𝕜；c : 𝕜；fun x => RCLike.re (f x)；RCLike.re c；fun x => RCLike.im (f x)
；RCLike.im c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.hasSum_re`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L :
 SummationFilter α} {f : α → 𝕜} {x : 𝕜},   HasSum f x L → HasSum (fun x => RCLik
e.re (…
· 使用定理 `RCLike.hasSum_im`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L :
 SummationFilter α} {f : α → 𝕜} {x : 𝕜},   HasSum f x L → HasSum (fun x => RCLik
e.im (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `HasSum.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f g : β → α} {a b : α}   {L : SummationFilter β} [Co
…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RCLike.hasSum_ofReal`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] 
{L : SummationFilter α} {f : α → ℝ} {x : ℝ},   HasSum (fun x => ↑(f x)) (↑x) L ↔
 HasSum f …
· 使用定理 `HasSum.mul_right`：HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (f
un i => f i * a₂) (a₁ * a₂) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
-/
theorem hasSum_iff (f : α → 𝕜) (c : 𝕜) :
    HasSum f c L ↔ HasSum (fun x => re (f x)) (re c) L ∧ HasSum (fun x => im (f x)) (im c) L := by
  refine ⟨fun h => ⟨hasSum_re _ h, hasSum_im _ h⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  simpa only [re_add_im] using
    ((hasSum_ofReal 𝕜).mpr h₁).add (((hasSum_ofReal 𝕜).mpr h₂).mul_right I)

end tsum

end RCLike

namespace Complex

/-!
We have to repeat the lemmas about `RCLike.re` and `RCLike.im` as they are not syntactic
matches for `Complex.re` and `Complex.im`.

We do not have this problem with `ofReal` and `conj`, although we repeat them anyway for
discoverability and to avoid the need to unify `𝕜`.
-/


section tsum

variable {α : Type*} {L : SummationFilter α}

open ComplexConjugate

/-
**Complex.hasSum_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} {f : α → ℂ} {x : ℂ},   HasSum (fu
n x => (starRingEnd ℂ) (f x)) x L ↔ HasSum f ((starRingEnd ℂ) x) L
参数：fun x => (starRingEnd ℂ) (f x)；(starRingEnd ℂ) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.hasSum_conj`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L
 : SummationFilter α} {f : α → 𝕜} {x : 𝕜},   HasSum (fun x => (starRingEnd 𝕜) (f
 x)) x L…
-/
theorem hasSum_conj {f : α → ℂ} {x : ℂ} : HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L :=
  RCLike.hasSum_conj _
/-
**Complex.hasSum_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} {f : α → ℂ} {x : ℂ},   HasSum (fu
n x => (starRingEnd ℂ) (f x)) ((starRingEnd ℂ) x) L ↔ HasSum f x L
参数：fun x => (starRingEnd ℂ) (f x)；(starRingEnd ℂ) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.hasSum_conj'`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {
L : SummationFilter α} {f : α → 𝕜} {x : 𝕜},   HasSum (fun x => (starRingEnd 𝕜) (
f x)) ((s…
-/
theorem hasSum_conj' {f : α → ℂ} {x : ℂ} : HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L :=
  RCLike.hasSum_conj' _
/-
**Complex.summable_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {f : α → ℂ}, (Summable fun x => (starRingEnd ℂ) (f x)) ↔ 
Summable f
参数：Summable fun x => (starRingEnd ℂ) (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.summable_conj`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] 
{L : SummationFilter α} {f : α → 𝕜},   Summable (fun x => (starRingEnd 𝕜) (f x))
 L ↔ Summa…
-/
theorem summable_conj {f : α → ℂ} : (Summable fun x => conj (f x)) ↔ Summable f :=
  RCLike.summable_conj _
/-
**Complex.conj_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℂ),   (starRingEnd ℂ) (∑
'[L] (a : α), f a) = ∑'[L] (a : α), (starRingEnd ℂ) (f a)
参数：f : α → ℂ；starRingEnd ℂ；∑'[L] (a : α), f a；a : α；starRingEnd ℂ；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.conj_tsum`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {L :
 SummationFilter α} (f : α → 𝕜),   (starRingEnd 𝕜) (∑'[L] (a : α), f a) = ∑'[L] 
(a : α…
-/
theorem conj_tsum (f : α → ℂ) : conj (∑'[L] a, f a) = ∑'[L] a, conj (f a) :=
  RCLike.conj_tsum _

@[simp, norm_cast]
/-
**Complex.hasSum_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} {f : α → ℝ} {x : ℝ}, HasSum (fun 
x => ↑(f x)) (↑x) L ↔ HasSum f x L
参数：fun x => ↑(f x)；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.hasSum_ofReal`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] 
{L : SummationFilter α} {f : α → ℝ} {x : ℝ},   HasSum (fun x => ↑(f x)) (↑x) L ↔
 HasSum f …
-/
theorem hasSum_ofReal {f : α → ℝ} {x : ℝ} : HasSum (fun x => (f x : ℂ)) x L ↔ HasSum f x L :=
  RCLike.hasSum_ofReal _

@[simp, norm_cast]
/-
**Complex.summable_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} {f : α → ℝ}, Summable (fun x => ↑
(f x)) L ↔ Summable f L
参数：fun x => ↑(f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.summable_ofReal`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜
] {L : SummationFilter α} {f : α → ℝ},   Summable (fun x => ↑(f x)) L ↔ Summable
 f L
-/
theorem summable_ofReal {f : α → ℝ} : (Summable (fun x => (f x : ℂ)) L) ↔ Summable f L :=
  RCLike.summable_ofReal _

@[norm_cast]
/-
**Complex.ofReal_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ), ↑(∑'[L] (a : α), f a
) = ∑'[L] (a : α), ↑(f a)
参数：f : α → ℝ；∑'[L] (a : α), f a；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.ofReal_tsum`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L
 : SummationFilter α} (f : α → ℝ),   ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f 
a)
-/
theorem ofReal_tsum (f : α → ℝ) : (↑(∑'[L] a, f a) : ℂ) = ∑'[L] a, ↑(f a) :=
  RCLike.ofReal_tsum _ _
/-
**Complex.hasSum_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} {f : α → ℂ} {x : ℂ}, HasSum f x L
 → HasSum (fun x => (f x).re) x.re L
参数：fun x => (f x).re。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.hasSum_re`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L :
 SummationFilter α} {f : α → 𝕜} {x : 𝕜},   HasSum f x L → HasSum (fun x => RCLik
e.re (…
-/
theorem hasSum_re {f : α → ℂ} {x : ℂ} (h : HasSum f x L) : HasSum (fun x => (f x).re) x.re L :=
  RCLike.hasSum_re ℂ h
/-
**Complex.hasSum_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} {f : α → ℂ} {x : ℂ}, HasSum f x L
 → HasSum (fun x => (f x).im) x.im L
参数：fun x => (f x).im。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.hasSum_im`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L :
 SummationFilter α} {f : α → 𝕜} {x : 𝕜},   HasSum f x L → HasSum (fun x => RCLik
e.im (…
-/
theorem hasSum_im {f : α → ℂ} {x : ℂ} (h : HasSum f x L) : HasSum (fun x => (f x).im) x.im L :=
  RCLike.hasSum_im ℂ h
/-
**Complex.re_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} [L.NeBot] {f : α → ℂ},   Summable
 f L → (∑'[L] (a : α), f a).re = ∑'[L] (a : α), (f a).re
参数：∑'[L] (a : α), f a；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.re_tsum`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : S
ummationFilter α} [L.NeBot] {f : α → 𝕜},   Summable f L → RCLike.re (∑'[L] (a : 
α), …
-/
theorem re_tsum [L.NeBot] {f : α → ℂ} (h : Summable f L) : (∑'[L] a, f a).re = ∑'[L] a, (f a).re :=
  RCLike.re_tsum _ h
/-
**Complex.im_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} [L.NeBot] {f : α → ℂ},   Summable
 f L → (∑'[L] (a : α), f a).im = ∑'[L] (a : α), (f a).im
参数：∑'[L] (a : α), f a；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.im_tsum`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L : S
ummationFilter α} [L.NeBot] {f : α → 𝕜},   Summable f L → RCLike.im (∑'[L] (a : 
α), …
-/
theorem im_tsum [L.NeBot] {f : α → ℂ} (h : Summable f L) : (∑'[L] a, f a).im = ∑'[L] a, (f a).im :=
  RCLike.im_tsum _ h
/-
**Complex.hasSum_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℂ) (c : ℂ),   HasSum f c
 L ↔ HasSum (fun x => (f x).re) c.re L ∧ HasSum (fun x => (f x).im) c.im L
参数：f : α → ℂ；c : ℂ；fun x => (f x).re；fun x => (f x).im。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.hasSum_iff`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {L 
: SummationFilter α} (f : α → 𝕜) (c : 𝕜),   HasSum f c L ↔ HasSum (fun x => RCLi
ke.re (…
-/
theorem hasSum_iff (f : α → ℂ) (c : ℂ) :
    HasSum f c L ↔ HasSum (fun x => (f x).re) c.re L ∧ HasSum (fun x => (f x).im) c.im L :=
  RCLike.hasSum_iff _ _

end tsum

section slitPlane

/-!
### Define the "slit plane" `ℂ ∖ ℝ≤0` and provide some API
-/

open scoped ComplexOrder

/-- The *slit plane* is the complex plane with the closed negative real axis removed. -/
/-
**Complex.slitPlane** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：Set ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *slit plane* is the complex plane with the closed negative real axis removed
.
-/
def slitPlane : Set ℂ := {z | 0 < z.re ∨ z.im ≠ 0}
/-
**Complex.mem_slitPlane_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {z : ℂ}, z ∈ Complex.slitPlane ↔ 0 < z.re ∨ z.im ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
-/
lemma mem_slitPlane_iff {z : ℂ} : z ∈ slitPlane ↔ 0 < z.re ∨ z.im ≠ 0 := Set.mem_ofPred

/- If `z` is non-zero, then either `z` or `-z` is in `slitPlane`. -/
/-
**Complex.mem_slitPlane_or_neg_mem_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
形式化陈述：∀ {z : ℂ}, z ≠ 0 → z ∈ Complex.slitPlane ∨ -z ∈ Complex.slitPlane
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mem_slitPlane_iff`：∀ {z : ℂ}, z ∈ Complex.slitPlane ↔ 0 < z.re ∨
 z.im ≠ 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `z` is non-zero, then either `z` or `-z` is in `slitPlane`.
-/
lemma mem_slitPlane_or_neg_mem_slitPlane {z : ℂ} (hz : z ≠ 0) :
    z ∈ slitPlane ∨ -z ∈ slitPlane := by
  rw [mem_slitPlane_iff, mem_slitPlane_iff]
  rw [ne_eq, Complex.ext_iff] at hz
  push Not at hz
  simp_all only [ne_eq, zero_re, zero_im, neg_re, Left.neg_pos_iff, neg_im, neg_eq_zero]
  by_contra! contra
  exact hz (le_antisymm contra.1.1 contra.2.1) contra.1.2
/-
**Complex.slitPlane_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.slitPlane = {z | 0 < z.re} ∪ {z | z.im ≠ 0}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ofPred_or`：ofPred_or {p q : α -> Prop} : { a | p a ∨ q a } = { a | p
 a } union { a | q a }
-/
lemma slitPlane_eq_union : slitPlane = {z | 0 < z.re} ∪ {z | z.im ≠ 0} := Set.ofPred_or.symm
/-
**Complex.isOpen_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：IsOpen Complex.slitPlane
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用引理 `RCLike.instOrderClosedTopology`：instOrderClosedTopology : OrderClosedTop
ology K where isClosed_le'
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `isOpen_ne_fun`：isOpen_ne_fun [T2Space X] {f g : Y -> X} (hf : Continuous
 f) (hg : Continuous g) : IsOpen { y : Y | f y != g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
lemma isOpen_slitPlane : IsOpen slitPlane :=
  (isOpen_lt continuous_const continuous_re).union (isOpen_ne_fun continuous_im continuous_const)

@[simp]
/-
**Complex.ofReal_mem_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {x : ℝ}, ↑x ∈ Complex.slitPlane ↔ 0 < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ofReal_mem_slitPlane {x : ℝ} : ↑x ∈ slitPlane ↔ 0 < x := by simp [mem_slitPlane_iff]

@[simp]
/-
**Complex.neg_ofReal_mem_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {x : ℝ}, -↑x ∈ Complex.slitPlane ↔ x < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Complex.ofReal_mem_slitPlane`：∀ {x : ℝ}, ↑x ∈ Complex.slitPlane ↔ 0 < x
-/
lemma neg_ofReal_mem_slitPlane {x : ℝ} : -↑x ∈ slitPlane ↔ x < 0 := by
  simpa using ofReal_mem_slitPlane (x := -x)
/-
**Complex.one_mem_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：1 ∈ Complex.slitPlane
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_mem_slitPlane`：∀ {x : ℝ}, ↑x ∈ Complex.slitPlane ↔ 0 < x
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
@[simp] lemma one_mem_slitPlane : 1 ∈ slitPlane := ofReal_mem_slitPlane.2 one_pos

@[simp]
/-
**Complex.zero_notMem_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：0 ∉ Complex.slitPlane
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.ofReal_mem_slitPlane`：∀ {x : ℝ}, ↑x ∈ Complex.slitPlane ↔ 0 < x
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
lemma zero_notMem_slitPlane : 0 ∉ slitPlane := mt ofReal_mem_slitPlane.1 (lt_irrefl _)

@[simp]
/-
**Complex.natCast_mem_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {n : ℕ}, ↑n ∈ Complex.slitPlane ↔ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Complex.ofReal_mem_slitPlane`：∀ {x : ℝ}, ↑x ∈ Complex.slitPlane ↔ 0 < x
-/
lemma natCast_mem_slitPlane {n : ℕ} : ↑n ∈ slitPlane ↔ n ≠ 0 := by
  simpa [pos_iff_ne_zero] using @ofReal_mem_slitPlane n

@[simp]
/-
**Complex.ofNat_mem_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], OfNat.ofNat n ∈ Complex.slitPlane
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.natCast_mem_slitPlane`：∀ {n : ℕ}, ↑n ∈ Complex.slitPlane ↔ n ≠ 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
lemma ofNat_mem_slitPlane (n : ℕ) [n.AtLeastTwo] : ofNat(n) ∈ slitPlane :=
  natCast_mem_slitPlane.2 (NeZero.ne n)
/-
**Complex.mem_slitPlane_iff_not_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {z : ℂ}, z ∈ Complex.slitPlane ↔ ¬z ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Complex.mem_slitPlane_iff`：∀ {z : ℂ}, z ∈ Complex.slitPlane ↔ 0 < z.re ∨
 z.im ≠ 0
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Complex.not_le_zero_iff`：not_le_zero_iff {z : Complex} : ¬z <= 0 ↔ 0 < z
.re ∨ z.im != 0
-/
lemma mem_slitPlane_iff_not_le_zero {z : ℂ} : z ∈ slitPlane ↔ ¬z ≤ 0 :=
  mem_slitPlane_iff.trans not_le_zero_iff.symm
/-
**Complex.compl_Iic_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：(Set.Iic 0)ᶜ = Complex.slitPlane
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Complex.mem_slitPlane_iff_not_le_zero`：∀ {z : ℂ}, z ∈ Complex.slitPlane 
↔ ¬z ≤ 0
-/
protected lemma compl_Iic_zero : (Set.Iic 0)ᶜ = slitPlane := Set.ext fun _ ↦
  mem_slitPlane_iff_not_le_zero.symm
/-
**Complex.slitPlane_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {z : ℂ}, z ∈ Complex.slitPlane → z ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Complex.zero_notMem_slitPlane`：0 ∉ Complex.slitPlane
-/
lemma slitPlane_ne_zero {z : ℂ} (hz : z ∈ slitPlane) : z ≠ 0 :=
  ne_of_mem_of_not_mem hz zero_notMem_slitPlane

/-- The slit plane includes the open unit ball of radius `1` around `1`. -/
/-
**Complex.ball_one_subset_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Metric.ball 1 1 ⊆ Complex.slitPlane
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Complex.re_le_norm`：re_le_norm (z : Complex) : z.re <= ‖z‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_ball_iff_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] {
a b : E} {r : ℝ}, b ∈ Metric.ball a r ↔ ‖a - b‖ < r

--- 原说明 ---
The slit plane includes the open unit ball of radius `1` around `1`.
-/
lemma ball_one_subset_slitPlane : Metric.ball 1 1 ⊆ slitPlane := by
  intro z hz
  apply Or.inl
  simpa using (re_le_norm _).trans_lt (mem_ball_iff_norm'.1 hz)

/-- The slit plane includes the open unit ball of radius `1` around `1`. -/
/-
**Complex.mem_slitPlane_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {z : ℂ}, ‖z‖ < 1 → 1 + z ∈ Complex.slitPlane
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ball_one_subset_slitPlane`：Metric.ball 1 1 ⊆ Complex.slitPlane
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self_add_left`：∀ {E : Type u_2} [inst : SeminormedAddGroup E] (a b 
: E), dist (b + a) b = ‖a‖

--- 原说明 ---
The slit plane includes the open unit ball of radius `1` around `1`.
-/
lemma mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ∈ slitPlane :=
  ball_one_subset_slitPlane <| by simpa

open Metric in
/-- A subset of the circle centered at the origin in `ℂ` of radius `r` is a subset of
the `slitPlane` if it does not contain `-r`. -/
/-
**Complex.subset_slitPlane_iff_of_subset_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Compl
ex`。
形式化陈述：∀ {r : ℝ} {s : Set ℂ}, s ⊆ Metric.sphere 0 r → (s ⊆ Complex.slitPlane ↔ -↑
r ∉ s)
参数：s ⊆ Complex.slitPlane ↔ -↑r ∉ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.eq_coe_norm_of_nonneg`：∀ {z : ℂ}, 0 ≤ z → z = ↑‖z‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖

--- 原说明 ---
A subset of the circle centered at the origin in `ℂ` of radius `r` is a subset o
f
the `slitPlane` if it does not contain `-r`.
-/
lemma subset_slitPlane_iff_of_subset_sphere {r : ℝ} {s : Set ℂ} (hs : s ⊆ sphere 0 r) :
    s ⊆ slitPlane ↔ (-r : ℂ) ∉ s := by
  simp_rw [Set.subset_def, mem_slitPlane_iff_not_le_zero]
  contrapose!
  refine ⟨?_, fun hr ↦ ⟨_, hr, by simpa using hs hr⟩⟩
  rintro ⟨z, hzs, hz⟩
  have : ‖z‖ = r := by simpa using hs hzs
  simpa [← this, ← norm_neg z ▸ eq_coe_norm_of_nonneg (neg_nonneg.mpr hz)]

end slitPlane

/-
**Complex._root_.IsCompact.reProdIm** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsCompact.reProdIm {s t : Set ℝ} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ℂ t) :=
  equivRealProdCLM.toHomeomorph.isCompact_preimage.2 (hs.prod ht)

end Complex

section realPart_imaginaryPart

variable {A : Type*} [SeminormedAddCommGroup A] [StarAddMonoid A] [NormedSpace ℂ A] [StarModule ℂ A]
  [NormedStarGroup A]

/-
**realPart.norm_le** 是 Mathlib 中的一个引理，位于命名空间 ``Complex`.`。
形式化陈述：realPart.norm_le (x : A) : ‖realPart x‖ <= ‖x‖
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `AddSubgroup.norm_coe`：∀ {E : Type u_1} [inst : SeminormedAddGroup E] {s 
: AddSubgroup E} (x : ↥s), ‖↑x‖ = ‖x‖
· 使用定理 `realPart_apply_coe`：realPart_apply_coe (a : A) : (ℜ a : A) = (2 : Real)⁻
¹ • (a + star a)
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
（共 32 条，此处仅展示前 30 条）
-/
lemma realPart.norm_le (x : A) : ‖realPart x‖ ≤ ‖x‖ := by
  rw [← inv_mul_cancel_left₀ two_ne_zero ‖x‖, ← AddSubgroup.norm_coe, realPart_apply_coe,
    norm_smul, norm_inv, Real.norm_ofNat]
  gcongr
  exact norm_add_le _ _ |>.trans <| by simp [two_mul]
/-
**imaginaryPart.norm_le** 是 Mathlib 中的一个引理，位于命名空间 ``Complex`.`。
形式化陈述：imaginaryPart.norm_le (x : A) : ‖imaginaryPart x‖ <= ‖x‖
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `realPart_I_smul`：realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `realPart.norm_le`：realPart.norm_le (x : A) : ‖realPart x‖ <= ‖x‖
-/
lemma imaginaryPart.norm_le (x : A) : ‖imaginaryPart x‖ ≤ ‖x‖ := by
  calc ‖imaginaryPart x‖ = ‖realPart (Complex.I • (-x))‖ := by simp
    _ ≤ ‖x‖ := by simpa only [smul_neg, map_neg, realPart_I_smul, neg_neg,
        AddSubgroupClass.coe_norm, norm_neg, norm_smul, Complex.norm_I, one_mul] using
        realPart.norm_le (Complex.I • (-x))

end realPart_imaginaryPart

