/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Unbundled.FiniteExtension
public import Mathlib.Data.Fintype.Order
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# algNormOfAlgEquiv and invariantExtension

Let `K` be a nonarchimedean normed field and `L/K` be a finite algebraic extension. In the comments,
`‖ ⬝ ‖` denotes any power-multiplicative `K`-algebra norm on `L` extending the norm on `K`.

## Main Definitions

* `IsUltrametricDist.algNormOfAlgEquiv` : given `σ : L ≃ₐ[K] L`, the function `L → ℝ` sending
  `x : L` to `‖ σ x ‖` is a `K`-algebra norm on `L`.
* `IsUltrametricDist.invariantExtension` : the function `L → ℝ` sending `x : L` to the maximum of
  `‖ σ x ‖` over all `σ : L ≃ₐ[K] L` is a `K`-algebra norm on `L`.

## Main Results
* `IsUltrametricDist.isPowMul_algNormOfAlgEquiv` : `algNormOfAlgEquiv` is power-multiplicative.
* `IsUltrametricDist.isNonarchimedean_algNormOfAlgEquiv` : `algNormOfAlgEquiv` is nonarchimedean.
* `IsUltrametricDist.algNormOfAlgEquiv_extends` : `algNormOfAlgEquiv` extends the norm on `K`.
* `IsUltrametricDist.isPowMul_invariantExtension` : `invariantExtension` is power-multiplicative.
* `IsUltrametricDist.isNonarchimedean_invariantExtension` : `invariantExtension` is nonarchimedean.
* `IsUltrametricDist.invariantExtension_extends` : `invariantExtension` extends the norm on `K`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

algNormOfAlgEquiv, invariantExtension, norm, nonarchimedean
-/

@[expose] public section

open scoped NNReal

noncomputable section

variable {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]
  [h_fin : FiniteDimensional K L] [hu : IsUltrametricDist K]

namespace IsUltrametricDist
section algNormOfAlgEquiv

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Given a normed field `K`, a finite algebraic extension `L/K` and `σ : L ≃ₐ[K] L`, the function
`L → ℝ` sending `x : L` to `‖ σ x ‖`, where `‖ ⬝ ‖` is any power-multiplicative algebra norm on `L`
extending the norm on `K`, is an algebra norm on `K`. -/
/-
**IsUltrametricDist.algNormOfAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsUltrametricDi
st`。
形式化陈述：algNormOfAlgEquiv (σ : L ≃ₐ[K] L) : AlgebraNorm K L where toFun x
参数：σ : L ≃ₐ[K] L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normed field `K`, a finite algebraic extension `L/K` and `σ : L ≃ₐ[K] L`
, the function
`L → ℝ` sending `x : L` to `‖ σ x ‖`, where `‖ ⬝ ‖` is any power-multiplicative 
algebra norm on `L`
extending the norm on `K`, is an algebra norm on `K`.
-/
def algNormOfAlgEquiv (σ : L ≃ₐ[K] L) :
    AlgebraNorm K L where
  toFun x     := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm) (σ x)
  map_zero'   := by simp
  add_le' x y := by simp [map_add σ, map_add_le_add]
  neg' x      := by simp [map_neg σ, map_neg_eq_map]
  mul_le' x y := by simp [map_mul σ, map_mul_le_mul]
  smul' x y   := by simp [map_smul σ, map_smul_eq_mul]
  eq_zero_of_map_eq_zero' x hx := EmbeddingLike.map_eq_zero_iff.mp (eq_zero_of_map_eq_zero _ hx)
/-
**IsUltrametricDist.algNormOfAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsUltrame
tricDist`。
形式化陈述：algNormOfAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : L) : algNormOfAlgEquiv σ x = 
Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_
fin hu.isNonarchimedean_norm) (σ x)
参数：σ : L ≃ₐ[K] L；x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algNormOfAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : L) :
    algNormOfAlgEquiv σ x =
      Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin
        hu.isNonarchimedean_norm) (σ x) := rfl

/-- The algebra norm `algNormOfAlgEquiv` is power-multiplicative. -/
/-
**IsUltrametricDist.isPowMul_algNormOfAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsUltr
ametricDist`。
形式化陈述：isPowMul_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) : IsPowMul (algNormOfAlgEquiv σ
)
参数：σ : L ≃ₐ[K] L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional`：exists_nona
rchimedean_pow_mul_seminorm_of_finiteDimensional (hfd : FiniteDimensional K L) (
hna : IsNonarchimedean (norm : K -> Real)) : exis…
· 使用引理 `IsUltrametricDist.isNonarchimedean_norm`：isNonarchimedean_norm {R} [Semi
normedAddCommGroup R] [IsUltrametricDist R] : IsNonarchimedean (‖·‖ : R -> Real)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The algebra norm `algNormOfAlgEquiv` is power-multiplicative.
-/
theorem isPowMul_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) :
    IsPowMul (algNormOfAlgEquiv σ) := by
  intro x n hn
  simp only [algNormOfAlgEquiv_apply, map_pow σ x n]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).1 _ hn

/-- The algebra norm `algNormOfAlgEquiv` is nonarchimedean. -/
/-
**IsUltrametricDist.isNonarchimedean_algNormOfAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间
 `IsUltrametricDist`。
形式化陈述：isNonarchimedean_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) : IsNonarchimedean (alg
NormOfAlgEquiv σ)
参数：σ : L ≃ₐ[K] L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional`：exists_nona
rchimedean_pow_mul_seminorm_of_finiteDimensional (hfd : FiniteDimensional K L) (
hna : IsNonarchimedean (norm : K -> Real)) : exis…
· 使用引理 `IsUltrametricDist.isNonarchimedean_norm`：isNonarchimedean_norm {R} [Semi
normedAddCommGroup R] [IsUltrametricDist R] : IsNonarchimedean (‖·‖ : R -> Real)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The algebra norm `algNormOfAlgEquiv` is nonarchimedean.
-/
theorem isNonarchimedean_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) :
    IsNonarchimedean (algNormOfAlgEquiv σ) := by
  intro x y
  simp only [algNormOfAlgEquiv_apply, map_add σ]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.2 _ _

/-- The algebra norm `algNormOfAlgEquiv` extends the norm on `K`. -/
/-
**IsUltrametricDist.algNormOfAlgEquiv_extends** 是 Mathlib 中的一个定理，位于命名空间 `IsUltra
metricDist`。
形式化陈述：algNormOfAlgEquiv_extends (σ : L ≃ₐ[K] L) (x : K) : (algNormOfAlgEquiv σ) 
((algebraMap K L) x) = ‖x‖
参数：σ : L ≃ₐ[K] L；x : K。
该定理/引理给出了一组等式。
继承自：(σ : L ≃ₐ[K] L) (x : K) : (algNormOfAlgEquiv σ) ((algebraMap K L) x) = ‖x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional`：exists_nona
rchimedean_pow_mul_seminorm_of_finiteDimensional (hfd : FiniteDimensional K L) (
hna : IsNonarchimedean (norm : K -> Real)) : exis…
· 使用引理 `IsUltrametricDist.isNonarchimedean_norm`：isNonarchimedean_norm {R} [Semi
normedAddCommGroup R] [IsUltrametricDist R] : IsNonarchimedean (‖·‖ : R -> Real)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The algebra norm `algNormOfAlgEquiv` extends the norm on `K`.
-/
theorem algNormOfAlgEquiv_extends (σ : L ≃ₐ[K] L) (x : K) :
    (algNormOfAlgEquiv σ) ((algebraMap K L) x) = ‖x‖ := by
  simp only [algNormOfAlgEquiv_apply, AlgEquiv.commutes]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.1 _

end algNormOfAlgEquiv

section invariantExtension

variable (K L)

/-- The function `L → ℝ` sending `x : L` to the maximum of `algNormOfAlgEquiv hna σ` over
  all `σ : L ≃ₐ[K] L` is an algebra norm on `L`. -/
/-
**IsUltrametricDist.invariantExtension** 是 Mathlib 中的一个定义，位于命名空间 `IsUltrametricD
ist`。
形式化陈述：invariantExtension : AlgebraNorm K L where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `L → ℝ` sending `x : L` to the maximum of `algNormOfAlgEquiv hna σ`
 over
  all `σ : L ≃ₐ[K] L` is an algebra norm on `L`.
-/
def invariantExtension : AlgebraNorm K L where
  toFun x := iSup fun σ : L ≃ₐ[K] L ↦ algNormOfAlgEquiv σ x
  map_zero' := by simp only [map_zero, ciSup_const]
  add_le' x y := ciSup_le fun σ ↦ le_trans (map_add_le_add (algNormOfAlgEquiv σ) x y)
    (add_le_add (Finite.le_ciSup_of_le σ le_rfl) (Finite.le_ciSup_of_le σ le_rfl))
  neg' x := by simp only [map_neg_eq_map]
  mul_le' x y := ciSup_le fun σ ↦ le_trans (map_mul_le_mul (algNormOfAlgEquiv σ) x y)
    (mul_le_mul (Finite.le_ciSup_of_le σ le_rfl)
      (Finite.le_ciSup_of_le σ le_rfl) (apply_nonneg _ _)
      (Finite.le_ciSup_of_le σ (apply_nonneg _ _)))
  eq_zero_of_map_eq_zero' x := by
    contrapose!
    exact fun hx ↦ ne_of_gt (lt_of_lt_of_le (map_pos_of_ne_zero _ hx)
      (Finite.le_ciSup (fun σ ↦ (algNormOfAlgEquiv σ) x) AlgEquiv.refl))
  smul' r x := by
    simp only [AlgebraNormClass.map_smul_eq_mul,
      Real.mul_iSup_of_nonneg (norm_nonneg _)]

@[simp]
/-
**IsUltrametricDist.invariantExtension_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsUltram
etricDist`。
形式化陈述：invariantExtension_apply (x : L) : invariantExtension K L x = iSup fun σ :
 L ≃ₐ[K] L => algNormOfAlgEquiv σ x
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invariantExtension_apply (x : L) :
    invariantExtension K L x = iSup fun σ : L ≃ₐ[K] L ↦ algNormOfAlgEquiv σ x :=
  rfl

/-- The algebra norm `invariantExtension` is power-multiplicative. -/
/-
**IsUltrametricDist.isPowMul_invariantExtension** 是 Mathlib 中的一个定理，位于命名空间 `IsUlt
rametricDist`。
形式化陈述：isPowMul_invariantExtension : IsPowMul (invariantExtension K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUltrametricDist.invariantExtension_apply`：invariantExtension_apply (x 
: L) : invariantExtension K L x = iSup fun σ : L ≃ₐ[K] L => algNormOfAlgEquiv σ 
x
· 使用引理 `Real.iSup_pow`：Real.iSup_pow [Nonempty ι] {f : ι -> Real} (hf : forall i
, 0 <= f i) (n : Nat) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `RingNormClass.toRingSeminormClass`：∀ {F : Type u_7} {α : outParam (Type 
u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst_1 : Sem
iring β} {inst_2 : Part…
· 使用定理 `AlgebraNormClass.toRingNormClass`：∀ {F : Type u_1} {R : outParam (Type u
_2)} {inst : SeminormedCommRing R} {S : outParam (Type u_3)} {inst_1 : Ring S}  
 {inst_2 : Algebra R S…
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
· 使用定理 `IsUltrametricDist.isPowMul_algNormOfAlgEquiv`：isPowMul_algNormOfAlgEquiv
 (σ : L ≃ₐ[K] L) : IsPowMul (algNormOfAlgEquiv σ)

--- 原说明 ---
The algebra norm `invariantExtension` is power-multiplicative.
-/
theorem isPowMul_invariantExtension :
    IsPowMul (invariantExtension K L) := by
  intro x n hn
  rw [invariantExtension_apply, invariantExtension_apply, Real.iSup_pow
    (fun σ ↦ apply_nonneg (algNormOfAlgEquiv σ) x)]
  exact iSup_congr fun σ ↦ isPowMul_algNormOfAlgEquiv σ _ hn

/-- The algebra norm `invariantExtension` is nonarchimedean. -/
/-
**IsUltrametricDist.isNonarchimedean_invariantExtension** 是 Mathlib 中的一个定理，位于命名空
间 `IsUltrametricDist`。
形式化陈述：isNonarchimedean_invariantExtension : IsNonarchimedean (invariantExtension
 K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `IsUltrametricDist.isNonarchimedean_algNormOfAlgEquiv`：isNonarchimedean_a
lgNormOfAlgEquiv (σ : L ≃ₐ[K] L) : IsNonarchimedean (algNormOfAlgEquiv σ)
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The algebra norm `invariantExtension` is nonarchimedean.
-/
theorem isNonarchimedean_invariantExtension :
    IsNonarchimedean (invariantExtension K L) := fun x y ↦
  ciSup_le fun σ ↦ le_trans (isNonarchimedean_algNormOfAlgEquiv σ x y)
    (max_le_max (Finite.le_ciSup_of_le σ le_rfl) (Finite.le_ciSup_of_le σ le_rfl))

/-- The algebra norm `invariantExtension` extends the norm on `K`. -/
/-
**IsUltrametricDist.invariantExtension_extends** 是 Mathlib 中的一个定理，位于命名空间 `IsUltr
ametricDist`。
形式化陈述：invariantExtension_extends (x : K) : (invariantExtension K L) (algebraMap 
K L x) = ‖x‖
参数：x : K。
该定理/引理给出了一组等式。
继承自：(x : K) : (invariantExtension K L) (algebraMap K L x) = ‖x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsUltrametricDist.algNormOfAlgEquiv_extends`：algNormOfAlgEquiv_extends (
σ : L ≃ₐ[K] L) (x : K) : (algNormOfAlgEquiv σ) ((algebraMap K L) x) = ‖x‖
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The algebra norm `invariantExtension` extends the norm on `K`.
-/
theorem invariantExtension_extends (x : K) :
    (invariantExtension K L) (algebraMap K L x) = ‖x‖ := by
  simp [algNormOfAlgEquiv_extends _ x, ciSup_const]

end invariantExtension

end IsUltrametricDist

