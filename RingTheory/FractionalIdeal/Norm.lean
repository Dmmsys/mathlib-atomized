/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Localization.NormTrace

/-!

# Fractional ideal norms

This file defines the absolute ideal norm of a fractional ideal `I : FractionalIdeal R⁰ K` where
`K` is a fraction field of `R`. The norm is defined by
`FractionalIdeal.absNorm I = Ideal.absNorm I.num / |Algebra.norm ℤ I.den|` where `I.num` is an
ideal of `R` and `I.den` an element of `R⁰` such that `I.den • I = I.num`.

## Main definitions and results

* `FractionalIdeal.absNorm`: the norm as a zero-preserving morphism with values in `ℚ`.
* `FractionalIdeal.absNorm_eq'`: the value of the norm does not depend on the choice of
  `I.num` and `I.den`.
* `FractionalIdeal.abs_det_basis_change`: the norm is given by the determinant
  of the basis change matrix.
* `FractionalIdeal.absNorm_span_singleton`: the norm of a principal fractional ideal is the
  norm of its generator
-/

@[expose] public section

open Module
open scoped Pointwise nonZeroDivisors

namespace FractionalIdeal
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]
variable {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]

/-
**FractionalIdeal.absNorm_div_norm_eq_absNorm_div_norm** 是 Mathlib 中的一个定理，位于命名空间
 `FractionalIdeal`。
形式化陈述：absNorm_div_norm_eq_absNorm_div_norm {I : FractionalIdeal R⁰ K} (a : R⁰) (
I₀ : Ideal R) (h : a • (I : Submodule R K) = Submodule.map (Algebra.linearMap R 
K) I₀) : (Ideal.absNorm I.num : Rat) / |Algebra.norm Int (I.den : R)| = (Ideal.a
bsNorm I₀ : Rat) / |Algebra.norm Int (a : R)|
参数：a : R⁰；I₀ : Ideal R；h : a • (I : Submodule R K) = Submodule.map (Algebra.line
arMap R K) I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `FractionalIdeal.den_mul_self_eq_num`：den_mul_self_eq_num (I : Fractional
Ideal S P) : I.den • (I : Submodule R P) = Submodule.map (Algebra.linearMap R P)
 I.num
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearMap.map_injective`：map_injective {f : M ->ₛₗ[τ₁₂] M₂} (hf : ker f 
= ⊥) : Injective (map f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `Submodule.ideal_span_singleton_smul`：ideal_span_singleton_smul (r : R) (
N : Submodule R M) : (Ideal.span {r} : Ideal R) • N = r • N
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
（共 31 条，此处仅展示前 30 条）
-/
theorem absNorm_div_norm_eq_absNorm_div_norm {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
    (h : a • (I : Submodule R K) = Submodule.map (Algebra.linearMap R K) I₀) :
    (Ideal.absNorm I.num : ℚ) / |Algebra.norm ℤ (I.den : R)| =
      (Ideal.absNorm I₀ : ℚ) / |Algebra.norm ℤ (a : R)| := by
  rw [div_eq_div_iff]
  · replace h := congr_arg (I.den • ·) h
    have h' := congr_arg (a • ·) (den_mul_self_eq_num I)
    rw [smul_comm] at h
    rw [h, Submonoid.smul_def, Submonoid.smul_def, ← Submodule.ideal_span_singleton_smul,
      ← Submodule.ideal_span_singleton_smul, ← Submodule.map_smul'', ← Submodule.map_smul'',
      (LinearMap.map_injective ?_).eq_iff, smul_eq_mul, smul_eq_mul] at h'
    · simp_rw [← Nat.cast_natAbs, ← Nat.cast_mul, ← Ideal.absNorm_span_singleton]
      rw [← map_mul, ← map_mul, mul_comm, ← h', mul_comm]
    · exact LinearMap.ker_eq_bot.mpr (IsFractionRing.injective R K)
  all_goals simp [Algebra.norm_eq_zero_iff]

/-- The absolute norm of the fractional ideal `I` extending by multiplicativity the absolute norm
on (integral) ideals. -/
/-
**FractionalIdeal.absNorm** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：absNorm : FractionalIdeal R⁰ K ->*₀ Rat where toFun I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute norm of the fractional ideal `I` extending by multiplicativity the 
absolute norm
on (integral) ideals.
-/
noncomputable def absNorm : FractionalIdeal R⁰ K →*₀ ℚ where
  toFun I := (Ideal.absNorm I.num : ℚ) / |Algebra.norm ℤ (I.den : R)|
  map_zero' := by
    rw [num_zero_eq, Submodule.zero_eq_bot, Ideal.absNorm_bot, Nat.cast_zero, zero_div]
    exact IsFractionRing.injective R K
  map_one' := by
    rw [absNorm_div_norm_eq_absNorm_div_norm 1 ⊤ (by simp [Submodule.one_eq_range]),
      Ideal.absNorm_top, Nat.cast_one, OneMemClass.coe_one, map_one, abs_one,
      Int.cast_one,
      one_div_one]
  map_mul' I J := by
    rw [absNorm_div_norm_eq_absNorm_div_norm (I.den * J.den) (I.num * J.num) (by
        have : Algebra.linearMap R K = (IsScalarTower.toAlgHom R R K).toLinearMap := rfl
        rw [coe_mul, this, Submodule.map_mul, ← this, ← den_mul_self_eq_num, ← den_mul_self_eq_num]
        exact Submodule.mul_smul_mul_eq_smul_mul_smul _ _ _ _),
      Submonoid.coe_mul, map_mul, map_mul, Nat.cast_mul, div_mul_div_comm,
      Int.cast_abs, Int.cast_abs, Int.cast_abs, ← abs_mul, Int.cast_mul]
/-
**FractionalIdeal.absNorm_eq** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：absNorm_eq (I : FractionalIdeal R⁰ K) : absNorm I = (Ideal.absNorm I.num :
 Rat) / |Algebra.norm Int (I.den : R)|
参数：I : FractionalIdeal R⁰ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem absNorm_eq (I : FractionalIdeal R⁰ K) :
    absNorm I = (Ideal.absNorm I.num : ℚ) / |Algebra.norm ℤ (I.den : R)| := rfl
/-
**FractionalIdeal.absNorm_eq'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：absNorm_eq' {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R) (h : a • (I
 : Submodule R K) = Submodule.map (Algebra.linearMap R K) I₀) : absNorm I = (Ide
al.absNorm I₀ : Rat) / |Algebra.norm Int (a : R)|
参数：a : R⁰；I₀ : Ideal R；h : a • (I : Submodule R K) = Submodule.map (Algebra.line
arMap R K) I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.absNorm.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst
_1 : IsDedekindDomain R] [inst_2 : Module.Free ℤ R]   [inst_3 : Module.Finite ℤ 
R] {K : Type u_2} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.absNorm_div_norm_eq_absNorm_div_norm`：absNorm_div_norm_e
q_absNorm_div_norm {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R) (h : a • (
I : Submodule R K) = Submodule.map (Algebr…
· 使用定理 `MonoidWithZeroHom.coe_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZer
oOneClass α] [inst_1 : MulZeroOneClass β] (f : ZeroHom α β)   (h1 : f.toFun 1 = 
1) (hmul : ∀ (…
· 使用定理 `ZeroHom.coe_mk`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 
: Zero N] (f : M → N) (h1 : f 0 = 0),   ⇑{ toFun := f, map_zero' := h1 } = f
-/
theorem absNorm_eq' {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
    (h : a • (I : Submodule R K) = Submodule.map (Algebra.linearMap R K) I₀) :
    absNorm I = (Ideal.absNorm I₀ : ℚ) / |Algebra.norm ℤ (a : R)| := by
  rw [absNorm, ← absNorm_div_norm_eq_absNorm_div_norm a I₀ h, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk]
/-
**FractionalIdeal.absNorm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：absNorm_nonneg (I : FractionalIdeal R⁰ K) : 0 <= absNorm I
参数：I : FractionalIdeal R⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Int.cast_nonneg`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1
 : PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] {n : ℤ},   0 ≤ n → 0 ≤ ↑n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem absNorm_nonneg (I : FractionalIdeal R⁰ K) : 0 ≤ absNorm I := by dsimp [absNorm]; positivity
/-
**FractionalIdeal.absNorm_bot** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：absNorm_bot : absNorm (⊥ : FractionalIdeal R⁰ K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.map_zero'`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M] [in
st_1 : Zero N] (self : ZeroHom M N), self.toFun 0 = 0
-/
theorem absNorm_bot : absNorm (⊥ : FractionalIdeal R⁰ K) = 0 := absNorm.map_zero'
/-
**FractionalIdeal.absNorm_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：absNorm_one : absNorm (1 : FractionalIdeal R⁰ K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidWithZeroHom.map_one'`：∀ {α : Type u_7} {β : Type u_8} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (self : α →*₀ β),   (↑self).toFun 1 
= 1
-/
theorem absNorm_one : absNorm (1 : FractionalIdeal R⁰ K) = 1 := by convert! absNorm.map_one'
/-
**FractionalIdeal.absNorm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal
`。
形式化陈述：absNorm_eq_zero_iff [IsDomain K] {I : FractionalIdeal R⁰ K} : absNorm I = 
0 ↔ I = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.zero_of_num_eq_bot`：zero_of_num_eq_bot [IsDomain R] [Mod
ule.IsTorsionFree R P] (hS : 0 ∉ S) {I : FractionalIdeal S P} (hI : I.num = ⊥) :
 I = 0
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `zero_notMem_nonZeroDivisors`：zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.absNorm_eq_zero_iff`：absNorm_eq_zero_iff {I : Ideal S} : Ideal.abs
Norm I = 0 ↔ I = ⊥
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_zero_iff`：div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `FractionalIdeal.absNorm_eq`：absNorm_eq (I : FractionalIdeal R⁰ K) : absN
orm I = (Ideal.absNorm I.num : Rat) / |Algebra.norm Int (I.den : R)|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FractionalIdeal.absNorm_bot`：absNorm_bot : absNorm (⊥ : FractionalIdeal 
R⁰ K) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem absNorm_eq_zero_iff [IsDomain K] {I : FractionalIdeal R⁰ K} :
    absNorm I = 0 ↔ I = 0 := by
  refine ⟨fun h ↦ zero_of_num_eq_bot zero_notMem_nonZeroDivisors ?_, fun h ↦ h ▸ absNorm_bot⟩
  rw [absNorm_eq, div_eq_zero_iff] at h
  refine Ideal.absNorm_eq_zero_iff.mp <| Nat.cast_eq_zero.mp <| h.resolve_right ?_
  simp [Algebra.norm_eq_zero_iff]
/-
**FractionalIdeal.coeIdeal_absNorm** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_absNorm (I₀ : Ideal R) : absNorm (I₀ : FractionalIdeal R⁰ K) = Id
eal.absNorm I₀
参数：I₀ : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.absNorm_eq'`：absNorm_eq' {I : FractionalIdeal R⁰ K} (a :
 R⁰) (I₀ : Ideal R) (h : a • (I : Submodule R K) = Submodule.map (Algebra.linear
Map R K) I₀) : ab…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `OneMemClass.coe_one`：coe_one : ((1 : S') : M₁) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem coeIdeal_absNorm (I₀ : Ideal R) :
    absNorm (I₀ : FractionalIdeal R⁰ K) = Ideal.absNorm I₀ := by
  rw [absNorm_eq' 1 I₀ (by rw [one_smul]; rfl), OneMemClass.coe_one, map_one, abs_one,
    Int.cast_one, _root_.div_one]

section IsLocalization

variable [IsLocalization (Algebra.algebraMapSubmonoid R ℤ⁰) K] [Algebra ℚ K]

/-
**FractionalIdeal.abs_det_basis_change** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdea
l`。
形式化陈述：abs_det_basis_change [IsDomain K] {ι : Type*} [Fintype ι] [DecidableEq ι] 
(b : Basis ι Int R) (I : FractionalIdeal R⁰ K) (bI : Basis ι Int I) : |(b.locali
zationLocalization Rat Int⁰ K).det ((↑) ∘ bI)| = absNorm I
参数：b : Basis ι Int R；I : FractionalIdeal R⁰ K；bI : Basis ι Int I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.nontrivial`：∀ (R : Type u_8) (S : Type u_9) [inst : CommS
emiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   [h : IsFractionRin
g R S] [hR : No…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.absNorm_eq`：absNorm_eq (I : FractionalIdeal R⁰ K) : absN
orm I = (Ideal.absNorm I.num : Rat) / |Algebra.norm Int (I.den : R)|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.natAbs_det_basis_change`：natAbs_det_basis_change {ι : Type*} [Fint
ype ι] [DecidableEq ι] (b : Basis ι Int S) (I : Ideal S) (bI : Basis ι Int I) : 
(b.det ((↑) ∘ bI)).…
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Module.Basis.localizationLocalization_repr_algebraMap`：localizationLocal
ization_repr_algebraMap {ι : Type*} (b : Basis ι R A) (x i) : (b.localizationLoc
alization Rₛ S Aₛ).repr (algebraMap A Aₛ x)…
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `FractionalIdeal.equivNum_apply`：equivNum_apply [IsDomain R] [Module.IsTo
rsionFree R P] [Nontrivial P] {I : FractionalIdeal S P} (h_nz : (I.den : R) != 0
) (x : I) : algebraM…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.toMatrix_smul`：toMatrix_smul {R₁ S : Type*} [CommSemiring R
₁] [Semiring S] [Algebra R₁ S] [Fintype ι] [DecidableEq ι] (x : S) (b : Basis ι 
R₁ S) (w : ι -> …
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Algebra.norm_eq_matrix_det`：norm_eq_matrix_det [Fintype ι] [DecidableEq 
ι] (b : Basis ι R S) (s : S) : norm R s = Matrix.det (Algebra.leftMulMatrix b s)
（共 41 条，此处仅展示前 30 条）
-/
theorem abs_det_basis_change [IsDomain K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℤ R) (I : FractionalIdeal R⁰ K) (bI : Basis ι ℤ I) :
    |(b.localizationLocalization ℚ ℤ⁰ K).det ((↑) ∘ bI)| = absNorm I := by
  have := IsFractionRing.nontrivial R K
  let b₀ : Basis ι ℚ K := b.localizationLocalization ℚ ℤ⁰ K
  let bI.num : Basis ι ℤ I.num := bI.map
      ((equivNum (nonZeroDivisors.coe_ne_zero _)).restrictScalars ℤ)
  rw [absNorm_eq, ← Ideal.natAbs_det_basis_change b I.num bI.num, Nat.cast_natAbs, Int.cast_abs,
    Int.cast_abs, Basis.det_apply, Basis.det_apply]
  change _ = |algebraMap ℤ ℚ _| / _
  rw [RingHom.map_det, show RingHom.mapMatrix (algebraMap ℤ ℚ) (b.toMatrix ((↑) ∘ bI.num)) =
      b₀.toMatrix ((algebraMap R K (den I : R)) • ((↑) ∘ bI)) by
    ext : 2
    simp_rw [bI.num, RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply,
      ← Basis.localizationLocalization_repr_algebraMap ℚ ℤ⁰ K, Function.comp_apply,
      Basis.map_apply, LinearEquiv.restrictScalars_apply, equivNum_apply, Submonoid.smul_def,
      Algebra.smul_def]
    rfl]
  rw [Basis.toMatrix_smul, Matrix.det_mul, abs_mul, ← Algebra.norm_eq_matrix_det,
    Algebra.norm_localization ℤ ℤ⁰, show (Algebra.norm ℤ (den I : R) : ℚ) =
    algebraMap ℤ ℚ (Algebra.norm ℤ (den I : R)) by rfl, mul_div_assoc, mul_div_cancel₀ _ (by
    rw [ne_eq, abs_eq_zero, IsFractionRing.to_map_eq_zero_iff, Algebra.norm_eq_zero_iff_of_basis b]
    exact nonZeroDivisors.coe_ne_zero _)]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
@[simp]
/-
**FractionalIdeal.absNorm_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：absNorm_span_singleton [Module.Finite Rat K] (x : K) : absNorm (spanSingle
ton R⁰ x) = |(Algebra.norm Rat x)|
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.isDomain`：∀ (A : Type u_4) [inst : CommRing A] {K : Type 
u_5} [inst_1 : CommRing K] [inst_2 : Algebra A K] [IsFractionRing A K]   [IsDoma
in A], IsDoma…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsLocalization.exists_integer_multiple`：exists_integer_multiple (a : S) 
: exists b : M, IsInteger R ((b : R) • a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.absNorm_eq'`：absNorm_eq' {I : FractionalIdeal R⁰ K} (a :
 R⁰) (I₀ : Ideal R) (h : a • (I : Submodule R K) = Submodule.map (Algebra.linear
Map R K) I₀) : ab…
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.norm_localization`：Algebra.norm_localization [Module.Free R S] [
Module.Finite R S] (a : S) : Algebra.norm Rₘ (algebraMap S Sₘ a) = algebraMap R 
Rₘ (Algebra.nor…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `abs_eq_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| = 0 ↔ a = 0
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
（共 40 条，此处仅展示前 30 条）
-/
theorem absNorm_span_singleton [Module.Finite ℚ K] (x : K) :
    absNorm (spanSingleton R⁰ x) = |(Algebra.norm ℚ x)| := by
  have : IsDomain K := IsFractionRing.isDomain R
  obtain ⟨d, ⟨r, hr⟩⟩ := IsLocalization.exists_integer_multiple R⁰ x
  rw [absNorm_eq' d (Ideal.span {r})]
  · rw [Ideal.absNorm_span_singleton]
    simp_rw [Nat.cast_natAbs, Int.cast_abs, show ((Algebra.norm ℤ _) : ℚ) = algebraMap ℤ ℚ
      (Algebra.norm ℤ _) by rfl, ← Algebra.norm_localization ℤ ℤ⁰ (Sₘ := K) _]
    rw [hr, Algebra.smul_def, map_mul, abs_mul, mul_div_assoc, mul_div_cancel₀ _ (by
      rw [ne_eq, abs_eq_zero, Algebra.norm_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff]
      exact nonZeroDivisors.coe_ne_zero _)]
  · ext
    simp_rw [Submodule.mem_smul_pointwise_iff_exists, mem_coe, mem_spanSingleton, Submodule.mem_map,
      Algebra.linearMap_apply, Submonoid.smul_def, Ideal.mem_span_singleton', exists_exists_eq_and,
      map_mul, hr, ← Algebra.smul_def, smul_comm (d : R)]

end IsLocalization

end FractionalIdeal

