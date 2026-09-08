/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.RingHom.Finite

/-!
# Instances for Dedekind domains

This file contains various instances to work with localization of a ring extension.

A very common situation in number theory is to have an extension of (say) Dedekind domains `R` and
`S`, and to prove a property of this extension it is useful to consider the localization `Rₚ` of `R`
at `P`, a prime ideal of `R`. One also works with the corresponding localization `Sₚ` of `S` and the
fraction fields `K` and `L` of `R` and `S`. In this situation there are many compatible algebra
structures and various properties of the rings involved. Another situation is when we have a
tower extension `R ⊆ S ⊆ T` and thus we work with `Rₚ ⊆ Sₚ ⊆ Tₚ` where
`Tₚ` is the localization of `T` at `P`. This file contains a collection of such instances.

## Implementation details
In general one wants all the results below for any algebra satisfying `IsLocalization`, but those
cannot be instances (since Lean has no way of guessing the submonoid). Having the instances in the
special case of *the* localization at a prime ideal is useful in working with Dedekind domains.

-/

public section

open nonZeroDivisors IsLocalization Algebra Module IsFractionRing IsScalarTower

attribute [local instance] FractionRing.liftAlgebra

variable {R : Type*} (S : Type*) (T : Type*) [CommRing R] [CommRing S] [CommRing T] [IsDomain R]
  [IsDomain S] [IsDomain T] [Algebra R S]

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "F" => FractionRing T

section

/-
**algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul {A : Type*} (B : Ty
pe*) [CommSemiring A] [CommSemiring B] [Algebra A B] [NoZeroDivisors B] [Faithfu
lSMul A B] {S : Submonoid A} (hS : S <= A⁰) : algebraMapSubmonoid B S <= B⁰
参数：B : Type*；hS : S <= A⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_le_nonZeroDivisors_of_injective`：map_le_nonZeroDivisors_of_injective
 [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Injective 
f) {S : Submonoid M₀} (hS…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul {A : Type*} (B : Type*)
    [CommSemiring A] [CommSemiring B] [Algebra A B] [NoZeroDivisors B] [FaithfulSMul A B]
    {S : Submonoid A} (hS : S ≤ A⁰) : algebraMapSubmonoid B S ≤ B⁰ :=
  map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective A B) hS

variable (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ] [IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] {M : Submonoid R} [IsLocalization M Rₘ]
    [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ]
    [IsScalarTower R S Sₘ] [IsLocalization (algebraMapSubmonoid S M) Sₘ]
    [Algebra (FractionRing Rₘ) (FractionRing Sₘ)]
    [IsScalarTower Rₘ (FractionRing Rₘ) (FractionRing Sₘ)]

set_option backward.isDefEq.respectTransparency false in
include R S in
/-
**FractionRing.isSeparable_of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FractionRing.isSeparable_of_isLocalization (hM : M <= R⁰) : Algebra.IsSepa
rable (FractionRing Rₘ) (FractionRing Sₘ)
参数：hM : M <= R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul`：algebraMapSubmon
oid_le_nonZeroDivisors_of_faithfulSMul {A : Type*} (B : Type*) [CommSemiring A] 
[CommSemiring B] [Algebra A B] [NoZeroDiviso…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsLocalization.localization_isScalarTower_of_submonoid_le`：localization_
isScalarTower_of_submonoid_le (M N : Submonoid R) (h : M <= N) [IsLocalization M
 S] [IsLocalization N T] : @IsScalarTower R S T…
· 使用定理 `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`：isFractionR
ing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [CommRing S] [CommR
ing T] [Algebra R S] [Algebra R T] [Algebra S T] …
· 使用定理 `IsLocalization.isDomain_of_le_nonZeroDivisors`：isDomain_of_le_nonZeroDiv
isors (hM : M <= nonZeroDivisors R) : IsDomain S where __ : IsCancelMulZero S
· 使用引理 `Algebra.IsSeparable.of_equiv_equiv`：Algebra.IsSeparable.of_equiv_equiv [
Algebra.IsSeparable A₁ B₁] : Algebra.IsSeparable A₂ B₂
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `AlgEquiv.coe_ringEquiv`：coe_ringEquiv : ((e : A₁ ≃+* A₂) : A₁ -> A₂) = e
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem FractionRing.isSeparable_of_isLocalization (hM : M ≤ R⁰) :
    Algebra.IsSeparable (FractionRing Rₘ) (FractionRing Sₘ) := by
  let M' := algebraMapSubmonoid S M
  have hM' : algebraMapSubmonoid S M ≤ S⁰ := algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
    _ hM
  let f₁ : Rₘ →+* K := map _ (T := R⁰) (RingHom.id R) hM
  let f₂ : Sₘ →+* L := map _ (T := S⁰) (RingHom.id S) hM'
  algebraize [f₁, f₂]
  have := localization_isScalarTower_of_submonoid_le Rₘ K _ _ hM
  have := localization_isScalarTower_of_submonoid_le Sₘ L _ _ hM'
  have := isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  have := isFractionRing_of_isDomain_of_isLocalization M' Sₘ L
  have : IsDomain Rₘ := isDomain_of_le_nonZeroDivisors _ hM
  apply Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv Rₘ K).symm.toRingEquiv
    (FractionRing.algEquiv Sₘ L).symm.toRingEquiv
  apply ringHom_ext R⁰
  ext
  simp only [RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, ← algebraMap_apply]
  rw [algebraMap_apply R Rₘ (FractionRing R), AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
    algebraMap_apply R S L, algebraMap_apply S Sₘ L, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  simp only [← algebraMap_apply]
  rw [algebraMap_apply R Rₘ (FractionRing Rₘ), ← algebraMap_apply Rₘ, ← algebraMap_apply]

end

variable {P : Ideal R} [P.IsPrime]

local notation3 "P'" => algebraMapSubmonoid S P.primeCompl
local notation3 "Rₚ" => Localization.AtPrime P
local notation3 "Sₚ" => Localization P'

variable [FaithfulSMul R S]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTorsionFree S Sₚ := by
  rw [isTorsionFree_iff_algebraMap_injective,
    injective_iff_isRegular (algebraMapSubmonoid S P.primeCompl)]
  exact fun ⟨x, hx⟩ ↦ isRegular_iff_ne_zero'.mpr <|
    ne_of_mem_of_not_mem hx <| by simp [Algebra.algebraMapSubmonoid]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTorsionFree R Sₚ := by
  have := IsLocalization.AtPrime.faithfulSMul Rₚ R P
  exact IsTorsionFree.trans_faithfulSMul R Rₚ _

/--
This is not an instance because it creates a diamond with `OreLocalization.instAlgebra`.
-/
/-
**Localization.AtPrime.liftAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Localization.AtPrime.liftAlgebra : Algebra Sₚ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not an instance because it creates a diamond with `OreLocalization.instA
lgebra`.
-/
noncomputable abbrev Localization.AtPrime.liftAlgebra : Algebra Sₚ L :=
  (map _ (T := S⁰) (RingHom.id S)
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)).toAlgebra

attribute [local instance] Localization.AtPrime.liftAlgebra
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower S Sₚ L :=
  localization_isScalarTower_of_submonoid_le _ _ _ _
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFractionRing Rₚ K :=
  isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFractionRing Sₚ L :=
  isFractionRing_of_isDomain_of_isLocalization P' _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Algebra Rₚ L :=
  (lift (M := P.primeCompl) (g := algebraMap R L) <|
    fun ⟨x, hx⟩ ↦ by simpa using fun h ↦ hx <| by simp [h]).toAlgebra

-- Make sure there are no diamonds in the case `R = S`.
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : instAlgebraLocalizationAtPrime P = instAlgebraAtPrimeFractionRing (S := R) := by
  with_reducible_and_instances rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower Rₚ K L :=
  of_algebraMap_eq' (ringHom_ext P.primeCompl
    (RingHom.ext fun x ↦ by simp [RingHom.algebraMap_toAlgebra]))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R Rₚ K :=
  of_algebraMap_eq' (RingHom.ext fun x ↦ by simp [RingHom.algebraMap_toAlgebra])
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower Rₚ Sₚ L := by
  refine IsScalarTower.of_algebraMap_eq' <| IsLocalization.ringHom_ext P.primeCompl ?_
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R Rₚ Sₚ, IsScalarTower.algebraMap_eq R S Sₚ,
    ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq S Sₚ L, IsScalarTower.algebraMap_eq Rₚ K L,
    RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq]

set_option linter.overlappingInstances false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDedekindDomain S] : IsDedekindDomain Sₚ :=
  isDedekindDomain S
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ P.primeCompl_le_nonZeroDivisors) _

set_option linter.overlappingInstances false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [hP : NeZero P] :
    IsPrincipalIdealRing Sₚ :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P (fun h ↦ hP.1 h)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsSeparable K L] :
    -- Without the following line there is a timeout
    letI : Algebra Rₚ (FractionRing Sₚ) := OreLocalization.instAlgebra
    Algebra.IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) :=
  let _ : Algebra Rₚ (FractionRing Sₚ) := OreLocalization.instAlgebra
  FractionRing.isSeparable_of_isLocalization S _ _ P.primeCompl_le_nonZeroDivisors

local notation3 "P''" => algebraMapSubmonoid T P.primeCompl
local notation3 "Tₚ" => Localization P''

variable [Algebra S T] [Algebra R T] [IsScalarTower R S T]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalization (algebraMapSubmonoid T P') Tₚ := by
  rw [show algebraMapSubmonoid T P' = P'' by simp]
  exact Localization.isLocalization

/--
Let `R ⊆ S ⊆ T` be a tower of rings. Let `Sₚ` and `Tₚ` denote the localizations of `S` and `T` at
the prime ideal `P` of `R`. Then `Tₚ` is a `Sₚ`-algebra.
This cannot be an instance since it creates a diamond when `S = T`.
-/
/-
**Localization.AtPrime.algebra_localization_localization** 是 Mathlib 中的一个缩写定义，位于
命名空间 ``。
形式化陈述：Localization.AtPrime.algebra_localization_localization : Algebra Sₚ Tₚ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLocalizationAlgebraMapSubmonoidPrimeComplLocalization`：∀ {R : Type
 u_1} (S : Type u_2) (T : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : CommRing T]   [inst_3 : Algebra R S] {P :…

--- 原说明 ---
Let `R ⊆ S ⊆ T` be a tower of rings. Let `Sₚ` and `Tₚ` denote the localizations 
of `S` and `T` at
the prime ideal `P` of `R`. Then `Tₚ` is a `Sₚ`-algebra.
This cannot be an instance since it creates a diamond when `S = T`.
-/
noncomputable abbrev Localization.AtPrime.algebra_localization_localization :
    Algebra Sₚ Tₚ := localizationAlgebra P' T

attribute [local instance] Localization.AtPrime.algebra_localization_localization
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower S Sₚ Tₚ :=
  IsScalarTower.of_algebraMap_eq' <|
    by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R Sₚ Tₚ :=
  IsScalarTower.of_algebraMap_eq' <|
    by rw [IsScalarTower.algebraMap_eq R S Sₚ, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq S, ← IsScalarTower.algebraMap_eq]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Finite S T] : Module.Finite Sₚ Tₚ := Module.Finite.of_isLocalization S T P'
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTorsionFree S T] : IsTorsionFree Sₚ Tₚ :=
  .of_isLocalization S T <| algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ <|
    Ideal.primeCompl_le_nonZeroDivisors P
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsIntegral R S] : Algebra.IsIntegral Rₚ Sₚ :=
  Algebra.isIntegral_def.mpr <| (algebraMap_eq_map_map_submonoid P.primeCompl S Rₚ Sₚ ▸
    isIntegral_localization : (algebraMap Rₚ Sₚ).IsIntegral)

variable [IsTorsionFree R T]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower Rₚ Sₚ Tₚ := by
  refine ⟨fun a b c ↦ a.ind fun ⟨a₁, a₂⟩ ↦ ?_⟩
  have : a₂.val ≠ 0 := nonZeroDivisors.ne_zero <| Ideal.primeCompl_le_nonZeroDivisors P <| a₂.prop
  rw [← smul_right_inj this, ← _root_.smul_assoc (M := R) (N := Sₚ), ← _root_.smul_assoc (M := R)
    (α := Sₚ), ← _root_.smul_assoc (M := R) (α := Tₚ), Localization.smul_mk, smul_eq_mul,
    Localization.mk_eq_mk', IsLocalization.mk'_mul_cancel_left, algebraMap_smul, algebraMap_smul,
    _root_.smul_assoc]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTorsionFree S T] [Algebra.IsSeparable L F] :
    Algebra.IsSeparable (FractionRing Sₚ) (FractionRing Tₚ) := by
  refine FractionRing.isSeparable_of_isLocalization T Sₚ Tₚ (M := P') ?_
  apply algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
  exact fun _ h ↦ mem_nonZeroDivisors_of_ne_zero <| ne_of_mem_of_not_mem h <| by simp
