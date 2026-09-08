/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SurjectiveOnStalks

/-!
# The residue field of a prime ideal

We define `Ideal.ResidueField I` to be the residue field of the local ring `Localization.Prime I`,
and provide an `IsFractionRing (R ⧸ I) I.ResidueField` instance.

-/

@[expose] public section

open scoped nonZeroDivisors

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (I : Ideal R) [I.IsPrime]

/--
The residue field at a prime ideal, defined to be the residue field of the local ring
`Localization.Prime I`.
We also provide an `IsFractionRing (R ⧸ I) I.ResidueField` instance.
-/
/-
**Ideal.ResidueField** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal.ResidueField : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The residue field at a prime ideal, defined to be the residue field of the local
 ring
`Localization.Prime I`.
We also provide an `IsFractionRing (R ⧸ I) I.ResidueField` instance.
-/
abbrev Ideal.ResidueField : Type _ :=
  IsLocalRing.ResidueField (Localization.AtPrime I)

/-- If `I = f⁻¹(J)`, then there is a canonical embedding `κ(I) ↪ κ(J)`. -/
noncomputable
/-
**Ideal.ResidueField.map** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.map (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
 (f : R ->+* S) (hf : I = J.comap f) : I.ResidueField ->+* J.ResidueField
参数：I : Ideal R；J : Ideal S；f : R ->+* S；hf : I = J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Ideal.ResidueField.map (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
    (f : R →+* S) (hf : I = J.comap f) : I.ResidueField →+* J.ResidueField :=
  IsLocalRing.ResidueField.map (Localization.localRingHom I J f hf)

@[simp]
/-
**Ideal.ResidueField.map_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.map_algebraMap (I : Ideal R) [I.IsPrime] (J : Ideal S) 
[J.IsPrime] (f : R ->+* S) (hf : I = J.comap f) (r : R) : ResidueField.map I J f
 hf (algebraMap _ _ r) = algebraMap _ _ (f r)
参数：I : Ideal R；J : Ideal S；f : R ->+* S；hf : I = J.comap f；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
-/
lemma Ideal.ResidueField.map_algebraMap (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
    (f : R →+* S) (hf : I = J.comap f) (r : R) :
    ResidueField.map I J f hf (algebraMap _ _ r) = algebraMap _ _ (f r) := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I)]
  simp [IsLocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
  rfl
/-
**RingHom.SurjectiveOnStalks.residueFieldMap_bijective** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：RingHom.SurjectiveOnStalks.residueFieldMap_bijective {f : R ->+* S} (H : f
.SurjectiveOnStalks) (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (hf : I
 = J.comap f) : Function.Bijective (Ideal.ResidueField.map I J f hf)
参数：H : f.SurjectiveOnStalks；I : Ideal R；J : Ideal S；hf : I = J.comap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Ideal.Quotient.lift_surjective_of_surjective`：lift_surjective_of_surject
ive {f : R ->+* S} (H : forall a : R, a in I -> f a = 0) (hf : Function.Surjecti
ve f) : Function.Surjective (Ideal…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
-/
lemma RingHom.SurjectiveOnStalks.residueFieldMap_bijective
    {f : R →+* S} (H : f.SurjectiveOnStalks)
    (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (hf : I = J.comap f) :
    Function.Bijective (Ideal.ResidueField.map I J f hf) := by
  subst hf
  exact ⟨RingHom.injective _, Ideal.Quotient.lift_surjective_of_surjective _ _
    (Ideal.Quotient.mk_surjective.comp (H J ‹_›))⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `I = f⁻¹(J)`, then there is a canonical embedding `κ(I) ↪ κ(J)`. -/
noncomputable
/-
**Ideal.ResidueField.map** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.map (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
 (f : R ->+* S) (hf : I = J.comap f) : I.ResidueField ->+* J.ResidueField
参数：I : Ideal R；J : Ideal S；f : R ->+* S；hf : I = J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Ideal.ResidueField.mapₐ (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (f : A →ₐ[R] B) (hf : I = J.comap f.toRingHom) : I.ResidueField →ₐ[R] J.ResidueField where
  __ := Ideal.ResidueField.map I J f hf
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R A I.ResidueField,
      IsScalarTower.algebraMap_apply R B J.ResidueField]
/-
**Ideal.ResidueField.map** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.map (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
 (f : R ->+* S) (hf : I = J.comap f) : I.ResidueField ->+* J.ResidueField
参数：I : Ideal R；J : Ideal S；f : R ->+* S；hf : I = J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Ideal.ResidueField.mapₐ_apply (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (f : A →ₐ[R] B) (hf : I = J.comap f.toRingHom) (x) :
    Ideal.ResidueField.mapₐ I J f hf x = Ideal.ResidueField.map I J _ hf x := rfl

variable {I} in
@[simp high] -- marked `high` to override the more general `FaithfulSMul.algebraMap_eq_zero_iff`
/-
**Ideal.algebraMap_residueField_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.algebraMap_residueField_eq_zero {x} : algebraMap R I.ResidueField x 
= 0 ↔ x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalRing.ResidueField.algebraMap_eq`：∀ (R : Type u_1) [inst : CommRin
g R] [inst_1 : IsLocalRing R],   algebraMap R (IsLocalRing.ResidueField R) = IsL
ocalRing.residue R
· 使用引理 `IsLocalRing.residue_eq_zero_iff`：residue_eq_zero_iff (x : R) : residue R
 x = 0 ↔ x in maximalIdeal R
· 使用定理 `IsLocalization.AtPrime.to_map_mem_maximal_iff`：to_map_mem_maximal_iff (x
 : R) (h : IsLocalRing S
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
-/
lemma Ideal.algebraMap_residueField_eq_zero {x} :
    algebraMap R I.ResidueField x = 0 ↔ x ∈ I := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I),
    IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _

@[simp high] -- marked `high` to override the more general `FaithfulSMul.ker_algebraMap_eq_bot`
/-
**Ideal.ker_algebraMap_residueField** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.ker_algebraMap_residueField : RingHom.ker (algebraMap R I.ResidueFie
ld) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用引理 `Ideal.algebraMap_residueField_eq_zero`：Ideal.algebraMap_residueField_eq_
zero {x} : algebraMap R I.ResidueField x = 0 ↔ x in I
-/
lemma Ideal.ker_algebraMap_residueField :
    RingHom.ker (algebraMap R I.ResidueField) = I :=
  Ideal.ext fun _ ↦ Ideal.algebraMap_residueField_eq_zero

attribute [-instance] IsLocalRing.ResidueField.field in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Algebra (R ⧸ I) I.ResidueField :=
  (Ideal.Quotient.liftₐ I (Algebra.ofId _ _)
    fun _ ↦ Ideal.algebraMap_residueField_eq_zero.mpr).toRingHom.toAlgebra
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Ideal A) [I.IsPrime] : IsScalarTower R (A ⧸ I) I.ResidueField :=
  .of_algebraMap_eq' rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Ideal R) [I.IsPrime] : (⊥ : Ideal I.ResidueField).LiesOver I :=
  ⟨I.ker_algebraMap_residueField.symm⟩

@[simp]
/-
**Ideal.algebraMap_quotient_residueField_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.algebraMap_quotient_residueField_mk (x) : algebraMap (R ⧸ I) I.Resid
ueField (Ideal.Quotient.mk _ x) = algebraMap R I.ResidueField x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma Ideal.algebraMap_quotient_residueField_mk (x) :
    algebraMap (R ⧸ I) I.ResidueField (Ideal.Quotient.mk _ x) =
    algebraMap R I.ResidueField x := rfl
/-
**Ideal.injective_algebraMap_quotient_residueField** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.injective_algebraMap_quotient_residueField : Function.Injective (alg
ebraMap (R ⧸ I) I.ResidueField)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.ker_quotient_lift`：ker_quotient_lift {I : Ideal R} [I.IsTwoSided] 
(f : R ->+* S) (H : I <= ker f) : ker (Ideal.Quotient.lift I f H) = (RingHom.ker
 f).map (Quot…
· 使用引理 `Ideal.ker_algebraMap_residueField`：Ideal.ker_algebraMap_residueField : R
ingHom.ker (algebraMap R I.ResidueField) = I
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
-/
lemma Ideal.injective_algebraMap_quotient_residueField :
    Function.Injective (algebraMap (R ⧸ I) I.ResidueField) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine (Ideal.ker_quotient_lift _ _).trans ?_
  change map (Quotient.mk I) (RingHom.ker (algebraMap R I.ResidueField)) = ⊥
  rw [Ideal.ker_algebraMap_residueField, map_quotient_self]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFractionRing (R ⧸ I) I.ResidueField where
  map_units y := isUnit_iff_ne_zero.mpr
    (map_ne_zero_of_mem_nonZeroDivisors _ I.injective_algebraMap_quotient_residueField y.2)
  surj x := by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq I.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk _ x, ⟨Ideal.Quotient.mk _ s, ?_⟩⟩, ?_⟩
    · rwa [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    · simp [IsScalarTower.algebraMap_eq R (Localization.AtPrime I) I.ResidueField, ← map_mul]
  exists_of_eq {x y} e := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← sub_eq_zero, ← map_sub, ← map_sub] at e
    simp only [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime I) I.ResidueField,
      Ideal.algebraMap_quotient_residueField_mk, IsLocalization.AtPrime.to_map_mem_maximal_iff _ I,
      ← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at e
    use 1
    simp [e]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain R] : IsFractionRing R (⊥ : Ideal R).ResidueField :=
  IsLocalization.of_ringEquiv_left (RingEquiv.quotientBot R).symm
    (MulEquivClass.map_nonZeroDivisors (RingEquiv.quotientBot R).symm) (by simp)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite (R ⧸ I)] : Finite I.ResidueField :=
  IsLocalization.finite (R ⧸ I) (nonZeroDivisors (R ⧸ I))
/-
**Ideal.bijective_algebraMap_quotient_residueField** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.bijective_algebraMap_quotient_residueField (I : Ideal R) [I.IsMaxima
l] : Function.Bijective (algebraMap (R ⧸ I) I.ResidueField)
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用引理 `Ideal.injective_algebraMap_quotient_residueField`：Ideal.injective_algebr
aMap_quotient_residueField : Function.Injective (algebraMap (R ⧸ I) I.ResidueFie
ld)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsFractionRing.surjective_iff_isField`：surjective_iff_isField [IsDomain 
R] : Function.Surjective (algebraMap R K) ↔ IsField R where mp h
· 使用定理 `instIsFractionRingQuotientIdealResidueField`：∀ {R : Type u_1} [inst : Co
mmRing R] (I : Ideal R) [inst_1 : I.IsPrime], IsFractionRing (R ⧸ I) I.ResidueFi
eld
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.maximal_ideal_iff_isField_quotient`：maximal_ideal_iff_isF
ield_quotient {R} [CommRing R] (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I)
-/
lemma Ideal.bijective_algebraMap_quotient_residueField (I : Ideal R) [I.IsMaximal] :
    Function.Bijective (algebraMap (R ⧸ I) I.ResidueField) :=
  ⟨I.injective_algebraMap_quotient_residueField, IsFractionRing.surjective_iff_isField.mpr
    ((Quotient.maximal_ideal_iff_isField_quotient I).mp inferInstance)⟩
/-
**Ideal.algebraMap_residueField_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.algebraMap_residueField_surjective (I : Ideal R) [I.IsMaximal] : Fun
ction.Surjective (algebraMap R I.ResidueField)
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `instIsScalarTowerQuotientIdealResidueField`：∀ {R : Type u_1} {A : Type u
_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal 
A)   [inst_3 : I.IsPrime], IsSca…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用引理 `Ideal.bijective_algebraMap_quotient_residueField`：Ideal.bijective_algebr
aMap_quotient_residueField (I : Ideal R) [I.IsMaximal] : Function.Bijective (alg
ebraMap (R ⧸ I) I.ResidueField)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
-/
lemma Ideal.algebraMap_residueField_surjective (I : Ideal R) [I.IsMaximal] :
    Function.Surjective (algebraMap R I.ResidueField) := by
  rw [IsScalarTower.algebraMap_eq R (R ⧸ I) _]
  exact I.bijective_algebraMap_quotient_residueField.surjective.comp Ideal.Quotient.mk_surjective
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Ideal R) [I.IsMaximal] : Module.Finite R I.ResidueField :=
  .of_surjective (Algebra.linearMap _ _) I.algebraMap_residueField_surjective

/-- The equivalence between a field and the residue field of its prime ideal,
induced by the algebra map. -/
/-
**Ideal.algEquivResidueFieldOfField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.algEquivResidueFieldOfField {k : Type*} [Field k] (p : Ideal k) [p.I
sPrime] : k ≃ₐ[k] p.ResidueField
参数：p : Ideal k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between a field and the residue field of its prime ideal,
induced by the algebra map.
-/
noncomputable def Ideal.algEquivResidueFieldOfField {k : Type*} [Field k]
    (p : Ideal k) [p.IsPrime] : k ≃ₐ[k] p.ResidueField :=
  AlgEquiv.ofBijective (Algebra.ofId k _) ⟨RingHom.injective _,
    haveI : p.IsMaximal := by simpa [p.eq_bot_of_prime] using Ideal.bot_isMaximal
    p.algebraMap_residueField_surjective⟩

@[simp]
/-
**Ideal.algEquivResidueFieldOfField_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.algEquivResidueFieldOfField_apply {k : Type*} [Field k] (p : Ideal k
) [p.IsPrime] (x : k) : p.algEquivResidueFieldOfField x = algebraMap k p.Residue
Field x
参数：p : Ideal k；x : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ideal.algEquivResidueFieldOfField_apply {k : Type*} [Field k] (p : Ideal k) [p.IsPrime]
    (x : k) : p.algEquivResidueFieldOfField x = algebraMap k p.ResidueField x :=
  rfl
/-
**Ideal.surjectiveOnStalks_residueField** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.surjectiveOnStalks_residueField (I : Ideal R) [I.IsPrime] : (algebra
Map R I.ResidueField).SurjectiveOnStalks
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.SurjectiveOnStalks.comp`：∀ {R : Type u_1} [inst : CommRing R] {S
 : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRing T]   {g : S
 →+* T} {f : R →+* S}…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `RingHom.surjectiveOnStalks_of_surjective`：surjectiveOnStalks_of_surjecti
ve (h : Function.Surjective f) : SurjectiveOnStalks f
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用引理 `RingHom.surjectiveOnStalks_of_isLocalization`：surjectiveOnStalks_of_isLo
calization [Algebra R S] [IsLocalization M S] : SurjectiveOnStalks (algebraMap R
 S)
-/
lemma Ideal.surjectiveOnStalks_residueField (I : Ideal R) [I.IsPrime] :
    (algebraMap R I.ResidueField).SurjectiveOnStalks :=
  (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective).comp
    (RingHom.surjectiveOnStalks_of_isLocalization I.primeCompl _)

section

open Localization AtPrime

variable (J : Ideal A) (K : Ideal B) [J.IsPrime] [K.IsPrime]
  [J.LiesOver I] [Algebra (Localization.AtPrime I) (Localization.AtPrime J)] [IsLiesOverAlgebra I J]
  [K.LiesOver I] [Algebra (Localization.AtPrime I) (Localization.AtPrime K)] [IsLiesOverAlgebra I K]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalHom (algebraMap (Localization.AtPrime I) (Localization.AtPrime J)) := by
  rw [IsLiesOverAlgebra.algebraMap_eq]
  exact isLocalHom_localRingHom _ _ _ (J.over_def I)

/-- An isomorphism of rings induces an isomorphism of residue fields. -/
/-
**Ideal.residueFieldRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.residueFieldRingEquiv (f : A ≃+* B) (h : J = K.comap f) : J.ResidueF
ield ≃+* K.ResidueField
参数：f : A ≃+* B；h : J = K.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of rings induces an isomorphism of residue fields.
-/
noncomputable def Ideal.residueFieldRingEquiv (f : A ≃+* B) (h : J = K.comap f) :
    J.ResidueField ≃+* K.ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (localRingEquiv J K f h)

/-- An isomorphism of rings induces an isomorphism of residue fields. -/
/-
**Ideal.residueFieldAlgEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal.residueFieldAlgEquiv (f : A ≃ₐ[R] B) (h : J = K.comap f) : J.Residue
Field ≃ₐ[R] K.ResidueField
参数：f : A ≃ₐ[R] B；h : J = K.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of rings induces an isomorphism of residue fields.
-/
noncomputable abbrev Ideal.residueFieldAlgEquiv (f : A ≃ₐ[R] B) (h : J = K.comap f) :
    J.ResidueField ≃ₐ[R] K.ResidueField :=
  IsLocalRing.ResidueField.mapAlgEquiv (localAlgEquiv J K f h)

/-- An isomorphism of rings induces an isomorphism of residue fields. -/
/-
**Ideal.residueFieldAlgEquiv'** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal.residueFieldAlgEquiv' (f : A ≃ₐ[R] B) (h : J = K.comap f) : J.Residu
eField ≃ₐ[I.ResidueField] K.ResidueField
参数：f : A ≃ₐ[R] B；h : J = K.comap f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…

--- 原说明 ---
An isomorphism of rings induces an isomorphism of residue fields.
-/
noncomputable abbrev Ideal.residueFieldAlgEquiv' (f : A ≃ₐ[R] B) (h : J = K.comap f) :
    J.ResidueField ≃ₐ[I.ResidueField] K.ResidueField :=
  IsLocalRing.ResidueField.mapAlgEquiv' (localAlgEquiv' I J K f h)

end

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Ideal R) [p.IsPrime] : Algebra.EssFiniteType R p.ResidueField :=
  .comp _ (Localization.AtPrime p) _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.EssFiniteType R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Algebra.EssFiniteType p.ResidueField q.ResidueField := by
  have : Algebra.EssFiniteType R q.ResidueField := .comp _ A _
  refine .of_comp R _ _

/-- If `f` sends `I` to `0` and `Iᶜ` to units, then `f` lifts to `κ(I)`. -/
/-
**Ideal.ResidueField.lift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.lift (f : R ->+* S) (hf₁ : I <= RingHom.ker f) (hf₂ : I
.primeCompl <= (IsUnit.submonoid S).comap f) : I.ResidueField ->+* S
参数：f : R ->+* S；hf₁ : I <= RingHom.ker f；hf₂ : I.primeCompl <= (IsUnit.submonoid
 S).comap f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsFractionRingQuotientIdealResidueField`：∀ {R : Type u_1} [inst : Co
mmRing R] (I : Ideal R) [inst_1 : I.IsPrime], IsFractionRing (R ⧸ I) I.ResidueFi
eld
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
If `f` sends `I` to `0` and `Iᶜ` to units, then `f` lifts to `κ(I)`.
-/
noncomputable def Ideal.ResidueField.lift
    (f : R →+* S) (hf₁ : I ≤ RingHom.ker f)
    (hf₂ : I.primeCompl ≤ (IsUnit.submonoid S).comap f) : I.ResidueField →+* S :=
  IsLocalization.lift (M := (R ⧸ I)⁰) (g := Ideal.Quotient.lift I (f := f) hf₁) <| by
    simpa [Ideal.Quotient.mk_surjective.forall, Ideal.Quotient.eq_zero_iff_mem]

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.ResidueField.lift_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.ResidueFie
ld`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
(I : Ideal R) [inst_2 : I.IsPrime]   (f : R →+* S) (hf₁ : I ≤ RingHom.ker f) (hf
₂ : I.primeCompl ≤ Submonoid.comap f (IsUnit.submonoid S)) (r : R),   (Ideal.Res
idueField.lift I f hf₁ hf₂) ((algebraMap R I.ResidueField) r) = f r
参数：I : Ideal R；f : R →+* S；hf₁ : I ≤ RingHom.ker f；hf₂ : I.primeCompl ≤ Submonoi
d.comap f (IsUnit.submonoid S)；r : R；Ideal.ResidueField.lift I f hf₁ hf₂；(algebr
aMap R I.ResidueField) r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instIsFractionRingQuotientIdealResidueField`：∀ {R : Type u_1} [inst : Co
mmRing R] (I : Ideal R) [inst_1 : I.IsPrime], IsFractionRing (R ⧸ I) I.ResidueFi
eld
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ResidueField.lift.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst : Co
mmRing R] [inst_1 : CommRing S] (I : Ideal R) [inst_2 : I.IsPrime]   (f : R →+* 
S) (hf₁ : I ≤ Ring…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `instIsScalarTowerQuotientIdealResidueField`：∀ {R : Type u_1} {A : Type u
_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal 
A)   [inst_3 : I.IsPrime], IsSca…
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma Ideal.ResidueField.lift_algebraMap
    (f : R →+* S) (hf₁ : I ≤ RingHom.ker f)
    (hf₂ : I.primeCompl ≤ (IsUnit.submonoid S).comap f) (r : R) :
    lift I f hf₁ hf₂ (algebraMap _ _ r) = f r := by
  rw [lift, IsScalarTower.algebraMap_apply R (R ⧸ I) I.ResidueField, IsLocalization.lift_eq]
  simp

/-- If `f` sends `I` to `0` and `Iᶜ` to units, then `f` lifts to `κ(I)`. -/
noncomputable
/-
**Ideal.ResidueField.lift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.lift (f : R ->+* S) (hf₁ : I <= RingHom.ker f) (hf₂ : I
.primeCompl <= (IsUnit.submonoid S).comap f) : I.ResidueField ->+* S
参数：f : R ->+* S；hf₁ : I <= RingHom.ker f；hf₂ : I.primeCompl <= (IsUnit.submonoid
 S).comap f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsFractionRingQuotientIdealResidueField`：∀ {R : Type u_1} [inst : Co
mmRing R] (I : Ideal R) [inst_1 : I.IsPrime], IsFractionRing (R ⧸ I) I.ResidueFi
eld
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
def Ideal.ResidueField.liftₐ (I : Ideal A) [I.IsPrime] (f : A →ₐ[R] B) (hf₁ : I ≤ RingHom.ker f)
    (hf₂ : I.primeCompl ≤ (IsUnit.submonoid B).comap f) : I.ResidueField →ₐ[R] B where
  __ := Ideal.ResidueField.lift I f.toRingHom hf₁ hf₂
  commutes' r := by simp [IsScalarTower.algebraMap_apply R A I.ResidueField]

@[simp]
/-
**Ideal.ResidueField.lift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.lift (f : R ->+* S) (hf₁ : I <= RingHom.ker f) (hf₂ : I
.primeCompl <= (IsUnit.submonoid S).comap f) : I.ResidueField ->+* S
参数：f : R ->+* S；hf₁ : I <= RingHom.ker f；hf₂ : I.primeCompl <= (IsUnit.submonoid
 S).comap f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsFractionRingQuotientIdealResidueField`：∀ {R : Type u_1} [inst : Co
mmRing R] (I : Ideal R) [inst_1 : I.IsPrime], IsFractionRing (R ⧸ I) I.ResidueFi
eld
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma Ideal.ResidueField.liftₐ_algebraMap (I : Ideal A) [I.IsPrime] (f : A →ₐ[R] B)
    (hf₁ : I ≤ RingHom.ker f) (hf₂ : I.primeCompl ≤ (IsUnit.submonoid B).comap f) (r : A) :
    liftₐ I f hf₁ hf₂ (algebraMap _ _ r) = f r :=
  lift_algebraMap _ _ _ hf₂ _
/-
**Ideal.ResidueField.lift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.lift (f : R ->+* S) (hf₁ : I <= RingHom.ker f) (hf₂ : I
.primeCompl <= (IsUnit.submonoid S).comap f) : I.ResidueField ->+* S
参数：f : R ->+* S；hf₁ : I <= RingHom.ker f；hf₂ : I.primeCompl <= (IsUnit.submonoid
 S).comap f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsFractionRingQuotientIdealResidueField`：∀ {R : Type u_1} [inst : Co
mmRing R] (I : Ideal R) [inst_1 : I.IsPrime], IsFractionRing (R ⧸ I) I.ResidueFi
eld
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
@[simp] lemma Ideal.ResidueField.liftₐ_comp_toAlgHom (I : Ideal A) [I.IsPrime] (f : A →ₐ[R] B)
    (hf₁ : I ≤ RingHom.ker f) (hf₂ : I.primeCompl ≤ (IsUnit.submonoid B).comap f) :
    (liftₐ I f hf₁ hf₂).comp (IsScalarTower.toAlgHom _ A _) = f :=
  AlgHom.ext fun _ ↦ liftₐ_algebraMap _ _ _ hf₂ _

@[ext high] -- higher than `RingHom.ext`.
/-
**Ideal.ResidueField.ringHom_ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.ringHom_ext {I : Ideal R} [I.IsPrime] {f g : I.ResidueF
ield ->+* S} (H : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g
参数：H : f.comp (algebraMap R _) = g.comp (algebraMap R _)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `instIsFractionRingQuotientIdealResidueField`：∀ {R : Type u_1} [inst : Co
mmRing R] (I : Ideal R) [inst_1 : I.IsPrime], IsFractionRing (R ⧸ I) I.ResidueFi
eld
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma Ideal.ResidueField.ringHom_ext {I : Ideal R} [I.IsPrime]
    {f g : I.ResidueField →+* S} (H : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g :=
  IsLocalization.ringHom_ext (R ⧸ I)⁰ (Ideal.Quotient.ringHom_ext H)

@[ext high] -- higher than `AlgHom.ext`.
/-
**Ideal.ResidueField.algHom_ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.algHom_ext {I : Ideal A} [I.IsPrime] {f g : I.ResidueFi
eld ->ₐ[R] B} (H : f.comp (IsScalarTower.toAlgHom R A _) = g.comp (IsScalarTower
.toAlgHom R A _)) : f = g
参数：H : f.comp (IsScalarTower.toAlgHom R A _) = g.comp (IsScalarTower.toAlgHom R 
A _)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用引理 `Ideal.ResidueField.ringHom_ext`：Ideal.ResidueField.ringHom_ext {I : Idea
l R} [I.IsPrime] {f g : I.ResidueField ->+* S} (H : f.comp (algebraMap R _) = g.
comp (algebraMap R _…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma Ideal.ResidueField.algHom_ext {I : Ideal A} [I.IsPrime] {f g : I.ResidueField →ₐ[R] B}
    (H : f.comp (IsScalarTower.toAlgHom R A _) = g.comp (IsScalarTower.toAlgHom R A _)) : f = g :=
  AlgHom.coe_ringHom_injective (ringHom_ext congr($H))

set_option backward.isDefEq.respectTransparency.types false in
/-
**Ideal.ResidueField.map** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal.ResidueField.map (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
 (f : R ->+* S) (hf : I = J.comap f) : I.ResidueField ->+* J.ResidueField
参数：I : Ideal R；J : Ideal S；f : R ->+* S；hf : I = J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Ideal.ResidueField.mapₐ_id (I : Ideal A) [I.IsPrime] :
    Ideal.ResidueField.mapₐ I I (.id R A) rfl = .id _ _ := by ext; simp
