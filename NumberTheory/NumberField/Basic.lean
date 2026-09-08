/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.AddMonoidHom
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Number fields

This file defines a number field and the ring of integers corresponding to it.

## Main definitions
- `NumberField` defines a number field as a field which has characteristic zero and is finite
  dimensional over ℚ.
- `RingOfIntegers` defines the ring of integers (or number ring) corresponding to a number field
  as the integral closure of ℤ in the number field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags
number field, ring of integers
-/

@[expose] public section

/-- A number field is a field which has characteristic zero and is finite
dimensional over ℚ. -/
@[stacks 09GA, wikidata Q616608]
/-
**NumberField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_1) → [Field K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A number field is a field which has characteristic zero and is finite
dimensional over ℚ.
-/
class NumberField (K : Type*) [Field K] : Prop where
  [to_charZero : CharZero K]
  [to_finiteDimensional : FiniteDimensional ℚ K]

open Function Module

open scoped nonZeroDivisors

namespace NumberField

variable (K L : Type*) [Field K] [Field L]

-- See note [lower instance priority]
attribute [instance] NumberField.to_charZero NumberField.to_finiteDimensional

/-
**NumberField.isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K], Algebra.IsAlge
braic ℚ K
参数：K : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
-/
protected theorem isAlgebraic [NumberField K] : Algebra.IsAlgebraic ℚ K :=
  Algebra.IsAlgebraic.of_finite _ _
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NumberField K] [NumberField L] [Algebra K L] : FiniteDimensional K L :=
  Module.Finite.of_restrictScalars_finite ℚ K L

/-- A finite extension of a number field is a number field. -/
/-
**NumberField.of_module_finite** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：of_module_finite [NumberField K] [Algebra K L] [Module.Finite K L] : Numbe
rField L where to_charZero
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `charZero_of_injective_algebraMap`：charZero_of_injective_algebraMap [Comm
Semiring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A))
 [CharZero R] : CharZe…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K

--- 原说明 ---
A finite extension of a number field is a number field.
-/
theorem of_module_finite [NumberField K] [Algebra K L] [Module.Finite K L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional :=
    letI := charZero_of_injective_algebraMap (algebraMap K L).injective
    Module.Finite.trans K L

variable {K} {L} in
/-
**NumberField.of_intermediateField** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
形式化陈述：of_intermediateField [NumberField K] [NumberField L] [Algebra K L] (E : In
termediateField K L) : NumberField E
参数：E : IntermediateField K L。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.of_module_finite`：of_module_finite [NumberField K] [Algebra 
K L] [Module.Finite K L] : NumberField L where to_charZero
· 使用定理 `NumberField.instFiniteDimensional`：∀ (K : Type u_1) (L : Type u_2) [inst
 : Field K] [inst_1 : Field L] [NumberField K] [NumberField L]   [inst_4 : Algeb
ra K L], FiniteDimensio…
-/
instance of_intermediateField [NumberField K] [NumberField L] [Algebra K L]
    (E : IntermediateField K L) : NumberField E :=
  of_module_finite K E

variable {K} in
/-
**NumberField.of_subfield** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
形式化陈述：of_subfield [NumberField K] (E : Subfield K) : NumberField E where to_fini
teDimensional
参数：E : Subfield K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `FiniteDimensional.left`：∀ (F : Type u) (K : Type v) (A : Type w) [inst :
 Ring F] [inst_1 : Ring K] [inst_2 : _root_.Module F K]   [inst_3 : AddCommGroup
 A] [inst_4 …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance of_subfield [NumberField K] (E : Subfield K) : NumberField E where
  to_finiteDimensional := FiniteDimensional.left ℚ E K
/-
**NumberField.of_tower** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：of_tower [NumberField K] [NumberField L] [Algebra K L] (E : Type*) [Field 
E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] : NumberField E
参数：E : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.of_module_finite`：of_module_finite [NumberField K] [Algebra 
K L] [Module.Finite K L] : NumberField L where to_charZero
· 使用定理 `Module.Finite.left`：left [IsDomain K] [Nontrivial A] : Module.Finite F K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `NumberField.instFiniteDimensional`：∀ (K : Type u_1) (L : Type u_2) [inst
 : Field K] [inst_1 : Field L] [NumberField K] [NumberField L]   [inst_4 : Algeb
ra K L], FiniteDimensio…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem of_tower [NumberField K] [NumberField L] [Algebra K L] (E : Type*) [Field E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L] : NumberField E :=
  letI := Module.Finite.left K E L
  of_module_finite K E
/-
**NumberField.of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：of_ringEquiv (e : K ≃+* L) [NumberField K] : NumberField L
参数：e : K ≃+* L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharZero.of_addMonoidHom`：CharZero.of_addMonoidHom {M N : Type*} [AddCom
mMonoidWithOne M] [AddCommMonoidWithOne N] [CharZero M] (e : M ->+ N) (he : e 1 
= 1) (he' : Fu…
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `RingEquivClass.toLinearEquivClassRat`：∀ {F : Type u_1} {R : Type u_2} {S
 : Type u_3} [inst : DivisionRing R] [inst_1 : CharZero R] [inst_2 : DivisionRin
g S]   [inst_3 : CharZero …
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
-/
theorem of_ringEquiv (e : K ≃+* L) [NumberField K] : NumberField L :=
  letI := CharZero.of_addMonoidHom e.toAddMonoidHom (by simp) e.injective
  {
    to_charZero := inferInstance
    to_finiteDimensional := (SemilinearEquivClass.semilinearEquiv e : K ≃ₗ[ℚ] L).finiteDimensional
  }

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field.

This is defined as its own type, rather than a `Subalgebra`, for performance reasons:
looking for instances of the form `SMul (RingOfIntegers _) (RingOfIntegers _)` makes
much more effective use of the discrimination tree than instances of the form
`SMul (Subtype _) (Subtype _)`.
The drawback is we have to copy over instances manually.
-/
@[wikidata Q1358313]
/-
**NumberField.RingOfIntegers** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：RingOfIntegers : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field.

This is defined as its own type, rather than a `Subalgebra`, for performance rea
sons:
looking for instances of the form `SMul (RingOfIntegers _) (RingOfIntegers _)` m
akes
much more effective use of the discrimination tree than instances of the form
`SMul (Subtype _) (Subtype _)`.
The drawback is we have to copy over instances manually.
-/
def RingOfIntegers : Type _ :=
  integralClosure ℤ K
deriving CommRing, IsDomain, Nontrivial

@[inherit_doc] scoped notation "𝓞" => NumberField.RingOfIntegers

namespace RingOfIntegers

/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NumberField K] : CharZero (𝓞 K) :=
  inferInstanceAs (CharZero (integralClosure _ _))
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {L : Type*} [Ring L] [Algebra K L] : Algebra (𝓞 K) L :=
  inferInstanceAs (Algebra (integralClosure _ _) L)
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra (𝓞 K) K := inferInstanceAs _
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTorsionFree (𝓞 K) K :=
  inferInstanceAs (IsTorsionFree (integralClosure _ _) _)
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {L : Type*} [Ring L] [Algebra K L] : IsScalarTower (𝓞 K) K L :=
  inferInstanceAs (IsScalarTower (integralClosure _ _) K L)
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [Group G] [MulSemiringAction G K] : MulSemiringAction G (𝓞 K) :=
  inferInstanceAs (MulSemiringAction G (integralClosure ℤ K))
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [Group G] [MulSemiringAction G K] : SMulDistribClass G (𝓞 K) K :=
  inferInstanceAs (SMulDistribClass G (integralClosure ℤ K) K)

-- verify that the two algebra instances agree
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个示例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : instAlgebra (L := K) (K := K) = instAlgebra_1 (K := K) := by
  with_reducible_and_instances rfl

variable {K}

/-- The canonical coercion from `𝓞 K` to `K`. -/
@[coe]
/-
**NumberField.RingOfIntegers.val** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField.RingOf
Integers`。
形式化陈述：val (x : 𝓞 K) : K
参数：x : 𝓞 K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical coercion from `𝓞 K` to `K`.
-/
abbrev val (x : 𝓞 K) : K := algebraMap _ _ x

/-- This instance has to be `CoeHead` because we only want to apply it from `𝓞 K` to `K`. -/
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance has to be `CoeHead` because we only want to apply it from `𝓞 K` to
 `K`.
-/
instance : CoeHead (𝓞 K) K := ⟨val⟩
/-
**NumberField.RingOfIntegers.coe_eq_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `Number
Field.RingOfIntegers`。
形式化陈述：coe_eq_algebraMap (x : 𝓞 K) : (x : K) = algebraMap _ _ x
参数：x : 𝓞 K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_eq_algebraMap (x : 𝓞 K) : (x : K) = algebraMap _ _ x := rfl
/-
**NumberField.RingOfIntegers.ext** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.RingOfIn
tegers`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {x y : NumberField.RingOfIntegers K}, ↑x
 = ↑y → x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
@[ext] theorem ext {x y : 𝓞 K} (h : (x : K) = (y : K)) : x = y :=
  Subtype.ext h

@[norm_cast]
/-
**NumberField.RingOfIntegers.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.RingO
fIntegers`。
形式化陈述：eq_iff {x y : 𝓞 K} : (x : K) = (y : K) ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `NumberField.RingOfIntegers.ext_iff`：∀ {K : Type u_1} [inst : Field K] {x
 y : NumberField.RingOfIntegers K}, x = y ↔ ↑x = ↑y
-/
theorem eq_iff {x y : 𝓞 K} : (x : K) = (y : K) ↔ x = y :=
  NumberField.RingOfIntegers.ext_iff.symm
/-
**NumberField.RingOfIntegers.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.RingO
fIntegers`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (x : K) (hx : x ∈ integralClosure ℤ K), 
  (algebraMap (NumberField.RingOfIntegers K) K) ⟨x, hx⟩ = x
参数：x : K；hx : x ∈ integralClosure ℤ K；algebraMap (NumberField.RingOfIntegers K) 
K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_mk (x : K) (hx) : algebraMap (𝓞 K) K ⟨x, hx⟩ = x := rfl
/-
**NumberField.RingOfIntegers.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.RingO
fIntegers`。
形式化陈述：coe_mk {x : K} (hx) : ((⟨x, hx⟩ : 𝓞 K) : K) = x
参数：hx。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk {x : K} (hx) : ((⟨x, hx⟩ : 𝓞 K) : K) = x := rfl
/-
**NumberField.RingOfIntegers.mk_eq_mk** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.Rin
gOfIntegers`。
形式化陈述：mk_eq_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) = ⟨y, hy⟩ ↔ x = y
参数：x y : K；hx hy。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mk_eq_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) = ⟨y, hy⟩ ↔ x = y := by simp
/-
**NumberField.RingOfIntegers.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.RingO
fIntegers`。
形式化陈述：∀ {K : Type u_1} [inst : Field K], ⟨1, ⋯⟩ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
@[simp] lemma mk_one : (⟨1, one_mem _⟩ : 𝓞 K) = 1 :=
  rfl
/-
**NumberField.RingOfIntegers.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Ring
OfIntegers`。
形式化陈述：∀ {K : Type u_1} [inst : Field K], ⟨0, ⋯⟩ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
@[simp] lemma mk_zero : (⟨0, zero_mem _⟩ : 𝓞 K) = 0 :=
  rfl
-- TODO: these lemmas don't seem to fire?
/-
**NumberField.RingOfIntegers.mk_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Ri
ngOfIntegers`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (x y : K) (hx : x ∈ integralClosure ℤ K)
 (hy : y ∈ integralClosure ℤ K),   ⟨x, hx⟩ + ⟨y, hy⟩ = ⟨x + y, ⋯⟩
参数：x y : K；hx : x ∈ integralClosure ℤ K；hy : y ∈ integralClosure ℤ K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_add_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) + ⟨y, hy⟩ = ⟨x + y, add_mem hx hy⟩ :=
  rfl
/-
**NumberField.RingOfIntegers.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Ri
ngOfIntegers`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (x y : K) (hx : x ∈ integralClosure ℤ K)
 (hy : y ∈ integralClosure ℤ K),   ⟨x, hx⟩ * ⟨y, hy⟩ = ⟨x * y, ⋯⟩
参数：x y : K；hx : x ∈ integralClosure ℤ K；hy : y ∈ integralClosure ℤ K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_mul_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl
/-
**NumberField.RingOfIntegers.mk_sub_mk** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Ri
ngOfIntegers`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (x y : K) (hx : x ∈ integralClosure ℤ K)
 (hy : y ∈ integralClosure ℤ K),   ⟨x, hx⟩ - ⟨y, hy⟩ = ⟨x - y, ⋯⟩
参数：x y : K；hx : x ∈ integralClosure ℤ K；hy : y ∈ integralClosure ℤ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
@[simp] lemma mk_sub_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) - ⟨y, hy⟩ = ⟨x - y, sub_mem hx hy⟩ :=
  rfl
/-
**NumberField.RingOfIntegers.neg_mk** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.RingO
fIntegers`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (x : K) (hx : x ∈ integralClosure ℤ K), 
-⟨x, hx⟩ = ⟨-x, ⋯⟩
参数：x : K；hx : x ∈ integralClosure ℤ K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_mk (x : K) (hx) : (-⟨x, hx⟩ : 𝓞 K) = ⟨-x, neg_mem hx⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The ring homomorphism `(𝓞 K) →+* (𝓞 L)` given by restricting a ring homomorphism
  `f : K →+* L` to `𝓞 K`. -/
/-
**NumberField.RingOfIntegers.mapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.R
ingOfIntegers`。
形式化陈述：mapRingHom {K L : Type*} [Field K] [Field L] (f : K ->+* L) : (𝓞 K) ->+* (
𝓞 L) where toFun k
参数：f : K ->+* L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism `(𝓞 K) →+* (𝓞 L)` given by restricting a ring homomorphism
  `f : K →+* L` to `𝓞 K`.
-/
def mapRingHom {K L : Type*} [Field K] [Field L] (f : K →+* L) : (𝓞 K) →+* (𝓞 L) where
  toFun k := ⟨f k.val, map_isIntegral_int f k.2⟩
  map_zero' := by ext; simp only [map_mk, map_zero]
  map_one' := by ext; simp only [map_mk, map_one]
  map_add' x y := by ext; simp only [map_mk, map_add]
  map_mul' x y := by ext; simp only [map_mk, map_mul]

@[simp]
/-
**NumberField.RingOfIntegers.mapRingHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.RingOfIntegers`。
形式化陈述：mapRingHom_apply {K L : Type*} [Field K] [Field L] (f : K ->+* L) (x : 𝓞 K
) : (mapRingHom f x : L) = f (x : K)
参数：f : K ->+* L；x : 𝓞 K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapRingHom_apply {K L : Type*} [Field K] [Field L] (f : K →+* L) (x : 𝓞 K) :
    (mapRingHom f x : L) = f (x : K) := rfl

/-- The ring isomorphism `(𝓞 K) ≃+* (𝓞 L)` given by restricting
  a ring isomorphism `e : K ≃+* L` to `𝓞 K`. -/
/-
**NumberField.RingOfIntegers.mapRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NumberField
.RingOfIntegers`。
形式化陈述：mapRingEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) : (𝓞 K) ≃+* (
𝓞 L)
参数：e : K ≃+* L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring isomorphism `(𝓞 K) ≃+* (𝓞 L)` given by restricting
  a ring isomorphism `e : K ≃+* L` to `𝓞 K`.
-/
def mapRingEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) : (𝓞 K) ≃+* (𝓞 L) :=
  RingEquiv.ofRingHom (mapRingHom e) (mapRingHom e.symm)
    (RingHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (RingHom.ext fun x => ext (EquivLike.left_inv e x.1))

@[simp]
/-
**NumberField.RingOfIntegers.mapRingEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.RingOfIntegers`。
形式化陈述：mapRingEquiv_apply {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x : 𝓞 
K) : (mapRingEquiv e x : L) = e (x : K)
参数：e : K ≃+* L；x : 𝓞 K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapRingEquiv_apply {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x : 𝓞 K) :
    (mapRingEquiv e x : L) = e (x : K) := rfl

@[simp]
/-
**NumberField.RingOfIntegers.mapRingEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.RingOfIntegers`。
形式化陈述：mapRingEquiv_symm_apply {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x
 : 𝓞 L) : ((mapRingEquiv e).symm x : K) = e.symm (x : L)
参数：e : K ≃+* L；x : 𝓞 L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapRingEquiv_symm_apply {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x : 𝓞 L) :
    ((mapRingEquiv e).symm x : K) = e.symm (x : L) := rfl

end RingOfIntegers

/-- Given an algebra structure between two fields, this instance creates an algebra structure
between their two rings of integers. -/
/-
**NumberField.inst_ringOfIntegersAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`
。
形式化陈述：inst_ringOfIntegersAlgebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an algebra structure between two fields, this instance creates an algebra 
structure
between their two rings of integers.
-/
instance inst_ringOfIntegersAlgebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L) :=
  (RingOfIntegers.mapRingHom (algebraMap K L)).toAlgebra

-- diamond at `reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
/-
**NumberField.** 是 Mathlib 中的一个示例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Algebra.id (𝓞 K) = inst_ringOfIntegersAlgebra K K := rfl

namespace RingOfIntegers

/-- The algebra homomorphism `(𝓞 K) →ₐ[𝓞 k] (𝓞 L)` given by restricting an algebra homomorphism
  `f : K →ₐ[k] L` to `𝓞 K`. -/
/-
**NumberField.RingOfIntegers.mapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Ri
ngOfIntegers`。
形式化陈述：mapAlgHom {k K L F : Type*} [Field k] [Field K] [Field L] [Algebra k K] [A
lgebra k L] [FunLike F K L] [AlgHomClass F k K L] (f : F) : (𝓞 K) ->ₐ[𝓞 k] (𝓞 L)
 where toRingHom
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra homomorphism `(𝓞 K) →ₐ[𝓞 k] (𝓞 L)` given by restricting an algebra h
omomorphism
  `f : K →ₐ[k] L` to `𝓞 K`.
-/
def mapAlgHom {k K L F : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [FunLike F K L] [AlgHomClass F k K L] (f : F) : (𝓞 K) →ₐ[𝓞 k] (𝓞 L) where
  toRingHom := mapRingHom f
  commutes' x := SetCoe.ext (AlgHomClass.commutes
    ((AlgHomClass.toAlgHom f).restrictScalars (𝓞 k)) x)

/-- The isomorphism of algebras `(𝓞 K) ≃ₐ[𝓞 k] (𝓞 L)` given by restricting
  an isomorphism of algebras `e : K ≃ₐ[k] L` to `𝓞 K`. -/
/-
**NumberField.RingOfIntegers.mapAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.
RingOfIntegers`。
形式化陈述：mapAlgEquiv {k K L E : Type*} [Field k] [Field K] [Field L] [Algebra k K] 
[Algebra k L] [EquivLike E K L] [AlgEquivClass E k K L] (e : E) : (𝓞 K) ≃ₐ[𝓞 k] 
(𝓞 L)
参数：e : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of algebras `(𝓞 K) ≃ₐ[𝓞 k] (𝓞 L)` given by restricting
  an isomorphism of algebras `e : K ≃ₐ[k] L` to `𝓞 K`.
-/
def mapAlgEquiv {k K L E : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [EquivLike E K L] [AlgEquivClass E k K L] (e : E) : (𝓞 K) ≃ₐ[𝓞 k] (𝓞 L) :=
  AlgEquiv.ofAlgHom (mapAlgHom e) (mapAlgHom (AlgEquivClass.toAlgEquiv e : K ≃ₐ[k] L).symm)
    (AlgHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (AlgHom.ext fun x => ext (EquivLike.left_inv e x.1))
/-
**NumberField.RingOfIntegers.inst_isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Numbe
rField.RingOfIntegers`。
形式化陈述：inst_isScalarTower (k K L : Type*) [Field k] [Field K] [Field L] [Algebra 
k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] : IsScalarTower (𝓞 k) (𝓞 
K) (𝓞 L)
参数：k K L : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
-/
instance inst_isScalarTower (k K L : Type*) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] :
    IsScalarTower (𝓞 k) (𝓞 K) (𝓞 L) :=
  IsScalarTower.of_algHom (mapAlgHom (IsScalarTower.toAlgHom k K L))

variable {K}

/-- The canonical map from `𝓞 K` to `K` is injective.

This is a convenient abbreviation for `FaithfulSMul.algebraMap_injective`.
-/
/-
**NumberField.RingOfIntegers.coe_injective** 是 Mathlib 中的一个引理，位于命名空间 `NumberFiel
d.RingOfIntegers`。
形式化陈述：coe_injective : Function.Injective (algebraMap (𝓞 K) K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
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
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree`：∀ (K : Type u_1) [inst : F
ield K], Module.IsTorsionFree (NumberField.RingOfIntegers K) K

--- 原说明 ---
The canonical map from `𝓞 K` to `K` is injective.

This is a convenient abbreviation for `FaithfulSMul.algebraMap_injective`.
-/
lemma coe_injective : Function.Injective (algebraMap (𝓞 K) K) :=
  FaithfulSMul.algebraMap_injective _ _

/-- The canonical map from `𝓞 K` to `K` is injective.

This is a convenient abbreviation for `map_eq_zero_iff` applied to
`FaithfulSMul.algebraMap_injective`.
-/
/-
**NumberField.RingOfIntegers.coe_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberFi
eld.RingOfIntegers`。
形式化陈述：coe_eq_zero_iff {x : 𝓞 K} : algebraMap _ K x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `NumberField.RingOfIntegers.coe_injective`：coe_injective : Function.Injec
tive (algebraMap (𝓞 K) K)

--- 原说明 ---
The canonical map from `𝓞 K` to `K` is injective.

This is a convenient abbreviation for `map_eq_zero_iff` applied to
`FaithfulSMul.algebraMap_injective`.
-/
lemma coe_eq_zero_iff {x : 𝓞 K} : algebraMap _ K x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ coe_injective

/-- The canonical map from `𝓞 K` to `K` is injective.

This is a convenient abbreviation for `map_ne_zero_iff` applied to
`FaithfulSMul.algebraMap_injective`.
-/
/-
**NumberField.RingOfIntegers.coe_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberFi
eld.RingOfIntegers`。
形式化陈述：coe_ne_zero_iff {x : 𝓞 K} : algebraMap _ K x != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `NumberField.RingOfIntegers.coe_injective`：coe_injective : Function.Injec
tive (algebraMap (𝓞 K) K)

--- 原说明 ---
The canonical map from `𝓞 K` to `K` is injective.

This is a convenient abbreviation for `map_ne_zero_iff` applied to
`FaithfulSMul.algebraMap_injective`.
-/
lemma coe_ne_zero_iff {x : 𝓞 K} : algebraMap _ K x ≠ 0 ↔ x ≠ 0 :=
  map_ne_zero_iff _ coe_injective
/-
**NumberField.RingOfIntegers.minpoly_coe** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
RingOfIntegers`。
形式化陈述：minpoly_coe (x : 𝓞 K) : minpoly Int (x : K) = minpoly Int x
参数：x : 𝓞 K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.algebraMap_eq`：algebraMap_eq {B} [CommRing B] [Algebra A B] [Alg
ebra B B'] [IsScalarTower A B B'] (h : Function.Injective (algebraMap B B')) (x 
: B) : minp…
· 使用引理 `NumberField.RingOfIntegers.coe_injective`：coe_injective : Function.Injec
tive (algebraMap (𝓞 K) K)
-/
theorem minpoly_coe (x : 𝓞 K) :
    minpoly ℤ (x : K) = minpoly ℤ x :=
  minpoly.algebraMap_eq RingOfIntegers.coe_injective x
/-
**NumberField.RingOfIntegers.isIntegral_coe** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.RingOfIntegers`。
形式化陈述：isIntegral_coe (x : 𝓞 K) : IsIntegral Int (algebraMap _ K x)
参数：x : 𝓞 K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isIntegral_coe (x : 𝓞 K) : IsIntegral ℤ (algebraMap _ K x) :=
  x.2
/-
**NumberField.RingOfIntegers.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.R
ingOfIntegers`。
形式化陈述：isIntegral (x : 𝓞 K) : IsIntegral Int x
参数：x : 𝓞 K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.isIntegral_coe`：isIntegral_coe (x : 𝓞 K) : Is
Integral Int (algebraMap _ K x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.RingOfIntegers.coe_eq_zero_iff`：coe_eq_zero_iff {x : 𝓞 K} : 
algebraMap _ K x = 0 ↔ x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
-/
theorem isIntegral (x : 𝓞 K) : IsIntegral ℤ x := by
  obtain ⟨P, hPm, hP⟩ := x.isIntegral_coe
  refine ⟨P, hPm, ?_⟩
  rwa [IsScalarTower.algebraMap_eq (S := 𝓞 K), ← Polynomial.hom_eval₂, coe_eq_zero_iff] at hP
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NumberField K] : IsFractionRing (𝓞 K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ _
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIntegralClosure (𝓞 K) ℤ K :=
  integralClosure.isIntegralClosure _ _
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsIntegral ℤ (𝓞 K) :=
  IsIntegralClosure.isIntegral_algebra ℤ K
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NumberField K] : IsIntegrallyClosed (𝓞 K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension ℚ

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
/-
**NumberField.RingOfIntegers.equiv** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.RingOf
Integers`。
形式化陈述：{K : Type u_1} →   [inst : Field K] →     (R : Type u_3) →       [inst_1 :
 CommRing R] → [inst_2 : Algebra R K] → [IsIntegralClosure R ℤ K] → NumberField.
RingOfIntegers K ≃+* R
参数：R : Type u_3。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K

--- 原说明 ---
The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K`
-/
protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra R K]
    [IsIntegralClosure R ℤ K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv

variable (K)
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CharZero K] : CharZero (𝓞 K) := .of_module K

variable [NumberField K]
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNoetherian ℤ (𝓞 K) :=
  IsIntegralClosure.isNoetherian _ ℚ K _
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroup.FG (𝓞 K) :=
  Finite.iff_addGroup_fg.mp <| IsNoetherian.finite ℤ (𝓞 K)

/-- The ring of integers of a number field is not a field. -/
/-
**NumberField.RingOfIntegers.not_isField** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
RingOfIntegers`。
形式化陈述：not_isField : ¬IsField (𝓞 K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective_int`：RingHom.injective_int {α : Type*} [NonAssocRing α
] (f : Int ->+* α) [CharZero α] : Function.Injective f
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Int.not_isField`：¬IsField ℤ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.IsIntegral.isField_iff_isField`：Algebra.IsIntegral.isField_iff_i
sField [IsDomain S] (hRS : Function.Injective (algebraMap R S)) : IsField R ↔ Is
Field S
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)

--- 原说明 ---
The ring of integers of a number field is not a field.
-/
theorem not_isField : ¬IsField (𝓞 K) := by
  have h_inj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int (algebraMap ℤ (𝓞 K))
  intro hf
  exact Int.not_isField
    (((IsIntegralClosure.isIntegral_algebra ℤ K).isField_iff_isField h_inj).mpr hf)
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {I : Ideal (𝓞 K)} [hI : I.IsMaximal] : NeZero I :=
  ⟨Ring.ne_bot_of_isMaximal_of_not_isField hI <| RingOfIntegers.not_isField K⟩
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDedekindDomain (𝓞 K) :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ K _
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Free ℤ (𝓞 K) :=
  IsIntegralClosure.module_free ℤ ℚ K (𝓞 K)
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) K :=
  IsIntegralClosure.isLocalization_of_isSeparable ℤ ℚ K (𝓞 K)

/-- A ℤ-basis of the ring of integers of `K`. -/
/-
**NumberField.RingOfIntegers.basis** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.RingOf
Integers`。
形式化陈述：basis : Basis (Free.ChooseBasisIndex Int (𝓞 K)) Int (𝓞 K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
A ℤ-basis of the ring of integers of `K`.
-/
noncomputable def basis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ (𝓞 K) :=
  Free.chooseBasis ℤ (𝓞 K)

variable {K} {M : Type*}

/-- Given `f : M → K` such that `∀ x, IsIntegral ℤ (f x)`, the corresponding function
`M → 𝓞 K`. -/
/-
**NumberField.RingOfIntegers.restrict** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Rin
gOfIntegers`。
形式化陈述：restrict (f : M -> K) (h : forall x, IsIntegral Int (f x)) (x : M) : 𝓞 K
参数：f : M -> K；h : forall x, IsIntegral Int (f x)；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : M → K` such that `∀ x, IsIntegral ℤ (f x)`, the corresponding functio
n
`M → 𝓞 K`.
-/
def restrict (f : M → K) (h : ∀ x, IsIntegral ℤ (f x)) (x : M) : 𝓞 K :=
  ⟨f x, h x⟩

/-- Given `f : M →+ K` such that `∀ x, IsIntegral ℤ (f x)`, the corresponding function
`M →+ 𝓞 K`. -/
/-
**NumberField.RingOfIntegers.restrict_addMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Nu
mberField.RingOfIntegers`。
形式化陈述：restrict_addMonoidHom [AddZeroClass M] (f : M ->+ K) (h : forall x, IsInte
gral Int (f x)) : M ->+ 𝓞 K where toFun
参数：f : M ->+ K；h : forall x, IsIntegral Int (f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : M →+ K` such that `∀ x, IsIntegral ℤ (f x)`, the corresponding functi
on
`M →+ 𝓞 K`.
-/
def restrict_addMonoidHom [AddZeroClass M] (f : M →+ K) (h : ∀ x, IsIntegral ℤ (f x)) :
    M →+ 𝓞 K where
  toFun := restrict f h
  map_zero' := by simp only [restrict, map_zero]; rfl
  map_add' x y := by simp only [restrict, map_add]; rfl

/-- Given `f : M →* K` such that `∀ x, IsIntegral ℤ (f x)`, the corresponding function
`M →* 𝓞 K`. -/
/-
**NumberField.RingOfIntegers.restrict_monoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Numbe
rField.RingOfIntegers`。
形式化陈述：restrict_monoidHom [MulOneClass M] (f : M ->* K) (h : forall x, IsIntegral
 Int (f x)) : M ->* 𝓞 K where toFun
参数：f : M ->* K；h : forall x, IsIntegral Int (f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : M →* K` such that `∀ x, IsIntegral ℤ (f x)`, the corresponding functi
on
`M →* 𝓞 K`.
-/
def restrict_monoidHom [MulOneClass M] (f : M →* K) (h : ∀ x, IsIntegral ℤ (f x)) : M →* 𝓞 K where
  toFun := restrict f h
  map_one' := by simp only [restrict, map_one]; rfl
  map_mul' x y := by simp only [restrict, map_mul]; rfl

section extension

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower (𝓞 K) (𝓞 L) L :=
  IsScalarTower.of_algebraMap_eq' rfl
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIntegralClosure (𝓞 L) (𝓞 K) L :=
  IsIntegralClosure.tower_top (R := ℤ)

/-- The ring of integers of `L` is isomorphic to any integral closure of `𝓞 K` in `L` -/
/-
**NumberField.RingOfIntegers.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Rin
gOfIntegers`。
形式化陈述：(K : Type u_4) →   (L : Type u_5) →     [inst : Field K] →       [inst_1 :
 Field L] →         [inst_2 : Algebra K L] →           (R : Type u_6) →         
    [inst_3 : CommRing R] →               [inst_4 : Algebra (NumberField.RingOfI
ntegers K) R] →                 [inst_5 : Algebra R L] →                   [IsSc
alarTower (NumberField.RingOfIntegers K) R L] →                     [IsIntegralC
losure R (NumberField.RingOfIntegers K) L] →                       NumberField.R
ingOfIntegers L ≃ₐ[NumberField.RingOfIntegers K] R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosure`：∀ (K : Type u_4) (L : 
Type u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   IsIntegr
alClosure (NumberField.RingOfIntegers …
· 使用定理 `NumberField.RingOfIntegers.instIsScalarTower_1`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   IsScalarTo
wer (NumberField.RingOfIntegers K) (…

--- 原说明 ---
The ring of integers of `L` is isomorphic to any integral closure of `𝓞 K` in `L
`
-/
protected noncomputable def algEquiv (R : Type*) [CommRing R] [Algebra (𝓞 K) R] [Algebra R L]
    [IsScalarTower (𝓞 K) R L] [IsIntegralClosure R (𝓞 K) L] : 𝓞 L ≃ₐ[𝓞 K] R :=
  (IsIntegralClosure.equiv (𝓞 K) R L _).symm

/-- Any extension between ring of integers is integral. -/
/-
**NumberField.RingOfIntegers.extension_algebra_isIntegral** 是 Mathlib 中的一个实例，位于命
名空间 `NumberField.RingOfIntegers`。
形式化陈述：extension_algebra_isIntegral : Algebra.IsIntegral (𝓞 K) (𝓞 L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosure`：∀ (K : Type u_4) (L : 
Type u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   IsIntegr
alClosure (NumberField.RingOfIntegers …
· 使用定理 `NumberField.RingOfIntegers.instIsScalarTower_1`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   IsScalarTo
wer (NumberField.RingOfIntegers K) (…

--- 原说明 ---
Any extension between ring of integers is integral.
-/
instance extension_algebra_isIntegral : Algebra.IsIntegral (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isIntegral_algebra (𝓞 K) L

/-- Any extension between ring of integers of number fields is Noetherian. -/
/-
**NumberField.RingOfIntegers.extension_isNoetherian** 是 Mathlib 中的一个实例，位于命名空间 `N
umberField.RingOfIntegers`。
形式化陈述：extension_isNoetherian [NumberField K] [NumberField L] : IsNoetherian (𝓞 K
) (𝓞 L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isNoetherian`：IsIntegralClosure.isNoetherian [IsIntegr
allyClosed A] [IsNoetherianRing A] : IsNoetherian A C
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instIsScalarTower`：∀ (K : Type u_1) [inst : F
ield K] {L : Type u_3} [inst_1 : Ring L] [inst_2 : Algebra K L],   IsScalarTower
 (NumberField.RingOfIntegers K) K …
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosure`：∀ (K : Type u_4) (L : 
Type u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   IsIntegr
alClosure (NumberField.RingOfIntegers …
· 使用定理 `NumberField.RingOfIntegers.instIsScalarTower_1`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   IsScalarTo
wer (NumberField.RingOfIntegers K) (…
· 使用定理 `NumberField.instFiniteDimensional`：∀ (K : Type u_1) (L : Type u_2) [inst
 : Field K] [inst_1 : Field L] [NumberField K] [NumberField L]   [inst_4 : Algeb
ra K L], FiniteDimensio…
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instIsIntegrallyClosed`：∀ {K : Type u_1} [ins
t : Field K] [NumberField K], IsIntegrallyClosed (NumberField.RingOfIntegers K)
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)

--- 原说明 ---
Any extension between ring of integers of number fields is Noetherian.
-/
instance extension_isNoetherian [NumberField K] [NumberField L] : IsNoetherian (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)

/-- The kernel of the algebraMap between ring of integers is `⊥`. -/
/-
**NumberField.RingOfIntegers.ker_algebraMap_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.RingOfIntegers`。
形式化陈述：ker_algebraMap_eq_bot : RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.ker_eq_bot_iff_eq_zero`：ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ for
all x, f x = 0 -> x = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
The kernel of the algebraMap between ring of integers is `⊥`.
-/
theorem ker_algebraMap_eq_bot : RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥ :=
  (RingHom.ker_eq_bot_iff_eq_zero (algebraMap (𝓞 K) (𝓞 L))).mpr <| fun x hx => by
  have h : (algebraMap K L) x = (algebraMap (𝓞 K) (𝓞 L)) x := rfl
  simp only [hx, map_zero, map_eq_zero, RingOfIntegers.coe_eq_zero_iff] at h
  exact h

/-- The algebraMap between ring of integers is injective. -/
/-
**NumberField.RingOfIntegers.algebraMap.injective** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.RingOfIntegers.algebraMap`。
形式化陈述：∀ (K : Type u_4) (L : Type u_5) [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L],   Function.Injective ⇑(algebraMap (NumberField.RingOfIntegers 
K) (NumberField.RingOfIntegers L))
参数：K : Type u_4；L : Type u_5；algebraMap (NumberField.RingOfIntegers K) (NumberFi
eld.RingOfIntegers L)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `NumberField.RingOfIntegers.ker_algebraMap_eq_bot`：ker_algebraMap_eq_bot 
: RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥

--- 原说明 ---
The algebraMap between ring of integers is injective.
-/
theorem algebraMap.injective : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
  (RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 K) (𝓞 L))).mpr (ker_algebraMap_eq_bot K L)
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTorsionFree (𝓞 K) (𝓞 L) :=
  isTorsionFree_iff_algebraMap_injective.mpr <| algebraMap.injective K L
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTorsionFree (𝓞 K) L := .trans_faithfulSMul (𝓞 K) (𝓞 L) L

end extension

end RingOfIntegers

variable [NumberField K]

/-- A basis of `K` over `ℚ` that is also a basis of `𝓞 K` over `ℤ`. -/
/-
**NumberField.integralBasis** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：integralBasis : Basis (Free.ChooseBasisIndex Int (𝓞 K)) Rat K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
A basis of `K` over `ℚ` that is also a basis of `𝓞 K` over `ℤ`.
-/
noncomputable def integralBasis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ K :=
  Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) K (RingOfIntegers.basis K)

@[simp]
/-
**NumberField.integralBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：integralBasis_apply (i : Free.ChooseBasisIndex Int (𝓞 K)) : integralBasis 
K i = algebraMap (𝓞 K) K (RingOfIntegers.basis K i)
参数：i : Free.ChooseBasisIndex Int (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Module.Basis.localizationLocalization_apply`：localizationLocalization_ap
ply {ι : Type*} (b : Basis ι R A) (i) : b.localizationLocalization Rₛ S Aₛ i = a
lgebraMap A Aₛ (b i)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
-/
theorem integralBasis_apply (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    integralBasis K i = algebraMap (𝓞 K) K (RingOfIntegers.basis K i) :=
  Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) K (RingOfIntegers.basis K) i

@[simp]
/-
**NumberField.integralBasis_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：integralBasis_repr_apply (x : (𝓞 K)) (i : Free.ChooseBasisIndex Int (𝓞 K))
 : (integralBasis K).repr (algebraMap _ _ x) i = (algebraMap Int Rat) ((RingOfIn
tegers.basis K).repr x i)
参数：x : (𝓞 K)；i : Free.ChooseBasisIndex Int (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Module.Basis.localizationLocalization_repr_algebraMap`：localizationLocal
ization_repr_algebraMap {ι : Type*} (b : Basis ι R A) (x i) : (b.localizationLoc
alization Rₛ S Aₛ).repr (algebraMap A Aₛ x)…
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
-/
theorem integralBasis_repr_apply (x : (𝓞 K)) (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (integralBasis K).repr (algebraMap _ _ x) i =
      (algebraMap ℤ ℚ) ((RingOfIntegers.basis K).repr x i) :=
  Basis.localizationLocalization_repr_algebraMap ℚ (nonZeroDivisors ℤ) K _ x i
/-
**NumberField.mem_span_integralBasis** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：mem_span_integralBasis {x : K} : x in Submodule.span Int (Set.range (integ
ralBasis K)) ↔ x in (algebraMap (𝓞 K) K).range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.localizationLocalization_span`：localizationLocalization_spa
n {ι : Type*} (b : Basis ι R A) : Submodule.span R (Set.range (b.localizationLoc
alization Rₛ S Aₛ)) = LinearMap.…
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_span_integralBasis {x : K} :
    x ∈ Submodule.span ℤ (Set.range (integralBasis K)) ↔ x ∈ (algebraMap (𝓞 K) K).range := by
  simp [integralBasis, Basis.localizationLocalization_span]
/-
**NumberField.RingOfIntegers.rank** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.RingOfI
ntegers`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],   Module.finra
nk ℤ (NumberField.RingOfIntegers K) = Module.finrank ℚ K
参数：K : Type u_1；NumberField.RingOfIntegers K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.rank`：IsIntegralClosure.rank [IsPrincipalIdealRing A] 
[IsTorsionFree A L] : Module.finrank A C = Module.finrank K L
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem RingOfIntegers.rank : Module.finrank ℤ (𝓞 K) = Module.finrank ℚ K :=
  IsIntegralClosure.rank ℤ ℚ K (𝓞 K)

end NumberField

namespace Rat

open NumberField

/-
**Rat.numberField** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：NumberField ℚ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance numberField : NumberField ℚ where

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
/-
**Rat.ringOfIntegersEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rat`。
形式化陈述：ringOfIntegersEquiv : 𝓞 Rat ≃+* Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring of integers of `ℚ` as a number field is just `ℤ`.
-/
noncomputable def ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ :=
  RingOfIntegers.equiv ℤ

@[simp]
/-
**Rat.ringOfIntegersEquiv_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：ringOfIntegersEquiv_apply_coe (z : 𝓞 Rat) : (Rat.ringOfIntegersEquiv z : R
at) = algebraMap (𝓞 Rat) Rat z
参数：z : 𝓞 Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ringOfIntegersEquiv_apply_coe (z : 𝓞 ℚ) :
    (Rat.ringOfIntegersEquiv z : ℚ) = algebraMap (𝓞 ℚ) ℚ z := by
  obtain ⟨z, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective z
  simp
/-
**Rat.ringOfIntegersEquiv_symm_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：ringOfIntegersEquiv_symm_apply_coe (x : Int) : (ringOfIntegersEquiv.symm x
 : Rat) = ↑x
参数：x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem ringOfIntegersEquiv_symm_apply_coe (x : ℤ) :
    (ringOfIntegersEquiv.symm x : ℚ) = ↑x :=
  eq_intCast ringOfIntegersEquiv.symm _ ▸ rfl

end Rat

namespace AdjoinRoot

/-- The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ[X]`
is a number field. -/
/-
**AdjoinRoot.** 是 Mathlib 中的一个实例，位于命名空间 `AdjoinRoot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ
[X]`
is a number field.
-/
instance {f : Polynomial ℚ} [hf : Fact (Irreducible f)] : NumberField (AdjoinRoot f) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := by convert! (AdjoinRoot.powerBasis hf.out.ne_zero).finite

end AdjoinRoot

