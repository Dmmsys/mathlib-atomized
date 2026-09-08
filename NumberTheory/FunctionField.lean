/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.Adjoin.Polynomial.Bivariate
public import Mathlib.FieldTheory.RatFunc.Valuation -- for deprecation to `RatFunc.inftyValuation` and `RatFunc.CompletionAtInfty`

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions

- `FunctionField F K` states that `K` is a function field over the field `F`,
  i.e. it is a finite extension of the field of rational functions in one variable over `F`.
- `FunctionField.ringOfIntegers` defines the ring of integers corresponding to a function field
  as the integral closure of `F[X]` in the function field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like
`IsScalarTower F[X] (FractionRing F[X]) K` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]
* [M. Rosen, *Number Theory in Function Fields*][rosen2002]

## Tags
function field, ring of integers
-/

@[expose] public section


noncomputable section

open scoped nonZeroDivisors Polynomial WithZero RatFunc

variable (F K : Type*) [Field F] [Field K]

/-- `K` is a function field over the field `F` if it is a finite
extension of the field of rational functions in one variable over `F`.

Note that `K` can be a function field over multiple, non-isomorphic, `F`.
-/
/-
**FunctionField** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FunctionField [Algebra F⟮X⟯ K] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`K` is a function field over the field `F` if it is a finite
extension of the field of rational functions in one variable over `F`.

Note that `K` can be a function field over multiple, non-isomorphic, `F`.
-/
abbrev FunctionField [Algebra F⟮X⟯ K] : Prop :=
  FiniteDimensional F⟮X⟯ K

/-- `K` is a function field over `F` iff it is a finite extension of `F(t)`. -/
/-
**functionField_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：functionField_iff (Ft : Type*) [Field Ft] [Algebra F[X] Ft] [IsFractionRin
g F[X] Ft] [Algebra F⟮X⟯ K] [Algebra Ft K] [Algebra F[X] K] [IsScalarTower F[X] 
Ft K] [IsScalarTower F[X] F⟮X⟯ K] : FunctionField F K ↔ FiniteDimensional Ft K
参数：Ft : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `IsLocalization.ext`：∀ {R : Type u_1} [inst : CommSemiring R] (M : Submon
oid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [IsLoca
lization…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
`K` is a function field over `F` iff it is a finite extension of `F(t)`.
-/
theorem functionField_iff (Ft : Type*) [Field Ft] [Algebra F[X] Ft]
    [IsFractionRing F[X] Ft] [Algebra F⟮X⟯ K] [Algebra Ft K] [Algebra F[X] K]
    [IsScalarTower F[X] Ft K] [IsScalarTower F[X] F⟮X⟯ K] :
    FunctionField F K ↔ FiniteDimensional Ft K := by
  let e := IsLocalization.algEquiv F[X]⁰ F⟮X⟯ Ft
  have : ∀ (c) (x : K), e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def]
    congr
    refine congr_fun (f := fun c => algebraMap Ft K (e c)) ?_ c
    refine IsLocalization.ext (nonZeroDivisors F[X]) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp only [map_one, map_mul, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  constructor <;> intro h
  · let b := Module.finBasis F⟮X⟯ K
    exact (b.mapCoeffs e this).finiteDimensional_of_finite
  · let b := Module.finBasis Ft K
    refine (b.mapCoeffs e.symm ?_).finiteDimensional_of_finite
    intro c x; convert! (this (e.symm c) x).symm; simp only [e.apply_symm_apply]

namespace FunctionField

/-
**FunctionField.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `FunctionField`。
形式化陈述：algebraMap_injective [Algebra F[X] K] [Algebra F⟮X⟯ K] [IsScalarTower F[X]
 F⟮X⟯ K] : Function.Injective (algebraMap F[X] K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
-/
theorem algebraMap_injective [Algebra F[X] K] [Algebra F⟮X⟯ K]
    [IsScalarTower F[X] F⟮X⟯ K] : Function.Injective (algebraMap F[X] K) := by
  rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
  exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)

/-- The function field analogue of `NumberField.ringOfIntegers`:
`FunctionField.ringOfIntegers F K` is the integral closure of `F[X]` in `K`.

We don't actually assume `K` is a function field over `F` in the definition,
only when proving its properties.
-/
/-
**FunctionField.ringOfIntegers** 是 Mathlib 中的一个定义，位于命名空间 `FunctionField`。
形式化陈述：ringOfIntegers [Algebra F[X] K]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function field analogue of `NumberField.ringOfIntegers`:
`FunctionField.ringOfIntegers F K` is the integral closure of `F[X]` in `K`.

We don't actually assume `K` is a function field over `F` in the definition,
only when proving its properties.
-/
def ringOfIntegers [Algebra F[X] K] :=
  integralClosure F[X] K

namespace ringOfIntegers

variable [Algebra F[X] K]

/-
**FunctionField.ringOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField.ringOfI
ntegers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDomain (ringOfIntegers F K) :=
  (ringOfIntegers F K).isDomain
/-
**FunctionField.ringOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField.ringOfI
ntegers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIntegralClosure (ringOfIntegers F K) F[X] K :=
  integralClosure.isIntegralClosure _ _

variable [Algebra F⟮X⟯ K] [IsScalarTower F[X] F⟮X⟯ K]
/-
**FunctionField.ringOfIntegers.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `F
unctionField.ringOfIntegers`。
形式化陈述：algebraMap_injective : Function.Injective (algebraMap F[X] (ringOfIntegers
 F K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subalgebra.coe_zero`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   ↑0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
-/
theorem algebraMap_injective : Function.Injective (algebraMap F[X] (ringOfIntegers F K)) := by
  have hinj : Function.Injective (algebraMap F[X] K) := by
    rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
    exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)
  rw [injective_iff_map_eq_zero (algebraMap F[X] (↥(ringOfIntegers F K)))]
  intro p hp
  rw [← Subtype.coe_inj, Subalgebra.coe_zero] at hp
  rw [injective_iff_map_eq_zero (algebraMap F[X] K)] at hinj
  exact hinj p hp
/-
**FunctionField.ringOfIntegers.not_isField** 是 Mathlib 中的一个定理，位于命名空间 `FunctionFi
eld.ringOfIntegers`。
形式化陈述：not_isField : ¬IsField (ringOfIntegers F K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.IsIntegral.isField_iff_isField`：Algebra.IsIntegral.isField_iff_i
sField [IsDomain S] (hRS : Function.Injective (algebraMap R S)) : IsField R ↔ Is
Field S
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
· 使用定理 `FunctionField.ringOfIntegers.instIsIntegralClosureSubtypeMemSubalgebraPo
lynomial`：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [inst_1 : Field K] [i
nst_2 : Algebra (Polynomial F) K],   IsIntegralClosure (↥(FunctionFiel…
· 使用定理 `FunctionField.ringOfIntegers.instIsDomainSubtypeMemSubalgebraPolynomial`
：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [inst_1 : Field K] [inst_2 : A
lgebra (Polynomial F) K],   IsDomain ↥(FunctionField.ringOfIn…
· 使用定理 `FunctionField.ringOfIntegers.algebraMap_injective`：algebraMap_injective 
: Function.Injective (algebraMap F[X] (ringOfIntegers F K))
· 使用定理 `Polynomial.not_isField`：∀ (R : Type u) [inst : Ring R], ¬IsField (Polyno
mial R)
-/
theorem not_isField : ¬IsField (ringOfIntegers F K) := by
  simpa [← (IsIntegralClosure.isIntegral_algebra F[X] K).isField_iff_isField
      (algebraMap_injective F K)] using
    Polynomial.not_isField F

variable [FunctionField F K]
/-
**FunctionField.ringOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField.ringOfI
ntegers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFractionRing (ringOfIntegers F K) K :=
  integralClosure.isFractionRing_of_finite_extension F⟮X⟯ K
/-
**FunctionField.ringOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField.ringOfI
ntegers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIntegrallyClosed (ringOfIntegers F K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension F⟮X⟯
/-
**FunctionField.ringOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField.ringOfI
ntegers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsSeparable F⟮X⟯ K] : IsNoetherian F[X] (ringOfIntegers F K) :=
  IsIntegralClosure.isNoetherian _ F⟮X⟯ K _
/-
**FunctionField.ringOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField.ringOfI
ntegers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsSeparable F⟮X⟯ K] : IsDedekindDomain (ringOfIntegers F K) :=
  IsIntegralClosure.isDedekindDomain F[X] F⟮X⟯ K _

end ringOfIntegers

section deprecated

@[deprecated RatFunc.inftyValuationDef (since := "2026-04-14")]
alias inftyValuationDef := RatFunc.inftyValuationDef

@[deprecated RatFunc.InftyValuation.map_zero' (since := "2026-04-14")]
alias InftyValuation.map_zero' := RatFunc.InftyValuation.map_zero'

@[deprecated RatFunc.InftyValuation.map_one' (since := "2026-04-14")]
alias InftyValuation.map_one' := RatFunc.InftyValuation.map_one'

@[deprecated RatFunc.InftyValuation.map_mul' (since := "2026-04-14")]
alias InftyValuation.map_mul' := RatFunc.InftyValuation.map_mul'

@[deprecated RatFunc.InftyValuation.map_add_le_max' (since := "2026-04-14")]
alias InftyValuation.map_add_le_max' := RatFunc.InftyValuation.map_add_le_max'

@[deprecated RatFunc.inftyValuation_of_nonzero (since := "2026-04-14")]
alias inftyValuation_of_nonzero := RatFunc.inftyValuation_of_nonzero

@[deprecated RatFunc.inftyValuation (since := "2026-04-14")]
alias inftyValuation := RatFunc.inftyValuation

@[deprecated RatFunc.inftyValuation_apply (since := "2026-04-14")]
alias inftyValuation_apply := RatFunc.inftyValuation_apply

@[deprecated RatFunc.inftyValuation.C (since := "2026-04-14")]
alias inftyValuation.C := RatFunc.inftyValuation.C

@[deprecated RatFunc.inftyValuation.X (since := "2026-04-14")]
alias inftyValuation.X := RatFunc.inftyValuation.X

@[deprecated RatFunc.inftyValuation.X_zpow (since := "2026-04-14")]
alias inftyValuation.X_zpow := RatFunc.inftyValuation.X_zpow

@[deprecated RatFunc.inftyValuation.X_inv (since := "2026-04-14")]
alias inftyValuation.X_inv := RatFunc.inftyValuation.X_inv

@[deprecated RatFunc.inftyValuation.polynomial (since := "2026-04-14")]
alias inftyValuation.polynomial := RatFunc.inftyValuation.polynomial

@[deprecated RatFunc.inftyValued (since := "2026-04-14")]
alias inftyValuedFqt := RatFunc.inftyValued

@[deprecated RatFunc.inftyValued.def (since := "2026-04-14")]
alias inftyValuedFqt.def := RatFunc.inftyValued.def

@[deprecated RatFunc.CompletionAtInfty (since := "2026-04-14")]
alias FqtInfty := RatFunc.CompletionAtInfty

@[deprecated "Use the anonymous `Valued` instance on `RatFunc.CompletionAtInfty`"
(since := "2026-04-14")]
/-
**FunctionField.valuedFqtInfty** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField`。
形式化陈述：valuedFqtInfty [DecidableEq F⟮X⟯] : Valued (RatFunc.CompletionAtInfty F) I
ntᵐ⁰
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance valuedFqtInfty [DecidableEq F⟮X⟯] :
    Valued (RatFunc.CompletionAtInfty F) ℤᵐ⁰ :=
  inferInstance

@[deprecated RatFunc.valuedCompletionAtInfty.def (since := "2026-04-14")]
alias valuedFqtInfty.def := RatFunc.valuedCompletionAtInfty.def

end deprecated

section AdjoinTranscendental

open IntermediateField RatFunc

variable {F K : Type*} [Field F] [Field K] [Algebra F⟮X⟯ K] [FunctionField F K]

/-
**FunctionField.FiniteDimensional.adjoin_X** 是 Mathlib 中的一个定理，位于命名空间 `FunctionFi
eld.FiniteDimensional`。
形式化陈述：∀ {F : Type u_3} {K : Type u_4} [inst : Field F] [inst_1 : Field K] [inst_
2 : Algebra (RatFunc F) K]   [FunctionField F K], FiniteDimensional (↥F⟮RatFunc.
X⟯) K
参数：RatFunc F；↥F⟮RatFunc.X⟯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.adjoin_X`：adjoin_X : K⟮(X : K⟮X⟯)⟯ = ⊤
-/
instance FiniteDimensional.adjoin_X : FiniteDimensional F⟮(X : F⟮X⟯)⟯ K :=
  have : Module.Finite (⊤ : IntermediateField F F⟮X⟯) F⟮X⟯ :=
    .top_left F⟮X⟯ F⟮X⟯
  RatFunc.adjoin_X (K := F) ▸ Module.Finite.trans F⟮X⟯ _

variable [Algebra F K] [IsScalarTower F F⟮X⟯ K]
/-
**FunctionField.FiniteDimensional.adjoin_algebraMap_X** 是 Mathlib 中的一个定理，位于命名空间 
`FunctionField.FiniteDimensional`。
形式化陈述：∀ {F : Type u_3} {K : Type u_4} [inst : Field F] [inst_1 : Field K] [inst_
2 : Algebra (RatFunc F) K] [FunctionField F K]   [inst_4 : Algebra F K] [IsScala
rTower F (RatFunc F) K], FiniteDimensional (↥F⟮(algebraMap (RatFunc F) K) RatFun
c.X⟯) K
参数：RatFunc F；RatFunc F；↥F⟮(algebraMap (RatFunc F) K) RatFunc.X⟯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.instIsScalarTowerSubtypeMemAdjoinSingletonSetCoeRingHo
mAlgebraMap`：∀ {A : Type u_3} {B : Type u_4} {C : Type u_5} [inst : Field A] [in
st_1 : Field B] [inst_2 : Field C]   [inst_3 : Algebra A B] [inst_4 : Alg…
· 使用定理 `FunctionField.FiniteDimensional.adjoin_X`：∀ {F : Type u_3} {K : Type u_4
} [inst : Field F] [inst_1 : Field K] [inst_2 : Algebra (RatFunc F) K]   [Functi
onField F K], FiniteDimensiona…
-/
theorem FiniteDimensional.adjoin_algebraMap_X :
    FiniteDimensional F⟮algebraMap _ K (X : F⟮X⟯)⟯ K :=
  .of_restrictScalars_finite F⟮(X : F⟮X⟯)⟯ _ _
/-
**FunctionField.Algebra.IsAlgebraic.adjoin_algebraMap_X** 是 Mathlib 中的一个定理，位于命名空
间 `FunctionField.Algebra.IsAlgebraic`。
形式化陈述：∀ {F : Type u_3} {K : Type u_4} [inst : Field F] [inst_1 : Field K] [inst_
2 : Algebra (RatFunc F) K] [FunctionField F K]   [inst_4 : Algebra F K] [IsScala
rTower F (RatFunc F) K],   Algebra.IsAlgebraic (↥F⟮(algebraMap (RatFunc F) K) Ra
tFunc.X⟯) K
参数：RatFunc F；RatFunc F；↥F⟮(algebraMap (RatFunc F) K) RatFunc.X⟯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.IsAlgebraic.tower_top`：Algebra.IsAlgebraic.tower_top [Algebra.Is
Algebraic K A] : Algebra.IsAlgebraic L A
· 使用定理 `IntermediateField.instIsScalarTowerSubtypeMemAdjoinSingletonSetCoeRingHo
mAlgebraMap`：∀ {A : Type u_3} {B : Type u_4} {C : Type u_5} [inst : Field A] [in
st_1 : Field B] [inst_2 : Field C]   [inst_3 : Algebra A B] [inst_4 : Alg…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FunctionField.FiniteDimensional.adjoin_X`：∀ {F : Type u_3} {K : Type u_4
} [inst : Field F] [inst_1 : Field K] [inst_2 : Algebra (RatFunc F) K]   [Functi
onField F K], FiniteDimensiona…
-/
theorem Algebra.IsAlgebraic.adjoin_algebraMap_X :
    Algebra.IsAlgebraic F⟮algebraMap _ K (X : F⟮X⟯)⟯ K := by
  exact .tower_top (K := F⟮(X : F⟮X⟯)⟯) _

variable {y : K}
/-
**FunctionField.isAlgebraic_X_over_adjoin_transcendental** 是 Mathlib 中的一个定理，位于命名
空间 `FunctionField`。
形式化陈述：isAlgebraic_X_over_adjoin_transcendental (hy : Transcendental F y) : IsAlg
ebraic F⟮y⟯ (algebraMap _ K (X : F⟮X⟯))
参数：hy : Transcendental F y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.isAlgebraic_adjoin_iff`：isAlgebraic_adjoin_iff {x : S}
 : IsAlgebraic (adjoin F s) x ↔ IsAlgebraic (Algebra.adjoin F s) x
· 使用定理 `IsAlgebraic.adjoin_singleton`：∀ {R : Type u_1} {A : Type u_2} [inst : Co
mmRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {B : Type u_3}   [inst_3 
: CommRing B] [ins…
· 使用引理 `RatFunc.transcendental_X`：transcendental_X : Transcendental K (X : K⟮X⟯)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FunctionField.FiniteDimensional.adjoin_X`：∀ {F : Type u_3} {K : Type u_4
} [inst : Field F] [inst_1 : Field K] [inst_2 : Algebra (RatFunc F) K]   [Functi
onField F K], FiniteDimensiona…
-/
theorem isAlgebraic_X_over_adjoin_transcendental (hy : Transcendental F y) :
    IsAlgebraic F⟮y⟯ (algebraMap _ K (X : F⟮X⟯)) :=
  isAlgebraic_adjoin_iff.mpr (.adjoin_singleton transcendental_X hy
    (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic y)))
/-
**FunctionField.finiteDimensional_of_adjoin_transcendental** 是 Mathlib 中的一个引理，位于
命名空间 `FunctionField`。
形式化陈述：finiteDimensional_of_adjoin_transcendental (hy : Transcendental F y) : Fin
iteDimensional F⟮y⟯ K
参数：hy : Transcendental F y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x
· 使用定理 `FunctionField.isAlgebraic_X_over_adjoin_transcendental`：isAlgebraic_X_ov
er_adjoin_transcendental (hy : Transcendental F y) : IsAlgebraic F⟮y⟯ (algebraMa
p _ K (X : F⟮X⟯))
· 使用定理 `FunctionField.FiniteDimensional.adjoin_algebraMap_X`：∀ {F : Type u_3} {K
 : Type u_4} [inst : Field F] [inst_1 : Field K] [inst_2 : Algebra (RatFunc F) K
] [FunctionField F K]   [inst_4 : Algebra…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin_simple_comm`：adjoin_simple_comm (β : E) : F⟮α⟯⟮
β⟯.restrictScalars F = F⟮β⟯⟮α⟯.restrictScalars F
· 使用定理 `FiniteDimensional.right`：∀ (F : Type u) (K : Type v) (A : Type w) [inst 
: Semiring F] [inst_1 : Semiring K] [inst_2 : _root_.Module F K]   [inst_3 : Add
CommMonoid A]…
· 使用定理 `FiniteDimensional.trans`：trans [FiniteDimensional F K] [FiniteDimensiona
l K A] : FiniteDimensional F A
-/
lemma finiteDimensional_of_adjoin_transcendental (hy : Transcendental F y) :
    FiniteDimensional F⟮y⟯ K :=
  -- Local definitions for convenience
  let x := algebraMap _ K (X : F⟮X⟯)
  let Fyx := restrictScalars F F⟮y⟯⟮x⟯
  let Fxy := restrictScalars F F⟮x⟯⟮y⟯
  -- Recalling instance to speed up search
  let : Algebra F⟮y⟯ Fyx := F⟮y⟯⟮x⟯.algebra
  let : Module F⟮y⟯ Fyx := Algebra.toModule
  let : SMul F⟮y⟯ Fyx := Algebra.toSMul
  let : Algebra F⟮x⟯ Fxy := F⟮x⟯⟮y⟯.algebra
  let : Module F⟮x⟯ Fxy := Algebra.toModule
  let : SMul F⟮x⟯ Fxy := Algebra.toSMul
  have : FiniteDimensional F⟮y⟯ Fyx :=
    adjoin.finiteDimensional
      (isAlgebraic_iff_isIntegral.mp (isAlgebraic_X_over_adjoin_transcendental hy))
  have : FiniteDimensional Fyx K := by
    have := FiniteDimensional.adjoin_algebraMap_X (F := F) (K := K)
    unfold Fyx
    rw [adjoin_simple_comm]
    have : IsScalarTower F⟮x⟯ Fxy K := isScalarTower_mid' F⟮x⟯⟮y⟯
    exact .right F⟮x⟯ Fxy K
  have : IsScalarTower F⟮y⟯ Fyx K := isScalarTower_mid' F⟮y⟯⟮x⟯
  .trans F⟮y⟯ Fyx K

end AdjoinTranscendental

section constantExtension

open RatFunc

variable {F}
variable [Algebra F[X] K] [FaithfulSMul F[X] K] [FunctionField F K]

attribute [local instance] Polynomial.algebra

section Unbundled

open Polynomial

variable {E : Type*} [Field E] [Algebra F E] [Algebra E[X] K] [FaithfulSMul E[X] K]

/-
**FunctionField.finiteDimensional_ratFunc_of_constantExtension** 是 Mathlib 中的一个定
理，位于命名空间 `FunctionField`。
形式化陈述：finiteDimensional_ratFunc_of_constantExtension [IsScalarTower F[X] E[X] K]
 : FiniteDimensional F⟮X⟯ E⟮X⟯
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RatFunc.instIsScalarTowerOfPolynomial_1`：∀ (A : Type u_1) (k : Type u_2)
 (K : Type u_3) [inst : CommRing A] [inst_1 : IsDomain A] [inst_2 : Field k]   [
inst_3 : Field K] [inst_4 : A…
· 使用定理 `RatFunc.instIsScalarTowerOfPolynomial`：∀ (R : Type u_1) (A : Type u_2) (
K : Type u_3) [inst : CommRing A] [inst_1 : IsDomain A] [inst_2 : Field K]   [in
st_3 : Algebra (Polynomial …
-/
theorem finiteDimensional_ratFunc_of_constantExtension [IsScalarTower F[X] E[X] K] :
    FiniteDimensional F⟮X⟯ E⟮X⟯ :=
  .equiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F⟮X⟯ E⟮X⟯ K)).toLinearEquiv.symm

/-- Let `K` be a function field over `F`. If `E` is an algebraic extension of `F` which is
contained in `K` then it is finite over `F`. -/
/-
**FunctionField.finiteDimensional_of_constantExtension** 是 Mathlib 中的一个定理，位于命名空间
 `FunctionField`。
形式化陈述：finiteDimensional_of_constantExtension [IsScalarTower F[X] E[X] K] [Algebr
a.IsAlgebraic F E] : FiniteDimensional F E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FunctionField.finiteDimensional_ratFunc_of_constantExtension`：finiteDime
nsional_ratFunc_of_constantExtension [IsScalarTower F[X] E[X] K] : FiniteDimensi
onal F⟮X⟯ E⟮X⟯
· 使用定理 `Module.finite_of_finrank_pos`：finite_of_finrank_pos (h : 0 < finrank R M
) : Module.Finite R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `RatFunc.finrank_ratFunc_ratFunc`：finrank_ratFunc_ratFunc : Module.finran
k k⟮X⟯ K⟮X⟯ = Module.finrank k K

--- 原说明 ---
Let `K` be a function field over `F`. If `E` is an algebraic extension of `F` wh
ich is
contained in `K` then it is finite over `F`.
-/
theorem finiteDimensional_of_constantExtension [IsScalarTower F[X] E[X] K]
    [Algebra.IsAlgebraic F E] : FiniteDimensional F E :=
  have := finiteDimensional_ratFunc_of_constantExtension (F := F) (E := E) K
  Module.finite_of_finrank_pos ((finrank_ratFunc_ratFunc F E) ▸ Module.finrank_pos)

end Unbundled

section IntermediateField

variable [Algebra F K] (E : IntermediateField F K) [Algebra E[X] K] [FaithfulSMul E[X] K]
  [IsScalarTower F[X] E[X] K]

/-
**FunctionField.** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FiniteDimensional F⟮X⟯ E⟮X⟯ :=
  finiteDimensional_ratFunc_of_constantExtension K

/-- Let `K` be a function field over `F`. If `E` is an algebraic extension of `F` which is
contained in `K` then it is finite over `F`. -/
/-
**FunctionField.** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `K` be a function field over `F`. If `E` is an algebraic extension of `F` wh
ich is
contained in `K` then it is finite over `F`.
-/
instance [Algebra.IsAlgebraic F E] : FiniteDimensional F E :=
  finiteDimensional_of_constantExtension K

end IntermediateField

end constantExtension

end FunctionField

