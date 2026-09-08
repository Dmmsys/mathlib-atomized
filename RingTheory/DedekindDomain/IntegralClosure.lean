/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Trace.Basic

/-!
# Integral closure of Dedekind domains

This file shows the integral closure of a Dedekind domain (in particular, the ring of integers
of a number field) is a Dedekind domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

public section

open Algebra Module
open scoped nonZeroDivisors Polynomial

variable (A K : Type*) [CommRing A] [Field K]

section IsIntegralClosure

/-! ### `IsIntegralClosure` section

We show that an integral closure of a Dedekind domain in a finite separable
field extension is again a Dedekind domain. This implies the ring of integers
of a number field is a Dedekind domain. -/


variable [Algebra A K] [IsFractionRing A K]
variable (L : Type*) [Field L] (C : Type*) [CommRing C]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]
include K L

set_option backward.isDefEq.respectTransparency.types false in
/-- If `L` is an algebraic extension of `K = Frac(A)` and `L` has no zero smul divisors by `A`,
then `L` is the localization of the integral closure `C` of `A` in `L` at `A⁰`. -/
/-
**IsIntegralClosure.isLocalization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.isLocalization [IsDomain A] [Algebra.IsAlgebraic K L] : 
IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.isDomain`：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [
inst_1 : Semiring B] [IsDomain B] (e : A ≃* B), IsDomain A
· 使用定理 `instIsDomainSubtypeMemSubalgebraIntegralClosure`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [IsDomain S] [inst_3 : Algebr
a R S],   IsDomain ↥(integralClosure …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Module.IsTorsionFree.trans_faithfulSMul`：Module.IsTorsionFree.trans_fait
hfulSMul [Nontrivial R] [IsCancelMulZero A] [AddCommMonoid M] [Module A M] [Modu
le R M] [IsTorsionFree A M] […
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `IsIntegralClosure.isTorsionFree`：isTorsionFree [Module R A] [IsScalarTow
er R A B] [IsTorsionFree R B] : IsTorsionFree R A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsIntegral.exists_multiple_integral_of_isLocalization`：IsIntegral.exists
_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S] (x : 
S) (hx : IsIntegral Rₘ x) : exists m : M, I…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `L` is an algebraic extension of `K = Frac(A)` and `L` has no zero smul divis
ors by `A`,
then `L` is the localization of the integral closure `C` of `A` in `L` at `A⁰`.
-/
theorem IsIntegralClosure.isLocalization [IsDomain A] [Algebra.IsAlgebraic K L] :
    IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L := by
  have : IsDomain C :=
    (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  have : IsTorsionFree A L := .trans_faithfulSMul A K L
  have : IsTorsionFree A C := IsIntegralClosure.isTorsionFree A L
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · rintro ⟨_, x, hx, rfl⟩
    rw [isUnit_iff_ne_zero, map_ne_zero_iff _ (IsIntegralClosure.algebraMap_injective C A L),
      Subtype.coe_mk, map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A C)]
    exact mem_nonZeroDivisors_iff_ne_zero.mp hx
  · obtain ⟨m, hm⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization A⁰ z
        (Algebra.IsIntegral.isIntegral (R := K) z)
    obtain ⟨x, hx⟩ : ∃ x, algebraMap C L x = m • z := IsIntegralClosure.isIntegral_iff.mp hm
    refine ⟨⟨x, algebraMap A C m, m, SetLike.coe_mem m, rfl⟩, ?_⟩
    rw [Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, hx, mul_comm, Submonoid.smul_def,
      smul_def]
  · simp only [IsIntegralClosure.algebraMap_injective C A L h]
/-
**IsIntegralClosure.isLocalization_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.isLocalization_of_isSeparable [IsDomain A] [Algebra.IsSe
parable K L] : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem IsIntegralClosure.isLocalization_of_isSeparable [IsDomain A] [Algebra.IsSeparable K L] :
    IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
  IsIntegralClosure.isLocalization A K L C

variable [FiniteDimensional K L]
variable {A K L}
/-
**IsIntegralClosure.range_le_span_dualBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.range_le_span_dualBasis [Algebra.IsSeparable K L] {ι : T
ype*} [Finite ι] [DecidableEq ι] (b : Basis ι K L) (hb_int : forall i, IsIntegra
l A (b i)) [IsIntegrallyClosed A] : LinearMap.range ((Algebra.linearMap C L).res
trictScalars A) <= Submodule.span A (Set.range <| (traceForm K L).dualBasis (tra
ceForm_nondegenerate K L) b)
参数：b : Basis ι K L；hb_int : forall i, IsIntegral A (b i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.BilinForm.dualSubmodule_span_of_basis`：dualSubmodule_span_of_b
asis {ι} [Finite ι] [DecidableEq ι] (hB : B.Nondegenerate) (b : Basis ι S M) : B
.dualSubmodule (Submodule.span R (Set…
· 使用引理 `LinearMap.BilinForm.le_flip_dualSubmodule`：le_flip_dualSubmodule {N₁ N₂ 
: Submodule R M} : N₁ <= B.flip.dualSubmodule N₂ ↔ N₂ <= B.dualSubmodule N₁
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosed.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosed R]
 {x : K} : IsIntegral R x ↔ exists y : R, algebraMap R K y = x
· 使用定理 `Algebra.isIntegral_trace`：Algebra.isIntegral_trace [FiniteDimensional L 
F] {x : F} (hx : IsIntegral R x) : IsIntegral R (Algebra.trace L F x)
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `IsIntegralClosure.isIntegral`：∀ (R : Type u_1) {A : Type u_2} (B : Type 
u_3) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 :
 Algebra R B] [ins…
-/
theorem IsIntegralClosure.range_le_span_dualBasis [Algebra.IsSeparable K L] {ι : Type*} [Finite ι]
    [DecidableEq ι] (b : Basis ι K L) (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    LinearMap.range ((Algebra.linearMap C L).restrictScalars A) ≤
    Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceForm_nondegenerate K L) b) := by
  rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis,
    ← LinearMap.BilinForm.le_flip_dualSubmodule, Submodule.span_le]
  rintro _ ⟨i, rfl⟩ _ ⟨y, rfl⟩
  simp only [LinearMap.coe_restrictScalars, linearMap_apply, LinearMap.BilinForm.flip_apply,
    traceForm_apply]
  refine Submodule.mem_one.mpr <| IsIntegrallyClosed.isIntegral_iff.mp ?_
  exact isIntegral_trace ((IsIntegralClosure.isIntegral A L y).algebraMap.mul (hb_int i))
/-
**integralClosure_le_span_dualBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure_le_span_dualBasis [Algebra.IsSeparable K L] {ι : Type*} [F
inite ι] [DecidableEq ι] (b : Basis ι K L) (hb_int : forall i, IsIntegral A (b i
)) [IsIntegrallyClosed A] : Subalgebra.toSubmodule (integralClosure A L) <= Subm
odule.span A (Set.range <| (traceForm K L).dualBasis (traceForm_nondegenerate K 
L) b)
参数：b : Basis ι K L；hb_int : forall i, IsIntegral A (b i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `IsIntegralClosure.range_le_span_dualBasis`：IsIntegralClosure.range_le_sp
an_dualBasis [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι] (b
 : Basis ι K L) (hb_int : foral…
-/
theorem integralClosure_le_span_dualBasis [Algebra.IsSeparable K L] {ι : Type*} [Finite ι]
    [DecidableEq ι] (b : Basis ι K L) (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    Subalgebra.toSubmodule (integralClosure A L) ≤
    Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceForm_nondegenerate K L) b) := by
  refine le_trans ?_ (IsIntegralClosure.range_le_span_dualBasis (integralClosure A L) b hb_int)
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

variable [IsDomain A]
variable (A K)

/-- Send a set of `x`s in a finite extension `L` of the fraction field of `R`
to `(y : R) • x ∈ integralClosure R L`. -/
/-
**exists_integral_multiples** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_integral_multiples (s : Finset L) : exists y != (0 : A), forall x i
n s, IsIntegral A (y • x)
参数：s : Finset L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isAlgebraic`：IsLocalization.isAlgebraic [Nontrivial R] (M
 : Submonoid R) [IsLocalization M S] : Algebra.IsAlgebraic R S where isAlgebraic
 x
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsAlgebraic.exists_integral_multiples`：∀ (R : Type u_1) {A : Typ
e u_3} [inst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [NoZeroDivis
ors R]   [alg : Algebra.IsAlgebraic…

--- 原说明 ---
Send a set of `x`s in a finite extension `L` of the fraction field of `R`
to `(y : R) • x ∈ integralClosure R L`.
-/
theorem exists_integral_multiples (s : Finset L) :
    ∃ y ≠ (0 : A), ∀ x ∈ s, IsIntegral A (y • x) :=
  have := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have := Algebra.IsAlgebraic.trans A K L
  Algebra.IsAlgebraic.exists_integral_multiples ..

variable (L)

/-- If `L` is a finite extension of `K = Frac(A)`,
then `L` has a basis over `A` consisting of integral elements. -/
/-
**FiniteDimensional.exists_is_basis_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.exists_is_basis_integral : exists (s : Finset L) (b : Ba
sis s K L), forall x, IsIntegral A (b x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `exists_integral_multiples`：exists_integral_multiples (s : Finset L) : ex
ists y != (0 : A), forall x in s, IsIntegral A (y • x)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `L` is a finite extension of `K = Frac(A)`,
then `L` has a basis over `A` consisting of integral elements.
-/
theorem FiniteDimensional.exists_is_basis_integral :
    ∃ (s : Finset L) (b : Basis s K L), ∀ x, IsIntegral A (b x) := by
  let := Classical.decEq L
  let s' := IsNoetherian.finsetBasisIndex K L
  let bs' := IsNoetherian.finsetBasis K L
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (Finset.univ.image bs')
  have hy' : algebraMap A L y ≠ 0 := by
    refine mt ((injective_iff_map_eq_zero (algebraMap A L)).mp ?_ _) hy
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  refine ⟨s', bs'.map {Algebra.lmul _ _ (algebraMap A L y) with
    toFun := fun x => algebraMap A L y * x
    invFun := fun x => (algebraMap A L y)⁻¹ * x
    left_inv := ?_
    right_inv := ?_}, ?_⟩
  · intro x; simp only [inv_mul_cancel_left₀ hy']
  · intro x; simp only [mul_inv_cancel_left₀ hy']
  · rintro ⟨x', hx'⟩
    simp only [Algebra.smul_def, Finset.mem_image, Finset.mem_univ,
      true_and] at his'
    exact his' _ ⟨_, rfl⟩

variable [Algebra.IsSeparable K L]

/-- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian over `A`. -/
/-
**IsIntegralClosure.isNoetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.isNoetherian [IsIntegrallyClosed A] [IsNoetherianRing A]
 : IsNoetherian A C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.exists_is_basis_integral`：FiniteDimensional.exists_is_
basis_integral : exists (s : Finset L) (b : Basis s K L), forall x, IsIntegral A
 (b x)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `isNoetherian_span_of_finite`：isNoetherian_span_of_finite (R) {M} [Ring R
] [AddCommGroup M] [Module R M] [IsNoetherianRing R] {A : Set M} (hA : A.Finite)
 : IsNoetherian R…
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsIntegralClosure.range_le_span_dualBasis`：IsIntegralClosure.range_le_sp
an_dualBasis [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι] (b
 : Basis ι K L) (hb_int : foral…
· 使用定理 `isNoetherian_of_ker_bot`：isNoetherian_of_ker_bot [IsNoetherian S P] {σ :
 R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->
ₛₗ[σ] P) (hf …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `Submodule.ker_inclusion`：ker_inclusion (p p' : Submodule R M) (h : p <= 
p') : ker (inclusion h) = ⊥
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …

--- 原说明 ---
If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian over `A`.
-/
theorem IsIntegralClosure.isNoetherian [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherian A C := by
  have := Classical.decEq L
  obtain ⟨s, b, hb_int⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' := (traceForm K L).dualBasis (traceForm_nondegenerate K L) b
  let := isNoetherian_span_of_finite A (Set.finite_range b')
  let f : C →ₗ[A] Submodule.span A (Set.range b') :=
    (Submodule.inclusion (IsIntegralClosure.range_le_span_dualBasis C b hb_int)).comp
      ((Algebra.linearMap C L).restrictScalars A).rangeRestrict
  refine isNoetherian_of_ker_bot f ?_
  rw [LinearMap.ker_comp, Submodule.ker_inclusion, Submodule.comap_bot, LinearMap.ker_codRestrict]
  exact LinearMap.ker_eq_bot_of_injective (IsIntegralClosure.algebraMap_injective C A L)

/-- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian. -/
/-
**IsIntegralClosure.isNoetherianRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRin
g A] : IsNoetherianRing C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isNoetherianRing_iff`：isNoetherianRing_iff {R} [Semiring R] : IsNoetheri
anRing R ↔ IsNoetherian R R
· 使用定理 `isNoetherian_of_tower`：isNoetherian_of_tower (R) {S M} [Semiring R] [Sem
iring S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R
 S M] (h : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsIntegralClosure.isNoetherian`：IsIntegralClosure.isNoetherian [IsIntegr
allyClosed A] [IsNoetherianRing A] : IsNoetherian A C

--- 原说明 ---
If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian.
-/
theorem IsIntegralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing C :=
  isNoetherianRing_iff.mpr <| isNoetherian_of_tower A (IsIntegralClosure.isNoetherian A K L C)

/-- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
finite over `A`. -/
/-
**IsIntegralClosure.finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.finite [IsIntegrallyClosed A] [IsNoetherianRing A] : Mod
ule.Finite A C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isNoetherian`：IsIntegralClosure.isNoetherian [IsIntegr
allyClosed A] [IsNoetherianRing A] : IsNoetherian A C
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…

--- 原说明 ---
If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
finite over `A`.
-/
theorem IsIntegralClosure.finite [IsIntegrallyClosed A] [IsNoetherianRing A] :
    Module.Finite A C := by
  have := IsIntegralClosure.isNoetherian A K L C
  exact Module.IsNoetherian.finite A C

/-- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a principal ring
and `L` has no zero smul divisors by `A`, the integral closure `C` of `A` in `L` is
a free `A`-module. -/
/-
**IsIntegralClosure.module_free** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.module_free [IsTorsionFree A L] [IsPrincipalIdealRing A]
 : Module.Free A C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsIntegralClosure.isNoetherian`：IsIntegralClosure.isNoetherian [IsIntegr
allyClosed A] [IsNoetherianRing A] : IsNoetherian A C
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用引理 `IsIntegralClosure.isTorsionFree`：isTorsionFree [Module R A] [IsScalarTow
er R A B] [IsTorsionFree R B] : IsTorsionFree R A

--- 原说明 ---
If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a principa
l ring
and `L` has no zero smul divisors by `A`, the integral closure `C` of `A` in `L`
 is
a free `A`-module.
-/
theorem IsIntegralClosure.module_free [IsTorsionFree A L] [IsPrincipalIdealRing A] :
    Module.Free A C :=
  haveI : IsTorsionFree A C := IsIntegralClosure.isTorsionFree A L
  haveI : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L _
  inferInstance

/-- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a principal ring
and `L` has no zero smul divisors by `A`, the `A`-rank of the integral closure `C` of `A` in `L`
is equal to the `K`-rank of `L`. -/
/-
**IsIntegralClosure.rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.rank [IsPrincipalIdealRing A] [IsTorsionFree A L] : Modu
le.finrank A C = Module.finrank K L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.module_free`：IsIntegralClosure.module_free [IsTorsionF
ree A L] [IsPrincipalIdealRing A] : Module.Free A C
· 使用定理 `IsIntegralClosure.isNoetherian`：IsIntegralClosure.isNoetherian [IsIntegr
allyClosed A] [IsNoetherianRing A] : IsNoetherian A C
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι

--- 原说明 ---
If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a principa
l ring
and `L` has no zero smul divisors by `A`, the `A`-rank of the integral closure `
C` of `A` in `L`
is equal to the `K`-rank of `L`.
-/
theorem IsIntegralClosure.rank [IsPrincipalIdealRing A] [IsTorsionFree A L] :
    Module.finrank A C = Module.finrank K L := by
  have : Module.Free A C := IsIntegralClosure.module_free A K L C
  have : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L C
  have : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
    IsIntegralClosure.isLocalization A K L C
  let b := Basis.localizationLocalization K A⁰ L (Module.Free.chooseBasis A C)
  rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis b]

variable {A K}

/-- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure of `A` in `L` is
Noetherian. -/
/-
**integralClosure.isNoetherianRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing 
A] : IsNoetherianRing (integralClosure A L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isNoetherianRing`：IsIntegralClosure.isNoetherianRing [
IsIntegrallyClosed A] [IsNoetherianRing A] : IsNoetherianRing C
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure of `A` in `L` is
Noetherian.
-/
theorem integralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing (integralClosure A L) :=
  IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)

variable (A K) [IsDomain C]

set_option linter.overlappingInstances false

/-- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure `C` of `A` in `L` is a Dedekind domain.

This cannot be an instance since `A`, `K` or `L` can't be inferred. See also the instance
`integralClosure.isDedekindDomain_fractionRing` where `K := FractionRing A`
and `C := integralClosure A L`. -/
/-
**IsIntegralClosure.isDedekindDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.isDedekindDomain [IsDedekindDomain A] : IsDedekindDomain
 C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isFractionRing_of_finite_extension`：isFractionRing_of_
finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L] [FiniteDimensi
onal K L] : IsFractionRing C L
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
· 使用定理 `IsIntegralClosure.isNoetherianRing`：IsIntegralClosure.isNoetherianRing [
IsIntegrallyClosed A] [IsNoetherianRing A] : IsNoetherianRing C
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `Ring.DimensionLEOne.of_isIntegral`：of_isIntegral (B : Type*) [CommRing B
] [IsDomain B] [Nontrivial R] [Algebra R B] [Algebra.IsIntegral R B] [DimensionL
EOne R] : DimensionLEOn…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x

--- 原说明 ---
If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind
 domain,
the integral closure `C` of `A` in `L` is a Dedekind domain.

This cannot be an instance since `A`, `K` or `L` can't be inferred. See also the
 instance
`integralClosure.isDedekindDomain_fractionRing` where `K := FractionRing A`
and `C := integralClosure A L`.
-/
theorem IsIntegralClosure.isDedekindDomain [IsDedekindDomain A] : IsDedekindDomain C :=
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  { IsIntegralClosure.isNoetherianRing A K L C,
    Ring.DimensionLEOne.of_isIntegral A C,
    (isIntegrallyClosed_iff L).mpr fun {x} hx =>
      ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
        IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain C }

/-- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

This cannot be an instance since `K` can't be inferred. See also the instance
`integralClosure.isDedekindDomain_fractionRing` where `K := FractionRing A`. -/
/-
**integralClosure.isDedekindDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure.isDedekindDomain [IsDedekindDomain A] : IsDedekindDomain (
integralClosure A L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isDedekindDomain`：IsIntegralClosure.isDedekindDomain [
IsDedekindDomain A] : IsDedekindDomain C
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsDomainSubtypeMemSubalgebraIntegralClosure`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [IsDomain S] [inst_3 : Algebr
a R S],   IsDomain ↥(integralClosure …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind
 domain,
the integral closure of `A` in `L` is a Dedekind domain.

This cannot be an instance since `K` can't be inferred. See also the instance
`integralClosure.isDedekindDomain_fractionRing` where `K := FractionRing A`.
-/
theorem integralClosure.isDedekindDomain [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)

variable [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]

/-- If `L` is a finite separable extension of `Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

See also the lemma `integralClosure.isDedekindDomain` where you can choose
the field of fractions yourself. -/
/-
**integralClosure.isDedekindDomain_fractionRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：integralClosure.isDedekindDomain_fractionRing [IsDedekindDomain A] : IsDed
ekindDomain (integralClosure A L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `integralClosure.isDedekindDomain`：integralClosure.isDedekindDomain [IsDe
dekindDomain A] : IsDedekindDomain (integralClosure A L)

--- 原说明 ---
If `L` is a finite separable extension of `Frac(A)`, where `A` is a Dedekind dom
ain,
the integral closure of `A` in `L` is a Dedekind domain.

See also the lemma `integralClosure.isDedekindDomain` where you can choose
the field of fractions yourself.
-/
instance integralClosure.isDedekindDomain_fractionRing [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  integralClosure.isDedekindDomain A (FractionRing A) L

end IsIntegralClosure

