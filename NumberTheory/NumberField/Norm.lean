/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Eric Rodriguez
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norm in number fields

Given a finite extension of number fields, we define the norm morphism as a function between the
rings of integers.

## Main definitions
* `RingOfIntegers.norm K` : `Algebra.norm` as a morphism `(𝓞 L) →* (𝓞 K)`.

## Main results
* `RingOfIntegers.dvd_norm` : if `L/K` is a finite Galois extension of fields, then, for all
  `(x : 𝓞 L)` we have that `x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x)`.

-/

@[expose] public section


open scoped NumberField

open Finset NumberField Algebra Module IntermediateField

section Rat

variable {K : Type*} [Field K] [NumberField K] (x : 𝓞 K)

/-
**Algebra.coe_norm_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.coe_norm_int : (Algebra.norm Int x : Rat) = Algebra.norm Rat (x : 
K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Algebra.norm_localization`：Algebra.norm_localization [Module.Free R S] [
Module.Finite R S] (a : S) : Algebra.norm Rₘ (algebraMap S Sₘ a) = algebraMap R 
Rₘ (Algebra.nor…
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
-/
theorem Algebra.coe_norm_int : (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K) :=
  (Algebra.norm_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors ℤ) x).symm
/-
**Algebra.coe_trace_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.coe_trace_int : (Algebra.trace Int _ x : Rat) = Algebra.trace Rat 
K (x : K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Algebra.trace_localization`：Algebra.trace_localization [Module.Free R S]
 [Module.Finite R S] (a : S) : Algebra.trace Rₘ Sₘ (algebraMap S Sₘ a) = algebra
Map R Rₘ (Algebr…
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
-/
theorem Algebra.coe_trace_int : (Algebra.trace ℤ _ x : ℚ) = Algebra.trace ℚ K (x : K) :=
  (Algebra.trace_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors ℤ) x).symm

end Rat

namespace RingOfIntegers

variable {L : Type*} (K : Type*) [Field K] [Field L] [Algebra K L]

/-- `Algebra.norm` as a morphism between the rings of integers. -/
/-
**RingOfIntegers.norm** 是 Mathlib 中的一个定义，位于命名空间 `RingOfIntegers`。
形式化陈述：norm : 𝓞 L ->* 𝓞 K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Algebra.norm` as a morphism between the rings of integers.
-/
noncomputable def norm : 𝓞 L →* 𝓞 K :=
  RingOfIntegers.restrict_monoidHom
    ((Algebra.norm K).comp (algebraMap (𝓞 L) L : (𝓞 L) →* L))
    fun x => isIntegral_norm K x.2
/-
**RingOfIntegers.coe_norm** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：∀ {L : Type u_1} (K : Type u_2) [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L]   (x : NumberField.RingOfIntegers L), ↑((RingOfIntegers.norm K)
 x) = (Algebra.norm K) ↑x
参数：K : Type u_2；x : NumberField.RingOfIntegers L；(RingOfIntegers.norm K) x；Algeb
ra.norm K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_norm (x : 𝓞 L) : norm K x = Algebra.norm K (x : L) :=
  rfl
/-
**RingOfIntegers.coe_algebraMap_norm** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：coe_algebraMap_norm (x : 𝓞 L) : (algebraMap (𝓞 K) (𝓞 L) (norm K x) : L) = 
algebraMap K L (Algebra.norm K (x : L))
参数：x : 𝓞 L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMap_norm (x : 𝓞 L) :
    (algebraMap (𝓞 K) (𝓞 L) (norm K x) : L) = algebraMap K L (Algebra.norm K (x : L)) :=
  rfl
/-
**RingOfIntegers.algebraMap_norm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RingOfInt
egers`。
形式化陈述：algebraMap_norm_algebraMap (x : 𝓞 K) : algebraMap _ K (norm K (algebraMap 
(𝓞 K) (𝓞 L) x)) = Algebra.norm K (algebraMap K L (algebraMap _ _ x))
参数：x : 𝓞 K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_norm_algebraMap (x : 𝓞 K) :
    algebraMap _ K (norm K (algebraMap (𝓞 K) (𝓞 L) x)) =
      Algebra.norm K (algebraMap K L (algebraMap _ _ x)) :=
  rfl
/-
**RingOfIntegers.norm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：norm_algebraMap (x : 𝓞 K) : norm K (algebraMap (𝓞 K) (𝓞 L) x) = x ^ finran
k K L
参数：x : 𝓞 K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.RingOfIntegers.ext_iff`：∀ {K : Type u_1} [inst : Field K] {x
 y : NumberField.RingOfIntegers K}, x = y ↔ ↑x = ↑y
· 使用引理 `NumberField.RingOfIntegers.coe_eq_algebraMap`：coe_eq_algebraMap (x : 𝓞 K
) : (x : K) = algebraMap _ _ x
· 使用定理 `RingOfIntegers.algebraMap_norm_algebraMap`：algebraMap_norm_algebraMap (x
 : 𝓞 K) : algebraMap _ K (norm K (algebraMap (𝓞 K) (𝓞 L) x)) = Algebra.norm K (a
lgebraMap K L (algebraMap _ _ x…
· 使用定理 `Algebra.norm_algebraMap`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRin
g R] [inst_1 : Ring S] [inst_2 : Algebra R S] [Module.Free R S] (x : R),   (Alge
bra.norm R) (…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem norm_algebraMap (x : 𝓞 K) : norm K (algebraMap (𝓞 K) (𝓞 L) x) = x ^ finrank K L := by
  rw [RingOfIntegers.ext_iff, RingOfIntegers.coe_eq_algebraMap,
    RingOfIntegers.algebraMap_norm_algebraMap, Algebra.norm_algebraMap,
    RingOfIntegers.coe_eq_algebraMap, map_pow]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `L/K` is a finite Galois extension of fields, then, for all `(x : 𝓞 L)` we have that
`x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x)`. -/
/-
**RingOfIntegers.dvd_norm** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：dvd_norm [FiniteDimensional K L] [IsGalois K L] (x : 𝓞 L) : x ∣ algebraMap
 (𝓞 K) (𝓞 L) (norm K x)
参数：x : 𝓞 L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.prod`：IsIntegral.prod {α : Type*} {s : Finset α} (f : α -> A)
 (h : forall x in s, IsIntegral R (f x)) : IsIntegral R (∏ x in s, f x)
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `NumberField.RingOfIntegers.isIntegral_coe`：isIntegral_coe (x : 𝓞 K) : Is
Integral Int (algebraMap _ K x)
· 使用定理 `NumberField.RingOfIntegers.ext`：∀ {K : Type u_1} [inst : Field K] {x y :
 NumberField.RingOfIntegers K}, ↑x = ↑y → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingOfIntegers.coe_algebraMap_norm`：coe_algebraMap_norm (x : 𝓞 L) : (alg
ebraMap (𝓞 K) (𝓞 L) (norm K x) : L) = algebraMap K L (Algebra.norm K (x : L))
· 使用定理 `Algebra.norm_eq_prod_automorphisms`：norm_eq_prod_automorphisms [IsGalois
 K L] (x : L) : algebraMap K L (norm K x) = ∏ σ : Gal(L/K), σ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `L/K` is a finite Galois extension of fields, then, for all `(x : 𝓞 L)` we ha
ve that
`x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x)`.
-/
theorem dvd_norm [FiniteDimensional K L] [IsGalois K L] (x : 𝓞 L) :
    x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x) := by
  classical
  have hint :
    IsIntegral ℤ (∏ σ ∈ univ.erase (AlgEquiv.refl : Gal(L/K)), σ x) :=
    IsIntegral.prod _ (fun σ _ =>
      ((RingOfIntegers.isIntegral_coe x).map σ))
  refine ⟨⟨_, hint⟩, ?_⟩
  ext
  rw [coe_algebraMap_norm K x, norm_eq_prod_automorphisms]
  simp [← Finset.mul_prod_erase _ _ (mem_univ AlgEquiv.refl)]
/-
**RingOfIntegers.isUnit_norm_of_isGalois** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntege
rs`。
形式化陈述：isUnit_norm_of_isGalois [FiniteDimensional K L] [IsGalois K L] {x : 𝓞 L} :
 IsUnit (norm K x) ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
· 使用定理 `RingOfIntegers.dvd_norm`：dvd_norm [FiniteDimensional K L] [IsGalois K L]
 (x : 𝓞 L) : x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x)
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem isUnit_norm_of_isGalois [FiniteDimensional K L] [IsGalois K L] {x : 𝓞 L} :
    IsUnit (norm K x) ↔ IsUnit x :=
  ⟨fun hx ↦ isUnit_of_dvd_unit (dvd_norm K x) (hx.map _), IsUnit.map _⟩

variable (F : Type*) [Field F] [Algebra K F] [FiniteDimensional K F]
/-
**RingOfIntegers.norm_norm** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：norm_norm [Algebra F L] [FiniteDimensional F L] [IsScalarTower K F L] (x :
 𝓞 L) : norm K (norm F x) = norm K x
参数：x : 𝓞 L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.RingOfIntegers.ext_iff`：∀ {K : Type u_1} [inst : Field K] {x
 y : NumberField.RingOfIntegers K}, x = y ↔ ↑x = ↑y
· 使用定理 `RingOfIntegers.coe_norm`：∀ {L : Type u_1} (K : Type u_2) [inst : Field K
] [inst_1 : Field L] [inst_2 : Algebra K L]   (x : NumberField.RingOfIntegers L)
, ↑((RingOfIn…
· 使用定理 `Algebra.norm_norm`：Algebra.norm_norm {A} [Ring A] [Algebra R A] [Algebra
 S A] [IsScalarTower R S A] [Module.Free S A] {a : A} : norm R (norm S a) = norm
 R a
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem norm_norm [Algebra F L] [FiniteDimensional F L] [IsScalarTower K F L] (x : 𝓞 L) :
    norm K (norm F x) = norm K x := by
  rw [RingOfIntegers.ext_iff, coe_norm, coe_norm, coe_norm, Algebra.norm_norm]

variable {F}
/-
**RingOfIntegers.isUnit_norm** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：isUnit_norm [CharZero K] {x : 𝓞 F} : IsUnit (norm K x) ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FiniteDimensional.right`：∀ (F : Type u) (K : Type v) (A : Type w) [inst 
: Semiring F] [inst_1 : Semiring K] [inst_2 : _root_.Module F K]   [inst_3 : Add
CommMonoid A]…
· 使用定理 `normalClosure.instIsScalarTowerSubtypeMemIntermediateFieldNormalClosure`
：∀ (F : Type u_1) (K : Type u_2) (L : Type u_3) [inst : Field F] [inst_1 : Field
 K] [inst_2 : Field L]   [inst_3 : Algebra F K] [inst_4 : Alg…
· 使用定理 `IsGalois.tower_top_of_isGalois`：IsGalois.tower_top_of_isGalois [IsGalois
 F E] : IsGalois K E
· 使用定理 `IsSepClosure.isGalois`：∀ {k : Type u} [inst : Field k] {K : Type v} [ins
t_1 : Field K] [inst_2 : Algebra k K] [IsSepClosure k K], IsGalois k K
· 使用定理 `IsSepClosure.of_isAlgClosure_of_perfectField`：∀ (k : Type u) [inst : Fie
ld k] (K : Type v) [inst_1 : Field K] [inst_2 : Algebra k K] [IsAlgClosure k K] 
  [PerfectField k], IsSepClosure k…
· 使用定理 `AlgebraicClosure.instIsAlgClosureOfIsAlgebraic`：∀ (k : Type u) [inst : F
ield k] {L : Type u_1} [inst_1 : Field L] [inst_2 : Algebra k L] [Algebra.IsAlge
braic k L],   IsAlgClosure k (Algebr…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isUnit_pow_iff`：∀ {M : Type u_1} [inst : Monoid M] {n : ℕ} {a : M}, n ≠ 
0 → (IsUnit (a ^ n) ↔ IsUnit a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingOfIntegers.norm_norm`：norm_norm [Algebra F L] [FiniteDimensional F L
] [IsScalarTower K F L] (x : 𝓞 L) : norm K (norm F x) = norm K x
· 使用定理 `RingOfIntegers.norm_algebraMap`：norm_algebraMap (x : 𝓞 K) : norm K (alge
braMap (𝓞 K) (𝓞 L) x) = x ^ finrank K L
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
（共 33 条，此处仅展示前 30 条）
-/
theorem isUnit_norm [CharZero K] {x : 𝓞 F} : IsUnit (norm K x) ↔ IsUnit x := by
  let : Algebra K (AlgebraicClosure K) := AlgebraicClosure.instAlgebra K
  let L := normalClosure K F (AlgebraicClosure F)
  have : FiniteDimensional F L := FiniteDimensional.right K F L
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  calc
    IsUnit (norm K x) ↔ IsUnit ((norm K) x ^ finrank F L) :=
      (isUnit_pow_iff (pos_iff_ne_zero.mp finrank_pos)).symm
    _ ↔ IsUnit (norm K (algebraMap (𝓞 F) (𝓞 L) x)) := by
      rw [← norm_norm K F (algebraMap (𝓞 F) (𝓞 L) x), norm_algebraMap F _, map_pow]
    _ ↔ IsUnit (algebraMap (𝓞 F) (𝓞 L) x) := isUnit_norm_of_isGalois K
    _ ↔ IsUnit (norm F (algebraMap (𝓞 F) (𝓞 L) x)) := (isUnit_norm_of_isGalois F).symm
    _ ↔ IsUnit (x ^ finrank F L) := (congr_arg IsUnit (norm_algebraMap F _)).to_iff
    _ ↔ IsUnit x := isUnit_pow_iff (pos_iff_ne_zero.mp finrank_pos)

end RingOfIntegers

