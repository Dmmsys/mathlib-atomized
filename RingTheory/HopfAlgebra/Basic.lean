/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Hopf algebras

In this file we define `HopfAlgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toHopfAlgebra`

## Main definitions

* `HopfAlgebra R A` : the Hopf algebra structure on an `R`-bialgebra `A`.
* `HopfAlgebra.antipode` : the `R`-linear map `A →ₗ[R] A`.
* `HopfAlgebra.ofConvInverse` : construct a Hopf algebra from a two-sided convolution inverse
  of the identity.
* `HopfAlgebra.ofAlgHom` : the same for commutative `A`, with `AlgHom` hypotheses.

## Main results

* `HopfAlgebra.antipode_one` : the antipode of the unit is the unit.
* `HopfAlgebra.antipode_mul` : the antipode is an antihomomorphism: `S(ab) = S(b)S(a)`.

## TODO

* Uniqueness of Hopf algebra structure on a bialgebra (i.e. if the algebra and coalgebra structures
  agree then the antipodes must also agree).

* If `A` is commutative then `antipode` is an algebra homomorphism.

* If `A` is commutative then `antipode` is necessarily a bijection and its square is
  the identity.

(Note that all three facts have been proved for Hopf bimonoids in an arbitrary braided category,
so we could deduce the facts here from an equivalence `HopfAlgCat R ≌ Hopf (ModuleCat R)`.)

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

public section

open Bialgebra

universe u v w

/-- Isolates the antipode of a Hopf algebra, to allow API to be constructed before proving the
Hopf algebra axioms. See `HopfAlgebra` for documentation. -/
/-
**HopfAlgebraStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (A : Type v) → [CommSemiring R] → [Semiring A] → Type (max 
u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isolates the antipode of a Hopf algebra, to allow API to be constructed before p
roving the
Hopf algebra axioms. See `HopfAlgebra` for documentation.
-/
class HopfAlgebraStruct (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    extends Bialgebra R A where
  /-- The antipode of the Hopf algebra. -/
  antipode (R) : A →ₗ[R] A

/-- A Hopf algebra over a commutative (semi)ring `R` is a bialgebra over `R` equipped with an
`R`-linear endomorphism `antipode` satisfying the antipode axioms. -/
/-
**HopfAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (A : Type v) → [CommSemiring R] → [Semiring A] → Type (max 
u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hopf algebra over a commutative (semi)ring `R` is a bialgebra over `R` equippe
d with an
`R`-linear endomorphism `antipode` satisfying the antipode axioms.
-/
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    HopfAlgebraStruct R A where
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_rTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_lTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

namespace HopfAlgebra

export HopfAlgebraStruct (antipode)

variable {R : Type u} {A : Type v} {ι : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  {a : A}

@[simp]
/-
**HopfAlgebra.mul_antipode_rTensor_comul_apply** 是 Mathlib 中的一个定理，位于命名空间 `HopfAl
gebra`。
形式化陈述：mul_antipode_rTensor_comul_apply (a : A) : LinearMap.mul' R A ((antipode R
).rTensor A (Coalgebra.comul a)) = algebraMap R A (Coalgebra.counit a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HopfAlgebra.mul_antipode_rTensor_comul`：∀ {R : Type u} {A : Type v} {ins
t : CommSemiring R} {inst_1 : Semiring A} [self : HopfAlgebra R A],   LinearMap.
mul' R A ∘ₗ LinearMap.rTenso…
-/
theorem mul_antipode_rTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).rTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_rTensor_comul a

@[simp]
/-
**HopfAlgebra.mul_antipode_lTensor_comul_apply** 是 Mathlib 中的一个定理，位于命名空间 `HopfAl
gebra`。
形式化陈述：mul_antipode_lTensor_comul_apply (a : A) : LinearMap.mul' R A ((antipode R
).lTensor A (Coalgebra.comul a)) = algebraMap R A (Coalgebra.counit a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HopfAlgebra.mul_antipode_lTensor_comul`：∀ {R : Type u} {A : Type v} {ins
t : CommSemiring R} {inst_1 : Semiring A} [self : HopfAlgebra R A],   LinearMap.
mul' R A ∘ₗ LinearMap.lTenso…
-/
theorem mul_antipode_lTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).lTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_lTensor_comul a

@[simp]
/-
**HopfAlgebra.antipode_one** 是 Mathlib 中的一个定理，位于命名空间 `HopfAlgebra`。
形式化陈述：antipode_one : HopfAlgebra.antipode R (1 : A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bialgebra.comul_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R}
 {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.comul 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Bialgebra.counit_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R
} {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.counit 1 = 1
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
· 使用定理 `HopfAlgebra.mul_antipode_rTensor_comul_apply`：mul_antipode_rTensor_comul
_apply (a : A) : LinearMap.mul' R A ((antipode R).rTensor A (Coalgebra.comul a))
 = algebraMap R A (Coalgebra.couni…
-/
theorem antipode_one :
    HopfAlgebra.antipode R (1 : A) = 1 := by
  simpa [Algebra.TensorProduct.one_def] using mul_antipode_rTensor_comul_apply (R := R) (1 : A)

open Coalgebra
/-
**HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit** 是 Mathlib 中的一个引理，位于命名空间 `H
opfAlgebra`。
形式化陈述：sum_antipode_mul_eq_algebraMap_counit (repr : Repr R a ι) : ∑ i in repr.in
dex, antipode R (repr.left i) * repr.right i = algebraMap R A (counit a)
参数：repr : Repr R a ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Coalgebra.Repr.eq`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [
inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : CoalgebraStru
ct R A]…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `HopfAlgebra.mul_antipode_rTensor_comul`：∀ {R : Type u} {A : Type v} {ins
t : CommSemiring R} {inst_1 : Semiring A} [self : HopfAlgebra R A],   LinearMap.
mul' R A ∘ₗ LinearMap.rTenso…
-/
lemma sum_antipode_mul_eq_algebraMap_counit (repr : Repr R a ι) :
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)
/-
**HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit** 是 Mathlib 中的一个引理，位于命名空间 `H
opfAlgebra`。
形式化陈述：sum_mul_antipode_eq_algebraMap_counit (repr : Repr R a ι) : ∑ i in repr.in
dex, repr.left i * antipode R (repr.right i) = algebraMap R A (counit a)
参数：repr : Repr R a ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Coalgebra.Repr.eq`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [
inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : CoalgebraStru
ct R A]…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `HopfAlgebra.mul_antipode_lTensor_comul`：∀ {R : Type u} {A : Type v} {ins
t : CommSemiring R} {inst_1 : Semiring A} [self : HopfAlgebra R A],   LinearMap.
mul' R A ∘ₗ LinearMap.lTenso…
-/
lemma sum_mul_antipode_eq_algebraMap_counit (repr : Repr R a ι) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)
/-
**HopfAlgebra.sum_antipode_mul_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `HopfAlgebra`。
形式化陈述：sum_antipode_mul_eq_smul (repr : Repr R a ι) : ∑ i in repr.index, antipode
 R (repr.left i) * repr.right i = counit (R
参数：repr : Repr R a ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit`：sum_antipode_mul_eq_a
lgebraMap_counit (repr : Repr R a ι) : ∑ i in repr.index, antipode R (repr.left 
i) * repr.right i = algebraMap R A (cou…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma sum_antipode_mul_eq_smul (repr : Repr R a ι) :
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      counit (R := R) a • 1 := by
  rw [sum_antipode_mul_eq_algebraMap_counit, Algebra.smul_def, mul_one]
/-
**HopfAlgebra.sum_mul_antipode_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `HopfAlgebra`。
形式化陈述：sum_mul_antipode_eq_smul (repr : Repr R a ι) : ∑ i in repr.index, repr.lef
t i * antipode R (repr.right i) = counit (R
参数：repr : Repr R a ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit`：sum_mul_antipode_eq_a
lgebraMap_counit (repr : Repr R a ι) : ∑ i in repr.index, repr.left i * antipode
 R (repr.right i) = algebraMap R A (cou…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma sum_mul_antipode_eq_smul (repr : Repr R a ι) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      counit (R := R) a • 1 := by
  rw [sum_mul_antipode_eq_algebraMap_counit, Algebra.smul_def, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-
**HopfAlgebra.counit_antipode** 是 Mathlib 中的一个定理，位于命名空间 `HopfAlgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : HopfAlgebra R A] (a : A),   CoalgebraStruct.counit ((HopfAlgebraStruct
.antipode R) a) = CoalgebraStruct.counit a
参数：a : A；(HopfAlgebraStruct.antipode R) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Bialgebra.counit_mul`：counit_mul (a b : A) : counit (R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Coalgebra.sum_counit_smul`：sum_counit_smul (𝓡 : Repr R a ι) : ∑ x in 𝓡.i
ndex, counit (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `Bialgebra.counit_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R
} {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.counit 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `HopfAlgebra.sum_mul_antipode_eq_smul`：sum_mul_antipode_eq_smul (repr : R
epr R a ι) : ∑ i in repr.index, repr.left i * antipode R (repr.right i) = counit
 (R
-/
@[simp] lemma counit_antipode (a : A) : counit (R := R) (antipode R a) = counit a := by
  calc
        counit (antipode R a)
    _ = counit (∑ i ∈ (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) := by
      simp_rw [map_sum, counit_mul, ← smul_eq_mul, ← map_smul, ← map_sum, sum_counit_smul]
    _ = counit a := by simpa using congr(counit (R := R) $(sum_mul_antipode_eq_smul (ℛ R a)))
/-
**HopfAlgebra.counit_comp_antipode** 是 Mathlib 中的一个定理，位于命名空间 `HopfAlgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : HopfAlgebra R A],   CoalgebraStruct.counit ∘ₗ HopfAlgebraStruct.antipo
de R = CoalgebraStruct.counit
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `HopfAlgebra.counit_antipode`：∀ {R : Type u} {A : Type v} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : HopfAlgebra R A] (a : A),   CoalgebraSt
ruct.counit ((Hop…
-/
@[simp] lemma counit_comp_antipode : counit ∘ₗ antipode R = counit (A := A) := by
  ext; exact counit_antipode _

end HopfAlgebra

namespace CommSemiring

variable (R : Type u) [CommSemiring R]

open HopfAlgebra

/-- Every commutative (semi)ring is a Hopf algebra over itself -/
/-
**CommSemiring.toHopfAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiring`。
形式化陈述：toHopfAlgebra : HopfAlgebra R R where antipode
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every commutative (semi)ring is a Hopf algebra over itself
-/
instance toHopfAlgebra : HopfAlgebra R R where
  antipode := .id
  mul_antipode_rTensor_comul := by ext; simp
  mul_antipode_lTensor_comul := by ext; simp

@[simp]
/-
**CommSemiring.antipode_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CommSemiring`。
形式化陈述：antipode_eq_id : antipode R (A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antipode_eq_id : antipode R (A := R) = .id := rfl

end CommSemiring

namespace HopfAlgebra

variable {R A : Type*}

open Coalgebra WithConv LinearMap

/-- Upgrade a bialgebra to a Hopf algebra by specifying a convolution inverse of the identity. -/
/-
**HopfAlgebra.ofConvInverse** 是 Mathlib 中的一个缩写定义，位于命名空间 `HopfAlgebra`。
形式化陈述：ofConvInverse [CommSemiring R] [Semiring A] [Bialgebra R A] (antipode : A 
->ₗ[R] A) (antipode_convMul_id : toConv antipode * toConv LinearMap.id = 1) (id_
convMul_antipode : toConv LinearMap.id * toConv antipode = 1) : HopfAlgebra R A 
where antipode
参数：antipode : A ->ₗ[R] A；antipode_convMul_id : toConv antipode * toConv LinearMa
p.id = 1；id_convMul_antipode : toConv LinearMap.id * toConv antipode = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrade a bialgebra to a Hopf algebra by specifying a convolution inverse of the
 identity.
-/
noncomputable abbrev ofConvInverse [CommSemiring R] [Semiring A] [Bialgebra R A]
    (antipode : A →ₗ[R] A)
    (antipode_convMul_id : toConv antipode * toConv LinearMap.id = 1)
    (id_convMul_antipode : toConv LinearMap.id * toConv antipode = 1) :
    HopfAlgebra R A where
  antipode := antipode
  mul_antipode_rTensor_comul := by simpa using! congr(($antipode_convMul_id).ofConv)
  mul_antipode_lTensor_comul := by simpa using! congr(($id_convMul_antipode).ofConv)

/-- Upgrade a commutative bialgebra to a Hopf algebra by specifying the antipode `A →ₐ[R] A`
with appropriate conditions. -/
/-
**HopfAlgebra.ofAlgHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `HopfAlgebra`。
形式化陈述：ofAlgHom [CommSemiring R] [CommSemiring A] [Bialgebra R A] (antipode : A -
>ₐ[R] A) (mul_antipode_rTensor_comul : ((Algebra.TensorProduct.lift antipode (.i
d R A) fun _ => Commute.all _).comp (Bialgebra.comulAlgHom R A)) = (Algebra.ofId
 R A).comp (Bialgebra.counitAlgHom R A)) (mul_antipode_lTensor_comul : (Algebra.
TensorProduct.lift (.id R A) antipode fun _ _ => Commute.all _ _).comp (Bialgebr
a.comulAlgHom R A) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)) : Hop
fAlgebra R A
参数：antipode : A ->ₐ[R] A；mul_antipode_rTensor_comul : ((Algebra.TensorProduct.li
ft antipode (.id R A) fun _ => Commute.all _).comp (Bialgebra.comulAlgHom R A)) 
= (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)；mul_antipode_lTensor_comu
l : (Algebra.TensorProduct.lift (.id R A) antipode fun _ _ => Commute.all _ _).c
omp (Bialgebra.comulAlgHom R A) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHo
m R A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrade a commutative bialgebra to a Hopf algebra by specifying the antipode `A 
→ₐ[R] A`
with appropriate conditions.
-/
noncomputable abbrev ofAlgHom [CommSemiring R] [CommSemiring A] [Bialgebra R A]
    (antipode : A →ₐ[R] A)
    (mul_antipode_rTensor_comul :
      ((Algebra.TensorProduct.lift antipode (.id R A) fun _ ↦ Commute.all _).comp
        (Bialgebra.comulAlgHom R A)) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A))
    (mul_antipode_lTensor_comul :
      (Algebra.TensorProduct.lift (.id R A) antipode fun _ _ ↦ Commute.all _ _).comp
        (Bialgebra.comulAlgHom R A) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)) :
    HopfAlgebra R A :=
  ofConvInverse antipode.toLinearMap
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_rTensor_comul).toLinearMap))
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_lTensor_comul).toLinearMap))

end HopfAlgebra

