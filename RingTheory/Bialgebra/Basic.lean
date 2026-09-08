/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey, Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebras

In this file we define `Bialgebra`s.

## Main definitions

* `Bialgebra R A`: the structure of a bialgebra on the `R`-algebra `A`;
* `CommSemiring.toBialgebra`: a commutative semiring is a bialgebra over itself.

## Implementation notes

Rather than the "obvious" axiom `∀ a b, counit (a * b) = counit a * counit b`, the far
more convoluted `mul_compr₂_counit` is used as a structure field; this says that
the corresponding two maps `A →ₗ[R] A →ₗ[R] R` are equal; a similar trick is
used for comultiplication as well. An alternative constructor `Bialgebra.mk'` is provided
with the more easily-readable axioms. The argument for using the more convoluted axioms
is that in practice there is evidence that they will be easier to prove (especially
when dealing with things like tensor products of bialgebras). This does make the definition
more surprising to mathematicians, however mathlib is no stranger to definitions which
are surprising to mathematicians -- see for example its definition of a group.
Note that this design decision is also compatible with that of `Coalgebra`. The lengthy
docstring for these convoluted fields attempts to explain what is going on.

The constructor `Bialgebra.ofAlgHom` is dual to the default constructor: For `R` is a commutative
semiring and `A` an `R`-algebra, it consumes the counit and comultiplication as algebra
homomorphisms that satisfy the coalgebra axioms to define a bialgebra structure on `A`.

## References

* <https://en.wikipedia.org/wiki/Bialgebra>

## Tags

bialgebra
-/

@[expose] public section

universe u v w

open Function
open scoped TensorProduct

/-- A bialgebra over a commutative (semi)ring `R` is both an algebra and a coalgebra over `R`, such
that the counit and comultiplication are algebra morphisms. -/
/-
**Bialgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (A : Type v) → [CommSemiring R] → [Semiring A] → Type (max 
u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bialgebra over a commutative (semi)ring `R` is both an algebra and a coalgebra
 over `R`, such
that the counit and comultiplication are algebra morphisms.
-/
class Bialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Algebra R A, Coalgebra R A where
  -- The counit is an algebra morphism
  /-- The counit on a bialgebra preserves 1. -/
  counit_one : counit 1 = 1
  /-- The counit on a bialgebra preserves multiplication. Note that this is written
  in a rather obscure way: it says that two bilinear maps `A →ₗ[R] A →ₗ[R]` are equal.
  The two corresponding equal linear maps `A ⊗[R] A →ₗ[R]`
  are the following: the first factors through `A` and is multiplication on `A` followed
  by `counit`. The second factors through `R ⊗[R] R`, and is `counit ⊗ counit` followed by
  multiplication on `R`.

  See `Bialgebra.mk'` for a constructor for bialgebras which uses
  the more familiar but mathematically equivalent `counit (a * b) = counit a * counit b`. -/
  mul_compr₂_counit : (LinearMap.mul R A).compr₂ counit = (LinearMap.mul R R).compl₁₂ counit counit
  -- The comultiplication is an algebra morphism
  /-- The comultiplication on a bialgebra preserves `1`. -/
  comul_one : comul 1 = 1
  /-- The comultiplication on a bialgebra preserves multiplication. This is written in
  a rather obscure way: it says that two bilinear maps `A →ₗ[R] A →ₗ[R] (A ⊗[R] A)`
  are equal. The corresponding equal linear maps `A ⊗[R] A →ₗ[R] A ⊗[R] A`
  are firstly multiplication followed by `comul`, and secondly `comul ⊗ comul` followed
  by multiplication on `A ⊗[R] A`.

  See `Bialgebra.mk'` for a constructor for bialgebras which uses the more familiar
  but mathematically equivalent `comul (a * b) = comul a * comul b`. -/
  mul_compr₂_comul :
    (LinearMap.mul R A).compr₂ comul = (LinearMap.mul R (A ⊗[R] A)).compl₁₂ comul comul

namespace Bialgebra

open Coalgebra

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [Bialgebra R A]

/-
**Bialgebra.counit_mul** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`。
形式化陈述：counit_mul (a b : A) : counit (R
参数：a b : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Bialgebra.mul_compr₂_counit`：∀ {R : Type u} {A : Type v} {inst : CommSem
iring R} {inst_1 : Semiring A} [self : Bialgebra R A],   (LinearMap.mul R A).com
pr₂ CoalgebraStru…
-/
lemma counit_mul (a b : A) : counit (R := R) (a * b) = counit a * counit b :=
  DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_counit a) b
/-
**Bialgebra.comul_mul** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`。
形式化陈述：comul_mul (a b : A) : comul (R
参数：a b : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Bialgebra.mul_compr₂_comul`：∀ {R : Type u} {A : Type v} {inst : CommSemi
ring R} {inst_1 : Semiring A} [self : Bialgebra R A],   (LinearMap.mul R A).comp
r₂ CoalgebraStru…
-/
lemma comul_mul (a b : A) : comul (R := R) (a * b) = comul a * comul b :=
  DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_comul a) b

attribute [simp] counit_one comul_one counit_mul comul_mul

/-- If `R` is a field (or even a commutative semiring) and `A`
is an `R`-algebra with a coalgebra structure, then `Bialgebra.mk'`
consumes proofs that the counit and comultiplication preserve
the identity and multiplication, and produces a bialgebra
/-
**Bialgebra.on** 是 Mathlib 中的一个结构，位于命名空间 `Bialgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on `A`. -/
@[instance_reducible]
/-
**Bialgebra.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
形式化陈述：mk' (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] 
[C : Coalgebra R A] (counit_one : C.counit 1 = 1) (counit_mul : forall {a b}, C.
counit (a * b) = C.counit a * C.counit b) (comul_one : C.comul 1 = 1) (comul_mul
 : forall {a b}, C.comul (a * b) = C.comul a * C.comul b) : Bialgebra R A where 
counit_one
参数：R : Type u；A : Type v；counit_one : C.counit 1 = 1；counit_mul : forall {a b}, 
C.counit (a * b) = C.counit a * C.counit b；comul_one : C.comul 1 = 1；comul_mul :
 forall {a b}, C.comul (a * b) = C.comul a * C.comul b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If `R` is a field (or even a commutative semiring) and `A`
is an `R`-algebra with a coalgebra structure, then `Bialgebra.mk'`
consumes proofs that the counit and comultiplication preserve
the identity and multiplication, and produces a bialgebra
structure on `A`.
-/
def mk' (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    [Algebra R A] [C : Coalgebra R A] (counit_one : C.counit 1 = 1)
    (counit_mul : ∀ {a b}, C.counit (a * b) = C.counit a * C.counit b)
    (comul_one : C.comul 1 = 1)
    (comul_mul : ∀ {a b}, C.comul (a * b) = C.comul a * C.comul b) :
    Bialgebra R A where
  counit_one := counit_one
  mul_compr₂_counit := by ext; exact counit_mul
  comul_one := comul_one
  mul_compr₂_comul := by ext; exact comul_mul

variable (R A)

/-- `counitAlgHom R A` is the counit of the `R`-bialgebra `A`, as an `R`-algebra map. -/
@[simps!]
/-
**Bialgebra.counitAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
形式化陈述：counitAlgHom : A ->ₐ[R] R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bialgebra.counit_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R
} {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.counit 1 = 1
· 使用引理 `Bialgebra.counit_mul`：counit_mul (a b : A) : counit (R

--- 原说明 ---
`counitAlgHom R A` is the counit of the `R`-bialgebra `A`, as an `R`-algebra map
.
-/
def counitAlgHom : A →ₐ[R] R :=
  .ofLinearMap counit counit_one counit_mul

/-- `comulAlgHom R A` is the comultiplication of the `R`-bialgebra `A`, as an `R`-algebra map. -/
@[simps!]
/-
**Bialgebra.comulAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
形式化陈述：comulAlgHom : A ->ₐ[R] A otimes[R] A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bialgebra.comul_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R}
 {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.comul 1 = 1
· 使用引理 `Bialgebra.comul_mul`：comul_mul (a b : A) : comul (R

--- 原说明 ---
`comulAlgHom R A` is the comultiplication of the `R`-bialgebra `A`, as an `R`-al
gebra map.
-/
def comulAlgHom : A →ₐ[R] A ⊗[R] A :=
  .ofLinearMap comul comul_one comul_mul

variable {R A}
/-
**Bialgebra.toLinearMap_counitAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Bialgebra R A],   (Bialgebra.counitAlgHom R A).toLinearMap = Coalgebra
Struct.counit
参数：Bialgebra.counitAlgHom R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_counitAlgHom : (counitAlgHom R A).toLinearMap = counit := rfl
/-
**Bialgebra.toLinearMap_comulAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Bialgebra R A],   (Bialgebra.comulAlgHom R A).toLinearMap = CoalgebraS
truct.comul
参数：Bialgebra.comulAlgHom R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_comulAlgHom : (comulAlgHom R A).toLinearMap = comul := rfl
/-
**Bialgebra.counit_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Bialgebra R A] (r : R),   CoalgebraStruct.counit ((algebraMap R A) r) 
= r
参数：r : R；(algebraMap R A) r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
@[simp] lemma counit_algebraMap (r : R) : counit (R := R) (algebraMap R A r) = r :=
  (counitAlgHom R A).commutes r
/-
**Bialgebra.comul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Bialgebra R A] (r : R),   CoalgebraStruct.comul ((algebraMap R A) r) =
 (algebraMap R (TensorProduct R A A)) r
参数：r : R；(algebraMap R A) r；algebraMap R (TensorProduct R A A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
@[simp] lemma comul_algebraMap (r : R) :
    comul (R := R) (algebraMap R A r) = algebraMap R (A ⊗[R] A) r :=
  (comulAlgHom R A).commutes r
/-
**Bialgebra.counit_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Bialgebra R A] (n : ℕ),   CoalgebraStruct.counit ↑n = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
@[simp] lemma counit_natCast (n : ℕ) : counit (R := R) (n : A) = n :=
  map_natCast (counitAlgHom R A) _
/-
**Bialgebra.comul_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Bialgebra R A] (n : ℕ),   CoalgebraStruct.comul ↑n = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
@[simp] lemma comul_natCast (n : ℕ) : comul (R := R) (n : A) = n :=
  map_natCast (comulAlgHom R A) _
/-
**Bialgebra.counit_pow** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Bialgebra R A] (a : A) (n : ℕ),   CoalgebraStruct.counit (a ^ n) = Coa
lgebraStruct.counit a ^ n
参数：a : A；n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
@[simp] lemma counit_pow (a : A) (n : ℕ) : counit (R := R) (a ^ n) = counit a ^ n :=
  map_pow (counitAlgHom R A) a n
/-
**Bialgebra.comul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Bialgebra R A] (a : A) (n : ℕ),   CoalgebraStruct.comul (a ^ n) = Coal
gebraStruct.comul a ^ n
参数：a : A；n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
@[simp] lemma comul_pow (a : A) (n : ℕ) : comul (R := R) (a ^ n) = comul a ^ n :=
  map_pow (comulAlgHom R A) a n

end Bialgebra

namespace CommSemiring
variable (R : Type u) [CommSemiring R]

open Bialgebra

/-- Every commutative (semi)ring is a bialgebra over itself -/
/-
**CommSemiring.toBialgebra** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiring`。
形式化陈述：toBialgebra : Bialgebra R R where mul_compr₂_counit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every commutative (semi)ring is a bialgebra over itself
-/
instance toBialgebra : Bialgebra R R where
  mul_compr₂_counit := by ext; simp
  counit_one := rfl
  mul_compr₂_comul := by ext; simp
  comul_one := rfl

end CommSemiring

namespace Bialgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-
**Bialgebra.counitAlgHom_self** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R], Bialgebra.counitAlgHom R R = Alg
Hom.id R R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma counitAlgHom_self : counitAlgHom R R = .id R R := rfl

/-- If `R` is a commutative semiring and `A` is an `R`-algebra,
then `Bialgebra.ofAlgHom` consumes the counit and comultiplication
as algebra homomorphisms that satisfy the coalgebra axioms to define
a bialgebra structure on `A`. -/
/-
**Bialgebra.ofAlgHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Bialgebra`。
形式化陈述：ofAlgHom (comul : A ->ₐ[R] (A otimes[R] A)) (counit : A ->ₐ[R] R) (h_coass
oc : (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp ((Algebra.TensorPro
duct.map comul (.id R A)).comp comul) = (Algebra.TensorProduct.map (.id R A) com
ul).comp comul) (h_rTensor : (Algebra.TensorProduct.map counit (.id R A)).comp c
omul = (Algebra.TensorProduct.lid R A).symm) (h_lTensor : (Algebra.TensorProduct
.map (.id R A) counit).comp comul = (Algebra.TensorProduct.rid R R A).symm) : Bi
algebra R A
参数：comul : A ->ₐ[R] (A otimes[R] A)；counit : A ->ₐ[R] R；h_coassoc : (Algebra.Ten
sorProduct.assoc R R R A A A).toAlgHom.comp ((Algebra.TensorProduct.map comul (.
id R A)).comp comul) = (Algebra.TensorProduct.map (.id R A) comul).comp comul；h_
rTensor : (Algebra.TensorProduct.map counit (.id R A)).comp comul = (Algebra.Ten
sorProduct.lid R A).symm；h_lTensor : (Algebra.TensorProduct.map (.id R A) counit
).comp comul = (Algebra.TensorProduct.rid R R A).symm。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a commutative semiring and `A` is an `R`-algebra,
then `Bialgebra.ofAlgHom` consumes the counit and comultiplication
as algebra homomorphisms that satisfy the coalgebra axioms to define
a bialgebra structure on `A`.
-/
abbrev ofAlgHom (comul : A →ₐ[R] (A ⊗[R] A)) (counit : A →ₐ[R] R)
    (h_coassoc : (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp
      ((Algebra.TensorProduct.map comul (.id R A)).comp comul)
      = (Algebra.TensorProduct.map (.id R A) comul).comp comul)
    (h_rTensor : (Algebra.TensorProduct.map counit (.id R A)).comp comul
      = (Algebra.TensorProduct.lid R A).symm)
    (h_lTensor : (Algebra.TensorProduct.map (.id R A) counit).comp comul
      = (Algebra.TensorProduct.rid R R A).symm) :
    Bialgebra R A :=
  letI : Coalgebra R A := {
    comul := comul
    counit := counit
    coassoc := congr(($h_coassoc).toLinearMap)
    rTensor_counit_comp_comul := congr(($h_rTensor).toLinearMap)
    lTensor_counit_comp_comul := congr(($h_lTensor).toLinearMap)
  }
  .mk' _ _ (map_one counit) (map_mul counit _ _) (map_one comul) (map_mul comul _ _)

end Bialgebra

namespace Bialgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (A) in
/-
**Bialgebra.algebraMap_injective** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`。
形式化陈述：algebraMap_injective : Injective (algebraMap R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `Bialgebra.counit_algebraMap`：∀ {R : Type u} {A : Type v} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (r : R),   CoalgebraStru
ct.counit ((algeb…
-/
lemma algebraMap_injective : Injective (algebraMap R A) := RightInverse.injective counit_algebraMap
/-
**Bialgebra.counit_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`。
形式化陈述：counit_surjective : Surjective (Coalgebra.counit : A ->ₗ[R] R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `Bialgebra.counit_algebraMap`：∀ {R : Type u} {A : Type v} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (r : R),   CoalgebraStru
ct.counit ((algeb…
-/
lemma counit_surjective : Surjective (Coalgebra.counit : A →ₗ[R] R) :=
  RightInverse.surjective counit_algebraMap

include R in
variable (R) in
/-- A bialgebra over a nontrivial ring is nontrivial. -/
/-
**Bialgebra.nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`。
形式化陈述：nontrivial [Nontrivial R] : Nontrivial A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用引理 `Bialgebra.algebraMap_injective`：algebraMap_injective : Injective (algebr
aMap R A)

--- 原说明 ---
A bialgebra over a nontrivial ring is nontrivial.
-/
lemma nontrivial [Nontrivial R] : Nontrivial A := (algebraMap_injective (R := R) _).nontrivial

end Bialgebra

