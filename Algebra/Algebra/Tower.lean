/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.Span.Basic


/-!
# Towers of algebras

In this file we prove basic facts about towers of algebras.

An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the latter asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `toAlgHom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/

@[expose] public section


open scoped Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]
variable {A}


/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `B`-module `M`.

This is a stronger version of `DistribSMul.toLinearMap`, and could also have been
called `Algebra.toModuleEnd`.

The typeclasses correspond to the situation where the types act on each other as
```
R ----→ B
| ⟍     |
|   ⟍   |
↓     ↘ ↓
A ----→ M
```
where the diagram commutes, the action by `R` commutes with everything, and the action by `A` and
`B` on `M` commute.

Typically this is most useful with `B = R` as `Algebra.lsmul R R A : A →ₐ[R] Module.End R M`.
However this can be used to get the fact that left-multiplication by `A` is right `A`-linear, and
vice versa, as
```lean
example : A →ₐ[R] Module.End Aᵐᵒᵖ A := Algebra.lsmul R Aᵐᵒᵖ A
example : Aᵐᵒᵖ →ₐ[R] Module.End A A := Algebra.lsmul R A A
```
respectively; though `LinearMap.mulLeft` and `LinearMap.mulRight` can also be used here.
-/
/-
**Algebra.lsmul** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：lsmul : A ->ₐ[R] Module.End B M where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
The `R`-algebra morphism `A → End (M)` corresponding to the representation of th
e algebra `A`
on the `B`-module `M`.

This is a stronger version of `DistribSMul.toLinearMap`, and could also have bee
n
called `Algebra.toModuleEnd`.

The typeclasses correspond to the situation where the types act on each other as
```
R ----→ B
| ⟍     |
|   ⟍   |
↓     ↘ ↓
A ----→ M
```
where the diagram commutes, the action by `R` commutes with everything, and the 
action by `A` and
`B` on `M` commute.

Typically this is most useful with `B = R` as `Algebra.lsmul R R A : A →ₐ[R] Mod
ule.End R M`.
However this can be used to get the fact that left-multiplication by `A` is righ
t `A`-linear, and
vice versa, as
```lean
example : A →ₐ[R] Module.End Aᵐᵒᵖ A := Algebra.lsmul R Aᵐᵒᵖ A
example : Aᵐᵒᵖ →ₐ[R] Module.End A A := Algebra.lsmul R A A
```
respectively; though `LinearMap.mulLeft` and `LinearMap.mulRight` can also be us
ed here.
-/
def lsmul : A →ₐ[R] Module.End B M where
  toFun := DistribSMul.toLinearMap B M
  map_one' := LinearMap.ext fun _ => one_smul A _
  map_mul' a b := LinearMap.ext <| smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' _a _b := LinearMap.ext fun _ => add_smul _ _ _
  commutes' r := LinearMap.ext <| algebraMap_smul A r

@[simp]
/-
**Algebra.lsmul_coe** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：lsmul_coe (a : A) : (lsmul R B M a : M -> M) = (a • ·)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
theorem lsmul_coe (a : A) : (lsmul R B M a : M → M) = (a • ·) := rfl
/-
**Algebra.lsmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：lsmul_apply (a : A) (m : M) : lsmul R B M a m = a • m
参数：a : A；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma lsmul_apply (a : A) (m : M) : lsmul R B M a m = a • m := rfl
/-
**Algebra.lsmul_eq_smul_one** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：lsmul_eq_smul_one (a : A) : lsmul R R M a = a • 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma lsmul_eq_smul_one (a : A) : lsmul R R M a = a • 1 := rfl

end Algebra

namespace IsScalarTower

section Module

variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [MulAction A M]
variable {R} {M}

/-
**IsScalarTower.algebraMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：algebraMap_smul [SMul R M] [IsScalarTower R A M] (r : R) (x : M) : algebra
Map R A r • x = r • x
参数：r : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `IsScalarTower.smul_assoc`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_1
1} {inst : SMul M N} {inst_1 : SMul N α} {inst_2 : SMul M α}   [self : IsScalarT
ower M N α] (x…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem algebraMap_smul [SMul R M] [IsScalarTower R A M] (r : R) (x : M) :
    algebraMap R A r • x = r • x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

variable {A} in
/-
**IsScalarTower.of_algebraMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：of_algebraMap_smul [SMul R M] (h : forall (r : R) (x : M), algebraMap R A 
r • x = r • x) : IsScalarTower R A M where smul_assoc r a x
参数：h : forall (r : R) (x : M), algebraMap R A r • x = r • x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem of_algebraMap_smul [SMul R M] (h : ∀ (r : R) (x : M), algebraMap R A r • x = r • x) :
    IsScalarTower R A M where
  smul_assoc r a x := by rw [Algebra.smul_def, mul_smul, h]

variable (R M) in
/-
**IsScalarTower.of_compHom** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：of_compHom : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_smul`：of_algebraMap_smul [SMul R M] (h : for
all (r : R) (x : M), algebraMap R A r • x = r • x) : IsScalarTower R A M where s
mul_assoc r a x
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem of_compHom : letI := MulAction.compHom M (algebraMap R A : R →* A); IsScalarTower R A M :=
  letI := MulAction.compHom M (algebraMap R A : R →* A); of_algebraMap_smul fun _ _ ↦ rfl

end Module

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable {R S A}

/-
**IsScalarTower.of_algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：of_algebraMap_eq [Algebra R A] (h : forall x, algebraMap R A x = algebraMa
p S A (algebraMap R S x)) : IsScalarTower R S A
参数：h : forall x, algebraMap R A x = algebraMap S A (algebraMap R S x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_algebraMap_eq [Algebra R A]
    (h : ∀ x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S A :=
  ⟨fun x y z => by simp_rw [Algebra.smul_def, map_mul, mul_assoc, h]⟩

/-- See note [partially-applied ext lemmas]. -/
/-
**IsScalarTower.of_algebraMap_eq'** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：of_algebraMap_eq' [Algebra R A] (h : algebraMap R A = (algebraMap S A).com
p (algebraMap R S)) : IsScalarTower R S A
参数：h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem of_algebraMap_eq' [Algebra R A]
    (h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A :=
  of_algebraMap_eq <| RingHom.ext_iff.1 h

variable (R S A)
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]
/-
**IsScalarTower.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.smul_assoc`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_1
1} {inst : SMul M N} {inst_1 : SMul N α} {inst_2 : SMul M α}   [self : IsScalarT
ower M N α] (x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) :=
  RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
/-
**IsScalarTower.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：algebraMap_apply (x : R) : algebraMap R A x = algebraMap S A (algebraMap R
 S x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
-/
theorem algebraMap_apply (x : R) : algebraMap R A x = algebraMap S A (algebraMap R S x) := by
  rw [algebraMap_eq R S A, RingHom.comp_apply]

@[ext]
/-
**IsScalarTower.Algebra.ext** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower.Algebra`。
形式化陈述：∀ {S : Type u} {A : Type v} [inst : CommSemiring S] [inst_1 : Semiring A] 
(h1 h2 : Algebra S A),   (∀ (r : S) (x : A),       (have I := h1;         r • x)
 =         r • x) →     h1 = h2
参数：h1 h2 : Algebra S A；∀ (r : S) (x : A),       (have I := h1;         r • x) = 
        r • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.algebra_ext`：algebra_ext {R : Type*} [CommSemiring R] {A : Type*
} [Semiring A] (P Q : Algebra R A) (h : forall r : R, (haveI
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by have I := h1; exact r • x) = r • x) : h1 = h2 :=
  Algebra.algebra_ext _ _ fun r => by
    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1

variable {R S A B}

@[simp]
/-
**IsScalarTower._root_.AlgHom.map_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsScalar
Tower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.map_algebraMap (f : A →ₐ[S] B) (r : R) :
    f (algebraMap R A r) = algebraMap R B r := by
  rw [algebraMap_apply R S A r, f.commutes, ← algebraMap_apply R S B]

variable (R)

@[simp]
/-
**IsScalarTower._root_.AlgHom.comp_algebraMap_of_tower** 是 Mathlib 中的一个定理，位于命名空间
 `IsScalarTower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.comp_algebraMap_of_tower (f : A →ₐ[S] B) :
    (f : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext (AlgHom.map_algebraMap f)

-- conflicts with IsScalarTower.Subalgebra
/-
**IsScalarTower.** 是 Mathlib 中的一个实例，位于命名空间 `IsScalarTower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 999) subsemiring (U : Subsemiring S) : IsScalarTower U S A :=
  of_algebraMap_eq fun _x => rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): removed @[nolint instance_priority], linter not ported yet
/-
**IsScalarTower.** 是 Mathlib 中的一个实例，位于命名空间 `IsScalarTower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 999) of_algHom {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    @IsScalarTower R A B _ f.toRingHom.toAlgebra.toSMul _ :=
  letI := (f : A →+* B).toAlgebra
  of_algebraMap_eq fun x => (f.commutes x).symm

end Semiring

end IsScalarTower

section Homs

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]
variable {A S B}

open IsScalarTower

namespace AlgHom

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
/-
**AlgHom.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：restrictScalars (f : A ->ₐ[S] B) : A ->ₐ[R] B
参数：f : A ->ₐ[S] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
R ⟶ S induces S-Alg ⥤ R-Alg
-/
def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
  { (f : A →+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
/-
**AlgHom.restrictScalars_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：restrictScalars_apply (f : A ->ₐ[S] B) (x : A) : f.restrictScalars R x = f
 x
参数：f : A ->ₐ[S] B；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_apply (f : A →ₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl
/-
**AlgHom.toLinearMap_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ (R : Type u) {S : Type v} {A : Type w} {B : Type u₁} [inst : CommSemirin
g R] [inst_1 : CommSemiring S]   [inst_2 : Semiring A] [inst_3 : Semiring B] [in
st_4 : Algebra R S] [inst_5 : Algebra S A] [inst_6 : Algebra S B]   [inst_7 : Al
gebra R A] [inst_8 : Algebra R B] [inst_9 : IsScalarTower R S A] [inst_10 : IsSc
alarTower R S B]   (f : A →ₐ[S] B), (AlgHom.restrictScalars R f).toLinearMap = ↑
R f.toLinearMap
参数：R : Type u；f : A →ₐ[S] B；AlgHom.restrictScalars R f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_restrictScalars (f : A →ₐ[S] B) :
    (f.restrictScalars R).toLinearMap = f.toLinearMap.restrictScalars R := rfl

@[simp]
/-
**AlgHom.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_restrictScalars (f : A ->ₐ[S] B) : (f.restrictScalars R : A ->+* B) = 
f
参数：f : A ->ₐ[S] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem coe_restrictScalars (f : A →ₐ[S] B) : (f.restrictScalars R : A →+* B) = f := rfl

@[simp]
/-
**AlgHom.coe_restrictScalars'** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_restrictScalars' (f : A ->ₐ[S] B) : (restrictScalars R f : A -> B) = f
参数：f : A ->ₐ[S] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars' (f : A →ₐ[S] B) : (restrictScalars R f : A → B) = f := rfl
/-
**AlgHom.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars R : (A ->ₐ
[S] B) -> A ->ₐ[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →ₐ[S] B) → A →ₐ[R] B) := fun _ _ h =>
  AlgHom.ext (AlgHom.congr_fun h :)

section

variable {R}

/-- Any `f : A →ₐ[R] B` is also an `S`-algebra homomorphism if the `R`-algebra structure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`. -/
@[simps! apply symm_apply]
/-
**AlgHom.extendScalarsOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S)) : (A 
->ₐ[R] B) ≃ (A ->ₐ[S] B) where toFun f
参数：h : Function.Surjective (algebraMap R S)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `f : A →ₐ[R] B` is also an `S`-algebra homomorphism if the `R`-algebra struc
ture on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`.
-/
def extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S)) :
    (A →ₐ[R] B) ≃ (A →ₐ[S] B) where
  toFun f := { f with commutes' := by simp [h.forall, ← IsScalarTower.algebraMap_apply] }
  invFun := restrictScalars R

@[simp]
/-
**AlgHom.restrictScalars_extendScalarsOfSurjective** 是 Mathlib 中的一个引理，位于命名空间 `Al
gHom`。
形式化陈述：restrictScalars_extendScalarsOfSurjective (h : Function.Surjective (algebr
aMap R S)) (f : A ->ₐ[R] B) : (f.extendScalarsOfSurjective h).restrictScalars R 
= f
参数：h : Function.Surjective (algebraMap R S)；f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S))
    (f : A →ₐ[R] B) :
    (f.extendScalarsOfSurjective h).restrictScalars R = f := rfl

/-- Any `f : A →ₐ[R] B` is also an `S`-algebra homomorphism if the `R`-algebra structure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`. -/
@[simps! apply symm_apply]
/-
**AlgHom.extendScalarsHomOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：extendScalarsHomOfSurjective (h : Function.Surjective (algebraMap R S)) : 
(A ->ₐ[R] A) ≃* (A ->ₐ[S] A) where __
参数：h : Function.Surjective (algebraMap R S)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `f : A →ₐ[R] B` is also an `S`-algebra homomorphism if the `R`-algebra struc
ture on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`.
-/
def extendScalarsHomOfSurjective (h : Function.Surjective (algebraMap R S)) :
    (A →ₐ[R] A) ≃* (A →ₐ[S] A) where
  __ := extendScalarsOfSurjective h
  map_mul' _ _ := rfl

end

end AlgHom

namespace AlgEquiv

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
/-
**AlgEquiv.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：restrictScalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B
参数：f : A ≃ₐ[S] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
R ⟶ S induces S-Alg ⥤ R-Alg
-/
def restrictScalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
  { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
/-
**AlgEquiv.restrictScalars_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：restrictScalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrictScalars R x = f 
x
参数：f : A ≃ₐ[S] B；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl
/-
**AlgEquiv.toAlgHom_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ (R : Type u) {S : Type v} {A : Type w} {B : Type u₁} [inst : CommSemirin
g R] [inst_1 : CommSemiring S]   [inst_2 : Semiring A] [inst_3 : Semiring B] [in
st_4 : Algebra R S] [inst_5 : Algebra S A] [inst_6 : Algebra S B]   [inst_7 : Al
gebra R A] [inst_8 : Algebra R B] [inst_9 : IsScalarTower R S A] [inst_10 : IsSc
alarTower R S B]   (f : A ≃ₐ[S] B), ↑(AlgEquiv.restrictScalars R f) = AlgHom.res
trictScalars R ↑f
参数：R : Type u；f : A ≃ₐ[S] B；AlgEquiv.restrictScalars R f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAlgHom_restrictScalars (f : A ≃ₐ[S] B) :
    (f.restrictScalars R).toAlgHom = f.toAlgHom.restrictScalars R := rfl
/-
**AlgEquiv.toLinearEquiv_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ (R : Type u) {S : Type v} {A : Type w} {B : Type u₁} [inst : CommSemirin
g R] [inst_1 : CommSemiring S]   [inst_2 : Semiring A] [inst_3 : Semiring B] [in
st_4 : Algebra R S] [inst_5 : Algebra S A] [inst_6 : Algebra S B]   [inst_7 : Al
gebra R A] [inst_8 : Algebra R B] [inst_9 : IsScalarTower R S A] [inst_10 : IsSc
alarTower R S B]   (f : A ≃ₐ[S] B), ↑(AlgEquiv.restrictScalars R f) = LinearEqui
v.restrictScalars R ↑f
参数：R : Type u；f : A ≃ₐ[S] B；AlgEquiv.restrictScalars R f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_restrictScalars (f : A ≃ₐ[S] B) :
    (f.restrictScalars R).toLinearEquiv = f.toLinearEquiv.restrictScalars R := rfl

@[simp]
/-
**AlgEquiv.toRingEquiv_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toRingEquiv_restrictScalars (f : A ≃ₐ[S] B) : (f.restrictScalars R : A ≃+*
 B) = f
参数：f : A ≃ₐ[S] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_restrictScalars (f : A ≃ₐ[S] B) : (f.restrictScalars R : A ≃+* B) = f := rfl

@[simp]
/-
**AlgEquiv.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_restrictScalars (f : A ≃ₐ[S] B) : (restrictScalars R f : A -> B) = f
参数：f : A ≃ₐ[S] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars (f : A ≃ₐ[S] B) : (restrictScalars R f : A → B) = f := rfl

@[deprecated (since := "2026-07-06")] alias coe_restrictScalars' := coe_restrictScalars
/-
**AlgEquiv.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars R : (A ≃ₐ[
S] B) -> A ≃ₐ[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `AlgEquiv.congr_fun`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A ≃ₐ[S] B) → A ≃ₐ[R] B) := fun _ _ h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h :)

@[simp]
/-
**AlgEquiv.symm_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：symm_restrictScalars (f : A ≃ₐ[S] B) : (f.restrictScalars R).symm = f.symm
.restrictScalars R
参数：f : A ≃ₐ[S] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_restrictScalars (f : A ≃ₐ[S] B) :
    (f.restrictScalars R).symm = f.symm.restrictScalars R :=
  rfl

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]
/-
**AlgEquiv.restrictScalars_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：restrictScalars_symm_apply (f : A ≃ₐ[S] B) (x : B) : (f.restrictScalars R)
.symm x = f.symm x
参数：f : A ≃ₐ[S] B；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrictScalars_symm_apply (f : A ≃ₐ[S] B) (x : B) :
    (f.restrictScalars R).symm x = f.symm x := by
  simp

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]
/-
**AlgEquiv.coe_restrictScalars_symm** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_restrictScalars_symm (f : A ≃ₐ[S] B) : ((f.restrictScalars R).symm : B
 ≃+* A) = f.symm
参数：f : A ≃ₐ[S] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `AlgEquiv.map_mul'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.map_add'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_restrictScalars_symm (f : A ≃ₐ[S] B) :
    ((f.restrictScalars R).symm : B ≃+* A) = f.symm := by
  simp

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]
/-
**AlgEquiv.coe_restrictScalars_symm'** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：coe_restrictScalars_symm' (f : A ≃ₐ[S] B) : ((restrictScalars R f).symm : 
B -> A) = f.symm
参数：f : A ≃ₐ[S] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_restrictScalars_symm' (f : A ≃ₐ[S] B) :
    ((restrictScalars R f).symm : B → A) = f.symm := by
  simp

/-- `AlgEquiv.restrictScalars` as a homomorphism. -/
/-
**AlgEquiv.restrictScalarsHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：restrictScalarsHom : (A ≃ₐ[S] A) ->* (A ≃ₐ[R] A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgEquiv.restrictScalars` as a homomorphism.
-/
def restrictScalarsHom : (A ≃ₐ[S] A) →* (A ≃ₐ[R] A) :=
  MulSemiringAction.toAlgAut (A ≃ₐ[S] A) R A

@[simp]
/-
**AlgEquiv.restrictScalarsHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：restrictScalarsHom_apply (f : A ≃ₐ[S] A) : f.restrictScalarsHom R = f.rest
rictScalars R
参数：f : A ≃ₐ[S] A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalarsHom_apply (f : A ≃ₐ[S] A) : f.restrictScalarsHom R = f.restrictScalars R :=
  rfl
/-
**AlgEquiv.restrictScalarsHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：restrictScalarsHom_injective : Function.Injective (restrictScalarsHom R : 
(A ≃ₐ[S] A) ->* (A ≃ₐ[R] A))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.restrictScalars_injective`：restrictScalars_injective : Function
.Injective (restrictScalars R : (A ≃ₐ[S] B) -> A ≃ₐ[R] B)
-/
theorem restrictScalarsHom_injective :
    Function.Injective (restrictScalarsHom R : (A ≃ₐ[S] A) →* (A ≃ₐ[R] A)) :=
  restrictScalars_injective R

section

variable {R}

/-- Any `f : A ≃ₐ[R] B` is also an `S`-algebra isomorphism if the `R`-algebra structure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`. -/
@[simps! apply symm_apply]
/-
**AlgEquiv.extendScalarsOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S)) : (A 
≃ₐ[R] B) ≃ A ≃ₐ[S] B where toFun f
参数：h : Function.Surjective (algebraMap R S)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.map_mul'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.map_add'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…

--- 原说明 ---
Any `f : A ≃ₐ[R] B` is also an `S`-algebra isomorphism if the `R`-algebra struct
ure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`.
-/
def extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S)) :
    (A ≃ₐ[R] B) ≃ A ≃ₐ[S] B where
  toFun f := { f with commutes' := (f.toAlgHom.extendScalarsOfSurjective h).commutes' }
  invFun := AlgEquiv.restrictScalars R
/-
**AlgEquiv.coe_extendScalarsOfSurjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type u} {S : Type v} {A : Type w} {B : Type u₁} [inst : CommSemirin
g R] [inst_1 : CommSemiring S]   [inst_2 : Semiring A] [inst_3 : Semiring B] [in
st_4 : Algebra R S] [inst_5 : Algebra S A] [inst_6 : Algebra S B]   [inst_7 : Al
gebra R A] [inst_8 : Algebra R B] [inst_9 : IsScalarTower R S A] [inst_10 : IsSc
alarTower R S B]   (h : Function.Surjective ⇑(algebraMap R S)) (f : A ≃ₐ[R] B), 
⇑((AlgEquiv.extendScalarsOfSurjective h) f) = ⇑f
参数：h : Function.Surjective ⇑(algebraMap R S)；f : A ≃ₐ[R] B；(AlgEquiv.extendScala
rsOfSurjective h) f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S))
    (f : A ≃ₐ[R] B) : ⇑(extendScalarsOfSurjective h f) = f := rfl

@[simp]
/-
**AlgEquiv.restrictScalars_extendScalarsOfSurjective** 是 Mathlib 中的一个引理，位于命名空间 `
AlgEquiv`。
形式化陈述：restrictScalars_extendScalarsOfSurjective (h : Function.Surjective (algebr
aMap R S)) (f : A ≃ₐ[R] B) : (f.extendScalarsOfSurjective h).restrictScalars R =
 f
参数：h : Function.Surjective (algebraMap R S)；f : A ≃ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S))
    (f : A ≃ₐ[R] B) :
    (f.extendScalarsOfSurjective h).restrictScalars R = f := rfl

@[simp]
/-
**AlgEquiv.extendScalarsOfSurjective_symm** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：extendScalarsOfSurjective_symm (h : Function.Surjective (algebraMap R S)) 
(f : A ≃ₐ[R] B) : (f.extendScalarsOfSurjective h).symm = f.symm.extendScalarsOfS
urjective h
参数：h : Function.Surjective (algebraMap R S)；f : A ≃ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extendScalarsOfSurjective_symm (h : Function.Surjective (algebraMap R S))
    (f : A ≃ₐ[R] B) :
    (f.extendScalarsOfSurjective h).symm = f.symm.extendScalarsOfSurjective h := rfl

/-- Any `f : A ≃ₐ[R] B` is also an `S`-algebra isomorphism if the `R`-algebra structure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`. -/
@[simps! apply symm_apply]
/-
**AlgEquiv.extendScalarsHomOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：extendScalarsHomOfSurjective (h : Function.Surjective ⇑(algebraMap R S)) :
 (A ≃ₐ[R] A) ≃* (A ≃ₐ[S] A) where __
参数：h : Function.Surjective ⇑(algebraMap R S)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `f : A ≃ₐ[R] B` is also an `S`-algebra isomorphism if the `R`-algebra struct
ure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`.
-/
def extendScalarsHomOfSurjective (h : Function.Surjective ⇑(algebraMap R S)) :
    (A ≃ₐ[R] A) ≃* (A ≃ₐ[S] A) where
  __ := extendScalarsOfSurjective h
  map_mul' _ _ := rfl

@[simp]
/-
**AlgEquiv.toMonoidHom_symm_extendScalarsHomOfSurjective** 是 Mathlib 中的一个引理，位于命名
空间 `AlgEquiv`。
形式化陈述：toMonoidHom_symm_extendScalarsHomOfSurjective (h : Function.Surjective (al
gebraMap R S)) : (extendScalarsHomOfSurjective h (A
参数：h : Function.Surjective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
lemma toMonoidHom_symm_extendScalarsHomOfSurjective (h : Function.Surjective (algebraMap R S)) :
    (extendScalarsHomOfSurjective h (A := A).symm : (A ≃ₐ[S] A) →* _) = restrictScalarsHom R :=
  rfl

end

end AlgEquiv

end Homs

namespace Submodule

variable {M}
variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
variable [Module R M] [Module A M] [IsScalarTower R A M]

/-- If `A` is an `R`-algebra such that the induced morphism `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
/-
**Submodule.restrictScalars_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_span (hsur : Function.Surjective (algebraMap R A)) (X : Se
t M) : restrictScalars R (span A X) = span R X
参数：hsur : Function.Surjective (algebraMap R A)；X : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p

--- 原说明 ---
If `A` is an `R`-algebra such that the induced morphism `R →+* A` is surjective,
 then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`.
-/
theorem restrictScalars_span (hsur : Function.Surjective (algebraMap R A)) (X : Set M) :
    restrictScalars R (span A X) = span R X := by
  refine ((span_le_restrictScalars R A X).antisymm fun m hm => ?_).symm
  refine span_induction subset_span (zero_mem _) (fun _ _ _ _ => add_mem) (fun a m _ hm => ?_) hm
  obtain ⟨r, rfl⟩ := hsur a
  simpa [algebraMap_smul] using smul_mem _ r hm
/-
**Submodule.coe_span_eq_span_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) 
(s : Set M) : (Submodule.span A s : Set M) = Submodule.span R s
参数：h : Function.Surjective (algebraMap R A)；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars_span`：restrictScalars_span (hsur : Function.Su
rjective (algebraMap R A)) (X : Set M) : restrictScalars R (span A X) = span R X
-/
theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s :=
  congr_arg ((↑) : Submodule R M → Set M) (Submodule.restrictScalars_span R A h s)

/--
Given a commutative ring `R`, an `R`-algebra `S` and an `R`-module `M` with a scalar tower
`IsScalarTower R S M`, if the algebra map from `R` to `S` is surjective, then this induces an order
isomorphism `Submodule S M ≃o Submodule R M`.
-/
@[simps apply symm_apply]
/-
**Submodule.orderIsoOfAlgebraMapSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`
。
形式化陈述：orderIsoOfAlgebraMapSurjective {R S M : Type*} [CommRing R] [Ring S] [AddC
ommGroup M] [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M] (h : F
unction.Surjective (algebraMap R S)) : Submodule S M ≃o Submodule R M where toFu
n N
参数：h : Function.Surjective (algebraMap R S)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a commutative ring `R`, an `R`-algebra `S` and an `R`-module `M` with a sc
alar tower
`IsScalarTower R S M`, if the algebra map from `R` to `S` is surjective, then th
is induces an order
isomorphism `Submodule S M ≃o Submodule R M`.
-/
def orderIsoOfAlgebraMapSurjective
    {R S M : Type*} [CommRing R] [Ring S] [AddCommGroup M]
    [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) : Submodule S M ≃o Submodule R M where
  toFun N := N.restrictScalars R
  invFun N := ⟨N.toAddSubmonoid, by simpa [h.forall] using N.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := .rfl

end Submodule

section Semiring

variable {R S A}

namespace Submodule

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid A]
variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

open IsScalarTower

/-
**Submodule.smul_mem_span_smul_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mem_span_smul_of_mem {s : Set S} {t : Set A} {k : S} (hks : k in span
 R s) {x : A} (hx : x in t) : k • x in span R (s • t)
参数：hks : k in span R s；hx : x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.smul_mem_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
: Set α} {t : Set β} {a : α} {b : β}, a ∈ s → b ∈ t → a • b ∈ s • t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `IsScalarTower.smul_assoc`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_1
1} {inst : SMul M N} {inst_1 : SMul N α} {inst_2 : SMul M α}   [self : IsScalarT
ower M N α] (x…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem smul_mem_span_smul_of_mem {s : Set S} {t : Set A} {k : S} (hks : k ∈ span R s) {x : A}
    (hx : x ∈ t) : k • x ∈ span R (s • t) :=
  span_induction (fun _ hc => subset_span <| Set.smul_mem_smul hc hx)
    (by rw [zero_smul]; exact zero_mem _)
    (fun c₁ c₂ _ _ ih₁ ih₂ => by rw [add_smul]; exact add_mem ih₁ ih₂)
    (fun b c _ hc => by rw [IsScalarTower.smul_assoc]; exact smul_mem _ _ hc) hks
/-
**Submodule.span_smul_of_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_smul_of_span_eq_top {s : Set S} (hs : span R s = ⊤) (t : Set A) : spa
n R (s • t) = (span S t).restrictScalars R
参数：hs : span R s = ⊤；t : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.closure_induction`：closure_induction {p : (x : M) -> x in span
 R s -> Prop} (zero : p 0 (Submodule.zero_mem _)) (add : forall x y hx hy, p x h
x -> p y hy -> p …
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `IsScalarTower.smul_assoc`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_1
1} {inst : SMul M N} {inst_1 : SMul N α} {inst_2 : SMul M α}   [self : IsScalarT
ower M N α] (x…
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem span_smul_of_span_eq_top {s : Set S} (hs : span R s = ⊤) (t : Set A) :
    span R (s • t) = (span S t).restrictScalars R :=
  le_antisymm
    (span_le.2 fun _x ⟨p, _hps, _q, hqt, hpqx⟩ ↦ hpqx ▸ (span S t).smul_mem p (subset_span hqt))
    fun _ hp ↦ closure_induction (hx := hp) (zero_mem _) (fun _ _ _ _ ↦ add_mem) fun s0 y hy ↦ by
      refine span_induction (fun x hx ↦ subset_span <| by exact ⟨x, hx, y, hy, rfl⟩) ?_ ?_ ?_
        (hs ▸ mem_top : s0 ∈ span R s)
      · rw [zero_smul]; apply zero_mem
      · intro _ _ _ _; rw [add_smul]; apply add_mem
      · intro r s0 _ hy; rw [IsScalarTower.smul_assoc]; exact smul_mem _ r hy

-- The following two lemmas were originally used to prove `span_smul_of_span_eq_top`
-- but are now not needed.
/-
**Submodule.smul_mem_span_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mem_span_smul' {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x
 : A} (hx : x in span R (s • t)) : k • x in span R (s • t)
参数：hs : span R s = ⊤；hx : x in span R (s • t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_smul_of_span_eq_top`：span_smul_of_span_eq_top {s : Set S}
 (hs : span R s = ⊤) (t : Set A) : span R (s • t) = (span S t).restrictScalars R
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem smul_mem_span_smul' {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R (s • t)) : k • x ∈ span R (s • t) := by
  rw [span_smul_of_span_eq_top hs] at hx ⊢; exact (span S t).smul_mem k hx
/-
**Submodule.smul_mem_span_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x 
: A} (hx : x in span R t) : k • x in span R (s • t)
参数：hs : span R s = ⊤；hx : x in span R t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_smul_of_span_eq_top`：span_smul_of_span_eq_top {s : Set S}
 (hs : span R s = ⊤) (t : Set A) : span R (s • t) = (span S t).restrictScalars R
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R
-/
theorem smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R t) : k • x ∈ span R (s • t) := by
  rw [span_smul_of_span_eq_top hs]
  exact (span S t).smul_mem k (span_le_restrictScalars R S t hx)

end Module

section Algebra

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]
variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

/-- A variant of `Submodule.span_image` for `algebraMap`. -/
/-
**Submodule.span_algebraMap_image** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_algebraMap_image (a : Set R) : Submodule.span R (algebraMap R S '' a)
 = (Submodule.span R a).map (Algebra.linearMap R S)
参数：a : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)

--- 原说明 ---
A variant of `Submodule.span_image` for `algebraMap`.
-/
theorem span_algebraMap_image (a : Set R) :
    Submodule.span R (algebraMap R S '' a) = (Submodule.span R a).map (Algebra.linearMap R S) :=
  (Submodule.span_image <| Algebra.linearMap R S).trans rfl
/-
**Submodule.span_algebraMap_image_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：span_algebraMap_image_of_tower {S T : Type*} [CommSemiring S] [Semiring T]
 [Module R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) : Su
bmodule.span R (algebraMap S T '' a) = (Submodule.span R a).map ((Algebra.linear
Map S T).restrictScalars R)
参数：a : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
-/
theorem span_algebraMap_image_of_tower {S T : Type*} [CommSemiring S] [Semiring T] [Module R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) :
    Submodule.span R (algebraMap S T '' a) =
      (Submodule.span R a).map ((Algebra.linearMap S T).restrictScalars R) :=
  (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl
/-
**Submodule.map_mem_span_algebraMap_image** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_mem_span_algebraMap_image {S T : Type*} [CommSemiring S] [Semiring T] 
[Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (x : S) (a : Set
 S) (hx : x in Submodule.span R a) : algebraMap S T x in Submodule.span R (algeb
raMap S T '' a)
参数：x : S；a : Set S；hx : x in Submodule.span R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_algebraMap_image_of_tower`：span_algebraMap_image_of_tower
 {S T : Type*} [CommSemiring S] [Semiring T] [Module R S] [Algebra R T] [Algebra
 S T] [IsScalarTower R S T] (a…
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
-/
theorem map_mem_span_algebraMap_image {S T : Type*} [CommSemiring S] [Semiring T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (x : S) (a : Set S)
    (hx : x ∈ Submodule.span R a) : algebraMap S T x ∈ Submodule.span R (algebraMap S T '' a) := by
  rw [span_algebraMap_image_of_tower, mem_map]
  exact ⟨x, hx, rfl⟩

end Algebra

end Submodule

end Semiring

section Ring

namespace Algebra

variable [CommSemiring R] [Semiring A] [IsDomain A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommGroup M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

/-
**Algebra.lsmul_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：lsmul_injective [Module.IsTorsionFree A M] {x : A} (hx : x != 0) : Functio
n.Injective (lsmul R B M x)
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
theorem lsmul_injective [Module.IsTorsionFree A M] {x : A} (hx : x ≠ 0) :
    Function.Injective (lsmul R B M x) :=
  smul_right_injective M hx

end Algebra

end Ring

section Algebra.algebraMapSubmonoid

@[simp]
/-
**Algebra.algebraMapSubmonoid_map_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.algebraMapSubmonoid_map_map {R A B : Type*} [CommSemiring R] [Comm
Semiring A] [Algebra R A] (M : Submonoid R) [Semiring B] [Algebra R B] [Algebra 
A B] [IsScalarTower R A B] : algebraMapSubmonoid B (algebraMapSubmonoid A M) = a
lgebraMapSubmonoid B M
参数：M : Submonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.algebraMapSubmonoid_map_eq`：algebraMapSubmonoid_map_eq (f : A ->
ₐ[R] B) : (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M
-/
theorem Algebra.algebraMapSubmonoid_map_map {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (M : Submonoid R) [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    algebraMapSubmonoid B (algebraMapSubmonoid A M) = algebraMapSubmonoid B M :=
  algebraMapSubmonoid_map_eq _ (IsScalarTower.toAlgHom R A B)

end Algebra.algebraMapSubmonoid

