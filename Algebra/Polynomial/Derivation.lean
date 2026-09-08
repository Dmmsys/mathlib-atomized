/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Richard M. Hill
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Derivation.Basic
/-!
# Derivations of univariate polynomials

In this file we prove that an `R`-derivation of `Polynomial R` is determined by its value on `X`.
We also provide a constructor `Polynomial.mkDerivation` that
builds a derivation from its value on `X`, and a linear equivalence
`Polynomial.mkDerivationEquiv` between `A` and `Derivation (Polynomial R) A`.
-/

@[expose] public section

noncomputable section

namespace Polynomial

section CommSemiring

variable {R A : Type*} [CommSemiring R]

set_option backward.isDefEq.respectTransparency false in
/-- `Polynomial.derivative` as a derivation. -/
@[simps]
/-
**Polynomial.derivative'** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：derivative' : Derivation R R[X] R[X] where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.derivative` as a derivation.
-/
def derivative' : Derivation R R[X] R[X] where
  toFun := derivative
  map_add' _ _ := derivative_add
  map_smul' := derivative_smul
  map_one_eq_zero' := derivative_one
  leibniz' f g := by simp [mul_comm, add_comm, derivative_mul]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

@[simp]
/-
**Polynomial.derivation_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：derivation_C (D : Derivation R R[X] A) (a : R) : D (C a) = 0
参数：D : Derivation R R[X] A；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.map_algebraMap`：map_algebraMap : D (algebraMap R A r) = 0
-/
theorem derivation_C (D : Derivation R R[X] A) (a : R) : D (C a) = 0 :=
  D.map_algebraMap a

@[simp]
/-
**Polynomial.C_smul_derivation_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_smul_derivation_apply (D : Derivation R R[X] A) (a : R) (f : R[X]) : C a
 • D f = a • D f
参数：D : Derivation R R[X] A；a : R；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `Polynomial.derivation_C`：derivation_C (D : Derivation R R[X] A) (a : R) 
: D (C a) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用定理 `Derivation.map_smul`：map_smul : D (r • a) = r • D a
-/
theorem C_smul_derivation_apply (D : Derivation R R[X] A) (a : R) (f : R[X]) :
    C a • D f = a • D f := by
  have : C a • D f = D (C a * f) := by simp
  rw [this, C_mul', D.map_smul]

@[ext]
/-
**Polynomial.derivation_ext** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：derivation_ext {D₁ D₂ : Derivation R R[X] A} (h : D₁ X = D₂ X) : D₁ = D₂
参数：h : D₁ X = D₂ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `Derivation.eqOn_adjoin`：eqOn_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) :
 Set.EqOn D1 D2 (adjoin R s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eqOn_singleton`：eqOn_singleton : Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.adjoin_X`：∀ {R : Type u} [inst : CommSemiring R], R[Polynomia
l.X] = ⊤
-/
theorem derivation_ext {D₁ D₂ : Derivation R R[X] A} (h : D₁ X = D₂ X) : D₁ = D₂ :=
  Derivation.ext fun f => Derivation.eqOn_adjoin (Set.eqOn_singleton.2 h) <| by
    simp only [adjoin_X, Algebra.coe_top, Set.mem_univ]

variable [IsScalarTower R (Polynomial R) A]
variable (R)

/-- The derivation on `R[X]` that takes the value `a` on `X`. -/
/-
**Polynomial.mkDerivation** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：mkDerivation : A ->ₗ[R] Derivation R R[X] A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivation on `R[X]` that takes the value `a` on `X`.
-/
def mkDerivation : A →ₗ[R] Derivation R R[X] A where
  toFun := fun a ↦ (LinearMap.toSpanSingleton R[X] A a).compDer derivative'
  map_add' := fun a b ↦ by ext; simp
  map_smul' := fun t a ↦ by ext; simp
/-
**Polynomial.mkDerivation_apply** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mkDerivation_apply (a : A) (f : R[X]) : mkDerivation R a f = derivative f 
• a
参数：a : A；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma mkDerivation_apply (a : A) (f : R[X]) :
    mkDerivation R a f = derivative f • a := by
  rfl

@[simp]
/-
**Polynomial.mkDerivation_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mkDerivation_X (a : A) : mkDerivation R a X = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.mkDerivation_apply`：mkDerivation_apply (a : A) (f : R[X]) : m
kDerivation R a f = derivative f • a
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mkDerivation_X (a : A) : mkDerivation R a X = a := by simp [mkDerivation_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.mkDerivation_one_eq_derivative'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：mkDerivation_one_eq_derivative' : mkDerivation R (1 : R[X]) = derivative'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.derivation_ext`：derivation_ext {D₁ D₂ : Derivation R R[X] A} 
(h : D₁ X = D₂ X) : D₁ = D₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mkDerivation_X`：mkDerivation_X (a : A) : mkDerivation R a X =
 a
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mkDerivation_one_eq_derivative' : mkDerivation R (1 : R[X]) = derivative' := by
  ext : 1
  simp [derivative']
/-
**Polynomial.mkDerivation_one_eq_derivative** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：mkDerivation_one_eq_derivative (f : R[X]) : mkDerivation R (1 : R[X]) f = 
derivative f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.mkDerivation_one_eq_derivative'`：mkDerivation_one_eq_derivati
ve' : mkDerivation R (1 : R[X]) = derivative'
-/
lemma mkDerivation_one_eq_derivative (f : R[X]) : mkDerivation R (1 : R[X]) f = derivative f := by
  rw [mkDerivation_one_eq_derivative']
  rfl

/-- `Polynomial.mkDerivation` as a linear equivalence. -/
/-
**Polynomial.mkDerivationEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：mkDerivationEquiv : A ≃ₗ[R] Derivation R R[X] A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mkDerivation_X`：mkDerivation_X (a : A) : mkDerivation R a X =
 a

--- 原说明 ---
`Polynomial.mkDerivation` as a linear equivalence.
-/
def mkDerivationEquiv : A ≃ₗ[R] Derivation R R[X] A :=
  LinearEquiv.symm <|
    { invFun := mkDerivation R
      toFun := fun D => D X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => derivation_ext <| mkDerivation_X _ _
      right_inv := fun _ => mkDerivation_X _ _ }
/-
**Polynomial.mkDerivationEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid A] [inst_2 : _root_.Module R A]   [inst_3 : _root_.Module (Polynomial R) A
] [inst_4 : IsScalarTower R (Polynomial R) A] (a : A),   (Polynomial.mkDerivatio
nEquiv R) a = (Polynomial.mkDerivation R) a
参数：R : Type u_1；Polynomial R；Polynomial R；a : A；Polynomial.mkDerivationEquiv R；P
olynomial.mkDerivation R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] lemma mkDerivationEquiv_apply (a : A) :
    mkDerivationEquiv R a = mkDerivation R a := by
  rfl
/-
**Polynomial.mkDerivationEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid A] [inst_2 : _root_.Module R A]   [inst_3 : _root_.Module (Polynomial R) A
] [inst_4 : IsScalarTower R (Polynomial R) A]   (D : Derivation R (Polynomial R)
 A), (Polynomial.mkDerivationEquiv R).symm D = D Polynomial.X
参数：R : Type u_1；Polynomial R；Polynomial R；D : Derivation R (Polynomial R) A；Poly
nomial.mkDerivationEquiv R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] lemma mkDerivationEquiv_symm_apply (D : Derivation R R[X] A) :
    (mkDerivationEquiv R).symm D = D X := rfl

end CommSemiring
end Polynomial

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

open Polynomial Module

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
For a derivation `d : A → M` and an element `a : A`, `d.compAEval a` is the
derivation of `R[X]` which takes a polynomial `f` to `d(aeval a f)`.

This derivation takes values in `Module.AEval R M a`, which is `M`, regarded as an
`R[X]`-module, with the action of a polynomial `f` defined by `f • m = (aeval a f) • m`.
-/
/-
Note: `compAEval` is not defined using `Derivation.compAlgebraMap`.
This because `A` is not an `R[X]` algebra and it would be messy to create an algebra instance
within the definition.
-/
@[simps]
/-
**Derivation.compAEval** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：compAEval : Derivation R R[X] AEval R M a where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: `compAEval` is not defined using `Derivation.compAlgebraMap`.
This because `A` is not an `R[X]` algebra and it would be messy to create an alg
ebra instance
within the definition.
-/
def compAEval : Derivation R R[X] <| AEval R M a where
  toFun f          := AEval.of R M a (d (aeval a f))
  map_add'         := by simp
  map_smul'        := by simp
  leibniz'         := by simp [AEval.of_aeval_smul, -Derivation.map_aeval]
  map_one_eq_zero' := by simp

/--
A form of the chain rule: if `f` is a polynomial over `R`
and `d : A → M` is an `R`-derivation then for all `a : A` we have
$$ d(f(a)) = f' (a) d a. $$
The equation is in the `R[X]`-module `Module.AEval R M a`.
For the same equation in `M`, see `Derivation.compAEval_eq`.
-/
/-
**Derivation.compAEval_eq** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：compAEval_eq (d : Derivation R A M) (f : R[X]) : d.compAEval a f = derivat
ive f • (AEval.of R M a (d a))
参数：d : Derivation R A M；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Derivation.compAEval_apply`：∀ {R : Type u_1} {A : Type u_2} {M : Type u_
3} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A]   [i
nst_3 : AddCommM…
· 使用定理 `Derivation.map_aeval`：map_aeval (P : R[X]) (x : A) : D (aeval x P) = aev
al x (derivative P) • D x
· 使用引理 `Module.AEval.of_aeval_smul`：of_aeval_smul (f : R[X]) (m : M) : of R M a 
(aeval a f • m) = f • of R M a m

--- 原说明 ---
A form of the chain rule: if `f` is a polynomial over `R`
and `d : A → M` is an `R`-derivation then for all `a : A` we have
$$ d(f(a)) = f' (a) d a. $$
The equation is in the `R[X]`-module `Module.AEval R M a`.
For the same equation in `M`, see `Derivation.compAEval_eq`.
-/
theorem compAEval_eq (d : Derivation R A M) (f : R[X]) :
    d.compAEval a f = derivative f • (AEval.of R M a (d a)) := by
  simpa using AEval.of_aeval_smul _ _ _

/--
A form of the chain rule: if `f` is a polynomial over `R`
and `d : A → M` is an `R`-derivation then for all `a : A` we have
$$ d(f(a)) = f' (a) d a. $$
The equation is in `M`. For the same equation in `Module.AEval R M a`,
see `Derivation.compAEval_eq`.
-/
/-
**Derivation.comp_aeval_eq** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：comp_aeval_eq (d : Derivation R A M) (f : R[X]) : d (aeval a f) = aeval a 
(derivative f) • d a
参数：d : Derivation R A M；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Derivation.compAEval_eq`：compAEval_eq (d : Derivation R A M) (f : R[X]) 
: d.compAEval a f = derivative f • (AEval.of R M a (d a))
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A form of the chain rule: if `f` is a polynomial over `R`
and `d : A → M` is an `R`-derivation then for all `a : A` we have
$$ d(f(a)) = f' (a) d a. $$
The equation is in `M`. For the same equation in `Module.AEval R M a`,
see `Derivation.compAEval_eq`.
-/
theorem comp_aeval_eq (d : Derivation R A M) (f : R[X]) :
    d (aeval a f) = aeval a (derivative f) • d a :=
  calc
    _ = (AEval.of R M a).symm (d.compAEval a f) := rfl
    _ = _ := by simp [-compAEval_apply, compAEval_eq]

end Derivation

