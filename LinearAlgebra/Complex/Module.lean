/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`SMul`, `MulAction`, `DistribMulAction`, `Module`, `Algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite-dimensional complex vector space is a finite-dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines bundled versions of four standard maps (respectively, the real part, the imaginary
part, the embedding of `ℝ` in `ℂ`, and the complex conjugate):

* `Complex.reLm` (`ℝ`-linear map);
* `Complex.imLm` (`ℝ`-linear map);
* `Complex.ofRealAm` (`ℝ`-algebra (homo)morphism);
* `Complex.conjAe` (`ℝ`-algebra equivalence).

It also provides a universal property of the complex numbers `Complex.lift`, which constructs a
`ℂ →ₐ[ℝ] A` into any `ℝ`-algebra `A` given a square root of `-1`.

In addition, this file provides a decomposition into `realPart` and `imaginaryPart` for any
element of a `StarModule` over `ℂ`.

## Notation

* `ℜ` and `ℑ` for the `realPart` and `imaginaryPart`, respectively, in the locale
  `ComplexStarModule`.
-/

@[expose] public section

assert_not_exists NNReal
namespace Complex

open ComplexConjugate

open scoped Complex.SMul

variable {R : Type*} {S : Type*}

attribute [local ext] Complex.ext


/- The priority of the following instances has been manually lowered, as when they don't apply
they lead Lean to a very costly path, and most often they don't apply (most actions on `ℂ` don't
come from actions on `ℝ`). See https://github.com/leanprover-community/mathlib4/pull/11980 -/

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) [SMul R ℝ] [SMul S ℝ] [SMulCommClass R S ℝ] : SMulCommClass R S ℂ where
  smul_comm r s x := by ext <;> simp [smul_re, smul_im, smul_comm]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) [SMul R S] [SMul R ℝ] [SMul S ℝ] [IsScalarTower R S ℝ] :
    IsScalarTower R S ℂ where
  smul_assoc r s x := by ext <;> simp [smul_re, smul_im, smul_assoc]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) [SMul R ℝ] [SMul Rᵐᵒᵖ ℝ] [IsCentralScalar R ℝ] :
    IsCentralScalar R ℂ where
  op_smul_eq_smul r x := by ext <;> simp [smul_re, smul_im, op_smul_eq_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) mulAction [Monoid R] [MulAction R ℝ] : MulAction R ℂ where
  one_smul x := by ext <;> simp [smul_re, smul_im, one_smul]
  mul_smul r s x := by ext <;> simp [smul_re, smul_im, mul_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) distribSMul [DistribSMul R ℝ] : DistribSMul R ℂ where
  smul_add r x y := by ext <;> simp [smul_re, smul_im, smul_add]
  smul_zero r := by ext <;> simp [smul_re, smul_im, smul_zero]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) [Semiring R] [DistribMulAction R ℝ] : DistribMulAction R ℂ :=
  { Complex.distribSMul, Complex.mulAction with }

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instModule [Semiring R] [Module R ℝ] : Module R ℂ where
  add_smul r s x := by ext <;> simp [smul_re, smul_im, add_smul]
  zero_smul r := by ext <;> simp [smul_re, smul_im, zero_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 95) instAlgebraOfReal [CommSemiring R] [Algebra R ℝ] : Algebra R ℂ where
  algebraMap := Complex.ofRealHom.comp (algebraMap R ℝ)
  smul_def' := fun r x => by ext <;> simp [smul_re, smul_im, Algebra.smul_def]
  commutes' := fun r ⟨xr, xi⟩ => by ext <;> simp [Algebra.commutes]
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarModule ℝ ℂ :=
  ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_ofReal]⟩

@[simp]
/-
**Complex.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：coe_algebraMap : (algebraMap Real Complex : Real -> Complex) = ((↑) : Real
 -> Complex)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMap : (algebraMap ℝ ℂ : ℝ → ℂ) = ((↑) : ℝ → ℂ) :=
  rfl
/-
**Complex.** 是 Mathlib 中的一个示例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (Semiring.toNatAlgebra : Algebra ℕ ℂ) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl
/-
**Complex.** 是 Mathlib 中的一个示例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (Ring.toIntAlgebra ℂ : Algebra ℤ ℂ) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl
/-
**Complex.** 是 Mathlib 中的一个示例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Module.restrictScalars ℝ ℂ ℂ = Complex.instModule := by
  with_reducible_and_instances rfl

section

variable {A : Type*} [Semiring A] [Algebra ℝ A]

/-- We need this lemma since `Complex.coe_algebraMap` diverts the simp-normal form away from
`AlgHom.commutes`. -/
@[simp]
/-
**Complex._root_.AlgHom.map_coe_real_complex** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We need this lemma since `Complex.coe_algebraMap` diverts the simp-normal form a
way from
`AlgHom.commutes`.
-/
theorem _root_.AlgHom.map_coe_real_complex (f : ℂ →ₐ[ℝ] A) (x : ℝ) : f x = algebraMap ℝ A x :=
  f.commutes x

/-- Two `ℝ`-algebra homomorphisms from `ℂ` are equal if they agree on `Complex.I`. -/
@[ext]
/-
**Complex.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：algHom_ext ⦃f g : Complex ->ₐ[Real] A⦄ (h : f I = g I) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mk_eq_add_mul_I`：mk_eq_add_mul_I (a b : Real) : Complex.mk a b =
 a + b * I
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgHom.map_coe_real_complex`：∀ {A : Type u_3} [inst : Semiring A] [inst_
1 : Algebra ℝ A] (f : ℂ →ₐ[ℝ] A) (x : ℝ), f ↑x = (algebraMap ℝ A) x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two `ℝ`-algebra homomorphisms from `ℂ` are equal if they agree on `Complex.I`.
-/
theorem algHom_ext ⦃f g : ℂ →ₐ[ℝ] A⦄ (h : f I = g I) : f = g := by
  ext ⟨x, y⟩
  simp only [mk_eq_add_mul_I, map_add, AlgHom.map_coe_real_complex, map_mul, h]

end

open Module Submodule

/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
/-
**Complex.basisOneI** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：basisOneI : Basis (Fin 2) Real Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℂ` has a basis over `ℝ` given by `1` and `I`.
-/
noncomputable def basisOneI : Basis (Fin 2) ℝ ℂ :=
  .ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
      right_inv := fun c => by
        ext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      map_smul' := fun c z => by simp }

@[simp]
/-
**Complex.coe_basisOneI_repr** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：coe_basisOneI_repr (z : Complex) : ⇑(basisOneI.repr z) = ![z.re, z.im]
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_basisOneI_repr (z : ℂ) : ⇑(basisOneI.repr z) = ![z.re, z.im] :=
  rfl

@[simp]
/-
**Complex.coe_basisOneI** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：coe_basisOneI : ⇑basisOneI = ![1, I]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem coe_basisOneI : ⇑basisOneI = ![1, I] :=
  funext fun i =>
    Basis.apply_eq_iff.mpr <|
      Finsupp.ext fun j => by
        fin_cases i <;> fin_cases j <;> simp

end Complex

/-- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Register as an instance (with low priority) the fact that a complex vector space
 is also a real
vector space.
-/
instance (priority := 900) Module.complexToReal (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module ℝ E :=
  .restrictScalars ℝ ℂ E

/-- Register as an instance (with low priority) the fact that a complex algebra is also a real
algebra. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Register as an instance (with low priority) the fact that a complex algebra is a
lso a real
algebra.
-/
instance (priority := 900) Algebra.complexToReal {A : Type*} [Semiring A] [Algebra ℂ A] :
    Algebra ℝ A :=
  .restrictScalars ℝ ℂ A

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Prod.algebra ℝ ℂ ℂ = (Prod.algebra ℂ ℂ ℂ).complexToReal := rfl

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {ι : Type*} [Fintype ι] :
    Pi.algebra (R := ℝ) ι (fun _ ↦ ℂ) = (Pi.algebra (R := ℂ) ι (fun _ ↦ ℂ)).complexToReal :=
  rfl
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {A : Type*} [Ring A] [inst : Algebra ℂ A] :
    (inst.complexToReal).toModule = (inst.toModule).complexToReal := by
  with_reducible_and_instances rfl

@[simp, norm_cast]
/-
**Complex.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.coe_smul {E : Type*} [AddCommGroup E] [Module Complex E] (x : Real
) (y : E) : (x : Complex) • y = x • y
参数：x : Real；y : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Complex.coe_smul {E : Type*} [AddCommGroup E] [Module ℂ E] (x : ℝ) (y : E) :
    (x : ℂ) • y = x • y :=
  rfl

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` commutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the action of `M`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` c
ommutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the
 action of `M`.
-/
instance (priority := 900) SMulCommClass.complexToReal {M E : Type*} [AddCommGroup E] [Module ℂ E]
    [SMul M E] [SMulCommClass ℂ M E] : SMulCommClass ℝ M E where
  smul_comm r _ _ := smul_comm (r : ℂ) _ _

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` associates with
another scalar action of `M` on `E` whenever the action of `ℂ` associates with the action of `M`. -/
/-
**IsScalarTower.complexToReal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsScalarTower.complexToReal {M E : Type*} [AddCommGroup M] [Module Complex
 M] [AddCommGroup E] [Module Complex E] [SMul M E] [IsScalarTower Complex M E] :
 IsScalarTower Real M E where smul_assoc r _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.smul_assoc`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_1
1} {inst : SMul M N} {inst_1 : SMul N α} {inst_2 : SMul M α}   [self : IsScalarT
ower M N α] (x…

--- 原说明 ---
The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` a
ssociates with
another scalar action of `M` on `E` whenever the action of `ℂ` associates with t
he action of `M`.
-/
instance IsScalarTower.complexToReal {M E : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup E]
    [Module ℂ E] [SMul M E] [IsScalarTower ℂ M E] : IsScalarTower ℝ M E where
  smul_assoc r _ _ := smul_assoc (r : ℂ) _ _

-- check that the following instance is implied by the one above.
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (E : Type*) [AddCommGroup E] [Module ℂ E] : IsScalarTower ℝ ℂ E := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) StarModule.complexToReal {E : Type*} [AddCommGroup E] [Star E]
    [Module ℂ E] [StarModule ℂ E] : StarModule ℝ E :=
  ⟨fun r a => by rw [← smul_one_smul ℂ r a, star_smul, star_smul, star_one, smul_one_smul]⟩

namespace Complex

open ComplexConjugate

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
/-
**Complex.reLm** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：reLm : Complex ->ₗ[Real] Real where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re

--- 原说明 ---
Linear map version of the real part function, from `ℂ` to `ℝ`.
-/
def reLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.re
  map_add' := add_re
  map_smul' := by simp

@[simp]
/-
**Complex.reLm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：reLm_coe : ⇑reLm = re
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reLm_coe : ⇑reLm = re :=
  rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
/-
**Complex.imLm** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：imLm : Complex ->ₗ[Real] Real where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.add_im`：add_im (z w : Complex) : (z + w).im = z.im + w.im

--- 原说明 ---
Linear map version of the imaginary part function, from `ℂ` to `ℝ`.
-/
def imLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.im
  map_add' := add_im
  map_smul' := by simp

@[simp]
/-
**Complex.imLm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：imLm_coe : ⇑imLm = im
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imLm_coe : ⇑imLm = im :=
  rfl

/-- `ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`. -/
/-
**Complex.ofRealAm** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ofRealAm : Real ->ₐ[Real] Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`.
-/
def ofRealAm : ℝ →ₐ[ℝ] ℂ :=
  Algebra.ofId ℝ ℂ

@[simp]
/-
**Complex.ofRealAm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofRealAm_coe : ⇑ofRealAm = ((↑) : Real -> Complex)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRealAm_coe : ⇑ofRealAm = ((↑) : ℝ → ℂ) :=
  rfl

/-- `ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to `ℂ` -/
/-
**Complex.conjAe** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：conjAe : Complex ≃ₐ[Real] Complex
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r

--- 原说明 ---
`ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to 
`ℂ`
-/
def conjAe : ℂ ≃ₐ[ℝ] ℂ :=
  { conj with
    invFun := conj
    left_inv := star_star
    right_inv := star_star
    commutes' := conj_ofReal }

@[simp]
/-
**Complex.conjAe_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conjAe_coe : ⇑conjAe = conj
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjAe_coe : ⇑conjAe = conj :=
  rfl

/-- The matrix representation of `conjAe`. -/
@[simp]
/-
**Complex.toMatrix_conjAe** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：toMatrix_conjAe : conjAe.toLinearEquiv.toLinearMap.toMatrix basisOneI basi
sOneI = !![1, 0; 0, -1]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Complex.coe_basisOneI`：coe_basisOneI : ⇑basisOneI = ![1, I]
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
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The matrix representation of `conjAe`.
-/
theorem toMatrix_conjAe :
    conjAe.toLinearEquiv.toLinearMap.toMatrix basisOneI basisOneI = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

/-- The identity and the complex conjugation are the only two `ℝ`-algebra homomorphisms of `ℂ`. -/
/-
**Complex.real_algHom_eq_id_or_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：real_algHom_eq_id_or_conj (f : Complex ->ₐ[Real] Complex) : f = AlgHom.id 
Real Complex ∨ f = conjAe
参数：f : Complex ->ₐ[Real] Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Complex.algHom_ext`：algHom_ext ⦃f g : Complex ->ₐ[Real] A⦄ (h : f I = g 
I) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用引理 `eq_or_eq_neg_of_sq_eq_sq`：eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b
 ^ 2 -> a = b ∨ a = -b
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…

--- 原说明 ---
The identity and the complex conjugation are the only two `ℝ`-algebra homomorphi
sms of `ℂ`.
-/
theorem real_algHom_eq_id_or_conj (f : ℂ →ₐ[ℝ] ℂ) : f = AlgHom.id ℝ ℂ ∨ f = conjAe := by
  refine
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp ?_ ?_ <;>
    refine fun h => algHom_ext ?_
  exacts [h, conj_I.symm ▸ h]

/-- The natural `LinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
/-
**Complex.equivRealProdLm** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：equivRealProdLm : Complex ≃ₗ[Real] Real × Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `LinearEquiv` from `ℂ` to `ℝ × ℝ`.
-/
def equivRealProdLm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  { equivRealProdAddHom with
    map_smul' := fun r c => by simp }
/-
**Complex.equivRealProdLm_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：equivRealProdLm_symm_apply (p : Real × Real) : Complex.equivRealProdLm.sym
m p = p.1 + p.2 * Complex.I
参数：p : Real × Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.equivRealProd_symm_apply`：equivRealProd_symm_apply (p : Real × R
eal) : equivRealProd.symm p = p.1 + p.2 * I
-/
theorem equivRealProdLm_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdLm.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

section lift

variable {A : Type*} [Ring A] [Algebra ℝ A]

open Algebra

/-- There is an `AlgHom` from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `Complex.lift` for this as an equiv. -/
/-
**Complex.liftAux** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：liftAux (I' : A) (hf : I' * I' = -1) : Complex ->ₐ[Real] A
参数：I' : A；hf : I' * I' = -1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is an `AlgHom` from `ℂ` to any `ℝ`-algebra with an element that squares to
 `-1`.

See `Complex.lift` for this as an equiv.
-/
def liftAux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
  AlgHom.ofLinearMap
    ((Algebra.linearMap ℝ A).comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap ℝ A 1 + (0 : ℝ) • I' = 1 by rw [map_one, zero_smul, add_zero]) ?_
where finally
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
  rw [mk_mul_mk]
  change
    algebraMap ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' =
      (algebraMap ℝ A x₁ + y₁ • I') * (algebraMap ℝ A x₂ + y₂ • I')
  rw [add_mul, mul_add, mul_add, add_comm _ (y₁ • I' * y₂ • I'), add_add_add_comm]
  congr 1
  -- equate "real" and "imaginary" parts
  · rw [smul_mul_smul_comm, hf, smul_neg, ← algebraMap_eq_smul_one, ← sub_eq_add_neg,
      ← map_mul, ← map_sub]
  · rw [smul_def, smul_def, smul_def, ← right_comm _ x₂,
      ← mul_assoc, ← add_mul, ← map_mul, ← map_mul, ← map_add]

@[simp]
/-
**Complex.liftAux_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：liftAux_apply (I' : A) (hI') (z : Complex) : liftAux I' hI' z = algebraMap
 Real A z.re + z.im • I'
参数：I' : A；hI'；z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAux_apply (I' : A) (hI') (z : ℂ) : liftAux I' hI' z = algebraMap ℝ A z.re + z.im • I' :=
  rfl
/-
**Complex.liftAux_apply_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：liftAux_apply_I (I' : A) (hI') : liftAux I' hI' I = I'
参数：I' : A；hI'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftAux_apply_I (I' : A) (hI') : liftAux I' hI' I = I' := by simp

@[simp]
/-
**Complex.adjoin_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：adjoin_I : Real[I] = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Complex.coe_algebraMap`：coe_algebraMap : (algebraMap Real Complex : Real
 -> Complex) = ((↑) : Real -> Complex)
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoin_I : ℝ[I] = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.re_add_im, ← smul_eq_mul, ← Complex.coe_algebraMap]
  exact add_mem (algebraMap_mem _ _) (Subalgebra.smul_mem _ (subset_adjoin <| by simp) _)

@[simp]
/-
**Complex.range_liftAux** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：range_liftAux (I' : A) (hI') : (liftAux I' hI').range = Real[I']
参数：I' : A；hI'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.liftAux_apply_I`：liftAux_apply_I (I' : A) (hI') : liftAux I' hI'
 I = I'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_liftAux (I' : A) (hI') : (liftAux I' hI').range = ℝ[I'] := by
  simp_rw [← Algebra.map_top, ← adjoin_I, AlgHom.map_adjoin, Set.image_singleton, liftAux_apply_I]

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `Quaternion`s.

This isomorphism is named to match the very similar `Zsqrtd.lift`. -/
@[simps +simpRhs]
/-
**Complex.lift** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：lift : { I' : A // I' * I' = -1 } ≃ (Complex ->ₐ[Real] A) where toFun I'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for 
every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `Quaternion`s.

This isomorphism is named to match the very similar `Zsqrtd.lift`.
-/
def lift : { I' : A // I' * I' = -1 } ≃ (ℂ →ₐ[ℝ] A) where
  toFun I' := liftAux I' I'.prop
  invFun F := ⟨F I, by rw [← map_mul, I_mul_I, map_neg, map_one]⟩
  left_inv I' := Subtype.ext <| liftAux_apply_I (I' : A) I'.prop
  right_inv _ := algHom_ext <| liftAux_apply_I _ _

-- When applied to `Complex.I` itself, `lift` is the identity.
@[simp]
/-
**Complex.liftAux_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：liftAux_I : liftAux I I_mul_I = AlgHom.id Real Complex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.algHom_ext`：algHom_ext ⦃f g : Complex ->ₐ[Real] A⦄ (h : f I = g 
I) : f = g
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用定理 `Complex.liftAux_apply_I`：liftAux_apply_I (I' : A) (hI') : liftAux I' hI'
 I = I'
-/
theorem liftAux_I : liftAux I I_mul_I = AlgHom.id ℝ ℂ :=
  algHom_ext <| liftAux_apply_I _ _

-- When applied to `-Complex.I`, `lift` is conjugation, `conj`.
@[simp]
/-
**Complex.liftAux_neg_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：liftAux_neg_I : liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conjAe
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.algHom_ext`：algHom_ext ⦃f g : Complex ->ₐ[Real] A⦄ (h : f I = g 
I) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用定理 `Complex.liftAux_apply_I`：liftAux_apply_I (I' : A) (hI') : liftAux I' hI'
 I = I'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
-/
theorem liftAux_neg_I : liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conjAe :=
  algHom_ext <| (liftAux_apply_I _ _).trans conj_I.symm

end lift

end Complex

section RealImaginaryPart

open Complex

variable {A : Type*}

section AddCommGroup

variable [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-
**Complex.I_mem_skewAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.I_mem_skewAdjoint : I in skewAdjoint Complex
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Complex.I_mem_skewAdjoint : I ∈ skewAdjoint ℂ := by simp [skewAdjoint.mem_iff]
/-
**Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `Co
mplex`。
形式化陈述：∀ {A : Type u_1} [inst : AddCommGroup A] [inst_1 : _root_.Module ℂ A] [ins
t_2 : StarAddMonoid A] [StarModule ℂ A]   {a : A}, Complex.I • a ∈ skewAdjoint A
 ↔ IsSelfAdjoint a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint {a : A} :
    I • a ∈ skewAdjoint A ↔ IsSelfAdjoint a := by
  simp [skewAdjoint.mem_iff, IsSelfAdjoint, smul_right_inj]
/-
**Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `Co
mplex`。
形式化陈述：∀ {A : Type u_1} [inst : AddCommGroup A] [inst_1 : _root_.Module ℂ A] [ins
t_2 : StarAddMonoid A] [StarModule ℂ A]   {a : A}, IsSelfAdjoint (Complex.I • a)
 ↔ a ∈ skewAdjoint A
参数：Complex.I • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint {a : A} :
    IsSelfAdjoint (I • a) ↔ a ∈ skewAdjoint A := by
  simp [← I_smul_mem_skewAdjoint_iff_isSelfAdjoint, smul_smul]

/-- Create a `selfAdjoint` element from a `skewAdjoint` element by multiplying by the scalar
`-Complex.I`. -/
@[simps]
/-
**skewAdjoint.negISMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjoint.negISMul : skewAdjoint A ->ₗ[Real] selfAdjoint A where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ

--- 原说明 ---
Create a `selfAdjoint` element from a `skewAdjoint` element by multiplying by th
e scalar
`-Complex.I`.
-/
def skewAdjoint.negISMul : skewAdjoint A →ₗ[ℝ] selfAdjoint A where
  toFun a := ⟨-I • ↑a, by simp [selfAdjoint.mem_iff]⟩
  map_add' a b := by simp
  map_smul' a b := by ext; simp [smul_comm I]
/-
**skewAdjoint.I_smul_neg_I** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：skewAdjoint.I_smul_neg_I (a : skewAdjoint A) : I • (skewAdjoint.negISMul a
 : A) = a
参数：a : skewAdjoint A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `skewAdjoint.negISMul_apply_coe`：∀ {A : Type u_1} [inst : AddCommGroup A]
 [inst_1 : _root_.Module ℂ A] [inst_2 : StarAddMonoid A]   [inst_3 : StarModule 
ℂ A] (a : ↥(skewAdjo…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem skewAdjoint.I_smul_neg_I (a : skewAdjoint A) : I • (skewAdjoint.negISMul a : A) = a := by
  simp [smul_smul]

/-- The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map. This is just
`selfAdjointPart ℝ`, but we provide it as a separate definition in order to link it with lemmas
concerning the `imaginaryPart`, which doesn't exist in star modules over other rings. -/
/-
**realPart** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：realPart : A ->ₗ[Real] selfAdjoint A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R

--- 原说明 ---
The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map
. This is just
`selfAdjointPart ℝ`, but we provide it as a separate definition in order to link
 it with lemmas
concerning the `imaginaryPart`, which doesn't exist in star modules over other r
ings.
-/
noncomputable def realPart : A →ₗ[ℝ] selfAdjoint A :=
  selfAdjointPart ℝ

/-- The imaginary part `ℑ a` of an element `a` of a star module over `ℂ`, as a linear map into the
self adjoint elements. In a general star module, we have a decomposition into the `selfAdjoint`
and `skewAdjoint` parts, but in a star module over `ℂ` we have
`realPart_add_I_smul_imaginaryPart`, which allows us to decompose into a linear combination of
`selfAdjoint`s. -/
/-
**imaginaryPart** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：imaginaryPart : A ->ₗ[Real] selfAdjoint A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R

--- 原说明 ---
The imaginary part `ℑ a` of an element `a` of a star module over `ℂ`, as a linea
r map into the
self adjoint elements. In a general star module, we have a decomposition into th
e `selfAdjoint`
and `skewAdjoint` parts, but in a star module over `ℂ` we have
`realPart_add_I_smul_imaginaryPart`, which allows us to decompose into a linear 
combination of
`selfAdjoint`s.
-/
noncomputable def imaginaryPart : A →ₗ[ℝ] selfAdjoint A :=
  skewAdjoint.negISMul.comp (skewAdjointPart ℝ)

@[inherit_doc]
scoped[ComplexStarModule] notation "ℜ" => realPart
@[inherit_doc]
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

open ComplexStarModule
/-
**realPart_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：realPart_apply_coe (a : A) : (ℜ a : A) = (2 : Real)⁻¹ • (a + star a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `selfAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem realPart_apply_coe (a : A) : (ℜ a : A) = (2 : ℝ)⁻¹ • (a + star a) := by
  simp [realPart]
/-
**imaginaryPart_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -I • (2 : Real)⁻¹ • (a - sta
r a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `skewAdjoint.negISMul_apply_coe`：∀ {A : Type u_1} [inst : AddCommGroup A]
 [inst_1 : _root_.Module ℂ A] [inst_2 : StarAddMonoid A]   [inst_3 : StarModule 
ℂ A] (a : ↥(skewAdjo…
· 使用定理 `skewAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -I • (2 : ℝ)⁻¹ • (a - star a) := by
  simp [imaginaryPart]

/-- The standard decomposition of `ℜ a + Complex.I • ℑ a = a` of an element of a star module over
`ℂ` into a linear combination of self adjoint elements. -/
/-
**realPart_add_I_smul_imaginaryPart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：realPart_add_I_smul_imaginaryPart (a : A) : (ℜ a : A) + I • (ℑ a : A) = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `selfAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `skewAdjoint.negISMul_apply_coe`：∀ {A : Type u_1} [inst : AddCommGroup A]
 [inst_1 : _root_.Module ℂ A] [inst_2 : StarAddMonoid A]   [inst_3 : StarModule 
ℂ A] (a : ↥(skewAdjo…
· 使用定理 `skewAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + c + (b - c) = a + b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The standard decomposition of `ℜ a + Complex.I • ℑ a = a` of an element of a sta
r module over
`ℂ` into a linear combination of self adjoint elements.
-/
theorem realPart_add_I_smul_imaginaryPart (a : A) : (ℜ a : A) + I • (ℑ a : A) = a := by
  simp [realPart, imaginaryPart, smul_smul, ← smul_add, inv_smul_eq_iff₀, two_smul]

@[simp]
/-
**realPart_I_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `realPart_apply_coe`：realPart_apply_coe (a : A) : (ℜ a : A) = (2 : Real)⁻
¹ • (a + star a)
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `imaginaryPart_apply_coe`：imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -
I • (2 : Real)⁻¹ • (a - star a)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a := by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I, sub_eq_add_neg, add_comm]

@[simp]
/-
**imaginaryPart_I_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imaginaryPart_apply_coe`：imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -
I • (2 : Real)⁻¹ • (a - star a)
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `realPart_apply_coe`：realPart_apply_coe (a : A) : (ℜ a : A) = (2 : Real)⁻
¹ • (a + star a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a := by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I (2⁻¹ : ℝ), smul_smul I]
/-
**realPart_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：realPart_smul (z : Complex) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a
参数：z : Complex；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `realPart_I_smul`：realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
theorem realPart_smul (z : ℂ) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a := by
  have := by congrm (ℜ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]
/-
**imaginaryPart_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imaginaryPart_smul (z : Complex) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im •
 ℜ a
参数：z : Complex；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `imaginaryPart_I_smul`：imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a
-/
theorem imaginaryPart_smul (z : ℂ) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im • ℜ a := by
  have := by congrm (ℑ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul]
/-
**skewAdjointPart_eq_I_smul_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：skewAdjointPart_eq_I_smul_imaginaryPart (x : A) : (skewAdjointPart Real x 
: A) = I • (imaginaryPart x : A)
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `skewAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `imaginaryPart_apply_coe`：imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -
I • (2 : Real)⁻¹ • (a - star a)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma skewAdjointPart_eq_I_smul_imaginaryPart (x : A) :
    (skewAdjointPart ℝ x : A) = I • (imaginaryPart x : A) := by
  simp [imaginaryPart_apply_coe, smul_smul]
/-
**imaginaryPart_eq_neg_I_smul_skewAdjointPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imaginaryPart_eq_neg_I_smul_skewAdjointPart (x : A) : (imaginaryPart x : A
) = -I • (skewAdjointPart Real x : A)
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
-/
lemma imaginaryPart_eq_neg_I_smul_skewAdjointPart (x : A) :
    (imaginaryPart x : A) = -I • (skewAdjointPart ℝ x : A) :=
  rfl
/-
**IsSelfAdjoint.coe_realPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.coe_realPart {x : A} (hx : IsSelfAdjoint x) : (ℜ x : A) = x
参数：hx : IsSelfAdjoint x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.coe_selfAdjointPart_apply`：IsSelfAdjoint.coe_selfAdjointPa
rt_apply {x : A} (hx : IsSelfAdjoint x) : (selfAdjointPart R x : A) = x
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
lemma IsSelfAdjoint.coe_realPart {x : A} (hx : IsSelfAdjoint x) :
    (ℜ x : A) = x :=
  hx.coe_selfAdjointPart_apply ℝ

nonrec lemma IsSelfAdjoint.imaginaryPart {x : A} (hx : IsSelfAdjoint x) :
    ℑ x = 0 := by
  rw [imaginaryPart, LinearMap.comp_apply, hx.skewAdjointPart_apply _, map_zero]
/-
**realPart_comp_subtype_selfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：realPart_comp_subtype_selfAdjoint : realPart.comp (selfAdjoint.submodule R
eal A).subtype = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `selfAdjointPart_comp_subtype_selfAdjoint`：selfAdjointPart_comp_subtype_s
elfAdjoint : (selfAdjointPart R).comp (selfAdjoint.submodule R A).subtype = .id
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
lemma realPart_comp_subtype_selfAdjoint :
    realPart.comp (selfAdjoint.submodule ℝ A).subtype = LinearMap.id :=
  selfAdjointPart_comp_subtype_selfAdjoint ℝ

set_option backward.isDefEq.respectTransparency.types false in
/-
**imaginaryPart_comp_subtype_selfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imaginaryPart_comp_subtype_selfAdjoint : imaginaryPart.comp (selfAdjoint.s
ubmodule Real A).subtype = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `skewAdjoint.negISMul_apply_coe`：∀ {A : Type u_1} [inst : AddCommGroup A]
 [inst_1 : _root_.Module ℂ A] [inst_2 : StarAddMonoid A]   [inst_3 : StarModule 
ℂ A] (a : ↥(skewAdjo…
· 使用定理 `skewAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `selfAdjoint.star_val_eq`：star_val_eq {x : selfAdjoint R} : star (x : R) 
= x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma imaginaryPart_comp_subtype_selfAdjoint :
    imaginaryPart.comp (selfAdjoint.submodule ℝ A).subtype = 0 := by
  ext; simp [imaginaryPart]

@[simp]
/-
**selfAdjoint.realPart_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：selfAdjoint.realPart_coe {x : selfAdjoint A} : ℜ (x : A) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用引理 `IsSelfAdjoint.coe_realPart`：IsSelfAdjoint.coe_realPart {x : A} (hx : IsS
elfAdjoint x) : (ℜ x : A) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma selfAdjoint.realPart_coe {x : selfAdjoint A} : ℜ (x : A) = x :=
  Subtype.ext x.property.coe_realPart

@[simp]
/-
**selfAdjoint.imaginaryPart_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：selfAdjoint.imaginaryPart_coe {x : selfAdjoint A} : ℑ (x : A) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.imaginaryPart`：∀ {A : Type u_1} [inst : AddCommGroup A] [i
nst_1 : _root_.Module ℂ A] [inst_2 : StarAddMonoid A]   [inst_3 : StarModule ℂ A
] {x : A}, IsSelf…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma selfAdjoint.imaginaryPart_coe {x : selfAdjoint A} : ℑ (x : A) = 0 :=
  x.property.imaginaryPart
/-
**imaginaryPart_realPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imaginaryPart_realPart {x : A} : ℑ (ℜ x : A) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.imaginaryPart`：∀ {A : Type u_1} [inst : AddCommGroup A] [i
nst_1 : _root_.Module ℂ A] [inst_2 : StarAddMonoid A]   [inst_3 : StarModule ℂ A
] {x : A}, IsSelf…
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma imaginaryPart_realPart {x : A} : ℑ (ℜ x : A) = 0 :=
  (ℜ x).property.imaginaryPart
/-
**imaginaryPart_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imaginaryPart_imaginaryPart {x : A} : ℑ (ℑ x : A) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.imaginaryPart`：∀ {A : Type u_1} [inst : AddCommGroup A] [i
nst_1 : _root_.Module ℂ A] [inst_2 : StarAddMonoid A]   [inst_3 : StarModule ℂ A
] {x : A}, IsSelf…
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma imaginaryPart_imaginaryPart {x : A} : ℑ (ℑ x : A) = 0 :=
  (ℑ x).property.imaginaryPart
/-
**realPart_idem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：realPart_idem {x : A} : ℜ (ℜ x : A) = ℜ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用引理 `IsSelfAdjoint.coe_realPart`：IsSelfAdjoint.coe_realPart {x : A} (hx : IsS
elfAdjoint x) : (ℜ x : A) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma realPart_idem {x : A} : ℜ (ℜ x : A) = ℜ x :=
  Subtype.ext <| (ℜ x).property.coe_realPart
/-
**realPart_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：realPart_imaginaryPart {x : A} : ℜ (ℑ x : A) = ℑ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用引理 `IsSelfAdjoint.coe_realPart`：IsSelfAdjoint.coe_realPart {x : A} (hx : IsS
elfAdjoint x) : (ℜ x : A) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma realPart_imaginaryPart {x : A} : ℜ (ℑ x : A) = ℑ x :=
  Subtype.ext <| (ℑ x).property.coe_realPart
/-
**realPart_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：realPart_surjective : Function.Surjective (realPart (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `IsSelfAdjoint.coe_realPart`：IsSelfAdjoint.coe_realPart {x : A} (hx : IsS
elfAdjoint x) : (ℜ x : A) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma realPart_surjective : Function.Surjective (realPart (A := A)) :=
  fun x ↦ ⟨(x : A), Subtype.ext x.property.coe_realPart⟩
/-
**imaginaryPart_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imaginaryPart_surjective : Function.Surjective (imaginaryPart (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imaginaryPart_I_smul`：imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a
· 使用引理 `IsSelfAdjoint.coe_realPart`：IsSelfAdjoint.coe_realPart {x : A} (hx : IsS
elfAdjoint x) : (ℜ x : A) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma imaginaryPart_surjective : Function.Surjective (imaginaryPart (A := A)) :=
  fun x ↦
    ⟨I • (x : A), Subtype.ext <| by simp only [imaginaryPart_I_smul, x.property.coe_realPart]⟩
/-
**ComplexStarModule.ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ComplexStarModule.ext {x y : A} (h₁ : ℜ x = ℜ y) (h₂ : ℑ x = ℑ y) : x = y
参数：h₁ : ℜ x = ℜ y；h₂ : ℑ x = ℑ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `realPart_add_I_smul_imaginaryPart`：realPart_add_I_smul_imaginaryPart (a 
: A) : (ℜ a : A) + I • (ℑ a : A) = a
-/
lemma ComplexStarModule.ext {x y : A} (h₁ : ℜ x = ℜ y) (h₂ : ℑ x = ℑ y) : x = y := by
  rw [← realPart_add_I_smul_imaginaryPart x, ← realPart_add_I_smul_imaginaryPart y, h₁, h₂]
/-
**ComplexStarModule.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ComplexStarModule.ext_iff {x y : A} : x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y where 
mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用引理 `ComplexStarModule.ext`：ComplexStarModule.ext {x y : A} (h₁ : ℜ x = ℜ y) 
(h₂ : ℑ x = ℑ y) : x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma ComplexStarModule.ext_iff {x y : A} : x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y where
  mp := by grind
  mpr h := ext h.1 h.2

section StarHomClass

variable {B F : Type*} [AddCommGroup B] [Module ℂ B] [StarAddMonoid B] [StarModule ℂ B]
    [FunLike F A B] [StarHomClass F A B] [LinearMapClass F ℂ A B]

/-
**map_realPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_realPart (f : F) (x : A) : f (ℜ x) = ℜ (f x)
参数：f : F；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `realPart_apply_coe`：realPart_apply_coe (a : A) : (ℜ a : A) = (2 : Real)⁻
¹ • (a + star a)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_realPart (f : F) (x : A) : f (ℜ x) = ℜ (f x) := by
  simp [realPart_apply_coe, ← Complex.coe_smul, map_star]
/-
**map_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_imaginaryPart (f : F) (x : A) : f (ℑ x) = ℑ (f x)
参数：f : F；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imaginaryPart_apply_coe`：imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -
I • (2 : Real)⁻¹ • (a - star a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_imaginaryPart (f : F) (x : A) : f (ℑ x) = ℑ (f x) := by
  simp [imaginaryPart_apply_coe, ← Complex.coe_smul, map_star]

end StarHomClass

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ker_imaginaryPart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ker_imaginaryPart : imaginaryPart.ker = selfAdjoint.submodule Real A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `skewAdjoint.negISMul_apply_coe`：∀ {A : Type u_1} [inst : AddCommGroup A]
 [inst_1 : _root_.Module ℂ A] [inst_2 : StarAddMonoid A]   [inst_3 : StarModule 
ℂ A] (a : ↥(skewAdjo…
· 使用定理 `skewAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem ker_imaginaryPart : imaginaryPart.ker = selfAdjoint.submodule ℝ A := by
  ext x
  simp [selfAdjoint.submodule, selfAdjoint.mem_iff, imaginaryPart, Subtype.ext_iff]
  grind

@[simp]
/-
**imaginaryPart_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imaginaryPart_eq_zero_iff {x : A} : ℑ x = 0 ↔ IsSelfAdjoint x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `ker_imaginaryPart`：ker_imaginaryPart : imaginaryPart.ker = selfAdjoint.s
ubmodule Real A
-/
lemma imaginaryPart_eq_zero_iff {x : A} : ℑ x = 0 ↔ IsSelfAdjoint x := by
  simpa [-ker_imaginaryPart] using! SetLike.ext_iff.mp ker_imaginaryPart x

open Submodule
/-
**span_selfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：span_selfAdjoint : span Complex (selfAdjoint A : Set A) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `realPart_add_I_smul_imaginaryPart`：realPart_add_I_smul_imaginaryPart (a 
: A) : (ℜ a : A) + I • (ℑ a : A) = a
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
-/
lemma span_selfAdjoint : span ℂ (selfAdjoint A : Set A) = ⊤ := by
  refine eq_top_iff'.mpr fun x ↦ ?_
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact add_mem (subset_span (ℜ x).property) <|
    SMulMemClass.smul_mem _ <| subset_span (ℑ x).property

end AddCommGroup

open scoped ComplexStarModule

/-- The natural `ℝ`-linear equivalence between `selfAdjoint ℂ` and `ℝ`. -/
@[simps apply symm_apply]
/-
**Complex.selfAdjointEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Complex.selfAdjointEquiv : selfAdjoint Complex ≃ₗ[Real] Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `Complex.instStarModuleReal`：StarModule ℝ ℂ
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r

--- 原说明 ---
The natural `ℝ`-linear equivalence between `selfAdjoint ℂ` and `ℝ`.
-/
def Complex.selfAdjointEquiv : selfAdjoint ℂ ≃ₗ[ℝ] ℝ where
  toFun := fun z ↦ (z : ℂ).re
  invFun := fun x ↦ ⟨x, conj_ofReal x⟩
  left_inv := fun z ↦ Subtype.ext <| conj_eq_iff_re.mp z.property.star_eq
  map_add' := by simp
  map_smul' := by simp
/-
**Complex.coe_selfAdjointEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.coe_selfAdjointEquiv (z : selfAdjoint Complex) : (selfAdjointEquiv
 z : Complex) = z
参数：z : selfAdjoint Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `Complex.instStarModuleReal`：StarModule ℝ ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.selfAdjointEquiv_apply`：∀ (z : ↥(selfAdjoint ℂ)), Complex.selfAd
jointEquiv z = (↑z).re
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.selfAdjointEquiv_symm_apply`：∀ (x : ℝ), Complex.selfAdjointEquiv
.symm x = ⟨↑x, ⋯⟩
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
-/
lemma Complex.coe_selfAdjointEquiv (z : selfAdjoint ℂ) :
    (selfAdjointEquiv z : ℂ) = z := by
  simpa [selfAdjointEquiv_symm_apply]
    using (congr_arg Subtype.val <| Complex.selfAdjointEquiv.left_inv z)

@[simp]
/-
**realPart_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：realPart_ofReal (r : Real) : (ℜ (r : Complex) : Complex) = r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `realPart_apply_coe`：realPart_apply_coe (a : A) : (ℜ a : A) = (2 : Real)⁻
¹ • (a + star a)
· 使用定理 `Complex.star_def`：star_def : (Star.star : Complex -> Complex) = conj
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma realPart_ofReal (r : ℝ) : (ℜ (r : ℂ) : ℂ) = r := by
  rw [realPart_apply_coe, star_def, conj_ofReal, ← two_smul ℝ (r : ℂ)]
  simp

@[simp]
/-
**imaginaryPart_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imaginaryPart_ofReal (r : Real) : ℑ (r : Complex) = 0
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `imaginaryPart_apply_coe`：imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -
I • (2 : Real)⁻¹ • (a - star a)
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma imaginaryPart_ofReal (r : ℝ) : ℑ (r : ℂ) = 0 := by
  ext1; simp [imaginaryPart_apply_coe, conj_ofReal]
/-
**Complex.coe_realPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.coe_realPart (z : Complex) : (ℜ z : Complex) = z.re
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `realPart_I_smul`：realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a
· 使用引理 `imaginaryPart_ofReal`：imaginaryPart_ofReal (r : Real) : ℑ (r : Complex) 
= 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `realPart_ofReal`：realPart_ofReal (r : Real) : (ℜ (r : Complex) : Complex
) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Complex.coe_realPart (z : ℂ) : (ℜ z : ℂ) = z.re := by
  conv_lhs => rw [← re_add_im z]
  simp [-re_add_im, realPart_I_smul, mul_comm _ I, ← smul_eq_mul]

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [StarModule ℂ A]

/-
**star_mul_self_add_self_mul_star** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：star_mul_self_add_self_mul_star (a : A) : star a * a + a * star a = 2 • (ℜ
 a * ℜ a + ℑ a * ℑ a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `realPart_add_I_smul_imaginaryPart`：realPart_add_I_smul_imaginaryPart (a 
: A) : (ℜ a : A) + I • (ℑ a : A) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `selfAdjoint.star_val_eq`：star_val_eq {x : selfAdjoint R} : star (x : R) 
= x
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `_private.Mathlib.LinearAlgebra.Complex.Module.0.star_mul_self_add_self_m
ul_star._abel_1_2`：∀ {A : Type u_1} [inst : NonUnitalNonAssocRing A] [inst_1 : S
tarRing A] [inst_2 : _root_.Module ℂ A]   [inst_3 : StarModule ℂ A] (a : A),   …
-/
lemma star_mul_self_add_self_mul_star (a : A) :
    star a * a + a * star a = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) :=
  have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a + a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) + $(a_eq) * (star $(a_eq)))
    _ = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) := by
      simp [mul_add, add_mul, smul_smul, mul_smul_comm,
        smul_mul_assoc]
      abel
/-
**star_mul_self_sub_self_mul_star** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：star_mul_self_sub_self_mul_star (a : A) : star a * a - a * star a = 2 • I 
• (ℜ a * ℑ a - ℑ a * ℜ a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `realPart_add_I_smul_imaginaryPart`：realPart_add_I_smul_imaginaryPart (a 
: A) : (ℜ a : A) + I • (ℑ a : A) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `selfAdjoint.star_val_eq`：star_val_eq {x : selfAdjoint R} : star (x : R) 
= x
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
（共 89 条，此处仅展示前 30 条）
-/
lemma star_mul_self_sub_self_mul_star (a : A) :
    star a * a - a * star a = 2 • I • (ℜ a * ℑ a - ℑ a * ℜ a) :=
  have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a - a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) - $(a_eq) * (star $(a_eq)))
    _ = 2 • I • (ℜ a * ℑ a - ℑ a * ℜ a) := by
      simp [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul]
      module

/-- An element in a non-unital star `ℂ`-algebra is normal if and only if its real and imaginary
parts commute. -/
/-
**isStarNormal_iff_commute_realPart_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isStarNormal_iff_commute_realPart_imaginaryPart {x : A} : IsStarNormal x ↔
 Commute (ℜ x : A) (ℑ x : A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isStarNormal_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] (x :
 R), IsStarNormal x ↔ Commute (star x) x
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `star_mul_self_sub_self_mul_star`：star_mul_self_sub_self_mul_star (a : A)
 : star a * a - a * star a = 2 • I • (ℜ a * ℑ a - ℑ a * ℜ a)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element in a non-unital star `ℂ`-algebra is normal if and only if its real an
d imaginary
parts commute.
-/
lemma isStarNormal_iff_commute_realPart_imaginaryPart {x : A} :
    IsStarNormal x ↔ Commute (ℜ x : A) (ℑ x : A) := by
  rw [isStarNormal_iff, commute_iff_eq, ← sub_eq_zero, star_mul_self_sub_self_mul_star,
    two_smul ℕ, ← two_smul ℂ, smul_eq_zero_iff_right two_ne_zero, smul_eq_zero_iff_right I_ne_zero,
    sub_eq_zero, commute_iff_eq]
/-
**Commute.realPart_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.realPart_imaginaryPart (x : A) [IsStarNormal x] : Commute (ℜ x : A
) (ℑ x : A)
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用引理 `isStarNormal_iff_commute_realPart_imaginaryPart`：isStarNormal_iff_commut
e_realPart_imaginaryPart {x : A} : IsStarNormal x ↔ Commute (ℜ x : A) (ℑ x : A)
-/
lemma Commute.realPart_imaginaryPart (x : A) [IsStarNormal x] :
    Commute (ℜ x : A) (ℑ x : A) :=
  isStarNormal_iff_commute_realPart_imaginaryPart.mp inferInstance
/-
**star_mul_self_eq_realPart_sq_add_imaginaryPart_sq** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：star_mul_self_eq_realPart_sq_add_imaginaryPart_sq (x : A) [hx : IsStarNorm
al x] : star x * x = ℜ x * ℜ x + ℑ x * ℑ x
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `realPart_add_I_smul_imaginaryPart`：realPart_add_I_smul_imaginaryPart (a 
: A) : (ℜ a : A) + I • (ℑ a : A) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `selfAdjoint.star_val_eq`：star_val_eq {x : selfAdjoint R} : star (x : R) 
= x
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用引理 `Commute.realPart_imaginaryPart`：Commute.realPart_imaginaryPart (x : A) [
IsStarNormal x] : Commute (ℜ x : A) (ℑ x : A)
（共 34 条，此处仅展示前 30 条）
-/
lemma star_mul_self_eq_realPart_sq_add_imaginaryPart_sq (x : A) [hx : IsStarNormal x] :
    star x * x = ℜ x * ℜ x + ℑ x * ℑ x := calc
  star x * x = ℜ x * ℜ x + ℑ x * ℑ x + Complex.I • (ℜ x * ℑ x - ℑ x * ℜ x) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
    simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
    grind
  _ = _ := by simp [Commute.realPart_imaginaryPart x |>.eq]

end NonUnitalNonAssocRing

section StarOrderedRing

variable [NonUnitalRing A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Module ℂ A] [StarModule ℂ A]

/-
**nonneg_iff_realPart_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonneg_iff_realPart_imaginaryPart {a : A} : 0 <= a ↔ 0 <= ℜ a ∧ ℑ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsSelfAdjoint.coe_realPart`：IsSelfAdjoint.coe_realPart {x : A} (hx : IsS
elfAdjoint x) : (ℜ x : A) = x
· 使用定理 `LE.le.isSelfAdjoint`：∀ {R : Type u_1} [inst : NonUnitalSemiring R] [inst
_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   {x : R}, 0 ≤ x 
→ IsSelfA…
· 使用引理 `selfAdjoint.realPart_coe`：selfAdjoint.realPart_coe {x : selfAdjoint A} :
 ℜ (x : A) = x
· 使用定理 `IsSelfAdjoint.imaginaryPart`：∀ {A : Type u_1} [inst : AddCommGroup A] [i
nst_1 : _root_.Module ℂ A] [inst_2 : StarAddMonoid A]   [inst_3 : StarModule ℂ A
] {x : A}, IsSelf…
· 使用定理 `realPart_add_I_smul_imaginaryPart`：realPart_add_I_smul_imaginaryPart (a 
: A) : (ℜ a : A) + I • (ℑ a : A) = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma nonneg_iff_realPart_imaginaryPart {a : A} :
    0 ≤ a ↔ 0 ≤ ℜ a ∧ ℑ a = 0 := by
  refine ⟨fun h ↦ ⟨?_, h.isSelfAdjoint.imaginaryPart⟩, fun h ↦ ?_⟩
  · simpa +singlePass [← h.isSelfAdjoint.coe_realPart] using! h
  · rw [← realPart_add_I_smul_imaginaryPart a, h.2]
    simpa using! h.1
/-
**nonpos_iff_realPart_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonpos_iff_realPart_imaginaryPart {a : A} : a <= 0 ↔ ℜ a <= 0 ∧ ℑ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddSubmonoidClass.toIsOrderedCancelAddMonoid`：∀ {M : Type u_1} {S : Type
 u_2} [inst : SetLike S M] [inst_1 : AddCommMonoid M] [inst_2 : Preorder M]   [I
sOrderedCancelAddMonoid M] [inst_4…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `nonneg_iff_realPart_imaginaryPart`：nonneg_iff_realPart_imaginaryPart {a 
: A} : 0 <= a ↔ 0 <= ℜ a ∧ ℑ a = 0
-/
lemma nonpos_iff_realPart_imaginaryPart {a : A} :
    a ≤ 0 ↔ ℜ a ≤ 0 ∧ ℑ a = 0 := by
  simpa using nonneg_iff_realPart_imaginaryPart (a := -a)
/-
**realPart_nonneg_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：realPart_nonneg_of_nonneg {a : A} (ha : 0 <= a) : 0 <= ℜ a
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `nonneg_iff_realPart_imaginaryPart`：nonneg_iff_realPart_imaginaryPart {a 
: A} : 0 <= a ↔ 0 <= ℜ a ∧ ℑ a = 0
-/
lemma realPart_nonneg_of_nonneg {a : A} (ha : 0 ≤ a) : 0 ≤ ℜ a :=
  nonneg_iff_realPart_imaginaryPart.mp ha |>.1
/-
**realPart_nonpos_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：realPart_nonpos_of_nonpos {a : A} (ha : a <= 0) : ℜ a <= 0
参数：ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `nonpos_iff_realPart_imaginaryPart`：nonpos_iff_realPart_imaginaryPart {a 
: A} : a <= 0 ↔ ℜ a <= 0 ∧ ℑ a = 0
-/
lemma realPart_nonpos_of_nonpos {a : A} (ha : a ≤ 0) : ℜ a ≤ 0 :=
  nonpos_iff_realPart_imaginaryPart.mp ha |>.1
/-
**le_iff_realPart_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iff_realPart_imaginaryPart {a b : A} : a <= b ↔ ℜ a <= ℜ b ∧ ℑ a = ℑ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `AddSubmonoidClass.toIsOrderedCancelAddMonoid`：∀ {M : Type u_1} {S : Type
 u_2} [inst : SetLike S M] [inst_1 : AddCommMonoid M] [inst_2 : Preorder M]   [I
sOrderedCancelAddMonoid M] [inst_4…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `nonneg_iff_realPart_imaginaryPart`：nonneg_iff_realPart_imaginaryPart {a 
: A} : 0 <= a ↔ 0 <= ℜ a ∧ ℑ a = 0
-/
lemma le_iff_realPart_imaginaryPart {a b : A} :
    a ≤ b ↔ ℜ a ≤ ℜ b ∧ ℑ a = ℑ b := by
  simpa [sub_eq_zero, eq_comm (a := ℑ a)] using nonneg_iff_realPart_imaginaryPart (a := b - a)
/-
**imaginaryPart_eq_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imaginaryPart_eq_of_le {a b : A} (hab : a <= b) : ℑ a = ℑ b
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_realPart_imaginaryPart`：le_iff_realPart_imaginaryPart {a b : A} :
 a <= b ↔ ℜ a <= ℜ b ∧ ℑ a = ℑ b
-/
lemma imaginaryPart_eq_of_le {a b : A} (hab : a ≤ b) :
    ℑ a = ℑ b :=
  le_iff_realPart_imaginaryPart.mp hab |>.2
/-
**realPart_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：realPart_mono {a b : A} (hab : a <= b) : ℜ a <= ℜ b
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_realPart_imaginaryPart`：le_iff_realPart_imaginaryPart {a b : A} :
 a <= b ↔ ℜ a <= ℜ b ∧ ℑ a = ℑ b
-/
lemma realPart_mono {a b : A} (hab : a ≤ b) :
    ℜ a ≤ ℜ b :=
  le_iff_realPart_imaginaryPart.mp hab |>.1

end StarOrderedRing

@[simp]
/-
**realPart_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：realPart_one [Ring A] [StarRing A] [Module Complex A] [StarModule Complex 
A] : ℜ (1 : A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `realPart_apply_coe`：realPart_apply_coe (a : A) : (ℜ a : A) = (2 : Real)⁻
¹ • (a + star a)
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma realPart_one [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A] :
    ℜ (1 : A) = 1 := by
  ext; simp [realPart_apply_coe, ← two_smul ℝ]
/-
**mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one** 是 M
athlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one [
Ring A] [StarRing A] [Module Complex A] [SMulCommClass Complex A A] [IsScalarTow
er Complex A A] [StarModule Complex A] {x : A} : x in unitary A ↔ IsStarNormal x
 ∧ ℜ x ^ 2 + ℑ x ^ 2 = (1 : A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitary.mem_iff`：mem_iff {U : R} : U in unitary R ↔ star U * U = 1 ∧ U *
 star U = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `star_mul_self_eq_realPart_sq_add_imaginaryPart_sq`：star_mul_self_eq_real
Part_sq_add_imaginaryPart_sq (x : A) [hx : IsStarNormal x] : star x * x = ℜ x * 
ℜ x + ℑ x * ℑ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `IsStarNormal.star_comm_self`：∀ {R : Type u_1} {inst : Mul R} {inst_1 : S
tar R} {x : R} [self : IsStarNormal x], Commute (star x) x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one [Ring A]
    [StarRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A] {x : A} :
    x ∈ unitary A ↔ IsStarNormal x ∧ ℜ x ^ 2 + ℑ x ^ 2 = (1 : A) := by
  rw [Unitary.mem_iff]
  refine ⟨fun ⟨h, h'⟩ ↦ ?_, fun ⟨hx, h⟩ ↦ ?_⟩
  · have : IsStarNormal x := ⟨h.trans h'.symm⟩
    exact ⟨this, by simp [sq, ← star_mul_self_eq_realPart_sq_add_imaginaryPart_sq x, h]⟩
  · simp [← hx.star_comm_self.eq, star_mul_self_eq_realPart_sq_add_imaginaryPart_sq, ← sq, h]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F E A : Type*} [AddCommGroup E] [PartialOrder E]
    [StarAddMonoid E] [SelfAdjointDecompose E] [Module ℂ E] [StarModule ℂ E]
    [NonUnitalRing A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Module ℂ A] [StarModule ℂ A]
    [FunLike F E A] [OrderHomClass F E A] [LinearMapClass F ℂ E A] :
    StarHomClass F E A where
  map_star φ x := by
    rw [← realPart_add_I_smul_imaginaryPart x]
    simp [(ℜ x).2.map' φ, IsSelfAdjoint.star_eq, (ℑ x).2.map' φ]

end RealImaginaryPart

