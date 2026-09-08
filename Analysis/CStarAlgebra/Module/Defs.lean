/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.NormNum.GCD

/-!
# Hilbert C⋆-modules

A Hilbert C⋆-module is a complex module `E` together with a right `A`-module structure, where `A`
is a C⋆-algebra, and with an `A`-valued inner product. This inner product satisfies the
Cauchy-Schwarz inequality, and induces a norm that makes `E` a normed vector space over `ℂ`.

## Main declarations

+ `CStarModule`: The class containing the Hilbert C⋆-module structure
+ `CStarModule.normedSpaceCore`: The proof that a Hilbert C⋆-module is a normed vector
  space. This can be used with `NormedAddCommGroup.ofCore` and `NormedSpace.ofCore` to create
  the relevant instances on a type of interest.
+ `CStarModule.inner_mul_inner_swap_le`: The statement that
  `⟪x, y⟫ * ⟪y, x⟫ ≤ ‖x‖ ^ 2 • ⟪y, y⟫`, which can be viewed as a version of the Cauchy-Schwarz
  inequality for Hilbert C⋆-modules.
+ `CStarModule.norm_inner_le`, which states that `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖`, i.e. the
  Cauchy-Schwarz inequality.

## Implementation notes

The class `CStarModule A E` requires `E` to already have a `Norm E` instance on it, but
no other norm-related instances. We then include the fact that this norm agrees with the norm
induced by the inner product among the axioms of the class. Furthermore, instead of registering
`NormedAddCommGroup E` and `NormedSpace ℂ E` instances (which might already be present on the type,
and which would send the type class search algorithm on a chase for `A`), we provide a
`NormedSpace.Core` structure which enables downstream users of the class to easily register
these instances themselves on a particular type.

Although the `Norm` is passed as a parameter, it almost never coincides with the norm on the
underlying type, unless that it is a purpose built type, as with the *standard Hilbert C⋆-module*.
However, with generic types already equipped with a norm, the norm as a Hilbert C⋆-module almost
never coincides with the norm on the underlying type. The two notable exceptions to this are when
we view `A` as a C⋆-module over itself, or when `A := ℂ`.  For this reason we will later use the
type synonym `WithCStarModule`.

As an example of just how different the norm can be, consider `CStarModule`s `E` and `F` over `A`.
One would like to put a `CStarModule` structure on (a type synonym of) `E × F`, where the `A`-valued
inner product is given, for `x y : E × F`, `⟪x, y⟫_A := ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A`. The norm this
induces satisfies `‖x‖ ^ 2 = ‖⟪x.1, y.1⟫ + ⟪x.2, y.2⟫‖`, but this doesn't coincide with *any*
natural norm on `E × F` unless `A := ℂ`, in which case it is `WithLp 2 (E × F)` because `E × F` is
then an `InnerProductSpace` over `ℂ`.

## References

+ Erin Wittlich. *Formalizing Hilbert Modules in C⋆-algebras with the Lean Proof Assistant*,
  December 2022. Master's thesis, Southern Illinois University Edwardsville.
-/

@[expose] public section

open scoped ComplexOrder RightActions

/-- A *Hilbert C⋆-module* is a complex module `E` endowed with a right `A`-module structure
(where `A` is typically a C⋆-algebra) and an inner product `⟪x, y⟫_A` which satisfies the
following properties. -/
/-
**CStarModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) →   (E : Type u_2) →     [inst : NonUnitalSemiring A] →    
   [StarRing A] →         [_root_.Module ℂ A] →           [inst : AddCommGroup E
] →             [_root_.Module ℂ E] → [PartialOrder A] → [SMul A E] → [Norm A] →
 [Norm E] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *Hilbert C⋆-module* is a complex module `E` endowed with a right `A`-module st
ructure
(where `A` is typically a C⋆-algebra) and an inner product `⟪x, y⟫_A` which sati
sfies the
following properties.
-/
class CStarModule (A E : Type*) [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    extends Inner A E where
  inner_add_right {x} {y} {z} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x} : 0 ≤ inner x x
  inner_self {x} : inner x x = 0 ↔ x = 0
  inner_op_smul_right {a : A} {x y : E} : inner x (a • y) = a * inner x y
  inner_smul_right_complex {z : ℂ} {x} {y} : inner x (z • y) = z • inner x y
  star_inner x y : star (inner x y) = inner y x
  norm_eq_sqrt_norm_inner_self x : ‖x‖ = √‖inner x x‖

attribute [simp] CStarModule.inner_add_right CStarModule.star_inner
  CStarModule.inner_op_smul_right CStarModule.inner_smul_right_complex

namespace CStarModule

section general

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [AddCommGroup E] [Module ℂ A]
  [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E] [CStarModule A E]

local notation "⟪" x ", " y "⟫" => inner A x y

@[simp]
/-
**CStarModule.inner_add_left** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CStarModule.star_inner`：∀ {A : Type u_1} {E : Type u_2} {inst : NonUnita
lSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 : AddC
ommGroup E} …
· 使用定理 `CStarModule.inner_add_right`：∀ {A : Type u_1} {E : Type u_2} {inst : Non
UnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 :
 AddCommGroup E} …
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := by
  rw [← star_star (r := ⟪x + y, z⟫)]
  simp only [inner_add_right, star_add, star_inner]

@[simp]
/-
**CStarModule.inner_op_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：inner_op_smul_left {a : A} {x y : E} : ⟪a • x, y⟫ = ⟪x, y⟫ * star a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CStarModule.star_inner`：∀ {A : Type u_1} {E : Type u_2} {inst : NonUnita
lSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 : AddC
ommGroup E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CStarModule.inner_op_smul_right`：∀ {A : Type u_1} {E : Type u_2} {inst :
 NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst
_3 : AddCommGroup E} …
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inner_op_smul_left {a : A} {x y : E} : ⟪a • x, y⟫ = ⟪x, y⟫ * star a := by
  rw [← star_inner]; simp

section StarModule

variable [StarModule ℂ A]

@[simp]
/-
**CStarModule.inner_smul_left_complex** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：inner_smul_left_complex {z : Complex} {x y : E} : ⟪z • x, y⟫ = star z • ⟪x
, y⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CStarModule.star_inner`：∀ {A : Type u_1} {E : Type u_2} {inst : NonUnita
lSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 : AddC
ommGroup E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CStarModule.inner_smul_right_complex`：∀ {A : Type u_1} {E : Type u_2} {i
nst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   
{inst_3 : AddCommGroup E} …
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inner_smul_left_complex {z : ℂ} {x y : E} : ⟪z • x, y⟫ = star z • ⟪x, y⟫ := by
  rw [← star_inner]
  simp

@[simp]
/-
**CStarModule.inner_smul_left_real** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：inner_smul_left_real {z : Real} {x y : E} : ⟪z • x, y⟫ = z • ⟪x, y⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CStarModule.star_inner`：∀ {A : Type u_1} {E : Type u_2} {inst : NonUnita
lSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 : AddC
ommGroup E} …
· 使用定理 `CStarModule.inner_smul_right_complex`：∀ {A : Type u_1} {E : Type u_2} {i
nst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   
{inst_3 : AddCommGroup E} …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
-/
lemma inner_smul_left_real {z : ℝ} {x y : E} : ⟪z • x, y⟫ = z • ⟪x, y⟫ := by
  have h₁ : z • x = (z : ℂ) • x := by simp
  rw [h₁, ← star_inner, inner_smul_right_complex]
  simp

@[simp]
/-
**CStarModule.inner_smul_right_real** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：inner_smul_right_real {z : Real} {x y : E} : ⟪x, z • y⟫ = z • ⟪x, y⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CStarModule.star_inner`：∀ {A : Type u_1} {E : Type u_2} {inst : NonUnita
lSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 : AddC
ommGroup E} …
· 使用引理 `CStarModule.inner_smul_left_complex`：inner_smul_left_complex {z : Comple
x} {x y : E} : ⟪z • x, y⟫ = star z • ⟪x, y⟫
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
-/
lemma inner_smul_right_real {z : ℝ} {x y : E} : ⟪x, z • y⟫ = z • ⟪x, y⟫ := by
  have h₁ : z • y = (z : ℂ) • y := by simp
  rw [h₁, ← star_inner, inner_smul_left_complex]
  simp

/-- The function `⟨x, y⟩ ↦ ⟪x, y⟫` bundled as a sesquilinear map. -/
/-
**CStarModule.inner** 是 Mathlib 中的一个定义，位于命名空间 `CStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `⟨x, y⟩ ↦ ⟪x, y⟫` bundled as a sesquilinear map.
-/
def innerₛₗ : E →ₗ⋆[ℂ] E →ₗ[ℂ] A where
  toFun x := { toFun := fun y => ⟪x, y⟫
               map_add' := fun z y => by simp
               map_smul' := fun z y => by simp }
  map_add' z y := by ext; simp
  map_smul' z y := by ext; simp
/-
**CStarModule.inner** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerₛₗ_apply {x y : E} : innerₛₗ x y = ⟪x, y⟫ := rfl
/-
**CStarModule.inner_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ {A : Type u_1} {E : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRin
g A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ A] [inst_4 : _root_.M
odule ℂ E] [inst_5 : PartialOrder A] [inst_6 : SMul A E]   [inst_7 : Norm A] [in
st_8 : Norm E] [inst_9 : CStarModule A E] [StarModule ℂ A] {x : E}, inner A x 0 
= 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma inner_zero_right {x : E} : ⟪x, 0⟫ = 0 := by simp [← innerₛₗ_apply]
/-
**CStarModule.inner_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ {A : Type u_1} {E : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRin
g A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ A] [inst_4 : _root_.M
odule ℂ E] [inst_5 : PartialOrder A] [inst_6 : SMul A E]   [inst_7 : Norm A] [in
st_8 : Norm E] [inst_9 : CStarModule A E] [StarModule ℂ A] {x : E}, inner A 0 x 
= 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma inner_zero_left {x : E} : ⟪0, x⟫ = 0 := by simp [← innerₛₗ_apply]
/-
**CStarModule.inner_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ {A : Type u_1} {E : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRin
g A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ A] [inst_4 : _root_.M
odule ℂ E] [inst_5 : PartialOrder A] [inst_6 : SMul A E]   [inst_7 : Norm A] [in
st_8 : Norm E] [inst_9 : CStarModule A E] [StarModule ℂ A] {x y : E},   inner A 
x (-y) = -inner A x y
参数：-y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma inner_neg_right {x y : E} : ⟪x, -y⟫ = -⟪x, y⟫ := by simp [← innerₛₗ_apply]
/-
**CStarModule.inner_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ {A : Type u_1} {E : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRin
g A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ A] [inst_4 : _root_.M
odule ℂ E] [inst_5 : PartialOrder A] [inst_6 : SMul A E]   [inst_7 : Norm A] [in
st_8 : Norm E] [inst_9 : CStarModule A E] [StarModule ℂ A] {x y : E},   inner A 
(-x) y = -inner A x y
参数：-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma inner_neg_left {x y : E} : ⟪-x, y⟫ = -⟪x, y⟫ := by simp [← innerₛₗ_apply]
/-
**CStarModule.inner_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ {A : Type u_1} {E : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRin
g A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ A] [inst_4 : _root_.M
odule ℂ E] [inst_5 : PartialOrder A] [inst_6 : SMul A E]   [inst_7 : Norm A] [in
st_8 : Norm E] [inst_9 : CStarModule A E] [StarModule ℂ A] {x y z : E},   inner 
A x (y - z) = inner A x y - inner A x z
参数：y - z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma inner_sub_right {x y z : E} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [← innerₛₗ_apply]
/-
**CStarModule.inner_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ {A : Type u_1} {E : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRin
g A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ A] [inst_4 : _root_.M
odule ℂ E] [inst_5 : PartialOrder A] [inst_6 : SMul A E]   [inst_7 : Norm A] [in
st_8 : Norm E] [inst_9 : CStarModule A E] [StarModule ℂ A] {x y z : E},   inner 
A (x - y) z = inner A x z - inner A y z
参数：x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma inner_sub_left {x y z : E} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [← innerₛₗ_apply]

@[simp]
/-
**CStarModule.inner_sum_right** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：inner_sum_right {ι : Type*} {s : Finset ι} {x : E} {y : ι -> E} : ⟪x, ∑ i 
in s, y i⟫ = ∑ i in s, ⟪x, y i⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
lemma inner_sum_right {ι : Type*} {s : Finset ι} {x : E} {y : ι → E} :
    ⟪x, ∑ i ∈ s, y i⟫ = ∑ i ∈ s, ⟪x, y i⟫ :=
  map_sum (innerₛₗ x) ..

@[simp]
/-
**CStarModule.inner_sum_left** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：inner_sum_left {ι : Type*} {s : Finset ι} {x : ι -> E} {y : E} : ⟪∑ i in s
, x i, y⟫ = ∑ i in s, ⟪x i, y⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
lemma inner_sum_left {ι : Type*} {s : Finset ι} {x : ι → E} {y : E} :
    ⟪∑ i ∈ s, x i, y⟫ = ∑ i ∈ s, ⟪x i, y⟫ :=
  map_sum (innerₛₗ.flip y) ..

end StarModule

@[simp]
/-
**CStarModule.isSelfAdjoint_inner_self** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：isSelfAdjoint_inner_self {x : E} : IsSelfAdjoint ⟪x, x⟫
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarModule.star_inner`：∀ {A : Type u_1} {E : Type u_2} {inst : NonUnita
lSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 : AddC
ommGroup E} …
-/
lemma isSelfAdjoint_inner_self {x : E} : IsSelfAdjoint ⟪x, x⟫ := star_inner _ _

end general

section norm

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [AddCommGroup E]
  [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

local notation "⟪" x ", " y "⟫" => inner A x y

open scoped InnerProductSpace in
/-- The norm associated with a Hilbert C⋆-module. It is not registered as a norm, since a type
might already have a norm defined on it. -/
@[instance_reducible]
/-
**CStarModule.norm** 是 Mathlib 中的一个定义，位于命名空间 `CStarModule`。
形式化陈述：norm (A : Type*) {E : Type*} [Norm A] [Inner A E] : Norm E where norm x
参数：A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm associated with a Hilbert C⋆-module. It is not registered as a norm, si
nce a type
might already have a norm defined on it.
-/
noncomputable def norm (A : Type*) {E : Type*} [Norm A] [Inner A E] : Norm E where
  norm x := √‖⟪x, x⟫_A‖

section
include A

variable (A)

/-
**CStarModule.norm_sq_eq** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖ := by simp [norm_eq_sqrt_norm_inner_self (A := A)]
/-
**CStarModule.norm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ (A : Type u_1) {E : Type u_2} [inst : NonUnitalCStarAlgebra A] [inst_1 :
 PartialOrder A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ E] [inst_
4 : SMul A E] [inst_5 : Norm E] [CStarModule A E] {x : E}, 0 ≤ ‖x‖
参数：A : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
-/
protected lemma norm_nonneg {x : E} : 0 ≤ ‖x‖ := by simp [norm_eq_sqrt_norm_inner_self (A := A)]
/-
**CStarModule.norm_pos** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ (A : Type u_1) {E : Type u_2} [inst : NonUnitalCStarAlgebra A] [inst_1 :
 PartialOrder A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ E] [inst_
4 : SMul A E] [inst_5 : Norm E] [CStarModule A E] {x : E}, x ≠ 0 → 0 < ‖x‖
参数：A : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
· 使用定理 `CStarModule.inner_self`：∀ {A : Type u_1} {E : Type u_2} {inst : NonUnita
lSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 : AddC
ommGroup E} …
-/
protected lemma norm_pos {x : E} (hx : x ≠ 0) : 0 < ‖x‖ := by
  simp only [norm_eq_sqrt_norm_inner_self (A := A), Real.sqrt_pos, norm_pos_iff]
  intro H
  rw [inner_self] at H
  exact hx H
/-
**CStarModule.norm_zero** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ (A : Type u_1) {E : Type u_2} [inst : NonUnitalCStarAlgebra A] [inst_1 :
 PartialOrder A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ E] [inst_
4 : SMul A E] [inst_5 : Norm E] [CStarModule A E], ‖0‖ = 0
参数：A : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
· 使用定理 `CStarModule.inner_zero_right`：∀ {A : Type u_1} {E : Type u_2} [inst : No
nUnitalRing A] [inst_1 : StarRing A] [inst_2 : AddCommGroup E]   [inst_3 : _root
_.Module ℂ A] [ins…
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma norm_zero : ‖(0 : E)‖ = 0 := by simp [norm_eq_sqrt_norm_inner_self (A := A)]
/-
**CStarModule.norm_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：norm_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CStarModule.inner_zero_right`：∀ {A : Type u_1} {E : Type u_2} [inst : No
nUnitalRing A] [inst_1 : StarRing A] [inst_2 : AddCommGroup E]   [inst_3 : _root
_.Module ℂ A] [ins…
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0 :=
  ⟨fun h => by simpa [norm_eq_sqrt_norm_inner_self (A := A), inner_self] using h,
    fun h => by simp [h, norm_eq_sqrt_norm_inner_self (A := A)]⟩

end

variable [StarOrderedRing A]

open scoped InnerProductSpace in
/-- The C⋆-algebra-valued Cauchy-Schwarz inequality for Hilbert C⋆-modules. -/
/-
**CStarModule.inner_mul_inner_swap_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：inner_mul_inner_swap_le {x y : E} : ⟪x, y⟫ * ⟪y, x⟫ <= ‖x‖ ^ 2 • ⟪y, y⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CStarModule.inner_zero_left`：∀ {A : Type u_1} {E : Type u_2} [inst : Non
UnitalRing A] [inst_1 : StarRing A] [inst_2 : AddCommGroup E]   [inst_3 : _root_
.Module ℂ A] [ins…
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `CStarModule.inner_zero_right`：∀ {A : Type u_1} {E : Type u_2} [inst : No
nUnitalRing A] [inst_1 : StarRing A] [inst_2 : AddCommGroup E]   [inst_3 : _root
_.Module ℂ A] [ins…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `CStarModule.norm_zero`：∀ (A : Type u_1) {E : Type u_2} [inst : NonUnital
CStarAlgebra A] [inst_1 : PartialOrder A] [inst_2 : AddCommGroup E]   [inst_3 : 
_root_.Modu…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `CStarModule.inner_self_nonneg`：∀ {A : Type u_1} {E : Type u_2} {inst : N
onUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3
 : AddCommGroup E} …
· 使用定理 `CStarModule.inner_sub_right`：∀ {A : Type u_1} {E : Type u_2} [inst : Non
UnitalRing A] [inst_1 : StarRing A] [inst_2 : AddCommGroup E]   [inst_3 : _root_
.Module ℂ A] [ins…
· 使用定理 `CStarModule.inner_op_smul_right`：∀ {A : Type u_1} {E : Type u_2} {inst :
 NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst
_3 : AddCommGroup E} …
· 使用定理 `CStarModule.inner_sub_left`：∀ {A : Type u_1} {E : Type u_2} [inst : NonU
nitalRing A] [inst_1 : StarRing A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.
Module ℂ A] [ins…
· 使用引理 `CStarModule.inner_op_smul_left`：inner_op_smul_left {a : A} {x y : E} : ⟪
a • x, y⟫ = ⟪x, y⟫ * star a
· 使用引理 `CStarModule.inner_smul_left_real`：inner_smul_left_real {z : Real} {x y :
 E} : ⟪z • x, y⟫ = z • ⟪x, y⟫
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用引理 `CStarModule.inner_smul_right_real`：inner_smul_right_real {z : Real} {x y
 : E} : ⟪x, z • y⟫ = z • ⟪x, y⟫
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `_private.Mathlib.Analysis.CStarAlgebra.Module.Defs.0.CStarModule.inner_m
ul_inner_swap_le._abel_1_1`：∀ {A : Type u_1} {E : Type u_2} [inst : NonUnitalCSt
arAlgebra A] [inst_1 : PartialOrder A] [inst_2 : AddCommGroup E]   [inst_3 : _ro
ot_.Modu…
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
The C⋆-algebra-valued Cauchy-Schwarz inequality for Hilbert C⋆-modules.
-/
lemma inner_mul_inner_swap_le {x y : E} : ⟪x, y⟫ * ⟪y, x⟫ ≤ ‖x‖ ^ 2 • ⟪y, y⟫ := by
  rcases eq_or_ne x 0 with h | h
  · simp [h, CStarModule.norm_zero A (E := E)]
  · have h₁ : ∀ (a : A),
        (0 : A) ≤ ‖x‖ ^ 2 • (a * star a) - ‖x‖ ^ 2 • (a * ⟪y, x⟫)
                  - ‖x‖ ^ 2 • (⟪x, y⟫ * star a) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := fun a => by
      calc (0 : A) ≤ ⟪a • x - ‖x‖ ^ 2 • y, a • x - ‖x‖ ^ 2 • y⟫_A := by
                      exact inner_self_nonneg
            _ = a * ⟪x, x⟫ * star a - ‖x‖ ^ 2 • (a * ⟪y, x⟫)
                  - ‖x‖ ^ 2 • (⟪x, y⟫ * star a) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := by
                      simp only [inner_sub_right, inner_op_smul_right, inner_sub_left,
                        inner_op_smul_left, inner_smul_left_real, mul_sub, mul_smul_comm,
                        inner_smul_right_real, smul_sub, mul_assoc]
                      abel
            _ ≤ ‖x‖ ^ 2 • (a * star a) - ‖x‖ ^ 2 • (a * ⟪y, x⟫)
                  - ‖x‖ ^ 2 • (⟪x, y⟫ * star a) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := by
                      gcongr
                      calc _ ≤ ‖⟪x, x⟫_A‖ • (a * star a) :=
                          CStarAlgebra.star_right_conjugate_le_norm_smul
                        _ = (√‖⟪x, x⟫_A‖) ^ 2 • (a * star a) := by
                          rw [Real.sq_sqrt]
                          positivity
                        _ = ‖x‖ ^ 2 • (a * star a) := by rw [← norm_eq_sqrt_norm_inner_self]
    specialize h₁ ⟪x, y⟫
    simp only [star_inner, sub_self, zero_sub, le_neg_add_iff_add_le, add_zero] at h₁
    rwa [smul_le_smul_iff_of_pos_left (pow_pos (CStarModule.norm_pos A h) _)] at h₁

open scoped InnerProductSpace in
variable (E) in
/-- The Cauchy-Schwarz inequality for Hilbert C⋆-modules. -/
/-
**CStarModule.norm_inner_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：norm_inner_le {x y : E} : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CStarModule.star_inner`：∀ {A : Type u_1} {E : Type u_2} {inst : NonUnita
lSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 : AddC
ommGroup E} …
· 使用定理 `CStarRing.norm_self_mul_star`：norm_self_mul_star {x : E} : ‖x * x⋆‖ = ‖x
‖ * ‖x‖
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `CStarAlgebra.norm_le_norm_of_nonneg_of_le`：norm_le_norm_of_nonneg_of_le 
{a b : A} (ha : 0 <= a
· 使用定理 `mul_star_self_nonneg`：mul_star_self_nonneg (r : R) : 0 <= r * star r
· 使用引理 `CStarModule.inner_mul_inner_swap_le`：inner_mul_inner_swap_le {x y : E} :
 ⟪x, y⟫ * ⟪y, x⟫ <= ‖x‖ ^ 2 • ⟪y, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `pow_le_pow_iff_left₀`：pow_le_pow_iff_left₀ [MulPosMono M₀] (ha : 0 <= a)
 (hb : 0 <= b) (hn : n != 0) : a ^ n <= b ^ n ↔ a <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The Cauchy-Schwarz inequality for Hilbert C⋆-modules.
-/
lemma norm_inner_le {x y : E} : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  have := calc ‖⟪x, y⟫‖ ^ 2 = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
                rw [← star_inner x, CStarRing.norm_self_mul_star, pow_two]
    _ ≤ ‖‖x‖ ^ 2 • ⟪y, y⟫‖ := by
                refine CStarAlgebra.norm_le_norm_of_nonneg_of_le ?_ inner_mul_inner_swap_le
                rw [← star_inner x]
                exact mul_star_self_nonneg ⟪x, y⟫_A
    _ = ‖x‖ ^ 2 * ‖⟪y, y⟫‖ := by simp [norm_smul]
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
                simp only [norm_eq_sqrt_norm_inner_self (A := A), norm_nonneg, Real.sq_sqrt]
    _ = (‖x‖ * ‖y‖) ^ 2 := by simp only [mul_pow]
  refine (pow_le_pow_iff_left₀ (norm_nonneg ⟪x, y⟫_A) ?_ (by simp)).mp this
  exact mul_nonneg (CStarModule.norm_nonneg A) (CStarModule.norm_nonneg A)

include A in
variable (A) in
/-
**CStarModule.norm_triangle** 是 Mathlib 中的一个定理，位于命名空间 `CStarModule`。
形式化陈述：∀ (A : Type u_1) {E : Type u_2} [inst : NonUnitalCStarAlgebra A] [inst_1 :
 PartialOrder A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module ℂ E] [inst_
4 : SMul A E] [inst_5 : Norm E] [CStarModule A E] [StarOrderedRing A] (x y : E),
   ‖x + y‖ ≤ ‖x‖ + ‖y‖
参数：A : Type u_1；x y : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
· 使用定理 `CStarModule.inner_add_right`：∀ {A : Type u_1} {E : Type u_2} {inst : Non
UnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3 :
 AddCommGroup E} …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CStarModule.inner_add_left`：inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x
, z⟫ + ⟪y, z⟫
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_add₃_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a b c : E}
, ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `CStarModule.norm_inner_le`：norm_inner_le {x y : E} : ‖⟪x, y⟫‖ <= ‖x‖ * ‖
y‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_pow_two`：∀ {α : Type u} [inst : CommSemiring α] (a b : α), (a + b) ^
 2 = a ^ 2 + 2 * a * b + b ^ 2
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 59 条，此处仅展示前 30 条）
-/
protected lemma norm_triangle (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    calc _ ≤ ‖⟪x, x⟫ + ⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by
          simp only [norm_eq_sqrt_norm_inner_self (A := A), inner_add_right, inner_add_left,
            ← add_assoc, norm_nonneg, Real.sq_sqrt]
          exact norm_add₃_le
      _ ≤ ‖⟪x, x⟫‖ + ‖⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖⟪x, x⟫‖ + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖⟪y, y⟫‖ := by gcongr <;> exact norm_inner_le E
      _ = ‖x‖ ^ 2 + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by
          simp [norm_eq_sqrt_norm_inner_self (A := A)]
      _ = (‖x‖ + ‖y‖) ^ 2 := by simp only [add_pow_two, add_left_inj]; ring
  refine (pow_le_pow_iff_left₀ (CStarModule.norm_nonneg A) ?_ (by simp)).mp h
  exact add_nonneg (CStarModule.norm_nonneg A) (CStarModule.norm_nonneg A)

include A in
variable (A) in
/-- This allows us to get `NormedAddCommGroup` and `NormedSpace` instances on `E` via
`NormedAddCommGroup.ofCore` and `NormedSpace.ofCore`. -/
/-
**CStarModule.normedSpaceCore** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：normedSpaceCore : NormedSpace.Core Complex E where norm_nonneg _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarModule.norm_nonneg`：∀ (A : Type u_1) {E : Type u_2} [inst : NonUnit
alCStarAlgebra A] [inst_1 : PartialOrder A] [inst_2 : AddCommGroup E]   [inst_3 
: _root_.Modu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
· 使用定理 `CStarModule.inner_smul_right_complex`：∀ {A : Type u_1} {E : Type u_2} {i
nst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   
{inst_3 : AddCommGroup E} …
· 使用引理 `CStarModule.inner_smul_left_complex`：inner_smul_left_complex {z : Comple
x} {x y : E} : ⟪z • x, y⟫ = star z • ⟪x, y⟫
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `Real.sqrt_mul'`：sqrt_mul' (x) {y : Real} (hy : 0 <= y) : √(x * y) = √x *
 √y
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CStarModule.norm_triangle`：∀ (A : Type u_1) {E : Type u_2} [inst : NonUn
italCStarAlgebra A] [inst_1 : PartialOrder A] [inst_2 : AddCommGroup E]   [inst_
3 : _root_.Modu…
· 使用引理 `CStarModule.norm_zero_iff`：norm_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0

--- 原说明 ---
This allows us to get `NormedAddCommGroup` and `NormedSpace` instances on `E` vi
a
`NormedAddCommGroup.ofCore` and `NormedSpace.ofCore`.
-/
lemma normedSpaceCore : NormedSpace.Core ℂ E where
  norm_nonneg _ := (CStarModule.norm_nonneg A)
  norm_eq_zero_iff x := norm_zero_iff A x
  norm_smul c x := by simp [norm_eq_sqrt_norm_inner_self (A := A), norm_smul, ← mul_assoc]
  norm_triangle x y := CStarModule.norm_triangle A x y

variable (A) in
/-- This is not listed as an instance because we often want to replace the topology, uniformity
and bornology instead of inheriting them from the norm. -/
/-
**CStarModule.normedAddCommGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `CStarModule`。
形式化陈述：normedAddCommGroup : NormedAddCommGroup E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CStarModule.normedSpaceCore`：normedSpaceCore : NormedSpace.Core Complex 
E where norm_nonneg _

--- 原说明 ---
This is not listed as an instance because we often want to replace the topology,
 uniformity
and bornology instead of inheriting them from the norm.
-/
noncomputable abbrev normedAddCommGroup : NormedAddCommGroup E :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

open scoped InnerProductSpace in
/-
**CStarModule.norm_eq_csSup** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：norm_eq_csSup (v : E) : ‖v‖ = sSup { ‖⟪w, v⟫_A‖ | (w : E) (_ : ‖w‖ <= 1) }
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarModule.normedSpaceCore`：normedSpaceCore : NormedSpace.Core Complex 
E where norm_nonneg _
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGreatest.csSup_eq`：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s =
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用引理 `inv_mul_le_one_of_le₀`：inv_mul_le_one_of_le₀ (h : a <= b) (hb : 0 <= b) 
: b⁻¹ * a <= 1
· 使用引理 `RCLike.toPosMulReflectLT`：toPosMulReflectLT : PosMulReflectLT K where el
im
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CStarModule.inner_smul_left_real`：inner_smul_left_real {z : Real} {x y :
 E} : ⟪z • x, y⟫ = z • ⟪x, y⟫
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `inv_mul_mul_self`：inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CStarModule.norm_inner_le`：norm_inner_le {x y : E} : ‖⟪x, y⟫‖ <= ‖x‖ * ‖
y‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma norm_eq_csSup (v : E) :
    ‖v‖ = sSup { ‖⟪w, v⟫_A‖ | (w : E) (_ : ‖w‖ ≤ 1) } := by
  let instNACG : NormedAddCommGroup E := NormedAddCommGroup.ofCore (normedSpaceCore A)
  let instNS : NormedSpace ℂ E := .ofCore (normedSpaceCore A)
  refine Eq.symm <| IsGreatest.csSup_eq ⟨⟨‖v‖⁻¹ • v, ?_, ?_⟩, ?_⟩
  · simpa only [norm_smul, norm_inv, norm_norm] using inv_mul_le_one_of_le₀ le_rfl (by positivity)
  · simp [norm_smul, ← norm_sq_eq, pow_two, ← mul_assoc]
  · rintro - ⟨w, hw, rfl⟩
    calc _ ≤ ‖w‖ * ‖v‖ := norm_inner_le E
      _ ≤ 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := by simp

end norm

section NormedAddCommGroup

open scoped InnerProductSpace

/- Note: one generally creates a `CStarModule` instance for a type `E` first before getting the
`NormedAddCommGroup` and `NormedSpace` instances via `CStarModule.normedSpaceCore`, especially by
using `NormedAddCommGroup.ofCoreReplaceAll` and `NormedSpace.ofCore`. See
`Analysis.CStarAlgebra.Module.Constructions` for examples. -/
variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [SMul A E]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CStarModule A E]

/-- The function `⟨x, y⟩ ↦ ⟪x, y⟫` bundled as a continuous sesquilinear map. -/
/-
**CStarModule.innerSL** 是 Mathlib 中的一个定义，位于命名空间 `CStarModule`。
形式化陈述：innerSL : E ->L⋆[Complex] E ->L[Complex] A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A

--- 原说明 ---
The function `⟨x, y⟩ ↦ ⟪x, y⟫` bundled as a continuous sesquilinear map.
-/
noncomputable def innerSL : E →L⋆[ℂ] E →L[ℂ] A :=
  LinearMap.mkContinuous₂ (innerₛₗ : E →ₗ⋆[ℂ] E →ₗ[ℂ] A) 1 <| fun x y => by
    simp [innerₛₗ_apply, norm_inner_le E]
/-
**CStarModule.innerSL_apply** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：innerSL_apply {x y : E} : innerSL x y = ⟪x, y⟫_A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma innerSL_apply {x y : E} : innerSL x y = ⟪x, y⟫_A := rfl

@[continuity, fun_prop]
/-
**CStarModule.continuous_inner** 是 Mathlib 中的一个引理，位于命名空间 `CStarModule`。
形式化陈述：continuous_inner : Continuous (fun x : E × E => ⟪x.1, x.2⟫_A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
lemma continuous_inner : Continuous (fun x : E × E => ⟪x.1, x.2⟫_A) := by
  simp_rw [← innerSL_apply]
  fun_prop

end NormedAddCommGroup

end CStarModule

