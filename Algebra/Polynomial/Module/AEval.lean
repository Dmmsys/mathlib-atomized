/-
Copyright (c) 2022 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Action of the polynomial ring on module induced by an algebra element.

Given an element `a` in an `R`-algebra `A` and an `A`-module `M` we define an
`R[X]`-module `Module.AEval R M a`, which is a type synonym of `M` with the
action of a polynomial `f` given by `f • m = Polynomial.aeval a f • m`.
In particular `X • m = a • m`.

In the special case that `A = M →ₗ[R] M` and `φ : M →ₗ[R] M`, the module `Module.AEval R M a` is
abbreviated `Module.AEval' φ`. In this module we have `X • m = ↑φ m`.
-/

@[expose] public section

open Set Function Polynomial

namespace Module
/--
Suppose `a` is an element of an `R`-algebra `A` and `M` is an `A`-module.
Loosely speaking, `Module.AEval R M a` is the `R[X]`-module with elements `m : M`,
where the action of a polynomial $f$ is given by $f • m = f(a) • m$.

More precisely, `Module.AEval R M a` has elements `Module.AEval.of R M a m` for `m : M`,
and the action of `f` is `f • (of R M a m) = of R M a ((aeval a f) • m)`.
-/
@[nolint unusedArguments]
/-
**Module.AEval** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：AEval (R M : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A
] [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M] (_ : A)
参数：R M : Type*；_ : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `a` is an element of an `R`-algebra `A` and `M` is an `A`-module.
Loosely speaking, `Module.AEval R M a` is the `R[X]`-module with elements `m : M
`,
where the action of a polynomial $f$ is given by $f • m = f(a) • m$.

More precisely, `Module.AEval R M a` has elements `Module.AEval.of R M a m` for 
`m : M`,
and the action of `f` is `f • (of R M a m) = of R M a ((aeval a f) • m)`.
-/
def AEval (R M : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M] (_ : A) := M
  deriving AddCommMonoid, Module R
/-
**Module.AEval.instAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Module.AEval`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {M : Type u_3} →       [inst : Com
mSemiring R] →         [inst_1 : Semiring A] →           (a : A) →             [
inst_2 : Algebra R A] →               [inst_3 : AddCommGroup M] →               
  [inst_4 : _root_.Module A M] →                   [inst_5 : _root_.Module R M] 
→ [inst_6 : IsScalarTower R A M] → AddCommGroup (Module.AEval R M a)
参数：a : A；Module.AEval R M a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AEval.instAddCommGroup {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    AddCommGroup <| AEval R M a := inferInstanceAs (AddCommGroup M)

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

namespace AEval

/-
**Module.AEval.instFiniteOrig** 是 Mathlib 中的一个实例，位于命名空间 `Module.AEval`。
形式化陈述：instFiniteOrig [Module.Finite R M] : Module.Finite R AEval R M a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFiniteOrig [Module.Finite R M] : Module.Finite R <| AEval R M a :=
  inferInstanceAs <| Module.Finite R M
/-
**Module.AEval.instModulePolynomial** 是 Mathlib 中的一个实例，位于命名空间 `Module.AEval`。
形式化陈述：instModulePolynomial : Module R[X] AEval R M a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instModulePolynomial : Module R[X] <| AEval R M a :=
  compHom M (aeval a).toRingHom

variable (R M)
/--
The canonical linear equivalence between `M` and `Module.AEval R M a` as an `R`-module.
-/
/-
**Module.AEval.of** 是 Mathlib 中的一个定义，位于命名空间 `Module.AEval`。
形式化陈述：of : M ≃ₗ[R] AEval R M a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear equivalence between `M` and `Module.AEval R M a` as an `R`-
module.
-/
def of : M ≃ₗ[R] AEval R M a :=
  LinearEquiv.refl _ _

variable {R M}
/-
**Module.AEval.of_aeval_smul** 是 Mathlib 中的一个引理，位于命名空间 `Module.AEval`。
形式化陈述：of_aeval_smul (f : R[X]) (m : M) : of R M a (aeval a f • m) = f • of R M a
 m
参数：f : R[X]；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_aeval_smul (f : R[X]) (m : M) : of R M a (aeval a f • m) = f • of R M a m := rfl
/-
**Module.AEval.of_symm_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.AEval`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {M : Type u_2} [inst : CommSemiring R] [in
st_1 : Semiring A] (a : A)   [inst_2 : Algebra R A] [inst_3 : AddCommMonoid M] [
inst_4 : _root_.Module A M] [inst_5 : _root_.Module R M]   [inst_6 : IsScalarTow
er R A M] (f : Polynomial R) (m : Module.AEval R M a),   (Module.AEval.of R M a)
.symm (f • m) = (Polynomial.aeval a) f • (Module.AEval.of R M a).symm m
参数：a : A；f : Polynomial R；m : Module.AEval R M a；Module.AEval.of R M a；f • m；Pol
ynomial.aeval a；Module.AEval.of R M a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma of_symm_smul (f : R[X]) (m : AEval R M a) :
    (of R M a).symm (f • m) = aeval a f • (of R M a).symm m := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Module.AEval.C_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.AEval`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {M : Type u_2} [inst : CommSemiring R] [in
st_1 : Semiring A] (a : A)   [inst_2 : Algebra R A] [inst_3 : AddCommMonoid M] [
inst_4 : _root_.Module A M] [inst_5 : _root_.Module R M]   [inst_6 : IsScalarTow
er R A M] (t : R) (m : Module.AEval R M a), Polynomial.C t • m = t • m
参数：a : A；t : R；m : Module.AEval R M a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma C_smul (t : R) (m : AEval R M a) : C t • m = t • m :=
  (of R M a).symm.injective <| by simp
/-
**Module.AEval.X_smul_of** 是 Mathlib 中的一个引理，位于命名空间 `Module.AEval`。
形式化陈述：X_smul_of (m : M) : (X : R[X]) • (of R M a m) = of R M a (a • m)
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.AEval.of_aeval_smul`：of_aeval_smul (f : R[X]) (m : M) : of R M a 
(aeval a f • m) = f • of R M a m
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
lemma X_smul_of (m : M) : (X : R[X]) • (of R M a m) = of R M a (a • m) := by
  rw [← of_aeval_smul, aeval_X]
/-
**Module.AEval.X_pow_smul_of** 是 Mathlib 中的一个引理，位于命名空间 `Module.AEval`。
形式化陈述：X_pow_smul_of (m : M) (n : Nat) : (X ^ n : R[X]) • (of R M a m) = of R M a
 (a ^ n • m)
参数：m : M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.AEval.of_aeval_smul`：of_aeval_smul (f : R[X]) (m : M) : of R M a 
(aeval a f • m) = f • of R M a m
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
-/
lemma X_pow_smul_of (m : M) (n : ℕ) : (X ^ n : R[X]) • (of R M a m) = of R M a (a ^ n • m) := by
  rw [← of_aeval_smul, aeval_X_pow]
/-
**Module.AEval.of_symm_X_smul** 是 Mathlib 中的一个引理，位于命名空间 `Module.AEval`。
形式化陈述：of_symm_X_smul (m : AEval R M a) : (of R M a).symm ((X : R[X]) • m) = a • 
(of R M a).symm m
参数：m : AEval R M a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.AEval.of_symm_smul`：∀ {R : Type u_1} {A : Type u_3} {M : Type u_2
} [inst : CommSemiring R] [inst_1 : Semiring A] (a : A)   [inst_2 : Algebra R A]
 [inst_3 : AddC…
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
lemma of_symm_X_smul (m : AEval R M a) :
    (of R M a).symm ((X : R[X]) • m) = a • (of R M a).symm m := by
  rw [of_symm_smul, aeval_X]
/-
**Module.AEval.instIsScalarTowerOrigPolynomial** 是 Mathlib 中的一个实例，位于命名空间 `Module
.AEval`。
形式化陈述：instIsScalarTowerOrigPolynomial : IsScalarTower R R[X] AEval R M a where s
mul_assoc r f m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.AEval.of_symm_smul`：∀ {R : Type u_1} {A : Type u_3} {M : Type u_2
} [inst : CommSemiring R] [inst_1 : Semiring A] (a : A)   [inst_2 : Algebra R A]
 [inst_3 : AddC…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
instance instIsScalarTowerOrigPolynomial : IsScalarTower R R[X] <| AEval R M a where
  smul_assoc r f m := by
    apply (of R M a).symm.injective
    rw [of_symm_smul, map_smul, smul_assoc, map_smul, of_symm_smul]
/-
**Module.AEval.instFinitePolynomial** 是 Mathlib 中的一个实例，位于命名空间 `Module.AEval`。
形式化陈述：instFinitePolynomial [Module.Finite R M] : Module.Finite R[X] AEval R M a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
-/
instance instFinitePolynomial [Module.Finite R M] : Module.Finite R[X] <| AEval R M a :=
  Finite.of_restrictScalars_finite R _ _

/-- Construct an `R[X]`-linear map out of `AEval R M a` from an `R`-linear map out of `M`. -/
/-
**Module.AEval._root_.LinearMap.ofAEval** 是 Mathlib 中的一个定义，位于命名空间 `Module.AEval`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an `R[X]`-linear map out of `AEval R M a` from an `R`-linear map out o
f `M`.
-/
def _root_.LinearMap.ofAEval {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
    [IsScalarTower R R[X] N] (f : M →ₗ[R] N) (hf : ∀ m : M, f (a • m) = (X : R[X]) • f m) :
    AEval R M a →ₗ[R[X]] N where
  __ := f ∘ₗ (of R M a).symm
  map_smul' p := p.induction_on (fun k m ↦ by simp [C_eq_algebraMap])
    (fun p q hp hq m ↦ by simp_all [add_smul]) fun n k h m ↦ by
      simp_rw [RingHom.id_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h ⊢
      simp_rw [pow_succ, ← mul_assoc, mul_smul _ X, ← hf, ← of_symm_X_smul, ← h]

/-- Construct an `R[X]`-linear equivalence out of `AEval R M a` from an `R`-linear map out of `M`.
-/
/-
**Module.AEval._root_.LinearEquiv.ofAEval** 是 Mathlib 中的一个定义，位于命名空间 `Module.AEva
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an `R[X]`-linear equivalence out of `AEval R M a` from an `R`-linear m
ap out of `M`.
-/
def _root_.LinearEquiv.ofAEval {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
    [IsScalarTower R R[X] N] (f : M ≃ₗ[R] N) (hf : ∀ m : M, f (a • m) = (X : R[X]) • f m) :
    AEval R M a ≃ₗ[R[X]] N where
  __ := LinearMap.ofAEval a f hf
  invFun := (of R M a) ∘ f.symm
  left_inv x := by simp [LinearMap.ofAEval]
  right_inv x := by simp [LinearMap.ofAEval]
/-
**Module.AEval.annihilator_eq_ker_aeval** 是 Mathlib 中的一个引理，位于命名空间 `Module.AEval`
。
形式化陈述：annihilator_eq_ker_aeval [FaithfulSMul A M] : annihilator R[X] (AEval R M 
a) = RingHom.ker (aeval a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma annihilator_eq_ker_aeval [FaithfulSMul A M] :
    annihilator R[X] (AEval R M a) = RingHom.ker (aeval a) := by
  ext p
  simp_rw [mem_annihilator, RingHom.mem_ker]
  change (∀ m : M, aeval a p • m = 0) ↔ _
  exact ⟨fun h ↦ eq_of_smul_eq_smul (α := M) <| by simp [h], fun h ↦ by simp [h]⟩

@[simp]
/-
**Module.AEval.annihilator_top_eq_ker_aeval** 是 Mathlib 中的一个引理，位于命名空间 `Module.AE
val`。
形式化陈述：annihilator_top_eq_ker_aeval [FaithfulSMul A M] : (⊤ : Submodule R[X] <| A
Eval R M a).annihilator = RingHom.ker (aeval a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma annihilator_top_eq_ker_aeval [FaithfulSMul A M] :
    (⊤ : Submodule R[X] <| AEval R M a).annihilator = RingHom.ker (aeval a) := by
  ext p
  simp only [Submodule.mem_annihilator, Submodule.mem_top, forall_true_left, RingHom.mem_ker]
  change (∀ m : M, aeval a p • m = 0) ↔ _
  exact ⟨fun h ↦ eq_of_smul_eq_smul (α := M) <| by simp [h], fun h ↦ by simp [h]⟩

section Submodule

variable (R M)

set_option backward.isDefEq.respectTransparency false in
/-- The natural order isomorphism between the two ways to represent invariant submodules. -/
/-
**Module.AEval.mapSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Module.AEval`。
形式化陈述：mapSubmodule : (Algebra.lsmul R R M a).invtSubmodule ≃o Submodule R[X] (AE
val R M a) where toFun p
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
The natural order isomorphism between the two ways to represent invariant submod
ules.
-/
noncomputable def mapSubmodule :
    (Algebra.lsmul R R M a).invtSubmodule ≃o Submodule R[X] (AEval R M a) where
  toFun p :=
    { toAddSubmonoid := (p : Submodule R M).toAddSubmonoid.map (of R M a)
      smul_mem' := by
        rintro f - ⟨m : M, h : m ∈ (p : Submodule R M), rfl⟩
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid]
        exact ⟨aeval a f • m, aeval_apply_smul_mem_of_le_comap' h f a p.2, of_aeval_smul a f m⟩ }
  invFun q := ⟨(Submodule.orderIsoMapComap (of R M a)).symm (q.restrictScalars R), fun m hm ↦ by
    simpa [← X_smul_of] using! q.smul_mem (X : R[X]) hm⟩
  left_inv p := by ext; simp
  right_inv q := by ext; aesop
  map_rel_iff' {p p'} := ⟨fun h x hx ↦ by aesop (rule_sets := [SetLike!]), fun h x hx ↦ by aesop⟩
/-
**Module.AEval.mem_mapSubmodule_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.AEval`。
形式化陈述：∀ (R : Type u_2) {A : Type u_3} (M : Type u_1) [inst : CommSemiring R] [in
st_1 : Semiring A] (a : A)   [inst_2 : Algebra R A] [inst_3 : AddCommMonoid M] [
inst_4 : _root_.Module A M] [inst_5 : _root_.Module R M]   [inst_6 : IsScalarTow
er R A M] {p : ↥((Algebra.lsmul R R M) a).invtSubmodule} {m : Module.AEval R M a
},   m ∈ (Module.AEval.mapSubmodule R M a) p ↔ (Module.AEval.of R M a).symm m ∈ 
↑p
参数：R : Type u_2；M : Type u_1；a : A；(Algebra.lsmul R R M) a；Module.AEval.mapSubmo
dule R M a；Module.AEval.of R M a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma mem_mapSubmodule_apply {p : (Algebra.lsmul R R M a).invtSubmodule} {m : AEval R M a} :
    m ∈ mapSubmodule R M a p ↔ (of R M a).symm m ∈ (p : Submodule R M) :=
  ⟨fun ⟨_, hm, hm'⟩ ↦ hm'.symm ▸ hm, fun hm ↦ ⟨(of R M a).symm m, hm, rfl⟩⟩
/-
**Module.AEval.mem_mapSubmodule_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.AEv
al`。
形式化陈述：∀ (R : Type u_1) {A : Type u_3} (M : Type u_2) [inst : CommSemiring R] [in
st_1 : Semiring A] (a : A)   [inst_2 : Algebra R A] [inst_3 : AddCommMonoid M] [
inst_4 : _root_.Module A M] [inst_5 : _root_.Module R M]   [inst_6 : IsScalarTow
er R A M] {q : Submodule (Polynomial R) (Module.AEval R M a)} {m : M},   m ∈ ↑((
Module.AEval.mapSubmodule R M a).symm q) ↔ (Module.AEval.of R M a) m ∈ q
参数：R : Type u_1；M : Type u_2；a : A；Polynomial R；Module.AEval R M a；(Module.AEval
.mapSubmodule R M a).symm q；Module.AEval.of R M a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
@[simp] lemma mem_mapSubmodule_symm_apply {q : Submodule R[X] (AEval R M a)} {m : M} :
    m ∈ ((mapSubmodule R M a).symm q : Submodule R M) ↔ of R M a m ∈ q :=
  Iff.rfl

variable {R M}
variable (p : Submodule R M) (hp : p ∈ (Algebra.lsmul R R M a).invtSubmodule)

/-- The natural `R`-linear equivalence between the two ways to represent an invariant submodule. -/
/-
**Module.AEval.equiv_mapSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Module.AEval`。
形式化陈述：equiv_mapSubmodule : p ≃ₗ[R] mapSubmodule R M a ⟨p, hp⟩ where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
The natural `R`-linear equivalence between the two ways to represent an invarian
t submodule.
-/
def equiv_mapSubmodule :
    p ≃ₗ[R] mapSubmodule R M a ⟨p, hp⟩ where
  toFun x := ⟨of R M a x, by simp⟩
  invFun x := ⟨((of R M _).symm (x : AEval R M a)), by obtain ⟨x, hx⟩ := x; simpa using hx⟩
  map_add' x y := rfl
  map_smul' t x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The natural `R[X]`-linear equivalence between the two ways to represent an invariant submodule.
-/
/-
**Module.AEval.restrict_equiv_mapSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Module.AEv
al`。
形式化陈述：restrict_equiv_mapSubmodule : (AEval R p <| (Algebra.lsmul R R M a).restri
ct hp) ≃ₗ[R[X]] mapSubmodule R M a ⟨p, hp⟩
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
The natural `R[X]`-linear equivalence between the two ways to represent an invar
iant submodule.
-/
noncomputable def restrict_equiv_mapSubmodule :
    (AEval R p <| (Algebra.lsmul R R M a).restrict hp) ≃ₗ[R[X]] mapSubmodule R M a ⟨p, hp⟩ :=
  LinearEquiv.ofAEval ((Algebra.lsmul R R M a).restrict hp) (equiv_mapSubmodule a p hp)
    (fun x ↦ by simp [equiv_mapSubmodule, X_smul_of])

end Submodule

end AEval

variable (φ : M →ₗ[R] M)
/--
Given and `R`-module `M` and a linear map `φ : M →ₗ[R] M`, `Module.AEval' φ` is loosely speaking
the `R[X]`-module with elements `m : M`, where the action of a polynomial $f$ is given by
$f • m = f(a) • m$.

More precisely, `Module.AEval' φ` has elements `Module.AEval'.of φ m` for `m : M`,
and the action of `f` is `f • (of φ m) = of φ ((aeval φ f) • m)`.

`Module.AEval'` is defined as a special case of `Module.AEval` in which the `R`-algebra is
`M →ₗ[R] M`. Lemmas involving `Module.AEval` may be applied to `Module.AEval'`.
-/
/-
**Module.AEval'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module`。
形式化陈述：AEval'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given and `R`-module `M` and a linear map `φ : M →ₗ[R] M`, `Module.AEval' φ` is 
loosely speaking
the `R[X]`-module with elements `m : M`, where the action of a polynomial $f$ is
 given by
$f • m = f(a) • m$.

More precisely, `Module.AEval' φ` has elements `Module.AEval'.of φ m` for `m : M
`,
and the action of `f` is `f • (of φ m) = of φ ((aeval φ f) • m)`.

`Module.AEval'` is defined as a special case of `Module.AEval` in which the `R`-
algebra is
`M →ₗ[R] M`. Lemmas involving `Module.AEval` may be applied to `Module.AEval'`.
-/
abbrev AEval' := AEval R M φ
/--
The canonical linear equivalence between `M` and `Module.AEval' φ` as an `R`-module,
where `φ : M →ₗ[R] M`.
-/
/-
**Module.AEval'.of** 是 Mathlib 中的一个定义，位于命名空间 `Module.AEval'`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → (φ : M →ₗ[R] M) → M ≃ₗ
[R] Module.AEval' φ
参数：φ : M →ₗ[R] M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear equivalence between `M` and `Module.AEval' φ` as an `R`-mod
ule,
where `φ : M →ₗ[R] M`.
-/
abbrev AEval'.of : M ≃ₗ[R] AEval' φ := AEval.of R M φ
/-
**Module.AEval'_def** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ {R : Type u_2} {M : Type u_1} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (φ : M →ₗ[R] M), Module.AEval' φ = Modul
e.AEval R M φ
参数：φ : M →ₗ[R] M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AEval'_def : AEval' φ = AEval R M φ := rfl
/-
**Module.AEval'.X_smul_of** 是 Mathlib 中的一个定理，位于命名空间 `Module.AEval'`。
形式化陈述：∀ {R : Type u_2} {M : Type u_1} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (φ : M →ₗ[R] M) (m : M), Polynomial.X • 
(Module.AEval'.of φ) m = (Module.AEval'.of φ) (φ m)
参数：φ : M →ₗ[R] M；m : M；Module.AEval'.of φ；Module.AEval'.of φ；φ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.AEval.X_smul_of`：X_smul_of (m : M) : (X : R[X]) • (of R M a m) = 
of R M a (a • m)
-/
lemma AEval'.X_smul_of (m : M) : (X : R[X]) • AEval'.of φ m = AEval'.of φ (φ m) :=
  AEval.X_smul_of _ _
/-
**Module.AEval'.X_pow_smul_of** 是 Mathlib 中的一个定理，位于命名空间 `Module.AEval'`。
形式化陈述：∀ {R : Type u_2} {M : Type u_1} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (φ : M →ₗ[R] M) (m : M) (n : ℕ), Polynom
ial.X ^ n • (Module.AEval'.of φ) m = (Module.AEval'.of φ) (φ ^ n • m)
参数：φ : M →ₗ[R] M；m : M；n : ℕ；Module.AEval'.of φ；Module.AEval'.of φ；φ ^ n • m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.AEval.X_pow_smul_of`：X_pow_smul_of (m : M) (n : Nat) : (X ^ n : R
[X]) • (of R M a m) = of R M a (a ^ n • m)
-/
lemma AEval'.X_pow_smul_of (m : M) (n : ℕ) : (X ^ n : R[X]) • AEval'.of φ m = .of φ (φ ^ n • m) :=
  AEval.X_pow_smul_of ..
/-
**Module.AEval'.of_symm_X_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.AEval'`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (φ : M →ₗ[R] M) (m : Module.AEval' φ), (
Module.AEval'.of φ).symm (Polynomial.X • m) = φ ((Module.AEval'.of φ).symm m)
参数：φ : M →ₗ[R] M；m : Module.AEval' φ；Module.AEval'.of φ；Polynomial.X • m；(Module
.AEval'.of φ).symm m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.AEval.of_symm_X_smul`：of_symm_X_smul (m : AEval R M a) : (of R M 
a).symm ((X : R[X]) • m) = a • (of R M a).symm m
-/
lemma AEval'.of_symm_X_smul (m : AEval' φ) :
    (AEval'.of φ).symm ((X : R[X]) • m) = φ ((AEval'.of φ).symm m) := AEval.of_symm_X_smul _ _
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Finite R M] : Module.Finite R[X] <| AEval' φ := inferInstance

end Module

