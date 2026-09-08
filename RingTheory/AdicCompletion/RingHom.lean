/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Lift of ring homomorphisms to adic completions

Let `R`, `S` be rings, `I` be an ideal of `S`.
In this file we prove that a compatible family of ring homomorphisms from a ring `R` to
`S ⧸ I ^ n` can be lifted to a ring homomorphism `R →+* AdicCompletion I S`.
If `S` is `I`-adically complete, then this compatible family of ring homomorphisms can be
lifted to a ring homomorphism `R →+* S`.

## Main definitions

- `IsAdicComplete.liftRingHom`: if `R` is
  `I`-adically complete, then a compatible family of
  ring maps `S →+* R ⧸ I ^ n` can be lifted to a unique ring map `S →+* R`.
  Together with `mk_liftRingHom_apply` and `eq_liftRingHom`, it gives the universal property
  of `R` being `I`-adically complete.
-/

@[expose] public section

open Ideal Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

namespace IsAdicComplete

open AdicCompletion

section

variable [IsAdicComplete I S] (f : (n : ℕ) → R →+* S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n), (factorPow I hle).comp (f n) = f m)

/--
Universal property of `IsAdicComplete` for rings.
The lift ring map `lift I f hf : R →+* S` of a sequence of compatible
ring maps `f n : R →+* S ⧸ (I ^ n)`.
-/
/-
**IsAdicComplete.liftRingHom** 是 Mathlib 中的一个定义，位于命名空间 `IsAdicComplete`。
形式化陈述：liftRingHom : R ->+* S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
Universal property of `IsAdicComplete` for rings.
The lift ring map `lift I f hf : R →+* S` of a sequence of compatible
ring maps `f n : R →+* S ⧸ (I ^ n)`.
-/
noncomputable def liftRingHom :
    R →+* S :=
  ((ofAlgEquiv I).symm : _ →+* _).comp (AdicCompletion.liftRingHom I f hf)

@[simp]
/-
**IsAdicComplete.of_liftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：of_liftRingHom (x : R) : of I S (liftRingHom I f hf x) = (AdicCompletion.l
iftRingHom I f hf x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.of_ofAlgEquiv_symm`：of_ofAlgEquiv_symm (x : AdicCompletio
n I S) : of I S ((ofAlgEquiv I).symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_liftRingHom (x : R) :
    of I S (liftRingHom I f hf x) = (AdicCompletion.liftRingHom I f hf x) := by
  simp [liftRingHom]

@[simp]
/-
**IsAdicComplete.ofAlgEquiv_comp_liftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicCo
mplete`。
形式化陈述：ofAlgEquiv_comp_liftRingHom : (ofAlgEquiv I : S ->+* AdicCompletion I S).c
omp (liftRingHom I f hf) = AdicCompletion.liftRingHom I f hf
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AdicCompletion.ofAlgEquiv_apply`：ofAlgEquiv_apply (x : S) : ofAlgEquiv I
 x = of I S x
· 使用定理 `IsAdicComplete.of_liftRingHom`：of_liftRingHom (x : R) : of I S (liftRing
Hom I f hf x) = (AdicCompletion.liftRingHom I f hf x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofAlgEquiv_comp_liftRingHom :
    (ofAlgEquiv I : S →+* AdicCompletion I S).comp (liftRingHom I f hf) =
      AdicCompletion.liftRingHom I f hf := by
  ext; simp

/--
The composition of lift linear map `lift I f hf : R →+* S` with the canonical
projection `S →+* S ⧸ (I ^ n)` is `f n` .
-/
@[simp]
/-
**IsAdicComplete.mk_liftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：mk_liftRingHom (n : Nat) (x : R) : Ideal.Quotient.mk (I ^ n) (liftRingHom 
I f hf x) = f n x
参数：n : Nat；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdicCompletion.evalₐ_of`：evalₐ_of (n : Nat) (x : R) : evalₐ I n (of I R 
x) = Ideal.Quotient.mk _ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AdicCompletion.of_ofAlgEquiv_symm`：of_ofAlgEquiv_symm (x : AdicCompletio
n I S) : of I S ((ofAlgEquiv I).symm x) = x
· 使用定理 `AdicCompletion.evalₐ_liftRingHom`：evalₐ_liftRingHom (n : Nat) (x : R) : 
evalₐ I n (liftRingHom I f hf x) = f n x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of lift linear map `lift I f hf : R →+* S` with the canonical
projection `S →+* S ⧸ (I ^ n)` is `f n` .
-/
theorem mk_liftRingHom (n : ℕ) (x : R) :
    Ideal.Quotient.mk (I ^ n) (liftRingHom I f hf x) = f n x := by
  simp only [liftRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← evalₐ_of I n]
  simp

@[simp]
/-
**IsAdicComplete.mk_comp_liftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：mk_comp_liftRingHom (n : Nat) : (Ideal.Quotient.mk (I ^ n)).comp (liftRing
Hom I f hf) = f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAdicComplete.mk_liftRingHom`：mk_liftRingHom (n : Nat) (x : R) : Ideal.
Quotient.mk (I ^ n) (liftRingHom I f hf x) = f n x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_comp_liftRingHom (n : ℕ) :
    (Ideal.Quotient.mk (I ^ n)).comp (liftRingHom I f hf) = f n := by
  ext; simp

/--
Uniqueness of the lift.
Given a compatible family of linear maps `f n : R →ₗ[R] S ⧸ (I ^ n)`.
If `F : R →+* S` makes the following diagram commute
```
  R
  | \
 F|  \ f n
  |   \
  v    v
  S --> S ⧸ (I ^ n)
```
Then it is the map `IsAdicComplete.lift`.
-/
/-
**IsAdicComplete.eq_liftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：eq_liftRingHom (F : R ->+* S) (hF : forall n, (Ideal.Quotient.mk (I ^ n)).
comp F = f n) : F = liftRingHom I f hf
参数：F : R ->+* S；hF : forall n, (Ideal.Quotient.mk (I ^ n)).comp F = f n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `IsHausdorff.funext'`：IsHausdorff.funext' {R S : Type*} [CommRing S] (I :
 Ideal S) [IsHausdorff I S] {f g : R -> S} (h : forall n r, Ideal.Quotient.mk (I
 ^ n) (f …
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAdicComplete.mk_liftRingHom`：mk_liftRingHom (n : Nat) (x : R) : Ideal.
Quotient.mk (I ^ n) (liftRingHom I f hf x) = f n x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Uniqueness of the lift.
Given a compatible family of linear maps `f n : R →ₗ[R] S ⧸ (I ^ n)`.
If `F : R →+* S` makes the following diagram commute
```
  R
  | \
 F|  \ f n
  |   \
  v    v
  S --> S ⧸ (I ^ n)
```
Then it is the map `IsAdicComplete.lift`.
-/
theorem eq_liftRingHom (F : R →+* S)
    (hF : ∀ n, (Ideal.Quotient.mk (I ^ n)).comp F = f n) :
    F = liftRingHom I f hf := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n m
  simp [← hF n]

section

variable {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal S)
  [IsAdicComplete I S] [CommRing A] [Algebra R A]

/-- `AlgHom` version of `IsAdicCompletion.liftRingHom`. -/
noncomputable
/-
**IsAdicComplete.liftAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `IsAdicComplete`。
形式化陈述：liftAlgHom (f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n) (hf : forall {m n : Nat} 
(hle : m <= n), (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f 
n) = f m) : A ->ₐ[R] S
参数：f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n；hf : forall {m n : Nat} (hle : m <= n), (
Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftAlgHom (f : (n : ℕ) → A →ₐ[R] S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m) :
    A →ₐ[R] S :=
  ((ofAlgEquiv I).symm.toAlgHom.restrictScalars R).comp (AdicCompletion.liftAlgHom I f hf)

variable (f : (n : ℕ) → A →ₐ[R] S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m)

@[simp]
/-
**IsAdicComplete.mk_liftAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `IsAdicComplete`。
形式化陈述：mk_liftAlgHom (n : Nat) (x : A) : liftAlgHom I f hf x = f n x
参数：n : Nat；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.mk_ofAlgEquiv_symm`：mk_ofAlgEquiv_symm (n : Nat) (x : Adi
cCompletion I S) : Ideal.Quotient.mk (I ^ n) ((ofAlgEquiv I).symm x) = evalₐ I n
 x
· 使用引理 `AdicCompletion.evalₐ_liftAlgHom`：evalₐ_liftAlgHom (n : Nat) (x : A) : ev
alₐ I n (liftAlgHom I f hf x) = f n x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mk_liftAlgHom (n : ℕ) (x : A) : liftAlgHom I f hf x = f n x := by
  simp [liftAlgHom]

@[simp]
/-
**IsAdicComplete.mk** 是 Mathlib 中的一个ctor，位于命名空间 `IsAdicComplete`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {I : Ideal R} {M : Type u_4} [inst_1 
: AddCommGroup M] [inst_2 : _root_.Module R M]   [toIsHausdorff : IsHausdorff I 
M] [toIsPrecomplete : IsPrecomplete I M], IsAdicComplete I M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkₐ_comp_liftAlgHom (n : ℕ) :
    (Ideal.Quotient.mkₐ R (I ^ n)).comp (liftAlgHom I f hf) = f n :=
  AlgHom.ext fun _ ↦ mk_liftAlgHom _ _ hf _ _
/-
**IsAdicComplete.algHom_ext** 是 Mathlib 中的一个引理，位于命名空间 `IsAdicComplete`。
形式化陈述：algHom_ext {f g : A ->ₐ[R] S} (H : forall n, (Ideal.Quotient.mkₐ R (I ^ n)
).comp f = (Ideal.Quotient.mkₐ R (I ^ n)).comp g) : f = g
参数：H : forall n, (Ideal.Quotient.mkₐ R (I ^ n)).comp f = (Ideal.Quotient.mkₐ R (
I ^ n)).comp g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgHom.cancel_left`：cancel_left {g₁ g₂ : A ->ₐ[R] B} {f : B ->ₐ[R] C} (h
f : Function.Injective f) : f.comp g₁ = f.comp g₂ ↔ g₁ = g₂
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用引理 `AdicCompletion.ext_evalₐ`：ext_evalₐ {x y : AdicCompletion I R} (H : fora
ll n, evalₐ I n x = evalₐ I n y) : x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AdicCompletion.ofAlgEquiv_apply`：ofAlgEquiv_apply (x : S) : ofAlgEquiv I
 x = of I S x
· 使用定理 `AdicCompletion.evalₐ_of`：evalₐ_of (n : Nat) (x : R) : evalₐ I n (of I R 
x) = Ideal.Quotient.mk _ x
-/
lemma algHom_ext {f g : A →ₐ[R] S}
    (H : ∀ n, (Ideal.Quotient.mkₐ R (I ^ n)).comp f = (Ideal.Quotient.mkₐ R (I ^ n)).comp g) :
    f = g := by
  rw [← AlgHom.cancel_left (f := ((ofAlgEquiv I).restrictScalars R).toAlgHom)
    (ofAlgEquiv I).injective]
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  simpa using congr($(H n) x)

end

end

namespace StrictMono

variable {a : ℕ → ℕ} (ha : StrictMono a) (f : (n : ℕ) → R →+* S ⧸ I ^ a n)
variable (hf : ∀ {m}, (factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)) = f m)

variable {I}

include hf in
/--
`RingHom` variant of `IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq`.
-/
/-
**IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq'** 是 Mat
hlib 中的一个定理，位于命名空间 `IsAdicComplete.StrictMono`。
形式化陈述：factorPow_comp_eq_of_factorPow_comp_succ_eq' {m n : Nat} (hle : m <= n) : 
(factorPow I (ha.monotone hle)).comp (f n) = f m
参数：hle : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.eq_factor_of_eq_factor_succ`：Submodule.eq_factor_of_eq_factor_
succ {p : Nat -> Submodule R M} (hp : Antitone p) (x : (n : Nat) -> M ⧸ (p n)) (
h : forall m, x m = factor …
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
`RingHom` variant of `IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_c
omp_succ_eq`.
-/
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq'
    {m n : ℕ} (hle : m ≤ n) : (factorPow I (ha.monotone hle)).comp (f n) = f m := by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n ↦ f n x) ?_ hle
  · exact fun _ _ le ↦ Ideal.pow_le_pow_right (ha.monotone le)
  · intro s
    simp only [RingHom.ext_iff] at hf
    simpa using (hf x).symm

variable [IsAdicComplete I S]

variable (I)

set_option backward.isDefEq.respectTransparency false in
/--
A variant of `IsAdicComplete.liftRingHom`. Only takes `f n : R →+* S ⧸ I ^ (a n)`
from a strictly increasing sequence `a n`.
-/
/-
**IsAdicComplete.StrictMono.liftRingHom** 是 Mathlib 中的一个定义，位于命名空间 `IsAdicComplet
e.StrictMono`。
形式化陈述：liftRingHom : R ->+* S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ

--- 原说明 ---
A variant of `IsAdicComplete.liftRingHom`. Only takes `f n : R →+* S ⧸ I ^ (a n)
`
from a strictly increasing sequence `a n`.
-/
noncomputable def liftRingHom : R →+* S :=
  IsAdicComplete.liftRingHom I (fun n ↦ (factorPow I (ha.id_le n)).comp (f n))
    (fun hle ↦ by ext; simp [← factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf hle])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**IsAdicComplete.StrictMono.mk_liftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComp
lete.StrictMono`。
形式化陈述：mk_liftRingHom {n : Nat} (x : R) : Ideal.Quotient.mk _ (liftRingHom I ha f
 hf x) = f n x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `AdicCompletion.mk_ofAlgEquiv_symm`：mk_ofAlgEquiv_symm (n : Nat) (x : Adi
cCompletion I S) : Ideal.Quotient.mk (I ^ n) ((ofAlgEquiv I).symm x) = evalₐ I n
 x
· 使用定理 `AdicCompletion.evalₐ_liftRingHom`：evalₐ_liftRingHom (n : Nat) (x : R) : 
evalₐ I n (liftRingHom I f hf x) = f n x
· 使用定理 `IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq'`：
factorPow_comp_eq_of_factorPow_comp_succ_eq' {m n : Nat} (hle : m <= n) : (facto
rPow I (ha.monotone hle)).comp (f n) = f m
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_liftRingHom {n : ℕ} (x : R) :
    Ideal.Quotient.mk _ (liftRingHom I ha f hf x) = f n x := by
  simp [liftRingHom, IsAdicComplete.liftRingHom,
      factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf ha.le_apply]

@[simp]
/-
**IsAdicComplete.StrictMono.mk_comp_liftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsAdi
cComplete.StrictMono`。
形式化陈述：mk_comp_liftRingHom {n : Nat} : (Ideal.Quotient.mk (I ^ (a n))).comp (lift
RingHom I ha f hf) = f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAdicComplete.StrictMono.mk_liftRingHom`：mk_liftRingHom {n : Nat} (x : 
R) : Ideal.Quotient.mk _ (liftRingHom I ha f hf x) = f n x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_comp_liftRingHom {n : ℕ} :
    (Ideal.Quotient.mk (I ^ (a n))).comp (liftRingHom I ha f hf) = f n := by
  ext; simp
/-
**IsAdicComplete.StrictMono.eq_liftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComp
lete.StrictMono`。
形式化陈述：eq_liftRingHom {F : R ->+* S} (hF : forall n, (Ideal.Quotient.mk _).comp F
 = f n) : F = liftRingHom I ha f hf
参数：hF : forall n, (Ideal.Quotient.mk _).comp F = f n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `IsHausdorff.StrictMono.funext'`：IsHausdorff.StrictMono.funext' {R S : Ty
pe*} [CommRing S] (I : Ideal S) [IsHausdorff I S] {f g : R -> S} {a : Nat -> Nat
} (ha : StrictMono a…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAdicComplete.StrictMono.mk_liftRingHom`：mk_liftRingHom {n : Nat} (x : 
R) : Ideal.Quotient.mk _ (liftRingHom I ha f hf x) = f n x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_liftRingHom {F : R →+* S}
    (hF : ∀ n, (Ideal.Quotient.mk _).comp F = f n) : F = liftRingHom I ha f hf := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' I ha
  intro n m
  simp [← hF n]

end StrictMono

end IsAdicComplete

