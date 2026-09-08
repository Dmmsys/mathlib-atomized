/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Facts about algebras involving bilinear maps and tensor products

We move a few basic statements about algebras out of `Algebra.Algebra.Basic`,
in order to avoid importing `LinearAlgebra.BilinearMap` and
`LinearAlgebra.TensorProduct` unnecessarily.
-/

@[expose] public section

open TensorProduct Module

variable {R A B : Type*}

namespace LinearMap

section NonUnitalNonAssoc

variable (R A) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`. -/
@[instance_reducible, simps!]
/-
**LinearMap.mul** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：mul : A ->ₗ[R] A ->ₗ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`.
-/
def mul : A →ₗ[R] A →ₗ[R] A :=
  LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm

/-- The multiplication map on a non-unital algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
/-
**LinearMap.mul'** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：mul' : A otimes[R] A ->ₗ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication map on a non-unital algebra, as an `R`-linear map from `A ⊗[R
] A` to `A`.
-/
def mul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (mul R A)

@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ" => LinearMap.mul' _ _
@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ[" R "]" => LinearMap.mul' R _

variable {A R}

@[simp]
/-
**LinearMap.mul_apply'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mul_apply' (a b : A) : mul R A a b = a * b
参数：a b : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply' (a b : A) : mul R A a b = a * b :=
  rfl

@[simp]
/-
**LinearMap.mul'_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : NonUnita
lNonAssocSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : SMulCommClass R A 
A] [inst_4 : IsScalarTower R A A] {a b : A},   (LinearMap.mul' R A) (a ⊗ₜ[R] b) 
= a * b
参数：LinearMap.mul' R A；a ⊗ₜ[R] b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul'_apply {a b : A} : mul' R A (a ⊗ₜ b) = a * b :=
  rfl
/-
**LinearMap.restrictScalars_mul** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_mul {S : Type*} [CommSemiring S] [Module S A] [SMulCommCla
ss S A A] [IsScalarTower S A A] [CompatibleSMul A A R S] (a : A) : LinearMap.res
trictScalars R (LinearMap.mul S A a) = LinearMap.mul R A a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrictScalars_mul {S : Type*} [CommSemiring S] [Module S A] [SMulCommClass S A A]
    [IsScalarTower S A A] [CompatibleSMul A A R S] (a : A) :
    LinearMap.restrictScalars R (LinearMap.mul S A a) = LinearMap.mul R A a := by
  ext x
  simp

variable {M : Type*} [AddCommMonoid M] [Module R M]
/-
**LinearMap.lift_lsmul_mul_eq_lsmul_lift_lsmul** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：lift_lsmul_mul_eq_lsmul_lift_lsmul {r : R} : lift (lsmul R M ∘ₗ mul R R r)
 = lsmul R M r ∘ₗ lift (lsmul R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_lsmul_mul_eq_lsmul_lift_lsmul {r : R} :
    lift (lsmul R M ∘ₗ mul R R r) = lsmul R M r ∘ₗ lift (lsmul R M) := by
  apply TensorProduct.ext'
  intro x a
  simp [← mul_smul, mul_comm]

end NonUnitalNonAssoc

section NonUnital

variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]
variable [SMulCommClass R B B] [IsScalarTower R B B]

variable (R A) in
/-- The multiplication in a non-unital algebra is a bilinear map.

A weaker version of this for non-unital non-associative algebras exists as `LinearMap.mul`. -/
/-
**LinearMap._root_.NonUnitalAlgHom.lmul** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication in a non-unital algebra is a bilinear map.

A weaker version of this for non-unital non-associative algebras exists as `Line
arMap.mul`.
-/
def _root_.NonUnitalAlgHom.lmul : A →ₙₐ[R] End R A where
  __ := mul R A
  map_mul' := mulLeft_mul _ _
  map_zero' := mulLeft_zero_eq_zero _ _

@[simp]
/-
**LinearMap._root_.NonUnitalAlgHom.coe_lmul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NonUnitalAlgHom.coe_lmul_eq_mul : ⇑(NonUnitalAlgHom.lmul R A) = mul R A :=
  rfl
/-
**LinearMap.commute_mulLeft_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：commute_mulLeft_right (a b : A) : Commute (mulLeft R a) (mulRight R b)
参数：a b : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem commute_mulLeft_right (a b : A) : Commute (mulLeft R a) (mulRight R b) := by
  ext c
  exact (mul_assoc a c b).symm

/-- A `LinearMap` preserves multiplication if pre- and post- composition with `LinearMap.mul` are
equivalent. By converting the statement into an equality of `LinearMap`s, this lemma allows various
specialized `ext` lemmas about `→ₗ[R]` to then be applied.

This is the `LinearMap` version of `AddMonoidHom.map_mul_iff`. -/
/-
**LinearMap.map_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_mul_iff (f : A ->ₗ[R] B) : (forall x y, f (x * y) = f x * f y) ↔ (Line
arMap.mul R A).compr₂ f = (LinearMap.mul R B ∘ₗ f).compl₂ f
参数：f : A ->ₗ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LinearMap.ext_iff₂`：ext_iff₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} : f = g ↔
 forall m n, f m n = g m n

--- 原说明 ---
A `LinearMap` preserves multiplication if pre- and post- composition with `Linea
rMap.mul` are
equivalent. By converting the statement into an equality of `LinearMap`s, this l
emma allows various
specialized `ext` lemmas about `→ₗ[R]` to then be applied.

This is the `LinearMap` version of `AddMonoidHom.map_mul_iff`.
-/
theorem map_mul_iff (f : A →ₗ[R] B) :
    (∀ x y, f (x * y) = f x * f y) ↔
      (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B ∘ₗ f).compl₂ f :=
  Iff.symm LinearMap.ext_iff₂

end NonUnital

section Semiring

variable (R A)
section one_side
variable [Semiring R] [Semiring A]

section left
variable [Module R A] [SMulCommClass R A A]

@[simp]
/-
**LinearMap.pow_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pow_mulLeft (a : A) (n : Nat) : mulLeft R a ^ n = mulLeft R (a ^ n)
参数：a : A；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_mulLeft (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n) :=
  match n with
  | 0 => by rw [pow_zero, pow_zero, mulLeft_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ, mulLeft_mul, Module.End.mul_eq_comp, pow_mulLeft]

end left

section right
variable [Module R A] [IsScalarTower R A A]

@[simp]
/-
**LinearMap.pow_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pow_mulRight (a : A) (n : Nat) : mulRight R a ^ n = mulRight R (a ^ n)
参数：a : A；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_mulRight (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n) :=
  match n with
  | 0 => by rw [pow_zero, pow_zero, mulRight_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ', mulRight_mul, Module.End.mul_eq_comp, pow_mulRight]

end right

end one_side

variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- The multiplication in an algebra is an algebra homomorphism into the endomorphisms on
the algebra.

A weaker version of this for non-unital algebras exists as `NonUnitalAlgHom.lmul`. -/
/-
**LinearMap._root_.Algebra.lmul** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication in an algebra is an algebra homomorphism into the endomorphis
ms on
the algebra.

A weaker version of this for non-unital algebras exists as `NonUnitalAlgHom.lmul
`.
-/
def _root_.Algebra.lmul : A →ₐ[R] End R A where
  __ := NonUnitalAlgHom.lmul R A
  map_one' := mulLeft_one _ _
  commutes' r := ext fun a => (Algebra.smul_def r a).symm

variable {R A}

@[simp]
/-
**LinearMap._root_.Algebra.coe_lmul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Algebra.coe_lmul_eq_mul : ⇑(Algebra.lmul R A) = mul R A :=
  rfl
/-
**LinearMap._root_.Algebra.lmul_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Algebra.lmul_injective : Function.Injective (Algebra.lmul R A) :=
  fun a₁ a₂ h ↦ by simpa using DFunLike.congr_fun h 1
/-
**LinearMap._root_.Algebra.lmul_isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Algebra.lmul_isUnit_iff {x : A} :
    IsUnit (Algebra.lmul R A x) ↔ IsUnit x := by
  rw [Module.End.isUnit_iff, Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective
/-
**LinearMap.toSpanSingleton_one_eq_algebraLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
形式化陈述：toSpanSingleton_one_eq_algebraLinearMap : toSpanSingleton R A 1 = Algebra.
linearMap R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSpanSingleton_one_eq_algebraLinearMap :
    toSpanSingleton R A 1 = Algebra.linearMap R A := by ext; simp

variable (R A) in
/-- The multiplication map on an `R`-algebra, as an `A`-linear map from `A ⊗[R] A` to `A`. -/
/-
**LinearMap.mul''** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     [inst : CommSemiring R] → [inst_1 
: Semiring A] → [inst_2 : Algebra R A] → TensorProduct R A A →ₗ[A] A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The multiplication map on an `R`-algebra, as an `A`-linear map from `A ⊗[R] A` t
o `A`.
-/
@[simps!] def mul'' : A ⊗[R] A →ₗ[A] A where
  __ := mul' R A
  map_smul' a x := x.induction_on (by simp) (by simp +contextual [mul', smul_tmul', mul_assoc])
    (by simp +contextual [mul_add])

end Semiring

section CommSemiring
variable [CommSemiring R] [NonUnitalNonAssocCommSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-
**LinearMap.flip_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : NonUnita
lNonAssocCommSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : SMulCommClass 
R A A] [inst_4 : IsScalarTower R A A],   (LinearMap.mul R A).flip = LinearMap.mu
l R A
参数：LinearMap.mul R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma flip_mul : (mul R A).flip = mul R A := by ext; simp [mul_comm]
/-
**LinearMap.mul'_comp_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : NonUnita
lNonAssocCommSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : SMulCommClass 
R A A] [inst_4 : IsScalarTower R A A],   LinearMap.mul' R A ∘ₗ ↑(TensorProduct.c
omm R A A) = LinearMap.mul' R A
参数：TensorProduct.comm R A A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.lift_comp_comm_eq`：lift_comp_comm_eq (f : M ->ₛₗ[σ₁₂] N ->
ₛₗ[σ₁₂] P₂) : lift f ∘ₛₗ (TensorProduct.comm R N M).toLinearMap = lift f.flip
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.flip_mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring
 R] [inst_1 : NonUnitalNonAssocCommSemiring A]   [inst_2 : _root_.Module R A] [i
nst_3 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul'_comp_comm : mul' R A ∘ₗ TensorProduct.comm R A A = mul' R A := by
  simp [mul', lift_comp_comm_eq]
/-
**LinearMap.mul'_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : NonUnita
lNonAssocCommSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : SMulCommClass 
R A A] [inst_4 : IsScalarTower R A A] (x : TensorProduct R A A),   (LinearMap.mu
l' R A) ((TensorProduct.comm R A A) x) = (LinearMap.mul' R A) x
参数：x : TensorProduct R A A；LinearMap.mul' R A；(TensorProduct.comm R A A) x；Linea
rMap.mul' R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mul'_comp_comm`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSe
miring R] [inst_1 : NonUnitalNonAssocCommSemiring A]   [inst_2 : _root_.Module R
 A] [inst_3 : …
-/
lemma mul'_comm (x : A ⊗[R] A) : mul' R A (TensorProduct.comm R A A x) = mul' R A x :=
  congr($mul'_comp_comm _)

end CommSemiring
end LinearMap

open scoped RingTheory.LinearMap

namespace NonUnitalAlgHom
variable [CommSemiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/-
**NonUnitalAlgHom.comp_mul'** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：comp_mul' (f : A ->ₙₐ[R] B) : (f : A ->ₗ[R] B) ∘ₗ μ = μ[R] ∘ₗ (f otimesₘ f
)
参数：f : A ->ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma comp_mul' (f : A →ₙₐ[R] B) : (f : A →ₗ[R] B) ∘ₗ μ = μ[R] ∘ₗ (f ⊗ₘ f) :=
  TensorProduct.ext' <| by simp

end NonUnitalAlgHom

namespace AlgHom
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-
**AlgHom.comp_mul'** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：comp_mul' (f : A ->ₐ B) : f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ (f.toLinearMap otim
esₘ f.toLinearMap)
参数：f : A ->ₐ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma comp_mul' (f : A →ₐ B) : f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap) :=
  TensorProduct.ext' <| by simp

end AlgHom

