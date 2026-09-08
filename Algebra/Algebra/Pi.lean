/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Prod

/-!
# The R-algebra structure on families of R-algebras

The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

## Main definitions

* `Pi.algebra`
* `Pi.evalAlgHom`
* `Pi.constAlgHom`
-/

@[expose] public section

namespace Pi

-- The indexing type
variable (ι : Type*)

-- The scalar type
variable {R : Type*}

-- The family of types already equipped with instances
variable (A : ι → Type*)
variable [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/-
**Pi.algebra** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：algebra : Algebra R (Π i, A i) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra : Algebra R (Π i, A i) where
  algebraMap := RingHom.pi fun i ↦ algebraMap R (A i)
  commutes' := fun a f ↦ by ext; simp [Algebra.commutes]
  smul_def' := fun a f ↦ by ext; simp [Algebra.smul_def]

@[push ←]
/-
**Pi.algebraMap_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：algebraMap_def (a : R) : algebraMap R (Π i, A i) a = fun i => algebraMap R
 (A i) a
参数：a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_def (a : R) : algebraMap R (Π i, A i) a = fun i ↦ algebraMap R (A i) a :=
  rfl

@[simp]
/-
**Pi.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：algebraMap_apply (a : R) (i : ι) : algebraMap R (Π i, A i) a i = algebraMa
p R (A i) a
参数：a : R；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply (a : R) (i : ι) : algebraMap R (Π i, A i) a i = algebraMap R (A i) a :=
  rfl

variable {ι}

variable {A} in
/-- A family of algebra homomorphisms `g i : B →ₐ[R] A i` defines an algebra homomorphism
`AlgHom.pi g : B →ₐ[R] Π i, A i` given by `AlgHom.pi g x i = g i x`. -/
@[simps!]
/-
**Pi._root_.AlgHom.pi** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of algebra homomorphisms `g i : B →ₐ[R] A i` defines an algebra homomor
phism
`AlgHom.pi g : B →ₐ[R] Π i, A i` given by `AlgHom.pi g x i = g i x`.
-/
def _root_.AlgHom.pi {B : Type*} [Semiring B] [Algebra R B] (g : Π i, B →ₐ[R] A i) :
    B →ₐ[R] Π i, A i where
  __ := RingHom.pi fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp

variable {A} in
/-- `AlgHom.pi` commutes with composition. -/
/-
**Pi._root_.AlgHom.pi_comp** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHom.pi` commutes with composition.
-/
theorem _root_.AlgHom.pi_comp {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (g : ∀ i, C →ₐ[R] A i) (h : B →ₐ[R] C) :
    (AlgHom.pi g).comp h = AlgHom.pi (fun i ↦ (g i).comp h) := rfl

variable (R)

/-- Use `AlgHom.pi` instead. -/
@[deprecated AlgHom.pi (since := "2026-05-30")]
/-
**Pi.algHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Pi`。
形式化陈述：algHom {B : Type*} [Semiring B] [Algebra R B] (g : Π i, B ->ₐ[R] A i) : B 
->ₐ[R] Π i, A i
参数：g : Π i, B ->ₐ[R] A i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `AlgHom.pi` instead.
-/
abbrev algHom {B : Type*} [Semiring B] [Algebra R B] (g : Π i, B →ₐ[R] A i) : B →ₐ[R] Π i, A i :=
  .pi g

/-- Use `AlgHom.pi_apply` instead. -/
@[deprecated AlgHom.pi_apply (since := "2026-05-30")]
/-
**Pi.algHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：algHom_apply {B : Type*} [Semiring B] [Algebra R B] (g : Π i, B ->ₐ[R] A i
) (x : B) (i : ι) : Pi.algHom R A g x i = g i x
参数：g : Π i, B ->ₐ[R] A i；x : B；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.pi_apply`：∀ {ι : Type u_1} {R : Type u_2} {A : ι → Type u_3} [ins
t : CommSemiring R] [inst_1 : (i : ι) → Semiring (A i)]   [inst_2 : (i : ι) → Al
gebra…

--- 原说明 ---
Use `AlgHom.pi_apply` instead.
-/
theorem algHom_apply {B : Type*} [Semiring B] [Algebra R B]
    (g : Π i, B →ₐ[R] A i) (x : B) (i : ι) : Pi.algHom R A g x i = g i x :=
  AlgHom.pi_apply g x i

@[deprecated AlgHom.pi_comp (since := "2026-05-30")]
/-
**Pi.algHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：algHom_comp {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra
 R C] (g : forall i, C ->ₐ[R] A i) (h : B ->ₐ[R] C) : (algHom R A g).comp h = al
gHom R A (fun i => (g i).comp h)
参数：g : forall i, C ->ₐ[R] A i；h : B ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algHom_comp {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (g : ∀ i, C →ₐ[R] A i) (h : B →ₐ[R] C) :
    (algHom R A g).comp h = algHom R A (fun i ↦ (g i).comp h) := rfl

/-- `Function.eval` as an `AlgHom`. The name matches `Pi.evalRingHom`, `Pi.evalMonoidHom`,
etc. -/
@[simps]
/-
**Pi.evalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：evalAlgHom (i : ι) : (Π i, A i) ->ₐ[R] A i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.eval` as an `AlgHom`. The name matches `Pi.evalRingHom`, `Pi.evalMonoi
dHom`,
etc.
-/
def evalAlgHom (i : ι) : (Π i, A i) →ₐ[R] A i :=
  { Pi.evalRingHom A i with
    toFun := fun f ↦ f i
    commutes' := fun _ ↦ rfl }
/-
**Pi.coe_evalAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：coe_evalAlgHom (i : ι) : evalAlgHom R A i = evalRingHom A i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma coe_evalAlgHom (i : ι) : evalAlgHom R A i = evalRingHom A i := rfl

@[simp]
/-
**Pi._root_.AlgHom.pi_evalAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.pi_evalAlgHom : AlgHom.pi (evalAlgHom R A) = AlgHom.id R (Π i, A i) :=
  rfl

@[deprecated (since := "2026-06-03")]
alias algHom_evalAlgHom := _root_.AlgHom.pi_evalAlgHom

variable (S : ι → Type*) [∀ i, CommSemiring (S i)]
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Algebra (S i) (A i)] : Algebra (Π i, S i) (Π i, A i) where
  algebraMap := RingHom.pi fun _ ↦ (algebraMap _ _).comp (Pi.evalRingHom S _)
  commutes' _ _ := funext fun _ ↦ Algebra.commutes _ _
  smul_def' _ _ := funext fun _ ↦ Algebra.smul_def _ _
/-
**Pi.** 是 Mathlib 中的一个示例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Pi.instAlgebraForall S S = Algebra.id _ := rfl

variable (A B : Type*) [Semiring B] [Algebra R B]

/-- `Function.const` as an `AlgHom`. The name matches `Pi.constRingHom`, `Pi.constMonoidHom`,
etc. -/
@[simps]
/-
**Pi.constAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：constAlgHom : B ->ₐ[R] A -> B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.const` as an `AlgHom`. The name matches `Pi.constRingHom`, `Pi.constMo
noidHom`,
etc.
-/
def constAlgHom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ ↦ rfl }

/-- When `R` is commutative and permits an `algebraMap`, `Pi.constRingHom` is equal to that
map. -/
@[simp]
/-
**Pi.constRingHom_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：constRingHom_eq_algebraMap : constRingHom A R = algebraMap R (A -> R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `R` is commutative and permits an `algebraMap`, `Pi.constRingHom` is equal 
to that
map.
-/
theorem constRingHom_eq_algebraMap : constRingHom A R = algebraMap R (A → R) :=
  rfl

@[simp]
/-
**Pi.constAlgHom_eq_algebra_ofId** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：constAlgHom_eq_algebra_ofId : constAlgHom R A R = Algebra.ofId R (A -> R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constAlgHom_eq_algebra_ofId : constAlgHom R A R = Algebra.ofId R (A → R) :=
  rfl

end Pi

/-- A special case of `Pi.algebra` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this. -/
/-
**Function.algebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.algebra {R : Type*} (ι : Type*) (A : Type*) [CommSemiring R] [Sem
iring A] [Algebra R A] : Algebra R (ι -> A)
参数：ι : Type*；A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A special case of `Pi.algebra` for non-dependent types. Lean struggles to elabor
ate
definitions elsewhere in the library without this.
-/
instance Function.algebra {R : Type*} (ι : Type*) (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Algebra R (ι → A) :=
  Pi.algebra _ _

namespace AlgHom

variable {R A B : Type*}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

/-- `R`-algebra homomorphism between the function spaces `ι → A` and `ι → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps]
/-
**AlgHom.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       [inst : Com
mSemiring R] →         [inst_1 : Semiring A] →           [inst_2 : Semiring B] →
             [inst_3 : Algebra R A] → [inst_4 : Algebra R B] → (A →ₐ[R] B) → (ι 
: Type u_4) → (ι → A) →ₐ[R] ι → B
参数：A →ₐ[R] B；ι : Type u_4；ι → A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R`-algebra homomorphism between the function spaces `ι → A` and `ι → B`, induce
d by an
`R`-algebra homomorphism `f` between `A` and `B`.
-/
protected def compLeft (f : A →ₐ[R] B) (ι : Type*) : (ι → A) →ₐ[R] ι → B :=
  { f.toRingHom.compLeft ι with
    toFun := fun h ↦ f ∘ h
    commutes' := fun c ↦ by
      ext
      exact f.commutes' c }

end AlgHom

namespace AlgEquiv

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}
variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]
variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

/-- A family of algebra equivalences `∀ i, (A₁ i ≃ₐ A₂ i)` generates a
multiplicative equivalence between `Π i, A₁ i` and `Π i, A₂ i`.

This is the `AlgEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`AlgEquiv.arrowCongr`.
-/
@[simps apply]
/-
**AlgEquiv.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：piCongrRight (e : forall i, A₁ i ≃ₐ[R] A₂ i) : (Π i, A₁ i) ≃ₐ[R] Π i, A₂ i
参数：e : forall i, A₁ i ≃ₐ[R] A₂ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of algebra equivalences `∀ i, (A₁ i ≃ₐ A₂ i)` generates a
multiplicative equivalence between `Π i, A₁ i` and `Π i, A₂ i`.

This is the `AlgEquiv` version of `Equiv.piCongrRight`, and the dependent versio
n of
`AlgEquiv.arrowCongr`.
-/
def piCongrRight (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (Π i, A₁ i) ≃ₐ[R] Π i, A₂ i :=
  { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i ↦ (e i).toRingEquiv with
    toFun := fun x j ↦ e j (x j)
    invFun := fun x j ↦ (e j).symm (x j)
    commutes' := fun r ↦ by
      ext i
      simp }

@[simp]
/-
**AlgEquiv.piCongrRight_refl** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：piCongrRight_refl : (piCongrRight fun i => (AlgEquiv.refl : A₁ i ≃ₐ[R] A₁ 
i)) = AlgEquiv.refl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_refl :
    (piCongrRight fun i ↦ (AlgEquiv.refl : A₁ i ≃ₐ[R] A₁ i)) = AlgEquiv.refl :=
  rfl

@[simp]
/-
**AlgEquiv.piCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：piCongrRight_symm (e : forall i, A₁ i ≃ₐ[R] A₂ i) : (piCongrRight e).symm 
= piCongrRight fun i => (e i).symm
参数：e : forall i, A₁ i ≃ₐ[R] A₂ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_symm (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) :
    (piCongrRight e).symm = piCongrRight fun i ↦ (e i).symm :=
  rfl

@[simp]
/-
**AlgEquiv.piCongrRight_trans** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：piCongrRight_trans (e₁ : forall i, A₁ i ≃ₐ[R] A₂ i) (e₂ : forall i, A₂ i ≃
ₐ[R] A₃ i) : (piCongrRight e₁).trans (piCongrRight e₂) = piCongrRight fun i => (
e₁ i).trans (e₂ i)
参数：e₁ : forall i, A₁ i ≃ₐ[R] A₂ i；e₂ : forall i, A₂ i ≃ₐ[R] A₃ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_trans (e₁ : ∀ i, A₁ i ≃ₐ[R] A₂ i) (e₂ : ∀ i, A₂ i ≃ₐ[R] A₃ i) :
    (piCongrRight e₁).trans (piCongrRight e₂) = piCongrRight fun i ↦ (e₁ i).trans (e₂ i) :=
  rfl

variable (R A₁) in
/-- The opposite of a direct product is isomorphic to the direct product of the opposites as
algebras. -/
/-
**AlgEquiv.piMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：piMulOpposite : (Π i, A₁ i)ᵐᵒᵖ ≃ₐ[R] Π i, (A₁ i)ᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a direct product is isomorphic to the direct product of the oppo
sites as
algebras.
-/
def piMulOpposite : (Π i, A₁ i)ᵐᵒᵖ ≃ₐ[R] Π i, (A₁ i)ᵐᵒᵖ where
  __ := RingEquiv.piMulOpposite A₁
  commutes' _ := rfl

variable (R A₁) in
/--
Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as an `AlgEquiv`.
-/
/-
**AlgEquiv.piCongrLeft'** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：piCongrLeft' {ι' : Type*} (e : ι ≃ ι') : (Π i, A₁ i) ≃ₐ[R] Π i, A₁ (e.symm
 i) where __
参数：e : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as an `AlgEquiv`.
-/
def piCongrLeft' {ι' : Type*} (e : ι ≃ ι') : (Π i, A₁ i) ≃ₐ[R] Π i, A₁ (e.symm i) where
  __ := RingEquiv.piCongrLeft' A₁ e
  commutes' _ := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.piCongrLeft'_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type u_3} {ι : Type u_4} {A₁ : ι → Type u_5} [inst : CommSemiring R
] [inst_1 : (i : ι) → Semiring (A₁ i)]   [inst_2 : (i : ι) → Algebra R (A₁ i)] {
ι' : Type u_8} (e : ι ≃ ι') (x : (i : ι) → A₁ i),   (AlgEquiv.piCongrLeft' R A₁ 
e) x = (Equiv.piCongrLeft' A₁ e) x
参数：i : ι；A₁ i；i : ι；A₁ i；e : ι ≃ ι'；x : (i : ι) → A₁ i；AlgEquiv.piCongrLeft' R A
₁ e；Equiv.piCongrLeft' A₁ e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma piCongrLeft'_apply {ι' : Type*} (e : ι ≃ ι') (x : (Π i, A₁ i)) :
    piCongrLeft' R A₁ e x = Equiv.piCongrLeft' _ _ x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.piCongrLeft'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ {R : Type u_3} {ι : Type u_4} {A₁ : ι → Type u_5} [inst : CommSemiring R
] [inst_1 : (i : ι) → Semiring (A₁ i)]   [inst_2 : (i : ι) → Algebra R (A₁ i)] {
ι' : Type u_8} (e : ι ≃ ι') (x : (i : ι') → A₁ (e.symm i)),   (AlgEquiv.piCongrL
eft' R A₁ e).symm x = (Equiv.piCongrLeft' A₁ e).symm x
参数：i : ι；A₁ i；i : ι；A₁ i；e : ι ≃ ι'；x : (i : ι') → A₁ (e.symm i)；AlgEquiv.piCong
rLeft' R A₁ e；Equiv.piCongrLeft' A₁ e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma piCongrLeft'_symm_apply {ι' : Type*} (e : ι ≃ ι') (x : Π i, A₁ (e.symm i)) :
    (piCongrLeft' R A₁ e).symm x = (Equiv.piCongrLeft' _ _).symm x := rfl

variable (R A₁) in
/--
Transport dependent functions through an equivalence of the base space, expressed as
"simplification".

This is `Equiv.piCongrLeft` as an `AlgEquiv`.
-/
/-
**AlgEquiv.piCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：piCongrLeft {ι' : Type*} (e : ι' ≃ ι) : (Π i, A₁ (e i)) ≃ₐ[R] Π i, A₁ i
参数：e : ι' ≃ ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transport dependent functions through an equivalence of the base space, expresse
d as
"simplification".

This is `Equiv.piCongrLeft` as an `AlgEquiv`.
-/
def piCongrLeft {ι' : Type*} (e : ι' ≃ ι) : (Π i, A₁ (e i)) ≃ₐ[R] Π i, A₁ i :=
  (AlgEquiv.piCongrLeft' R A₁ e.symm).symm

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.piCongrLeft_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：piCongrLeft_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ (e i)) : piCongrL
eft R A₁ e x = Equiv.piCongrLeft _ _ x
参数：e : ι' ≃ ι；x : Π i, A₁ (e i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piCongrLeft_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ (e i)) :
    piCongrLeft R A₁ e x = Equiv.piCongrLeft _ _ x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.piCongrLeft_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：piCongrLeft_symm_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ i) : (piCong
rLeft R A₁ e).symm x = (Equiv.piCongrLeft _ _).symm x
参数：e : ι' ≃ ι；x : Π i, A₁ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piCongrLeft_symm_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ i) :
    (piCongrLeft R A₁ e).symm x = (Equiv.piCongrLeft _ _).symm x := rfl

section

variable (S : Type*) [Semiring S] [Algebra R S]

variable (ι R) in
/-- If `ι` has a unique element, then `ι → S` is isomorphic to `S` as an `R`-algebra. -/
/-
**AlgEquiv.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：funUnique [Unique ι] : (ι -> S) ≃ₐ[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` has a unique element, then `ι → S` is isomorphic to `S` as an `R`-algebra
.
-/
def funUnique [Unique ι] : (ι → S) ≃ₐ[R] S :=
  .ofRingEquiv (f := .piUnique (fun i : ι ↦ S)) (by simp)

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.funUnique_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：funUnique_apply [Unique ι] (x : ι -> S) : funUnique R ι S x = Equiv.funUni
que ι S x
参数：x : ι -> S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma funUnique_apply [Unique ι] (x : ι → S) : funUnique R ι S x = Equiv.funUnique ι S x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.funUnique_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：funUnique_symm_apply [Unique ι] (x : S) : (funUnique R ι S).symm x = (Equi
v.funUnique ι S).symm x
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma funUnique_symm_apply [Unique ι] (x : S) :
    (funUnique R ι S).symm x = (Equiv.funUnique ι S).symm x := rfl

variable (α β R) in
/-- `Equiv.sumArrowEquivProdArrow` as an algebra equivalence. -/
/-
**AlgEquiv.sumArrowEquivProdArrow** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：sumArrowEquivProdArrow : (α oplus β -> S) ≃ₐ[R] (α -> S) × (β -> S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.sumArrowEquivProdArrow` as an algebra equivalence.
-/
def sumArrowEquivProdArrow : (α ⊕ β → S) ≃ₐ[R] (α → S) × (β → S) :=
  .ofRingEquiv (f := .sumArrowEquivProdArrow α β S) (by intro; ext <;> simp)

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.sumArrowEquivProdArrow_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：sumArrowEquivProdArrow_apply (x : α oplus β -> S) : sumArrowEquivProdArrow
 α β R S x = Equiv.sumArrowEquivProdArrow α β S x
参数：x : α oplus β -> S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumArrowEquivProdArrow_apply (x : α ⊕ β → S) :
    sumArrowEquivProdArrow α β R S x = Equiv.sumArrowEquivProdArrow α β S x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.sumArrowEquivProdArrow_symm_apply_inr** 是 Mathlib 中的一个引理，位于命名空间 `AlgE
quiv`。
形式化陈述：sumArrowEquivProdArrow_symm_apply_inr (x : (α -> S) × (β -> S)) : (sumArro
wEquivProdArrow α β R S).symm x = (Equiv.sumArrowEquivProdArrow α β S).symm x
参数：x : (α -> S) × (β -> S)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumArrowEquivProdArrow_symm_apply_inr (x : (α → S) × (β → S)) :
    (sumArrowEquivProdArrow α β R S).symm x = (Equiv.sumArrowEquivProdArrow α β S).symm x :=
  rfl

end

end AlgEquiv

/-- Apply an algebra map component-wise along a vector. -/
/-
**Pi.algebraMap** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：(ι : Type u_1) →   (R : Type u_2) →     (A : Type u_3) → [inst : CommSemir
ing R] → [inst_1 : Semiring A] → [inst_2 : Algebra R A] → (ι → R) →ₗ[R] ι → A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply an algebra map component-wise along a vector.
-/
protected def Pi.algebraMap (ι R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    (ι → R) →ₗ[R] (ι → A) where
  toFun v := algebraMap R A ∘ v
  map_add' v w := by simp
  map_smul' t v := by ext; simp [Algebra.smul_def]
