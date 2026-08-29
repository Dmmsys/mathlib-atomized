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
variable (A : ι -> Type*)
variable [CommSemiring R] [forall i, Semiring (A i)] [forall i, Algebra R (A i)]

/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: : Algebra R (Π i, A i) where
  body: RingHom.pi fun i => algebraMap R (A i)
  commutes' := fun a f => by ext; simp [Algebra.commutes]
  smul_def' := fun a f => by ext; simp [Algebra.smul_def]

@[push ←]

中文:
实例 algebra
  签名: : 代数 R (Π i, A i) where
  定义体: RingHom.pi fun i => algebraMap R (A i)
  commutes' := fun a f => by ext; simp [Algebra.commutes]
  smul_def' := fun a f => by ext; simp [Algebra.smul_def]

@[push ←]

Depends on / 依赖: RingHom, RingHom.pi, algebraMap
-/
instance algebra : Algebra R (Π i, A i) where
  algebraMap := RingHom.pi fun i => algebraMap R (A i)
  commutes' := fun a f => by ext; simp [Algebra.commutes]
  smul_def' := fun a f => by ext; simp [Algebra.smul_def]

@[push ←]
/--
theorem `algebraMap_def` / 定理 `algebraMap_def`

English:
theorem algebraMap_def
  given: (a : R)
  statement: algebraMap R (Π i, A i) a = fun i => algebraMap R (A i) a
  proof: rfl

@[simp]

中文:
定理 algebraMap_def
  条件: (a : R)
  结论: algebraMap R (Π i, A i) a = fun i => algebraMap R (A i) a
  证明: rfl

@[simp]
-/
theorem algebraMap_def (a : R) : algebraMap R (Π i, A i) a = fun i => algebraMap R (A i) a :=
  rfl

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (a : R) (i : ι)
  statement: algebraMap R (Π i, A i) a i = algebraMap R (A i) a
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (a : R) (i : ι)
  结论: algebraMap R (Π i, A i) a i = algebraMap R (A i) a
  证明: rfl
-/
theorem algebraMap_apply (a : R) (i : ι) : algebraMap R (Π i, A i) a i = algebraMap R (A i) a :=
  rfl

variable {ι}

variable {A} in
/-- A family of algebra homomorphisms `g i : B →ₐ[R] A i` defines an algebra homomorphism
`AlgHom.pi g : B →ₐ[R] Π i, A i` given by `AlgHom.pi g x i = g i x`. -/
@[simps!]
/--
Definition of `_root_.AlgHom.pi` / `_root_.AlgHom.pi` 的定义

English:
definition _root_.AlgHom.pi
  signature: {B : Type*} [Semiring B] [Algebra R B] (g : Π i, B ->ₐ[R] A i)
  body: RingHom.pi fun i => (g i).toRingHom
  commutes' r := by ext; simp

中文:
定义 _root_.代数态射.pi
  签名: {B : 类型} [半环 B] [代数 R B] (g : Π i, B ->ₐ[R] A i)
  定义体: RingHom.pi fun i => (g i).toRingHom
  commutes' r := by ext; simp

Depends on / 依赖: RingHom, RingHom.pi, toRingHom
-/
def _root_.AlgHom.pi {B : Type*} [Semiring B] [Algebra R B] (g : Π i, B ->ₐ[R] A i) :
    B ->ₐ[R] Π i, A i where
  __ := RingHom.pi fun i => (g i).toRingHom
  commutes' r := by ext; simp

variable {A} in
/--
theorem `_root_.AlgHom.pi_comp` / 定理 `_root_.AlgHom.pi_comp`

English:
theorem _root_.AlgHom.pi_comp
  statement: {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
  proof: rfl

中文:
定理 _root_.代数态射.pi_comp
  结论: {B C : 类型} [半环 B] [代数 R B] [半环 C] [代数 R C]
  证明: rfl
-/
theorem _root_.AlgHom.pi_comp {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (g : forall i, C ->ₐ[R] A i) (h : B ->ₐ[R] C) :
    (AlgHom.pi g).comp h = AlgHom.pi (fun i => (g i).comp h) := rfl

variable (R)

/-- Use `AlgHom.pi` instead. -/
@[deprecated AlgHom.pi (since := "2026-05-30")]
/--
Definition of `algHom` / `algHom` 的定义

English:
abbreviation algHom
  signature: {B : Type*} [Semiring B] [Algebra R B] (g : Π i, B ->ₐ[R] A i)
  body: .pi g

中文:
缩写 algHom
  签名: {B : 类型} [半环 B] [代数 R B] (g : Π i, B ->ₐ[R] A i)
  定义体: .pi g
-/
abbrev algHom {B : Type*} [Semiring B] [Algebra R B] (g : Π i, B ->ₐ[R] A i) : B ->ₐ[R] Π i, A i :=
  .pi g

/-- Use `AlgHom.pi_apply` instead. -/
@[deprecated AlgHom.pi_apply (since := "2026-05-30")]
/--
theorem `algHom_apply` / 定理 `algHom_apply`

English:
theorem algHom_apply
  statement: {B : Type*} [Semiring B] [Algebra R B]
  proof: AlgHom.pi_apply g x i

@[deprecated AlgHom.pi_comp (since := "2026-05-30")]

中文:
定理 algHom_apply
  结论: {B : 类型} [半环 B] [代数 R B]
  证明: AlgHom.pi_apply g x i

@[deprecated AlgHom.pi_comp (since := "2026-05-30")]

Depends on / 依赖: AlgHom, AlgHom.pi_apply, pi_apply
-/
theorem algHom_apply {B : Type*} [Semiring B] [Algebra R B]
    (g : Π i, B ->ₐ[R] A i) (x : B) (i : ι) : Pi.algHom R A g x i = g i x :=
  AlgHom.pi_apply g x i

@[deprecated AlgHom.pi_comp (since := "2026-05-30")]
/--
theorem `algHom_comp` / 定理 `algHom_comp`

English:
theorem algHom_comp
  statement: {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
  proof: rfl

中文:
定理 algHom_comp
  结论: {B C : 类型} [半环 B] [代数 R B] [半环 C] [代数 R C]
  证明: rfl
-/
theorem algHom_comp {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (g : forall i, C ->ₐ[R] A i) (h : B ->ₐ[R] C) :
    (algHom R A g).comp h = algHom R A (fun i => (g i).comp h) := rfl

/-- `Function.eval` as an `AlgHom`. The name matches `Pi.evalRingHom`, `Pi.evalMonoidHom`,
etc. -/
@[simps]
/--
Definition of `evalAlgHom` / `evalAlgHom` 的定义

English:
definition evalAlgHom
  signature: (i : ι)
  body: { Pi.evalRingHom A i with
    toFun := fun f => f i
    commutes' := fun _ => rfl }

中文:
定义 evalAlgHom
  签名: (i : ι)
  定义体: { Pi.evalRingHom A i with
    toFun := fun f => f i
    commutes' := fun _ => rfl }

Depends on / 依赖: Pi.evalRingHom, commutes, evalRingHom
-/
def evalAlgHom (i : ι) : (Π i, A i) ->ₐ[R] A i :=
  { Pi.evalRingHom A i with
    toFun := fun f => f i
    commutes' := fun _ => rfl }

/--
lemma `coe_evalAlgHom` / 引理 `coe_evalAlgHom`

English:
lemma coe_evalAlgHom
  given: (i : ι)
  statement: evalAlgHom R A i = evalRingHom A i
  proof: rfl

@[simp]

中文:
引理 coe_evalAlgHom
  条件: (i : ι)
  结论: evalAlgHom R A i = evalRingHom A i
  证明: rfl

@[simp]
-/
lemma coe_evalAlgHom (i : ι) : evalAlgHom R A i = evalRingHom A i := rfl

@[simp]
/--
theorem `_root_.AlgHom.pi_evalAlgHom` / 定理 `_root_.AlgHom.pi_evalAlgHom`

English:
theorem _root_.AlgHom.pi_evalAlgHom
  statement: AlgHom.pi (evalAlgHom R A) = AlgHom.id R (Π i, A i)
  proof: rfl

@[deprecated (since := "2026-06-03")]
alias algHom_evalAlgHom := _root_.AlgHom.pi_evalAlgHom

中文:
定理 _root_.代数态射.pi_evalAlgHom
  结论: 代数态射.pi (evalAlgHom R A) = 代数态射.id R (Π i, A i)
  证明: rfl

@[deprecated (since := "2026-06-03")]
alias algHom_evalAlgHom := _root_.AlgHom.pi_evalAlgHom
-/
theorem _root_.AlgHom.pi_evalAlgHom : AlgHom.pi (evalAlgHom R A) = AlgHom.id R (Π i, A i) :=
  rfl

@[deprecated (since := "2026-06-03")]
alias algHom_evalAlgHom := _root_.AlgHom.pi_evalAlgHom

variable (S : ι -> Type*) [forall i, CommSemiring (S i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Algebra (S i) (A i)] : Algebra (Π i, S i) (Π i, A i) where
  body: RingHom.pi fun _ => (algebraMap _ _).comp (Pi.evalRingHom S _)
  commutes' _ _ := funext fun _ => Algebra.commutes _ _
  smul_def' _ _ := funext fun _ => Algebra.smul_def _ _

example : Pi.instAlgebraForall S S = Algebra.id _ := rfl

中文:
实例 [对任意
  签名: i, 代数 (S i) (A i)] : 代数 (Π i, S i) (Π i, A i) where
  定义体: RingHom.pi fun _ => (algebraMap _ _).comp (Pi.evalRingHom S _)
  commutes' _ _ := funext fun _ => Algebra.commutes _ _
  smul_def' _ _ := funext fun _ => Algebra.smul_def _ _

example : Pi.instAlgebraForall S S = Algebra.id _ := rfl

Depends on / 依赖: Pi.evalRingHom, RingHom, RingHom.pi, algebraMap, evalRingHom
-/
instance [forall i, Algebra (S i) (A i)] : Algebra (Π i, S i) (Π i, A i) where
  algebraMap := RingHom.pi fun _ => (algebraMap _ _).comp (Pi.evalRingHom S _)
  commutes' _ _ := funext fun _ => Algebra.commutes _ _
  smul_def' _ _ := funext fun _ => Algebra.smul_def _ _

example : Pi.instAlgebraForall S S = Algebra.id _ := rfl

variable (A B : Type*) [Semiring B] [Algebra R B]

/-- `Function.const` as an `AlgHom`. The name matches `Pi.constRingHom`, `Pi.constMonoidHom`,
etc. -/
@[simps]
/--
Definition of `constAlgHom` / `constAlgHom` 的定义

English:
definition constAlgHom
  signature: : B ->ₐ[R] A -> B
  body: { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ => rfl }

中文:
定义 constAlgHom
  签名: : B ->ₐ[R] A -> B
  定义体: { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ => rfl }

Depends on / 依赖: Function, Function.const, Pi.constRingHom, commutes, constRingHom
-/
def constAlgHom : B ->ₐ[R] A -> B :=
  { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ => rfl }

/-- When `R` is commutative and permits an `algebraMap`, `Pi.constRingHom` is equal to that
map. -/
@[simp]
/--
theorem `constRingHom_eq_algebraMap` / 定理 `constRingHom_eq_algebraMap`

English:
theorem constRingHom_eq_algebraMap
  statement: constRingHom A R = algebraMap R (A -> R)
  proof: rfl

@[simp]

中文:
定理 constRingHom_eq_algebraMap
  结论: constRingHom A R = algebraMap R (A -> R)
  证明: rfl

@[simp]
-/
theorem constRingHom_eq_algebraMap : constRingHom A R = algebraMap R (A -> R) :=
  rfl

@[simp]
/--
theorem `constAlgHom_eq_algebra_ofId` / 定理 `constAlgHom_eq_algebra_ofId`

English:
theorem constAlgHom_eq_algebra_ofId
  statement: constAlgHom R A R = Algebra.ofId R (A -> R)
  proof: rfl

中文:
定理 constAlgHom_eq_algebra_ofId
  结论: constAlgHom R A R = 代数.ofId R (A -> R)
  证明: rfl

Depends on / 依赖: vadd_add_assoc
-/
theorem constAlgHom_eq_algebra_ofId : constAlgHom R A R = Algebra.ofId R (A -> R) :=
  rfl

end Pi

/--
Instance `Function.algebra` / 实例 `Function.algebra`

English:
instance Function.algebra
  signature: {R : Type*} (ι : Type*) (A : Type*) [CommSemiring R] [Semiring A]
  body: Pi.algebra _ _

中文:
实例 函数.algebra
  签名: {R : 类型} (ι : 类型) (A : 类型) [交换半环 R] [半环 A]
  定义体: Pi.algebra _ _

Depends on / 依赖: Pi.algebra, algebra
-/
instance Function.algebra {R : Type*} (ι : Type*) (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Algebra R (ι -> A) :=
  Pi.algebra _ _

namespace AlgHom

variable {R A B : Type*}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

/-- `R`-algebra homomorphism between the function spaces `ι → A` and `ι → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps]
/--
Definition of `compLeft` / `compLeft` 的定义

English:
definition compLeft
  signature: (f : A ->ₐ[R] B) (ι : Type*)
  body: { f.toRingHom.compLeft ι with
    toFun := fun h => f ∘ h
    commutes' := fun c => by
      ext
      exact f.commutes' c }

中文:
定义 compLeft
  签名: (f : A ->ₐ[R] B) (ι : 类型)
  定义体: { f.toRingHom.compLeft ι with
    toFun := fun h => f ∘ h
    commutes' := fun c => by
      ext
      exact f.commutes' c }

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addAction, addAction, coe_injective, coe_vadd
-/
protected def compLeft (f : A ->ₐ[R] B) (ι : Type*) : (ι -> A) ->ₐ[R] ι -> B :=
  { f.toRingHom.compLeft ι with
    toFun := fun h => f ∘ h
    commutes' := fun c => by
      ext
      exact f.commutes' c }

end AlgHom

namespace AlgEquiv

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι -> Type*}
variable [CommSemiring R] [forall i, Semiring (A₁ i)] [forall i, Semiring (A₂ i)] [forall i, Semiring (A₃ i)]
variable [forall i, Algebra R (A₁ i)] [forall i, Algebra R (A₂ i)] [forall i, Algebra R (A₃ i)]

/-- A family of algebra equivalences `∀ i, (A₁ i ≃ₐ A₂ i)` generates a
multiplicative equivalence between `Π i, A₁ i` and `Π i, A₂ i`.

This is the `AlgEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`AlgEquiv.arrowCongr`.
-/
@[simps apply]
/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: (e : forall i, A₁ i ≃ₐ[R] A₂ i)
  body: { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i => (e i).toRingEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j)
    commutes' := fun r => by
      ext i
      simp }

@[simp]

中文:
定义 piCongrRight
  签名: (e : 对任意 i, A₁ i ≃ₐ[R] A₂ i)
  定义体: { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i => (e i).toRingEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j)
    commutes' := fun r => by
      ext i
      simp }

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.piCongrRight, commutes, invFun, piCongrRight, toRingEquiv
-/
def piCongrRight (e : forall i, A₁ i ≃ₐ[R] A₂ i) : (Π i, A₁ i) ≃ₐ[R] Π i, A₂ i :=
  { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i => (e i).toRingEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j)
    commutes' := fun r => by
      ext i
      simp }

@[simp]
/--
theorem `piCongrRight_refl` / 定理 `piCongrRight_refl`

English:
theorem piCongrRight_refl
  proof: rfl

@[simp]

中文:
定理 piCongrRight_refl
  证明: rfl

@[simp]
-/
theorem piCongrRight_refl :
    (piCongrRight fun i => (AlgEquiv.refl : A₁ i ≃ₐ[R] A₁ i)) = AlgEquiv.refl :=
  rfl

@[simp]
/--
theorem `piCongrRight_symm` / 定理 `piCongrRight_symm`

English:
theorem piCongrRight_symm
  given: (e : forall i, A₁ i ≃ₐ[R] A₂ i)
  proof: rfl

@[simp]

中文:
定理 piCongrRight_symm
  条件: (e : 对任意 i, A₁ i ≃ₐ[R] A₂ i)
  证明: rfl

@[simp]
-/
theorem piCongrRight_symm (e : forall i, A₁ i ≃ₐ[R] A₂ i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl

@[simp]
/--
theorem `piCongrRight_trans` / 定理 `piCongrRight_trans`

English:
theorem piCongrRight_trans
  given: (e₁ : forall i, A₁ i ≃ₐ[R] A₂ i) (e₂ : forall i, A₂ i ≃ₐ[R] A₃ i)
  proof: rfl

中文:
定理 piCongrRight_trans
  条件: (e₁ : 对任意 i, A₁ i ≃ₐ[R] A₂ i) (e₂ : 对任意 i, A₂ i ≃ₐ[R] A₃ i)
  证明: rfl
-/
theorem piCongrRight_trans (e₁ : forall i, A₁ i ≃ₐ[R] A₂ i) (e₂ : forall i, A₂ i ≃ₐ[R] A₃ i) :
    (piCongrRight e₁).trans (piCongrRight e₂) = piCongrRight fun i => (e₁ i).trans (e₂ i) :=
  rfl

variable (R A₁) in
/--
Definition of `piMulOpposite` / `piMulOpposite` 的定义

English:
definition piMulOpposite
  signature: : (Π i, A₁ i)ᵐᵒᵖ ≃ₐ[R] Π i, (A₁ i)ᵐᵒᵖ where
  body: RingEquiv.piMulOpposite A₁
  commutes' _ := rfl

中文:
定义 piMulOpposite
  签名: : (Π i, A₁ i)ᵐᵒᵖ ≃ₐ[R] Π i, (A₁ i)ᵐᵒᵖ where
  定义体: RingEquiv.piMulOpposite A₁
  commutes' _ := rfl

Depends on / 依赖: RingEquiv, RingEquiv.piMulOpposite, piMulOpposite
-/
def piMulOpposite : (Π i, A₁ i)ᵐᵒᵖ ≃ₐ[R] Π i, (A₁ i)ᵐᵒᵖ where
  __ := RingEquiv.piMulOpposite A₁
  commutes' _ := rfl

variable (R A₁) in
/--
Definition of `piCongrLeft'` / `piCongrLeft'` 的定义

English:
definition piCongrLeft'
  signature: {ι' : Type*} (e : ι ≃ ι')
  body: RingEquiv.piCongrLeft' A₁ e
  commutes' _ := rfl

中文:
定义 piCongrLeft'
  签名: {ι' : 类型} (e : ι ≃ ι')
  定义体: RingEquiv.piCongrLeft' A₁ e
  commutes' _ := rfl

Depends on / 依赖: RingEquiv, RingEquiv.piCongrLeft, piCongrLeft
-/
def piCongrLeft' {ι' : Type*} (e : ι ≃ ι') : (Π i, A₁ i) ≃ₐ[R] Π i, A₁ (e.symm i) where
  __ := RingEquiv.piCongrLeft' A₁ e
  commutes' _ := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `piCongrLeft'_apply` / 引理 `piCongrLeft'_apply`

English:
lemma piCongrLeft'_apply
  given: {ι' : Type*} (e : ι ≃ ι') (x : (Π i, A₁ i))
  proof: rfl

中文:
引理 piCongrLeft'_apply
  条件: {ι' : 类型} (e : ι ≃ ι') (x : (Π i, A₁ i))
  证明: rfl
-/
lemma piCongrLeft'_apply {ι' : Type*} (e : ι ≃ ι') (x : (Π i, A₁ i)) :
    piCongrLeft' R A₁ e x = Equiv.piCongrLeft' _ _ x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `piCongrLeft'_symm_apply` / 引理 `piCongrLeft'_symm_apply`

English:
lemma piCongrLeft'_symm_apply
  given: {ι' : Type*} (e : ι ≃ ι') (x : Π i, A₁ (e.symm i))
  proof: rfl

中文:
引理 piCongrLeft'_symm_apply
  条件: {ι' : 类型} (e : ι ≃ ι') (x : Π i, A₁ (e.symm i))
  证明: rfl
-/
lemma piCongrLeft'_symm_apply {ι' : Type*} (e : ι ≃ ι') (x : Π i, A₁ (e.symm i)) :
    (piCongrLeft' R A₁ e).symm x = (Equiv.piCongrLeft' _ _).symm x := rfl

variable (R A₁) in
/--
Definition of `piCongrLeft` / `piCongrLeft` 的定义

English:
definition piCongrLeft
  signature: {ι' : Type*} (e : ι' ≃ ι)
  body: (AlgEquiv.piCongrLeft' R A₁ e.symm).symm

中文:
定义 piCongrLeft
  签名: {ι' : 类型} (e : ι' ≃ ι)
  定义体: (AlgEquiv.piCongrLeft' R A₁ e.symm).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.piCongrLeft, e.symm, piCongrLeft
-/
def piCongrLeft {ι' : Type*} (e : ι' ≃ ι) : (Π i, A₁ (e i)) ≃ₐ[R] Π i, A₁ i :=
  (AlgEquiv.piCongrLeft' R A₁ e.symm).symm

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `piCongrLeft_apply` / 引理 `piCongrLeft_apply`

English:
lemma piCongrLeft_apply
  given: {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ (e i))
  proof: rfl

中文:
引理 piCongrLeft_apply
  条件: {ι' : 类型} (e : ι' ≃ ι) (x : Π i, A₁ (e i))
  证明: rfl
-/
lemma piCongrLeft_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ (e i)) :
    piCongrLeft R A₁ e x = Equiv.piCongrLeft _ _ x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `piCongrLeft_symm_apply` / 引理 `piCongrLeft_symm_apply`

English:
lemma piCongrLeft_symm_apply
  given: {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ i)
  proof: rfl

中文:
引理 piCongrLeft_symm_apply
  条件: {ι' : 类型} (e : ι' ≃ ι) (x : Π i, A₁ i)
  证明: rfl
-/
lemma piCongrLeft_symm_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ i) :
    (piCongrLeft R A₁ e).symm x = (Equiv.piCongrLeft _ _).symm x := rfl

section

variable (S : Type*) [Semiring S] [Algebra R S]

variable (ι R) in
/--
Definition of `funUnique` / `funUnique` 的定义

English:
definition funUnique
  signature: [Unique ι]
  body: .ofRingEquiv (f := .piUnique (fun i : ι => S)) (by simp)

中文:
定义 funUnique
  签名: [唯一 ι]
  定义体: .ofRingEquiv (f := .piUnique (fun i : ι => S)) (by simp)

Depends on / 依赖: ofRingEquiv, piUnique
-/
def funUnique [Unique ι] : (ι -> S) ≃ₐ[R] S :=
  .ofRingEquiv (f := .piUnique (fun i : ι => S)) (by simp)

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `funUnique_apply` / 引理 `funUnique_apply`

English:
lemma funUnique_apply
  given: [Unique ι] (x : ι -> S)
  statement: funUnique R ι S x = Equiv.funUnique ι S x
  proof: rfl

中文:
引理 funUnique_apply
  条件: [唯一 ι] (x : ι -> S)
  结论: funUnique R ι S x = 等价.funUnique ι S x
  证明: rfl

Depends on / 依赖: f.toEquiv, toEquiv
-/
lemma funUnique_apply [Unique ι] (x : ι -> S) : funUnique R ι S x = Equiv.funUnique ι S x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `funUnique_symm_apply` / 引理 `funUnique_symm_apply`

English:
lemma funUnique_symm_apply
  given: [Unique ι] (x : S)
  proof: rfl

中文:
引理 funUnique_symm_apply
  条件: [唯一 ι] (x : S)
  证明: rfl

Depends on / 依赖: f.map_add_const, map_add_const
-/
lemma funUnique_symm_apply [Unique ι] (x : S) :
    (funUnique R ι S).symm x = (Equiv.funUnique ι S).symm x := rfl

variable (α β R) in
/--
Definition of `sumArrowEquivProdArrow` / `sumArrowEquivProdArrow` 的定义

English:
definition sumArrowEquivProdArrow
  signature: : (α oplus β -> S) ≃ₐ[R] (α -> S) × (β -> S)
  body: .ofRingEquiv (f := .sumArrowEquivProdArrow α β S) (by intro; ext <;> simp)

中文:
定义 sumArrowEquivProdArrow
  签名: : (α oplus β -> S) ≃ₐ[R] (α -> S) × (β -> S)
  定义体: .ofRingEquiv (f := .sumArrowEquivProdArrow α β S) (by intro; ext <;> simp)

Depends on / 依赖: ofRingEquiv, sumArrowEquivProdArrow
-/
def sumArrowEquivProdArrow : (α oplus β -> S) ≃ₐ[R] (α -> S) × (β -> S) :=
  .ofRingEquiv (f := .sumArrowEquivProdArrow α β S) (by intro; ext <;> simp)

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `sumArrowEquivProdArrow_apply` / 引理 `sumArrowEquivProdArrow_apply`

English:
lemma sumArrowEquivProdArrow_apply
  given: (x : α oplus β -> S)
  proof: rfl

中文:
引理 sumArrowEquivProdArrow_apply
  条件: (x : α oplus β -> S)
  证明: rfl
-/
lemma sumArrowEquivProdArrow_apply (x : α oplus β -> S) :
    sumArrowEquivProdArrow α β R S x = Equiv.sumArrowEquivProdArrow α β S x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `sumArrowEquivProdArrow_symm_apply_inr` / 引理 `sumArrowEquivProdArrow_symm_apply_inr`

English:
lemma sumArrowEquivProdArrow_symm_apply_inr
  given: (x : (α -> S) × (β -> S))
  proof: rfl

中文:
引理 sumArrowEquivProdArrow_symm_apply_inr
  条件: (x : (α -> S) × (β -> S))
  证明: rfl
-/
lemma sumArrowEquivProdArrow_symm_apply_inr (x : (α -> S) × (β -> S)) :
    (sumArrowEquivProdArrow α β R S).symm x = (Equiv.sumArrowEquivProdArrow α β S).symm x :=
  rfl

end

end AlgEquiv

/--
Definition of `Pi.algebraMap` / `Pi.algebraMap` 的定义

English:
definition Pi.algebraMap
  signature: (ι R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  body: algebraMap R A ∘ v
  map_add' v w := by simp
  map_smul' t v := by ext; simp [Algebra.smul_def]

中文:
定义 依赖函数类型.algebraMap
  签名: (ι R A : 类型) [交换半环 R] [半环 A] [代数 R A]
  定义体: algebraMap R A ∘ v
  map_add' v w := by simp
  map_smul' t v := by ext; simp [Algebra.smul_def]
-/
protected def Pi.algebraMap (ι R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    (ι -> R) ->ₗ[R] (ι -> A) where
  toFun v := algebraMap R A ∘ v
  map_add' v w := by simp
  map_smul' t v := by ext; simp [Algebra.smul_def]
