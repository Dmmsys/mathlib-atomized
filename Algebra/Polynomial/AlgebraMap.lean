/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Eval.Algebra
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Monomial

/-!
# Theory of univariate polynomials

We show that `A[X]` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.

## Main definitions

- `Polynomial.aeval`: given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
  the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

- `Polynomial.mapAlgHom` : given `φ : S →ₐ[R] S'`, `mapAlgHom φ` applies `φ` on the
  coefficients of a polynomial in `S[X]`.

-/

@[expose] public section

assert_not_exists Ideal

noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

section CommSemiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable {p q r : R[X]}

/-- Note that this instance also provides `Algebra R R[X]`. -/
/-
**Polynomial.algebraOfAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：algebraOfAlgebra : Algebra R A[X] where smul_def' r p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this instance also provides `Algebra R R[X]`.
-/
instance algebraOfAlgebra : Algebra R A[X] where
  smul_def' r p :=
    toFinsupp_injective <| by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      rw [toFinsupp_smul, toFinsupp_mul, toFinsupp_C]
      exact Algebra.smul_def' _ _
  commutes' r p :=
    toFinsupp_injective <| by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      simp_rw [toFinsupp_mul, toFinsupp_C]
      convert! Algebra.commutes' r p.toFinsupp
  algebraMap := C.comp (algebraMap R A)

@[simp]
/-
**Polynomial.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：algebraMap_apply (r : R) : algebraMap R A[X] r = C (algebraMap R A r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply (r : R) : algebraMap R A[X] r = C (algebraMap R A r) :=
  rfl

@[simp]
/-
**Polynomial.toFinsupp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_algebraMap (r : R) : (algebraMap R A[X] r).toFinsupp = algebraMa
p R _ r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toFinsupp_C`：toFinsupp_C (a : R) : (C a).toFinsupp = single 0
 a
-/
theorem toFinsupp_algebraMap (r : R) : (algebraMap R A[X] r).toFinsupp = algebraMap R _ r :=
  show toFinsupp (C (algebraMap _ _ r)) = _ by
    rw [toFinsupp_C]
    rfl
/-
**Polynomial.ofFinsupp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_algebraMap (r : R) : (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R 
A[X] r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.toFinsupp_injective`：toFinsupp_injective : Function.Injective
 (toFinsupp : R[X] -> AddMonoidAlgebra _ _)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.toFinsupp_algebraMap`：toFinsupp_algebraMap (r : R) : (algebra
Map R A[X] r).toFinsupp = algebraMap R _ r
-/
theorem ofFinsupp_algebraMap (r : R) : (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R A[X] r :=
  toFinsupp_injective (toFinsupp_algebraMap _).symm

/-- When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R[X]`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebraMap` is not available.)
-/
/-
**Polynomial.C_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_eq_algebraMap (r : R) : C r = algebraMap R R[X] r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R
[X]`.

(But note that `C` is defined when `R` is not necessarily commutative, in which 
case
`algebraMap` is not available.)
-/
theorem C_eq_algebraMap (r : R) : C r = algebraMap R R[X] r :=
  rfl

@[simp]
/-
**Polynomial.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：algebraMap_eq : algebraMap R R[X] = C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq : algebraMap R R[X] = C :=
  rfl

/-- `Polynomial.C` as an `AlgHom`. -/
@[simps! apply]
/-
**Polynomial.CAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：CAlgHom : A ->ₐ[R] A[X] where toRingHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.C` as an `AlgHom`.
-/
def CAlgHom : A →ₐ[R] A[X] where
  toRingHom := C
  commutes' _ := rfl

/-- Extensionality lemma for algebra maps out of `A'[X]` over a smaller base ring than `A'`
-/
@[ext 1100]
/-
**Polynomial.algHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：algHom_ext' {f g : A[X] ->ₐ[R] B} (hC : f.comp CAlgHom = g.comp CAlgHom) (
hX : f X = g X) : f = g
参数：hC : f.comp CAlgHom = g.comp CAlgHom；hX : f X = g X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `Polynomial.ringHom_ext'`：ringHom_ext' {S} [Semiring S] {f g : R[X] ->+* 
S} (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Extensionality lemma for algebra maps out of `A'[X]` over a smaller base ring th
an `A'`
-/
theorem algHom_ext' {f g : A[X] →ₐ[R] B}
    (hC : f.comp CAlgHom = g.comp CAlgHom)
    (hX : f X = g X) : f = g :=
  AlgHom.coe_ringHom_injective (ringHom_ext' (congr_arg AlgHom.toRingHom hC) hX)

set_option backward.defeqAttrib.useBackward true in
variable (R) in
open AddMonoidAlgebra in
/-- Algebra isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps!]
/-
**Polynomial.toFinsuppIsoAlg** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toFinsuppIsoAlg : R[X] ≃ₐ[R] R[Nat]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` t
o polynomials.
-/
def toFinsuppIsoAlg : R[X] ≃ₐ[R] R[ℕ] :=
  { toFinsuppIso R with
    commutes' := fun r => by
      dsimp }
/-
**Polynomial.subalgebraNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：subalgebraNontrivial [Nontrivial A] : Nontrivial (Subalgebra R A[X])
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Polynomial.ext_iff`：ext_iff {p q : R[X]} : p = q ↔ forall n, coeff p n =
 coeff q n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
instance subalgebraNontrivial [Nontrivial A] : Nontrivial (Subalgebra R A[X]) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne, SetLike.ext_iff, not_forall]
      refine ⟨X, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top,
        algebraMap_apply]
      intro x
      rw [ext_iff, not_forall]
      refine ⟨1, ?_⟩
      simp⟩⟩

@[simp]
/-
**Polynomial.algHom_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algHom_eval₂_algebraMap {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (p : R[X]) (f : A →ₐ[R] B) (a : A) :
    f (eval₂ (algebraMap R A) a p) = eval₂ (algebraMap R B) (f a) p := by
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow, AlgHom.commutes]

@[simp]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_algebraMap_X {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (p : R[X])
    (f : R[X] →ₐ[R] A) : eval₂ (algebraMap R A) (f X) p = f p := by
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow]
  simp [Polynomial.C_eq_algebraMap]

-- these used to be about `algebraMap ℤ R`, but now the simp-normal form is `Int.castRingHom R`.
@[simp]
/-
**Polynomial.ringHom_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ringHom_eval₂_intCastRingHom {R S : Type*} [Ring R] [Ring S] (p : ℤ[X]) (f : R →+* S)
    (r : R) : f (eval₂ (Int.castRingHom R) r p) = eval₂ (Int.castRingHom S) (f r) p :=
  algHom_eval₂_algebraMap p f.toIntAlgHom r

@[simp]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_intCastRingHom_X {R : Type*} [Ring R] (p : ℤ[X]) (f : ℤ[X] →+* R) :
    eval₂ (Int.castRingHom R) (f X) p = f p :=
  eval₂_algebraMap_X p f.toIntAlgHom

/-- `Polynomial.eval₂` as an `AlgHom` for noncommutative algebras.

This is `Polynomial.eval₂RingHom'` for `AlgHom`s. -/
@[simps!]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.eval₂` as an `AlgHom` for noncommutative algebras.

This is `Polynomial.eval₂RingHom'` for `AlgHom`s.
-/
def eval₂AlgHom (f : A →ₐ[R] B) (b : B) (hf : ∀ a, Commute (f a) b) : A[X] →ₐ[R] B where
  toRingHom := eval₂RingHom' f b hf
  commutes' _ := (eval₂_C _ _).trans (f.commutes _)

section Map

/-- `Polynomial.map` as an `AlgHom` for noncommutative algebras.

  This is the algebra version of `Polynomial.mapRingHom`. -/
/-
**Polynomial.mapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：mapAlgHom (f : A ->ₐ[R] B) : Polynomial A ->ₐ[R] Polynomial B where toRing
Hom
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.map` as an `AlgHom` for noncommutative algebras.

  This is the algebra version of `Polynomial.mapRingHom`.
-/
def mapAlgHom (f : A →ₐ[R] B) : Polynomial A →ₐ[R] Polynomial B where
  toRingHom := mapRingHom f.toRingHom
  commutes' := by simp

@[simp]
/-
**Polynomial.coe_mapAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_mapAlgHom (f : A ->ₐ[R] B) : ⇑(mapAlgHom f) = map f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mapAlgHom (f : A →ₐ[R] B) : ⇑(mapAlgHom f) = map f :=
  rfl

@[simp]
/-
**Polynomial.mapAlgHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapAlgHom_id : mapAlgHom (AlgHom.id R A) = AlgHom.id R (Polynomial A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
-/
theorem mapAlgHom_id : mapAlgHom (AlgHom.id R A) = AlgHom.id R (Polynomial A) :=
  AlgHom.ext fun _x => map_id

@[simp]
/-
**Polynomial.mapAlgHom_coe_ringHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapAlgHom_coe_ringHom (f : A ->ₐ[R] B) : ↑(mapAlgHom f : _ ->ₐ[R] Polynomi
al B) = (mapRingHom ↑f : Polynomial A ->+* Polynomial B)
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem mapAlgHom_coe_ringHom (f : A →ₐ[R] B) :
    ↑(mapAlgHom f : _ →ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A →+* Polynomial B) :=
  rfl

@[simp]
/-
**Polynomial.mapAlgHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapAlgHom_comp (C : Type*) [Semiring C] [Algebra R C] (f : B ->ₐ[R] C) (g 
: A ->ₐ[R] B) : (mapAlgHom f).comp (mapAlgHom g) = mapAlgHom (f.comp g)
参数：C : Type*；f : B ->ₐ[R] C；g : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.algHom_ext'`：algHom_ext' {f g : A[X] ->ₐ[R] B} (hC : f.comp C
AlgHom = g.comp CAlgHom) (hX : f X = g X) : f = g
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.CAlgHom_apply`：∀ {R : Type u} {A : Type z} [inst : CommSemiri
ng R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : A),   Polynomial.CAlgHom
 a = Polynomia…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
-/
theorem mapAlgHom_comp (C : Type*) [Semiring C] [Algebra R C] (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    (mapAlgHom f).comp (mapAlgHom g) = mapAlgHom (f.comp g) := by
  ext <;> simp
/-
**Polynomial.mapAlgHom_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAlgHom_eq_eval₂AlgHom_CAlgHom (f : A →ₐ[R] B) : mapAlgHom f = eval₂AlgHom
    (CAlgHom.comp f) X (fun a => (commute_X (C (f a))).symm) := by
  rfl
/-
**Polynomial.coeff_mapAlgHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coeff_mapAlgHom_apply (f : A ->ₐ[R] B) (p : A[X]) (n : Nat) : coeff (mapAl
gHom f p) n = f (coeff p n)
参数：f : A ->ₐ[R] B；p : A[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_mapAlgHom_apply (f : A →ₐ[R] B) (p : A[X]) (n : ℕ) :
    coeff (mapAlgHom f p) n = f (coeff p n) := by
  simp
/-
**Polynomial.lcoeff_comp_mapAlgHom_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：lcoeff_comp_mapAlgHom_eq (f : A ->ₐ[R] B) (n : Nat) : (lcoeff B n).restric
tScalars R ∘ₗ (mapAlgHom f).toLinearMap = f.toLinearMap ∘ₗ (lcoeff A n).restrict
Scalars R
参数：f : A ->ₐ[R] B；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lcoeff_comp_mapAlgHom_eq (f : A →ₐ[R] B) (n : ℕ) :
    (lcoeff B n).restrictScalars R ∘ₗ (mapAlgHom f).toLinearMap =
      f.toLinearMap ∘ₗ (lcoeff A n).restrictScalars R := by
  ext f; simp
/-
**Polynomial.mapAlgHom_monomial** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mapAlgHom_monomial (f : A ->ₐ[R] B) (n : Nat) (a : A) : mapAlgHom f (monom
ial n a) = monomial n (f a)
参数：f : A ->ₐ[R] B；n : Nat；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapAlgHom_monomial (f : A →ₐ[R] B) (n : ℕ) (a : A) :
    mapAlgHom f (monomial n a) = monomial n (f a) := by simp

/-- If `A` and `B` are isomorphic as `R`-algebras, then so are their polynomial rings -/
/-
**Polynomial.mapAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：mapAlgEquiv (f : A ≃ₐ[R] B) : Polynomial A ≃ₐ[R] Polynomial B
参数：f : A ≃ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are isomorphic as `R`-algebras, then so are their polynomial ring
s
-/
def mapAlgEquiv (f : A ≃ₐ[R] B) : Polynomial A ≃ₐ[R] Polynomial B :=
  AlgEquiv.ofAlgHom (mapAlgHom f.toAlgHom) (mapAlgHom f.symm.toAlgHom) (by simp) (by simp)

@[simp]
/-
**Polynomial.coe_mapAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_mapAlgEquiv (f : A ≃ₐ[R] B) : ⇑(mapAlgEquiv f) = map f
参数：f : A ≃ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mapAlgEquiv (f : A ≃ₐ[R] B) : ⇑(mapAlgEquiv f) = map f :=
  rfl

@[simp]
/-
**Polynomial.mapAlgEquiv_id** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapAlgEquiv_id : mapAlgEquiv (@AlgEquiv.refl R A _ _ _) = AlgEquiv.refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
-/
theorem mapAlgEquiv_id : mapAlgEquiv (@AlgEquiv.refl R A _ _ _) = AlgEquiv.refl :=
  AlgEquiv.ext fun _x => map_id

@[simp]
/-
**Polynomial.mapAlgEquiv_coe_ringHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapAlgEquiv_coe_ringHom (f : A ≃ₐ[R] B) : ↑(mapAlgEquiv f : _ ≃ₐ[R] Polyno
mial B) = (mapRingHom ↑f : Polynomial A ->+* Polynomial B)
参数：f : A ≃ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem mapAlgEquiv_coe_ringHom (f : A ≃ₐ[R] B) :
    ↑(mapAlgEquiv f : _ ≃ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A →+* Polynomial B) :=
  rfl

@[simp]
/-
**Polynomial.mapAlgEquiv_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapAlgEquiv_toAlgHom (f : A ≃ₐ[R] B) : (mapAlgEquiv f : Polynomial A ->ₐ[R
] Polynomial B) = mapAlgHom f
参数：f : A ≃ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAlgEquiv_toAlgHom (f : A ≃ₐ[R] B) :
    (mapAlgEquiv f : Polynomial A →ₐ[R] Polynomial B) = mapAlgHom f := rfl

@[simp]
/-
**Polynomial.mapAlgEquiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapAlgEquiv_comp (C : Type*) [Semiring C] [Algebra R C] (f : A ≃ₐ[R] B) (g
 : B ≃ₐ[R] C) : (mapAlgEquiv f).trans (mapAlgEquiv g) = mapAlgEquiv (f.trans g)
参数：C : Type*；f : A ≃ₐ[R] B；g : B ≃ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapAlgEquiv_comp (C : Type*) [Semiring C] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (mapAlgEquiv f).trans (mapAlgEquiv g) = mapAlgEquiv (f.trans g) := by
  ext
  simp

end Map

end CommSemiring

section aeval

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]
variable [Algebra R A] [Algebra R B]
variable {p q : R[X]} (x : A)

variable (R A) in
/-- Given a valuation `x` of the variable in an `R`-algebra `A`, the bijection induced by the unique
`R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`. -/
@[simps! symm_apply]
/-
**Polynomial.aevalEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：aevalEquiv : A ≃ (R[X] ->ₐ[R] A) where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r

--- 原说明 ---
Given a valuation `x` of the variable in an `R`-algebra `A`, the bijection induc
ed by the unique
`R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.
-/
def aevalEquiv : A ≃ (R[X] →ₐ[R] A) where
  toFun x := eval₂AlgHom (Algebra.ofId _ _) x (Algebra.commutes · _)
  invFun f := f X
  left_inv := eval₂_X _
  right_inv _ := algHom_ext' (Subsingleton.elim ..) <| eval₂_X ..

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

This is a stronger variant of the linear map `Polynomial.leval`. -/
/-
**Polynomial.aeval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：aeval : R[X] ->ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

This is a stronger variant of the linear map `Polynomial.leval`.
-/
def aeval : R[X] →ₐ[R] A :=
  aevalEquiv R A x
/-
**Polynomial.aevalEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：aevalEquiv_apply (x : A) : aevalEquiv R A x = aeval x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma aevalEquiv_apply (x : A) : aevalEquiv R A x = aeval x :=
  rfl

/-- The map `R[X] → S[X]` as an algebra homomorphism. -/
/-
**Polynomial.mapAlg** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：mapAlg (R : Type u) [CommSemiring R] (S : Type v) [Semiring S] [Algebra R 
S] : R[X] ->ₐ[R] S[X]
参数：R : Type u；S : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `R[X] → S[X]` as an algebra homomorphism.
-/
def mapAlg (R : Type u) [CommSemiring R] (S : Type v) [Semiring S] [Algebra R S] :
    R[X] →ₐ[R] S[X] :=
  @aeval _ S[X] _ _ _ (X : S[X])

@[ext 1200]
/-
**Polynomial.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X) : f = g
参数：hX : f X = g X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.algHom_ext'`：algHom_ext' {f g : A[X] ->ₐ[R] B} (hC : f.comp C
AlgHom = g.comp CAlgHom) (hX : f X = g X) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `AlgHom.subsingleton`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem algHom_ext {f g : R[X] →ₐ[R] B} (hX : f X = g X) :
    f = g :=
  algHom_ext' (Subsingleton.elim ..) hX
/-
**Polynomial.aeval_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraMap R A) x p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aeval_def (p : R[X]) : aeval x p = eval₂ (algebraMap R A) x p :=
  rfl

@[simp]
/-
**Polynomial.eval_map_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：eval_map_algebraMap (P : R[X]) (b : B) : (map (algebraMap R B) P).eval b =
 aeval b P
参数：P : R[X]；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
-/
lemma eval_map_algebraMap (P : R[X]) (b : B) :
    (map (algebraMap R B) P).eval b = aeval b P := by
  rw [aeval_def, eval_map]

/-- `mapAlg` is the morphism induced by `R → S`. -/
/-
**Polynomial.mapAlg_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapAlg_eq_map (S : Type v) [Semiring S] [Algebra R S] (p : R[X]) : mapAlg 
R S p = map (algebraMap R S) p
参数：S : Type v；p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapAlg` is the morphism induced by `R → S`.
-/
theorem mapAlg_eq_map (S : Type v) [Semiring S] [Algebra R S] (p : R[X]) :
    mapAlg R S p = map (algebraMap R S) p := by
  rfl
/-
**Polynomial.aeval_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_zero : aeval x (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem aeval_zero : aeval x (0 : R[X]) = 0 :=
  map_zero (aeval x)

@[simp]
/-
**Polynomial.aeval_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_X : aeval x (X : R[X]) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
-/
theorem aeval_X : aeval x (X : R[X]) = x :=
  eval₂_X _ x

@[simp]
/-
**Polynomial.aeval_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
-/
theorem aeval_C (r : R) : aeval x (C r) = algebraMap R A r :=
  eval₂_C _ x

@[simp]
/-
**Polynomial.aeval_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_monomial {n : Nat} {r : R} : aeval x (monomial n r) = algebraMap _ _
 r * x ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_monomial`：eval₂_monomial {n : Nat} {r : R} : (monomial 
n r).eval₂ f x = f r * x ^ n
-/
theorem aeval_monomial {n : ℕ} {r : R} : aeval x (monomial n r) = algebraMap _ _ r * x ^ n :=
  eval₂_monomial _ _
/-
**Polynomial.aeval_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n) = x ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_X_pow`：eval₂_X_pow {n : Nat} : (X ^ n).eval₂ f x = x ^ 
n
-/
theorem aeval_X_pow {n : ℕ} : aeval x ((X : R[X]) ^ n) = x ^ n :=
  eval₂_X_pow _ _
/-
**Polynomial.aeval_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_add : aeval x (p + q) = aeval x p + aeval x q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem aeval_add : aeval x (p + q) = aeval x p + aeval x q :=
  map_add _ _ _
/-
**Polynomial.aeval_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_one : aeval x (1 : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem aeval_one : aeval x (1 : R[X]) = 1 :=
  map_one _
/-
**Polynomial.aeval_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_natCast (n : Nat) : aeval x (n : R[X]) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem aeval_natCast (n : ℕ) : aeval x (n : R[X]) = n :=
  map_natCast _ _
/-
**Polynomial.aeval_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_mul : aeval x (p * q) = aeval x p * aeval x q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem aeval_mul : aeval x (p * q) = aeval x p * aeval x q :=
  map_mul _ _ _
/-
**Polynomial.comp_eq_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：comp_eq_aeval : p.comp q = aeval q p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eq_aeval : p.comp q = aeval q p := rfl
/-
**Polynomial.aeval_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_comp {A : Type*} [Semiring A] [Algebra R A] (x : A) : aeval x (p.com
p q) = aeval (aeval x q) p
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_comp'`：eval₂_comp' : eval₂ (algebraMap R S) x (p.comp q
) = eval₂ (algebraMap R S) (eval₂ (algebraMap R S) x q) p
-/
theorem aeval_comp {A : Type*} [Semiring A] [Algebra R A] (x : A) :
    aeval x (p.comp q) = aeval (aeval x q) p :=
  eval₂_comp' x p q

@[gcongr]
/-
**Polynomial.aeval_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_dvd (h : p ∣ q) : p.aeval x ∣ q.aeval x
参数：h : p ∣ q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem aeval_dvd (h : p ∣ q) : p.aeval x ∣ q.aeval x := _root_.map_dvd (aeval x) h

section IsScalarTower

variable {A : Type*} (B C : Type*) [CommSemiring A] [CommSemiring B] [Semiring C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-
**Polynomial.mapAlg_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapAlg_comp (p : A[X]) : (mapAlg A C) p = (mapAlg B C) (mapAlg A B p)
参数：p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mapAlg_eq_map`：mapAlg_eq_map (S : Type v) [Semiring S] [Algeb
ra R S] (p : R[X]) : mapAlg R S p = map (algebraMap R S) p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapAlg_comp (p : A[X]) : (mapAlg A C) p = (mapAlg B C) (mapAlg A B p) := by
  simp [mapAlg_eq_map, map_map, IsScalarTower.algebraMap_eq A B C]
/-
**Polynomial.coeff_zero_of_isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_zero_of_isScalarTower (p : A[X]) : (algebraMap B C) ((algebraMap A B
) (p.coeff 0)) = (mapAlg A C p).coeff 0
参数：p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mapAlg_eq_map`：mapAlg_eq_map (S : Type v) [Semiring S] [Algeb
ra R S] (p : R[X]) : mapAlg R S p = map (algebraMap R S) p
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
-/
theorem coeff_zero_of_isScalarTower (p : A[X]) :
    (algebraMap B C) ((algebraMap A B) (p.coeff 0)) = (mapAlg A C p).coeff 0 := by
  rw [mapAlg_eq_map, coeff_map, IsScalarTower.algebraMap_eq A B C, RingHom.comp_apply]

end IsScalarTower

/-- Two polynomials `p` and `q` such that `p(q(X))=X` and `q(p(X))=X`
  induces an automorphism of the polynomial algebra. -/
@[simps! apply]
/-
**Polynomial.algEquivOfCompEqX** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：algEquivOfCompEqX (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X) :
 R[X] ≃ₐ[R] R[X]
参数：p q : R[X]；hpq : p.comp q = X；hqp : q.comp p = X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two polynomials `p` and `q` such that `p(q(X))=X` and `q(p(X))=X`
  induces an automorphism of the polynomial algebra.
-/
def algEquivOfCompEqX (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X) : R[X] ≃ₐ[R] R[X] := by
  refine AlgEquiv.ofAlgHom (aeval p) (aeval q) ?_ ?_ <;>
    exact AlgHom.ext fun _ ↦ by simp [← comp_eq_aeval, comp_assoc, hpq, hqp]

@[simp]
/-
**Polynomial.algEquivOfCompEqX_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：algEquivOfCompEqX_eq_iff (p q p' q' : R[X]) (hpq : p.comp q = X) (hqp : q.
comp p = X) (hpq' : p'.comp q' = X) (hqp' : q'.comp p' = X) : algEquivOfCompEqX 
p q hpq hqp = algEquivOfCompEqX p' q' hpq' hqp' ↔ p = p'
参数：p q p' q' : R[X]；hpq : p.comp q = X；hqp : q.comp p = X；hpq' : p'.comp q' = X；
hqp' : q'.comp p' = X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.algEquivOfCompEqX_apply`：∀ {R : Type u} [inst : CommSemiring 
R] (p q : Polynomial R) (hpq : p.comp q = Polynomial.X)   (hqp : q.comp p = Poly
nomial.X) (a : Polynomia…
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.algEquivOfCompEqX.congr_simp`：∀ {R : Type u} [inst : CommSemi
ring R] (p p_1 : Polynomial R) (e_p : p = p_1) (q q_1 : Polynomial R) (e_q : q =
 q_1)   (hpq : p.comp q = Pol…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquivOfCompEqX_eq_iff (p q p' q' : R[X])
    (hpq : p.comp q = X) (hqp : q.comp p = X) (hpq' : p'.comp q' = X) (hqp' : q'.comp p' = X) :
    algEquivOfCompEqX p q hpq hqp = algEquivOfCompEqX p' q' hpq' hqp' ↔ p = p' :=
  ⟨fun h ↦ by simpa using congr($h X), fun h ↦ by ext1; simp [h]⟩

@[simp]
/-
**Polynomial.algEquivOfCompEqX_symm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：algEquivOfCompEqX_symm (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p =
 X) : (algEquivOfCompEqX p q hpq hqp).symm = algEquivOfCompEqX q p hqp hpq
参数：p q : R[X]；hpq : p.comp q = X；hqp : q.comp p = X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquivOfCompEqX_symm (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X) :
    (algEquivOfCompEqX p q hpq hqp).symm = algEquivOfCompEqX q p hqp hpq := rfl

/-- The automorphism of the polynomial algebra given by `p(X) ↦ p(a * X + b)`,
  with inverse `p(X) ↦ p(a⁻¹ * (X - b))`. -/
@[simps!]
/-
**Polynomial.algEquivCMulXAddC** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：algEquivCMulXAddC {R : Type*} [CommRing R] (a b : R) [Invertible a] : R[X]
 ≃ₐ[R] R[X]
参数：a b : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The automorphism of the polynomial algebra given by `p(X) ↦ p(a * X + b)`,
  with inverse `p(X) ↦ p(a⁻¹ * (X - b))`.
-/
def algEquivCMulXAddC {R : Type*} [CommRing R] (a b : R) [Invertible a] : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (C a * X + C b) (C ⅟a * (X - C b))
    (by simp [← C_mul, ← mul_assoc]) (by simp [← C_mul, ← mul_assoc])
/-
**Polynomial.algEquivCMulXAddC_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：algEquivCMulXAddC_symm_eq {R : Type*} [CommRing R] (a b : R) [Invertible a
] : (algEquivCMulXAddC a b).symm = algEquivCMulXAddC (⅟a) (-⅟a * b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.algEquivCMulXAddC_symm_apply`：∀ {R : Type u_3} [inst : CommRi
ng R] (a b : R) [inst_1 : Invertible a] (a_1 : Polynomial R),   (Polynomial.algE
quivCMulXAddC a b).symm a_1 =…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Polynomial.algEquivCMulXAddC_apply`：∀ {R : Type u_3} [inst : CommRing R]
 (a b : R) [inst_1 : Invertible a] (a_1 : Polynomial R),   (Polynomial.algEquivC
MulXAddC a b) a_1 = (Pol…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquivCMulXAddC_symm_eq {R : Type*} [CommRing R] (a b : R) [Invertible a] :
    (algEquivCMulXAddC a b).symm = algEquivCMulXAddC (⅟a) (-⅟a * b) := by
  ext p : 1
  simp only [algEquivCMulXAddC_symm_apply, neg_mul, algEquivCMulXAddC_apply, map_neg, map_mul]
  congr
  simp [mul_add, sub_eq_add_neg]

/-- The automorphism of the polynomial algebra given by `p(X) ↦ p(X+t)`,
  with inverse `p(X) ↦ p(X-t)`. -/
@[simps! apply]
/-
**Polynomial.algEquivAevalXAddC** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：algEquivAevalXAddC {R : Type*} [CommRing R] (t : R) : R[X] ≃ₐ[R] R[X]
参数：t : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The automorphism of the polynomial algebra given by `p(X) ↦ p(X+t)`,
  with inverse `p(X) ↦ p(X-t)`.
-/
def algEquivAevalXAddC {R : Type*} [CommRing R] (t : R) : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (X + C t) (X - C t) (by simp) (by simp)

@[simp]
/-
**Polynomial.algEquivAevalXAddC_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：algEquivAevalXAddC_eq_iff {R : Type*} [CommRing R] (t t' : R) : algEquivAe
valXAddC t = algEquivAevalXAddC t' ↔ t = t'
参数：t t' : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem algEquivAevalXAddC_eq_iff {R : Type*} [CommRing R] (t t' : R) :
    algEquivAevalXAddC t = algEquivAevalXAddC t' ↔ t = t' := by
  simp [algEquivAevalXAddC]

@[simp]
/-
**Polynomial.algEquivAevalXAddC_symm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：algEquivAevalXAddC_symm {R : Type*} [CommRing R] (t : R) : (algEquivAevalX
AddC t).symm = algEquivAevalXAddC (-t)
参数：t : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.algEquivOfCompEqX.congr_simp`：∀ {R : Type u} [inst : CommSemi
ring R] (p p_1 : Polynomial R) (e_p : p = p_1) (q q_1 : Polynomial R) (e_q : q =
 q_1)   (hpq : p.comp q = Pol…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquivAevalXAddC_symm {R : Type*} [CommRing R] (t : R) :
    (algEquivAevalXAddC t).symm = algEquivAevalXAddC (-t) := by
  simp [algEquivAevalXAddC, sub_eq_add_neg]

/-- The involutive automorphism of the polynomial algebra given by `p(X) ↦ p(-X)`. -/
@[simps!]
/-
**Polynomial.algEquivAevalNegX** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：algEquivAevalNegX {R : Type*} [CommRing R] : R[X] ≃ₐ[R] R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The involutive automorphism of the polynomial algebra given by `p(X) ↦ p(-X)`.
-/
def algEquivAevalNegX {R : Type*} [CommRing R] : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (-X) (-X) (by simp) (by simp)
/-
**Polynomial.comp_neg_X_comp_neg_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：comp_neg_X_comp_neg_X {R : Type*} [CommRing R] (p : R[X]) : (p.comp (-X)).
comp (-X) = p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.comp_assoc`：comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : 
R[X]) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.neg_comp`：neg_comp : (-p).comp q = -p.comp q
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Polynomial.comp_X`：comp_X : p.comp X = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_neg_X_comp_neg_X {R : Type*} [CommRing R] (p : R[X]) :
    (p.comp (-X)).comp (-X) = p := by
  rw [comp_assoc]
  simp only [neg_comp, X_comp, neg_neg, comp_X]
/-
**Polynomial.aeval_algHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (f x) = f.comp (aeval x)
参数：f : A ->ₐ[R] B；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aeval_algHom (f : A →ₐ[R] B) (x : A) : aeval (f x) = f.comp (aeval x) :=
  algHom_ext <| by simp only [aeval_X, AlgHom.comp_apply]

@[simp]
/-
**Polynomial.aeval_X_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_X_left : aeval (X : R[X]) = AlgHom.id R R[X]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
theorem aeval_X_left : aeval (X : R[X]) = AlgHom.id R R[X] :=
  algHom_ext <| aeval_X X
/-
**Polynomial.aeval_X_left_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_X_left_apply (p : R[X]) : aeval X p = p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Polynomial.aeval_X_left`：aeval_X_left : aeval (X : R[X]) = AlgHom.id R R
[X]
-/
theorem aeval_X_left_apply (p : R[X]) : aeval X p = p :=
  AlgHom.congr_fun (@aeval_X_left R _) p
/-
**Polynomial.aeval_X_left_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：aeval_X_left_eq_map [CommSemiring S] [Algebra R S] (p : R[X]) : aeval X p 
= map (algebraMap R S) p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma aeval_X_left_eq_map [CommSemiring S] [Algebra R S] (p : R[X]) :
    aeval X p = map (algebraMap R S) p :=
  rfl
/-
**Polynomial.eval_unique** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_unique (φ : R[X] ->ₐ[R] A) (p) : φ p = eval₂ (algebraMap R A) (φ X) p
参数：φ : R[X] ->ₐ[R] A；p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
· 使用定理 `Polynomial.aeval_X_left`：aeval_X_left : aeval (X : R[X]) = AlgHom.id R R
[X]
· 使用定理 `AlgHom.comp_id`：comp_id : φ.comp (AlgHom.id R A) = φ
-/
theorem eval_unique (φ : R[X] →ₐ[R] A) (p) : φ p = eval₂ (algebraMap R A) (φ X) p := by
  rw [← aeval_def, aeval_algHom, aeval_X_left, AlgHom.comp_id]
/-
**Polynomial.aeval_algHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_algHom_apply {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : 
F) (x : A) (p : R[X]) : aeval (f x) p = f (aeval x p)
参数：f : F；x : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
theorem aeval_algHom_apply {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (x : A) (p : R[X]) :
    aeval (f x) p = f (aeval x p) := by
  refine Polynomial.induction_on p (by simp [AlgHomClass.commutes]) (fun p q hp hq => ?_)
    (by simp [AlgHomClass.commutes])
  rw [map_add, hp, hq, ← map_add, ← map_add]
/-
**Polynomial.aeval_op_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_op_apply (x : A) (p : R[X]) : aeval (MulOpposite.op x) p = MulOpposi
te.op (aeval x p)
参数：x : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
-/
theorem aeval_op_apply (x : A) (p : R[X]) :
    aeval (MulOpposite.op x) p = MulOpposite.op (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n c => simp [aeval_monomial, MulOpposite.op_pow, Algebra.commutes]
/-
**Polynomial.aeval_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_smul (f : R[X]) {G : Type*} [Monoid G] [MulSemiringAction G A] [SMul
CommClass G R A] (g : G) (x : A) : f.aeval (g • x) = g • (f.aeval x)
参数：f : R[X]；g : G；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulSemiringAction.toAlgHom_apply`：∀ {M : Type u_1} (R : Type u_3) (A : T
ype u_4) [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   
[inst_3 : Monoid M] [i…
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
-/
theorem aeval_smul (f : R[X]) {G : Type*} [Monoid G] [MulSemiringAction G A] [SMulCommClass G R A]
    (g : G) (x : A) : f.aeval (g • x) = g • (f.aeval x) := by
  rw [← MulSemiringAction.toAlgHom_apply R, aeval_algHom_apply, MulSemiringAction.toAlgHom_apply]

@[simp]
/-
**Polynomial.coe_aeval_mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coe_aeval_mk_apply {S : Subalgebra R A} (h : x in S) : (aeval (⟨x, h⟩ : S)
 p : A) = aeval x p
参数：h : x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
-/
lemma coe_aeval_mk_apply {S : Subalgebra R A} (h : x ∈ S) :
    (aeval (⟨x, h⟩ : S) p : A) = aeval x p :=
  (aeval_algHom_apply S.val (⟨x, h⟩ : S) p).symm
/-
**Polynomial.aeval_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_algEquiv (f : A ≃ₐ[R] B) (x : A) : aeval (f x) = (f : A ->ₐ[R] B).co
mp (aeval x)
参数：f : A ≃ₐ[R] B；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
-/
theorem aeval_algEquiv (f : A ≃ₐ[R] B) (x : A) : aeval (f x) = (f : A →ₐ[R] B).comp (aeval x) :=
  aeval_algHom (f : A →ₐ[R] B) x
/-
**Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：aeval_algebraMap_apply_eq_algebraMap_eval (x : R) (p : R[X]) : aeval (alge
braMap R A x) p = algebraMap R A (p.eval x)
参数：x : R；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
-/
theorem aeval_algebraMap_apply_eq_algebraMap_eval (x : R) (p : R[X]) :
    aeval (algebraMap R A x) p = algebraMap R A (p.eval x) :=
  aeval_algHom_apply (Algebra.ofId R A) x p

/-- Polynomial evaluation on a pair is a product of the evaluations on the components. -/
/-
**Polynomial.aeval_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_prod (x : A × B) : aeval (R
参数：x : A × B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.prod_comp`：prod_comp {C' : Type*} [Semiring C'] [Algebra R C'] (f
 : A ->ₐ[R] B) (g : B ->ₐ[R] C) (g' : B ->ₐ[R] C') : (g.prod g').comp f = (g.com
p f).p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)

--- 原说明 ---
Polynomial evaluation on a pair is a product of the evaluations on the component
s.
-/
theorem aeval_prod (x : A × B) : aeval (R := R) x = (aeval x.1).prod (aeval x.2) :=
  aeval_algHom (.fst R A B) x ▸ aeval_algHom (.snd R A B) x ▸
    (aeval x).prod_comp (.fst R A B) (.snd R A B)

/-- Polynomial evaluation on a pair is a pair of evaluations. -/
/-
**Polynomial.aeval_prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_prod_apply (x : A × B) (p : Polynomial R) : p.aeval x = (p.aeval x.1
, p.aeval x.2)
参数：x : A × B；p : Polynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_prod`：aeval_prod (x : A × B) : aeval (R
· 使用定理 `AlgHom.prod_apply`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} {C : T
ype u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Algebra R A] 
[inst_3…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Polynomial evaluation on a pair is a pair of evaluations.
-/
theorem aeval_prod_apply (x : A × B) (p : Polynomial R) :
    p.aeval x = (p.aeval x.1, p.aeval x.2) := by simp [aeval_prod]

section Pi

variable {I : Type*} {A : I → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
variable (x : Π i, A i) (p : R[X])

/-- Polynomial evaluation on an indexed tuple is the indexed product of the evaluations
on the components.
Generalizes `Polynomial.aeval_prod` to indexed products. -/
/-
**Polynomial.aeval_pi** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_pi (x : Π i, A i) : aeval (R
参数：x : Π i, A i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.pi_comp`：∀ {ι : Type u_1} {R : Type u_2} {A : ι → Type u_3} [inst
 : CommSemiring R] [inst_1 : (i : ι) → Semiring (A i)]   [inst_2 : (i : ι) → Alg
ebra…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)

--- 原说明 ---
Polynomial evaluation on an indexed tuple is the indexed product of the evaluati
ons
on the components.
Generalizes `Polynomial.aeval_prod` to indexed products.
-/
theorem aeval_pi (x : Π i, A i) : aeval (R := R) x = AlgHom.pi (fun i ↦ aeval (x i)) :=
  (funext fun i ↦ aeval_algHom (Pi.evalAlgHom R A i) x) ▸
    (AlgHom.pi_comp (Pi.evalAlgHom R A) (aeval x))
/-
**Polynomial.aeval_pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_pi_apply : p.aeval x = fun j => p.aeval (x j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.aeval_pi_apply₂`：aeval_pi_apply₂ (j : I) : p.aeval x j = p.ae
val (x j)
-/
theorem aeval_pi_apply₂ (j : I) : p.aeval x j = p.aeval (x j) :=
  aeval_pi (R := R) x ▸ AlgHom.pi_apply (fun i ↦ aeval (x i)) p j

/-- Polynomial evaluation on an indexed tuple is the indexed tuple of the evaluations
on the components.
Generalizes `Polynomial.aeval_prod_apply` to indexed products. -/
/-
**Polynomial.aeval_pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_pi_apply : p.aeval x = fun j => p.aeval (x j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.aeval_pi_apply₂`：aeval_pi_apply₂ (j : I) : p.aeval x j = p.ae
val (x j)

--- 原说明 ---
Polynomial evaluation on an indexed tuple is the indexed tuple of the evaluation
s
on the components.
Generalizes `Polynomial.aeval_prod_apply` to indexed products.
-/
theorem aeval_pi_apply : p.aeval x = fun j ↦ p.aeval (x j) :=
  funext fun j ↦ aeval_pi_apply₂ x p j

end Pi

@[simp]
/-
**Polynomial.coe_aeval_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_aeval_eq_eval (r : R) : (aeval r : R[X] -> R) = eval r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_aeval_eq_eval (r : R) : (aeval r : R[X] → R) = eval r :=
  rfl

@[simp]
/-
**Polynomial.coe_aeval_eq_evalRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_aeval_eq_evalRingHom (x : R) : ((aeval x : R[X] ->ₐ[R] R) : R[X] ->+* 
R) = evalRingHom x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem coe_aeval_eq_evalRingHom (x : R) :
    ((aeval x : R[X] →ₐ[R] R) : R[X] →+* R) = evalRingHom x :=
  rfl

@[simp]
/-
**Polynomial.aeval_fn_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_fn_apply {X : Type*} (g : R[X]) (f : X -> R) (x : X) : ((aeval f) g)
 x = aeval (f x) g
参数：g : R[X]；f : X -> R；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
-/
theorem aeval_fn_apply {X : Type*} (g : R[X]) (f : X → R) (x : X) :
    ((aeval f) g) x = aeval (f x) g :=
  (aeval_algHom_apply (Pi.evalAlgHom R (fun _ => R) x) f g).symm

@[norm_cast]
/-
**Polynomial.aeval_subalgebra_coe** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_subalgebra_coe (g : R[X]) {A : Type*} [Semiring A] [Algebra R A] (s 
: Subalgebra R A) (f : s) : (aeval f g : A) = aeval (f : A) g
参数：g : R[X]；s : Subalgebra R A；f : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
-/
theorem aeval_subalgebra_coe (g : R[X]) {A : Type*} [Semiring A] [Algebra R A] (s : Subalgebra R A)
    (f : s) : (aeval f g : A) = aeval (f : A) g :=
  (aeval_algHom_apply s.val f g).symm
/-
**Polynomial.coeff_zero_eq_aeval_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_zero_eq_aeval_zero (p : R[X]) : p.coeff 0 = aeval 0 p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_zero_eq_aeval_zero (p : R[X]) : p.coeff 0 = aeval 0 p := by
  simp [coeff_zero_eq_eval_zero]
/-
**Polynomial.coeff_zero_eq_aeval_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_zero_eq_aeval_zero' (p : R[X]) : algebraMap R A (p.coeff 0) = aeval 
(0 : A) p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_at_zero`：eval₂_at_zero : p.eval₂ f 0 = f (coeff p 0)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_zero_eq_aeval_zero' (p : R[X]) : algebraMap R A (p.coeff 0) = aeval (0 : A) p := by
  simp [aeval_def]
/-
**Polynomial.map_aeval_eq_aeval_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_aeval_eq_aeval_map {S T U : Type*} [Semiring S] [CommSemiring T] [Semi
ring U] [Algebra R S] [Algebra T U] {φ : R ->+* T} {ψ : S ->+* U} (h : (algebraM
ap T U).comp φ = ψ.comp (algebraMap R S)) (p : R[X]) (a : S) : ψ (aeval a p) = a
eval (ψ a) (p.map φ)
参数：h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)；p : R[X]；a : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Polynomial.eval₂_at_apply`：eval₂_at_apply {S : Type*} [Semiring S] (f : 
R ->+* S) (r : R) : p.eval₂ f (f r) = f (p.eval r)
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
-/
theorem map_aeval_eq_aeval_map {S T U : Type*} [Semiring S] [CommSemiring T] [Semiring U]
    [Algebra R S] [Algebra T U] {φ : R →+* T} {ψ : S →+* U}
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) (p : R[X]) (a : S) :
    ψ (aeval a p) = aeval (ψ a) (p.map φ) := by
  conv_rhs => rw [← eval_map_algebraMap]
  rw [map_map, h, ← map_map, eval_map, eval₂_at_apply, aeval_def, eval_map]
/-
**Polynomial.aeval_eq_aeval_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_eq_aeval_map [Semiring S] [CommSemiring T] [Algebra R S] [Algebra T 
S] {φ : R ->+* T} (h : (algebraMap T S).comp φ = (algebraMap R S)) (p : R[X]) (a
 : S) : aeval a p = aeval a (p.map φ)
参数：h : (algebraMap T S).comp φ = (algebraMap R S)；p : R[X]；a : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.map_aeval_eq_aeval_map`：map_aeval_eq_aeval_map {S T U : Type*
} [Semiring S] [CommSemiring T] [Semiring U] [Algebra R S] [Algebra T U] {φ : R 
->+* T} {ψ : S ->+* U} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.id_comp`：id_comp (f : α ->+* β) : (id β).comp f = f
-/
theorem aeval_eq_aeval_map [Semiring S] [CommSemiring T] [Algebra R S]
    [Algebra T S] {φ : R →+* T} (h : (algebraMap T S).comp φ = (algebraMap R S))
    (p : R[X]) (a : S) : aeval a p = aeval a (p.map φ) :=
  map_aeval_eq_aeval_map (by rwa [RingHom.id_comp]) p a
/-
**Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：aeval_eq_zero_of_dvd_aeval_eq_zero {x : B} (h₁ : p ∣ q) (h₂ : aeval x p = 
0) : aeval x q = 0
参数：h₁ : p ∣ q；h₂ : aeval x p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Polynomial.aeval_dvd`：aeval_dvd (h : p ∣ q) : p.aeval x ∣ q.aeval x
-/
theorem aeval_eq_zero_of_dvd_aeval_eq_zero {x : B} (h₁ : p ∣ q) (h₂ : aeval x p = 0) :
    aeval x q = 0 := zero_dvd_iff.mp (h₂ ▸ aeval_dvd _ h₁)

section Semiring

variable [Semiring S] {f : R →+* S}

/-
**Polynomial.aeval_eq_sum_range** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_eq_sum_range [Algebra R S] {p : R[X]} (x : S) : aeval x p = ∑ i in F
inset.range (p.natDegree + 1), p.coeff i • x ^ i
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Polynomial.eval₂_eq_sum_range`：eval₂_eq_sum_range : p.eval₂ f x = ∑ i in
 Finset.range (p.natDegree + 1), f (p.coeff i) * x ^ i
-/
theorem aeval_eq_sum_range [Algebra R S] {p : R[X]} (x : S) :
    aeval x p = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range (algebraMap R S) x
/-
**Polynomial.aeval_eq_sum_range'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_eq_sum_range' [Algebra R S] {p : R[X]} {n : Nat} (hn : p.natDegree <
 n) (x : S) : aeval x p = ∑ i in Finset.range n, p.coeff i • x ^ i
参数：hn : p.natDegree < n；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Polynomial.eval₂_eq_sum_range'`：eval₂_eq_sum_range' (f : R ->+* S) {p : 
R[X]} {n : Nat} (hn : p.natDegree < n) (x : S) : eval₂ f x p = ∑ i in Finset.ran
ge n, f (p.coeff i) …
-/
theorem aeval_eq_sum_range' [Algebra R S] {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : S) :
    aeval x p = ∑ i ∈ Finset.range n, p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range' (algebraMap R S) hn x
/-
**Polynomial.isRoot_of_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isRoot_of_eval₂_map_eq_zero (hf : Function.Injective f) {r : R} :
    eval₂ f (f r) p = 0 → p.IsRoot r := by
  intro h
  apply hf
  rw [← eval₂_hom, h, f.map_zero]
/-
**Polynomial.isRoot_of_aeval_algebraMap_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：isRoot_of_aeval_algebraMap_eq_zero [Algebra R S] [FaithfulSMul R S] {p : R
[X]} {r : R} (hr : p.aeval (algebraMap R S r) = 0) : p.IsRoot r
参数：hr : p.aeval (algebraMap R S r) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isRoot_of_eval₂_map_eq_zero`：isRoot_of_eval₂_map_eq_zero (hf 
: Function.Injective f) {r : R} : eval₂ f (f r) p = 0 -> p.IsRoot r
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem isRoot_of_aeval_algebraMap_eq_zero [Algebra R S] [FaithfulSMul R S] {p : R[X]} {r : R}
    (hr : p.aeval (algebraMap R S r) = 0) : p.IsRoot r :=
  isRoot_of_eval₂_map_eq_zero (FaithfulSMul.algebraMap_injective _ _) hr

end Semiring

section CommSemiring

section aevalTower

variable [CommSemiring S] [Algebra S R] [Algebra S A'] [Algebra S B]

/-- Version of `aeval` for defining algebra homs out of `R[X]` over a smaller base ring
  than `R`. -/
/-
**Polynomial.aevalTower** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：aevalTower (f : R ->ₐ[S] A') (x : A') : R[X] ->ₐ[S] A'
参数：f : R ->ₐ[S] A'；x : A'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `aeval` for defining algebra homs out of `R[X]` over a smaller base r
ing
  than `R`.
-/
def aevalTower (f : R →ₐ[S] A') (x : A') : R[X] →ₐ[S] A' :=
  eval₂AlgHom f x fun _ => Commute.all _ _

variable (g : R →ₐ[S] A') (y : A')

@[simp]
/-
**Polynomial.aevalTower_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aevalTower_X : aevalTower g y X = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
-/
theorem aevalTower_X : aevalTower g y X = y :=
  eval₂_X _ _

@[simp]
/-
**Polynomial.aevalTower_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aevalTower_C (x : R) : aevalTower g y (C x) = g x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
-/
theorem aevalTower_C (x : R) : aevalTower g y (C x) = g x :=
  eval₂_C _ _

@[simp]
/-
**Polynomial.aevalTower_comp_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aevalTower_comp_C : (aevalTower g y : R[X] ->+* A').comp C = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aevalTower_C`：aevalTower_C (x : R) : aevalTower g y (C x) = g
 x
-/
theorem aevalTower_comp_C : (aevalTower g y : R[X] →+* A').comp C = g :=
  RingHom.ext <| aevalTower_C _ _
/-
**Polynomial.aevalTower_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R R[X] x) = g x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
-/
theorem aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R R[X] x) = g x :=
  eval₂_C _ _
/-
**Polynomial.aevalTower_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aevalTower_comp_algebraMap : (aevalTower g y : R[X] ->+* A').comp (algebra
Map R R[X]) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.aevalTower_comp_C`：aevalTower_comp_C : (aevalTower g y : R[X]
 ->+* A').comp C = g
-/
theorem aevalTower_comp_algebraMap : (aevalTower g y : R[X] →+* A').comp (algebraMap R R[X]) = g :=
  aevalTower_comp_C _ _
/-
**Polynomial.aevalTower_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aevalTower_toAlgHom (x : R) : aevalTower g y (IsScalarTower.toAlgHom S R R
[X] x) = g x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.aevalTower_algebraMap`：aevalTower_algebraMap (x : R) : aevalT
ower g y (algebraMap R R[X] x) = g x
-/
theorem aevalTower_toAlgHom (x : R) : aevalTower g y (IsScalarTower.toAlgHom S R R[X] x) = g x :=
  aevalTower_algebraMap _ _ _

@[simp]
/-
**Polynomial.aevalTower_comp_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aevalTower_comp_toAlgHom : (aevalTower g y).comp (IsScalarTower.toAlgHom S
 R R[X]) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.aevalTower_comp_algebraMap`：aevalTower_comp_algebraMap : (aev
alTower g y : R[X] ->+* A').comp (algebraMap R R[X]) = g
-/
theorem aevalTower_comp_toAlgHom : (aevalTower g y).comp (IsScalarTower.toAlgHom S R R[X]) = g :=
  AlgHom.coe_ringHom_injective <| aevalTower_comp_algebraMap _ _

@[simp]
/-
**Polynomial.aevalTower_id** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aevalTower_id : aevalTower (AlgHom.id S S) = aeval
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalTower_X`：aevalTower_X : aevalTower g y X = y
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aevalTower_id : aevalTower (AlgHom.id S S) = aeval := by
  ext s
  simp only [eval_X, aevalTower_X, coe_aeval_eq_eval]

@[simp]
/-
**Polynomial.aevalTower_ofId** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aevalTower_ofId : aevalTower (Algebra.ofId S A') = aeval
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalTower_X`：aevalTower_X : aevalTower g y X = y
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aevalTower_ofId : aevalTower (Algebra.ofId S A') = aeval := by
  ext
  simp only [aeval_X, aevalTower_X]

end aevalTower

open LinearMap TensorProduct in
/-
**Polynomial.X_pow_smul_rTensor_monomial** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_smul_rTensor_monomial [CommSemiring S] [Algebra R S] {N : Type*} [Ad
dCommMonoid N] [Module R N] (k : Nat) (sn : S otimes[R] N) : X (R
参数：k : Nat；sn : S otimes[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
lemma X_pow_smul_rTensor_monomial [CommSemiring S] [Algebra R S] {N : Type*}
    [AddCommMonoid N] [Module R N] (k : ℕ) (sn : S ⊗[R] N) :
    X (R := S) ^ k • (LinearMap.rTensor N ((monomial 0).restrictScalars R)) sn =
      (LinearMap.rTensor N ((monomial k).restrictScalars R)) sn := by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul s n =>
    simp only [rTensor_tmul, coe_restrictScalars, monomial_zero_left]
    rw [smul_tmul', smul_eq_mul, mul_comm, C_mul_X_pow_eq_monomial]


end CommSemiring

section CommRing

variable [CommRing S] {f : R →+* S}

/-
**Polynomial.dvd_term_of_dvd_eval_of_dvd_terms** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : S[X]} (i : Nat) (dvd_eval
 : p ∣ f.eval z) (dvd_terms : forall j != i, p ∣ f.coeff j * z ^ j) : p ∣ f.coef
f i * z ^ i
参数：i : Nat；dvd_eval : p ∣ f.eval z；dvd_terms : forall j != i, p ∣ f.coeff j * z 
^ j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dvd_add_left`：dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b
· 使用引理 `Finset.dvd_sum`：dvd_sum (h : forall i in s, a ∣ f i) : a ∣ ∑ i in s, f i
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Polynomial.sum_def`：sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f 
: Nat -> R -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
· 使用定理 `Polynomial.eval₂_eq_sum`：eval₂_eq_sum {f : R ->+* S} {x : S} : p.eval₂ f
 x = p.sum fun e a => f a * x ^ e
· 使用定理 `Polynomial.eval.eq_1`：∀ {R : Type u} [inst : Semiring R] (x : R) (p : Po
lynomial R), Polynomial.eval x p = Polynomial.eval₂ (RingHom.id R) x p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.notMem_support_iff`：notMem_support_iff : n ∉ p.support ↔ p.co
eff n = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
-/
theorem dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : S[X]} (i : ℕ) (dvd_eval : p ∣ f.eval z)
    (dvd_terms : ∀ j ≠ i, p ∣ f.coeff j * z ^ j) : p ∣ f.coeff i * z ^ i := by
  by_cases hi : i ∈ f.support
  · rw [eval, eval₂_eq_sum, sum_def] at dvd_eval
    rw [← Finset.insert_erase hi, Finset.sum_insert (Finset.notMem_erase _ _)] at dvd_eval
    refine (dvd_add_left ?_).mp dvd_eval
    apply Finset.dvd_sum
    intro j hj
    exact dvd_terms j (Finset.ne_of_mem_erase hj)
  · convert! dvd_zero p
    rw [notMem_support_iff] at hi
    simp [hi]
/-
**Polynomial.dvd_term_of_isRoot_of_dvd_terms** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：dvd_term_of_isRoot_of_dvd_terms {r p : S} {f : S[X]} (i : Nat) (hr : f.IsR
oot r) (h : forall j != i, p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i
参数：i : Nat；hr : f.IsRoot r；h : forall j != i, p ∣ f.coeff j * r ^ j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.dvd_term_of_dvd_eval_of_dvd_terms`：dvd_term_of_dvd_eval_of_dv
d_terms {z p : S} {f : S[X]} (i : Nat) (dvd_eval : p ∣ f.eval z) (dvd_terms : fo
rall j != i, p ∣ f.coeff j * z ^ j…
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dvd_term_of_isRoot_of_dvd_terms {r p : S} {f : S[X]} (i : ℕ) (hr : f.IsRoot r)
    (h : ∀ j ≠ i, p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i :=
  dvd_term_of_dvd_eval_of_dvd_terms i (Eq.symm hr ▸ dvd_zero p) h

end CommRing

end aeval

section Ring

variable [Ring R]

/-- The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - C r)` is sent to zero when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
/-
**Polynomial.eval_mul_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_mul_X_sub_C {p : R[X]} (r : R) : (p * (X - C r)).eval r = 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `Polynomial.eval_mul_C_of_commute`：eval_mul_C_of_commute (h : Commute a x
) : (p * C a).eval x = p.eval x * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The evaluation map is not generally multiplicative when the coefficient ring is 
noncommutative,
but nevertheless any polynomial of the form `p * (X - C r)` is sent to zero when
 evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
theorem eval_mul_X_sub_C {p : R[X]} (r : R) : (p * (X - C r)).eval r = 0 := by
  rw [mul_sub, eval_sub, eval_mul_X, eval_mul_C_of_commute] <;> simp
/-
**Polynomial.not_isUnit_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：not_isUnit_X_sub_C [Nontrivial R] (r : R) : ¬IsUnit (X - C r)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zero_ne_one'`：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_mul_X_sub_C`：eval_mul_X_sub_C {p : R[X]} (r : R) : (p * 
(X - C r)).eval r = 0
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
-/
theorem not_isUnit_X_sub_C [Nontrivial R] (r : R) : ¬IsUnit (X - C r) :=
  fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ => zero_ne_one' R <| by rw [← eval_mul_X_sub_C, hgf, eval_one]

end Ring

section CommRing
variable [CommRing R] {p : R[X]} {t : R}

@[simp]
/-
**Polynomial.aeval_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_neg {p : R[X]} [Ring A] [Algebra R A] (x : A) : aeval x (-p) = -aeva
l x p
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem aeval_neg {p : R[X]} [Ring A] [Algebra R A] (x : A) :
    aeval x (-p) = -aeval x p := map_neg ..

@[simp]
/-
**Polynomial.aeval_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x : A) : aeval x (p - q) = 
aeval x p - aeval x q
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
-/
theorem aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x : A) :
    aeval x (p - q) = aeval x p - aeval x q := map_sub ..
/-
**Polynomial.aeval_endomorphism** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_endomorphism {M : Type*} [AddCommGroup M] [Module R M] (f : M ->ₗ[R]
 M) (v : M) (p : R[X]) : aeval f p v = p.sum fun n b => b • (f ^ n) v
参数：f : M ->ₗ[R] M；v : M；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_eq_sum`：eval₂_eq_sum {f : R ->+* S} {x : S} : p.eval₂ f
 x = p.sum fun e a => f a * x ^ e
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem aeval_endomorphism {M : Type*} [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (v : M) (p : R[X]) : aeval f p v = p.sum fun n b => b • (f ^ n) v := by
  rw [aeval_def, eval₂_eq_sum]
  exact map_sum (LinearMap.applyₗ v) _ _
/-
**Polynomial.X_sub_C_pow_dvd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：X_sub_C_pow_dvd_iff {n : Nat} : (X - C t) ^ n ∣ p ↔ X ^ n ∣ p.comp (X + C 
t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.algEquivAevalXAddC_apply`：∀ {R : Type u_3} [inst : CommRing R
] (t : R) (a : Polynomial R),   (Polynomial.algEquivAevalXAddC t) a = (Polynomia
l.aeval (Polynomial.X + P…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `map_dvd_iff`：map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
lemma X_sub_C_pow_dvd_iff {n : ℕ} : (X - C t) ^ n ∣ p ↔ X ^ n ∣ p.comp (X + C t) := by
  convert! (map_dvd_iff <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]
/-
**Polynomial.comp_X_add_C_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：comp_X_add_C_eq_zero_iff : p.comp (X + C t) = 0 ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.map_eq_zero_iff`：∀ {F : Type u_1} {M : Type u_4} {N : Type
 u_5} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [EmbeddingLik
e F M N] [ZeroHomCl…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
lemma comp_X_add_C_eq_zero_iff : p.comp (X + C t) = 0 ↔ p = 0 :=
  EmbeddingLike.map_eq_zero_iff (f := algEquivAevalXAddC t)
/-
**Polynomial.comp_X_add_C_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：comp_X_add_C_ne_zero_iff : p.comp (X + C t) != 0 ↔ p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Polynomial.comp_X_add_C_eq_zero_iff`：comp_X_add_C_eq_zero_iff : p.comp (
X + C t) = 0 ↔ p = 0
-/
lemma comp_X_add_C_ne_zero_iff : p.comp (X + C t) ≠ 0 ↔ p ≠ 0 := comp_X_add_C_eq_zero_iff.not
/-
**Polynomial.dvd_comp_C_mul_X_add_C_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：dvd_comp_C_mul_X_add_C_iff (p q : R[X]) (a b : R) [Invertible a] : p ∣ q.c
omp (C a * X + C b) ↔ p.comp (C ⅟a * (X - C b)) ∣ q
参数：p q : R[X]；a b : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.algEquivCMulXAddC_apply`：∀ {R : Type u_3} [inst : CommRing R]
 (a b : R) [inst_1 : Invertible a] (a_1 : Polynomial R),   (Polynomial.algEquivC
MulXAddC a b) a_1 = (Pol…
· 使用定理 `Polynomial.comp_assoc`：comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : 
R[X]) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `Polynomial.sub_comp`：sub_comp : (p - q).comp r = p.comp r - q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `invOf_mul_self'`：invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : ⅟a * a = 1
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.comp_X`：comp_X : p.comp X = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_dvd_iff`：map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
lemma dvd_comp_C_mul_X_add_C_iff (p q : R[X]) (a b : R) [Invertible a] :
    p ∣ q.comp (C a * X + C b) ↔ p.comp (C ⅟a * (X - C b)) ∣ q := by
  convert! map_dvd_iff <| algEquivCMulXAddC a b using 2
  simp [← comp_eq_aeval, comp_assoc, ← mul_assoc, ← C_mul]
/-
**Polynomial.dvd_comp_X_sub_C_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：dvd_comp_X_sub_C_iff (p q : R[X]) (a : R) : p ∣ q.comp (X - C a) ↔ p.comp 
(X + C a) ∣ q
参数：p q : R[X]；a : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `invOf_one'`：invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 
1
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用引理 `Polynomial.dvd_comp_C_mul_X_add_C_iff`：dvd_comp_C_mul_X_add_C_iff (p q :
 R[X]) (a b : R) [Invertible a] : p ∣ q.comp (C a * X + C b) ↔ p.comp (C ⅟a * (X
 - C b)) ∣ q
-/
lemma dvd_comp_X_sub_C_iff (p q : R[X]) (a : R) :
    p ∣ q.comp (X - C a) ↔ p.comp (X + C a) ∣ q := by
  let _ := invertibleOne (α := R)
  simpa using! dvd_comp_C_mul_X_add_C_iff p q 1 (-a)
/-
**Polynomial.dvd_comp_X_add_C_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：dvd_comp_X_add_C_iff (p q : R[X]) (a : R) : p ∣ q.comp (X + C a) ↔ p.comp 
(X - C a) ∣ q
参数：p q : R[X]；a : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Polynomial.dvd_comp_X_sub_C_iff`：dvd_comp_X_sub_C_iff (p q : R[X]) (a : 
R) : p ∣ q.comp (X - C a) ↔ p.comp (X + C a) ∣ q
-/
lemma dvd_comp_X_add_C_iff (p q : R[X]) (a : R) :
    p ∣ q.comp (X + C a) ↔ p.comp (X - C a) ∣ q := by
  simpa using! dvd_comp_X_sub_C_iff p q (-a)
/-
**Polynomial.dvd_comp_neg_X_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：dvd_comp_neg_X_iff (p q : R[X]) : p ∣ q.comp (-X) ↔ p.comp (-X) ∣ q
参数：p q : R[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `invOf_neg`：invOf_neg [Monoid R] [HasDistribNeg R] (a : R) [Invertible a]
 [Invertible (-a)] : ⅟(-a) = -⅟a
· 使用定理 `invOf_one'`：invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 
1
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `Polynomial.dvd_comp_C_mul_X_add_C_iff`：dvd_comp_C_mul_X_add_C_iff (p q :
 R[X]) (a b : R) [Invertible a] : p ∣ q.comp (C a * X + C b) ↔ p.comp (C ⅟a * (X
 - C b)) ∣ q
-/
lemma dvd_comp_neg_X_iff (p q : R[X]) : p ∣ q.comp (-X) ↔ p.comp (-X) ∣ q := by
  let _ := invertibleOne (α := R)
  let _ := invertibleNeg (R := R) 1
  simpa using dvd_comp_C_mul_X_add_C_iff p q (-1) 0

variable [IsDomain R]
/-
**Polynomial.units_coeff_zero_smul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：units_coeff_zero_smul (c : R[X]ˣ) (p : R[X]) : (c : R[X]).coeff 0 • p = c 
* p
参数：c : R[X]ˣ；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用定理 `Polynomial.eq_C_of_degree_eq_zero`：eq_C_of_degree_eq_zero (h : degree p 
= 0) : p = C (coeff p 0)
· 使用引理 `Polynomial.degree_coe_units`：degree_coe_units [Nontrivial R] (u : R[X]ˣ)
 : degree (u : R[X]) = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
lemma units_coeff_zero_smul (c : R[X]ˣ) (p : R[X]) : (c : R[X]).coeff 0 • p = c * p := by
  rw [← Polynomial.C_mul', ← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

end CommRing

section StableSubmodule

variable {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {q : Submodule R M} {m : M}

/-
**Polynomial.aeval_apply_smul_mem_of_le_comap'** 是 Mathlib 中的一个引理，位于命名空间 `Polyno
mial`。
形式化陈述：aeval_apply_smul_mem_of_le_comap' [Semiring A] [Algebra R A] [Module A M] 
[IsScalarTower R A M] (hm : m in q) (p : R[X]) (a : A) (hq : q <= q.comap (Algeb
ra.lsmul R R M a)) : aeval a p • m in q
参数：hm : m in q；p : R[X]；a : A；hq : q <= q.comap (Algebra.lsmul R R M a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
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
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
lemma aeval_apply_smul_mem_of_le_comap'
    [Semiring A] [Algebra R A] [Module A M] [IsScalarTower R A M] (hm : m ∈ q) (p : R[X]) (a : A)
    (hq : q ≤ q.comap (Algebra.lsmul R R M a)) :
    aeval a p • m ∈ q := by
  induction p using Polynomial.induction_on with
  | C a => simpa using SMulMemClass.smul_mem a hm
  | add f₁ f₂ h₁ h₂ =>
    simp_rw [map_add, add_smul]
    exact Submodule.add_mem q h₁ h₂
  | monomial n t hmq =>
    rw [pow_succ', mul_left_comm, map_mul, aeval_X, mul_smul]
    solve_by_elim
/-
**Polynomial.aeval_apply_smul_mem_of_le_comap** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
形式化陈述：aeval_apply_smul_mem_of_le_comap (hm : m in q) (p : R[X]) (f : Module.End 
R M) (hq : q <= q.comap f) : aeval f p m in q
参数：hm : m in q；p : R[X]；f : Module.End R M；hq : q <= q.comap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.aeval_apply_smul_mem_of_le_comap'`：aeval_apply_smul_mem_of_le
_comap' [Semiring A] [Algebra R A] [Module A M] [IsScalarTower R A M] (hm : m in
 q) (p : R[X]) (a : A) (hq : q <= …
-/
lemma aeval_apply_smul_mem_of_le_comap
    (hm : m ∈ q) (p : R[X]) (f : Module.End R M) (hq : q ≤ q.comap f) :
    aeval f p m ∈ q :=
  aeval_apply_smul_mem_of_le_comap' hm p f hq

end StableSubmodule

section CommSemiring

variable [CommSemiring R] {a p : R[X]}

/-
**Polynomial.eq_zero_of_mul_eq_zero_of_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：eq_zero_of_mul_eq_zero_of_smul (P : R[X]) (h : forall r : R, r • P = 0 -> 
r = 0) (Q : R[X]) (hQ : P * Q = 0) : Q = 0
参数：P : R[X]；h : forall r : R, r • P = 0 -> r = 0；Q : R[X]；hQ : P * Q = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_zero_of_mul_eq_zero_of_smul._unary`：∀ {R : Type u} [inst :
 CommSemiring R] (P : Polynomial R),   (∀ (r : R), r • P = 0 → r = 0) → ∀ (_x : 
(Q : Polynomial R) ×' P * Q = 0), _x.1…
-/
theorem eq_zero_of_mul_eq_zero_of_smul (P : R[X]) (h : ∀ r : R, r • P = 0 → r = 0) (Q : R[X])
    (hQ : P * Q = 0) : Q = 0 := by
  suffices ∀ i, P.coeff i • Q = 0 by
    rw [← leadingCoeff_eq_zero]
    apply h
    simpa [ext_iff, mul_comm Q.leadingCoeff] using fun i ↦ congr_arg (·.coeff Q.natDegree) (this i)
  apply Nat.strong_decreasing_induction
  · use P.natDegree
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt hi, zero_smul]
  intro l IH
  obtain _ | hl := (natDegree_smul_le (P.coeff l) Q).lt_or_eq
  · apply eq_zero_of_mul_eq_zero_of_smul _ h (P.coeff l • Q)
    rw [smul_eq_C_mul, mul_left_comm, hQ, mul_zero]
  suffices P.coeff l * Q.leadingCoeff = 0 by
    rwa [← leadingCoeff_eq_zero, ← coeff_natDegree, coeff_smul, hl, coeff_natDegree, smul_eq_mul]
  let m := Q.natDegree
  suffices (P * Q).coeff (l + m) = P.coeff l * Q.leadingCoeff by rw [← this, hQ, coeff_zero]
  rw [coeff_mul]
  apply Finset.sum_eq_single (l, m) _ (by simp)
  simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
  intro i j hij H
  obtain hi | rfl | hi := lt_trichotomy i l
  · have hj : m < j := by lia
    rw [coeff_eq_zero_of_natDegree_lt hj, mul_zero]
  · lia
  · rw [← coeff_C_mul, ← smul_eq_C_mul, IH _ hi, coeff_zero]
termination_by Q.natDegree

open nonZeroDivisors

/-- *McCoy theorem*: a polynomial `P : R[X]` is a zerodivisor if and only if there is `a : R`
such that `a ≠ 0` and `a • P = 0`. -/
/-
**Polynomial.notMem_nonZeroDivisors_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：notMem_nonZeroDivisors_iff {P : R[X]} : P ∉ R[X]⁰ ↔ exists a : R, a != 0 ∧
 a • P = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `notMem_nonZeroDivisors_iff_right`：notMem_nonZeroDivisors_iff_right : r ∉
 M₀⁰ ↔ {s | s * r = 0 ∧ s != 0}.Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.eq_zero_of_mul_eq_zero_of_smul`：eq_zero_of_mul_eq_zero_of_smu
l (P : R[X]) (h : forall r : R, r • P = 0 -> r = 0) (Q : R[X]) (hQ : P * Q = 0) 
: Q = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
· 使用定理 `Polynomial.smul_eq_C_mul`：smul_eq_C_mul (a : R) : a • p = C a * p

--- 原说明 ---
*McCoy theorem*: a polynomial `P : R[X]` is a zerodivisor if and only if there i
s `a : R`
such that `a ≠ 0` and `a • P = 0`.
-/
theorem notMem_nonZeroDivisors_iff {P : R[X]} : P ∉ R[X]⁰ ↔ ∃ a : R, a ≠ 0 ∧ a • P = 0 := by
  refine ⟨fun hP ↦ ?_, fun ⟨a, ha, h⟩ h1 ↦ ha <| C_eq_zero.1 <| (h1.2 _) <| smul_eq_C_mul a ▸ h⟩
  by_contra! h
  obtain ⟨Q, hQ⟩ := notMem_nonZeroDivisors_iff_right.1 hP
  refine hQ.2 (eq_zero_of_mul_eq_zero_of_smul P (fun a ha ↦ ?_) Q (mul_comm P _ ▸ hQ.1))
  contrapose! ha
  exact h a ha
/-
**Polynomial.mem_nonZeroDivisors_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {P : Polynomial R},   P ∈ nonZeroDi
visors (Polynomial R) ↔ ∀ (a : R), a • P = 0 → a = 0
参数：Polynomial R；a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.notMem_nonZeroDivisors_iff`：notMem_nonZeroDivisors_iff {P : R
[X]} : P ∉ R[X]⁰ ↔ exists a : R, a != 0 ∧ a • P = 0
-/
protected lemma mem_nonZeroDivisors_iff {P : R[X]} : P ∈ R[X]⁰ ↔ ∀ a : R, a • P = 0 → a = 0 := by
  simpa [not_imp_not] using (notMem_nonZeroDivisors_iff (P := P)).not
/-
**Polynomial.mem_nonzeroDivisors_of_coeff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
形式化陈述：mem_nonzeroDivisors_of_coeff_mem {p : R[X]} (n : Nat) (hp : p.coeff n in R
⁰) : p in R[X]⁰
参数：n : Nat；hp : p.coeff n in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_nonZeroDivisors_iff`：∀ {R : Type u} [inst : CommSemiring 
R] {P : Polynomial R},   P ∈ nonZeroDivisors (Polynomial R) ↔ ∀ (a : R), a • P =
 0 → a = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
-/
lemma mem_nonzeroDivisors_of_coeff_mem {p : R[X]} (n : ℕ) (hp : p.coeff n ∈ R⁰) :
    p ∈ R[X]⁰ :=
  Polynomial.mem_nonZeroDivisors_iff.mpr fun r hr ↦ hp.2 _ (by simpa using congr(coeff $hr n))
/-
**Polynomial.X_mem_nonzeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：X_mem_nonzeroDivisors : X in R[X]⁰
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.mem_nonzeroDivisors_of_coeff_mem`：mem_nonzeroDivisors_of_coef
f_mem {p : R[X]} (n : Nat) (hp : p.coeff n in R⁰) : p in R[X]⁰
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
lemma X_mem_nonzeroDivisors : X ∈ R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem 1 (by simp [one_mem])

end CommSemiring

end Polynomial

