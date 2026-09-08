/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Algebra.Module.Rat
public import Mathlib.LinearAlgebra.Prod

/-!
# The star operation, bundled as a star-linear equiv

We define `starLinearEquiv`, which is the star operation bundled as a star-linear map.
It is defined on a star algebra `A` over the base ring `R`.

This file also provides some lemmas that need `Algebra.Module.Basic` imported to prove.

## TODO

- Define `starLinearEquiv` for noncommutative `R`. We only the commutative case for now since,
  in the noncommutative case, the ring hom needs to reverse the order of multiplication. This
  requires a ring hom of type `R →+* Rᵐᵒᵖ`, which is very undesirable in the commutative case.
  One way out would be to define a new typeclass `IsOp R S` and have an instance `IsOp R R`
  for commutative `R`.
- Also note that such a definition involving `Rᵐᵒᵖ` or `is_op R S` would require adding
  the appropriate `RingHomInvPair` instances to be able to define the semilinear
  equivalence.
-/

@[expose] public section


section SMulLemmas

variable {R M : Type*}

@[simp]
/-
**star_natCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_natCast_smul [Semiring R] [AddCommMonoid M] [Module R M] [StarAddMono
id M] (n : Nat) (x : M) : star ((n : R) • x) = (n : R) • star x
参数：n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast_smul`：map_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] 
{F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [S
emirin…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem star_natCast_smul [Semiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M] (n : ℕ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
/-
**star_intCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_intCast_smul [Ring R] [AddCommGroup M] [Module R M] [StarAddMonoid M]
 (n : Int) (x : M) : star ((n : R) • x) = (n : R) • star x
参数：n : Int；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_intCast_smul`：map_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F
 : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Rin
g R] […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem star_intCast_smul [Ring R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℤ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
/-
**star_inv_natCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid M] [Module R M] 
[StarAddMonoid M] (n : Nat) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x
参数：n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv_natCast_smul`：map_inv_natCast_smul [AddCommMonoid M] [AddCommMon
oid M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : T
ype*) [Div…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem star_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M]
    (n : ℕ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
/-
**star_inv_intCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_inv_intCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [Star
AddMonoid M] (n : Int) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x
参数：n : Int；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv_intCast_smul`：map_inv_intCast_smul [AddCommGroup M] [AddCommGrou
p M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Typ
e*) [Divis…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem star_inv_intCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M]
    (n : ℤ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
/-
**star_ratCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_ratCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddM
onoid M] (n : Rat) (x : M) : star ((n : R) • x) = (n : R) • star x
参数：n : Rat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ratCast_smul`：map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F
 : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Div
isionR…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem star_ratCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℚ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_ratCast_smul (starAddEquiv : M ≃+ M) _ _ _ x

/-!
Per the naming convention, these two lemmas call `(q • ·)` `nnrat_smul` and `rat_smul` respectively,
rather than `nnqsmul` and `qsmul` because the latter are reserved to the actions coming from
`DivisionSemiring` and `DivisionRing`. We provide aliases with `nnqsmul` and `qsmul` for
discoverability.
-/

/-- Note that this lemma holds for an arbitrary `ℚ≥0`-action, rather than merely one coming from a
`DivisionSemiring`. We keep both the `nnqsmul` and `nnrat_smul` naming conventions for
discoverability. See `star_nnqsmul`. -/
@[simp high]
/-
**star_nnrat_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：star_nnrat_smul [AddCommMonoid R] [StarAddMonoid R] [Module Rat>=0 R] (q :
 Rat>=0) (x : R) : star (q • x) = q • star x
参数：q : Rat>=0；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nnrat_smul`：map_nnrat_smul [AddCommMonoid M] [AddCommMonoid M₂] [_in
stM : Module Rat>=0 M] [_instM₂ : Module Rat>=0 M₂] {F : Type*} [FunLike F M M₂]
 [Ad…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N

--- 原说明 ---
Note that this lemma holds for an arbitrary `ℚ≥0`-action, rather than merely one
 coming from a
`DivisionSemiring`. We keep both the `nnqsmul` and `nnrat_smul` naming conventio
ns for
discoverability. See `star_nnqsmul`.
-/
lemma star_nnrat_smul [AddCommMonoid R] [StarAddMonoid R] [Module ℚ≥0 R] (q : ℚ≥0) (x : R) :
    star (q • x) = q • star x := map_nnrat_smul (starAddEquiv : R ≃+ R) _ _

/-- Note that this lemma holds for an arbitrary `ℚ`-action, rather than merely one coming from a
`DivisionRing`. We keep both the `qsmul` and `rat_smul` naming conventions for discoverability.
See `star_qsmul`. -/
/-
**star_rat_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : AddCommGroup R] [inst_1 : StarAddMonoid R] [inst_
2 : _root_.Module ℚ R] (q : ℚ) (x : R),   star (q • x) = q • star x
参数：q : ℚ；x : R；q • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_rat_smul`：map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [_instM : 
Module Rat M] [_instM₂ : Module Rat M₂] {F : Type*} [FunLike F M M₂] [AddMonoidH
om…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N

--- 原说明 ---
Note that this lemma holds for an arbitrary `ℚ`-action, rather than merely one c
oming from a
`DivisionRing`. We keep both the `qsmul` and `rat_smul` naming conventions for d
iscoverability.
See `star_qsmul`.
-/
@[simp high] lemma star_rat_smul [AddCommGroup R] [StarAddMonoid R] [Module ℚ R] (q : ℚ) (x : R) :
    star (q • x) = q • star x :=
  map_rat_smul (starAddEquiv : R ≃+ R) _ _

/-- Note that this lemma holds for an arbitrary `ℚ≥0`-action, rather than merely one coming from a
`DivisionSemiring`. We keep both the `nnqsmul` and `nnrat_smul` naming conventions for
discoverability. See `star_nnrat_smul`. -/
alias star_nnqsmul := star_nnrat_smul

/-- Note that this lemma holds for an arbitrary `ℚ`-action, rather than merely one coming from a
`DivisionRing`. We keep both the `qsmul` and `rat_smul` naming conventions for
discoverability. See `star_rat_smul`. -/
alias star_qsmul := star_rat_smul

/-
**StarAddMonoid.toStarModuleNNRat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：StarAddMonoid.toStarModuleNNRat [AddCommMonoid R] [Module Rat>=0 R] [StarA
ddMonoid R] : StarModule Rat>=0 R where star_smul
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `star_nnrat_smul`：star_nnrat_smul [AddCommMonoid R] [StarAddMonoid R] [Mo
dule Rat>=0 R] (q : Rat>=0) (x : R) : star (q • x) = q • star x
-/
instance StarAddMonoid.toStarModuleNNRat [AddCommMonoid R] [Module ℚ≥0 R] [StarAddMonoid R] :
    StarModule ℚ≥0 R where star_smul := star_nnrat_smul
/-
**StarAddMonoid.toStarModuleRat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：StarAddMonoid.toStarModuleRat [AddCommGroup R] [Module Rat R] [StarAddMono
id R] : StarModule Rat R where star_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `star_rat_smul`：∀ {R : Type u_1} [inst : AddCommGroup R] [inst_1 : StarAd
dMonoid R] [inst_2 : _root_.Module ℚ R] (q : ℚ) (x : R),   star (q • x) = q • st
ar …
-/
instance StarAddMonoid.toStarModuleRat [AddCommGroup R] [Module ℚ R] [StarAddMonoid R] :
    StarModule ℚ R where star_smul := star_rat_smul

end SMulLemmas

section starLinearEquiv

variable (R : Type*) {A : Type*}
  [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A] [Module R A] [StarModule R A]

/-- If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
@[simps! apply]
/-
**starLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starLinearEquiv : A ≃ₗ⋆[R] A where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)

--- 原说明 ---
If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence.
-/
def starLinearEquiv : A ≃ₗ⋆[R] A where
  __ := starAddEquiv
  map_smul' := star_smul

@[simp]
/-
**toAddEquiv_starLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAddEquiv_starLinearEquiv : (starLinearEquiv R : A ≃ₗ⋆[R] A).toAddEquiv =
 starAddEquiv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
theorem toAddEquiv_starLinearEquiv :
    (starLinearEquiv R : A ≃ₗ⋆[R] A).toAddEquiv = starAddEquiv :=
  rfl

@[simp]
/-
**symm_starLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symm_starLinearEquiv : (starLinearEquiv R : A ≃ₗ⋆[R] A).symm = starLinearE
quiv R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
theorem symm_starLinearEquiv : (starLinearEquiv R : A ≃ₗ⋆[R] A).symm = starLinearEquiv R :=
  rfl

@[deprecated "Use `symm_starLinearEquiv` and `starLinearEquiv_apply` instead"
  (since := "2026-06-03")]
/-
**starLinearEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starLinearEquiv_symm_apply (x : A) : (starLinearEquiv R).symm x = starAddE
quiv.invFun x
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `starLinearEquiv_apply`：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemir
ing R] [inst_1 : StarRing R] [inst_2 : AddCommMonoid A]   [inst_3 : StarAddMonoi
d A] [inst_…
· 使用定理 `Equiv.Perm.star_apply`：∀ {R : Type u} [inst : InvolutiveStar R] (a : R),
 Equiv.Perm.star a = star a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem starLinearEquiv_symm_apply (x : A) :
    (starLinearEquiv R).symm x = starAddEquiv.invFun x := by
  simp

end starLinearEquiv

section SelfSkewAdjoint

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

/-- The self-adjoint elements of a star module, as a submodule. -/
/-
**selfAdjoint.submodule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：selfAdjoint.submodule : Submodule R A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The self-adjoint elements of a star module, as a submodule.
-/
def selfAdjoint.submodule : Submodule R A :=
  { selfAdjoint A with smul_mem' := fun _ _ => (IsSelfAdjoint.all _).smul }

/-- The skew-adjoint elements of a star module, as a submodule. -/
/-
**skewAdjoint.submodule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjoint.submodule : Submodule R A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skew-adjoint elements of a star module, as a submodule.
-/
def skewAdjoint.submodule : Submodule R A :=
  { skewAdjoint A with smul_mem' := skewAdjoint.smul_mem }

variable {A} [Invertible (2 : R)]

/-- The self-adjoint part of an element of a star module, as a linear map. -/
@[simps]
/-
**selfAdjointPart** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：selfAdjointPart : A ->ₗ[R] selfAdjoint A where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The self-adjoint part of an element of a star module, as a linear map.
-/
def selfAdjointPart : A →ₗ[R] selfAdjoint A where
  toFun x :=
    ⟨(⅟2 : R) • (x + star x), by
      rw [selfAdjoint.mem_iff, star_smul, star_trivial, star_add, star_star, add_comm]⟩
  map_add' x y := by
    ext
    simp [add_add_add_comm]
  map_smul' r x := by
    ext
    simp [← mul_smul, show ⅟2 * r = r * ⅟2 from Commute.invOf_left <| (2 : ℕ).cast_commute r]

/-- The skew-adjoint part of an element of a star module, as a linear map. -/
@[simps]
/-
**skewAdjointPart** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjointPart : A ->ₗ[R] skewAdjoint A where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skew-adjoint part of an element of a star module, as a linear map.
-/
def skewAdjointPart : A →ₗ[R] skewAdjoint A where
  toFun x :=
    ⟨(⅟2 : R) • (x - star x), by
      simp only [skewAdjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ← smul_neg,
        neg_sub]⟩
  map_add' x y := by
    ext
    simp only [sub_add, ← smul_add, sub_sub_eq_add_sub, star_add, AddSubgroup.coe_add]
  map_smul' r x := by
    ext
    simp [← mul_smul, ← smul_sub,
      show r * ⅟2 = ⅟2 * r from Commute.invOf_right <| (2 : ℕ).commute_cast r]
/-
**StarModule.selfAdjointPart_add_skewAdjointPart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarModule.selfAdjointPart_add_skewAdjointPart (x : A) : (selfAdjointPart 
R x : A) + skewAdjointPart R x = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `selfAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `skewAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `add_add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + c + (b - c) = a + b
· 使用定理 `invOf_two_smul_add_invOf_two_smul`：invOf_two_smul_add_invOf_two_smul (R)
 [Semiring R] [AddCommMonoid M] [Module R M] [Invertible (2 : R)] (x : M) : (⅟2 
: R) • x + (⅟2 : R) • x…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem StarModule.selfAdjointPart_add_skewAdjointPart (x : A) :
    (selfAdjointPart R x : A) + skewAdjointPart R x = x := by
  simp only [smul_sub, selfAdjointPart_apply_coe, smul_add, skewAdjointPart_apply_coe,
    add_add_sub_cancel, invOf_two_smul_add_invOf_two_smul]
/-
**IsSelfAdjoint.coe_selfAdjointPart_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.coe_selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) : (
selfAdjointPart R x : A) = x
参数：hx : IsSelfAdjoint x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `selfAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `invOf_two_smul_add_invOf_two_smul`：invOf_two_smul_add_invOf_two_smul (R)
 [Semiring R] [AddCommMonoid M] [Module R M] [Invertible (2 : R)] (x : M) : (⅟2 
: R) • x + (⅟2 : R) • x…
-/
theorem IsSelfAdjoint.coe_selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    (selfAdjointPart R x : A) = x := by
  rw [selfAdjointPart_apply_coe, hx.star_eq, smul_add, invOf_two_smul_add_invOf_two_smul]
/-
**IsSelfAdjoint.selfAdjointPart_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) : selfA
djointPart R x = ⟨x, hx⟩
参数：hx : IsSelfAdjoint x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsSelfAdjoint.coe_selfAdjointPart_apply`：IsSelfAdjoint.coe_selfAdjointPa
rt_apply {x : A} (hx : IsSelfAdjoint x) : (selfAdjointPart R x : A) = x
-/
theorem IsSelfAdjoint.selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    selfAdjointPart R x = ⟨x, hx⟩ :=
  Subtype.ext (hx.coe_selfAdjointPart_apply R)

@[simp]
/-
**selfAdjointPart_comp_subtype_selfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：selfAdjointPart_comp_subtype_selfAdjoint : (selfAdjointPart R).comp (selfA
djoint.submodule R A).subtype = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsSelfAdjoint.selfAdjointPart_apply`：IsSelfAdjoint.selfAdjointPart_apply
 {x : A} (hx : IsSelfAdjoint x) : selfAdjointPart R x = ⟨x, hx⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem selfAdjointPart_comp_subtype_selfAdjoint :
    (selfAdjointPart R).comp (selfAdjoint.submodule R A).subtype = .id :=
  LinearMap.ext fun x ↦ x.2.selfAdjointPart_apply R
/-
**IsSelfAdjoint.skewAdjointPart_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.skewAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) : skewA
djointPart R x = 0
参数：hx : IsSelfAdjoint x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `skewAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
-/
theorem IsSelfAdjoint.skewAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    skewAdjointPart R x = 0 := Subtype.ext <| by
  rw [skewAdjointPart_apply_coe, hx.star_eq, sub_self, smul_zero, ZeroMemClass.coe_zero]

@[simp]
/-
**skewAdjointPart_comp_subtype_selfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：skewAdjointPart_comp_subtype_selfAdjoint : (skewAdjointPart R).comp (selfA
djoint.submodule R A).subtype = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsSelfAdjoint.skewAdjointPart_apply`：IsSelfAdjoint.skewAdjointPart_apply
 {x : A} (hx : IsSelfAdjoint x) : skewAdjointPart R x = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem skewAdjointPart_comp_subtype_selfAdjoint :
    (skewAdjointPart R).comp (selfAdjoint.submodule R A).subtype = 0 :=
  LinearMap.ext fun x ↦ x.2.skewAdjointPart_apply R

@[simp]
/-
**selfAdjointPart_comp_subtype_skewAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：selfAdjointPart_comp_subtype_skewAdjoint : (selfAdjointPart R).comp (skewA
djoint.submodule R A).subtype = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `selfAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem selfAdjointPart_comp_subtype_skewAdjoint :
    (selfAdjointPart R).comp (skewAdjoint.submodule R A).subtype = 0 :=
  LinearMap.ext fun ⟨x, (hx : _ = _)⟩ ↦ Subtype.ext <| by simp [hx]

@[simp]
/-
**skewAdjointPart_comp_subtype_skewAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：skewAdjointPart_comp_subtype_skewAdjoint : (skewAdjointPart R).comp (skewA
djoint.submodule R A).subtype = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `skewAdjointPart_apply_coe`：∀ (R : Type u_1) {A : Type u_2} [inst : Semir
ing R] [inst_1 : StarMul R] [inst_2 : TrivialStar R]   [inst_3 : AddCommGroup A]
 [inst_4 : _roo…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `invOf_two_smul_add_invOf_two_smul`：invOf_two_smul_add_invOf_two_smul (R)
 [Semiring R] [AddCommMonoid M] [Module R M] [Invertible (2 : R)] (x : M) : (⅟2 
: R) • x + (⅟2 : R) • x…
-/
theorem skewAdjointPart_comp_subtype_skewAdjoint :
    (skewAdjointPart R).comp (skewAdjoint.submodule R A).subtype = .id :=
  LinearMap.ext fun ⟨x, (hx : _ = _)⟩ ↦ Subtype.ext <| by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, skewAdjointPart_apply_coe, hx,
      sub_neg_eq_add, smul_add, invOf_two_smul_add_invOf_two_smul]; rfl

variable (A)

set_option backward.isDefEq.respectTransparency false in
/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a linear equivalence. -/
@[simps!]
/-
**StarModule.decomposeProdAdjoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StarModule.decomposeProdAdjoint : A ≃ₗ[R] selfAdjoint A × skewAdjoint A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The decomposition of elements of a star module into their self- and skew-adjoint
 parts,
as a linear equivalence.
-/
def StarModule.decomposeProdAdjoint : A ≃ₗ[R] selfAdjoint A × skewAdjoint A := by
  refine LinearEquiv.ofLinearMap ((selfAdjointPart R).prod (skewAdjointPart R))
    (LinearMap.coprod ((selfAdjoint.submodule R A).subtype) (skewAdjoint.submodule R A).subtype)
    ?_ (LinearMap.ext <| StarModule.selfAdjointPart_add_skewAdjointPart R)
  -- Note: with https://github.com/leanprover-community/mathlib4/pull/6965 `Submodule.coe_subtype` doesn't fire in `dsimp` or `simp`
  ext x <;> dsimp <;> erw [Submodule.coe_subtype, Submodule.coe_subtype] <;> simp

end SelfSkewAdjoint

section algebraMap

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A]
variable [StarMul A] [Algebra R A] [StarModule R A]

@[simp]
/-
**algebraMap_star_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap_star_comm (r : R) : algebraMap R A (star r) = star (algebraMap 
R A r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_star_comm (r : R) : algebraMap R A (star r) = star (algebraMap R A r) := by
  simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]

variable (A) in
/-
**IsSelfAdjoint.algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) [inst : CommSemiring R] [inst_1 : StarRing
 R] [inst_2 : Semiring A] [inst_3 : StarMul A]   [inst_4 : Algebra R A] [StarMod
ule R A] {r : R}, IsSelfAdjoint r → IsSelfAdjoint ((algebraMap R A) r)
参数：A : Type u_2；(algebraMap R A) r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap_star_comm`：algebraMap_star_comm (r : R) : algebraMap R A (sta
r r) = star (algebraMap R A r)
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
-/
protected lemma IsSelfAdjoint.algebraMap {r : R} (hr : IsSelfAdjoint r) :
    IsSelfAdjoint (algebraMap R A r) := by
  simpa using! congr(algebraMap R A $(hr.star_eq))
/-
**isSelfAdjoint_algebraMap_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSelfAdjoint_algebraMap_iff {r : R} (h : Function.Injective (algebraMap R
 A)) : IsSelfAdjoint (algebraMap R A r) ↔ IsSelfAdjoint r
参数：h : Function.Injective (algebraMap R A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_star_comm`：algebraMap_star_comm (r : R) : algebraMap R A (sta
r r) = star (algebraMap R A r)
· 使用定理 `IsSelfAdjoint.algebraMap`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : StarRing R] [inst_2 : Semiring A] [inst_3 : StarMul A]   [in
st_4 : Algebra…
-/
lemma isSelfAdjoint_algebraMap_iff {r : R} (h : Function.Injective (algebraMap R A)) :
    IsSelfAdjoint (algebraMap R A r) ↔ IsSelfAdjoint r :=
  ⟨fun hr ↦ h <| algebraMap_star_comm r (A := A) ▸ hr.star_eq, IsSelfAdjoint.algebraMap A⟩

end algebraMap

/-
**IsIdempotentElem.star_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIdempotentElem.star_iff {R : Type*} [Mul R] [StarMul R] {a : R} : IsIdem
potentElem (star a) ↔ IsIdempotentElem a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsIdempotentElem.star_iff {R : Type*} [Mul R] [StarMul R] {a : R} :
    IsIdempotentElem (star a) ↔ IsIdempotentElem a := by
  simp [IsIdempotentElem, ← star_mul]

alias ⟨_, IsIdempotentElem.star⟩ := IsIdempotentElem.star_iff
