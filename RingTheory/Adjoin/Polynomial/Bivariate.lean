/-
Copyright (c) 2026 Xavier Généreux, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Ring.Defs

/-!
# Bivariate polynomials and adjoining transcendental elements

## Main results

* `IsAlgebraic.adjoin_singleton`:
  Given two transcendental elements `a`, `b` over `R`, if one of them, say `a`, is algebraic over
  `R[b]` then `b` is algebraic over `R[a]`.
-/

@[expose] public noncomputable section

namespace Polynomial.Bivariate

open Polynomial Bivariate Algebra Transcendental

variable {R A : Type*} [CommRing R]

section Ring

variable [Ring A] [Algebra R A] {x : A}

/-- The `AlgEquiv` between `R[X][Y]` and `R[a][Y]` for some transcendental `a`. -/
/-
**Polynomial.Bivariate.Transcendental.algEquivAdjoin** 是 Mathlib 中的一个定义，位于命名空间 `
Polynomial.Bivariate.Transcendental`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     [inst : CommRing R] →       [inst_
1 : Ring A] →         [inst_2 : Algebra R A] → {x : A} → Transcendental R x → Po
lynomial (Polynomial R) ≃ₐ[R] Polynomial ↥R[x]
参数：Polynomial R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `AlgEquiv` between `R[X][Y]` and `R[a][Y]` for some transcendental `a`.
-/
def Transcendental.algEquivAdjoin (hx : Transcendental R x) :
    R[X][Y] ≃ₐ[R] (Algebra.adjoin R {x})[X] :=
  mapAlgEquiv (algEquivOfTranscendental _ x hx)
/-
**Polynomial.Bivariate.Transcendental.algEquivAdjoin_apply** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial.Bivariate.Transcendental`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {x : A}   (hx : Transcendental R x) (p : Polynomial (Polynomi
al R)),   (Polynomial.Bivariate.Transcendental.algEquivAdjoin hx) p = (Polynomia
l.mapAlgHom (Polynomial.aeval ⟨x, ⋯⟩)) p
参数：hx : Transcendental R x；p : Polynomial (Polynomial R)；Polynomial.Bivariate.Tr
anscendental.algEquivAdjoin hx；Polynomial.mapAlgHom (Polynomial.aeval ⟨x, ⋯⟩)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Transcendental.algEquivAdjoin_apply (hx : Transcendental R x) (p : R[X][Y]) :
    hx.algEquivAdjoin p = mapAlgHom (aeval ⟨x, self_mem_adjoin_singleton R x⟩) p :=
  rfl

attribute [local instance] algebra in
/-
**Polynomial.Bivariate.Transcendental.algEquivAdjoin_swap_eq_aeval** 是 Mathlib 中
的一个定理，位于命名空间 `Polynomial.Bivariate.Transcendental`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {x : A}   (hx : Transcendental R x) (p : Polynomial (Polynomi
al R)),   (Polynomial.Bivariate.Transcendental.algEquivAdjoin hx) (Polynomial.Bi
variate.swap p) =     (Polynomial.aeval (Polynomial.C ⟨x, ⋯⟩)) p
参数：hx : Transcendental R x；p : Polynomial (Polynomial R)；Polynomial.Bivariate.Tr
anscendental.algEquivAdjoin hx；Polynomial.Bivariate.swap p；Polynomial.aeval (Pol
ynomial.C ⟨x, ⋯⟩)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Bivariate.aveal_eq_map_swap`：∀ {R : Type u_1} {A : Type u_2} 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (x : A)
   (p : Polynomial (Polynomi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Transcendental.algEquivAdjoin_swap_eq_aeval (hx : Transcendental R x) (p : R[X][Y]) :
    hx.algEquivAdjoin (swap p) = aeval (C ⟨x, self_mem_adjoin_singleton R x⟩) p := by
  simp [algEquivAdjoin, Bivariate.aveal_eq_map_swap]

end Ring

section CommRing

variable [CommRing A] [Algebra R A]

variable {B : Type*} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

attribute [local instance] Polynomial.algebra in
/-
**Polynomial.Bivariate.aeval_aeval_eq_aeval_algEquivAdjoin** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial.Bivariate`。
形式化陈述：aeval_aeval_eq_aeval_algEquivAdjoin {x : A} (y : B) (hx : Transcendental R
 x) (p : R[X][Y]) : aeval (algebraMap A B x) (aeval (C (⟨y, self_mem_adjoin_sing
leton R y⟩ : adjoin R {y})) p) = aeval y (hx.algEquivAdjoin p)
参数：y : B；hx : Transcendental R x；p : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
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
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用引理 `Polynomial.coe_aeval_mk_apply`：coe_aeval_mk_apply {S : Subalgebra R A} (
h : x in S) : (aeval (⟨x, h⟩ : S) p : A) = aeval x p
-/
theorem aeval_aeval_eq_aeval_algEquivAdjoin {x : A} (y : B)
    (hx : Transcendental R x) (p : R[X][Y]) :
    aeval (algebraMap A B x) (aeval (C (⟨y, self_mem_adjoin_singleton R y⟩ :
      adjoin R {y})) p) = aeval y (hx.algEquivAdjoin p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp_all [map_add]
  | monomial n a =>
    simp_all [aeval_algebraMap_apply, Transcendental.algEquivAdjoin, Subalgebra.algebraMap_def]
/-
**Polynomial.Bivariate._root_.IsAlgebraic.adjoin_singleton** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial.Bivariate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsAlgebraic.adjoin_singleton {x : A} {y : B} (hx : Transcendental R x)
    (hy : Transcendental R y) (h : IsAlgebraic (adjoin R {x}) y) :
    IsAlgebraic (adjoin R {y}) (algebraMap A B x) := by
  obtain ⟨f, hnezero, halg⟩ := h
  refine ⟨hy.algEquivAdjoin (swap (hx.algEquivAdjoin.symm f)),
    by simpa only [map_ne_zero_iff _ (AlgEquiv.injective _)], ?_⟩
  simpa [Transcendental.algEquivAdjoin_swap_eq_aeval hy, aeval_aeval_eq_aeval_algEquivAdjoin y hx]

end CommRing

end Polynomial.Bivariate

end

