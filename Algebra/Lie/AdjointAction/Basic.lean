/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Properties of the adjoint action

Theorems about the adjoint action `LieAlgebra.ad` on associative algebras.

## Main results

* `LieAlgebra.commute_ad_of_commute`: commuting elements have commuting adjoints.
* `LieAlgebra.ad_nilpotent_of_nilpotent`: the adjoint of a nilpotent element is nilpotent.
* `LieAlgebra.ad_isSemisimple_of_isSemisimple`: the adjoint of a semisimple element is semisimple.
-/

public section

section CommRing

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

set_option backward.isDefEq.respectTransparency false in
/-- Commuting elements have commuting adjoint actions. -/
/-
**LieAlgebra.commute_ad_of_commute** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.commute_ad_of_commute {a b : A} (h : Commute a b) : Commute (Li
eAlgebra.ad R A a) (LieAlgebra.ad R A b)
参数：h : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq_1`：∀ {S : Type u_3} [inst : Mul S] (a b : S), Commute a b = S
emiconjBy a b b
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Ring.lie_def`：lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…

--- 原说明 ---
Commuting elements have commuting adjoint actions.
-/
theorem LieAlgebra.commute_ad_of_commute {a b : A} (h : Commute a b) :
    Commute (LieAlgebra.ad R A a) (LieAlgebra.ad R A b) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, ← Ring.lie_def,
    ← (LieAlgebra.ad R A).map_lie, Ring.lie_def, sub_eq_zero.mpr h, map_zero]

/-- The adjoint of a nilpotent element is nilpotent. -/
/-
**LieAlgebra.ad_nilpotent_of_nilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.ad_nilpotent_of_nilpotent {a : A} (h : IsNilpotent a) : IsNilpo
tent (LieAlgebra.ad R A a)
参数：h : IsNilpotent a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.ad_eq_lmul_left_sub_lmul_right`：LieAlgebra.ad_eq_lmul_left_su
b_lmul_right (A : Type v) [Ring A] [Algebra R A] : (ad R A : A -> Module.End R A
) = LinearMap.mulLeft R - Linea…
· 使用定理 `LinearMap.isNilpotent_mulLeft_iff`：isNilpotent_mulLeft_iff (a : A) : IsN
ilpotent (mulLeft R a) ↔ IsNilpotent a
· 使用定理 `LinearMap.isNilpotent_mulRight_iff`：isNilpotent_mulRight_iff (a : A) : I
sNilpotent (mulRight R a) ↔ IsNilpotent a
· 使用定理 `Commute.isNilpotent_sub`：isNilpotent_sub (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y)
· 使用定理 `LinearMap.commute_mulLeft_right`：commute_mulLeft_right (a b : A) : Commu
te (mulLeft R a) (mulRight R b)

--- 原说明 ---
The adjoint of a nilpotent element is nilpotent.
-/
theorem LieAlgebra.ad_nilpotent_of_nilpotent {a : A} (h : IsNilpotent a) :
    IsNilpotent (LieAlgebra.ad R A a) := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : IsNilpotent (LinearMap.mulLeft R a) := by rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hr : IsNilpotent (LinearMap.mulRight R a) := by rwa [LinearMap.isNilpotent_mulRight_iff]
  exact (LinearMap.commute_mulLeft_right a a).isNilpotent_sub hl hr
/-
**LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad {L : Type*} [LieRing L] [Li
eAlgebra R L] (K : LieSubalgebra R L) {x : K} (h : IsNilpotent (LieAlgebra.ad R 
L ↑x)) : IsNilpotent (LieAlgebra.ad R K x)
参数：K : LieSubalgebra R L；h : IsNilpotent (LieAlgebra.ad R L ↑x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.submodule_pow_eq_zero_of_pow_eq_zero`：∀ {R : Type u_1} {M : T
ype u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
R M]   {N : Submodule R M} {g : Modul…
· 使用定理 `LieSubalgebra.ad_comp_incl_eq`：LieSubalgebra.ad_comp_incl_eq (K : LieSub
algebra R L) (x : K) : (ad R L ↑x).comp (K.incl : K ->ₗ[R] L) = (K.incl : K ->ₗ[
R] L).comp (ad R K …
-/
theorem LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad {L : Type*} [LieRing L] [LieAlgebra R L]
    (K : LieSubalgebra R L) {x : K} (h : IsNilpotent (LieAlgebra.ad R L ↑x)) :
    IsNilpotent (LieAlgebra.ad R K x) := by
  obtain ⟨n, hn⟩ := h
  use n
  exact Module.End.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn
/-
**LieAlgebra.isNilpotent_ad_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.isNilpotent_ad_of_isNilpotent {L : LieSubalgebra R A} {x : L} (
h : IsNilpotent (x : A)) : IsNilpotent (LieAlgebra.ad R L x)
参数：h : IsNilpotent (x : A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad`：LieSubalgebra.isNilpoten
t_ad_of_isNilpotent_ad {L : Type*} [LieRing L] [LieAlgebra R L] (K : LieSubalgeb
ra R L) {x : K} (h : IsNilpotent (Li…
· 使用定理 `LieAlgebra.ad_nilpotent_of_nilpotent`：LieAlgebra.ad_nilpotent_of_nilpote
nt {a : A} (h : IsNilpotent a) : IsNilpotent (LieAlgebra.ad R A a)
-/
theorem LieAlgebra.isNilpotent_ad_of_isNilpotent
    {L : LieSubalgebra R A} {x : L} (h : IsNilpotent (x : A)) :
    IsNilpotent (LieAlgebra.ad R L x) :=
  L.isNilpotent_ad_of_isNilpotent_ad <| LieAlgebra.ad_nilpotent_of_nilpotent h

end CommRing

section Field

variable {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The adjoint of a semisimple element is semisimple. -/
/-
**LieAlgebra.ad_isSemisimple_of_isSemisimple** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.ad_isSemisimple_of_isSemisimple {a : Module.End K V} (ha : a.Is
Semisimple) : (LieAlgebra.ad K (Module.End K V) a).IsSemisimple
参数：ha : a.IsSemisimple。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.ad_eq_lmul_left_sub_lmul_right`：LieAlgebra.ad_eq_lmul_left_su
b_lmul_right (A : Type v) [Ring A] [Algebra R A] : (ad R A : A -> Module.End R A
) = LinearMap.mulLeft R - Linea…
· 使用定理 `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`：isSemisimple_of_squ
arefree_aeval_eq_zero {p : K[X]} (hp : Squarefree p) (hpf : aeval f p = 0) : f.I
sSemisimple
· 使用定理 `Module.End.IsSemisimple.minpoly_squarefree`：∀ {M : Type u_2} [inst : Add
CommGroup M] {K : Type u_3} [inst_1 : Field K] [inst_2 : _root_.Module K M]   {f
 : Module.End K M} [FiniteDimens…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
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
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.aeval_op_apply`：aeval_op_apply (x : A) (p : R[X]) : aeval (Mu
lOpposite.op x) p = MulOpposite.op (aeval x p)
· 使用定理 `MulOpposite.op_zero`：∀ {α : Type u_1} [inst : Zero α], MulOpposite.op 0 
= 0
· 使用定理 `Module.End.IsSemisimple.sub_of_commute`：∀ {M : Type u_2} [inst : AddComm
Group M] {K : Type u_3} [inst_1 : Field K] [inst_2 : _root_.Module K M]   {f g :
 Module.End K M} [FiniteDime…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LinearMap.commute_mulLeft_right`：commute_mulLeft_right (a b : A) : Commu
te (mulLeft R a) (mulRight R b)

--- 原说明 ---
The adjoint of a semisimple element is semisimple.
-/
theorem LieAlgebra.ad_isSemisimple_of_isSemisimple {a : Module.End K V} (ha : a.IsSemisimple) :
    (LieAlgebra.ad K (Module.End K V) a).IsSemisimple := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : Module.End.IsSemisimple (LinearMap.mulLeft K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have : Polynomial.aeval (Algebra.lmul K (Module.End K V) a) (minpoly K a) = 0 := by
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    simpa using! this
  have hr : Module.End.IsSemisimple (LinearMap.mulRight K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have hrw : LinearMap.mulRight K a =
        (Algebra.lsmul (A := (Module.End K V)ᵐᵒᵖ) K K (Module.End K V)) (.op a) := by
      ext; simp [Algebra.lsmul]
    rw [hrw, Polynomial.aeval_algHom_apply, Polynomial.aeval_op_apply, minpoly.aeval,
      MulOpposite.op_zero, map_zero]
  exact hl.sub_of_commute (LinearMap.commute_mulLeft_right a a) hr

end Field

