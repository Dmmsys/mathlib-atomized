/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base change for the naive cotangent complex

This file shows that the cotangent space and first homology of the naive cotangent complex
commute with base change.

## Main results

- `Algebra.Extension.tensorCotangentSpace`: If `T` is an `R`-algebra, there is a `T`-linear
  isomorphism `T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange).CotangentSpace`.
- `Algebra.Extension.tensorCotangentOfFlat`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`.
- `Algebra.Extension.tensorH1CotangentOfFlat`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`.
- `Algebra.tensorH1CotangentOfFlat`: Flat base change commutes with `H1Cotangent`.

-/

public section

universe u

open TensorProduct

namespace Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

variable {R S} (P : Extension.{u} R S)
variable (T : Type*) [CommRing T] [Algebra R T]

/-- The cotangent space of an extension commutes with base change. -/
noncomputable
/-
**Algebra.Extension.tensorCotangentSpace** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Exte
nsion`。
形式化陈述：tensorCotangentSpace (P : Extension.{u} R S) (T : Type*) [CommRing T] [Alg
ebra R T] : T otimes[R] P.CotangentSpace ≃ₗ[T] (P.baseChange (T
参数：P : Extension.{u} R S；T : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerRingTensorProductBaseChange`：∀ {R : T
ype u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra 
R S] (P : Algebra.Extension R S)   {T : Type u_1} [i…
-/
def tensorCotangentSpace (P : Extension.{u} R S) (T : Type*) [CommRing T] [Algebra R T] :
    T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange (T := T)).CotangentSpace :=
  letI := P.algebraBaseChange T
  letI : Algebra S (T ⊗[R] S) := TensorProduct.rightAlgebra
  letI : Algebra P.Ring (T ⊗[R] S) := Algebra.compHom _ (algebraMap P.Ring S)
  haveI : IsScalarTower R P.Ring (T ⊗[R] S) :=
    .of_algebraMap_eq fun x ↦ by
      rw [TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.tmul_one_eq_one_tmul, IsScalarTower.algebraMap_apply R P.Ring]
      rfl
  letI PT : Extension T (T ⊗[R] S) := P.baseChange
  haveI : IsPushout R T P.Ring PT.Ring := by
    convert! TensorProduct.isPushout (R := R) (T := P.Ring) (S := T)
    exact Algebra.algebra_ext _ _ fun _ ↦ rfl
  haveI : IsScalarTower P.Ring PT.Ring (T ⊗[R] S) := .of_algebraMap_eq' rfl
  (IsTensorProduct.assocOfMapSMul (TensorProduct.mk R T S) (isTensorProduct _ _ _)
    (TensorProduct.mk _ _ _) (isTensorProduct _ _ _) (by simp [Algebra.smul_def])
    (by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra])).symm ≪≫ₗ
  (AlgebraTensorModule.cancelBaseChange _ PT.Ring PT.Ring _ _).symm.restrictScalars T ≪≫ₗ
  (AlgebraTensorModule.congr (LinearEquiv.refl PT.Ring (T ⊗[R] S))
    (KaehlerDifferential.tensorKaehlerEquiv R T P.Ring PT.Ring)).restrictScalars T

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] algebraBaseChange in
/-
**Algebra.Extension.tensorCotangentSpace_tmul_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.Extension`。
形式化陈述：tensorCotangentSpace_tmul_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) : P.tenso
rCotangentSpace T (t otimesₜ (s otimesₜ x)) = t otimesₜ s otimesₜ KaehlerDiffere
ntial.map _ _ _ _ x
参数：t : T；s : S；x : Ω[P.Ring⁄R]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instSMulCommClass`：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Al
gebra R…
· 使用定理 `Algebra.Extension.instIsScalarTowerRingTensorProductBaseChange`：∀ {R : T
ype u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra 
R S] (P : Algebra.Extension R S)   {T : Type u_1} [i…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_1`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.mk_apply`：mk_apply (m : M) (n : N) : mk R M N m n = m otim
esₜ n
· 使用引理 `IsTensorProduct.assocOfMapSMul_symm_tmul`：assocOfMapSMul_symm_tmul (x₁ :
 M₁) (x₂ : M₂) (x₃ : M₃) : (assocOfMapSMul f hf g hg h₁ h₂).symm (x₁ otimesₜ g x
₂ x₃) = f x₁ x₂ otimesₜ x₃
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `KaehlerDifferential.span_range_derivation`：KaehlerDifferential.span_rang
e_derivation : Submodule.span S (Set.range <| KaehlerDifferential.D R S) = ⊤
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `KaehlerDifferential.tensorKaehlerEquiv_tmul_D`：tensorKaehlerEquiv_tmul_D
 [Algebra.IsPushout R S A B] (b a) : tensorKaehlerEquiv R S A B (b otimesₜ D _ _
 a) = b • D S B (algebraMap A B a)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `KaehlerDifferential.map_D`：KaehlerDifferential.map_D (x : A) : KaehlerDi
fferential.map R S A B (KaehlerDifferential.D R A x) = KaehlerDifferential.D S B
 (algebraMap A …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
（共 37 条，此处仅展示前 30 条）
-/
lemma tensorCotangentSpace_tmul_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) :
    P.tensorCotangentSpace T (t ⊗ₜ (s ⊗ₜ x)) = t ⊗ₜ s ⊗ₜ KaehlerDifferential.map _ _ _ _ x := by
  simp only [tensorCotangentSpace, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    ← mk_apply s x, IsTensorProduct.assocOfMapSMul_symm_tmul]
  simp only [mk_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  have : x ∈ Submodule.span P.Ring (Set.range (KaehlerDifferential.D R P.Ring)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction this using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => simp [tmul_add, hx, hy]
  | mem y hy =>
    obtain ⟨y, rfl⟩ := hy
    simp
  | smul a x _ hx =>
    rw [tmul_smul, ← algebraMap_smul (P.baseChange (T := T)).Ring a, LinearEquiv.map_smul,
      tmul_smul, hx, LinearMap.map_smul, ← algebraMap_smul (P.baseChange (T := T)).Ring a,
      tmul_smul]

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/-
**Algebra.Extension.tensorCotangentSpace_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
.Extension`。
形式化陈述：tensorCotangentSpace_tmul (t : T) (x : P.CotangentSpace) : P.tensorCotange
ntSpace T (t otimesₜ x) = t • CotangentSpace.map (P.toBaseChange T) x
参数：t : T；x : P.CotangentSpace。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instSMulCommClass`：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Al
gebra R…
· 使用定理 `Algebra.Extension.instIsScalarTowerRingTensorProductBaseChange`：∀ {R : T
ype u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra 
R S] (P : Algebra.Extension R S)   {T : Type u_1} [i…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_1`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Algebra.Extension.tensorCotangentSpace_tmul_tmul`：tensorCotangentSpace_t
mul_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) : P.tensorCotangentSpace T (t otimesₜ
 (s otimesₜ x)) = t otimesₜ s otimesₜ …
· 使用引理 `Algebra.Extension.CotangentSpace.map_tmul_eq_tmul_map`：map_tmul_eq_tmul_
map (f : P.Hom P') (x : S) (y : Ω[P.Ring⁄R]) : letI : Algebra P.Ring P'.Ring
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `LinearEquiv.map_add`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ 
: Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst_…
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
lemma tensorCotangentSpace_tmul (t : T) (x : P.CotangentSpace) :
    P.tensorCotangentSpace T (t ⊗ₜ x) = t • CotangentSpace.map (P.toBaseChange T) x := by
  dsimp only [CotangentSpace] at x
  induction x with
  | zero => rw [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, smul_add, hx, hy]
  | tmul s y =>
  simp [tensorCotangentSpace_tmul_tmul, CotangentSpace.map_tmul_eq_tmul_map,
    smul_tmul', Algebra.smul_def, RingHom.algebraMap_toAlgebra]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`. -/
/-
**Algebra.Extension.tensorCotangentOfFlat** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Ext
ension`。
形式化陈述：tensorCotangentOfFlat [Module.Flat R T] : T otimes[R] P.Cotangent ≃ₗ[T] (P
.baseChange (T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`.
-/
noncomputable def tensorCotangentOfFlat [Module.Flat R T] :
    T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
  AlgebraTensorModule.congr (.refl T T) (P.cotangentEquivCotangentKer.restrictScalars R) ≪≫ₗ
    P.ker.tensorCotangentEquiv R T ≪≫ₗ
    (Ideal.Cotangent.equivOfEq _ _ (P.ker_baseChange T).symm).restrictScalars T ≪≫ₗ
    (P.baseChange (T := T)).cotangentEquivCotangentKer.symm.restrictScalars T

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/-
**Algebra.Extension.tensorCotangentOfFlat_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.Extension`。
形式化陈述：tensorCotangentOfFlat_tmul [Module.Flat R T] (t : T) (x : P.Cotangent) : P
.tensorCotangentOfFlat T (t otimesₜ x) = t • Cotangent.map (P.toBaseChange T) x
参数：t : T；x : P.Cotangent。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `Algebra.Extension.cotangentEquivCotangentKer_apply`：∀ {R : Type u} {S : 
Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Al
gebra.Extension R S}   (x : P.Cotangent)…
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
-/
lemma tensorCotangentOfFlat_tmul [Module.Flat R T] (t : T) (x : P.Cotangent) :
    P.tensorCotangentOfFlat T (t ⊗ₜ x) = t • Cotangent.map (P.toBaseChange T) x := by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [tensorCotangentOfFlat, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply, cotangentEquivCotangentKer_apply,
    Cotangent.val_mk, Ideal.tensorCotangentEquiv_tmul, map_smul, Cotangent.map_mk,
    Hom.toAlgHom_apply, Ideal.Cotangent.equivOfEq_toCotangent]
  rfl

/-- The canonical map `T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange).H1Cotangent`. -/
@[expose]
noncomputable
/-
**Algebra.Extension.tensorToH1Cotangent** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Exten
sion`。
形式化陈述：tensorToH1Cotangent : T otimes[R] P.H1Cotangent ->ₗ[T] (P.baseChange (T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def tensorToH1Cotangent : T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  letI : Algebra S (T ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  LinearMap.liftBaseChange T <|
    (Extension.H1Cotangent.map (P.toBaseChange T)).restrictScalars R

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/-
**Algebra.Extension.tensorToH1Cotangent_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.
Extension`。
形式化陈述：tensorToH1Cotangent_tmul (t : T) (x : P.H1Cotangent) : (P.tensorToH1Cotang
ent T (t otimesₜ x)).val = t • Cotangent.map (P.toBaseChange T) x.val
参数：t : T；x : P.H1Cotangent。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma tensorToH1Cotangent_tmul (t : T) (x : P.H1Cotangent) :
    (P.tensorToH1Cotangent T (t ⊗ₜ x)).val = t • Cotangent.map (P.toBaseChange T) x.val :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- If `T` is `R`-flat, the canonical map `T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange T).H1Cotangent`
is bijective. -/
/-
**Algebra.Extension.tensorToH1Cotangent_bijective_of_flat** 是 Mathlib 中的一个引理，位于命
名空间 `Algebra.Extension`。
形式化陈述：tensorToH1Cotangent_bijective_of_flat [Module.Flat R T] : Function.Bijecti
ve (P.tensorToH1Cotangent T)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
`：bijective_of_surjective_of_bijective_of_bijective_of_injective (hi₁ : Function
.Surjective i₁) (hi₂ : Function.Bijective i₂) (hi₄ : Function.…
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_1`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_zero`：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->
ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.Extension.h1Cotangentι_apply`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   (self : ↥P.cotang…
· 使用定理 `Algebra.Extension.Cotangent.val_smul''`：∀ {R : Type u} {S : Type v} [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extens
ion R S}   (r : R) (x : P.Co…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.restrictScalars_toLinearMap`：∀ (R : Type u_1) {S : Type u_4}
 {M : Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [ins
t_2 : AddCommMonoid M] [inst_…
· 使用引理 `Algebra.Extension.tensorCotangentOfFlat_tmul`：tensorCotangentOfFlat_tmul
 [Module.Flat R T] (t : T) (x : P.Cotangent) : P.tensorCotangentOfFlat T (t otim
esₜ x) = t • Cotangent.map (P.toBa…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用引理 `Algebra.Extension.tensorCotangentSpace_tmul`：tensorCotangentSpace_tmul (
t : T) (x : P.CotangentSpace) : P.tensorCotangentSpace T (t otimesₜ x) = t • Cot
angentSpace.map (P.toBaseChange T…
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If `T` is `R`-flat, the canonical map `T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange 
T).H1Cotangent`
is bijective.
-/
lemma tensorToH1Cotangent_bijective_of_flat [Module.Flat R T] :
    Function.Bijective (P.tensorToH1Cotangent T) := by
  -- We apply the five lemma.
  apply LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective (M₁ := Unit)
      (N₁ := Unit) (M₂ := Unit) (N₂ := Unit)
    -- The row `0 → 0 → T ⊗ H¹(P) → T ⊗ P.Cotangent → T ⊗ P.CotangentSpace`.
    0 0
    ((P.h1Cotangentι.restrictScalars R).lTensor T)
    ((P.cotangentComplex.restrictScalars R).lTensor T)
    -- The row `0 → 0 → H¹(T ⊗ P) → (T ⊗ P).Cotangent → (T ⊗ P).CotangentSpace`.
    0 0
    (h1Cotangentι.restrictScalars R)
    ((P.baseChange (T := T)).cotangentComplex.restrictScalars R)
    -- The vertical maps induced by base change.
    0 0
    ((P.tensorToH1Cotangent T).restrictScalars R)
    ((P.tensorCotangentOfFlat T).restrictScalars R)
    ((P.tensorCotangentSpace T).restrictScalars R)
  · simp
  · simp
  · ext
    simp
  · ext
    simp [CotangentSpace.map_cotangentComplex]
  · tauto
  · simp only [LinearMap.exact_zero_iff_injective]
    apply Module.Flat.lTensor_preserves_injective_linearMap
    exact h1Cotangentι_injective
  · apply Module.Flat.lTensor_exact
    exact P.exact_hCotangentι_cotangentComplex
  · tauto
  · rw [LinearMap.exact_zero_iff_injective]
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · apply exact_hCotangentι_cotangentComplex
  · tauto
  · simp
  · exact (P.tensorCotangentOfFlat T).bijective
  · exact (P.tensorCotangentSpace T).injective

/-- If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`. -/
@[expose]
/-
**Algebra.Extension.tensorH1CotangentOfFlat** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.E
xtension`。
形式化陈述：tensorH1CotangentOfFlat [Module.Flat R T] : T otimes[R] P.H1Cotangent ≃ₗ[T
] (P.baseChange (T
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Extension.tensorToH1Cotangent_bijective_of_flat`：tensorToH1Cotan
gent_bijective_of_flat [Module.Flat R T] : Function.Bijective (P.tensorToH1Cotan
gent T)

--- 原说明 ---
If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`.
-/
noncomputable def tensorH1CotangentOfFlat [Module.Flat R T] :
    T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  LinearEquiv.ofBijective (P.tensorToH1Cotangent T)
    (P.tensorToH1Cotangent_bijective_of_flat T)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**Algebra.Extension.tensorH1CotangentOfFlat_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Alge
bra.Extension`。
形式化陈述：tensorH1CotangentOfFlat_tmul [Module.Flat R T] (t : T) (x : P.H1Cotangent)
 : P.tensorH1CotangentOfFlat T (t otimesₜ x) = t • H1Cotangent.map (P.toBaseChan
ge T) x
参数：t : T；x : P.H1Cotangent。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma tensorH1CotangentOfFlat_tmul [Module.Flat R T] (t : T) (x : P.H1Cotangent) :
    P.tensorH1CotangentOfFlat T (t ⊗ₜ x) = t • H1Cotangent.map (P.toBaseChange T) x :=
  rfl

end Extension

/-- Flat base change commutes with `H1Cotangent`. -/
/-
**Algebra.tensorH1CotangentOfFlat** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：tensorH1CotangentOfFlat (T : Type*) [CommRing T] [Algebra R T] [Module.Fla
t R T] : T otimes[R] H1Cotangent R S ≃ₗ[T] H1Cotangent T (T otimes[R] S)
参数：T : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flat base change commutes with `H1Cotangent`.
-/
noncomputable def tensorH1CotangentOfFlat (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T] :
    T ⊗[R] H1Cotangent R S ≃ₗ[T] H1Cotangent T (T ⊗[R] S) :=
  (Generators.self R S).toExtension.tensorH1CotangentOfFlat T ≪≫ₗ
    (Extension.H1Cotangent.equiv
      ((Generators.self R S).baseChangeFromBaseChange T)
      ((Generators.self R S).baseChangeToBaseChange T)).restrictScalars T ≪≫ₗ
    ((Generators.self R S).baseChange (T := T)).equivH1Cotangent.restrictScalars T

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] TensorProduct.rightAlgebra in
/-
**Algebra.tensorH1CotangentOfFlat_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：tensorH1CotangentOfFlat_tmul (T : Type*) [CommRing T] [Algebra R T] [Modul
e.Flat R T] (t : T) (x : H1Cotangent R S) : tensorH1CotangentOfFlat R S T (t oti
mesₜ x) = t • H1Cotangent.map _ _ _ _ x
参数：T : Type*；t : T；x : H1Cotangent R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Extension.H1Cotangent.map_comp_apply`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R' : Type u'} {S…
· 使用定理 `Algebra.H1Cotangent.map.eq_1`：∀ (R : Type u) (S : Type v) [inst : CommRi
ng R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (S' : Type u_2)   [inst_3 : C
ommRing S'] [inst_…
· 使用定理 `Algebra.Extension.H1Cotangent.map_eq`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u'} {S…
-/
lemma tensorH1CotangentOfFlat_tmul (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T]
    (t : T) (x : H1Cotangent R S) :
    tensorH1CotangentOfFlat R S T (t ⊗ₜ x) = t • H1Cotangent.map _ _ _ _ x := by
  simp only [tensorH1CotangentOfFlat, LinearEquiv.trans_apply,
    Extension.tensorH1CotangentOfFlat_tmul, map_smul, LinearEquiv.restrictScalars_apply,
    Extension.H1Cotangent.equiv, LinearEquiv.coe_mk, Generators.equivH1Cotangent,
    Generators.H1Cotangent.equiv]
  rw [← Extension.H1Cotangent.map_comp_apply, ← Extension.H1Cotangent.map_comp_apply,
    H1Cotangent.map, Extension.H1Cotangent.map_eq]

end Algebra

