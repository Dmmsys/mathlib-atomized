/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Kähler differential module under base change

## Main results
- `KaehlerDifferential.tensorKaehlerEquivBase`: `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.tensorKaehlerEquiv`: `(B ⊗[A] Ω[A⁄R]) ≃ₗ[B] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.isLocalizedModule_of_isLocalizedModule`:
  `Ω[Aₚ/Rₚ]` is the localization of `Ω[A/R]` at `p`.

-/

@[expose] public section

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]

open TensorProduct

attribute [local instance] SMulCommClass.of_commMonoid

attribute [local irreducible] KaehlerDifferential

namespace KaehlerDifferential

/-- (Implementation). `A`-action on `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
/-
**KaehlerDifferential.mulActionBaseChange** 是 Mathlib 中的一个缩写定义，位于命名空间 `KaehlerDi
fferential`。
形式化陈述：mulActionBaseChange : MulAction A (S otimes[R] Ω[A⁄R])
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev mulActionBaseChange : MulAction A (S ⊗[R] Ω[A⁄R]) :=
  (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A

attribute [local instance] mulActionBaseChange

@[simp]
/-
**KaehlerDifferential.mulActionBaseChange_smul_tmul** 是 Mathlib 中的一个引理，位于命名空间 `K
aehlerDifferential`。
形式化陈述：mulActionBaseChange_smul_tmul (a : A) (s : S) (x : Ω[A⁄R]) : a • (s otimes
ₜ[R] x) = s otimesₜ (a • x)
参数：a : A；s : S；x : Ω[A⁄R]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma mulActionBaseChange_smul_tmul (a : A) (s : S) (x : Ω[A⁄R]) :
    a • (s ⊗ₜ[R] x) = s ⊗ₜ (a • x) := rfl

@[local simp]
/-
**KaehlerDifferential.mulActionBaseChange_smul_zero** 是 Mathlib 中的一个引理，位于命名空间 `K
aehlerDifferential`。
形式化陈述：mulActionBaseChange_smul_zero (a : A) : a • (0 : S otimes[R] Ω[A⁄R]) = 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `KaehlerDifferential.mulActionBaseChange_smul_tmul`：mulActionBaseChange_s
mul_tmul (a : A) (s : S) (x : Ω[A⁄R]) : a • (s otimesₜ[R] x) = s otimesₜ (a • x)
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma mulActionBaseChange_smul_zero (a : A) :
    a • (0 : S ⊗[R] Ω[A⁄R]) = 0 := by
  rw [← zero_tmul _ (0 : Ω[A⁄R]), mulActionBaseChange_smul_tmul, smul_zero]

@[local simp]
/-
**KaehlerDifferential.mulActionBaseChange_smul_add** 是 Mathlib 中的一个引理，位于命名空间 `Ka
ehlerDifferential`。
形式化陈述：mulActionBaseChange_smul_add (a : A) (x y : S otimes[R] Ω[A⁄R]) : a • (x +
 y) = a • x + a • y
参数：a : A；x y : S otimes[R] Ω[A⁄R]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
lemma mulActionBaseChange_smul_add (a : A) (x y : S ⊗[R] Ω[A⁄R]) :
    a • (x + y) = a • x + a • y := by
  change (TensorProduct.comm R S Ω[A⁄R]).symm (a • (TensorProduct.comm R S Ω[A⁄R]) (x + y)) = _
  rw [map_add, smul_add, map_add]
  rfl

/-- (Implementation). `A`-module structure on `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
/-
**KaehlerDifferential.moduleBaseChange** 是 Mathlib 中的一个缩写定义，位于命名空间 `KaehlerDiffe
rential`。
形式化陈述：moduleBaseChange : Module A (S otimes[R] Ω[A⁄R]) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev moduleBaseChange :
    Module A (S ⊗[R] Ω[A⁄R]) where
  __ := (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A
  add_smul r s x := by induction x <;> simp [add_smul, tmul_add, *, add_add_add_comm]
  zero_smul x := by induction x <;> simp [*]
  smul_zero := by simp
  smul_add := by simp

attribute [local instance] moduleBaseChange
/-
**KaehlerDifferential.** 是 Mathlib 中的一个实例，位于命名空间 `KaehlerDifferential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R A (S ⊗[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  induction x
  · simp only [smul_zero]
  · rw [mulActionBaseChange_smul_tmul, algebraMap_smul, tmul_smul]
  · simp only [smul_add, *]
/-
**KaehlerDifferential.** 是 Mathlib 中的一个实例，位于命名空间 `KaehlerDifferential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass S A (S ⊗[R] Ω[A⁄R]) where
  smul_comm s a x := by
    induction x
    · simp only [smul_zero]
    · rw [mulActionBaseChange_smul_tmul, smul_tmul', smul_tmul', mulActionBaseChange_smul_tmul]
    · simp only [smul_add, *]
/-
**KaehlerDifferential.** 是 Mathlib 中的一个实例，位于命名空间 `KaehlerDifferential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass A S (S ⊗[R] Ω[A⁄R]) where
  smul_comm s a x := by rw [← smul_comm]

/-- (Implementation). `B = S ⊗[R] A`-module structure on `S ⊗[R] Ω[A⁄R]`. -/
@[reducible] noncomputable
/-
**KaehlerDifferential.moduleBaseChange'** 是 Mathlib 中的一个定义，位于命名空间 `KaehlerDiffer
ential`。
形式化陈述：moduleBaseChange' [Algebra.IsPushout R S A B] : Module B (S otimes[R] Ω[A⁄
R])
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `KaehlerDifferential.instIsScalarTowerTensorProduct`：∀ (R : Type u_1) (S 
: Type u_2) (A : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : A
lgebra R S]   [inst_3 : CommRing A] [ins…
· 使用定理 `KaehlerDifferential.instSMulCommClassTensorProduct_1`：∀ (R : Type u_1) (
S : Type u_2) (A : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 :
 Algebra R S]   [inst_3 : CommRing A] [ins…

--- 原说明 ---
(Implementation). `B = S ⊗[R] A`-module structure on `S ⊗[R] Ω[A⁄R]`.
-/
def moduleBaseChange' [Algebra.IsPushout R S A B] :
    Module B (S ⊗[R] Ω[A⁄R]) :=
  Module.compHom _ (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S ⊗[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)).toRingHom

attribute [local instance] moduleBaseChange'
/-
**KaehlerDifferential.** 是 Mathlib 中的一个实例，位于命名空间 `KaehlerDifferential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsPushout R S A B] :
    IsScalarTower A B (S ⊗[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S ⊗[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap A B r)) • x = r • x
  simp only [Algebra.pushoutDesc_right, Module.End.smul_def, Algebra.lsmul_coe]
/-
**KaehlerDifferential.** 是 Mathlib 中的一个实例，位于命名空间 `KaehlerDifferential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsPushout R S A B] :
    IsScalarTower S B (S ⊗[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S ⊗[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap S B r)) • x = r • x
  simp only [Algebra.pushoutDesc_left, Module.End.smul_def, Algebra.lsmul_coe]
/-
**KaehlerDifferential.map_liftBaseChange_smul** 是 Mathlib 中的一个引理，位于命名空间 `Kaehler
Differential`。
形式化陈述：map_liftBaseChange_smul [h : Algebra.IsPushout R S A B] (b : B) (x) : ((ma
p R S A B).restrictScalars R).liftBaseChange S (b • x) = b • ((map R S A B).rest
rictScalars R).liftBaseChange S x
参数：b : B；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsBaseChange.inductionOn`：∀ {R : Type u_1} {M : Type v₁} {N : Type v₂} {
S : Type v₃} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : Com
mSemiring R] […
· 使用定理 `Algebra.IsPushout.out`：∀ {R : Type u_1} {S : Type v₃} {inst : CommSemiri
ng R} {inst_1 : CommSemiring S} {inst_2 : Algebra R S} {R' : Type u_6}   {S' : T
ype u_7} {i…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `KaehlerDifferential.instIsScalarTowerTensorProduct_1`：∀ (R : Type u_1) (
S : Type u_2) (A : Type u_3) (B : Type u_4) [inst : CommRing R] [inst_1 : CommRi
ng S]   [inst_2 : Algebra R S] [inst_3 : C…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `KaehlerDifferential.instIsScalarTowerTensorProduct_2`：∀ (R : Type u_1) (
S : Type u_2) (A : Type u_3) (B : Type u_4) [inst : CommRing R] [inst_1 : CommRi
ng S]   [inst_2 : Algebra R S] [inst_3 : C…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
lemma map_liftBaseChange_smul [h : Algebra.IsPushout R S A B] (b : B) (x) :
    ((map R S A B).restrictScalars R).liftBaseChange S (b • x) =
    b • ((map R S A B).restrictScalars R).liftBaseChange S x := by
  induction b using h.1.inductionOn with
  | zero => simp only [zero_smul, map_zero]
  | smul s b e => rw [smul_assoc, map_smul, e, smul_assoc]
  | add b₁ b₂ e₁ e₂ => simp only [map_add, e₁, e₂, add_smul]
  | tmul a =>
    induction x
    · simp only [smul_zero, map_zero]
    · simp [smul_comm]
    · simp only [map_add, smul_add, *]

/-- (Implementation).
The `S`-derivation `B = S ⊗[R] A` to `S ⊗[R] Ω[A⁄R]` sending `a ⊗ b` to `a ⊗ d b`. -/
noncomputable
/-
**KaehlerDifferential.derivationTensorProduct** 是 Mathlib 中的一个定义，位于命名空间 `Kaehler
Differential`。
形式化陈述：derivationTensorProduct [h : Algebra.IsPushout R S A B] : Derivation S B (
S otimes[R] Ω[A⁄R]) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def derivationTensorProduct [h : Algebra.IsPushout R S A B] :
    Derivation S B (S ⊗[R] Ω[A⁄R]) where
  __ := h.out.lift ((TensorProduct.mk R S Ω[A⁄R] 1).comp (D R A).toLinearMap)
  map_one_eq_zero' := by
    rw [← (algebraMap A B).map_one]
    refine (h.out.lift_eq _ _).trans ?_
    dsimp
    rw [Derivation.map_one_eq_zero, TensorProduct.tmul_zero]
  leibniz' a b := by
    induction a using h.out.inductionOn with
    | zero => rw [map_zero, zero_smul, smul_zero, zero_add, zero_mul, map_zero]
    | smul x y e =>
      rw [smul_mul_assoc, map_smul, e, map_smul, smul_add,
        smul_comm x b, smul_assoc]
    | add b₁ b₂ e₁ e₂ => simp only [add_mul, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]
    | tmul z =>
      dsimp
      induction b using h.out.inductionOn with
      | zero => rw [map_zero, zero_smul, smul_zero, zero_add, mul_zero, map_zero]
      | tmul =>
        simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          algebraMap_smul, ← map_mul]
        rw [← IsScalarTower.toAlgHom_apply R, ← AlgHom.toLinearMap_apply, h.out.lift_eq,
          ← IsScalarTower.toAlgHom_apply R, ← AlgHom.toLinearMap_apply, h.out.lift_eq,
          ← IsScalarTower.toAlgHom_apply R, ← AlgHom.toLinearMap_apply, h.out.lift_eq]
        simp only [LinearMap.coe_comp, Derivation.coeFn_coe, Function.comp_apply,
          Derivation.leibniz, mk_apply, mulActionBaseChange_smul_tmul, TensorProduct.tmul_add]
      | smul _ _ e =>
        rw [mul_comm, smul_mul_assoc, map_smul, mul_comm, e,
            map_smul, smul_add, smul_comm, smul_assoc]
      | add _ _ e₁ e₂ => simp only [mul_add, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]
/-
**KaehlerDifferential.derivationTensorProduct_algebraMap** 是 Mathlib 中的一个引理，位于命名
空间 `KaehlerDifferential`。
形式化陈述：derivationTensorProduct_algebraMap [Algebra.IsPushout R S A B] (x) : deriv
ationTensorProduct R S A B (algebraMap A B x) = 1 otimesₜ D _ _ x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBaseChange.lift_eq`：∀ {R : Type u_1} {M : Type v₁} {N : Type v₂} {S : 
Type v₃} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : CommSem
iring R] […
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma derivationTensorProduct_algebraMap [Algebra.IsPushout R S A B] (x) :
    derivationTensorProduct R S A B (algebraMap A B x) =
    1 ⊗ₜ D _ _ x :=
IsBaseChange.lift_eq _ _ _
/-
**KaehlerDifferential.tensorKaehlerEquiv_left_inv** 是 Mathlib 中的一个引理，位于命名空间 `Kae
hlerDifferential`。
形式化陈述：tensorKaehlerEquiv_left_inv [Algebra.IsPushout R S A B] : ((derivationTens
orProduct R S A B).liftKaehlerDifferential.restrictScalars S).comp (((map R S A 
B).restrictScalars R).liftBaseChange S) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars R : (M ->ₗ[S] M₂) -> M ->ₗ[R] M₂)
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `KaehlerDifferential.instIsScalarTowerTensorProduct_2`：∀ (R : Type u_1) (
S : Type u_2) (A : Type u_3) (B : Type u_4) [inst : CommRing R] [inst_1 : CommRi
ng S]   [inst_2 : Algebra R S] [inst_3 : C…
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `KaehlerDifferential.tensorProductTo_surjective`：KaehlerDifferential.tens
orProductTo_surjective : Function.Surjective (KaehlerDifferential.D R S).tensorP
roductTo
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
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
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `KaehlerDifferential.map_D`：KaehlerDifferential.map_D (x : A) : KaehlerDi
fferential.map R S A B (KaehlerDifferential.D R A x) = KaehlerDifferential.D S B
 (algebraMap A …
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `KaehlerDifferential.instIsScalarTowerTensorProduct_1`：∀ (R : Type u_1) (
S : Type u_2) (A : Type u_3) (B : Type u_4) [inst : CommRing R] [inst_1 : CommRi
ng S]   [inst_2 : Algebra R S] [inst_3 : C…
· 使用定理 `Derivation.liftKaehlerDifferential_comp_D`：Derivation.liftKaehlerDiffere
ntial_comp_D (D' : Derivation R S M) (x : S) : D'.liftKaehlerDifferential (Kaehl
erDifferential.D R S x) = D' x
· 使用引理 `KaehlerDifferential.derivationTensorProduct_algebraMap`：derivationTensor
Product_algebraMap [Algebra.IsPushout R S A B] (x) : derivationTensorProduct R S
 A B (algebraMap A B x) = 1 otimesₜ D _ _ x
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `KaehlerDifferential.instSMulCommClassTensorProduct`：∀ (R : Type u_1) (S 
: Type u_2) (A : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : A
lgebra R S]   [inst_3 : CommRing A] [ins…
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
（共 35 条，此处仅展示前 30 条）
-/
lemma tensorKaehlerEquiv_left_inv [Algebra.IsPushout R S A B] :
    ((derivationTensorProduct R S A B).liftKaehlerDifferential.restrictScalars S).comp
    (((map R S A B).restrictScalars R).liftBaseChange S) = LinearMap.id := by
  refine LinearMap.restrictScalars_injective R ?_
  apply TensorProduct.ext'
  intro x y
  obtain ⟨y, rfl⟩ := tensorProductTo_surjective _ _ y
  induction y
  · simp only [map_zero, TensorProduct.tmul_zero]
  · simp only [LinearMap.restrictScalars_comp, Derivation.tensorProductTo_tmul, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.liftBaseChange_tmul, map_smul,
      map_D, LinearMap.map_smul_of_tower, Derivation.liftKaehlerDifferential_comp_D,
      LinearMap.id_coe, id_eq, derivationTensorProduct_algebraMap]
    rw [smul_comm, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  · simp only [map_add, TensorProduct.tmul_add, *]

/-- The canonical isomorphism `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
Also see `KaehlerDifferential.tensorKaehlerEquiv` for the version with `B ⊗[A] Ω[A⁄R]`. -/
@[simps! symm_apply] noncomputable
/-
**KaehlerDifferential.tensorKaehlerEquivBase** 是 Mathlib 中的一个定义，位于命名空间 `KaehlerD
ifferential`。
形式化陈述：tensorKaehlerEquivBase [h : Algebra.IsPushout R S A B] : (S otimes[R] Ω[A⁄
R]) ≃ₗ[S] Ω[B⁄S] where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `KaehlerDifferential.instIsScalarTowerTensorProduct_2`：∀ (R : Type u_1) (
S : Type u_2) (A : Type u_3) (B : Type u_4) [inst : CommRing R] [inst_1 : CommRi
ng S]   [inst_2 : Algebra R S] [inst_3 : C…

--- 原说明 ---
The canonical isomorphism `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
Also see `KaehlerDifferential.tensorKaehlerEquiv` for the version with `B ⊗[A] Ω
[A⁄R]`.
-/
def tensorKaehlerEquivBase [h : Algebra.IsPushout R S A B] :
    (S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S] where
  __ := ((map R S A B).restrictScalars R).liftBaseChange S
  invFun := (derivationTensorProduct R S A B).liftKaehlerDifferential
  left_inv := LinearMap.congr_fun (tensorKaehlerEquiv_left_inv R S A B)
  right_inv x := by
    obtain ⟨x, rfl⟩ := tensorProductTo_surjective _ _ x
    dsimp
    induction x with
    | zero => simp
    | add x y e₁ e₂ => simp only [map_add, e₁, e₂]
    | tmul x y =>
      -- We use the specialized version of `map_smul` here for performance.
      simp only [Derivation.tensorProductTo_tmul, LinearMap.map_smul,
        Derivation.liftKaehlerDifferential_comp_D, map_liftBaseChange_smul]
      induction y using h.1.inductionOn
      · simp only [map_zero, smul_zero]
      · simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          derivationTensorProduct_algebraMap, LinearMap.liftBaseChange_tmul,
          LinearMap.coe_restrictScalars, map_D, one_smul]
      · -- We use the specialized version of `map_smul` here for performance.
        simp only [Derivation.map_smul, LinearMap.map_smul, *, smul_comm x]
      · simp only [map_add, smul_add, *]

@[simp]
/-
**KaehlerDifferential.tensorKaehlerEquivBase_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Kae
hlerDifferential`。
形式化陈述：tensorKaehlerEquivBase_tmul [Algebra.IsPushout R S A B] (a b) : tensorKaeh
lerEquivBase R S A B (a otimesₜ b) = a • map R S A B b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.liftBaseChange_tmul`：liftBaseChange_tmul (l : M ->ₗ[R] N) (x y
) : l.liftBaseChange A (x otimesₜ y) = x • l y
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma tensorKaehlerEquivBase_tmul [Algebra.IsPushout R S A B] (a b) :
    tensorKaehlerEquivBase R S A B (a ⊗ₜ b) = a • map R S A B b :=
  LinearMap.liftBaseChange_tmul _ _ _ _

@[deprecated (since := "2026-01-01")] alias tensorKaehlerEquiv_tmul := tensorKaehlerEquivBase_tmul

/--
If `B` is the tensor product of `S` and `A` over `R`,
then `Ω[B⁄S]` is the base change of `Ω[A⁄R]` along `R → S`.
-/
/-
**KaehlerDifferential.isBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `KaehlerDifferentia
l`。
形式化陈述：isBaseChange [h : Algebra.IsPushout R S A B] : IsBaseChange S ((map R S A 
B).restrictScalars R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `KaehlerDifferential.tensorKaehlerEquivBase_tmul`：tensorKaehlerEquivBase_
tmul [Algebra.IsPushout R S A B] (a b) : tensorKaehlerEquivBase R S A B (a otime
sₜ b) = a • map R S A B b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsBaseChange.comp`：IsBaseChange.comp {f : M ->ₗ[R] N} (hf : IsBaseChange
 S f) {g : N ->ₗ[S] O} (hg : IsBaseChange T g) : IsBaseChange T ((g.restrictScal
ars R).…
· 使用定理 `TensorProduct.isBaseChange`：TensorProduct.isBaseChange : IsBaseChange S 
(TensorProduct.mk R S M 1)
· 使用定理 `IsBaseChange.ofEquiv`：IsBaseChange.ofEquiv (e : M ≃ₗ[R] N) : IsBaseChang
e R e.toLinearMap

--- 原说明 ---
If `B` is the tensor product of `S` and `A` over `R`,
then `Ω[B⁄S]` is the base change of `Ω[A⁄R]` along `R → S`.
-/
lemma isBaseChange [h : Algebra.IsPushout R S A B] :
    IsBaseChange S ((map R S A B).restrictScalars R) := by
  convert!
    (TensorProduct.isBaseChange R Ω[A⁄R] S).comp
      (IsBaseChange.ofEquiv (tensorKaehlerEquivBase R S A B))
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, mk_apply, tensorKaehlerEquivBase_tmul, one_smul]
/-
**KaehlerDifferential.isLocalizedModule** 是 Mathlib 中的一个实例，位于命名空间 `KaehlerDiffer
ential`。
形式化陈述：isLocalizedModule (p : Submonoid R) [IsLocalization p S] [IsLocalization (
Algebra.algebraMapSubmonoid A p) B] : IsLocalizedModule p ((map R S A B).restric
tScalars R)
参数：p : Submonoid R；Algebra.algebraMapSubmonoid A p。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用引理 `Algebra.isPushout_of_isLocalization`：Algebra.isPushout_of_isLocalization
 [IsLocalization (Algebra.algebraMapSubmonoid T S) B] : Algebra.IsPushout R T A 
B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用引理 `KaehlerDifferential.isBaseChange`：isBaseChange [h : Algebra.IsPushout R 
S A B] : IsBaseChange S ((map R S A B).restrictScalars R)
-/
instance isLocalizedModule (p : Submonoid R) [IsLocalization p S]
      [IsLocalization (Algebra.algebraMapSubmonoid A p) B] :
    IsLocalizedModule p ((map R S A B).restrictScalars R) :=
  have := (Algebra.isPushout_of_isLocalization p S A B).symm
  (isLocalizedModule_iff_isBaseChange p S _).mpr (isBaseChange R S A B)
/-
**KaehlerDifferential.isLocalizedModule_of_isLocalizedModule** 是 Mathlib 中的一个实例，
位于命名空间 `KaehlerDifferential`。
形式化陈述：isLocalizedModule_of_isLocalizedModule (p : Submonoid R) [IsLocalization p
 S] [IsLocalizedModule p (IsScalarTower.toAlgHom R A B).toLinearMap] : IsLocaliz
edModule p ((map R S A B).restrictScalars R)
参数：p : Submonoid R；IsScalarTower.toAlgHom R A B。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLocalizedModule_iff_isLocalization`：isLocalizedModule_iff_isLocalizati
on : IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔ IsLocaliz
ation (Algebra.algebraMapS…
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
instance isLocalizedModule_of_isLocalizedModule (p : Submonoid R) [IsLocalization p S]
      [IsLocalizedModule p (IsScalarTower.toAlgHom R A B).toLinearMap] :
    IsLocalizedModule p ((map R S A B).restrictScalars R) :=
  have : IsLocalization (Algebra.algebraMapSubmonoid A p) B :=
    isLocalizedModule_iff_isLocalization.mp inferInstance
  inferInstance

/-- The canonical isomorphism `(B ⊗[A] Ω[A⁄R]) ≃ₗ[B] Ω[B⁄S]` for `B = S ⊗[R] A`.
Also see `KaehlerDifferential.tensorKaehlerEquivBase` for the version with `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
/-
**KaehlerDifferential.tensorKaehlerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `KaehlerDiffe
rential`。
形式化陈述：tensorKaehlerEquiv [h : Algebra.IsPushout R S A B] : B otimes[A] Ω[A⁄R] ≃ₗ
[B] Ω[B⁄S]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def tensorKaehlerEquiv [h : Algebra.IsPushout R S A B] :
    B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S] := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  let e₁ : B ⊗[A] Ω[A⁄R] ≃ₗ[A] Ω[A⁄R] ⊗[R] S :=
    AlgebraTensorModule.congr (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv (.refl _ _)
      ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange ..
  let e₂ : B ⊗[A] Ω[A⁄R] ≃ₗ[R] Ω[B⁄S] :=
    e₁.restrictScalars R ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquivBase R S A B).restrictScalars R
  refine { __ := e₂, map_smul' := ?_ }
  intro m x
  obtain ⟨m, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective m
  dsimp
  induction m with
  | zero => simp
  | add x y _ _ => simp only [add_smul, map_add, *]
  | tmul a b =>
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *]
  | tmul x y =>
  obtain ⟨x, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective x
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *, add_tmul]
  | tmul x z =>
  suffices b • z • a • x • KaehlerDifferential.map R S A B y =
      (algebraMap A B a * algebraMap S B b) • z • x • KaehlerDifferential.map R S A B y by
    simpa [e₂, e₁, smul_tmul', Algebra.IsPushout.equiv_tmul, ← mul_smul,
      Algebra.IsPushout.equiv_symm_algebraMap_left, Algebra.IsPushout.equiv_symm_algebraMap_right]
  simp only [← mul_smul, ← @algebraMap_smul S _ B, ← @algebraMap_smul A _ B]
  ring_nf

@[simp]
/-
**KaehlerDifferential.tensorKaehlerEquiv_tmul_D** 是 Mathlib 中的一个引理，位于命名空间 `Kaehl
erDifferential`。
形式化陈述：tensorKaehlerEquiv_tmul_D [Algebra.IsPushout R S A B] (b a) : tensorKaehle
rEquiv R S A B (b otimesₜ D _ _ a) = b • D S B (algebraMap A B a)
参数：b a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
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
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用引理 `KaehlerDifferential.tensorKaehlerEquivBase_tmul`：tensorKaehlerEquivBase_
tmul [Algebra.IsPushout R S A B] (a b) : tensorKaehlerEquivBase R S A B (a otime
sₜ b) = a • map R S A B b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
（共 42 条，此处仅展示前 30 条）
-/
lemma tensorKaehlerEquiv_tmul_D [Algebra.IsPushout R S A B] (b a) :
    tensorKaehlerEquiv R S A B (b ⊗ₜ D _ _ a) = b • D S B (algebraMap A B a) := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  obtain ⟨b, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective b
  induction b with
  | zero => simp
  | add x y _ _ => simp only [map_add, *, add_tmul, add_smul]
  | tmul a' s =>
  trans s • a' • D S B (algebraMap A B a)
  · simp [tensorKaehlerEquiv]
  · simp [Algebra.IsPushout.equiv_tmul, mul_smul, smul_comm]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/-
**KaehlerDifferential.tensorKaehlerEquiv_symm_D_tmul** 是 Mathlib 中的一个引理，位于命名空间 `
KaehlerDifferential`。
形式化陈述：tensorKaehlerEquiv_symm_D_tmul (s a) : (tensorKaehlerEquiv R S A (S otimes
[R] A)).symm (D _ _ (s otimesₜ a)) = algebraMap _ _ s otimesₜ D _ _ a
参数：s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `KaehlerDifferential.tensorKaehlerEquiv_tmul_D`：tensorKaehlerEquiv_tmul_D
 [Algebra.IsPushout R S A B] (b a) : tensorKaehlerEquiv R S A B (b otimesₜ D _ _
 a) = b • D S B (algebraMap A B a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Algebra.TensorProduct.right_algebraMap_apply`：right_algebraMap_apply (b 
: B) : algebraMap B (A otimes[R] B) b = 1 otimesₜ b
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Derivation.map_smul`：map_smul : D (r • a) = r • D a
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma tensorKaehlerEquiv_symm_D_tmul (s a) :
    (tensorKaehlerEquiv R S A (S ⊗[R] A)).symm (D _ _ (s ⊗ₜ a)) = algebraMap _ _ s ⊗ₜ D _ _ a := by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [show s ⊗ₜ 1 = algebraMap S (S ⊗ A) s by simp, Algebra.TensorProduct.right_algebraMap_apply,
    algebraMap_smul, ← Derivation.map_smul, smul_tmul', smul_eq_mul, mul_one]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/-
**KaehlerDifferential.tensorKaehlerEquiv_symm_D_tmul'** 是 Mathlib 中的一个引理，位于命名空间 
`KaehlerDifferential`。
形式化陈述：tensorKaehlerEquiv_symm_D_tmul' (s a) : (tensorKaehlerEquiv R S A (A otime
s[R] S)).symm (D _ _ (a otimesₜ s)) = algebraMap _ _ s otimesₜ D _ _ a
参数：s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `KaehlerDifferential.tensorKaehlerEquiv_tmul_D`：tensorKaehlerEquiv_tmul_D
 [Algebra.IsPushout R S A B] (b a) : tensorKaehlerEquiv R S A B (b otimesₜ D _ _
 a) = b • D S B (algebraMap A B a)
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Derivation.map_smul`：map_smul : D (r • a) = r • D a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用引理 `Algebra.TensorProduct.right_algebraMap_apply`：right_algebraMap_apply (b 
: B) : algebraMap B (A otimes[R] B) b = 1 otimesₜ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorKaehlerEquiv_symm_D_tmul' (s a) :
    (tensorKaehlerEquiv R S A (A ⊗[R] S)).symm (D _ _ (a ⊗ₜ s)) = algebraMap _ _ s ⊗ₜ D _ _ a := by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [algebraMap_smul, ← Derivation.map_smul, Algebra.smul_def,
    Algebra.TensorProduct.right_algebraMap_apply]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end KaehlerDifferential

