/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Derivations into Square-Zero Ideals

## Main statements

- `derivationToSquareZeroOfLift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

-/

@[expose] public section


section ToSquareZero

universe u v w

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [CommSemiring A] [CommRing B]
variable [Algebra R A] [Algebra R B] (I : Ideal B)

/-- If `f₁ f₂ : A →ₐ[R] B` are two lifts of the same `A →ₐ[R] B ⧸ I`,
  we may define a map `f₁ - f₂ : A →ₗ[R] I`. -/
/-
**diffToIdealOfQuotientCompEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：diffToIdealOfQuotientCompEq (f₁ f₂ : A ->ₐ[R] B) (e : (Ideal.Quotient.mkₐ 
R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) : A ->ₗ[R] I
参数：f₁ f₂ : A ->ₐ[R] B；e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ
 R I).comp f₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
If `f₁ f₂ : A →ₐ[R] B` are two lifts of the same `A →ₐ[R] B ⧸ I`,
  we may define a map `f₁ - f₂ : A →ₗ[R] I`.
-/
def diffToIdealOfQuotientCompEq (f₁ f₂ : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) : A →ₗ[R] I :=
  LinearMap.codRestrict (I.restrictScalars _) (f₁.toLinearMap - f₂.toLinearMap)
    (fun x => by simpa [Ideal.Quotient.eq] using congr($e x))

@[simp]
/-
**diffToIdealOfQuotientCompEq_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：diffToIdealOfQuotientCompEq_apply (f₁ f₂ : A ->ₐ[R] B) (e : (Ideal.Quotien
t.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) (x : A) : ((diffToIdealOf
QuotientCompEq I f₁ f₂ e) x : B) = f₁ x - f₂ x
参数：f₁ f₂ : A ->ₐ[R] B；e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ
 R I).comp f₂；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem diffToIdealOfQuotientCompEq_apply (f₁ f₂ : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) (x : A) :
    ((diffToIdealOfQuotientCompEq I f₁ f₂ e) x : B) = f₁ x - f₂ x :=
  rfl

variable [Algebra A B]

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`, each lift `A →ₐ[R] B`
of the canonical map `A →ₐ[R] B ⧸ I` corresponds to an `R`-derivation from `A` to `I`. -/
/-
**derivationToSquareZeroOfLift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：derivationToSquareZeroOfLift [IsScalarTower R A B] (hI : I ^ 2 = ⊥) (f : A
 ->ₐ[R] B) (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B 
⧸ I)) : Derivation R A I
参数：hI : I ^ 2 = ⊥；f : A ->ₐ[R] B；e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarT
ower.toAlgHom R A (B ⧸ I)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`, each lif
t `A →ₐ[R] B`
of the canonical map `A →ₐ[R] B ⧸ I` corresponds to an `R`-derivation from `A` t
o `I`.
-/
def derivationToSquareZeroOfLift [IsScalarTower R A B] (hI : I ^ 2 = ⊥) (f : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) :
    Derivation R A I := by
  refine
    { diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) ?_ with
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · ext; simp [e]
  · ext; simp
  · intro x y
    let F := diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) (by rw [e]; ext; rfl)
    have : (f x - algebraMap A B x) * (f y - algebraMap A B y) = 0 := by
      rw [← Ideal.mem_bot, ← hI, pow_two]
      convert! Ideal.mul_mem_mul (F x).2 (F y).2 using 1
    ext
    dsimp only [Submodule.coe_add, Submodule.coe_mk, LinearMap.coe_mk,
      diffToIdealOfQuotientCompEq_apply, Submodule.coe_smul_of_tower, IsScalarTower.coe_toAlgHom',
      LinearMap.toFun_eq_coe]
    simp only [map_mul, sub_mul, mul_sub, Algebra.smul_def] at this ⊢
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at this
    simp only [this]
    ring

variable (hI : I ^ 2 = ⊥)
/-
**derivationToSquareZeroOfLift_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivationToSquareZeroOfLift_apply [IsScalarTower R A B] (f : A ->ₐ[R] B) 
(e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) (x : 
A) : (derivationToSquareZeroOfLift I hI f e x : B) = f x - algebraMap A B x
参数：f : A ->ₐ[R] B；e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R
 A (B ⧸ I)；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem derivationToSquareZeroOfLift_apply [IsScalarTower R A B] (f : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) (x : A) :
    (derivationToSquareZeroOfLift I hI f e x : B) = f x - algebraMap A B x :=
  rfl

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`, each `R`-derivation
from `A` to `I` corresponds to a lift `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps -isSimp]
/-
**liftOfDerivationToSquareZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：liftOfDerivationToSquareZero [IsScalarTower R A B] (hI : I ^ 2 = ⊥) (f : D
erivation R A I) : A ->ₐ[R] B
参数：hI : I ^ 2 = ⊥；f : Derivation R A I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`, each `R`
-derivation
from `A` to `I` corresponds to a lift `A →ₐ[R] B` of the canonical map `A →ₐ[R] 
B ⧸ I`.
-/
def liftOfDerivationToSquareZero [IsScalarTower R A B] (hI : I ^ 2 = ⊥) (f : Derivation R A I) :
    A →ₐ[R] B :=
  { ((I.restrictScalars R).subtype.comp f.toLinearMap + (IsScalarTower.toAlgHom R A B).toLinearMap :
      A →ₗ[R] B) with
    toFun := fun x => f x + algebraMap A B x
    map_one' := by
      rw [map_one (algebraMap _ _), f.map_one_eq_zero, Submodule.coe_zero, zero_add]
    map_mul' := fun x y => by
      have : (f x : B) * f y = 0 := by
        rw [← Ideal.mem_bot, ← hI, pow_two]
        convert! Ideal.mul_mem_mul (f x).2 (f y).2 using 1
      simp only [map_mul, f.leibniz, add_mul, mul_add, Submodule.coe_add,
        Submodule.coe_smul_of_tower, Algebra.smul_def, this]
      ring
    commutes' := fun r => by
      simp only [Derivation.map_algebraMap, zero_add, Submodule.coe_zero, ←
        IsScalarTower.algebraMap_apply R A B r]
    map_zero' := ((I.restrictScalars R).subtype.comp f.toLinearMap +
      (IsScalarTower.toAlgHom R A B).toLinearMap).map_zero }

-- simp normal form is `liftOfDerivationToSquareZero_mk_apply'`
/-
**liftOfDerivationToSquareZero_mk_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：liftOfDerivationToSquareZero_mk_apply [IsScalarTower R A B] (d : Derivatio
n R A I) (x : A) : Ideal.Quotient.mk I (liftOfDerivationToSquareZero I hI d x) =
 algebraMap A (B ⧸ I) x
参数：d : Derivation R A I；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `liftOfDerivationToSquareZero_apply`：∀ {R : Type u} {A : Type v} {B : Typ
e w} [inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : CommRing B]   [
inst_3 : Algebra R A] [i…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ideal.Quotient.mk_algebraMap`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : C
ommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_
3 : I.IsTwoSided] …
-/
theorem liftOfDerivationToSquareZero_mk_apply [IsScalarTower R A B] (d : Derivation R A I) (x : A) :
    Ideal.Quotient.mk I (liftOfDerivationToSquareZero I hI d x) = algebraMap A (B ⧸ I) x := by
  rw [liftOfDerivationToSquareZero_apply, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop,
    zero_add, Ideal.Quotient.mk_algebraMap]

@[simp]
/-
**liftOfDerivationToSquareZero_mk_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：liftOfDerivationToSquareZero_mk_apply' (d : Derivation R A I) (x : A) : (I
deal.Quotient.mk I) (d x) + (algebraMap A (B ⧸ I)) x = algebraMap A (B ⧸ I) x
参数：d : Derivation R A I；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftOfDerivationToSquareZero_mk_apply' (d : Derivation R A I) (x : A) :
    (Ideal.Quotient.mk I) (d x) + (algebraMap A (B ⧸ I)) x = algebraMap A (B ⧸ I) x := by
  simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop, zero_add]

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`,
there is a 1-1 correspondence between `R`-derivations from `A` to `I` and
lifts `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps!]
/-
**derivationToSquareZeroEquivLift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：derivationToSquareZeroEquivLift [IsScalarTower R A B] : Derivation R A I ≃
 { f : A ->ₐ[R] B // (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R 
A (B ⧸ I) }
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`,
there is a 1-1 correspondence between `R`-derivations from `A` to `I` and
lifts `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`.
-/
def derivationToSquareZeroEquivLift [IsScalarTower R A B] : Derivation R A I ≃
    { f : A →ₐ[R] B // (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I) } := by
  refine ⟨fun d => ⟨liftOfDerivationToSquareZero I hI d, ?_⟩, fun f =>
    (derivationToSquareZeroOfLift I hI f.1 f.2 :), ?_, ?_⟩
  · ext x; exact liftOfDerivationToSquareZero_mk_apply I hI d x
  · intro d; ext x; exact add_sub_cancel_right (d x : B) (algebraMap A B x)
  · rintro ⟨f, hf⟩; ext x; exact sub_add_cancel (f x) (algebraMap A B x)

end ToSquareZero

