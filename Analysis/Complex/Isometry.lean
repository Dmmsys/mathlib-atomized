/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.SuppressCompilation

/-!
# Isometries of the Complex Plane

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`

The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `LinearIsometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/

@[expose] public section


noncomputable section
suppress_compilation -- needed to avoid a panic!

open Complex

open CharZero

open ComplexConjugate

local notation "|" x "|" => Complex.abs x

set_option backward.isDefEq.respectTransparency.types false in
/-- An element of the unit circle defines a `LinearIsometryEquiv` from `ℂ` to itself, by
rotation. -/
/-
**rotation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rotation : Circle ->* Complex ≃ₗᵢ[Real] Complex where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the unit circle defines a `LinearIsometryEquiv` from `ℂ` to itself
, by
rotation.
-/
def rotation : Circle →* ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun a :=
    { DistribMulAction.toLinearEquiv ℝ ℂ a with
      norm_map' x := show ‖a * x‖ = ‖x‖ by
        rw [norm_mul, Circle.norm_coe, one_mul] }
  map_one' := LinearIsometryEquiv.ext <| by simp
  map_mul' a b := LinearIsometryEquiv.ext <| mul_smul a b

@[simp]
/-
**rotation_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rotation_apply (a : Circle) (z : Complex) : rotation a z = a * z
参数：a : Circle；z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rotation_apply (a : Circle) (z : ℂ) : rotation a z = a * z :=
  rfl

@[simp]
/-
**rotation_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rotation_symm (a : Circle) : (rotation a).symm = rotation a⁻¹
参数：a : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
-/
theorem rotation_symm (a : Circle) : (rotation a).symm = rotation a⁻¹ :=
  LinearIsometryEquiv.ext fun _ => rfl

@[simp]
/-
**rotation_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rotation_trans (a b : Circle) : (rotation a).trans (rotation b) = rotation
 (b * a)
参数：a b : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rotation_trans (a b : Circle) : (rotation a).trans (rotation b) = rotation (b * a) := by
  ext1
  simp
/-
**rotation_ne_conjLIE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rotation_ne_conjLIE (a : Circle) : rotation a != conjLIE
参数：a : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.congr_fun`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Typ
e u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+*
 R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharZero.eq_neg_self_iff`：∀ {R : Type u_2} [inst : NonAssocRing R] [NoZe
roDivisors R] [CharZero R] {a : R}, a = -a ↔ a = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
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
· 使用定理 `rotation_apply`：rotation_apply (a : Circle) (z : Complex) : rotation a z
 = a * z
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
-/
theorem rotation_ne_conjLIE (a : Circle) : rotation a ≠ conjLIE := by
  intro h
  have h1 : rotation a 1 = conj 1 := LinearIsometryEquiv.congr_fun h 1
  have hI : rotation a I = conj I := LinearIsometryEquiv.congr_fun h I
  rw [rotation_apply, map_one, mul_one] at h1
  rw [rotation_apply, conj_I, ← neg_one_mul, mul_left_inj' I_ne_zero, h1, eq_neg_self_iff] at hI
  exact one_ne_zero hI

/-- Takes an element of `ℂ ≃ₗᵢ[ℝ] ℂ` and checks if it is a rotation, returns an element of the
unit circle. -/
@[simps]
/-
**rotationOf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rotationOf (e : Complex ≃ₗᵢ[Real] Complex) : Circle
参数：e : Complex ≃ₗᵢ[Real] Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Takes an element of `ℂ ≃ₗᵢ[ℝ] ℂ` and checks if it is a rotation, returns an elem
ent of the
unit circle.
-/
def rotationOf (e : ℂ ≃ₗᵢ[ℝ] ℂ) : Circle :=
  ⟨e 1 / ‖e 1‖, by simp [Submonoid.unitSphere]⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**rotationOf_rotation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rotationOf_rotation (a : Circle) : rotationOf (rotation a) = a
参数：a : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rotationOf_coe`：∀ (e : ℂ ≃ₗᵢ[ℝ] ℂ), ↑(rotationOf e) = e 1 / ↑‖e 1‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_eq_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ} (x : ↑(Metric.sphere 0 r)), ‖↑x‖ = r
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rotationOf_rotation (a : Circle) : rotationOf (rotation a) = a :=
  Subtype.ext <| by simp
/-
**rotation_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rotation_injective : Function.Injective rotation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `rotationOf_rotation`：rotationOf_rotation (a : Circle) : rotationOf (rota
tion a) = a
-/
theorem rotation_injective : Function.Injective rotation :=
  Function.LeftInverse.injective rotationOf_rotation
/-
**LinearIsometry.re_apply_eq_re_of_add_conj_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.re_apply_eq_re_of_add_conj_eq (f : Complex ->ₗᵢ[Real] Compl
ex) (h₃ : forall z, z + conj z = f z + conj (f z)) (z : Complex) : (f z).re = z.
re
参数：f : Complex ->ₗᵢ[Real] Complex；h₃ : forall z, z + conj z = f z + conj (f z)；z
 : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem LinearIsometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ)
    (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re := by
  simpa [Complex.ext_iff, add_re, add_im, conj_re, conj_im, ← two_mul,
    show (2 : ℝ) ≠ 0 by simp] using (h₃ z).symm
/-
**LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : Complex ->ₗᵢ[R
eal] Complex} (h₂ : forall z, (f z).re = z.re) (z : Complex) : (f z).im = z.im ∨
 (f z).im = -z.im
参数：h₂ : forall z, (f z).re = z.re；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_self_eq_mul_self_iff`：mul_self_eq_mul_self_iff [NonUnitalNonAssocCom
mRing R] [NoZeroDivisors R] {a b : R} : a * a = b * b ↔ a = b ∨ a = -b
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Complex.normSq_apply`：normSq_apply (z : Complex) : normSq z = z.re * z.r
e + z.im * z.im
· 使用定理 `Real.sqrt_inj`：sqrt_inj (hx : 0 <= x) (hy : 0 <= y) : √x = √y ↔ x = y
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
-/
theorem LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ}
    (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) : (f z).im = z.im ∨ (f z).im = -z.im := by
  have h₁ := f.norm_map z
  simp only [norm_def] at h₁
  rwa [Real.sqrt_inj (normSq_nonneg _) (normSq_nonneg _), normSq_apply (f z), normSq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁
/-
**LinearIsometry.im_apply_eq_im** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.im_apply_eq_im {f : Complex ->ₗᵢ[Real] Complex} (h : f 1 = 
1) (z : Complex) : z + conj z = f z + conj (f z)
参数：h : f 1 = 1；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.add_conj`：add_conj (z : Complex) : z + conj z = (2 * z.re : Real
)
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 37 条，此处仅展示前 30 条）
-/
theorem LinearIsometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) :
    z + conj z = f z + conj (f z) := by
  have hsq : ‖f z - 1‖ ^ 2 = ‖z - 1‖ ^ 2 := by simpa [h] using f.norm_map (z - 1)
  simp_rw [← normSq_eq_norm_sq, Complex.normSq_sub] at hsq
  simpa [normSq_eq_norm_sq, Complex.add_conj, LinearIsometry.norm_map] using hsq.symm
/-
**LinearIsometry.re_apply_eq_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.re_apply_eq_re {f : Complex ->ₗᵢ[Real] Complex} (h : f 1 = 
1) (z : Complex) : (f z).re = z.re
参数：h : f 1 = 1；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.re_apply_eq_re_of_add_conj_eq`：LinearIsometry.re_apply_eq
_re_of_add_conj_eq (f : Complex ->ₗᵢ[Real] Complex) (h₃ : forall z, z + conj z =
 f z + conj (f z)) (z : Complex) :…
· 使用定理 `LinearIsometry.im_apply_eq_im`：LinearIsometry.im_apply_eq_im {f : Comple
x ->ₗᵢ[Real] Complex} (h : f 1 = 1) (z : Complex) : z + conj z = f z + conj (f z
)
-/
theorem LinearIsometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re := by
  apply LinearIsometry.re_apply_eq_re_of_add_conj_eq
  apply LinearIsometry.im_apply_eq_im h
/-
**linear_isometry_complex_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linear_isometry_complex_aux {f : Complex ≃ₗᵢ[Real] Complex} (h : f 1 = 1) 
: f = LinearIsometryEquiv.refl Real Complex ∨ f = conjLIE
参数：h : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.I_re`：I_re : I.re = 0
· 使用定理 `LinearIsometry.re_apply_eq_re`：LinearIsometry.re_apply_eq_re {f : Comple
x ->ₗᵢ[Real] Complex} (h : f 1 = 1) (z : Complex) : (f z).re = z.re
· 使用定理 `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re`：LinearIsometry.i
m_apply_eq_im_or_neg_of_re_apply_eq_re {f : Complex ->ₗᵢ[Real] Complex} (h₂ : fo
rall z, (f z).re = z.re) (z : Complex) : (f …
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LinearIsometryEquiv.toLinearEquiv_injective`：∀ {R : Type u_1} {R₂ : Type
 u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂] 
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `Module.Basis.ext'`：ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = 
f₂ (b i)) : f₁ = f₂
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Complex.coe_basisOneI`：coe_basisOneI : ⇑basisOneI = ![1, I]
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
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
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
-/
theorem linear_isometry_complex_aux {f : ℂ ≃ₗᵢ[ℝ] ℂ} (h : f 1 = 1) :
    f = LinearIsometryEquiv.refl ℝ ℂ ∨ f = conjLIE := by
  have h0 : f I = I ∨ f I = -I := by
    simp only [Complex.ext_iff, ← and_or_left, neg_re, I_re, neg_im, neg_zero]
    constructor
    · rw [← I_re]
      exact @LinearIsometry.re_apply_eq_re f.toLinearIsometry h I
    · apply @LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.toLinearIsometry
      intro z
      rw [@LinearIsometry.re_apply_eq_re f.toLinearIsometry h]
  refine h0.imp (fun h' : f I = I => ?_) fun h' : f I = -I => ?_ <;>
    · apply LinearIsometryEquiv.toLinearEquiv_injective
      apply Complex.basisOneI.ext'
      intro i
      fin_cases i <;> simp [h, h']

set_option backward.isDefEq.respectTransparency false in
/-
**linear_isometry_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linear_isometry_complex (f : Complex ≃ₗᵢ[Real] Complex) : exists a : Circl
e, f = rotation a ∨ f = conjLIE.trans (rotation a)
参数：f : Complex ≃ₗᵢ[Real] Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIsometryEquiv.trans.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} {E : Type u_5} {E₂ : Type u_6} {E₃ : Type u_7} [inst : Semiring R
]   [inst_1 : Semiring R₂]…
· 使用定理 `rotation_symm`：rotation_symm (a : Circle) : (rotation a).symm = rotation
 a⁻¹
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `rotation_apply`：rotation_apply (a : Circle) (z : Complex) : rotation a z
 = a * z
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LinearIsometryEquiv.mul_refl`：mul_refl (e : E ≃ₗᵢ[R] E) : e * refl _ _ =
 e
· 使用定理 `eq_mul_of_inv_mul_eq`：eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c
· 使用定理 `linear_isometry_complex_aux`：linear_isometry_complex_aux {f : Complex ≃ₗ
ᵢ[Real] Complex} (h : f 1 = 1) : f = LinearIsometryEquiv.refl Real Complex ∨ f =
 conjLIE
-/
theorem linear_isometry_complex (f : ℂ ≃ₗᵢ[ℝ] ℂ) :
    ∃ a : Circle, f = rotation a ∨ f = conjLIE.trans (rotation a) := by
  let a : Circle := ⟨f 1, by simp [Submonoid.unitSphere, f.norm_map]⟩
  use a
  have : (f.trans (rotation a).symm) 1 = 1 := by simpa [a] using rotation_apply a⁻¹ (f 1)
  refine (linear_isometry_complex_aux this).imp (fun h₁ => ?_) fun h₂ => ?_
  · simpa using eq_mul_of_inv_mul_eq h₁
  · exact eq_mul_of_inv_mul_eq h₂

/-- The matrix representation of `rotation a` is equal to the conformal matrix
`!![re a, -im a; im a, re a]`. -/
/-
**toMatrix_rotation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMatrix_rotation (a : Circle) : LinearMap.toMatrix basisOneI basisOneI (r
otation a).toLinearEquiv = Matrix.planeConformalMatrix (re a) (im a) (by simp [p
ow_two, ← normSq_apply])
参数：a : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Complex.coe_basisOneI`：coe_basisOneI : ⇑basisOneI = ![1, I]
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `Matrix.val_planeConformalMatrix`：∀ {R : Type u_1} [inst : Field R] (a b 
: R) (hab : a ^ 2 + b ^ 2 ≠ 0),   ↑(Matrix.planeConformalMatrix a b hab) = !![a,
 -b; b, a]
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.empty_val'`：empty_val' {n' : Type*} (j : n') : (fun i => (![] : F
in 0 -> n' -> α) i j) = ![]
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The matrix representation of `rotation a` is equal to the conformal matrix
`!![re a, -im a; im a, re a]`.
-/
theorem toMatrix_rotation (a : Circle) :
    LinearMap.toMatrix basisOneI basisOneI (rotation a).toLinearEquiv =
      Matrix.planeConformalMatrix (re a) (im a) (by simp [pow_two, ← normSq_apply]) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, coe_basisOneI, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, rotation_apply, coe_basisOneI_repr, mul_re, mul_im,
    Matrix.val_planeConformalMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j <;> simp

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
/-
**det_rotation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：det_rotation (a : Circle) : LinearMap.det ((rotation a).toLinearEquiv : Co
mplex ->ₗ[Real] Complex) = 1
参数：a : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `toMatrix_rotation`：toMatrix_rotation (a : Circle) : LinearMap.toMatrix b
asisOneI basisOneI (rotation a).toLinearEquiv = Matrix.planeConformalMatrix (re 
a) (im …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.val_planeConformalMatrix`：∀ {R : Type u_1} [inst : Field R] (a b 
: R) (hab : a ^ 2 + b ^ 2 ≠ 0),   ↑(Matrix.planeConformalMatrix a b hab) = !![a,
 -b; b, a]
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Circle.normSq_coe`：∀ (z : Circle), Complex.normSq ↑z = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The determinant of `rotation` (as a linear map) is equal to `1`.
-/
theorem det_rotation (a : Circle) : LinearMap.det ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [← LinearMap.det_toMatrix basisOneI, toMatrix_rotation, Matrix.det_fin_two]
  simp [← normSq_apply]

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
/-
**linearEquiv_det_rotation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearEquiv_det_rotation (a : Circle) : LinearEquiv.det (rotation a).toLin
earEquiv = 1
参数：a : Circle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `LinearEquiv.coe_det`：coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = Li
nearMap.det (f : M ->ₗ[R] M)
· 使用定理 `det_rotation`：det_rotation (a : Circle) : LinearMap.det ((rotation a).to
LinearEquiv : Complex ->ₗ[Real] Complex) = 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1

--- 原说明 ---
The determinant of `rotation` (as a linear equiv) is equal to `1`.
-/
theorem linearEquiv_det_rotation (a : Circle) : LinearEquiv.det (rotation a).toLinearEquiv = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det, det_rotation, Units.val_one]
