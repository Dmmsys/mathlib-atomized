/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Extending an `ℝ`-linear functional to a `𝕜`-linear functional

In this file we provide a way to extend a (optionally, continuous) `ℝ`-linear map to a (continuous)
`𝕜`-linear map in a way that bounds the norm by the norm of the original map, when `𝕜` is either
`ℝ` (the extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `RCLike 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `im (fc x) = -re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

In `Mathlib/Analysis/Normed/Module/RCLike/Extend.lean` we show that this extension is isometric.
This is separate to avoid importing material about the operator norm into files about more
elementary properties, like locally convex spaces.

## Main definitions

* `LinearMap.extendRCLike`
* `ContinuousLinearMap.extendRCLike`

-/

@[expose] public section

open RCLike

open ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
namespace Module.Dual

variable [AddCommGroup F] [Module ℝ F] [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F]

/-- Extend `fr : Dual ℝ F` to `Dual 𝕜 F` in a way that will also be continuous and have its norm
(as a continuous linear map) equal to `‖fr‖` when `fr` is itself continuous on a normed space. -/
/-
**Module.Dual.extendRCLike** 是 Mathlib 中的一个定义，位于命名空间 `Module.Dual`。
形式化陈述：extendRCLike (fr : Dual Real F) : Dual 𝕜 F
参数：fr : Dual Real F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend `fr : Dual ℝ F` to `Dual 𝕜 F` in a way that will also be continuous and h
ave its norm
(as a continuous linear map) equal to `‖fr‖` when `fr` is itself continuous on a
 normed space.
-/
noncomputable def extendRCLike (fr : Dual ℝ F) : Dual 𝕜 F :=
  letI fc : F → 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add (x y) : fc (x + y) = fc x + fc y := by
    simp only [fc, smul_add, map_add, mul_add]
    abel
  have A (c : ℝ) (x : F) : (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) := by simp
  have smul_ℝ (c : ℝ) (x : F) : fc ((c : 𝕜) • x) = (c : 𝕜) * fc x := by
    simp only [fc, A, smul_comm I, mul_comm I, mul_sub, mul_assoc]
  have smul_I (x : F) : fc ((I : 𝕜) • x) = (I : 𝕜) * fc x := by
    obtain (h | h) := @I_mul_I_ax 𝕜 _
    · simp [fc, h]
    · simp [fc, mul_sub, ← mul_assoc, smul_smul, h, add_comm]
  have smul_𝕜 (c : 𝕜) (x : F) : fc (c • x) = c • fc x := by
    rw [← re_add_im c]
    simp only [add_smul, ← smul_smul, add, smul_ℝ, smul_I, ← mul_assoc, smul_eq_mul, add_mul]
  { toFun := fc
    map_add' := add
    map_smul' := smul_𝕜 }
/-
**Module.Dual.extendRCLike_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`。
形式化陈述：extendRCLike_apply (fr : Dual Real F) (x : F) : fr.extendRCLike x = (fr x 
: 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜)
参数：fr : Dual Real F；x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extendRCLike_apply (fr : Dual ℝ F) (x : F) :
    fr.extendRCLike x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

@[simp]
/-
**Module.Dual.re_extendRCLike_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`。
形式化陈述：re_extendRCLike_apply (fr : Dual Real F) (x : F) : re (fr.extendRCLike x :
 𝕜) = fr x
参数：fr : Dual Real F；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_extendRCLike_apply (fr : Dual ℝ F) (x : F) : re (fr.extendRCLike x : 𝕜) = fr x := by
  simp only [extendRCLike_apply, map_sub, zero_mul, mul_zero, sub_zero, rclike_simps]

@[simp]
/-
**Module.Dual.im_extendRCLike_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module.Dual`。
形式化陈述：im_extendRCLike_apply (g : Dual Real F) (x : F) : im ((extendRCLike g) x :
 𝕜) = - g ((I : 𝕜) • x)
参数：g : Dual Real F；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.I_eq_zero_or_im_I_eq_one`：I_eq_zero_or_im_I_eq_one : (I : K) = 0 
∨ im (I : K) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
-/
lemma im_extendRCLike_apply (g : Dual ℝ F) (x : F) :
    im ((extendRCLike g) x : 𝕜) = - g ((I : 𝕜) • x) := by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]
/-
**Module.Dual.norm_extendRCLike_apply_sq** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`
。
形式化陈述：norm_extendRCLike_apply_sq (fr : Dual Real F) (x : F) : ‖(fr.extendRCLike 
x : 𝕜)‖ ^ 2 = fr (conj (fr.extendRCLike x : 𝕜) • x)
参数：fr : Dual Real F；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.conj_mul`：conj_mul (z : K) : conj z * z = ‖z‖ ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K
) = (r : K) ^ n
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Dual.re_extendRCLike_apply`：re_extendRCLike_apply (fr : Dual Real
 F) (x : F) : re (fr.extendRCLike x : 𝕜) = fr x
-/
theorem norm_extendRCLike_apply_sq (fr : Dual ℝ F) (x : F) :
    ‖(fr.extendRCLike x : 𝕜)‖ ^ 2 = fr (conj (fr.extendRCLike x : 𝕜) • x) := calc
  ‖(fr.extendRCLike x : 𝕜)‖ ^ 2 = re (conj (fr.extendRCLike x) * fr.extendRCLike x : 𝕜) := by
    rw [RCLike.conj_mul, ← ofReal_pow, ofReal_re]
  _ = fr (conj (fr.extendRCLike x : 𝕜) • x) := by
    rw [← smul_eq_mul, ← map_smul, re_extendRCLike_apply]

/-- The extension `Module.Dual.extendRCLike` as a linear equivalence between the algebraic duals. -/
@[simps -isSimp apply symm_apply]
/-
**Module.Dual.extendRCLike** 是 Mathlib 中的一个定义，位于命名空间 `Module.Dual`。
形式化陈述：extendRCLike (fr : Dual Real F) : Dual 𝕜 F
参数：fr : Dual Real F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension `Module.Dual.extendRCLike` as a linear equivalence between the alg
ebraic duals.
-/
noncomputable def extendRCLikeₗ : Dual ℝ F ≃ₗ[ℝ] Dual 𝕜 F where
  toFun := extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reLm.comp (f.restrictScalars ℝ)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

end Module.Dual

namespace StrongDual

variable [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
variable [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- Extend `fr : StrongDual ℝ F` to `StrongDual 𝕜 F`.

Norm properties of this extension can be found in
`Mathlib/Analysis/Normed/Module/RCLike/Extend.lean`. -/
/-
**StrongDual.extendRCLike** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：extendRCLike (fr : StrongDual Real F) : StrongDual 𝕜 F where __
参数：fr : StrongDual Real F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend `fr : StrongDual ℝ F` to `StrongDual 𝕜 F`.

Norm properties of this extension can be found in
`Mathlib/Analysis/Normed/Module/RCLike/Extend.lean`.
-/
noncomputable def extendRCLike (fr : StrongDual ℝ F) : StrongDual 𝕜 F where
  __ := Module.Dual.extendRCLike fr.toLinearMap
  cont := show Continuous fun x ↦ (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) by fun_prop
/-
**StrongDual.extendRCLike_apply** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：extendRCLike_apply (fr : StrongDual Real F) (x : F) : fr.extendRCLike x = 
(fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜)
参数：fr : StrongDual Real F；x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extendRCLike_apply (fr : StrongDual ℝ F) (x : F) :
    fr.extendRCLike x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

@[simp]
/-
**StrongDual.re_extendRCLike_apply** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
形式化陈述：re_extendRCLike_apply (g : StrongDual Real F) (x : F) : re ((extendRCLike 
g) x : 𝕜) = g x
参数：g : StrongDual Real F；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma re_extendRCLike_apply (g : StrongDual ℝ F) (x : F) :
    re ((extendRCLike g) x : 𝕜) = g x := by
  simp [extendRCLike_apply]

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.re_extendTo𝕜ₗ := re_extendRCLike_apply

@[simp]
/-
**StrongDual.im_extendRCLike_apply** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
形式化陈述：im_extendRCLike_apply (g : StrongDual Real F) (x : F) : im ((extendRCLike 
g) x : 𝕜) = - g ((I : 𝕜) • x)
参数：g : StrongDual Real F；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.I_eq_zero_or_im_I_eq_one`：I_eq_zero_or_im_I_eq_one : (I : K) = 0 
∨ im (I : K) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
-/
lemma im_extendRCLike_apply (g : StrongDual ℝ F) (x : F) :
    im ((extendRCLike g) x : 𝕜) = - g ((I : 𝕜) • x) := by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]

/-- The extension `StrongDual.extendRCLike` as a linear equivalence between the algebraic duals.

When `F` is a normed space, this can be upgraded to an *isometric* linear equivalence, see
`StrongDual.extendRCLikeₗᵢ`. -/
@[simps -isSimp apply symm_apply]
/-
**StrongDual.extendRCLike** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：extendRCLike (fr : StrongDual Real F) : StrongDual 𝕜 F where __
参数：fr : StrongDual Real F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension `StrongDual.extendRCLike` as a linear equivalence between the alge
braic duals.

When `F` is a normed space, this can be upgraded to an *isometric* linear equiva
lence, see
`StrongDual.extendRCLikeₗᵢ`.
-/
noncomputable def extendRCLikeₗ : StrongDual ℝ F ≃ₗ[ℝ] StrongDual 𝕜 F where
  toFun := StrongDual.extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reCLM.comp (f.restrictScalars ℝ)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp [extendRCLike_apply]
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.extendTo𝕜ₗ := extendRCLikeₗ

end StrongDual

namespace LinearMap

open Module.Dual

@[deprecated (since := "2026-02-24")] alias extendTo𝕜' := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜'_apply := extendRCLike_apply
@[deprecated (since := "2026-02-24")] alias extendTo𝕜'_apply_re := re_extendRCLike_apply
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜'_apply_sq := norm_extendRCLike_apply_sq
@[deprecated (since := "2026-02-24")] alias extendTo𝕜 := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜_apply := extendRCLike_apply

end LinearMap

namespace ContinuousLinearMap

open StrongDual

@[deprecated (since := "2026-02-24")] alias extendTo𝕜' := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜'_apply := extendRCLike_apply
@[deprecated (since := "2026-02-24")] alias extendTo𝕜 := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜_apply := extendRCLike_apply

end ContinuousLinearMap

