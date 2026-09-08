/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Linear maps on inner product spaces

This file studies linear maps on inner product spaces.

## Main results

- We define `innerSL` as the inner product bundled as a continuous sesquilinear map
- We prove a general polarization identity for linear maps (`inner_map_polarization`)
- We show that a linear map preserving the inner product is an isometry
  (`LinearMap.isometryOfInner`) and conversely an isometry preserves the inner product
  (`LinearIsometry.inner_map_map`).

## Tags

inner product space, Hilbert space, norm

-/

@[expose] public section

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section Complex_Seminormed

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option backward.isDefEq.respectTransparency false in
/-- A complex polarization identity, with a linear map. -/
/-
**inner_map_polarization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_map_polarization (T : V ->ₗ[Complex] V) (x y : V) : ⟪T y, x⟫_Complex
 = (⟪T (x + y), x + y⟫_Complex - ⟪T (x - y), x - y⟫_Complex + Complex.I * ⟪T (x 
+ Complex.I • y), x + Complex.I • y⟫_Complex - Complex.I * ⟪T (x - Complex.I • y
), x - Complex.I • y⟫_Complex) / 4
参数：T : V ->ₗ[Complex] V；x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
A complex polarization identity, with a linear map.
-/
theorem inner_map_polarization (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T y, x⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ +
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

set_option backward.isDefEq.respectTransparency false in
/-
**inner_map_polarization'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_map_polarization' (T : V ->ₗ[Complex] V) (x y : V) : ⟪T x, y⟫_Comple
x = (⟪T (x + y), x + y⟫_Complex - ⟪T (x - y), x - y⟫_Complex - Complex.I * ⟪T (x
 + Complex.I • y), x + Complex.I • y⟫_Complex + Complex.I * ⟪T (x - Complex.I • 
y), x - Complex.I • y⟫_Complex) / 4
参数：T : V ->ₗ[Complex] V；x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 77 条，此处仅展示前 30 条）
-/
theorem inner_map_polarization' (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T x, y⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ -
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ +
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

end Complex_Seminormed

section Complex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A linear map `T` is zero, if and only if the identity `⟪T x, x⟫_ℂ = 0` holds for all `x`.
-/
/-
**inner_map_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_map_self_eq_zero (T : V ->ₗ[Complex] V) : (forall x : V, ⟪T x, x⟫_Co
mplex = 0) ↔ T = 0
参数：T : V ->ₗ[Complex] V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `inner_map_polarization`：inner_map_polarization (T : V ->ₗ[Complex] V) (x
 y : V) : ⟪T y, x⟫_Complex = (⟪T (x + y), x + y⟫_Complex - ⟪T (x - y), x - y⟫_Co
mplex + Comp…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0

--- 原说明 ---
A linear map `T` is zero, if and only if the identity `⟪T x, x⟫_ℂ = 0` holds for
 all `x`.
-/
theorem inner_map_self_eq_zero (T : V →ₗ[ℂ] V) : (∀ x : V, ⟪T x, x⟫_ℂ = 0) ↔ T = 0 := by
  constructor
  · intro hT
    ext x
    rw [LinearMap.zero_apply, ← @inner_self_eq_zero ℂ V, inner_map_polarization]
    simp only [hT]
    simp
  · rintro rfl x
    simp only [LinearMap.zero_apply, inner_zero_left]

/--
Two linear maps `S` and `T` are equal, if and only if the identity `⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ` holds
for all `x`.
-/
/-
**ext_inner_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_inner_map (S T : V ->ₗ[Complex] V) : (forall x : V, ⟪S x, x⟫_Complex =
 ⟪T x, x⟫_Complex) ↔ S = T
参数：S T : V ->ₗ[Complex] V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `inner_map_self_eq_zero`：inner_map_self_eq_zero (T : V ->ₗ[Complex] V) : 
(forall x : V, ⟪T x, x⟫_Complex = 0) ↔ T = 0
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `LinearMap.sub_apply`：sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) 
x = f x - g x
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two linear maps `S` and `T` are equal, if and only if the identity `⟪S x, x⟫_ℂ =
 ⟪T x, x⟫_ℂ` holds
for all `x`.
-/
theorem ext_inner_map (S T : V →ₗ[ℂ] V) : (∀ x : V, ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ) ↔ S = T := by
  rw [← sub_eq_zero, ← inner_map_self_eq_zero]
  refine forall_congr' fun x => ?_
  rw [LinearMap.sub_apply, inner_sub_left, sub_eq_zero]

end Complex

section

variable {ι : Type*} {ι' : Type*} {ι'' : Type*}
variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
variable {E'' : Type*} [SeminormedAddCommGroup E''] [InnerProductSpace 𝕜 E'']

set_option backward.isDefEq.respectTransparency false in
/-- A linear isometry preserves the inner product. -/
@[simp]
/-
**LinearIsometry.inner_map_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪
x, y⟫
参数：f : E ->ₗᵢ[𝕜] E'；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_eq_sum_norm_sq_div_four`：inner_eq_sum_norm_sq_div_four (x y : E) :
 ⟪x, y⟫ = ((‖x + y‖ : 𝕜) ^ 2 - (‖x - y‖ : 𝕜) ^ 2 + ((‖x - IK • y‖ : 𝕜) ^ 2 - (‖x
 + IK • y‖ : 𝕜) ^ 2…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A linear isometry preserves the inner product.
-/
theorem LinearIsometry.inner_map_map (f : E →ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ := by
  simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]

/-- A linear isometric equivalence preserves the inner product. -/
@[simp]
/-
**LinearIsometryEquiv.inner_map_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometryEquiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫
 = ⟪x, y⟫
参数：f : E ≃ₗᵢ[𝕜] E'；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫

--- 原说明 ---
A linear isometric equivalence preserves the inner product.
-/
theorem LinearIsometryEquiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
  f.toLinearIsometry.inner_map_map x y

/-- The adjoint of a linear isometric equivalence is its inverse. -/
/-
**LinearIsometryEquiv.inner_map_eq_flip** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometryEquiv.inner_map_eq_flip (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E') :
 ⟪f x, y⟫_𝕜 = ⟪x, f.symm y⟫_𝕜
参数：f : E ≃ₗᵢ[𝕜] E'；x : E；y : E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫

--- 原说明 ---
The adjoint of a linear isometric equivalence is its inverse.
-/
theorem LinearIsometryEquiv.inner_map_eq_flip (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E') :
    ⟪f x, y⟫_𝕜 = ⟪x, f.symm y⟫_𝕜 := by
  conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map]

/-- A linear map that preserves the inner product is a linear isometry. -/
/-
**LinearMap.isometryOfInner** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.isometryOfInner (f : E ->ₗ[𝕜] E') (h : forall x y, ⟪f x, f y⟫ = 
⟪x, y⟫) : E ->ₗᵢ[𝕜] E'
参数：f : E ->ₗ[𝕜] E'；h : forall x y, ⟪f x, f y⟫ = ⟪x, y⟫。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map that preserves the inner product is a linear isometry.
-/
def LinearMap.isometryOfInner (f : E →ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[𝕜] E' :=
  ⟨f, fun x => by simp only [@norm_eq_sqrt_re_inner 𝕜, h]⟩

@[simp]
/-
**LinearMap.coe_isometryOfInner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.coe_isometryOfInner (f : E ->ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner 
h) = f
参数：f : E ->ₗ[𝕜] E'；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.coe_isometryOfInner (f : E →ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
/-
**LinearMap.isometryOfInner_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.isometryOfInner_toLinearMap (f : E ->ₗ[𝕜] E') (h) : (f.isometryO
fInner h).toLinearMap = f
参数：f : E ->ₗ[𝕜] E'；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.isometryOfInner_toLinearMap (f : E →ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearMap = f :=
  rfl

/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
/-
**LinearEquiv.isometryOfInner** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E') (h : forall x y, ⟪f x, f y⟫ =
 ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E'
参数：f : E ≃ₗ[𝕜] E'；h : forall x y, ⟪f x, f y⟫ = ⟪x, y⟫。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence that preserves the inner product is a linear isometric equi
valence.
-/
def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E' :=
  ⟨f, ((f : E →ₗ[𝕜] E').isometryOfInner h).norm_map⟩

@[simp]
/-
**LinearEquiv.coe_isometryOfInner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.coe_isometryOfInner (f : E ≃ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner
 h) = f
参数：f : E ≃ₗ[𝕜] E'；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearEquiv.coe_isometryOfInner (f : E ≃ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
/-
**LinearEquiv.isometryOfInner_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isometryOfInner_toLinearEquiv (f : E ≃ₗ[𝕜] E') (h) : (f.isomet
ryOfInner h).toLinearEquiv = f
参数：f : E ≃ₗ[𝕜] E'；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearEquiv.isometryOfInner_toLinearEquiv (f : E ≃ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearEquiv = f :=
  rfl

/-- A linear map is an isometry if and it preserves the inner product. -/
/-
**LinearMap.norm_map_iff_inner_map_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.norm_map_iff_inner_map_map {F : Type*} [FunLike F E E'] [LinearM
apClass F 𝕜 E E'] (f : F) : (forall x, ‖f x‖ = ‖x‖) ↔ (forall x y, ⟪f x, f y⟫_𝕜 
= ⟪x, y⟫_𝕜)
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…

--- 原说明 ---
A linear map is an isometry if and it preserves the inner product.
-/
theorem LinearMap.norm_map_iff_inner_map_map {F : Type*} [FunLike F E E'] [LinearMapClass F 𝕜 E E']
    (f : F) : (∀ x, ‖f x‖ = ‖x‖) ↔ (∀ x y, ⟪f x, f y⟫_𝕜 = ⟪x, y⟫_𝕜) :=
  ⟨({ toLinearMap := LinearMapClass.linearMap f, norm_map' := · : E →ₗᵢ[𝕜] E' }.inner_map_map),
    (LinearMapClass.linearMap f |>.isometryOfInner · |>.norm_map)⟩

end

variable (𝕜)

/-- The inner product as a continuous sesquilinear map. Note that `toDualMap` (resp. `toDual`)
in `InnerProductSpace.Dual` is a version of this given as a linear isometry (resp. linear
isometric equivalence). -/
/-
**innerSL** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：innerSL : E ->L⋆[𝕜] E ->L[𝕜] 𝕜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inner product as a continuous sesquilinear map. Note that `toDualMap` (resp.
 `toDual`)
in `InnerProductSpace.Dual` is a version of this given as a linear isometry (res
p. linear
isometric equivalence).
-/
def innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous₂ (innerₛₗ 𝕜) 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply_apply]

@[simp]
/-
**coe_innerSL_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_innerSL_apply (v : E) : ⇑(innerSL 𝕜 v) = fun w => ⟪v, w⟫
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
theorem coe_innerSL_apply (v : E) : ⇑(innerSL 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl
/-
**innerSL_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：innerSL_apply_apply (v w : E) : innerSL 𝕜 v w = ⟪v, w⟫
参数：v w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
theorem innerSL_apply_apply (v w : E) : innerSL 𝕜 v w = ⟪v, w⟫ :=
  rfl
/-
**ContinuousLinearMap.toLinearMap_innerSL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：∀ (𝕜 : Type u_1) {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (v : E), ↑((innerSL 𝕜) v) = (inne
rₛₗ 𝕜) v
参数：𝕜 : Type u_1；v : E；(innerSL 𝕜) v；innerₛₗ 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
@[simp] theorem ContinuousLinearMap.toLinearMap_innerSL_apply (v : E) :
    (innerSL 𝕜 v).toLinearMap = innerₛₗ 𝕜 v := rfl

/-- The inner product as a continuous sesquilinear map, with the two arguments flipped. -/
/-
**innerSLFlip** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：innerSLFlip : E ->L[𝕜] E ->L⋆[𝕜] 𝕜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inner product as a continuous sesquilinear map, with the two arguments flipp
ed.
-/
def innerSLFlip : E →L[𝕜] E →L⋆[𝕜] 𝕜 :=
  @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _
    (innerSL 𝕜)

@[simp]
/-
**innerSLFlip_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：innerSLFlip_apply_apply (x y : E) : innerSLFlip 𝕜 x y = ⟪y, x⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
theorem innerSLFlip_apply_apply (x y : E) : innerSLFlip 𝕜 x y = ⟪y, x⟫ :=
  rfl

variable (F) in
/-
**flip_innerSL_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (F : Type u_3) [inst : SeminormedAddCommGroup F] [inst_1 : InnerProductS
pace ℝ F], (innerSL ℝ).flip = innerSL ℝ
参数：F : Type u_3；innerSL ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `instCStarRingReal`：CStarRing ℝ
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
-/
@[simp] lemma flip_innerSL_real : (innerSL ℝ (E := F)).flip = innerSL ℝ (E := F) := by
  ext v w
  exact real_inner_comm _ _

variable {𝕜}

namespace ContinuousLinearMap

variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

-- Note: odd and expensive build behavior is explicitly turned off using `noncomputable`
/-- Given `f : E →L[𝕜] E'`, construct the continuous sesquilinear form `fun x y ↦ ⟪x, A y⟫`, given
as a continuous linear map. -/
/-
**ContinuousLinearMap.toSesqForm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：toSesqForm : (E ->L[𝕜] E') ->L[𝕜] E' ->L⋆[𝕜] E ->L[𝕜] 𝕜
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Given `f : E →L[𝕜] E'`, construct the continuous sesquilinear form `fun x y ↦ ⟪x
, A y⟫`, given
as a continuous linear map.
-/
noncomputable def toSesqForm : (E →L[𝕜] E') →L[𝕜] E' →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.flipₗᵢ' E E' 𝕜 (starRingEnd 𝕜) (RingHom.id 𝕜)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' →L⋆[𝕜] 𝕜) (RingHom.id 𝕜) (RingHom.id 𝕜) (innerSLFlip 𝕜)

@[simp]
/-
**ContinuousLinearMap.toSesqForm_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：toSesqForm_apply_coe (f : E ->L[𝕜] E') (x : E') : toSesqForm f x = (innerS
L 𝕜 x).comp f
参数：f : E ->L[𝕜] E'；x : E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem toSesqForm_apply_coe (f : E →L[𝕜] E') (x : E') : toSesqForm f x = (innerSL 𝕜 x).comp f :=
  rfl
/-
**ContinuousLinearMap.toSesqForm_apply_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：toSesqForm_apply_norm_le {f : E ->L[𝕜] E'} {v : E'} : ‖toSesqForm f v‖ <= 
‖f‖ * ‖v‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 33 条，此处仅展示前 30 条）
-/
theorem toSesqForm_apply_norm_le {f : E →L[𝕜] E'} {v : E'} : ‖toSesqForm f v‖ ≤ ‖f‖ * ‖v‖ := by
  refine opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have h₁ : ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
  have h₂ := @norm_inner_le_norm 𝕜 E' _ _ _ v (f x)
  calc
    ‖⟪v, f x⟫‖ ≤ ‖v‖ * ‖f x‖ := h₂
    _ ≤ ‖v‖ * (‖f‖ * ‖x‖) := by gcongr
    _ = ‖f‖ * ‖v‖ * ‖x‖ := by ring

end ContinuousLinearMap

variable (𝕜)

/-- `innerSL` is an isometry. Note that the associated `LinearIsometry` is defined in
`InnerProductSpace.Dual` as `toDualMap`. -/
@[simp]
/-
**innerSL_apply_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：innerSL_apply_norm (x : E) : ‖innerSL 𝕜 x‖ = ‖x‖
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_le_mul_iff_left₀`：mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflect
LE α] (a0 : 0 < a) : b * a <= c * a ↔ b <= c
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `RCLike.norm_ofReal`：norm_ofReal (r : Real) : ‖(r : K)‖ = |r|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
`innerSL` is an isometry. Note that the associated `LinearIsometry` is defined i
n
`InnerProductSpace.Dual` as `toDualMap`.
-/
theorem innerSL_apply_norm (x : E) : ‖innerSL 𝕜 x‖ = ‖x‖ := by
  refine
    le_antisymm ((innerSL 𝕜 x).opNorm_le_bound (norm_nonneg _) fun y => norm_inner_le_norm _ _) ?_
  rcases (norm_nonneg x).eq_or_lt' with (h | h)
  · simp [h]
  · refine (mul_le_mul_iff_left₀ h).mp ?_
    calc
      ‖x‖ * ‖x‖ = ‖(⟪x, x⟫ : 𝕜)‖ := by
        rw [← sq, inner_self_eq_norm_sq_to_K, norm_pow, norm_ofReal, abs_norm]
      _ ≤ ‖innerSL 𝕜 x‖ * ‖x‖ := (innerSL 𝕜 x).le_opNorm _
/-
**norm_innerSL_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_innerSL_le : ‖innerSL 𝕜 (E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `innerSL_apply_norm`：innerSL_apply_norm (x : E) : ‖innerSL 𝕜 x‖ = ‖x‖
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma norm_innerSL_le : ‖innerSL 𝕜 (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

end Norm_Seminormed

section RCLikeToReal

open scoped InnerProductSpace

variable {G : Type*}

/-- The inner product on an inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
/-
**inner_map_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_map_complex [SeminormedAddCommGroup G] [InnerProductSpace Real G] (f
 : G ≃ₗᵢ[Real] Complex) (x y : G) : ⟪x, y⟫_Real = (f y * conj (f x)).re
参数：f : G ≃ₗᵢ[Real] Complex；x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.inner`：∀ (w z : ℂ), inner ℝ w z = (z * (starRingEnd ℂ) w).re
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫

--- 原说明 ---
The inner product on an inner product space of dimension 2 can be evaluated in t
erms
of a complex-number representation of the space.
-/
theorem inner_map_complex [SeminormedAddCommGroup G] [InnerProductSpace ℝ G] (f : G ≃ₗᵢ[ℝ] ℂ)
    (x y : G) : ⟪x, y⟫_ℝ = (f y * conj (f x)).re := by rw [← Complex.inner, f.inner_map_map]

end RCLikeToReal

section ReApplyInnerSelf

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Extract a real bilinear form from an operator `T`,
by taking the pairing `fun x ↦ re ⟪T x, x⟫`. -/
/-
**ContinuousLinearMap.reApplyInnerSelf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.reApplyInnerSelf (T : E ->L[𝕜] E) (x : E) : Real
参数：T : E ->L[𝕜] E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract a real bilinear form from an operator `T`,
by taking the pairing `fun x ↦ re ⟪T x, x⟫`.
-/
def ContinuousLinearMap.reApplyInnerSelf (T : E →L[𝕜] E) (x : E) : ℝ :=
  re ⟪T x, x⟫
/-
**ContinuousLinearMap.reApplyInnerSelf_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.reApplyInnerSelf_apply (T : E ->L[𝕜] E) (x : E) : T.re
ApplyInnerSelf x = re ⟪T x, x⟫
参数：T : E ->L[𝕜] E；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousLinearMap.reApplyInnerSelf_apply (T : E →L[𝕜] E) (x : E) :
    T.reApplyInnerSelf x = re ⟪T x, x⟫ :=
  rfl

end ReApplyInnerSelf

section ReApplyInnerSelf_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-
**ContinuousLinearMap.reApplyInnerSelf_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.reApplyInnerSelf_continuous (T : E ->L[𝕜] E) : Continu
ous T.reApplyInnerSelf
参数：T : E ->L[𝕜] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem ContinuousLinearMap.reApplyInnerSelf_continuous (T : E →L[𝕜] E) :
    Continuous T.reApplyInnerSelf :=
  reCLM.continuous.comp <| T.continuous.inner continuous_id

set_option backward.isDefEq.respectTransparency false in
/-
**ContinuousLinearMap.reApplyInnerSelf_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.reApplyInnerSelf_smul (T : E ->L[𝕜] E) (x : E) {c : 𝕜}
 : T.reApplyInnerSelf (c • x) = ‖c‖ ^ 2 * T.reApplyInnerSelf x
参数：T : E ->L[𝕜] E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `RCLike.mul_conj`：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ContinuousLinearMap.reApplyInnerSelf_smul (T : E →L[𝕜] E) (x : E) {c : 𝕜} :
    T.reApplyInnerSelf (c • x) = ‖c‖ ^ 2 * T.reApplyInnerSelf x := by
  simp only [map_smul, ContinuousLinearMap.reApplyInnerSelf_apply, inner_smul_left,
    inner_smul_right, ← mul_assoc, mul_conj, ← ofReal_pow, ← smul_re,
    Algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebraMap_eq_ofReal]

end ReApplyInnerSelf_Seminormed

namespace InnerProductSpace
variable {𝕜 E F G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]

open ContinuousLinearMap

variable (𝕜) in
/-- A rank-one operator on an inner product space is given by `x ↦ y ↦ z ↦ ⟪y, z⟫ • x`.

This is also sometimes referred to as an outer product of vectors on a Hilbert space.
This corresponds to the matrix outer product `Matrix.vecMulVec`, see
`InnerProductSpace.toMatrix_rankOne` and `InnerProductSpace.symm_toEuclideanLin_rankOne` in
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`. -/
/-
**InnerProductSpace.rankOne** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpace`。
形式化陈述：rankOne : E ->L[𝕜] F ->L⋆[𝕜] F ->L[𝕜] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rank-one operator on an inner product space is given by `x ↦ y ↦ z ↦ ⟪y, z⟫ • 
x`.

This is also sometimes referred to as an outer product of vectors on a Hilbert s
pace.
This corresponds to the matrix outer product `Matrix.vecMulVec`, see
`InnerProductSpace.toMatrix_rankOne` and `InnerProductSpace.symm_toEuclideanLin_
rankOne` in
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`.
-/
noncomputable def rankOne : E →L[𝕜] F →L⋆[𝕜] F →L[𝕜] E :=
  .flip <| .comp (.smulRightL 𝕜 _ _) (innerSL 𝕜)
/-
**InnerProductSpace.rankOne_def** 是 Mathlib 中的一个引理，位于命名空间 `InnerProductSpace`。
形式化陈述：rankOne_def (x : E) (y : F) : rankOne 𝕜 x y = (innerSL 𝕜 y).smulRight x
参数：x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma rankOne_def (x : E) (y : F) : rankOne 𝕜 x y = (innerSL 𝕜 y).smulRight x := rfl
/-
**InnerProductSpace.rankOne_def'** 是 Mathlib 中的一个引理，位于命名空间 `InnerProductSpace`。
形式化陈述：rankOne_def' (x : E) (y : F) : rankOne 𝕜 x y = .toSpanSingleton 𝕜 x ∘L inn
erSL 𝕜 y
参数：x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma rankOne_def' (x : E) (y : F) : rankOne 𝕜 x y = .toSpanSingleton 𝕜 x ∘L innerSL 𝕜 y := rfl
/-
**InnerProductSpace.toLinearMap_rankOne** 是 Mathlib 中的一个引理，位于命名空间 `InnerProductS
pace`。
形式化陈述：toLinearMap_rankOne (x : E) (y : F) : (rankOne 𝕜 x y).toLinearMap = (inner
ₛₗ 𝕜 y).smulRight x
参数：x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toLinearMap_rankOne (x : E) (y : F) :
    (rankOne 𝕜 x y).toLinearMap = (innerₛₗ 𝕜 y).smulRight x := rfl
/-
**InnerProductSpace.norm_rankOne** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst : RCLike 𝕜] [inst_1 :
 SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : SeminormedAddC
ommGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x : E) (y : F),   ‖((InnerProductS
pace.rankOne 𝕜) x) y‖ = ‖x‖ * ‖y‖
参数：x : E；y : F；(InnerProductSpace.rankOne 𝕜) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InnerProductSpace.rankOne_def`：rankOne_def (x : E) (y : F) : rankOne 𝕜 x
 y = (innerSL 𝕜 y).smulRight x
· 使用定理 `ContinuousLinearMap.norm_smulRight_apply`：norm_smulRight_apply (c : Stro
ngDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖
· 使用定理 `innerSL_apply_norm`：innerSL_apply_norm (x : E) : ‖innerSL 𝕜 x‖ = ‖x‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
@[simp] theorem norm_rankOne (x : E) (y : F) : ‖rankOne 𝕜 x y‖ = ‖x‖ * ‖y‖ := by
  rw [rankOne_def, norm_smulRight_apply, innerSL_apply_norm, mul_comm]
/-
**InnerProductSpace.nnnorm_rankOne** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`
。
形式化陈述：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst : RCLike 𝕜] [inst_1 :
 SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : SeminormedAddC
ommGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x : E) (y : F),   ‖((InnerProductS
pace.rankOne 𝕜) x) y‖₊ = ‖x‖₊ * ‖y‖₊
参数：x : E；y : F；(InnerProductSpace.rankOne 𝕜) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `InnerProductSpace.norm_rankOne`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Typ
e u_6} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : …
-/
@[simp] theorem nnnorm_rankOne (x : E) (y : F) : ‖rankOne 𝕜 x y‖₊ = ‖x‖₊ * ‖y‖₊ :=
  NNReal.eq <| norm_rankOne _ _
/-
**InnerProductSpace.enorm_rankOne** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst : RCLike 𝕜] [inst_1 :
 SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : SeminormedAddC
ommGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x : E) (y : F),   ‖((InnerProductS
pace.rankOne 𝕜) x) y‖ₑ = ‖x‖ₑ * ‖y‖ₑ
参数：x : E；y : F；(InnerProductSpace.rankOne 𝕜) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `InnerProductSpace.nnnorm_rankOne`：∀ {𝕜 : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] [inst_3 : …
-/
@[simp] theorem enorm_rankOne (x : E) (y : F) : ‖rankOne 𝕜 x y‖ₑ = ‖x‖ₑ * ‖y‖ₑ :=
  ENNReal.coe_inj.mpr <| nnnorm_rankOne _ _
/-
**InnerProductSpace.rankOne_apply** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：∀ {𝕜 : Type u_4} {E : Type u_5} {F : Type u_6} [inst : RCLike 𝕜] [inst_1 :
 SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : SeminormedAddC
ommGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x : E) (y z : F),   (((InnerProduc
tSpace.rankOne 𝕜) x) y) z = inner 𝕜 y z • x
参数：x : E；y z : F；((InnerProductSpace.rankOne 𝕜) x) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
@[simp] lemma rankOne_apply (x : E) (y z : F) : rankOne 𝕜 x y z = inner 𝕜 y z • x := rfl
/-
**InnerProductSpace.comp_rankOne** 是 Mathlib 中的一个引理，位于命名空间 `InnerProductSpace`。
形式化陈述：comp_rankOne {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] (x :
 E) (y : F) (f : E ->L[𝕜] G) : f ∘L rankOne 𝕜 x y = rankOne 𝕜 (f x) y
参数：x : E；y : F；f : E ->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.comp_toSpanSingleton`：comp_toSpanSingleton (f : M₁ -
>L[R₁] M₂) (x : M₁) : f ∘L toSpanSingleton R₁ x = toSpanSingleton R₁ (f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_rankOne {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (x : E) (y : F) (f : E →L[𝕜] G) : f ∘L rankOne 𝕜 x y = rankOne 𝕜 (f x) y := by
  simp_rw [rankOne_def', ← comp_assoc, comp_toSpanSingleton]
/-
**InnerProductSpace.isIdempotentElem_rankOne_self** 是 Mathlib 中的一个定理，位于命名空间 `Inn
erProductSpace`。
形式化陈述：isIdempotentElem_rankOne_self {x : F} (hx : ‖x‖ = 1) : IsIdempotentElem (r
ankOne 𝕜 x x)
参数：hx : ‖x‖ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InnerProductSpace.comp_rankOne`：comp_rankOne {G : Type*} [SeminormedAddC
ommGroup G] [NormedSpace 𝕜 G] (x : E) (y : F) (f : E ->L[𝕜] G) : f ∘L rankOne 𝕜 
x y = rankOne 𝕜 (f x…
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
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
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isIdempotentElem_rankOne_self {x : F} (hx : ‖x‖ = 1) :
    IsIdempotentElem (rankOne 𝕜 x x) := by simp [IsIdempotentElem, mul_def, comp_rankOne, hx]
/-
**InnerProductSpace.rankOne_one_right_eq_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名
空间 `InnerProductSpace`。
形式化陈述：∀ {𝕜 : Type u_4} {F : Type u_6} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   (x : F), ((InnerProductSpace.rank
One 𝕜) x) 1 = ContinuousLinearMap.toSpanSingleton 𝕜 x
参数：x : F；(InnerProductSpace.rankOne 𝕜) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
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
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem rankOne_one_right_eq_toSpanSingleton (x : F) :
    rankOne 𝕜 x 1 = toSpanSingleton 𝕜 x := by ext; simp
/-
**InnerProductSpace.rankOne_one_left_eq_innerSL** 是 Mathlib 中的一个定理，位于命名空间 `Inner
ProductSpace`。
形式化陈述：∀ {𝕜 : Type u_4} {F : Type u_6} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   (x : F), ((InnerProductSpace.rank
One 𝕜) 1) x = (innerSL 𝕜) x
参数：x : F；(InnerProductSpace.rankOne 𝕜) 1；innerSL 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem rankOne_one_left_eq_innerSL (x : F) : rankOne 𝕜 1 x = innerSL 𝕜 x := by ext; simp
/-
**InnerProductSpace.rankOne_comp_rankOne** 是 Mathlib 中的一个引理，位于命名空间 `InnerProduct
Space`。
形式化陈述：rankOne_comp_rankOne (x : E) (y z : F) (w : G) : rankOne 𝕜 x y ∘L rankOne 
𝕜 z w = inner 𝕜 y z • rankOne 𝕜 x w
参数：x : E；y z : F；w : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InnerProductSpace.comp_rankOne`：comp_rankOne {G : Type*} [SeminormedAddC
ommGroup G] [NormedSpace 𝕜 G] (x : E) (y : F) (f : E ->L[𝕜] G) : f ∘L rankOne 𝕜 
x y = rankOne 𝕜 (f x…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rankOne_comp_rankOne (x : E) (y z : F) (w : G) :
    rankOne 𝕜 x y ∘L rankOne 𝕜 z w = inner 𝕜 y z • rankOne 𝕜 x w := by
  simp [comp_rankOne]
/-
**InnerProductSpace.inner_left_rankOne_apply** 是 Mathlib 中的一个引理，位于命名空间 `InnerPro
ductSpace`。
形式化陈述：inner_left_rankOne_apply (x : F) (y z : G) (w : F) : inner 𝕜 (rankOne 𝕜 x 
y z) w = inner 𝕜 z y * inner 𝕜 x w
参数：x : F；y z : G；w : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inner_left_rankOne_apply (x : F) (y z : G) (w : F) :
    inner 𝕜 (rankOne 𝕜 x y z) w = inner 𝕜 z y * inner 𝕜 x w := by
  simp [inner_smul_left, inner_conj_symm]
/-
**InnerProductSpace.inner_right_rankOne_apply** 是 Mathlib 中的一个引理，位于命名空间 `InnerPr
oductSpace`。
形式化陈述：inner_right_rankOne_apply (x y : F) (z w : G) : inner 𝕜 x (rankOne 𝕜 y z w
) = inner 𝕜 x y * inner 𝕜 z w
参数：x y : F；z w : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inner_right_rankOne_apply (x y : F) (z w : G) :
    inner 𝕜 x (rankOne 𝕜 y z w) = inner 𝕜 x y * inner 𝕜 z w := by
  simp [inner_smul_right, mul_comm]

section Normed
variable {F H : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-
**InnerProductSpace.rankOne_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace
`。
形式化陈述：∀ {𝕜 : Type u_4} {E : Type u_5} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : NormedSpace 𝕜 E]   {F : Type u_8} [inst_3 : NormedAddCommG
roup F] [inst_4 : InnerProductSpace 𝕜 F] {x : E} {y : F},   ((InnerProductSpace.
rankOne 𝕜) x) y = 0 ↔ x = 0 ∨ y = 0
参数：(InnerProductSpace.rankOne 𝕜) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `ext_iff_inner_right`：ext_iff_inner_right {x y : E} : x = y ↔ forall v, ⟪
x, v⟫ = ⟪y, v⟫
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem rankOne_eq_zero {x : E} {y : F} : rankOne 𝕜 x y = 0 ↔ x = 0 ∨ y = 0 := by
  simp [ContinuousLinearMap.ext_iff, rankOne_apply, forall_or_right, or_comm,
    ext_iff_inner_right 𝕜 (E := F)]
/-
**InnerProductSpace.rankOne_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `InnerProductSpace
`。
形式化陈述：rankOne_ne_zero {x : E} {y : F} (hx : x != 0) (hy : y != 0) : rankOne 𝕜 x 
y != 0
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rankOne_ne_zero {x : E} {y : F} (hx : x ≠ 0) (hy : y ≠ 0) : rankOne 𝕜 x y ≠ 0 := by
  grind [rankOne_eq_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**InnerProductSpace.isIdempotentElem_rankOne_self_iff** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductSpace`。
形式化陈述：isIdempotentElem_rankOne_self_iff {x : F} (hx : x != 0) : IsIdempotentElem
 (rankOne 𝕜 x x) ↔ ‖x‖ = 1
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `InnerProductSpace.comp_rankOne`：comp_rankOne {G : Type*} [SeminormedAddC
ommGroup G] [NormedSpace 𝕜 G] (x : E) (y : F) (f : E ->L[𝕜] G) : f ∘L rankOne 𝕜 
x y = rankOne 𝕜 (f x…
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 33 条，此处仅展示前 30 条）
-/
theorem isIdempotentElem_rankOne_self_iff {x : F} (hx : x ≠ 0) :
    IsIdempotentElem (rankOne 𝕜 x x) ↔ ‖x‖ = 1 := by
  refine ⟨?_, isIdempotentElem_rankOne_self⟩
  simp only [IsIdempotentElem, mul_def, comp_rankOne, rankOne_apply, inner_self_eq_norm_sq_to_K,
    map_smul, _root_.smul_apply]
  nth_rw 2 [← one_smul 𝕜 (rankOne 𝕜 x x)]
  rw [← sub_eq_zero, ← sub_smul]
  simp only [smul_eq_zero, rankOne_eq_zero, hx, or_self, or_false, sub_eq_zero, sq_eq_one_iff,
    FaithfulSMul.algebraMap_eq_one_iff, ← show ((-(1 : ℝ) : ℝ) : 𝕜) = -1 by grind, ofReal_inj]
  grind [norm_nonneg]
/-
**InnerProductSpace.rankOne_eq_rankOne_iff_comm** 是 Mathlib 中的一个定理，位于命名空间 `Inner
ProductSpace`。
形式化陈述：rankOne_eq_rankOne_iff_comm {a c : F} {b d : H} : rankOne 𝕜 a b = rankOne 
𝕜 c d ↔ rankOne 𝕜 b a = rankOne 𝕜 d c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ext_iff_inner_left`：ext_iff_inner_left {x y : E} : x = y ↔ forall v, ⟪v,
 x⟫ = ⟪v, y⟫
· 使用定理 `ext_iff_inner_right`：ext_iff_inner_right {x y : E} : x = y ↔ forall v, ⟪
x, v⟫ = ⟪y, v⟫
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rankOne_eq_rankOne_iff_comm {a c : F} {b d : H} :
    rankOne 𝕜 a b = rankOne 𝕜 c d ↔ rankOne 𝕜 b a = rankOne 𝕜 d c := by
  simp_rw [ContinuousLinearMap.ext_iff, ext_iff_inner_left 𝕜 (E := F),
    ext_iff_inner_right 𝕜 (E := H)]
  rw [forall_comm]
  simp [inner_smul_left, inner_smul_right, mul_comm]

open ComplexOrder in
/-
**InnerProductSpace.exists_of_rankOne_eq_rankOne** 是 Mathlib 中的一个定理，位于命名空间 `Inne
rProductSpace`。
形式化陈述：exists_of_rankOne_eq_rankOne {a c : F} {b d : H} (ha : a != 0) (hb : b != 
0) (h : rankOne 𝕜 a b = rankOne 𝕜 c d) : exists (α β : 𝕜) (_ : α != 0) (_ : 0 < 
β), a = α • c ∧ b = (α * β) • d
参数：ha : a != 0；hb : b != 0；h : rankOne 𝕜 a b = rankOne 𝕜 c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `InnerProductSpace.rankOne_eq_rankOne_iff_comm`：rankOne_eq_rankOne_iff_co
mm {a c : F} {b d : H} : rankOne 𝕜 a b = rankOne 𝕜 c d ↔ rankOne 𝕜 b a = rankOne
 𝕜 d c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
（共 74 条，此处仅展示前 30 条）
-/
theorem exists_of_rankOne_eq_rankOne {a c : F} {b d : H}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : rankOne 𝕜 a b = rankOne 𝕜 c d) :
    ∃ (α β : 𝕜) (_ : α ≠ 0) (_ : 0 < β), a = α • c ∧ b = (α * β) • d := by
  have h₂ := rankOne_eq_rankOne_iff_comm.mp h
  simp only [ContinuousLinearMap.ext_iff, rankOne_apply] at h h₂
  have h₃ := calc
    a = (⟪b, b⟫_𝕜 / ⟪b, b⟫_𝕜) • a := by simp_all
    _ = (1 / ⟪b, b⟫_𝕜) • (⟪b, b⟫_𝕜 • a) := by simp only [smul_smul]; ring_nf
    _ = (⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) • c := by simp only [h, smul_smul]; ring_nf
  have h₄ := calc
    b = (⟪a, a⟫_𝕜 / ⟪a, a⟫_𝕜) • b := by simp_all
    _ = (1 / ⟪a, a⟫_𝕜) • (⟪a, a⟫_𝕜 • b) := by simp only [smul_smul]; ring_nf
    _ = ((⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) * (⟪c, c⟫_𝕜 / ⟪a, a⟫_𝕜)) • d := by
      simp_rw [h₂, h₃, inner_smul_right, smul_smul]; ring_nf
  have h₅ : ⟪d, b⟫_𝕜 ≠ 0 := fun h ↦ by simp [h, hb] at h₄
  have h₆ : c ≠ 0 := fun h ↦ by simp [h, ha] at h₃
  refine ⟨_, ‖c‖ ^ 2 / ‖a‖ ^ 2, div_ne_zero h₅ <| by simpa, ?_, h₃, by simpa using h₄⟩
  simp_rw [← ofReal_pow, ← ofReal_div, pos_iff (K := 𝕜), ofReal_re, ofReal_im, and_true]
  exact div_pos (by simpa [sq_pos_iff]) (by simpa [sq_pos_iff])

end Normed

end InnerProductSpace

namespace ContinuousLinearMap

open InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-
**ContinuousLinearMap.opNorm_le_of_re_inner_le** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：opNorm_le_of_re_inner_le {T : E ->L[𝕜] F} {C : Real} (hC : 0 <= C) (h : fo
rall x y, ‖x‖ = 1 -> ‖y‖ = 1 -> re ⟪T x, y⟫_𝕜 <= C) : ‖T‖ <= C
参数：hC : 0 <= C；h : forall x y, ‖x‖ = 1 -> ‖y‖ = 1 -> re ⟪T x, y⟫_𝕜 <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_of_unit_norm`：opNorm_le_of_unit_norm [Norm
edAlgebra Real 𝕜] {f : E ->SL[σ₁₂] F} {C : Real} (hC : 0 <= C) (hf : forall x, ‖
x‖ = 1 -> ‖f x‖ <= C) : ‖f‖ <= C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_self_div_self`：mul_self_div_self (a : G₀) : a * a / a = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.norm_sq_eq_re_inner`：∀ {𝕜 : Type u_4} {E : Type u_5} {
inst : RCLike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜
 E]   (x : E), ‖x‖ ^ 2 = RC…
· 使用定理 `RCLike.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r
 * re z
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opNorm_le_of_re_inner_le {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, ‖x‖ = 1 → ‖y‖ = 1 → re ⟪T x, y⟫_𝕜 ≤ C) : ‖T‖ ≤ C := by
  refine opNorm_le_of_unit_norm hC fun x hx ↦ ?_
  by_cases hTx : ‖T x‖ = 0
  · rwa [hTx]
  · specialize h x (((‖T x‖⁻¹ : ℝ) : 𝕜) • T x) hx (by simp [norm_smul, hTx])
    rwa [inner_smul_right, re_ofReal_mul, ← norm_sq_eq_re_inner,
      inv_mul_eq_div, sq, mul_self_div_self] at h

end ContinuousLinearMap

