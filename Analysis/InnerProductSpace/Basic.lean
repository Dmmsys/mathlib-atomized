/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Properties of inner product spaces

This file proves many basic properties of inner product spaces (real or complex).

## Main results

- `inner_mul_inner_self_le`: the Cauchy-Schwarz inequality (one of many variants).
- `norm_inner_eq_norm_iff`: the equality criterion in the Cauchy-Schwarz inequality (also in many
  variants).
- `inner_eq_sum_norm_sq_div_four`: the polarization identity.

## Tags

inner product space, Hilbert space, norm

-/

@[expose] public section


noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section BasicProperties_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_re_inner)

@[simp]
/-
**inner_conj_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.conj_inner_symm`：∀ {𝕜 : Type u_4} {E : Type u_5} {inst
 : RCLike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜 E] 
  (x y : E), (starRingE…
-/
theorem inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  InnerProductSpace.conj_inner_symm _ _
/-
**real_inner_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
-/
theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ :=
  @inner_conj_symm ℝ _ _ _ _ x y
/-
**inner_eq_zero_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `star_eq_zero`：star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : sta
r x = 0 ↔ x = 0
-/
theorem inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 := by
  rw [← inner_conj_symm]
  exact star_eq_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Sort*} (v : ι → E) : Std.Symm fun i j => ⟪v i, v j⟫ = 0 where
  symm _ _ := inner_eq_zero_symm.1
/-
**inner_self_im** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_im (x : E) : im ⟪x, x⟫ = 0
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_inj`：ofReal_inj {z w : Real} : (z : K) = (w : K) ↔ z = w
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RCLike.im_eq_conj_sub`：im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - 
z) / 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_self_im (x : E) : im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj 𝕜, im_eq_conj_sub]; simp
/-
**inner_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
参数：x y z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.add_left`：∀ {𝕜 : Type u_4} {E : Type u_5} {inst : RCLi
ke 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜 E]   (x y 
z : E), inner 𝕜 …
-/
theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  InnerProductSpace.add_left _ _ _
/-
**inner_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
参数：x y z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, map_add]
  simp only [inner_conj_symm]
/-
**inner_re_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.conj_re`：conj_re (z : K) : re (conj z) = re z
-/
theorem inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]
/-
**inner_im_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_im_symm (x y : E) : im ⟪x, y⟫ = -im ⟪y, x⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.conj_im`：conj_im (z : K) : im (conj z) = -im z
-/
theorem inner_im_symm (x y : E) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

section Algebra
variable {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [Module 𝕝 E]
  [IsScalarTower 𝕝 𝕜 E] [StarModule 𝕝 𝕜]

/-- See `inner_smul_left` for the common special when `𝕜 = 𝕝`. -/
/-
**inner_smul_left_eq_star_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inner_smul_left_eq_star_smul (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r† • ⟪x, y⟫
参数：x y : E；r : 𝕝。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `InnerProductSpace.smul_left`：∀ {𝕜 : Type u_4} {E : Type u_5} {inst : RCL
ike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜 E]   (x y
 : E) (r : 𝕜), in…
· 使用定理 `starRingEnd_apply`：starRingEnd_apply (x : R) : starRingEnd R x = star x
· 使用定理 `algebraMap_star_comm`：algebraMap_star_comm (r : R) : algebraMap R A (sta
r r) = star (algebraMap R A r)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
See `inner_smul_left` for the common special when `𝕜 = 𝕝`.
-/
lemma inner_smul_left_eq_star_smul (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r† • ⟪x, y⟫ := by
  rw [← algebraMap_smul 𝕜 r, InnerProductSpace.smul_left, starRingEnd_apply, starRingEnd_apply,
    ← algebraMap_star_comm, ← smul_eq_mul, algebraMap_smul]

/-- Special case of `inner_smul_left_eq_star_smul` when the acting ring has a trivial star
(e.g. `ℕ`, `ℤ`, `ℚ≥0`, `ℚ`, `ℝ`). -/
/-
**inner_smul_left_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inner_smul_left_eq_smul [TrivialStar 𝕝] (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r
 • ⟪x, y⟫
参数：x y : E；r : 𝕝。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inner_smul_left_eq_star_smul`：inner_smul_left_eq_star_smul (x y : E) (r 
: 𝕝) : ⟪r • x, y⟫ = r† • ⟪x, y⟫
· 使用定理 `starRingEnd_apply`：starRingEnd_apply (x : R) : starRingEnd R x = star x
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r

--- 原说明 ---
Special case of `inner_smul_left_eq_star_smul` when the acting ring has a trivia
l star
(e.g. `ℕ`, `ℤ`, `ℚ≥0`, `ℚ`, `ℝ`).
-/
lemma inner_smul_left_eq_smul [TrivialStar 𝕝] (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left_eq_star_smul, starRingEnd_apply, star_trivial]

/-- See `inner_smul_right` for the common special when `𝕜 = 𝕝`. -/
/-
**inner_smul_right_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inner_smul_right_eq_smul (x y : E) (r : 𝕝) : ⟪x, r • y⟫ = r • ⟪x, y⟫
参数：x y : E；r : 𝕝。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用引理 `inner_smul_left_eq_star_smul`：inner_smul_left_eq_star_smul (x y : E) (r 
: 𝕝) : ⟪r • x, y⟫ = r† • ⟪x, y⟫
· 使用定理 `starRingEnd_apply`：starRingEnd_apply (x : R) : starRingEnd R x = star x
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r

--- 原说明 ---
See `inner_smul_right` for the common special when `𝕜 = 𝕝`.
-/
lemma inner_smul_right_eq_smul (x y : E) (r : 𝕝) : ⟪x, r • y⟫ = r • ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left_eq_star_smul, starRingEnd_apply, starRingEnd_apply,
    star_smul, star_star, ← starRingEnd_apply, inner_conj_symm]

end Algebra

/-- See `inner_smul_left_eq_star_smul` for the case of a general algebra action. -/
/-
**inner_smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫
参数：x y : E；r : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inner_smul_left_eq_star_smul`：inner_smul_left_eq_star_smul (x y : E) (r 
: 𝕝) : ⟪r • x, y⟫ = r† • ⟪x, y⟫

--- 原说明 ---
See `inner_smul_left_eq_star_smul` for the case of a general algebra action.
-/
theorem inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  inner_smul_left_eq_star_smul ..
/-
**real_inner_smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x, y⟫_Real = r * ⟪x, y⟫_R
eal
参数：x y : F；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
-/
theorem real_inner_smul_left (x y : F) (r : ℝ) : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_left _ _ _
/-
**inner_smul_real_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_smul_real_left (x y : E) (r : Real) : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫
参数：x y : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem inner_smul_real_left (x y : E) (r : ℝ) : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left, conj_ofReal, Algebra.smul_def]

/-- See `inner_smul_right_eq_smul` for the case of a general algebra action. -/
/-
**inner_smul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫
参数：x y : E；r : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inner_smul_right_eq_smul`：inner_smul_right_eq_smul (x y : E) (r : 𝕝) : ⟪
x, r • y⟫ = r • ⟪x, y⟫

--- 原说明 ---
See `inner_smul_right_eq_smul` for the case of a general algebra action.
-/
theorem inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
  inner_smul_right_eq_smul ..
/-
**real_inner_smul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_smul_right (x y : F) (r : Real) : ⟪x, r • y⟫_Real = r * ⟪x, y⟫_
Real
参数：x y : F；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
-/
theorem real_inner_smul_right (x y : F) (r : ℝ) : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_right _ _ _
/-
**inner_smul_real_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_smul_real_right (x y : E) (r : Real) : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫
参数：x y : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem inner_smul_real_right (x y : E) (r : ℝ) : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_right, Algebra.smul_def]


variable (𝕜)

/-- The inner product as a sesquilinear map.

Note that in the case `𝕜 = ℝ` this is a bilinear form. -/
/-
**inner** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inner product as a sesquilinear map.

Note that in the case `𝕜 = ℝ` this is a bilinear form.
-/
def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _

@[simp]
/-
**coe_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_innerₛₗ_apply (v : E) : ⇑(innerₛₗ 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
/-
**inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem innerₛₗ_apply_apply (v w : E) : innerₛₗ 𝕜 v w = ⟪v, w⟫ :=
  rfl

variable (F)
/-- The inner product as a bilinear map in the real case. -/
/-
**inner** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inner product as a bilinear map in the real case.
-/
def innerₗ : F →ₗ[ℝ] F →ₗ[ℝ] ℝ := innerₛₗ ℝ
/-
**flip_inner** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma flip_innerₗ : (innerₗ F).flip = innerₗ F := by
  ext v w
  exact real_inner_comm v w

variable {F}
/-
**inner** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma innerₗ_apply_apply (v w : F) : innerₗ F v w = ⟪v, w⟫_ℝ := rfl

variable {𝕜}

/-- An inner product with a sum on the left. -/
/-
**sum_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪∑ i in s, f i
, x⟫ = ∑ i in s, ⟪f i, x⟫
参数：s : Finset ι；f : ι -> E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
An inner product with a sum on the left.
-/
theorem sum_inner {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪∑ i ∈ s, f i, x⟫ = ∑ i ∈ s, ⟪f i, x⟫ :=
  map_sum ((innerₛₗ 𝕜).flip x) _ _

/-- An inner product with a sum on the right. -/
/-
**inner_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪x, ∑ i in s, 
f i⟫ = ∑ i in s, ⟪x, f i⟫
参数：s : Finset ι；f : ι -> E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
An inner product with a sum on the right.
-/
theorem inner_sum {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫ :=
  map_sum (innerₛₗ 𝕜 x) _ _

/-- An inner product with a sum on the left, `Finsupp` version. -/
/-
**Finsupp.sum_inner** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u_4} {M : Type u_5} [in
st_3 : Zero M] (l : ι →₀ M) (v : ι → M → E) (x : E),   inner 𝕜 (l.sum v) x = l.s
um fun i a => inner 𝕜 (v i a) x
参数：l : ι →₀ M；v : ι → M → E；x : E；l.sum v；v i a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An inner product with a sum on the left, `Finsupp` version.
-/
protected theorem Finsupp.sum_inner {ι : Type*} {M : Type*} [Zero M] (l : ι →₀ M)
    (v : ι → M → E) (x : E) : ⟪l.sum v, x⟫ = l.sum fun (i : ι) (a : M) ↦ ⟪v i a, x⟫ := by
  simp [sum, sum_inner]

/-- An inner product with a sum on the right, `Finsupp` version. -/
/-
**Finsupp.inner_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u_4} {M : Type u_5} [in
st_3 : Zero M] (l : ι →₀ M) (v : ι → M → E) (x : E),   inner 𝕜 x (l.sum v) = l.s
um fun i a => inner 𝕜 x (v i a)
参数：l : ι →₀ M；v : ι → M → E；x : E；l.sum v；v i a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An inner product with a sum on the right, `Finsupp` version.
-/
protected theorem Finsupp.inner_sum {ι : Type*} {M : Type*} [Zero M] (l : ι →₀ M)
    (v : ι → M → E) (x : E) : ⟪x, l.sum v⟫ = l.sum fun (i : ι) (a : M) ↦ ⟪x, v i a⟫ := by
  simp [sum, inner_sum]
/-
**DFinsupp.sum_inner** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u_4} [inst_3 : Decidabl
eEq ι] {α : ι → Type u_5} [inst_4 : (i : ι) → AddZeroClass (α i)]   [inst_5 : (i
 : ι) → (x : α i) → Decidable (x ≠ 0)] (f : (i : ι) → α i → E) (l : Π₀ (i : ι), 
α i) (x : E),   inner 𝕜 (l.sum f) x = l.sum fun i a => inner 𝕜 (f i a) x
参数：i : ι；α i；i : ι；x : α i；x ≠ 0；f : (i : ι) → α i → E；l : Π₀ (i : ι), α i；x : E
；l.sum f；f i a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem DFinsupp.sum_inner {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪l.sum f, x⟫ = l.sum fun i a => ⟪f i a, x⟫ := by
  simp +contextual only [DFinsupp.sum, sum_inner]
/-
**DFinsupp.inner_sum** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u_4} [inst_3 : Decidabl
eEq ι] {α : ι → Type u_5} [inst_4 : (i : ι) → AddZeroClass (α i)]   [inst_5 : (i
 : ι) → (x : α i) → Decidable (x ≠ 0)] (f : (i : ι) → α i → E) (l : Π₀ (i : ι), 
α i) (x : E),   inner 𝕜 x (l.sum f) = l.sum fun i a => inner 𝕜 x (f i a)
参数：i : ι；α i；i : ι；x : α i；x ≠ 0；f : (i : ι) → α i → E；l : Π₀ (i : ι), α i；x : E
；l.sum f；f i a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem DFinsupp.inner_sum {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪x, l.sum f⟫ = l.sum fun i a => ⟪x, f i a⟫ := by
  simp +contextual only [DFinsupp.sum, inner_sum]

@[simp]
/-
**inner_zero_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_zero_left (x : E) : ⟪0, x⟫ = 0
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem inner_zero_left (x : E) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : E), inner_smul_left, map_zero, zero_mul]
/-
**inner_re_zero_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_re_zero_left (x : E) : re ⟪0, x⟫ = 0
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_re_zero_left (x : E) : re ⟪0, x⟫ = 0 := by
  simp only [inner_zero_left, map_zero]

@[simp]
/-
**inner_zero_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem inner_zero_right (x : E) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left, map_zero]
/-
**inner_re_zero_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0 := by
  simp only [inner_zero_right, map_zero]
/-
**inner_self_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_nonneg {x : E} : 0 <= re ⟪x, x⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreInnerProductSpace.Core.re_inner_nonneg`：∀ {𝕜 : Type u_4} {F : Type u_
5} [inst : RCLike 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   (s
elf : PreInnerProductSpace.Core…
-/
theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ :=
  PreInnerProductSpace.toCore.re_inner_nonneg x
/-
**real_inner_self_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_self_nonneg {x : F} : 0 <= ⟪x, x⟫_Real
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_self_nonneg`：inner_self_nonneg {x : E} : 0 <= re ⟪x, x⟫
-/
theorem real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ :=
  @inner_self_nonneg ℝ F _ _ _ x
/-
**inner_self_ofReal_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `RCLike.is_real_TFAE`：is_real_TFAE (z : K) : TFAE [conj z = z, exists r :
 Real, (r : K) = z, ↑(re z) = z, im z = 0, IsSelfAdjoint z]
· 使用定理 `inner_self_im`：inner_self_im (x : E) : im ⟪x, x⟫ = 0
-/
theorem inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  ((RCLike.is_real_TFAE (⟪x, x⟫ : 𝕜)).out 2 3).2 (inner_self_im (𝕜 := 𝕜) x)

@[simp]
/-
**inner_self_eq_norm_sq_to_K** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (‖x‖ : 𝕜) ^ 2
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_ofReal_re`：inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪
x, x⟫
· 使用定理 `InnerProductSpace.norm_sq_eq_re_inner`：∀ {𝕜 : Type u_4} {E : Type u_5} {
inst : RCLike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜
 E]   (x : E), ‖x‖ ^ 2 = RC…
· 使用定理 `RCLike.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K
) = (r : K) ^ n
-/
theorem inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (‖x‖ : 𝕜) ^ 2 := by
  rw [← inner_self_ofReal_re, ← norm_sq_eq_re_inner, ofReal_pow]
/-
**inner_self_re_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_re_eq_norm (x : E) : re ⟪x, x⟫ = ‖⟪x, x⟫‖
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_ofReal_re`：inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪
x, x⟫
· 使用定理 `RCLike.norm_of_nonneg`：norm_of_nonneg {r : Real} (h : 0 <= r) : ‖(r : K)
‖ = r
· 使用定理 `inner_self_nonneg`：inner_self_nonneg {x : E} : 0 <= re ⟪x, x⟫
-/
theorem inner_self_re_eq_norm (x : E) : re ⟪x, x⟫ = ‖⟪x, x⟫‖ := by
  conv_rhs => rw [← inner_self_ofReal_re]
  symm
  exact norm_of_nonneg inner_self_nonneg
/-
**inner_self_ofReal_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_ofReal_norm (x : E) : (‖⟪x, x⟫‖ : 𝕜) = ⟪x, x⟫
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_re_eq_norm`：inner_self_re_eq_norm (x : E) : re ⟪x, x⟫ = ‖⟪x, 
x⟫‖
· 使用定理 `inner_self_ofReal_re`：inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪
x, x⟫
-/
theorem inner_self_ofReal_norm (x : E) : (‖⟪x, x⟫‖ : 𝕜) = ⟪x, x⟫ := by
  rw [← inner_self_re_eq_norm]
  exact inner_self_ofReal_re _
/-
**real_inner_self_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_self_abs (x : F) : |⟪x, x⟫_Real| = ⟪x, x⟫_Real
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_self_ofReal_norm`：inner_self_ofReal_norm (x : E) : (‖⟪x, x⟫‖ : 𝕜) 
= ⟪x, x⟫
-/
theorem real_inner_self_abs (x : F) : |⟪x, x⟫_ℝ| = ⟪x, x⟫_ℝ :=
  @inner_self_ofReal_norm ℝ F _ _ _ x
/-
**norm_inner_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inner_symm (x y : E) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
-/
theorem norm_inner_symm (x y : E) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]

@[simp]
/-
**inner_neg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp

@[simp]
/-
**inner_neg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left]; simp only [map_neg, inner_conj_symm]
/-
**inner_neg_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_neg_neg (x y : E) : ⟪-x, -y⟫ = ⟪x, y⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_neg_neg (x y : E) : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp
/-
**inner_self_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_conj (x : E) : ⟪x, x⟫† = ⟪x, x⟫
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
-/
theorem inner_self_conj (x : E) : ⟪x, x⟫† = ⟪x, x⟫ := inner_conj_symm _ _
/-
**inner_sub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫
参数：x y z : E。
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
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]
/-
**inner_sub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫
参数：x y z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]
/-
**inner_mul_symm_re_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_mul_symm_re_eq_norm (x y : E) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y,
 x⟫‖
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.re_eq_norm_of_mul_conj`：re_eq_norm_of_mul_conj (x : K) : re (x * 
conj x) = ‖x * conj x‖
-/
theorem inner_mul_symm_re_eq_norm (x y : E) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

/-- Expand `⟪x + y, x + y⟫` -/
/-
**inner_add_add_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ +
 ⟪y, y⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a

--- 原说明 ---
Expand `⟪x + y, x + y⟫`
-/
theorem inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

/-- Expand `⟪x + y, x + y⟫_ℝ` -/
/-
**real_inner_add_add_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_add_add_self (x y : F) : ⟪x + y, x + y⟫_Real = ⟪x, x⟫_Real + 2 
* ⟪x, y⟫_Real + ⟪y, y⟫_Real
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_add_add_self`：inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, 
x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Expand `⟪x + y, x + y⟫_ℝ`
-/
theorem real_inner_add_add_self (x y : F) :
    ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm]; rfl
  simp only [inner_add_add_self, this, add_left_inj]
  ring

-- Expand `⟪x - y, x - y⟫`
/-
**inner_sub_sub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ +
 ⟪y, y⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
-/
theorem inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring

/-- Expand `⟪x - y, x - y⟫_ℝ` -/
/-
**real_inner_sub_sub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_sub_sub_self (x y : F) : ⟪x - y, x - y⟫_Real = ⟪x, x⟫_Real - 2 
* ⟪x, y⟫_Real + ⟪y, y⟫_Real
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_sub_sub_self`：inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, 
x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Expand `⟪x - y, x - y⟫_ℝ`
-/
theorem real_inner_sub_sub_self (x y : F) :
    ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm]; rfl
  simp only [inner_sub_sub_self, this, add_left_inj]
  ring

/-- Parallelogram law -/
/-
**parallelogram_law** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x
⟫ + ⟪y, y⟫)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_add_add_self`：inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, 
x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫
· 使用定理 `inner_sub_sub_self`：inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, 
x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Parallelogram law
-/
theorem parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) := by
  simp only [inner_add_add_self, inner_sub_sub_self]
  ring

/-- **Cauchy–Schwarz inequality**. -/
@[wikidata Q190546]
/-
**inner_mul_inner_self_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re 
⟪y, y⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.Core.inner_mul_inner_self_le`：inner_mul_inner_self_le 
(x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re ⟪y, y⟫

--- 原说明 ---
**Cauchy–Schwarz inequality**.
-/
theorem inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
  letI : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  InnerProductSpace.Core.inner_mul_inner_self_le x y

/-- Cauchy–Schwarz inequality for real inner products. -/
/-
**real_inner_mul_inner_self_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_Real * ⟪x, y⟫_Real <= ⟪x, 
x⟫_Real * ⟪y, y⟫_Real
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `inner_mul_inner_self_le`：inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * 
‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re ⟪y, y⟫

--- 原说明 ---
Cauchy–Schwarz inequality for real inner products.
-/
theorem real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ :=
  calc
    ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ‖⟪x, y⟫_ℝ‖ * ‖⟪y, x⟫_ℝ‖ := by
      rw [real_inner_comm y, ← norm_mul]
      exact le_abs_self _
    _ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ := @inner_mul_inner_self_le ℝ _ _ _ _ x y
/-
**inner_eq_ofReal_norm_sq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_ofReal_norm_sq_left_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖v‖ ^ 2 ↔ ⟪v, v - 
w⟫_𝕜 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inner_eq_ofReal_norm_sq_left_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_𝕜 = 0 := by
  rw [inner_sub_right, sub_eq_zero, inner_self_eq_norm_sq_to_K, eq_comm]
/-
**inner_eq_norm_sq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_norm_sq_left_iff {v w : F} : ⟪v, w⟫_Real = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_R
eal = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_eq_ofReal_norm_sq_left_iff`：inner_eq_ofReal_norm_sq_left_iff {v w 
: E} : ⟪v, w⟫_𝕜 = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_𝕜 = 0
-/
theorem inner_eq_norm_sq_left_iff {v w : F} : ⟪v, w⟫_ℝ = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_ℝ = 0 :=
  inner_eq_ofReal_norm_sq_left_iff
/-
**inner_eq_ofReal_norm_sq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_ofReal_norm_sq_right_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖w‖ ^ 2 ↔ ⟪v - w,
 w⟫_𝕜 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inner_eq_ofReal_norm_sq_right_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_𝕜 = 0 := by
  rw [inner_sub_left, sub_eq_zero, inner_self_eq_norm_sq_to_K, eq_comm]
/-
**inner_eq_norm_sq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_norm_sq_right_iff {v w : F} : ⟪v, w⟫_Real = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_
Real = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_eq_ofReal_norm_sq_right_iff`：inner_eq_ofReal_norm_sq_right_iff {v 
w : E} : ⟪v, w⟫_𝕜 = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_𝕜 = 0
-/
theorem inner_eq_norm_sq_right_iff {v w : F} : ⟪v, w⟫_ℝ = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_ℝ = 0 :=
  inner_eq_ofReal_norm_sq_right_iff

end BasicProperties_Seminormed

section BasicProperties

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

export InnerProductSpace (norm_sq_eq_re_inner)

/-
**inner_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `RCLike.ofReal_eq_zero`：ofReal_eq_zero {x : Real} : (x : K) = 0 ↔ x = 0
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  rw [inner_self_eq_norm_sq_to_K, sq_eq_zero_iff, ofReal_eq_zero, norm_eq_zero]
/-
**inner_self_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_ne_zero {x : E} : ⟪x, x⟫ != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
-/
theorem inner_self_ne_zero {x : E} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

variable (𝕜)
/-
**ext_inner_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫) : x = y
参数：h : forall v, ⟪v, x⟫ = ⟪v, y⟫。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
-/
theorem ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_right, sub_eq_zero, h (x - y)]
/-
**ext_iff_inner_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_iff_inner_left {x y : E} : x = y ↔ forall v, ⟪v, x⟫ = ⟪v, y⟫
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ext_inner_left`：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
 : x = y
-/
theorem ext_iff_inner_left {x y : E} : x = y ↔ ∀ v, ⟪v, x⟫ = ⟪v, y⟫ :=
  ⟨fun h _ ↦ h ▸ rfl, ext_inner_left 𝕜⟩
/-
**ext_inner_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_inner_right {x y : E} (h : forall v, ⟪x, v⟫ = ⟪y, v⟫) : x = y
参数：h : forall v, ⟪x, v⟫ = ⟪y, v⟫。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
-/
theorem ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_left, sub_eq_zero, h (x - y)]
/-
**ext_iff_inner_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_iff_inner_right {x y : E} : x = y ↔ forall v, ⟪x, v⟫ = ⟪y, v⟫
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ext_inner_right`：ext_inner_right {x y : E} (h : forall v, ⟪x, v⟫ = ⟪y, v
⟫) : x = y
-/
theorem ext_iff_inner_right {x y : E} : x = y ↔ ∀ v, ⟪x, v⟫ = ⟪y, v⟫ :=
  ⟨fun h _ ↦ h ▸ rfl, ext_inner_right 𝕜⟩

variable {𝕜}
/-
**re_inner_self_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：re_inner_self_nonpos {x : E} : re ⟪x, x⟫ <= 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `RCLike.re_ofReal_pow`：re_ofReal_pow (a : Real) (n : Nat) : re ((a : K) ^
 n) = a ^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem re_inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 := by
  simp
/-
**re_inner_self_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：re_inner_self_pos {x : E} : 0 < re ⟪x, x⟫ ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `RCLike.re_ofReal_pow`：re_ofReal_pow (a : Real) (n : Nat) : re ((a : K) ^
 n) = a ^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma re_inner_self_pos {x : E} : 0 < re ⟪x, x⟫ ↔ x ≠ 0 := by
  simp [sq_pos_iff]

open scoped InnerProductSpace in
/-
**real_inner_self_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_self_nonpos {x : F} : ⟪x, x⟫_Real <= 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `re_inner_self_nonpos`：re_inner_self_nonpos {x : E} : re ⟪x, x⟫ <= 0 ↔ x 
= 0
-/
theorem real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 := re_inner_self_nonpos (𝕜 := ℝ)

open scoped InnerProductSpace in
/-
**real_inner_self_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_self_pos {x : F} : 0 < ⟪x, x⟫_Real ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `re_inner_self_pos`：re_inner_self_pos {x : E} : 0 < re ⟪x, x⟫ ↔ x != 0
-/
theorem real_inner_self_pos {x : F} : 0 < ⟪x, x⟫_ℝ ↔ x ≠ 0 := re_inner_self_pos (𝕜 := ℝ)

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
/-
**linearIndependent_of_ne_zero_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_of_ne_zero_of_inner_eq_zero {ι : Type*} {v : ι -> E} (hz
 : forall i, v i != 0) (ho : Pairwise fun i j => ⟪v i, v j⟫ = 0) : LinearIndepen
dent 𝕜 v
参数：hz : forall i, v i != 0；ho : Pairwise fun i j => ⟪v i, v j⟫ = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
A family of vectors is linearly independent if they are nonzero
and orthogonal.
-/
theorem linearIndependent_of_ne_zero_of_inner_eq_zero {ι : Type*} {v : ι → E} (hz : ∀ i, v i ≠ 0)
    (ho : Pairwise fun i j => ⟪v i, v j⟫ = 0) : LinearIndependent 𝕜 v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h' : g i * ⟪v i, v i⟫ = ⟪v i, ∑ j ∈ s, g j • v j⟫ := by
    rw [inner_sum]
    symm
    convert! Finset.sum_eq_single (M := 𝕜) i ?_ ?_
    · rw [inner_smul_right]
    · intro j _hj hji
      rw [inner_smul_right, ho hji.symm, mul_zero]
    · exact fun h => False.elim (h hi)
  simpa [hg, hz] using h'

end BasicProperties

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "IK" => @RCLike.I 𝕜 _

/-
**norm_eq_sqrt_re_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `InnerProductSpace.norm_sq_eq_re_inner`：∀ {𝕜 : Type u_4} {E : Type u_5} {
inst : RCLike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜
 E]   (x : E), ‖x‖ ^ 2 = RC…
-/
theorem norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫) :=
  calc
    ‖x‖ = √(‖x‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ = √(re ⟪x, x⟫) := congr_arg _ (norm_sq_eq_re_inner _)
/-
**norm_eq_sqrt_real_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫_Real
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_eq_sqrt_re_inner`：norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫
)
-/
theorem norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫_ℝ :=
  @norm_eq_sqrt_re_inner ℝ _ _ _ _ x
/-
**inner_self_eq_norm_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ‖x‖ * ‖x‖
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_sqrt_re_inner`：norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `inner_self_nonneg`：inner_self_nonneg {x : E} : 0 <= re ⟪x, x⟫
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
-/
theorem inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [@norm_eq_sqrt_re_inner 𝕜, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
    sqrt_mul_self inner_self_nonneg]
/-
**inner_self_eq_norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^ 2
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `inner_self_eq_norm_mul_norm`：inner_self_eq_norm_mul_norm (x : E) : re ⟪x
, x⟫ = ‖x‖ * ‖x‖
-/
theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^ 2 := by
  rw [pow_two, inner_self_eq_norm_mul_norm]
/-
**real_inner_self_eq_norm_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_self_eq_norm_mul_norm (x : F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_self_eq_norm_mul_norm`：inner_self_eq_norm_mul_norm (x : E) : re ⟪x
, x⟫ = ‖x‖ * ‖x‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
-/
theorem real_inner_self_eq_norm_mul_norm (x : F) : ⟪x, x⟫_ℝ = ‖x‖ * ‖x‖ := by
  have h := @inner_self_eq_norm_mul_norm ℝ F _ _ _ x
  simpa using h
/-
**real_inner_self_eq_norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_Real = ‖x‖ ^ 2
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
-/
theorem real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := by
  rw [pow_two, real_inner_self_eq_norm_mul_norm]

/-- Expand the square -/
/-
**norm_add_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_eq_norm_mul_norm`：inner_self_eq_norm_mul_norm (x : E) : re ⟪x
, x⟫ = ‖x‖ * ‖x‖
· 使用定理 `inner_add_add_self`：inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, 
x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.conj_re`：conj_re (z : K) : re (conj z) = re z

--- 原说明 ---
Expand the square
-/
theorem norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  repeat' rw [sq (M := ℝ), ← @inner_self_eq_norm_mul_norm 𝕜]
  rw [inner_add_add_self, two_mul]
  simp only [add_assoc, add_left_inj, add_right_inj, map_add]
  rw [← inner_conj_symm, conj_re]

alias norm_add_pow_two := norm_add_sq

/-- Expand the square -/
/-
**norm_add_sq_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_add_sq_real (x y : F) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_Real + ‖y‖
 ^ 2
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `norm_add_sq`：norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, 
y⟫ + ‖y‖ ^ 2

--- 原说明 ---
Expand the square
-/
theorem norm_add_sq_real (x y : F) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 := by
  have h := @norm_add_sq ℝ _ _ _ _ x y
  simpa using h

alias norm_add_pow_two_real := norm_add_sq_real

/-- Expand the square -/
/-
**norm_add_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_add_mul_self (x y : E) : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * re ⟪x, y
⟫ + ‖y‖ * ‖y‖
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `norm_add_sq`：norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, 
y⟫ + ‖y‖ ^ 2

--- 原说明 ---
Expand the square
-/
theorem norm_add_mul_self (x y : E) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by
  repeat' rw [← sq (M := ℝ)]
  exact norm_add_sq _ _

/-- Expand the square -/
/-
**norm_add_mul_self_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_add_mul_self_real (x y : F) : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * ⟪x,
 y⟫_Real + ‖y‖ * ‖y‖
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `norm_add_mul_self`：norm_add_mul_self (x y : E) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖

--- 原说明 ---
Expand the square
-/
theorem norm_add_mul_self_real (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ := by
  have h := @norm_add_mul_self ℝ _ _ _ _ x y
  simpa using h

/-- Expand the square -/
/-
**norm_sub_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `norm_add_sq`：norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, 
y⟫ + ‖y‖ ^ 2
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)

--- 原说明 ---
Expand the square
-/
theorem norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  rw [sub_eq_add_neg, @norm_add_sq 𝕜 _ _ _ _ x (-y), norm_neg, inner_neg_right, map_neg, mul_neg,
    sub_eq_add_neg]

alias norm_sub_pow_two := norm_sub_sq

/-- Expand the square -/
/-
**norm_sub_sq_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_sq_real (x y : F) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_Real + ‖y‖
 ^ 2
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_sub_sq`：norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, 
y⟫ + ‖y‖ ^ 2

--- 原说明 ---
Expand the square
-/
theorem norm_sub_sq_real (x y : F) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 :=
  @norm_sub_sq ℝ _ _ _ _ _ _

alias norm_sub_pow_two_real := norm_sub_sq_real

/-- Expand the square -/
/-
**norm_sub_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_mul_self (x y : E) : ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * re ⟪x, y
⟫ + ‖y‖ * ‖y‖
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `norm_sub_sq`：norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, 
y⟫ + ‖y‖ ^ 2

--- 原说明 ---
Expand the square
-/
theorem norm_sub_mul_self (x y : E) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by
  repeat' rw [← sq (M := ℝ)]
  exact norm_sub_sq _ _

/-- Expand the square -/
/-
**norm_sub_mul_self_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_mul_self_real (x y : F) : ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * ⟪x,
 y⟫_Real + ‖y‖ * ‖y‖
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `norm_sub_mul_self`：norm_sub_mul_self (x y : E) : ‖x - y‖ * ‖x - y‖ = ‖x‖
 * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖

--- 原说明 ---
Expand the square
-/
theorem norm_sub_mul_self_real (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ := by
  have h := @norm_sub_mul_self ℝ _ _ _ _ x y
  simpa using h

/-- Cauchy–Schwarz inequality with norm -/
/-
**norm_inner_le_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_sqrt_re_inner`：norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫
)
· 使用定理 `InnerProductSpace.Core.norm_inner_le_norm`：norm_inner_le_norm (x y : F) 
: ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖

--- 原说明 ---
Cauchy–Schwarz inequality with norm
-/
theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) x, norm_eq_sqrt_re_inner (𝕜 := 𝕜) y]
  let : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  exact InnerProductSpace.Core.norm_inner_le_norm x y
/-
**nnnorm_inner_le_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ <= ‖x‖₊ * ‖y‖₊
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
-/
theorem nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ ≤ ‖x‖₊ * ‖y‖₊ :=
  norm_inner_le_norm x y
/-
**re_inner_le_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：re_inner_le_norm (x y : E) : re ⟪x, y⟫ <= ‖x‖ * ‖y‖
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `RCLike.re_le_norm`：re_le_norm (z : K) : re z <= ‖z‖
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
-/
theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
  le_trans (re_le_norm ⟪x, y⟫) (norm_inner_le_norm x y)

/-- Cauchy–Schwarz inequality with norm -/
/-
**abs_real_inner_le_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_Real| <= ‖x‖ * ‖y‖
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖

--- 原说明 ---
Cauchy–Schwarz inequality with norm
-/
theorem abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ :=
  (Real.norm_eq_abs _).ge.trans (norm_inner_le_norm x y)

/-- Cauchy–Schwarz inequality with norm -/
/-
**real_inner_le_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_le_norm (x y : F) : ⟪x, y⟫_Real <= ‖x‖ * ‖y‖
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `abs_real_inner_le_norm`：abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_Real|
 <= ‖x‖ * ‖y‖

--- 原说明 ---
Cauchy–Schwarz inequality with norm
-/
theorem real_inner_le_norm (x y : F) : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ :=
  le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
/-
**inner_eq_zero_of_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inner_eq_zero_of_left {x : E} (y : E) (h : ‖x‖ = 0) : ⟪x, y⟫_𝕜 = 0
参数：y : E；h : ‖x‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
lemma inner_eq_zero_of_left {x : E} (y : E) (h : ‖x‖ = 0) : ⟪x, y⟫_𝕜 = 0 := by
  rw [← norm_eq_zero]
  refine le_antisymm ?_ (by positivity)
  exact norm_inner_le_norm _ _ |>.trans <| by simp [h]
/-
**inner_eq_zero_of_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inner_eq_zero_of_right (x : E) {y : E} (h : ‖y‖ = 0) : ⟪x, y⟫_𝕜 = 0
参数：x : E；h : ‖y‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0
· 使用引理 `inner_eq_zero_of_left`：inner_eq_zero_of_left {x : E} (y : E) (h : ‖x‖ = 
0) : ⟪x, y⟫_𝕜 = 0
-/
lemma inner_eq_zero_of_right (x : E) {y : E} (h : ‖y‖ = 0) : ⟪x, y⟫_𝕜 = 0 := by
  rw [inner_eq_zero_symm, inner_eq_zero_of_left _ h]

variable (𝕜)

include 𝕜 in
/-
**parallelogram_law_with_norm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelogram_law_with_norm_mul (x y : E) : ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * 
‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_eq_norm_mul_norm`：inner_self_eq_norm_mul_norm (x : E) : re ⟪x
, x⟫ = ‖x‖ * ‖x‖
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
· 使用定理 `parallelogram_law`：parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y
, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem parallelogram_law_with_norm_mul (x y : E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  simp only [← @inner_self_eq_norm_mul_norm 𝕜]
  rw [← re.map_add, parallelogram_law, two_mul, two_mul]
  simp only [re.map_add]

include 𝕜 in
/-
**parallelogram_law_with_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelogram_law_with_norm (x y : E) : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖
x‖ ^ 2 + ‖y‖ ^ 2)
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `parallelogram_law_with_norm_mul`：parallelogram_law_with_norm_mul (x y : 
E) : ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem parallelogram_law_with_norm (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  simp_rw [sq, parallelogram_law_with_norm_mul 𝕜 x y]

include 𝕜 in
/-
**parallelogram_law_with_nnnorm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelogram_law_with_nnnorm_mul (x y : E) : ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y
‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊)
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `parallelogram_law_with_norm_mul`：parallelogram_law_with_norm_mul (x y : 
E) : ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)
-/
theorem parallelogram_law_with_nnnorm_mul (x y : E) :
    ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊) :=
  Subtype.ext <| parallelogram_law_with_norm_mul 𝕜 x y

include 𝕜 in
/-
**parallelogram_law_with_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：parallelogram_law_with_nnnorm (x y : E) : ‖x + y‖₊ ^ 2 + ‖x - y‖₊ ^ 2 = 2 
* (‖x‖₊ ^ 2 + ‖y‖₊ ^ 2)
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `parallelogram_law_with_nnnorm_mul`：parallelogram_law_with_nnnorm_mul (x 
y : E) : ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖
y‖₊)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem parallelogram_law_with_nnnorm (x y : E) :
    ‖x + y‖₊ ^ 2 + ‖x - y‖₊ ^ 2 = 2 * (‖x‖₊ ^ 2 + ‖y‖₊ ^ 2) := by
  simp_rw [sq, parallelogram_law_with_nnnorm_mul 𝕜 x y]

variable {𝕜}

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
/-
**re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two** 是 
Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two 
(x y : E) : re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_add_mul_self`：norm_add_mul_self (x y : E) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Polarization identity: The real part of the inner product, in terms of the norm.
-/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 := by
  rw [@norm_add_mul_self 𝕜]
  ring

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
/-
**re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two** 是 
Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two 
(x y : E) : re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_sub_mul_self`：norm_sub_mul_self (x y : E) : ‖x - y‖ * ‖x - y‖ = ‖x‖
 * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Polarization identity: The real part of the inner product, in terms of the norm.
-/
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 := by
  rw [@norm_sub_mul_self 𝕜]
  ring

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
/-
**re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) : r
e ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_add_mul_self`：norm_add_mul_self (x y : E) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖
· 使用定理 `norm_sub_mul_self`：norm_sub_mul_self (x y : E) : ‖x - y‖ * ‖x - y‖ = ‖x‖
 * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
Polarization identity: The real part of the inner product, in terms of the norm.
-/
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4 := by
  rw [@norm_add_mul_self 𝕜, @norm_sub_mul_self 𝕜]
  ring

/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
/-
**im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four** 是
 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
 (x y : E) : im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • y‖ * ‖x + IK •
 y‖) / 4
参数：x y : E。
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
· 使用定理 `norm_sub_mul_self`：norm_sub_mul_self (x y : E) : ‖x - y‖ * ‖x - y‖ = ‖x‖
 * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `RCLike.I_mul_re`：I_mul_re (z : K) : re (I * z) = -im z
· 使用定理 `norm_add_mul_self`：norm_add_mul_self (x y : E) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
Polarization identity: The imaginary part of the inner product, in terms of the 
norm.
-/
theorem im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (x y : E) :
    im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • y‖ * ‖x + IK • y‖) / 4 := by
  simp only [@norm_add_mul_self 𝕜, @norm_sub_mul_self 𝕜, inner_smul_right, I_mul_re]
  ring

/-- Polarization identity: The inner product, in terms of the norm. -/
/-
**inner_eq_sum_norm_sq_div_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_sum_norm_sq_div_four (x y : E) : ⟪x, y⟫ = ((‖x + y‖ : 𝕜) ^ 2 - (‖
x - y‖ : 𝕜) ^ 2 + ((‖x - IK • y‖ : 𝕜) ^ 2 - (‖x + IK • y‖ : 𝕜) ^ 2) * IK) / 4
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four`：re_inner_e
q_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) : re ⟪x, y⟫ = (‖x +
 y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4
· 使用定理 `im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_fo
ur`：im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (
x y : E) : im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : K) = r / 
s
· 使用定理 `algebraMap.coe_sub`：coe_sub (a b : R) : (↑(a - b : R) : A) = ↑a - ↑b
· 使用定理 `algebraMap.coe_mul`：coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b
· 使用定理 `RCLike.ofReal_ofNat`：ofReal_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) 
: Real) : K) = ofNat(n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Polarization identity: The inner product, in terms of the norm.
-/
theorem inner_eq_sum_norm_sq_div_four (x y : E) :
    ⟪x, y⟫ = ((‖x + y‖ : 𝕜) ^ 2 - (‖x - y‖ : 𝕜) ^ 2 +
              ((‖x - IK • y‖ : 𝕜) ^ 2 - (‖x + IK • y‖ : 𝕜) ^ 2) * IK) / 4 := by
  rw [← re_add_im ⟪x, y⟫, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
  push_cast
  simp only [sq, ← mul_div_right_comm, ← add_div]

/-- Polarization identity: The real inner product, in terms of the norm. -/
/-
**real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two** 
是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_tw
o (x y : F) : ⟪x, y⟫_Real = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_to_real`：re_to_real {x : Real} : reR x = x
· 使用定理 `re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_tw
o`：re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x 
y : E) : re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖…

--- 原说明 ---
Polarization identity: The real inner product, in terms of the norm.
-/
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

/-- Polarization identity: The real inner product, in terms of the norm. -/
/-
**real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two** 
是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_tw
o (x y : F) : ⟪x, y⟫_Real = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_to_real`：re_to_real {x : Real} : reR x = x
· 使用定理 `re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_tw
o`：re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x 
y : E) : re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖…

--- 原说明 ---
Polarization identity: The real inner product, in terms of the norm.
-/
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
/-
**norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x +
 y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0
参数：x y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_add_mul_self`：norm_add_mul_self (x y : E) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖
· 使用定理 `add_right_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd 
G] {a b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Pythagorean theorem, if-and-only-if vector inner product form.
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [@norm_add_mul_self ℝ, add_right_cancel_iff, add_eq_left, mul_eq_zero]
  simp

/-- Pythagorean theorem, if-and-if vector inner product form using square roots. -/
/-
**norm_add_eq_sqrt_iff_real_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_add_eq_sqrt_iff_real_inner_eq_zero {x y : F} : ‖x + y‖ = √(‖x‖ * ‖x‖ 
+ ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_Real = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`：norm_add_sq_e
q_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Real.sqrt_eq_iff_mul_self_eq`：sqrt_eq_iff_mul_self_eq (hx : 0 <= x) (hy 
: 0 <= y) : √x = y ↔ x = y * y
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Pythagorean theorem, if-and-if vector inner product form using square roots.
-/
theorem norm_add_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x + y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [← norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm, sqrt_eq_iff_mul_self_eq,
    eq_comm] <;> positivity

/-- Pythagorean theorem, vector inner product form. -/
/-
**norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ 
= 0) : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖
参数：x y : E；h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_add_mul_self`：norm_add_mul_self (x y : E) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖
· 使用定理 `add_right_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd 
G] {a b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.zero_re`：zero_re : re (0 : K) = (0 : Real)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pythagorean theorem, vector inner product form.
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ := by
  rw [@norm_add_mul_self 𝕜, add_right_cancel_iff, add_eq_left, mul_eq_zero]
  apply Or.inr
  simp only [h, zero_re]

/-- Pythagorean theorem, vector inner product form. -/
/-
**norm_add_sq_eq_norm_sq_add_norm_sq_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_Real = 0) : 
‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖
参数：h : ⟪x, y⟫_Real = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`：norm_add_sq_e
q_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0

--- 原说明 ---
Pythagorean theorem, vector inner product form.
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
/-
**norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x -
 y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0
参数：x y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_sub_mul_self`：norm_sub_mul_self (x y : E) : ‖x - y‖ * ‖x - y‖ = ‖x‖
 * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖
· 使用定理 `add_right_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd 
G] {a b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form.
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [@norm_sub_mul_self ℝ, add_right_cancel_iff, sub_eq_add_neg, add_eq_left, neg_eq_zero,
    mul_eq_zero]
  simp

/-- Pythagorean theorem, subtracting vectors, if-and-if vector inner product form using square
roots. -/
/-
**norm_sub_eq_sqrt_iff_real_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_eq_sqrt_iff_real_inner_eq_zero {x y : F} : ‖x - y‖ = √(‖x‖ * ‖x‖ 
+ ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_Real = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`：norm_sub_sq_e
q_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x - y‖ * ‖x - y‖ = ‖x‖
 * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Real.sqrt_eq_iff_mul_self_eq`：sqrt_eq_iff_mul_self_eq (hx : 0 <= x) (hy 
: 0 <= y) : √x = y ↔ x = y * y
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Pythagorean theorem, subtracting vectors, if-and-if vector inner product form us
ing square
roots.
-/
theorem norm_sub_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x - y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm, sqrt_eq_iff_mul_self_eq,
    eq_comm] <;> positivity

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
/-
**norm_sub_sq_eq_norm_sq_add_norm_sq_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_Real = 0) : 
‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖
参数：h : ⟪x, y⟫_Real = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`：norm_sub_sq_e
q_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x - y‖ * ‖x - y‖ = ‖x‖
 * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0

--- 原说明 ---
Pythagorean theorem, subtracting vectors, vector inner product
form.
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
/-
**real_inner_add_sub_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_Real = 0 ↔ ‖x‖ =
 ‖y‖
参数：x y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_inj_of_nonneg`：mul_self_inj_of_nonneg {α : Type*} [CommRing α] 
[NoZeroDivisors α] [PartialOrder α] [IsStrictOrderedRing α] {a b : α} (a0 : 0 <=
 a) (b0 : 0 …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `inner_self_eq_norm_mul_norm`：inner_self_eq_norm_mul_norm (x : E) : re ⟪x
, x⟫ = ‖x‖ * ‖x‖

--- 原说明 ---
The sum and difference of two vectors are orthogonal if and only
if they have the same norm.
-/
theorem real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_ℝ = 0 ↔ ‖x‖ = ‖y‖ := by
  conv_rhs => rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [← @inner_self_eq_norm_mul_norm ℝ, inner_add_left, inner_sub_right, real_inner_comm y x,
    sub_eq_zero, re_to_real]
  grind

/-- Given two orthogonal vectors, their sum and difference have equal norms. -/
/-
**norm_sub_eq_norm_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ‖w - v‖ = ‖w + v‖
参数：h : ⟪v, w⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_inj_of_nonneg`：mul_self_inj_of_nonneg {α : Type*} [CommRing α] 
[NoZeroDivisors α] [PartialOrder α] [IsStrictOrderedRing α] {a b : α} (a0 : 0 <=
 a) (b0 : 0 …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_self_eq_norm_mul_norm`：inner_self_eq_norm_mul_norm (x : E) : re ⟪x
, x⟫ = ‖x‖ * ‖x‖
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_re_symm`：inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫
· 使用定理 `RCLike.zero_re`：zero_re : re (0 : K) = (0 : Real)
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given two orthogonal vectors, their sum and difference have equal norms.
-/
theorem norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ‖w - v‖ = ‖w + v‖ := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [h, ← @inner_self_eq_norm_mul_norm 𝕜, sub_neg_eq_add, sub_zero, map_sub, zero_re,
    zero_sub, add_zero, map_add, inner_add_right, inner_sub_left, inner_sub_right, inner_re_symm,
    zero_add]

/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
/-
**abs_real_inner_div_norm_mul_norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_real_inner_div_norm_mul_norm_le_one (x y : F) : |⟪x, y⟫_Real / (‖x‖ * 
‖y‖)| <= 1
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `abs_real_inner_le_norm`：abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_Real|
 <= ‖x‖ * ‖y‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1.
-/
theorem abs_real_inner_div_norm_mul_norm_le_one (x y : F) : |⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)| ≤ 1 := by
  rw [abs_div, abs_mul, abs_norm, abs_norm]
  exact div_le_one_of_le₀ (abs_real_inner_le_norm x y) (by positivity)

/-- The inner product of a vector with a multiple of itself. -/
/-
**real_inner_smul_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_smul_self_left (x : F) (r : Real) : ⟪r • x, x⟫_Real = r * (‖x‖ 
* ‖x‖)
参数：x : F；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖

--- 原说明 ---
The inner product of a vector with a multiple of itself.
-/
theorem real_inner_smul_self_left (x : F) (r : ℝ) : ⟪r • x, x⟫_ℝ = r * (‖x‖ * ‖x‖) := by
  rw [real_inner_smul_left, ← real_inner_self_eq_norm_mul_norm]

/-- The inner product of a vector with a multiple of itself. -/
/-
**real_inner_smul_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_smul_self_right (x : F) (r : Real) : ⟪x, r • x⟫_Real = r * (‖x‖
 * ‖x‖)
参数：x : F；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖

--- 原说明 ---
The inner product of a vector with a multiple of itself.
-/
theorem real_inner_smul_self_right (x : F) (r : ℝ) : ⟪x, r • x⟫_ℝ = r * (‖x‖ * ‖x‖) := by
  rw [inner_smul_right, ← real_inner_self_eq_norm_mul_norm]

/-- The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences. -/
/-
**inner_sum_smul_sum_smul_of_sum_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type*} {s₁ : Finset ι₁} {w₁ :
 ι₁ -> Real} (v₁ : ι₁ -> F) (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : Finset
 ι₂} {w₂ : ι₂ -> Real} (v₂ : ι₂ -> F) (h₂ : ∑ i in s₂, w₂ i = 0) : ⟪∑ i₁ in s₁, 
w₁ i₁ • v₁ i₁, ∑ i₂ in s₂, w₂ i₂ • v₂ i₂⟫_Real = (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁
 * w₂ i₂ * (‖v₁ i₁ - v₂ i₂‖ * ‖v₁ i₁ - v₂ i₂‖)) / 2
参数：v₁ : ι₁ -> F；h₁ : ∑ i in s₁, w₁ i = 0；v₂ : ι₂ -> F；h₂ : ∑ i in s₂, w₂ i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `real_inner_smul_right`：real_inner_smul_right (x y : F) (r : Real) : ⟪x, 
r • y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_
two`：real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
 (x y : F) : ⟪x, y⟫_Real = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x …
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_sub_left_distrib`：mul_sub_left_distrib (a b c : α) : a * (b - c) = a
 * b - a * c
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences.
-/
theorem inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type*} {s₁ : Finset ι₁} {w₁ : ι₁ → ℝ}
    (v₁ : ι₁ → F) (h₁ : ∑ i ∈ s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : Finset ι₂} {w₂ : ι₂ → ℝ}
    (v₂ : ι₂ → F) (h₂ : ∑ i ∈ s₂, w₂ i = 0) :
    ⟪∑ i₁ ∈ s₁, w₁ i₁ • v₁ i₁, ∑ i₂ ∈ s₂, w₂ i₂ • v₂ i₂⟫_ℝ =
      (-∑ i₁ ∈ s₁, ∑ i₂ ∈ s₂, w₁ i₁ * w₂ i₂ * (‖v₁ i₁ - v₂ i₂‖ * ‖v₁ i₁ - v₂ i₂‖)) / 2 := by
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ← div_sub_div_same,
    add_div, mul_sub_left_distrib, left_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h₁, h₂, zero_mul,
    mul_zero, Finset.sum_const_zero, zero_add, zero_sub, Finset.mul_sum, neg_div,
    Finset.sum_div, mul_div_assoc, mul_assoc]

end Norm_Seminormed

section Norm

open scoped InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Formula for the distance between the images of two nonzero points under an inversion with center
zero. See also `EuclideanGeometry.dist_inversion_inversion` for inversions around a general
point. -/
/-
**dist_div_norm_sq_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_div_norm_sq_smul {x y : F} (hx : x != 0) (hy : y != 0) (R : Real) : d
ist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) = R ^ 2 / (‖x‖ * ‖y‖) * dist x y
参数：hx : x != 0；hy : y != 0；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `norm_sub_mul_self_real`：norm_sub_mul_self_real (x y : F) : ‖x - y‖ * ‖x 
- y‖ = ‖x‖ * ‖x‖ - 2 * ⟪x, y⟫_Real + ‖y‖ * ‖y‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
（共 100 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for the distance between the images of two nonzero points under an inver
sion with center
zero. See also `EuclideanGeometry.dist_inversion_inversion` for inversions aroun
d a general
point.
-/
theorem dist_div_norm_sq_smul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (R : ℝ) :
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) = R ^ 2 / (‖x‖ * ‖y‖) * dist x y :=
  calc
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) =
        √(‖(R / ‖x‖) ^ 2 • x - (R / ‖y‖) ^ 2 • y‖ ^ 2) := by
      rw [dist_eq_norm, sqrt_sq (norm_nonneg _)]
    _ = √((R ^ 2 / (‖x‖ * ‖y‖)) ^ 2 * ‖x - y‖ ^ 2) :=
      congr_arg (√·) <| by
        simp [field, sq, norm_sub_mul_self_real, norm_smul, real_inner_smul_left, inner_smul_right,
          Real.norm_of_nonneg (mul_self_nonneg _), -mul_eq_mul_left_iff]
        ring
    _ = R ^ 2 / (‖x‖ * ‖y‖) * dist x y := by
      rw [sqrt_mul, sqrt_sq, sqrt_sq, dist_eq_norm] <;> positivity

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value 1. -/
/-
**norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r :
 𝕜} (hx : x != 0) (hr : r != 0) : ‖⟪x, r • x⟫‖ / (‖x‖ * ‖r • x‖) = 1
参数：hx : x != 0；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_re_eq_norm`：inner_self_re_eq_norm (x : E) : re ⟪x, x⟫ = ‖⟪x, 
x⟫‖
· 使用定理 `inner_self_eq_norm_mul_norm`：inner_self_eq_norm_mul_norm (x : E) : re ⟪x
, x⟫ = ‖x‖ * ‖x‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1

--- 原说明 ---
The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value 1.
-/
theorem norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : 𝕜} (hx : x ≠ 0)
    (hr : r ≠ 0) : ‖⟪x, r • x⟫‖ / (‖x‖ * ‖r • x‖) = 1 := by
  have hx' : ‖x‖ ≠ 0 := by simp [hx]
  have hr' : ‖r‖ ≠ 0 := by simp [hr]
  rw [inner_smul_right, norm_mul, ← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm, norm_smul]
  rw [← mul_assoc, ← div_div, mul_div_cancel_right₀ _ hx', ← div_div, mul_comm,
    mul_div_cancel_right₀ _ hr', div_self hx']

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value 1. -/
/-
**abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : F} 
{r : Real} (hx : x != 0) (hr : r != 0) : |⟪x, r • x⟫_Real| / (‖x‖ * ‖r • x‖) = 1
参数：hx : x != 0；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul`：norm_inne
r_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : 𝕜} (hx : x != 
0) (hr : r != 0) : ‖⟪x, r • x⟫‖ / (‖x‖ * ‖r • x‖) =…

--- 原说明 ---
The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value 1.
-/
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : F} {r : ℝ}
    (hx : x ≠ 0) (hr : r ≠ 0) : |⟪x, r • x⟫_ℝ| / (‖x‖ * ‖r • x‖) = 1 :=
  norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
/-
**real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : Rea
l} (hx : x != 0) (hr : 0 < r) : ⟪x, r • x⟫_Real / (‖x‖ * ‖r • x‖) = 1
参数：hx : x != 0；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_smul_self_right`：real_inner_smul_self_right (x : F) (r : Real
) : ⟪x, r • x⟫_Real = r * (‖x‖ * ‖x‖)
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_ne_zero`：mul_self_ne_zero : a * a != 0 ↔ a != 0
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0

--- 原说明 ---
The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1.
-/
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : 0 < r) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = 1 := by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ‖x‖, mul_comm _ |r|,
    mul_assoc, abs_of_nonneg hr.le, div_self]
  exact mul_ne_zero hr.ne' (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
/-
**real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {x : F} {r :
 Real} (hx : x != 0) (hr : r < 0) : ⟪x, r • x⟫_Real / (‖x‖ * ‖r • x‖) = -1
参数：hx : x != 0；hr : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_smul_self_right`：real_inner_smul_self_right (x : F) (r : Real
) : ⟪x, r • x⟫_Real = r * (‖x‖ * ‖x‖)
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `div_neg_eq_neg_div`：div_neg_eq_neg_div (a b : R) : b / -a = -(b / a)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_ne_zero`：mul_self_ne_zero : a * a != 0 ↔ a != 0
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0

--- 原说明 ---
The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1.
-/
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : r < 0) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = -1 := by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ‖x‖, mul_comm _ |r|,
    mul_assoc, abs_of_neg hr, neg_mul, div_neg_eq_neg_div, div_self]
  exact mul_ne_zero hr.ne (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

variable (𝕜) in
/-
**norm_inner_eq_norm_tfae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inner_eq_norm_tfae (x y : E) : List.TFAE [‖⟪x, y⟫‖ = ‖x‖ * ‖y‖, x = 0
 ∨ y = (⟪x, y⟫ / ⟪x, x⟫) • x, x = 0 ∨ exists r : 𝕜, y = r • x, x = 0 ∨ y in 𝕜 ∙ 
x]
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `InnerProductSpace.Core.normSq_eq_zero`：normSq_eq_zero {x : F} : normSqF 
x = 0 ↔ x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.cauchy_schwarz_aux`：cauchy_schwarz_aux (x y : F) 
: normSqF (⟪x, y⟫ • x - ⟪x, x⟫ • y) = normSqF x * (normSqF x * normSqF y - ‖⟪x, 
y⟫‖ ^ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `InnerProductSpace.norm_sq_eq_re_inner`：∀ {𝕜 : Type u_4} {E : Type u_5} {
inst : RCLike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜
 E]   (x : E), ‖x‖ ^ 2 = RC…
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 54 条，此处仅展示前 30 条）
-/
theorem norm_inner_eq_norm_tfae (x y : E) :
    List.TFAE [‖⟪x, y⟫‖ = ‖x‖ * ‖y‖,
      x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫) • x,
      x = 0 ∨ ∃ r : 𝕜, y = r • x,
      x = 0 ∨ y ∈ 𝕜 ∙ x] := by
  tfae_have 1 → 2 := by
    refine fun h => or_iff_not_imp_left.2 fun hx₀ => ?_
    have : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hx₀)
    rw [← sq_eq_sq₀, mul_pow, ← mul_right_inj' this, eq_comm, ← sub_eq_zero, ← mul_sub] at h <;>
      try positivity
    simp only [@norm_sq_eq_re_inner 𝕜] at h
    let : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
    erw [← InnerProductSpace.Core.cauchy_schwarz_aux (𝕜 := 𝕜) (F := E)] at h
    rw [InnerProductSpace.Core.normSq_eq_zero, sub_eq_zero] at h
    rw [div_eq_inv_mul, mul_smul, h, inv_smul_smul₀]
    rwa [inner_self_ne_zero]
  tfae_have 2 → 3 := fun h => h.imp_right fun h' => ⟨_, h'⟩
  tfae_have 3 → 1 := by
    rintro (rfl | ⟨r, rfl⟩) <;>
    simp [inner_smul_right, norm_smul, inner_self_eq_norm_sq_to_K,
      sq, mul_left_comm]
  tfae_have 3 ↔ 4 := by simp only [Submodule.mem_span_singleton, eq_comm]
  tfae_finish

/-- If the inner product of two vectors is equal to the product of their norms, then the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
/-
**norm_inner_eq_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inner_eq_norm_iff {x y : E} (hx₀ : x != 0) (hy₀ : y != 0) : ‖⟪x, y⟫‖ 
= ‖x‖ * ‖y‖ ↔ exists r : 𝕜, r != 0 ∧ y = r • x
参数：hx₀ : x != 0；hy₀ : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `norm_inner_eq_norm_tfae`：norm_inner_eq_norm_tfae (x y : E) : List.TFAE [
‖⟪x, y⟫‖ = ‖x‖ * ‖y‖, x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫) • x, x = 0 ∨ exists r : 𝕜, y
 = r • x, x =…
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the inner product of two vectors is equal to the product of their norms, then
 the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ‖
x‖ * ‖y‖`.
-/
theorem norm_inner_eq_norm_iff {x y : E} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
  calc
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ r : 𝕜, y = r • x :=
      (norm_inner_eq_norm_tfae 𝕜 x y).out 0 2
    _ ↔ ∃ r : 𝕜, y = r • x := or_iff_right hx₀
    _ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
      ⟨fun ⟨r, h⟩ => ⟨r, fun hr₀ => hy₀ <| h.symm ▸ smul_eq_zero.2 <| Or.inl hr₀, h⟩,
        fun ⟨r, _hr₀, h⟩ => ⟨r, h⟩⟩

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
/-
**norm_inner_div_norm_mul_norm_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inner_div_norm_mul_norm_eq_one_iff (x y : E) : ‖⟪x, y⟫ / (‖x‖ * ‖y‖)‖
 = 1 ↔ x != 0 ∧ exists r : 𝕜, r != 0 ∧ y = r • x
参数：x y : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_inner_eq_norm_iff`：norm_inner_eq_norm_iff {x y : E} (hx₀ : x != 0) 
(hy₀ : y != 0) : ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ exists r : 𝕜, r != 0 ∧ y = r • x
· 使用定理 `eq_of_div_eq_one`：eq_of_div_eq_one (h : a / b = 1) : a = b
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `RCLike.norm_ofReal`：norm_ofReal (r : Real) : ‖(r : K)‖ = |r|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul`：norm_inne
r_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : 𝕜} (hx : x != 
0) (hr : r != 0) : ‖⟪x, r • x⟫‖ / (‖x‖ * ‖r • x‖) =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz.
-/
theorem norm_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
    ‖⟪x, y⟫ / (‖x‖ * ‖y‖)‖ = 1 ↔ x ≠ 0 ∧ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x := by
  constructor
  · intro h
    have hx₀ : x ≠ 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y ≠ 0 := fun h₀ => by simp [h₀] at h
    refine ⟨hx₀, (norm_inner_eq_norm_iff hx₀ hy₀).1 <| eq_of_div_eq_one ?_⟩
    simpa using h
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    simp only [norm_div, norm_mul, norm_ofReal, abs_norm]
    exact norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
/-
**abs_real_inner_div_norm_mul_norm_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) : |⟪x, y⟫_Real / (‖x
‖ * ‖y‖)| = 1 ↔ x != 0 ∧ exists r : Real, r != 0 ∧ y = r • x
参数：x y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_inner_div_norm_mul_norm_eq_one_iff`：norm_inner_div_norm_mul_norm_eq
_one_iff (x y : E) : ‖⟪x, y⟫ / (‖x‖ * ‖y‖)‖ = 1 ↔ x != 0 ∧ exists r : 𝕜, r != 0 
∧ y = r • x

--- 原说明 ---
The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz.
-/
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    |⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)| = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r ≠ 0 ∧ y = r • x :=
  @norm_inner_div_norm_mul_norm_eq_one_iff ℝ F _ _ _ x y
/-
**inner_eq_norm_mul_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_norm_mul_iff_div {x y : E} (h₀ : x != 0) : ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖
y‖ ↔ (‖y‖ / ‖x‖ : 𝕜) • x = y
参数：h₀ : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `norm_inner_eq_norm_tfae`：norm_inner_eq_norm_tfae (x y : E) : List.TFAE [
‖⟪x, y⟫‖ = ‖x‖ * ‖y‖, x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫) • x, x = 0 ∨ exists r : 𝕜, y
 = r • x, x =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 62 条，此处仅展示前 30 条）
-/
theorem inner_eq_norm_mul_iff_div {x y : E} (h₀ : x ≠ 0) :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ / ‖x‖ : 𝕜) • x = y := by
  have h₀' := h₀
  rw [← norm_ne_zero_iff, Ne, ← @ofReal_eq_zero 𝕜] at h₀'
  constructor <;> intro h
  · have : x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫ : 𝕜) • x :=
      ((norm_inner_eq_norm_tfae 𝕜 x y).out 0 1).1 (by simp [h])
    rw [this.resolve_left h₀, h]
    simp [norm_smul, mul_div_cancel_right₀ _ h₀']
  · conv_lhs => rw [← h, inner_smul_right, inner_self_eq_norm_sq_to_K]
    field

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `norm_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
/-
**inner_eq_norm_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_norm_mul_iff {x y : E} : ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x
 = (‖x‖ : 𝕜) • y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_eq_norm_mul_iff_div`：inner_eq_norm_mul_iff_div {x y : E} (h₀ : x !
= 0) : ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ / ‖x‖ : 𝕜) • x = y
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `inv_smul_eq_iff₀`：inv_smul_eq_iff₀ (ha : a != 0) {x y : β} : a⁻¹ • x = y
 ↔ x = a • y
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `RCLike.ofReal_eq_zero`：ofReal_eq_zero {x : Real} : (x : K) = 0 ↔ x = 0
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If the inner product of two vectors is equal to the product of their norms (i.e.
,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of ea
ch other. One form
of the equality case for Cauchy-Schwarz.
Compare `norm_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ 
= ‖x‖ * ‖y‖`.
-/
theorem inner_eq_norm_mul_iff {x y : E} :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y := by
  rcases eq_or_ne x 0 with (rfl | h₀)
  · simp
  · rw [inner_eq_norm_mul_iff_div h₀, div_eq_inv_mul, mul_smul, inv_smul_eq_iff₀]
    rwa [Ne, ofReal_eq_zero, norm_eq_zero]

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `norm_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
/-
**inner_eq_norm_mul_iff_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_Real = ‖x‖ * ‖y‖ ↔ ‖y‖ • x =
 ‖x‖ • y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_eq_norm_mul_iff`：inner_eq_norm_mul_iff {x y : E} : ⟪x, y⟫ = (‖x‖ :
 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y

--- 原说明 ---
If the inner product of two vectors is equal to the product of their norms (i.e.
,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of ea
ch other. One form
of the equality case for Cauchy-Schwarz.
Compare `norm_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ 
= ‖x‖ * ‖y‖`.
-/
theorem inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y :=
  inner_eq_norm_mul_iff

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
/-
**real_inner_div_norm_mul_norm_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_div_norm_mul_norm_eq_one_iff (x y : F) : ⟪x, y⟫_Real / (‖x‖ * ‖
y‖) = 1 ↔ x != 0 ∧ exists r : Real, 0 < r ∧ y = r • x
参数：x y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inner_eq_norm_mul_iff_div`：inner_eq_norm_mul_iff_div {x y : E} (h₀ : x !
= 0) : ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ / ‖x‖ : 𝕜) • x = y
· 使用定理 `eq_of_div_eq_one`：eq_of_div_eq_one (h : a / b = 1) : a = b
· 使用定理 `real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul`：real_inner_di
v_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : Real} (hx : x != 0) (h
r : 0 < r) : ⟪x, r • x⟫_Real / (‖x‖ * ‖r • x‖) …

--- 原说明 ---
The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other.
-/
theorem real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x := by
  constructor
  · intro h
    have hx₀ : x ≠ 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y ≠ 0 := fun h₀ => by simp [h₀] at h
    refine ⟨hx₀, ‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy₀) (norm_pos_iff.2 hx₀), ?_⟩
    exact ((inner_eq_norm_mul_iff_div hx₀).1 (eq_of_div_eq_one h)).symm
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
/-
**real_inner_div_norm_mul_norm_eq_neg_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) : ⟪x, y⟫_Real / (‖x‖
 * ‖y‖) = -1 ↔ x != 0 ∧ exists r : Real, r < 0 ∧ y = r • x
参数：x y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `real_inner_div_norm_mul_norm_eq_one_iff`：real_inner_div_norm_mul_norm_eq
_one_iff (x y : F) : ⟪x, y⟫_Real / (‖x‖ * ‖y‖) = 1 ↔ x != 0 ∧ exists r : Real, 0
 < r ∧ y = r • x
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `neg_surjective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Surj
ective Neg.neg
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b

--- 原说明 ---
The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other.
-/
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = -1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x := by
  rw [← neg_eq_iff_eq_neg, ← neg_div, ← inner_neg_right, ← norm_neg y,
    real_inner_div_norm_mul_norm_eq_one_iff, (@neg_surjective ℝ _).exists]
  refine Iff.rfl.and (exists_congr fun r => ?_)
  rw [neg_pos, neg_smul, neg_inj]

/-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
the equality case for Cauchy-Schwarz. -/
/-
**inner_eq_one_iff_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_one_iff_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 
⟪x, y⟫ = 1 ↔ x = y
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `inner_eq_norm_mul_iff`：inner_eq_norm_mul_iff {x y : E} : ⟪x, y⟫ = (‖x‖ :
 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y

--- 原说明 ---
If the inner product of two unit vectors is `1`, then the two vectors are equal.
 One form of
the equality case for Cauchy-Schwarz.
-/
theorem inner_eq_one_iff_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = 1 ↔ x = y := by
  convert inner_eq_norm_mul_iff (𝕜 := 𝕜) (E := E) <;> simp [hx, hy]

/-- If the inner product of two unit vectors is `-1`, then the two vectors are negations of each
other. -/
/-
**inner_eq_neg_one_iff_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_eq_neg_one_iff_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1
) : ⟪x, y⟫ = -1 ↔ x = -y
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `inner_eq_one_iff_of_norm_eq_one`：inner_eq_one_iff_of_norm_eq_one {x y : 
E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫ = 1 ↔ x = y
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If the inner product of two unit vectors is `-1`, then the two vectors are negat
ions of each
other.
-/
theorem inner_eq_neg_one_iff_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = -1 ↔ x = -y := by
  rw [← neg_eq_iff_eq_neg, ← inner_neg_right, inner_eq_one_iff_of_norm_eq_one hx (norm_neg y ▸ hy)]

/-- The inner product of two unit vectors is less than or equal to `1`. -/
/-
**real_inner_le_one_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_le_one_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
 ⟪x, y⟫_Real <= 1
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `real_inner_le_norm`：real_inner_le_norm (x y : F) : ⟪x, y⟫_Real <= ‖x‖ * 
‖y‖

--- 原说明 ---
The inner product of two unit vectors is less than or equal to `1`.
-/
theorem real_inner_le_one_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ ≤ 1 := by
  simpa [hx, hy] using real_inner_le_norm x y

/-- The inner product of two unit vectors is greater than or equal to `-1`. -/
/-
**neg_one_le_real_inner_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_one_le_real_inner_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 
1) : -1 <= ⟪x, y⟫_Real
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_le_of_abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Lin
earOrder G] [IsOrderedAddMonoid G] {a b : G}, |a| ≤ b → -b ≤ a
· 使用定理 `abs_real_inner_le_norm`：abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_Real|
 <= ‖x‖ * ‖y‖

--- 原说明 ---
The inner product of two unit vectors is greater than or equal to `-1`.
-/
theorem neg_one_le_real_inner_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -1 ≤ ⟪x, y⟫_ℝ := by
  simpa [hx, hy] using neg_le_of_abs_le (abs_real_inner_le_norm x y)

/-- If `x` and `y` are unit vectors, then `-1 ≤ ⟪x, y⟫ ≤ 1`. -/
/-
**real_inner_mem_Icc_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_mem_Icc_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) 
: ⟪x, y⟫_Real in Set.Icc (-1) 1
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_one_le_real_inner_of_norm_eq_one`：neg_one_le_real_inner_of_norm_eq_o
ne {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : -1 <= ⟪x, y⟫_Real
· 使用定理 `real_inner_le_one_of_norm_eq_one`：real_inner_le_one_of_norm_eq_one {x y 
: F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫_Real <= 1

--- 原说明 ---
If `x` and `y` are unit vectors, then `-1 ≤ ⟪x, y⟫ ≤ 1`.
-/
theorem real_inner_mem_Icc_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ ∈ Set.Icc (-1) 1 :=
  ⟨neg_one_le_real_inner_of_norm_eq_one hx hy, real_inner_le_one_of_norm_eq_one hx hy⟩
/-
**inner_self_eq_one_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_self_eq_one_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) : ⟪x, x⟫_𝕜 = 1
参数：hx : ‖x‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inner_eq_one_iff_of_norm_eq_one`：inner_eq_one_iff_of_norm_eq_one {x y : 
E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫ = 1 ↔ x = y
-/
theorem inner_self_eq_one_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) : ⟪x, x⟫_𝕜 = 1 :=
  (inner_eq_one_iff_of_norm_eq_one hx hx).mpr rfl
/-
**inner_lt_norm_mul_iff_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_lt_norm_mul_iff_real {x y : F} : ⟪x, y⟫_Real < ‖x‖ * ‖y‖ ↔ ‖y‖ • x !
= ‖x‖ • y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `real_inner_le_norm`：real_inner_le_norm (x y : F) : ⟪x, y⟫_Real <= ‖x‖ * 
‖y‖
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `inner_eq_norm_mul_iff_real`：inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y
⟫_Real = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y
-/
theorem inner_lt_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ‖y‖ • x ≠ ‖x‖ • y :=
  calc
    ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ ≠ ‖x‖ * ‖y‖ :=
      ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
    _ ↔ ‖y‖ • x ≠ ‖x‖ • y := not_congr inner_eq_norm_mul_iff_real

/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
/-
**inner_lt_one_iff_real_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_lt_one_iff_real_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 
1) : ⟪x, y⟫_Real < 1 ↔ x != y
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `inner_lt_norm_mul_iff_real`：inner_lt_norm_mul_iff_real {x y : F} : ⟪x, y
⟫_Real < ‖x‖ * ‖y‖ ↔ ‖y‖ • x != ‖x‖ • y

--- 原说明 ---
If the inner product of two unit vectors is strictly less than `1`, then the two
 vectors are
distinct. One form of the equality case for Cauchy-Schwarz.
-/
theorem inner_lt_one_iff_real_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ < 1 ↔ x ≠ y := by convert! inner_lt_norm_mul_iff_real (F := F) <;> simp [hx, hy]

/-- The sphere of radius `r = ‖y‖` is tangent to the plane `⟪x, y⟫ = ‖y‖ ^ 2` at `x = y`. -/
/-
**eq_of_norm_le_re_inner_eq_norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_norm_le_re_inner_eq_norm_sq {x y : E} (hle : ‖x‖ <= ‖y‖) (h : re ⟪x,
 y⟫ = ‖y‖ ^ 2) : x = y
参数：hle : ‖x‖ <= ‖y‖；h : re ⟪x, y⟫ = ‖y‖ ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.conj_re`：conj_re (z : K) : re (conj z) = re z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.re_ofReal_pow`：re_ofReal_pow (a : Real) (n : Nat) : re ((a : K) ^
 n) = a ^ n
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `re_inner_self_nonpos`：re_inner_self_nonpos {x : E} : re ⟪x, x⟫ <= 0 ↔ x 
= 0

--- 原说明 ---
The sphere of radius `r = ‖y‖` is tangent to the plane `⟪x, y⟫ = ‖y‖ ^ 2` at `x 
= y`.
-/
theorem eq_of_norm_le_re_inner_eq_norm_sq {x y : E} (hle : ‖x‖ ≤ ‖y‖) (h : re ⟪x, y⟫ = ‖y‖ ^ 2) :
    x = y := by
  suffices H : re ⟪x - y, x - y⟫ ≤ 0 by rwa [re_inner_self_nonpos, sub_eq_zero] at H
  have H₁ : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
  have H₂ : re ⟪y, x⟫ = ‖y‖ ^ 2 := by rwa [← inner_conj_symm, conj_re]
  simp only [inner_sub_left, inner_sub_right]
  simpa [h, H₂] using H₁

/-- Equality is achieved in the triangle inequality iff the two vectors are collinear. -/
/-
**norm_add_eq_iff_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_add_eq_iff_real {x y : F} : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_left_inj₀`：pow_left_inj₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b)
 (hn : n != 0) : a ^ n = b ^ n ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Left.add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preo
rder α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `norm_add_sq`：norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, 
y⟫ + ‖y‖ ^ 2
· 使用定理 `add_pow_two`：∀ {α : Type u} [inst : CommSemiring α] (a b : α), (a + b) ^
 2 = a ^ 2 + 2 * a * b + b ^ 2
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `RCLike.re_to_real`：re_to_real {x : Real} : reR x = x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `inner_eq_norm_mul_iff_real`：inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y
⟫_Real = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Equality is achieved in the triangle inequality iff the two vectors are collinea
r.
-/
theorem norm_add_eq_iff_real {x y : F} : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y := by
  rw [← pow_left_inj₀ (norm_nonneg _) (Left.add_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero,
    norm_add_sq (𝕜 := ℝ), add_pow_two, add_left_inj, add_right_inj, re_to_real, mul_assoc,
    mul_right_inj' two_ne_zero, ← inner_eq_norm_mul_iff_real]

end Norm

section Induced

variable {G : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] [AddCommGroup G]
    [Module 𝕜 G]

/-- A linear map from a `Module` to an `InnerProductSpace` induces an `InnerProductSpace`
structure on the domain using the `SeminormedAddCommGroup.induced` norm.

See note [reducible non-instances]. -/
/-
**InnerProductSpace.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：InnerProductSpace.induced {F : Type*} [FunLike F G E] [LinearMapClass F 𝕜 
G E] (f : F) : letI
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map from a `Module` to an `InnerProductSpace` induces an `InnerProductS
pace`
structure on the domain using the `SeminormedAddCommGroup.induced` norm.

See note [reducible non-instances].
-/
abbrev InnerProductSpace.induced {F : Type*} [FunLike F G E] [LinearMapClass F 𝕜 G E] (f : F) :
    letI := SeminormedAddCommGroup.induced G E f
    InnerProductSpace 𝕜 G :=
  letI := SeminormedAddCommGroup.induced G E f
  letI := NormedSpace.induced 𝕜 G E f
  { inner x y := inner 𝕜 (f x) (f y)
    add_left x y z := by rw [map_add, inner_add_left]
    smul_left x y r := by rw [map_smul, inner_smul_left]
    norm_sq_eq_re_inner x := norm_sq_eq_re_inner (f x)
    conj_inner_symm x y := inner_conj_symm (f x) (f y) }
/-
**inner_induced_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_induced_eq (g₁ g₂ : G) (f : G ->ₗ[𝕜] E) : letI
参数：g₁ g₂ : G；f : G ->ₗ[𝕜] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem inner_induced_eq (g₁ g₂ : G) (f : G →ₗ[𝕜] E) :
    letI := InnerProductSpace.induced f
    inner 𝕜 g₁ g₂ = inner 𝕜 (f g₁) (f g₂) := rfl

end Induced

section RCLike

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A field `𝕜` satisfying `RCLike` is itself a `𝕜`-inner product space. -/
/-
**RCLike.innerProductSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RCLike.innerProductSpace : InnerProductSpace 𝕜 𝕜 where inner x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field `𝕜` satisfying `RCLike` is itself a `𝕜`-inner product space.
-/
instance RCLike.innerProductSpace : InnerProductSpace 𝕜 𝕜 where
  inner x y := y * star x
  norm_sq_eq_re_inner x := by rw [star_def, mul_conj, ← ofReal_pow, ofReal_re]
  conj_inner_symm x y := by rw [star_def, map_mul, starRingEnd_self_apply, mul_comm]
  add_left x y z := by rw [star_def, map_add, mul_add]
  smul_left x y z := by rw [star_def, smul_eq_mul, map_mul, mul_left_comm]

@[simp]
/-
**RCLike.inner_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.inner_apply (x y : 𝕜) : ⟪x, y⟫ = y * conj x
参数：x y : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RCLike.inner_apply (x y : 𝕜) : ⟪x, y⟫ = y * conj x :=
  rfl

/-- A version of `RCLike.inner_apply` that swaps the order of multiplication. -/
/-
**RCLike.inner_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y
参数：x y : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
A version of `RCLike.inner_apply` that swaps the order of multiplication.
-/
theorem RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y := mul_comm _ _

end RCLike

section RCLikeToReal

open scoped InnerProductSpace

variable {G : Type*}
variable (𝕜 E)
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A general inner product implies a real inner product. This is not registered as an instance
since `𝕜` does not appear in the return type `Inner ℝ E`. -/
@[instance_reducible]
/-
**Inner.rclikeToReal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Inner.rclikeToReal : Inner Real E where inner x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A general inner product implies a real inner product. This is not registered as 
an instance
since `𝕜` does not appear in the return type `Inner ℝ E`.
-/
def Inner.rclikeToReal : Inner ℝ E where inner x y := re ⟪x, y⟫

/-- A general inner product space structure implies a real inner product structure.

This is not registered as an instance since
* `𝕜` does not appear in the return type `InnerProductSpace ℝ E`,
* It is likely to create instance diamonds, as it builds upon the diamond-prone
  `NormedSpace.restrictScalars`.

However, it can be used in a proof to obtain a real inner product space structure from a given
`𝕜`-inner product space structure. -/
-- See note [reducible non-instances]
/-
**InnerProductSpace.rclikeToReal** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：InnerProductSpace.rclikeToReal : InnerProductSpace Real E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.norm_sq_eq_re_inner`：∀ {𝕜 : Type u_4} {E : Type u_5} {
inst : RCLike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜
 E]   (x : E), ‖x‖ ^ 2 = RC…
· 使用定理 `inner_re_symm`：inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫
-/
abbrev InnerProductSpace.rclikeToReal : InnerProductSpace ℝ E :=
  { Inner.rclikeToReal 𝕜 E,
    NormedSpace.restrictScalars ℝ 𝕜 E with
    norm_sq_eq_re_inner := norm_sq_eq_re_inner
    conj_inner_symm := fun _ _ => inner_re_symm _ _
    add_left := fun x y z => by
      simp +instances only [Inner.rclikeToReal, inner_add_left, map_add]
    smul_left := fun x y r => by
      let := NormedSpace.restrictScalars ℝ 𝕜 E
      have : r • x = (r : 𝕜) • x := rfl
      simp +instances only [Inner.rclikeToReal, this, conj_trivial, inner_smul_left, conj_ofReal,
        re_ofReal_mul] }

variable {E}
/-
**real_inner_eq_re_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_eq_re_inner (x y : E) : (Inner.rclikeToReal 𝕜 E).inner x y = re
 ⟪x, y⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem real_inner_eq_re_inner (x y : E) :
    (Inner.rclikeToReal 𝕜 E).inner x y = re ⟪x, y⟫ :=
  rfl
/-
**real_inner_I_smul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：real_inner_I_smul_self (x : E) : (Inner.rclikeToReal 𝕜 E).inner x ((I : 𝕜)
 • x) = 0
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_eq_re_inner`：real_inner_eq_re_inner (x y : E) : (Inner.rclike
ToReal 𝕜 E).inner x y = re ⟪x, y⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `RCLike.re_ofReal_pow`：re_ofReal_pow (a : Real) (n : Nat) : re ((a : K) ^
 n) = a ^ n
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RCLike.im_ofReal_pow`：im_ofReal_pow (a : Real) (n : Nat) : im ((a : K) ^
 n) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem real_inner_I_smul_self (x : E) :
    (Inner.rclikeToReal 𝕜 E).inner x ((I : 𝕜) • x) = 0 := by
  simp [real_inner_eq_re_inner 𝕜, inner_smul_right]

/-- A complex inner product implies a real inner product. This cannot be an instance since it
creates a diamond with `PiLp.innerProductSpace` because `re (sum i, ⟪x i, y i⟫)` and
`sum i, re ⟪x i, y i⟫` are not defeq. -/
@[instance_reducible]
/-
**InnerProductSpace.complexToReal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InnerProductSpace.complexToReal [SeminormedAddCommGroup G] [InnerProductSp
ace Complex G] : InnerProductSpace Real G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complex inner product implies a real inner product. This cannot be an instance
 since it
creates a diamond with `PiLp.innerProductSpace` because `re (sum i, ⟪x i, y i⟫)`
 and
`sum i, re ⟪x i, y i⟫` are not defeq.
-/
def InnerProductSpace.complexToReal [SeminormedAddCommGroup G] [InnerProductSpace ℂ G] :
    InnerProductSpace ℝ G :=
  InnerProductSpace.rclikeToReal ℂ G
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InnerProductSpace ℝ ℂ := InnerProductSpace.complexToReal

@[simp]
/-
**Complex.inner** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (w z : ℂ), inner ℝ w z = (z * (starRingEnd ℂ) w).re
参数：w z : ℂ；z * (starRingEnd ℂ) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Complex.inner (w z : ℂ) : ⟪w, z⟫_ℝ = (z * conj w).re :=
  rfl

end RCLikeToReal

/-- An `RCLike` field is a real inner product space. -/
/-
**RCLike.toInnerProductSpaceReal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RCLike.toInnerProductSpaceReal : InnerProductSpace Real 𝕜 where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `RCLike` field is a real inner product space.
-/
noncomputable instance RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ 𝕜 where
  __ := Inner.rclikeToReal 𝕜 𝕜
  norm_sq_eq_re_inner := norm_sq_eq_re_inner
  conj_inner_symm x y := inner_re_symm ..
  add_left x y z :=
    show re (_ * _) = re (_ * _) + re (_ * _) by
      simp only [star_def, map_add, mul_re, conj_re, conj_im]; ring
  smul_left x y r :=
    show re (_ * _) = _ * re (_ * _) by
      simp only [star_def, mul_re, conj_re, conj_im, conj_trivial, smul_re, smul_im]; ring

-- The instance above does not create diamonds for concrete `𝕜`:
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (innerProductSpace : InnerProductSpace ℝ ℝ) = RCLike.toInnerProductSpaceReal := rfl
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example :
    (instInnerProductSpaceRealComplex : InnerProductSpace ℝ ℂ) = RCLike.toInnerProductSpaceReal :=
  rfl
/-
**Real.inner_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.inner_apply (x y : Real) : inner Real x y = x * y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem Real.inner_apply (x y : ℝ) : inner ℝ x y = x * y := by rw [mul_comm]; rfl

section IsPosSemidef

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
**isSymm_inner** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSymm_inner : LinearMap.IsSymm (innerₗ E) where eq x y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isSymm_inner : LinearMap.IsSymm (innerₗ E) where
  eq x y := by simp [real_inner_comm]
/-
**isNonneg_inner** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isNonneg_inner : LinearMap.IsNonneg (innerₗ E) where nonneg x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma isNonneg_inner : LinearMap.IsNonneg (innerₗ E) where
  nonneg x := by simp
/-
**isPosSemidef_inner** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isPosSemidef_inner : LinearMap.IsPosSemidef (innerₗ E) where isSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isSymm_inner`：isSymm_inner : LinearMap.IsSymm (innerₗ E) where eq x y
· 使用引理 `isNonneg_inner`：isNonneg_inner : LinearMap.IsNonneg (innerₗ E) where non
neg x
-/
lemma isPosSemidef_inner : LinearMap.IsPosSemidef (innerₗ E) where
  isSymm := isSymm_inner
  isNonneg := isNonneg_inner

end IsPosSemidef

/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (instInnerProductSpaceRealComplex.toSMul : SMul ℝ ℂ) =
    Complex.instRCLike.toSMul := by
  with_reducible_and_instances rfl
