/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Reflection

A linear isometry equivalence `K.reflection : E ≃ₗᵢ[𝕜] E` in constructed, by choosing
for each `u : E`, `K.reflection u = 2 • K.starProjection u - u`.
-/

@[expose] public section

noncomputable section

namespace Submodule

section reflection

open Submodule RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : Submodule 𝕜 E)
variable [K.HasOrthogonalProjection]

/-- Auxiliary definition for `reflection`: the reflection as a linear equivalence. -/
/-
**Submodule.reflectionLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：reflectionLinearEquiv : E ≃ₗ[𝕜] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `reflection`: the reflection as a linear equivalence.
-/
def reflectionLinearEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInvolutive
    (2 • (K.starProjection.toLinearMap) - LinearMap.id) fun x => by
    simp [two_smul, starProjection_eq_self_iff.mpr]

set_option backward.isDefEq.respectTransparency false in
/-- Reflection in a complete subspace of an inner product space.  The word "reflection" is
sometimes understood to mean specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The definition here, of
reflection in a subspace, is a more general sense of the word that includes both those common
cases. -/
/-
**Submodule.reflection** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：reflection : E ≃ₗᵢ[𝕜] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reflection in a complete subspace of an inner product space.  The word "reflecti
on" is
sometimes understood to mean specifically reflection in a codimension-one subspa
ce, and sometimes
more generally to cover operations such as reflection in a point.  The definitio
n here, of
reflection in a subspace, is a more general sense of the word that includes both
 those common
cases.
-/
def reflection : E ≃ₗᵢ[𝕜] E :=
  { K.reflectionLinearEquiv with
    norm_map' := by
      intro x
      let w : K := K.orthogonalProjectionOnto x
      let v := x - w
      have : ⟪v, w⟫ = 0 := starProjection_inner_eq_zero x w w.2
      convert norm_sub_eq_norm_add this
      · dsimp [reflectionLinearEquiv, v, w]
        abel
      · simp only [v, add_sub_cancel] }

variable {K}

/-- The result of reflecting. -/
/-
**Submodule.reflection_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_apply (p : E) : K.reflection p = 2 • K.starProjection p - p
参数：p : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of reflecting.
-/
theorem reflection_apply (p : E) : K.reflection p = 2 • K.starProjection p - p :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
/-
**Submodule.reflection_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_symm : K.reflection.symm = K.reflection
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reflection is its own inverse.
-/
theorem reflection_symm : K.reflection.symm = K.reflection :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
/-
**Submodule.reflection_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_inv : K.reflection⁻¹ = K.reflection
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reflection is its own inverse.
-/
theorem reflection_inv : K.reflection⁻¹ = K.reflection :=
  rfl

variable (K)

/-- Reflecting twice in the same subspace. -/
@[simp]
/-
**Submodule.reflection_reflection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_reflection (p : E) : K.reflection (K.reflection p) = p
参数：p : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…

--- 原说明 ---
Reflecting twice in the same subspace.
-/
theorem reflection_reflection (p : E) : K.reflection (K.reflection p) = p :=
  K.reflection.left_inv p

/-- Reflection is involutive. -/
/-
**Submodule.reflection_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_involutive : Function.Involutive K.reflection
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.reflection_reflection`：reflection_reflection (p : E) : K.refle
ction (K.reflection p) = p

--- 原说明 ---
Reflection is involutive.
-/
theorem reflection_involutive : Function.Involutive K.reflection :=
  K.reflection_reflection

/-- Reflection is involutive. -/
@[simp]
/-
**Submodule.reflection_trans_reflection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_trans_reflection : K.reflection.trans K.reflection = LinearIsom
etryEquiv.refl 𝕜 E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `Submodule.reflection_involutive`：reflection_involutive : Function.Involu
tive K.reflection

--- 原说明 ---
Reflection is involutive.
-/
theorem reflection_trans_reflection :
    K.reflection.trans K.reflection = LinearIsometryEquiv.refl 𝕜 E :=
  LinearIsometryEquiv.ext <| reflection_involutive K

/-- Reflection is involutive. -/
@[simp]
/-
**Submodule.reflection_mul_reflection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_mul_reflection : K.reflection * K.reflection = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.reflection_trans_reflection`：reflection_trans_reflection : K.r
eflection.trans K.reflection = LinearIsometryEquiv.refl 𝕜 E

--- 原说明 ---
Reflection is involutive.
-/
theorem reflection_mul_reflection : K.reflection * K.reflection = 1 :=
  reflection_trans_reflection _
/-
**Submodule.reflection_orthogonal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_orthogonal_apply (v : E) : Kᗮ.reflection v = -K.reflection v
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.starProjection_orthogonal_val`：starProjection_orthogonal_val (
u : E) : Kᗮ.starProjection u = u - K.starProjection u
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Projection.Reflection.0.Subm
odule.reflection_orthogonal_apply._abel_1_2`：∀ {𝕜 : Type u_2} {E : Type u_1} [in
st : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] 
  (K : Submodule 𝕜 E) [in…
-/
theorem reflection_orthogonal_apply (v : E) : Kᗮ.reflection v = -K.reflection v := by
  simp [reflection_apply]; abel
/-
**Submodule.reflection_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_orthogonal : Kᗮ.reflection = .trans K.reflection (.neg _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.reflection_orthogonal_apply`：reflection_orthogonal_apply (v : 
E) : Kᗮ.reflection v = -K.reflection v
-/
theorem reflection_orthogonal : Kᗮ.reflection = .trans K.reflection (.neg _) := by
  ext; apply reflection_orthogonal_apply

variable {K}
/-
**Submodule.reflection_singleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_singleton_apply (u v : E) : reflection (𝕜 ∙ u) v = 2 • (⟪u, v⟫ 
/ ((‖u‖ : 𝕜) ^ 2)) • u - v
参数：u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.reflection_apply`：reflection_apply (p : E) : K.reflection p = 
2 • K.starProjection p - p
· 使用定理 `Submodule.starProjection_singleton`：starProjection_singleton {v : E} (w 
: E) : (𝕜 ∙ v).starProjection w = (⟪v, w⟫ / ((‖v‖ ^ 2 : Real) : 𝕜)) • v
· 使用定理 `RCLike.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K
) = (r : K) ^ n
-/
theorem reflection_singleton_apply (u v : E) :
    reflection (𝕜 ∙ u) v = 2 • (⟪u, v⟫ / ((‖u‖ : 𝕜) ^ 2)) • u - v := by
  rw [reflection_apply, starProjection_singleton, ofReal_pow]

/-- A point is its own reflection if and only if it is in the subspace. -/
/-
**Submodule.reflection_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_eq_self_iff (x : E) : K.reflection x = x ↔ x in K
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.starProjection_eq_self_iff`：starProjection_eq_self_iff {v : E}
 : K.starProjection v = v ↔ v in K
· 使用定理 `Submodule.reflection_apply`：reflection_apply (p : E) : K.reflection p = 
2 • K.starProjection p - p
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K

--- 原说明 ---
A point is its own reflection if and only if it is in the subspace.
-/
theorem reflection_eq_self_iff (x : E) : K.reflection x = x ↔ x ∈ K := by
  rw [← starProjection_eq_self_iff, reflection_apply, sub_eq_iff_eq_add', ← two_smul 𝕜,
    two_smul ℕ, ← two_smul 𝕜]
  refine (smul_right_injective E ?_).eq_iff
  exact two_ne_zero
/-
**Submodule.reflection_mem_subspace_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：reflection_mem_subspace_eq_self {x : E} (hx : x in K) : K.reflection x = x
参数：hx : x in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.reflection_eq_self_iff`：reflection_eq_self_iff (x : E) : K.ref
lection x = x ↔ x in K
-/
theorem reflection_mem_subspace_eq_self {x : E} (hx : x ∈ K) : K.reflection x = x :=
  (reflection_eq_self_iff x).mpr hx

/-- Reflection in the `Submodule.map` of a subspace. -/
/-
**Submodule.reflection_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_map_apply {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommG
roup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K :
 Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E') : reflection (K.map (f.toLi
nearEquiv : E ->ₗ[𝕜] E')) x = f (K.reflection (f.symm x))
参数：f : E ≃ₗᵢ[𝕜] E'；K : Submodule 𝕜 E；x : E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.HasOrthogonalProjection.map_linearIsometryEquiv`：∀ {𝕜 : Type u
_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : I
nnerProductSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.starProjection_map_apply`：starProjection_map_apply {E E' : Typ
e*} [NormedAddCommGroup E] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [Inne
rProductSpace 𝕜 E'] (f :…
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
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reflection in the `Submodule.map` of a subspace.
-/
theorem reflection_map_apply {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (x : E') :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) x = f (K.reflection (f.symm x)) := by
  simp [reflection_apply, starProjection_map_apply f K x]

/-- Reflection in the `Submodule.map` of a subspace. -/
/-
**Submodule.reflection_map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_map {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E
'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submo
dule 𝕜 E) [K.HasOrthogonalProjection] : reflection (K.map (f.toLinearEquiv : E -
>ₗ[𝕜] E')) = f.symm.trans (K.reflection.trans f)
参数：f : E ≃ₗᵢ[𝕜] E'；K : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `Submodule.HasOrthogonalProjection.map_linearIsometryEquiv`：∀ {𝕜 : Type u
_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : I
nnerProductSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.reflection_map_apply`：reflection_map_apply {E E' : Type*} [Nor
medAddCommGroup E] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProduct
Space 𝕜 E'] (f : E ≃…

--- 原说明 ---
Reflection in the `Submodule.map` of a subspace.
-/
theorem reflection_map {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) = f.symm.trans (K.reflection.trans f) :=
  LinearIsometryEquiv.ext <| reflection_map_apply f K

/-- Reflection through the trivial subspace `{0}` is just negation. -/
@[simp]
/-
**Submodule.reflection_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_bot : reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 
𝕜
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.starProjection_bot`：starProjection_bot : (⊥ : Submodule 𝕜 E).s
tarProjection = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reflection through the trivial subspace `{0}` is just negation.
-/
theorem reflection_bot : reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 𝕜 := by
  ext; simp [reflection_apply]

/-- The reflection in `K` of an element of `Kᗮ` is its negation. -/
/-
**Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg** 是 Mathlib 中的一个
定理，位于命名空间 `Submodule`。
形式化陈述：reflection_mem_subspace_orthogonalComplement_eq_neg {v : E} (hv : v in Kᗮ)
 : K.reflection v = -v
参数：hv : v in Kᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal`：orthogonalPr
ojectionOnto_apply_of_mem_orthogonal [K.HasOrthogonalProjection] {v : E} (hv : v
 in Kᗮ) : K.orthogonalProjectionOnto v = 0
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The reflection in `K` of an element of `Kᗮ` is its negation.
-/
theorem reflection_mem_subspace_orthogonalComplement_eq_neg {v : E}
    (hv : v ∈ Kᗮ) : K.reflection v = -v := by
  simp [starProjection_apply, reflection_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hv]

/-- The reflection in `Kᗮ` of an element of `K` is its negation. -/
/-
**Submodule.reflection_mem_subspace_orthogonal_precomplement_eq_neg** 是 Mathlib 
中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_mem_subspace_orthogonal_precomplement_eq_neg {v : E} (hv : v in
 K) : Kᗮ.reflection v = -v
参数：hv : v in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg`：reflectio
n_mem_subspace_orthogonalComplement_eq_neg {v : E} (hv : v in Kᗮ) : K.reflection
 v = -v
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.le_orthogonal_orthogonal`：le_orthogonal_orthogonal : K <= Kᗮᗮ

--- 原说明 ---
The reflection in `Kᗮ` of an element of `K` is its negation.
-/
theorem reflection_mem_subspace_orthogonal_precomplement_eq_neg {v : E}
    (hv : v ∈ K) : Kᗮ.reflection v = -v :=
  reflection_mem_subspace_orthogonalComplement_eq_neg (K.le_orthogonal_orthogonal hv)

/-- The reflection in `(𝕜 ∙ v)ᗮ` of `v` is `-v`. -/
/-
**Submodule.reflection_orthogonalComplement_singleton_eq_neg** 是 Mathlib 中的一个定理，
位于命名空间 `Submodule`。
形式化陈述：reflection_orthogonalComplement_singleton_eq_neg (v : E) : reflection (𝕜 ∙
 v)ᗮ v = -v
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.reflection_mem_subspace_orthogonal_precomplement_eq_neg`：refle
ction_mem_subspace_orthogonal_precomplement_eq_neg {v : E} (hv : v in K) : Kᗮ.re
flection v = -v
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x

--- 原说明 ---
The reflection in `(𝕜 ∙ v)ᗮ` of `v` is `-v`.
-/
theorem reflection_orthogonalComplement_singleton_eq_neg (v : E) : reflection (𝕜 ∙ v)ᗮ v = -v :=
  reflection_mem_subspace_orthogonal_precomplement_eq_neg (Submodule.mem_span_singleton_self v)
/-
**Submodule.reflection_sub** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：reflection_sub {v w : F} (h : ‖v‖ = ‖w‖) : reflection (Real ∙ (v - w))ᗮ v 
= w
参数：h : ‖v‖ = ‖w‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.reflection_orthogonalComplement_singleton_eq_neg`：reflection_o
rthogonalComplement_singleton_eq_neg (v : E) : reflection (𝕜 ∙ v)ᗮ v = -v
· 使用定理 `Submodule.reflection_mem_subspace_eq_self`：reflection_mem_subspace_eq_se
lf {x : E} (hx : x in K) : K.reflection x = x
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_left`：mem_orthogonal_single
ton_iff_inner_left {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0
· 使用定理 `real_inner_add_sub_eq_zero_iff`：real_inner_add_sub_eq_zero_iff (x y : F)
 : ⟪x + y, x - y⟫_Real = 0 ↔ ‖x‖ = ‖y‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `add_add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + c + (b - c) = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Projection.Reflection.0.Subm
odule.reflection_sub._abel_1_1`：∀ {F : Type u_1} [inst : NormedAddCommGroup F] {
v w : F}, w + w = v + w + -(v - w)
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
（共 35 条，此处仅展示前 30 条）
-/
theorem reflection_sub {v w : F} (h : ‖v‖ = ‖w‖) : reflection (ℝ ∙ (v - w))ᗮ v = w := by
  set R : F ≃ₗᵢ[ℝ] F := reflection (ℝ ∙ (v - w))ᗮ
  suffices R v + R v = w + w by
    apply smul_right_injective F (by simp : (2 : ℝ) ≠ 0)
    simpa [two_smul] using this
  have h₁ : R (v - w) = -(v - w) := reflection_orthogonalComplement_singleton_eq_neg (v - w)
  have h₂ : R (v + w) = v + w := by
    apply reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_add_sub_eq_zero_iff]
    exact h
  convert! congr_arg₂ (· + ·) h₂ h₁ using 1
  · simp
  · abel

end reflection

end Submodule

end

