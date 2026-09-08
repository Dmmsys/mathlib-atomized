/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Operator norm for maps on normed spaces

This file contains statements about operator norm for which it really matters that the
underlying space has a norm (rather than just a seminorm).
-/

@[expose] public section

suppress_compilation

open Topology
open scoped NNReal

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₁ 𝕜₂ 𝕜₃ E F Fₗ G : Type*}

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f : E →SL[σ₁₂] F)

namespace LinearIsometry
section
variable [NontrivialTopology E] [RingHomIsometric σ₁₂]

/-
**LinearIsometry.norm_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearIso
metry`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : Type u_5} {F : Type u_6} [inst : Sem
inormedAddCommGroup E]   [inst_1 : SeminormedAddCommGroup F] [inst_2 : Nontrivia
llyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂]   [inst_4 : NormedSpace 
𝕜 E] [inst_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [NontrivialTopology E] [RingHo
mIsometric σ₁₂]   (f : E →ₛₗᵢ[σ₁₂] F), ‖f.toContinuousLinearMap‖ = 1
参数：f : E →ₛₗᵢ[σ₁₂] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.homothety_norm`：homothety_norm [NontrivialTopology E
] (f : E ->SL[σ₁₂] F) {a : Real} (hf : forall x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma norm_toContinuousLinearMap (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ = 1 :=
  f.toContinuousLinearMap.homothety_norm <| by simp
/-
**LinearIsometry.nnnorm_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearI
sometry`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : Type u_5} {F : Type u_6} [inst : Sem
inormedAddCommGroup E]   [inst_1 : SeminormedAddCommGroup F] [inst_2 : Nontrivia
llyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂]   [inst_4 : NormedSpace 
𝕜 E] [inst_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [NontrivialTopology E]   [inst
_7 : RingHomIsometric σ₁₂] (f : E →ₛₗᵢ[σ₁₂] F), ‖f.toContinuousLinearMap‖₊ = 1
参数：f : E →ₛₗᵢ[σ₁₂] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u
_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 : 
SeminormedAddCommGroup F] [inst…
-/
@[simp] lemma nnnorm_toContinuousLinearMap (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖₊ = 1 :=
  Subtype.ext f.norm_toContinuousLinearMap
/-
**LinearIsometry.enorm_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearIs
ometry`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : Type u_5} {F : Type u_6} [inst : Sem
inormedAddCommGroup E]   [inst_1 : SeminormedAddCommGroup F] [inst_2 : Nontrivia
llyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂]   [inst_4 : NormedSpace 
𝕜 E] [inst_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [NontrivialTopology E]   [inst
_7 : RingHomIsometric σ₁₂] (f : E →ₛₗᵢ[σ₁₂] F), ‖f.toContinuousLinearMap‖ₑ = 1
参数：f : E →ₛₗᵢ[σ₁₂] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometry.nnnorm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type
 u_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 
: SeminormedAddCommGroup F] [inst…
-/
@[simp] lemma enorm_toContinuousLinearMap (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ₑ = 1 :=
  congrArg _ f.nnnorm_toContinuousLinearMap

end

variable {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Postcomposition of a continuous linear map with a linear isometry preserves
the operator norm. -/
/-
**LinearIsometry.norm_toContinuousLinearMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Line
arIsometry`。
形式化陈述：norm_toContinuousLinearMap_comp [RingHomIsometric σ₁₂] (f : F ->ₛₗᵢ[σ₂₃] G
) {g : E ->SL[σ₁₂] F} : ‖f.toContinuousLinearMap.comp g‖ = ‖g‖
参数：f : F ->ₛₗᵢ[σ₂₃] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_ext`：opNorm_ext [RingHomIsometric σ₁₃] (f : E
 ->SL[σ₁₂] F) (g : E ->SL[σ₁₃] G) (h : forall x, ‖f x‖ = ‖g x‖) : ‖f‖ = ‖g‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Postcomposition of a continuous linear map with a linear isometry preserves
the operator norm.
-/
lemma norm_toContinuousLinearMap_comp [RingHomIsometric σ₁₂] (f : F →ₛₗᵢ[σ₂₃] G)
    {g : E →SL[σ₁₂] F} : ‖f.toContinuousLinearMap.comp g‖ = ‖g‖ :=
  (f.toContinuousLinearMap.comp g).opNorm_ext g fun x ↦ by simp

/-- Composing on the left with a linear isometry gives a linear isometry between spaces of
continuous linear maps. -/
/-
**LinearIsometry.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry`。
形式化陈述：postcomp [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] (a : F ->ₛₗᵢ[σ₂₃] G
) : (E ->SL[σ₁₂] F) ->ₛₗᵢ[σ₂₃] (E ->SL[σ₁₃] G) where toFun f
参数：a : F ->ₛₗᵢ[σ₂₃] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing on the left with a linear isometry gives a linear isometry between spa
ces of
continuous linear maps.
-/
def postcomp [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] (a : F →ₛₗᵢ[σ₂₃] G) :
    (E →SL[σ₁₂] F) →ₛₗᵢ[σ₂₃] (E →SL[σ₁₃] G) where
  toFun f := a.toContinuousLinearMap.comp f
  map_add' f g := by simp
  map_smul' c f := by simp
  norm_map' f := by simp [a.norm_toContinuousLinearMap_comp]

end LinearIsometry

namespace LinearIsometryEquiv
variable [NontrivialTopology E] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [RingHomIsometric σ₁₂]

/-
**LinearIsometryEquiv.norm_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Line
arIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : Type u_5} {F : Type u_6} [inst : Sem
inormedAddCommGroup E]   [inst_1 : SeminormedAddCommGroup F] [inst_2 : Nontrivia
llyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂]   [inst_4 : NormedSpace 
𝕜 E] [inst_5 : NormedSpace 𝕜₂ F] [NontrivialTopology E] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 
𝕜₂ →+* 𝕜}   [inst_7 : RingHomInvPair σ₁₂ σ₂₁] [inst_8 : RingHomInvPair σ₂₁ σ₁₂] 
[RingHomIsometric σ₁₂] (e : E ≃ₛₗᵢ[σ₁₂] F),   ‖↑↑e‖ = 1
参数：e : E ≃ₛₗᵢ[σ₁₂] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u
_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 : 
SeminormedAddCommGroup F] [inst…
-/
@[simp] lemma norm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ = 1 :=
  e.toLinearIsometry.norm_toContinuousLinearMap
/-
**LinearIsometryEquiv.nnnorm_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : Type u_5} {F : Type u_6} [inst : Sem
inormedAddCommGroup E]   [inst_1 : SeminormedAddCommGroup F] [inst_2 : Nontrivia
llyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂]   [inst_4 : NormedSpace 
𝕜 E] [inst_5 : NormedSpace 𝕜₂ F] [NontrivialTopology E] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 
𝕜₂ →+* 𝕜}   [inst_7 : RingHomInvPair σ₁₂ σ₂₁] [inst_8 : RingHomInvPair σ₂₁ σ₁₂] 
[inst_9 : RingHomIsometric σ₁₂]   (e : E ≃ₛₗᵢ[σ₁₂] F), ‖↑↑e‖₊ = 1
参数：e : E ≃ₛₗᵢ[σ₁₂] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.nnnorm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type
 u_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 
: SeminormedAddCommGroup F] [inst…
-/
@[simp] lemma nnnorm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖₊ = 1 :=
  e.toLinearIsometry.nnnorm_toContinuousLinearMap
/-
**LinearIsometryEquiv.enorm_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : Type u_5} {F : Type u_6} [inst : Sem
inormedAddCommGroup E]   [inst_1 : SeminormedAddCommGroup F] [inst_2 : Nontrivia
llyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂]   [inst_4 : NormedSpace 
𝕜 E] [inst_5 : NormedSpace 𝕜₂ F] [NontrivialTopology E] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 
𝕜₂ →+* 𝕜}   [inst_7 : RingHomInvPair σ₁₂ σ₂₁] [inst_8 : RingHomInvPair σ₂₁ σ₁₂] 
[inst_9 : RingHomIsometric σ₁₂]   (e : E ≃ₛₗᵢ[σ₁₂] F), ‖↑↑e‖ₑ = 1
参数：e : E ≃ₛₗᵢ[σ₁₂] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.enorm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type 
u_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 :
 SeminormedAddCommGroup F] [inst…
-/
@[simp] lemma enorm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ₑ = 1 :=
  e.toLinearIsometry.enorm_toContinuousLinearMap

end LinearIsometryEquiv
end SeminormedAddCommGroup

section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

open Metric ContinuousLinearMap

section

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f : E →SL[σ₁₂] F)

namespace LinearMap

/-
**LinearMap.bound_of_shell** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：bound_of_shell [RingHomIsometric σ₁₂] (f : E ->ₛₗ[σ₁₂] F) {ε C : Real} (ε_
pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall x, ε / ‖c‖ <= ‖x‖ -> ‖x‖ < ε ->
 ‖f x‖ <= C * ‖x‖) (x : E) : ‖f x‖ <= C * ‖x‖
参数：f : E ->ₛₗ[σ₁₂] F；ε_pos : 0 < ε；hc : 1 < ‖c‖；hf : forall x, ε / ‖c‖ <= ‖x‖ ->
 ‖x‖ < ε -> ‖f x‖ <= C * ‖x‖；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `SemilinearMapClass.bound_of_shell_semi_normed`：SemilinearMapClass.bound_
of_shell_semi_normed [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) {ε C : Real} (ε_pos 
: 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
-/
theorem bound_of_shell [RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) (x : E) :
    ‖f x‖ ≤ C * ‖x‖ := by
  by_cases hx : x = 0; · simp [hx]
  exact SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf (norm_ne_zero_iff.2 hx)

/-- `LinearMap.bound_of_ball_bound'` is a version of this lemma over a field satisfying `RCLike`
that produces a concrete bound.
-/
/-
**LinearMap.bound_of_ball_bound** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：bound_of_ball_bound {r : Real} (r_pos : 0 < r) (c : Real) (f : E ->ₗ[𝕜] Fₗ
) (h : forall z in Metric.ball (0 : E) r, ‖f z‖ <= c) : exists C, forall z : E, 
‖f z‖ <= C * ‖z‖
参数：r_pos : 0 < r；c : Real；f : E ->ₗ[𝕜] Fₗ；h : forall z in Metric.ball (0 : E) r,
 ‖f z‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NontriviallyNormedField.non_trivial`：∀ {α : Type u_5} [self : Nontrivial
lyNormedField α], ∃ x, 1 < ‖x‖
· 使用定理 `LinearMap.bound_of_shell`：bound_of_shell [RingHomIsometric σ₁₂] (f : E -
>ₛₗ[σ₁₂] F) {ε C : Real} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall x, 
ε / ‖c‖ <= ‖x‖…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `one_le_div`：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
`LinearMap.bound_of_ball_bound'` is a version of this lemma over a field satisfy
ing `RCLike`
that produces a concrete bound.
-/
theorem bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] Fₗ)
    (h : ∀ z ∈ Metric.ball (0 : E) r, ‖f z‖ ≤ c) : ∃ C, ∀ z : E, ‖f z‖ ≤ C * ‖z‖ := by
  obtain ⟨k, hk⟩ := @NontriviallyNormedField.non_trivial 𝕜 _
  use c * (‖k‖ / r)
  intro z
  refine bound_of_shell _ r_pos hk (fun x hko hxo => ?_) _
  calc
    ‖f x‖ ≤ c := h _ (mem_ball_zero_iff.mpr hxo)
    _ ≤ c * (‖x‖ * ‖k‖ / r) := le_mul_of_one_le_right ?_ ?_
    _ = _ := by ring
  · exact le_trans (norm_nonneg _) (h 0 (by simp [r_pos]))
  · rw [div_le_iff₀ (zero_lt_one.trans hk)] at hko
    exact (one_le_div r_pos).mpr hko
/-
**LinearMap.antilipschitz_of_comap_nhds_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：antilipschitz_of_comap_nhds_le [h : RingHomIsometric σ₁₂] (f : E ->ₛₗ[σ₁₂]
 F) (hf : (𝓝 0).comap f <= 𝓝 0) : exists K, AntilipschitzWith K f
参数：f : E ->ₛₗ[σ₁₂] F；hf : (𝓝 0).comap f <= 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `AddMonoidHomClass.antilipschitz_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]  
 [inst_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Specializes.eq`：Specializes.eq [T1Space X] {x y : X} (h : x ⤳ y) : x = y
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `specializes_iff_pure`：specializes_iff_pure : x ⤳ y ↔ pure x <= 𝓝 y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
（共 53 条，此处仅展示前 30 条）
-/
theorem antilipschitz_of_comap_nhds_le [h : RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F)
    (hf : (𝓝 0).comap f ≤ 𝓝 0) : ∃ K, AntilipschitzWith K f := by
  rcases ((nhds_basis_ball.comap _).le_basis_iff nhds_basis_ball).1 hf 1 one_pos with ⟨ε, ε0, hε⟩
  simp only [Set.subset_def, Set.mem_preimage, mem_ball_zero_iff] at hε
  lift ε to ℝ≥0 using ε0.le
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨ε⁻¹ * ‖c‖₊, AddMonoidHomClass.antilipschitz_of_bound f fun x => ?_⟩
  by_cases hx : f x = 0
  · rw [← hx] at hf
    obtain rfl : x = 0 := Specializes.eq (specializes_iff_pure.2 <|
      ((Filter.tendsto_pure_pure _ _).mono_right (pure_le_nhds _)).le_comap.trans hf)
    exact norm_zero.trans_le (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
  have hc₀ : c ≠ 0 := norm_pos_iff.1 (one_pos.trans hc)
  rw [← h.1] at hc
  rcases rescale_to_shell_zpow hc ε0 hx with ⟨n, -, hlt, -, hle⟩
  simp only [← map_zpow₀, h.1, ← map_smulₛₗ] at hlt hle
  calc
    ‖x‖ = ‖c ^ n‖⁻¹ * ‖c ^ n • x‖ := by
      rwa [← norm_inv, ← norm_smul, inv_smul_smul₀ (zpow_ne_zero _ _)]
    _ ≤ ‖c ^ n‖⁻¹ * 1 := by gcongr; exact (hε _ hlt).le
    _ ≤ ε⁻¹ * ‖c‖ * ‖f x‖ := by rwa [mul_one]

end LinearMap

namespace ContinuousLinearMap

open Set Real

/-- An operator is zero iff its norm vanishes. -/
/-
**ContinuousLinearMap.opNorm_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：opNorm_zero_iff [RingHomIsometric σ₁₂] : ‖f‖ = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ContinuousLinearMap.opNorm_zero`：opNorm_zero : ‖(0 : E ->SL[σ₁₂] F)‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An operator is zero iff its norm vanishes.
-/
theorem opNorm_zero_iff [RingHomIsometric σ₁₂] : ‖f‖ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn => ContinuousLinearMap.ext fun x => norm_le_zero_iff.1
      (calc
        _ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
        _ = _ := by rw [hn, zero_mul]))
    (by
      rintro rfl
      exact opNorm_zero)

/-- Continuous linear maps themselves form a normed space with respect to the operator norm. -/
/-
**ContinuousLinearMap.toNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Continuous
LinearMap`。
形式化陈述：toNormedAddCommGroup [RingHomIsometric σ₁₂] : NormedAddCommGroup (E ->SL[σ
₁₂] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear maps themselves form a normed space with respect to the operat
or norm.
-/
instance toNormedAddCommGroup [RingHomIsometric σ₁₂] : NormedAddCommGroup (E →SL[σ₁₂] F) :=
  NormedAddCommGroup.ofSeparation fun f => (opNorm_zero_iff f).mp

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
/-
**ContinuousLinearMap.toNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：toNormedRing : NormedRing (E ->L[𝕜] E) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear maps form a normed ring with respect to the operator norm.
-/
instance toNormedRing : NormedRing (E →L[𝕜] E) where
  __ := toNormedAddCommGroup
  __ := toSeminormedRing

/-- If a continuous linear map is a topology embedding, then it is expands the distances
by a positive factor. -/
/-
**ContinuousLinearMap.antilipschitz_of_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：antilipschitz_of_isEmbedding (f : E ->L[𝕜] Fₗ) (hf : IsEmbedding f) : exis
ts K, AntilipschitzWith K f
参数：f : E ->L[𝕜] Fₗ；hf : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.antilipschitz_of_comap_nhds_le`：antilipschitz_of_comap_nhds_le
 [h : RingHomIsometric σ₁₂] (f : E ->ₛₗ[σ₁₂] F) (hf : (𝓝 0).comap f <= 𝓝 0) : ex
ists K, AntilipschitzWith K f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
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

--- 原说明 ---
If a continuous linear map is a topology embedding, then it is expands the dista
nces
by a positive factor.
-/
theorem antilipschitz_of_isEmbedding (f : E →L[𝕜] Fₗ) (hf : IsEmbedding f) :
    ∃ K, AntilipschitzWith K f :=
  f.toLinearMap.antilipschitz_of_comap_nhds_le <| map_zero f ▸ (hf.nhds_eq_comap 0).ge

end ContinuousLinearMap

end

namespace ContinuousLinearMap
variable
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ]
  [NontriviallyNormedField 𝕜₁] [NormedSpace 𝕜₁ E]
  [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜₂ F]
  [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₃₂ : 𝕜₃ →+* 𝕜₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : 𝕜₁ →+* 𝕜₃} [RingHomIsometric σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

@[simp]
/-
**ContinuousLinearMap.norm_smulRightL** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：norm_smulRightL (c : StrongDual 𝕜 E) [Nontrivial Fₗ] : ‖smulRightL 𝕜 E Fₗ 
c‖ = ‖c‖
参数：c : StrongDual 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.homothety_norm`：homothety_norm [NontrivialTopology E
] (f : E ->SL[σ₁₂] F) {a : Real} (hf : forall x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousLinearMap.norm_smulRight_apply`：norm_smulRight_apply (c : Stro
ngDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖
-/
theorem norm_smulRightL (c : StrongDual 𝕜 E) [Nontrivial Fₗ] : ‖smulRightL 𝕜 E Fₗ c‖ = ‖c‖ :=
  ContinuousLinearMap.homothety_norm _ c.norm_smulRight_apply
/-
**ContinuousLinearMap.norm_smulRightL_le** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：norm_smulRightL_le : ‖smulRightL 𝕜 E Fₗ‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous₂_norm_le`：mkContinuous₂_norm_le (f : E ->ₛₗ[σ₁₃] 
F ->ₛₗ[σ₂₃] G) {C : Real} (h0 : 0 <= C) (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖
y‖) : ‖f.mkContinuous…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma norm_smulRightL_le : ‖smulRightL 𝕜 E Fₗ‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-! ### Composition with isometries -/

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
/-
**ContinuousLinearMap.opNNNorm_comp_linearIsometryEquiv** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：opNNNorm_comp_linearIsometryEquiv [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] 
G) (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E ->SL[σ₁₂] F)‖₊ = ‖f‖₊
参数：f : F ->SL[σ₂₃] G；e : E ≃ₛₗᵢ[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `nnnorm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semin
ormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso
…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Precomposition with a linear isometry preserves the operator norm.
-/
lemma opNNNorm_comp_linearIsometryEquiv [RingHomIsometric σ₂₃] (f : F →SL[σ₂₃] G)
    (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E →SL[σ₁₂] F)‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun r ↦ by simp [opNNNorm_le_iff, ← e.forall_congr_right]

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
/-
**ContinuousLinearMap.opNNNorm_linearIsometryEquiv_comp** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：opNNNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] 
G) (f : E ->SL[σ₁₂] F) : ‖(e : F ->SL[σ₂₃] G).comp f‖₊ = ‖f‖₊
参数：e : F ≃ₛₗᵢ[σ₂₃] G；f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nnnorm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semin
ormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso
…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Postcomposition with a linear isometry preserves the operator norm.
-/
lemma opNNNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
    (f : E →SL[σ₁₂] F) : ‖(e : F →SL[σ₂₃] G).comp f‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun r ↦ by simp [opNNNorm_le_iff]

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
/-
**ContinuousLinearMap.opNorm_comp_linearIsometryEquiv** 是 Mathlib 中的一个引理，位于命名空间 
`ContinuousLinearMap`。
形式化陈述：opNorm_comp_linearIsometryEquiv [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G)
 (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E ->SL[σ₁₂] F)‖ = ‖f‖
参数：f : F ->SL[σ₂₃] G；e : E ≃ₛₗᵢ[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousLinearMap.opNNNorm_comp_linearIsometryEquiv`：opNNNorm_comp_lin
earIsometryEquiv [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G) (e : E ≃ₛₗᵢ[σ₁₂] F) 
: ‖f.comp (e : E ->SL[σ₁₂] F)‖₊ = ‖f‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Precomposition with a linear isometry preserves the operator norm.
-/
lemma opNorm_comp_linearIsometryEquiv [RingHomIsometric σ₂₃] (f : F →SL[σ₂₃] G)
    (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E →SL[σ₁₂] F)‖ = ‖f‖ := by simp [← coe_nnnorm]

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
/-
**ContinuousLinearMap.opNorm_linearIsometryEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 
`ContinuousLinearMap`。
形式化陈述：opNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
 (f : E ->SL[σ₁₂] F) : ‖(e : F ->SL[σ₂₃] G).comp f‖ = ‖f‖
参数：e : F ≃ₛₗᵢ[σ₂₃] G；f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousLinearMap.opNNNorm_linearIsometryEquiv_comp`：opNNNorm_linearIs
ometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G) (f : E ->SL[σ₁₂] F) 
: ‖(e : F ->SL[σ₂₃] G).comp f‖₊ = ‖f‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Postcomposition with a linear isometry preserves the operator norm.
-/
lemma opNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
    (f : E →SL[σ₁₂] F) : ‖(e : F →SL[σ₂₃] G).comp f‖ = ‖f‖ := by simp [← coe_nnnorm]

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
/-
**ContinuousLinearMap.opNNNorm_mul_linearIsometryEquiv** 是 Mathlib 中的一个引理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：opNNNorm_mul_linearIsometryEquiv (f : E ->L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * 
e‖₊ = ‖f‖₊
参数：f : E ->L[𝕜] E；e : E ≃ₗᵢ[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.opNNNorm_comp_linearIsometryEquiv`：opNNNorm_comp_lin
earIsometryEquiv [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G) (e : E ≃ₛₗᵢ[σ₁₂] F) 
: ‖f.comp (e : E ->SL[σ₁₂] F)‖₊ = ‖f‖₊

--- 原说明 ---
Precomposition with a linear isometry preserves the operator norm.
-/
lemma opNNNorm_mul_linearIsometryEquiv (f : E →L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * e‖₊ = ‖f‖₊ :=
  opNNNorm_comp_linearIsometryEquiv ..

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
/-
**ContinuousLinearMap.opNNNorm_linearIsometryEquiv_mul** 是 Mathlib 中的一个引理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：opNNNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E ->L[𝕜] E) : ‖e * 
f‖₊ = ‖f‖₊
参数：e : E ≃ₗᵢ[𝕜] E；f : E ->L[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.opNNNorm_linearIsometryEquiv_comp`：opNNNorm_linearIs
ometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G) (f : E ->SL[σ₁₂] F) 
: ‖(e : F ->SL[σ₂₃] G).comp f‖₊ = ‖f‖₊

--- 原说明 ---
Postcomposition with a linear isometry preserves the operator norm.
-/
lemma opNNNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E →L[𝕜] E) : ‖e * f‖₊ = ‖f‖₊ :=
  opNNNorm_linearIsometryEquiv_comp ..

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
/-
**ContinuousLinearMap.opNorm_mul_linearIsometryEquiv** 是 Mathlib 中的一个引理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：opNorm_mul_linearIsometryEquiv (f : E ->L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * e‖
 = ‖f‖
参数：f : E ->L[𝕜] E；e : E ≃ₗᵢ[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.opNorm_comp_linearIsometryEquiv`：opNorm_comp_linearI
sometryEquiv [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G) (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f
.comp (e : E ->SL[σ₁₂] F)‖ = ‖f‖

--- 原说明 ---
Precomposition with a linear isometry preserves the operator norm.
-/
lemma opNorm_mul_linearIsometryEquiv (f : E →L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * e‖ = ‖f‖ :=
  opNorm_comp_linearIsometryEquiv ..

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
/-
**ContinuousLinearMap.opNorm_linearIsometryEquiv_mul** 是 Mathlib 中的一个引理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：opNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E ->L[𝕜] E) : ‖e * f‖
 = ‖f‖
参数：e : E ≃ₗᵢ[𝕜] E；f : E ->L[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.opNorm_linearIsometryEquiv_comp`：opNorm_linearIsomet
ryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G) (f : E ->SL[σ₁₂] F) : ‖(
e : F ->SL[σ₂₃] G).comp f‖ = ‖f‖

--- 原说明 ---
Postcomposition with a linear isometry preserves the operator norm.
-/
lemma opNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E →L[𝕜] E) : ‖e * f‖ = ‖f‖ :=
  opNorm_linearIsometryEquiv_comp ..

end ContinuousLinearMap

namespace Submodule

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

/-
**Submodule.norm_subtypeL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：norm_subtypeL (K : Submodule 𝕜 E) [Nontrivial K] : ‖K.subtypeL‖ = 1
参数：K : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u
_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 : 
SeminormedAddCommGroup F] [inst…
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
-/
theorem norm_subtypeL (K : Submodule 𝕜 E) [Nontrivial K] : ‖K.subtypeL‖ = 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap

end Submodule

namespace ContinuousLinearEquiv

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂]

section

variable [RingHomIsometric σ₂₁]

/-
**ContinuousLinearEquiv.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : Type u_5} {F : Type u_6} [inst : Nor
medAddCommGroup E]   [inst_1 : NormedAddCommGroup F] [inst_2 : NontriviallyNorme
dField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂]   [inst_4 : NormedSpace 𝕜 E] [in
st_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜}   [inst_6 : RingHomIn
vPair σ₁₂ σ₂₁] [inst_7 : RingHomInvPair σ₂₁ σ₁₂] [inst_8 : RingHomIsometric σ₂₁]
   (e : E ≃SL[σ₁₂] F), AntilipschitzWith ‖↑e.symm‖₊ ⇑e
参数：e : E ≃SL[σ₁₂] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.to_rightInverse`：LipschitzWith.to_rightInverse [PseudoEMet
ricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β} (hf : LipschitzWit
h K f) {g : β -> α}…
· 使用定理 `ContinuousLinearEquiv.lipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Nontrivia
llyNormedField 𝕜₂] [i…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
-/
protected theorem antilipschitz (e : E ≃SL[σ₁₂] F) :
    AntilipschitzWith ‖(e.symm : F →SL[σ₂₁] E)‖₊ e :=
  e.symm.lipschitz.to_rightInverse e.left_inv
/-
**ContinuousLinearEquiv.one_le_norm_mul_norm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearEquiv`。
形式化陈述：one_le_norm_mul_norm_symm [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL
[σ₁₂] F) : 1 <= ‖(e : E ->SL[σ₁₂] F)‖ * ‖(e.symm : F ->SL[σ₂₁] E)‖
参数：e : E ≃SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.coe_symm_comp_coe`：coe_symm_comp_coe (e : M₁ ≃SL[σ
₁₂] M₂) : (e.symm : M₂ ->SL[σ₂₁] M₁).comp (e : M₁ ->SL[σ₁₂] M₂) = ContinuousLine
arMap.id R₁ M₁
· 使用定理 `ContinuousLinearMap.norm_id`：norm_id [NontrivialTopology E] : ‖Continuou
sLinearMap.id 𝕜 E‖ = 1
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
-/
theorem one_le_norm_mul_norm_symm [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    1 ≤ ‖(e : E →SL[σ₁₂] F)‖ * ‖(e.symm : F →SL[σ₂₁] E)‖ := by
  rw [mul_comm]
  convert! (e.symm : F →SL[σ₂₁] E).opNorm_comp_le (e : E →SL[σ₁₂] F)
  rw [e.coe_symm_comp_coe, ContinuousLinearMap.norm_id]
/-
**ContinuousLinearEquiv.norm_pos** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：norm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) : 0 < ‖(
e : E ->SL[σ₁₂] F)‖
参数：e : E ≃SL[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_of_mul_pos_left`：pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a 
* b) (hb : 0 <= b) : 0 < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ContinuousLinearEquiv.one_le_norm_mul_norm_symm`：one_le_norm_mul_norm_sy
mm [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) : 1 <= ‖(e : E ->SL[
σ₁₂] F)‖ * ‖(e.symm : F ->SL[σ₂₁] E)‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e : E →SL[σ₁₂] F)‖ :=
  pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)
/-
**ContinuousLinearEquiv.norm_symm_pos** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：norm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) : 0
 < ‖(e.symm : F ->SL[σ₂₁] E)‖
参数：e : E ≃SL[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_of_mul_pos_right`：pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < 
a * b) (ha : 0 <= a) : 0 < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ContinuousLinearEquiv.one_le_norm_mul_norm_symm`：one_le_norm_mul_norm_sy
mm [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) : 1 <= ‖(e : E ->SL[
σ₁₂] F)‖ * ‖(e.symm : F ->SL[σ₂₁] E)‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖ :=
  pos_of_mul_pos_right (zero_lt_one.trans_le e.one_le_norm_mul_norm_symm) (norm_nonneg _)
/-
**ContinuousLinearEquiv.nnnorm_symm_pos** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：nnnorm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
 0 < ‖(e.symm : F ->SL[σ₂₁] E)‖₊
参数：e : E ≃SL[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.norm_symm_pos`：norm_symm_pos [RingHomIsometric σ₁₂
] [Nontrivial E] (e : E ≃SL[σ₁₂] F) : 0 < ‖(e.symm : F ->SL[σ₂₁] E)‖
-/
theorem nnnorm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  e.norm_symm_pos
/-
**ContinuousLinearEquiv.subsingleton_or_norm_symm_pos** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearEquiv`。
形式化陈述：subsingleton_or_norm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) : 
Subsingleton E ∨ 0 < ‖(e.symm : F ->SL[σ₂₁] E)‖
参数：e : E ≃SL[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `ContinuousLinearEquiv.norm_symm_pos`：norm_symm_pos [RingHomIsometric σ₁₂
] [Nontrivial E] (e : E ≃SL[σ₁₂] F) : 0 < ‖(e.symm : F ->SL[σ₂₁] E)‖
-/
theorem subsingleton_or_norm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖ := by
  rcases subsingleton_or_nontrivial E with (_i | _i)
  · left
    infer_instance
  · right
    exact e.norm_symm_pos
/-
**ContinuousLinearEquiv.subsingleton_or_nnnorm_symm_pos** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearEquiv`。
形式化陈述：subsingleton_or_nnnorm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) 
: Subsingleton E ∨ 0 < ‖(e.symm : F ->SL[σ₂₁] E)‖₊
参数：e : E ≃SL[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.subsingleton_or_norm_symm_pos`：subsingleton_or_nor
m_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) : Subsingleton E ∨ 0 < ‖(e.
symm : F ->SL[σ₂₁] E)‖
-/
theorem subsingleton_or_nnnorm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  subsingleton_or_norm_symm_pos e

variable (𝕜)

@[simp]
/-
**ContinuousLinearEquiv.coord_norm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：coord_norm (x : E) (h : x != 0) : ‖coord 𝕜 x h‖ = ‖x‖⁻¹
参数：x : E；h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Submodule.nontrivial_span_singleton`：nontrivial_span_singleton {x : M} (
h : x != 0) : Nontrivial (R ∙ x)
· 使用定理 `ContinuousLinearMap.homothety_norm`：homothety_norm [NontrivialTopology E
] (f : E ->SL[σ₁₂] F) {a : Real} (hf : forall x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `ContinuousLinearEquiv.homothety_inverse`：ContinuousLinearEquiv.homothety
_inverse (a : Real) (ha : 0 < a) (f : E ≃ₛₗ[σ] F) : (forall x : E, ‖f x‖ = a * ‖
x‖) -> forall y : F, ‖f.symm …
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LinearEquiv.toSpanNonzeroSingleton_homothety`：∀ (𝕜 : Type u_1) {E : Type
 u_2} [inst : NormedDivisionRing 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_
2 : _root_.Module 𝕜 E] [NormSMulCl…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
theorem coord_norm (x : E) (h : x ≠ 0) : ‖coord 𝕜 x h‖ = ‖x‖⁻¹ := by
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
  have : Nontrivial (𝕜 ∙ x) := Submodule.nontrivial_span_singleton h
  exact ContinuousLinearMap.homothety_norm _ fun y =>
    homothety_inverse _ hx _ (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h) _

end

end ContinuousLinearEquiv

end Normed

/-- A bounded bilinear form `B` in a real normed space is *coercive*
if there is some positive constant C such that `C * ‖u‖ * ‖u‖ ≤ B u u`.
-/
/-
**IsCoercive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCoercive [SeminormedAddCommGroup E] [NormedSpace Real E] (B : E ->L[Real
] E ->L[Real] Real) : Prop
参数：B : E ->L[Real] E ->L[Real] Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
A bounded bilinear form `B` in a real normed space is *coercive*
if there is some positive constant C such that `C * ‖u‖ * ‖u‖ ≤ B u u`.
-/
def IsCoercive [SeminormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∃ C, 0 < C ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u

section Equicontinuous

variable {ι : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [RingHomIsometric σ₁₂] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] (f : ι → E →SL[σ₁₂] F)

/-- Equivalent characterizations for equicontinuity of a family of continuous linear maps
between normed spaces. See also `WithSeminorms.equicontinuous_TFAE` for similar characterizations
between spaces satisfying `WithSeminorms`. -/
/-
**NormedSpace.equicontinuous_TFAE** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : Type u_5} {F : Type u_6} {ι : Type u
_9} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NontriviallyNormedField 𝕜₂] {
σ₁₂ : 𝕜 →+* 𝕜₂} [inst_2 : RingHomIsometric σ₁₂]   [inst_3 : SeminormedAddCommGro
up E] [inst_4 : SeminormedAddCommGroup F] [inst_5 : NormedSpace 𝕜 E]   [inst_6 :
 NormedSpace 𝕜₂ F] (f : ι → E →SL[σ₁₂] F),   [EquicontinuousAt (DFunLike.coe ∘ f
) 0, Equicontinuous (DFunLike.coe ∘ f), UniformEquicontinuous (DFunLike.coe ∘ f)
,       ∃ C, ∀ (i : ι) (x : E), ‖(f i) x‖ ≤ C * ‖x‖, ∃ C ≥ 0, ∀ (i : ι) (x : E),
 ‖(f i) x‖ ≤ C * ‖x‖,       ∃ C, ∀ (i : ι), ‖f i‖ ≤ C, ∃ C ≥ 0, ∀ (i : ι), ‖f i‖
 ≤ C, BddAbove (Set.range fun x => ‖f x‖),       ⨆ i, ↑‖f i‖₊ < ⊤].TFAE
参数：f : ι → E →SL[σ₁₂] F；DFunLike.coe ∘ f；DFunLike.coe ∘ f；DFunLike.coe ∘ f；i : ι
；x : E；f i；i : ι；x : E；f i；i : ι；i : ι；Set.range fun x => ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformEquicontinuous_of_equicontinuousAt_zero`：∀ {ι : Type u_1} {G : Ty
pe u_2} {M : Type u_3} {hom : Type u_4} [inst : UniformSpace G] [inst_1 : Unifor
mSpace M]   [inst_2 : AddGroup G] [i…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformEquicontinuous.equicontinuous`：UniformEquicontinuous.equicontinuo
us {F : ι -> β -> α} (h : UniformEquicontinuous F) : Equicontinuous F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_ge_and_iff_exists`：exists_ge_and_iff_exists [SemilatticeSup α] {P
 : α -> Prop} {x₀ : α} (hP : Monotone P) : (exists x, x₀ <= x ∧ P x) ↔ exists x,
 P x
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
· 使用定理 `le_trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → c ≤
 b → c ≤ a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `ContinuousLinearMap.opNorm_le_iff`：opNorm_le_iff {f : E ->SL[σ₁₂] F} {M 
: Real} (hMp : 0 <= M) : ‖f‖ <= M ↔ forall x, ‖f x‖ <= M * ‖x‖
· 使用定理 `bddAbove_iff_exists_ge`：bddAbove_iff_exists_ge [SemilatticeSup γ] {s : S
et γ} (x₀ : γ) : BddAbove s ↔ exists x, x₀ <= x ∧ forall y in s, y <= x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `ENNReal.iSup_coe_lt_top`：iSup_coe_lt_top : ⨆ i, (f i : Real>=0∞) < ⊤ ↔ B
ddAbove (range f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.bddAbove_coe`：bddAbove_coe {s : Set Real>=0} : BddAbove (((↑) : R
eal>=0 -> Real) '' s) ↔ BddAbove s
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm`：unif
ormEquicontinuous_iff_exists_continuous_seminorm {κ : Type*} {q : SeminormFamily
 𝕜₂ F ι'} [UniformSpace E] [IsUniformAddGroup E] [u : Un…
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Equivalent characterizations for equicontinuity of a family of continuous linear
 maps
between normed spaces. See also `WithSeminorms.equicontinuous_TFAE` for similar 
characterizations
between spaces satisfying `WithSeminorms`.
-/
protected theorem NormedSpace.equicontinuous_TFAE : List.TFAE
    [ EquicontinuousAt ((↑) ∘ f) 0,
      Equicontinuous ((↑) ∘ f),
      UniformEquicontinuous ((↑) ∘ f),
      ∃ C, ∀ i x, ‖f i x‖ ≤ C * ‖x‖,
      ∃ C ≥ 0, ∀ i x, ‖f i x‖ ≤ C * ‖x‖,
      ∃ C, ∀ i, ‖f i‖ ≤ C,
      ∃ C ≥ 0, ∀ i, ‖f i‖ ≤ C,
      BddAbove (Set.range (‖f ·‖)),
      (⨆ i, (‖f i‖₊ : ENNReal)) < ⊤ ] := by
  -- `1 ↔ 2 ↔ 3` follows from `uniformEquicontinuous_of_equicontinuousAt_zero`
  tfae_have 1 → 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 → 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 → 1 := fun H ↦ H 0
  -- `4 ↔ 5 ↔ 6 ↔ 7 ↔ 8 ↔ 9` is morally trivial, we just have to use a lot of rewriting
  -- and `congr` lemmas
  tfae_have 4 ↔ 5 := by
    rw [exists_ge_and_iff_exists]
    exact fun C₁ C₂ hC ↦ forall₂_imp fun i x ↦ le_trans' <| by gcongr
  tfae_have 5 ↔ 7 := by
    refine exists_congr (fun C ↦ and_congr_right fun hC ↦ forall_congr' fun i ↦ ?_)
    rw [ContinuousLinearMap.opNorm_le_iff hC]
  tfae_have 7 ↔ 8 := by
    simp_rw [bddAbove_iff_exists_ge (0 : ℝ), Set.forall_mem_range]
  tfae_have 6 ↔ 8 := by
    simp_rw [bddAbove_def, Set.forall_mem_range]
  tfae_have 8 ↔ 9 := by
    rw [ENNReal.iSup_coe_lt_top, ← NNReal.bddAbove_coe, ← Set.range_comp]
    rfl
  -- `3 ↔ 4` is the interesting part of the result. It is essentially a combination of
  -- `WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm` which turns
  -- equicontinuity into existence of some continuous seminorm and
  -- `Seminorm.bound_of_continuous_normedSpace` which characterize such seminorms.
  tfae_have 3 ↔ 4 := by
    refine ((norm_withSeminorms 𝕜₂ F).uniformEquicontinuous_iff_exists_continuous_seminorm _).trans
      ?_
    rw [forall_const]
    constructor
    · intro ⟨p, hp, hpf⟩
      rcases p.bound_of_continuous_normedSpace hp with ⟨C, -, hC⟩
      exact ⟨C, fun i x ↦ (hpf i x).trans (hC x)⟩
    · intro ⟨C, hC⟩
      refine ⟨C.toNNReal • normSeminorm 𝕜 E,
        ((norm_withSeminorms 𝕜 E).continuous_seminorm 0).const_smul C.toNNReal, fun i x ↦ ?_⟩
      exact (hC i x).trans (mul_le_mul_of_nonneg_right (C.le_coe_toNNReal) (norm_nonneg x))
  tfae_finish

end Equicontinuous

section single

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : ι → Type*)

/-- The injection `x ↦ Pi.single i x` as a linear isometry. -/
/-
**LinearIsometry.single** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry`。
形式化陈述：{ι : Type u_9} →   [inst : Fintype ι] →     [DecidableEq ι] →       (𝕜 : T
ype u_10) →         [inst_2 : NontriviallyNormedField 𝕜] →           (E : ι → Ty
pe u_11) →             [inst_3 : (i : ι) → SeminormedAddCommGroup (E i)] →      
         [inst_4 : (i : ι) → NormedSpace 𝕜 (E i)] → (i : ι) → E i →ₗᵢ[𝕜] (j : ι)
 → E j
参数：𝕜 : Type u_10；E : ι → Type u_11；i : ι；E i；i : ι；E i；i : ι；j : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The injection `x ↦ Pi.single i x` as a linear isometry.
-/
protected def LinearIsometry.single [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (i : ι) : E i →ₗᵢ[𝕜] Π j, E j :=
  (LinearMap.single 𝕜 E i).toLinearIsometry (.single i)
/-
**ContinuousLinearMap.norm_single_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_single_le_one [forall i, SeminormedAddCommGroup (
E i)] [forall i, NormedSpace 𝕜 (E i)] (i : ι) : ‖ContinuousLinearMap.single 𝕜 E 
i‖ <= 1
参数：E i；E i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap_le`：norm_toContinuousLinearMap
_le (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ <= 1
-/
lemma ContinuousLinearMap.norm_single_le_one [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] (i : ι) :
    ‖ContinuousLinearMap.single 𝕜 E i‖ ≤ 1 :=
  (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap_le
/-
**ContinuousLinearMap.norm_single** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_single [forall i, SeminormedAddCommGroup (E i)] [
forall i, NormedSpace 𝕜 (E i)] (i : ι) [NontrivialTopology (E i)] : ‖ContinuousL
inearMap.single 𝕜 E i‖ = 1
参数：E i；E i；i : ι；E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u
_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 : 
SeminormedAddCommGroup F] [inst…
-/
lemma ContinuousLinearMap.norm_single [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] (i : ι) [NontrivialTopology (E i)] :
    ‖ContinuousLinearMap.single 𝕜 E i‖ = 1 :=
  (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap

end single

section inl_inr

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E F : Type*)

/-- The injection `x ↦ LinearMap.inl E F x` as a linear isometry. -/
/-
**LinearIsometry.inl** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry`。
形式化陈述：(𝕜 : Type u_9) →   [inst : NontriviallyNormedField 𝕜] →     (E : Type u_10
) →       (F : Type u_11) →         [inst_1 : SeminormedAddCommGroup E] →       
    [inst_2 : NormedSpace 𝕜 E] → [inst_3 : SeminormedAddCommGroup F] → [inst_4 :
 NormedSpace 𝕜 F] → E →ₗᵢ[𝕜] E × F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The injection `x ↦ LinearMap.inl E F x` as a linear isometry.
-/
protected def LinearIsometry.inl [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : E →ₗᵢ[𝕜] E × F :=
  (LinearMap.inl 𝕜 E F).toLinearIsometry .inl

@[simp]
/-
**LinearIsometry.inl_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIsometry.inl_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Sem
inormedAddCommGroup F] [NormedSpace 𝕜 F] (x : E) : LinearIsometry.inl 𝕜 E F x = 
(x, 0)
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LinearIsometry.inl_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (x : E) :
    LinearIsometry.inl 𝕜 E F x = (x, 0) := rfl

/-- The injection `x ↦ LinearMap.inr E F x` as a linear isometry. -/
/-
**LinearIsometry.inr** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry`。
形式化陈述：(𝕜 : Type u_9) →   [inst : NontriviallyNormedField 𝕜] →     (E : Type u_10
) →       (F : Type u_11) →         [inst_1 : SeminormedAddCommGroup E] →       
    [inst_2 : NormedSpace 𝕜 E] → [inst_3 : SeminormedAddCommGroup F] → [inst_4 :
 NormedSpace 𝕜 F] → F →ₗᵢ[𝕜] E × F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The injection `x ↦ LinearMap.inr E F x` as a linear isometry.
-/
protected def LinearIsometry.inr [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : F →ₗᵢ[𝕜] E × F :=
  (LinearMap.inr 𝕜 E F).toLinearIsometry .inr

@[simp]
/-
**LinearIsometry.inr_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIsometry.inr_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Sem
inormedAddCommGroup F] [NormedSpace 𝕜 F] (y : F) : LinearIsometry.inr 𝕜 E F y = 
(0, y)
参数：y : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LinearIsometry.inr_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (y : F) :
    LinearIsometry.inr 𝕜 E F y = (0, y) := rfl
/-
**ContinuousLinearMap.norm_inl_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_inl_le_one [SeminormedAddCommGroup E] [NormedSpac
e 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : ‖ContinuousLinearMap.inl 𝕜
 E F‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap_le`：norm_toContinuousLinearMap
_le (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ <= 1
-/
lemma ContinuousLinearMap.norm_inl_le_one [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.inl 𝕜 E F‖ ≤ 1 :=
  (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap_le
/-
**ContinuousLinearMap.norm_inr_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_inr_le_one [SeminormedAddCommGroup E] [NormedSpac
e 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : ‖ContinuousLinearMap.inr 𝕜
 E F‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap_le`：norm_toContinuousLinearMap
_le (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ <= 1
-/
lemma ContinuousLinearMap.norm_inr_le_one [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.inr 𝕜 E F‖ ≤ 1 :=
  (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap_le
/-
**ContinuousLinearMap.norm_inl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_inl [SeminormedAddCommGroup E] [NontrivialTopolog
y E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : ‖Continuou
sLinearMap.inl 𝕜 E F‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u
_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 : 
SeminormedAddCommGroup F] [inst…
-/
lemma ContinuousLinearMap.norm_inl [SeminormedAddCommGroup E] [NontrivialTopology E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.inl 𝕜 E F‖ = 1 :=
  (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap
/-
**ContinuousLinearMap.norm_inr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_inr [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] 
[SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NontrivialTopology F] : ‖Continuou
sLinearMap.inr 𝕜 E F‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u
_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 : 
SeminormedAddCommGroup F] [inst…
-/
lemma ContinuousLinearMap.norm_inr [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NontrivialTopology F] :
    ‖ContinuousLinearMap.inr 𝕜 E F‖ = 1 :=
  (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap

end inl_inr

