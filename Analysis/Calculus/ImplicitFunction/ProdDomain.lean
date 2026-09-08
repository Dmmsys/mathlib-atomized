/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
module

public import Mathlib.Analysis.Calculus.Implicit

/-!
# Implicit function theorem — domain a product space

This specialization of the implicit function theorem applies to an uncurried bivariate function
`f : E₁ × E₂ → F` and assumes strict differentiability of `f` at `u : E₁ × E₂` as well as
invertibility of `f₂u : E₂ →L[𝕜] F` its partial derivative with respect to the second argument.

It proves the existence of `ψ : E₁ → E₂` such that for `v` in a neighbourhood of `u` we have
`f v = f u ↔ ψ v.1 = v.2`. This is `HasStrictFDerivAt.implicitFunctionOfProdDomain`. A formula for
its first derivative follows.

A similar specialization is made to a curried bivariate function by `implicitFunctionOfBivariate` in
a sister file .

## Tags

implicit function
-/

public section

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}

/-- Given `f : E₁ × E₂ → F` strictly differentiable at `u` with invertible partial derivative
`f₂u : E₂ →L[𝕜] F`, we may construct an `ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁` with `f` as its
`leftFun` and `Prod.fst : E₁ × E₂ → E₁` as its `rightFun` by proving that the kernels of the
associated `leftDeriv` and `rightDeriv` are complementary. -/
/-
**HasStrictFDerivAt.implicitFunctionDataOfProdDomain** 是 Mathlib 中的一个定义，位于命名空间 `
HasStrictFDerivAt`。
形式化陈述：implicitFunctionDataOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u :
 (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ whe
re leftFun
参数：dfu : HasStrictFDerivAt f f'u u；if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_fst`：hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.
fst E F) (fst 𝕜 E F) p

--- 原说明 ---
Given `f : E₁ × E₂ → F` strictly differentiable at `u` with invertible partial d
erivative
`f₂u : E₂ →L[𝕜] F`, we may construct an `ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁` 
with `f` as its
`leftFun` and `Prod.fst : E₁ × E₂ → E₁` as its `rightFun` by proving that the ke
rnels of the
associated `leftDeriv` and `rightDeriv` are complementary.
-/
def implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ where
  leftFun := f
  rightFun := Prod.fst
  pt := u
  leftDeriv := f'u
  hasStrictFDerivAt_leftFun := dfu
  rightDeriv := .fst 𝕜 E₁ E₂
  hasStrictFDerivAt_rightFun := hasStrictFDerivAt_fst
  range_leftDeriv := by
    have : (f'u ∘L .inr 𝕜 E₁ E₂).range ≤ f'u.range := LinearMap.range_comp_le_range ..
    rwa [LinearMap.range_eq_top.mpr if₂u.surjective, top_le_iff] at this
  range_rightDeriv := Submodule.range_fst
  isCompl_ker := by
    constructor
    · rw [LinearMap.disjoint_ker]
      intro (_, y) h rfl
      simpa using (injective_iff_map_eq_zero _).mp if₂u.injective y h
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro v
      have ⟨y, hy⟩ := if₂u.surjective (f'u v)
      use v - (0, y), (0, y)
      aesop
/-
**HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain** 是 Mathlib 中的一个定理，位于命名空
间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_
1 : NormedAddCommGroup E₁]   [inst_2 : NormedSpace 𝕜 E₁] [inst_3 : CompleteSpace
 E₁] {E₂ : Type u_3} [inst_4 : NormedAddCommGroup E₂]   [inst_5 : NormedSpace 𝕜 
E₂] [inst_6 : CompleteSpace E₂] {F : Type u_4} [inst_7 : NormedAddCommGroup F]  
 [inst_8 : NormedSpace 𝕜 F] [inst_9 : CompleteSpace F] {u : E₁ × E₂} {f : E₁ × E
₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}   (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u 
∘SL ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible),   (dfu.implicitFunctionDataO
fProdDomain if₂u).pt = u
参数：dfu : HasStrictFDerivAt f f'u u；if₂u : (f'u ∘SL ContinuousLinearMap.inr 𝕜 E₁ 
E₂).IsInvertible；dfu.implicitFunctionDataOfProdDomain if₂u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem pt_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).pt = u := by
  rfl
/-
**HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain** 是 Mathlib 中的一个定理，
位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_
1 : NormedAddCommGroup E₁]   [inst_2 : NormedSpace 𝕜 E₁] [inst_3 : CompleteSpace
 E₁] {E₂ : Type u_3} [inst_4 : NormedAddCommGroup E₂]   [inst_5 : NormedSpace 𝕜 
E₂] [inst_6 : CompleteSpace E₂] {F : Type u_4} [inst_7 : NormedAddCommGroup F]  
 [inst_8 : NormedSpace 𝕜 F] [inst_9 : CompleteSpace F] {u : E₁ × E₂} {f : E₁ × E
₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}   (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u 
∘SL ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible),   (dfu.implicitFunctionDataO
fProdDomain if₂u).leftFun = f
参数：dfu : HasStrictFDerivAt f f'u u；if₂u : (f'u ∘SL ContinuousLinearMap.inr 𝕜 E₁ 
E₂).IsInvertible；dfu.implicitFunctionDataOfProdDomain if₂u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem leftFun_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).leftFun = f := by
  rfl
/-
**HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain** 是 Mathlib 中的一个定理
，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_
1 : NormedAddCommGroup E₁]   [inst_2 : NormedSpace 𝕜 E₁] [inst_3 : CompleteSpace
 E₁] {E₂ : Type u_3} [inst_4 : NormedAddCommGroup E₂]   [inst_5 : NormedSpace 𝕜 
E₂] [inst_6 : CompleteSpace E₂] {F : Type u_4} [inst_7 : NormedAddCommGroup F]  
 [inst_8 : NormedSpace 𝕜 F] [inst_9 : CompleteSpace F] {u : E₁ × E₂} {f : E₁ × E
₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}   (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u 
∘SL ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible),   (dfu.implicitFunctionDataO
fProdDomain if₂u).rightFun = Prod.fst
参数：dfu : HasStrictFDerivAt f f'u u；if₂u : (f'u ∘SL ContinuousLinearMap.inr 𝕜 E₁ 
E₂).IsInvertible；dfu.implicitFunctionDataOfProdDomain if₂u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem rightFun_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).rightFun = Prod.fst := by
  rfl

/-- Implicit function `ψ : E₁ → E₂` associated with the (uncurried) bivariate function
`f : E₁ × E₂ → F` at `u : E₁ × E₂`. -/
/-
**HasStrictFDerivAt.implicitFunctionOfProdDomain** 是 Mathlib 中的一个定义，位于命名空间 `HasS
trictFDerivAt`。
形式化陈述：implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'
u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : E₁ -> E₂
参数：dfu : HasStrictFDerivAt f f'u u；if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implicit function `ψ : E₁ → E₂` associated with the (uncurried) bivariate functi
on
`f : E₁ × E₂ → F` at `u : E₁ × E₂`.
-/
noncomputable def implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    E₁ → E₂ :=
  fun x => ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction (f u) x).2
/-
**HasStrictFDerivAt.implicitFunctionOfProdDomain_def** 是 Mathlib 中的一个定理，位于命名空间 `
HasStrictFDerivAt`。
形式化陈述：implicitFunctionOfProdDomain_def {dfu : HasStrictFDerivAt f f'u u} {if₂u :
 (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible} : dfu.implicitFunctionOfProdDomain if₂u = f
un x => ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction (f u) x).2
参数：f'u ∘L .inr 𝕜 E₁ E₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem implicitFunctionOfProdDomain_def
    {dfu : HasStrictFDerivAt f f'u u} {if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible} :
    dfu.implicitFunctionOfProdDomain if₂u =
      fun x => ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction (f u) x).2 := by
  rfl
/-
**HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain** 是 Mat
hlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：eventually_apply_eq_iff_implicitFunctionOfProdDomain (dfu : HasStrictFDeri
vAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ v in 𝓝 u, f v
 = f u ↔ dfu.implicitFunctionOfProdDomain if₂u v.1 = v.2
参数：dfu : HasStrictFDerivAt f f'u u；if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ImplicitFunctionData.rightFun_implicitFunction_eq_rightFun`：rightFun_imp
licitFunction_eq_rightFun : forallᶠ x in 𝓝 φ.pt, φ.rightFun (φ.implicitFunction 
(φ.leftFun φ.pt) (φ.rightFun x)) = φ.rightFun x
· 使用定理 `ImplicitFunctionData.leftFun_eq_iff_implicitFunction`：leftFun_eq_iff_imp
licitFunction : forallᶠ x in 𝓝 φ.pt, φ.leftFun x = φ.leftFun φ.pt ↔ φ.implicitFu
nction (φ.leftFun φ.pt) (φ.rightFun x) = x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain`：∀ {𝕜 : Type u_1} 
[inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_1 : NormedAddCommGroup 
E₁]   [inst_2 : NormedSpace 𝕜 E₁] [inst_3 :…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain`：∀ {𝕜 : Type 
u_1} [inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_1 : NormedAddCommG
roup E₁]   [inst_2 : NormedSpace 𝕜 E₁] [inst_3 :…
· 使用定理 `HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain`：∀ {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_1 : NormedAddComm
Group E₁]   [inst_2 : NormedSpace 𝕜 E₁] [inst_3 :…
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ v in 𝓝 u, f v = f u ↔ dfu.implicitFunctionOfProdDomain if₂u v.1 = v.2 := by
  let φ := dfu.implicitFunctionDataOfProdDomain if₂u
  filter_upwards [φ.leftFun_eq_iff_implicitFunction, φ.rightFun_implicitFunction_eq_rightFun]
  exact fun v h _ => Iff.trans h ⟨congrArg _, by aesop⟩
/-
**HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain** 是 Mathlib 中
的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：hasStrictFDerivAt_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f 
f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : HasStrictFDerivAt (dfu.impl
icitFunctionOfProdDomain if₂u) (-(f'u ∘L .inr 𝕜 E₁ E₂).inverse ∘L (f'u ∘L .inl 𝕜
 E₁ E₂)) u.1
参数：dfu : HasStrictFDerivAt f f'u u；if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.comp_inl_add_comp_inr`：comp_inl_add_comp_inr (L : M₁
 × M₂ ->L[R] M₃) (v : M₁ × M₂) : L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M
₂) v.2 = L v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.IsInvertible.self_apply_inverse`：self_apply_inverse 
(hf : f.IsInvertible) (y : M₂) : f (f.inverse y) = y
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictFDerivAt.snd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt_implicitFunction`：hasStrictFDeriv
At_implicitFunction (g'inv : G ->L[𝕜] E) (hg'inv : φ.rightDeriv.comp g'inv = Con
tinuousLinearMap.id 𝕜 G) (hg'invf : φ.leftDer…
· 使用定理 `ContinuousLinearMap.fst_comp_prod`：fst_comp_prod (f : M₁ ->L[R] M₂) (g :
 M₁ ->L[R] M₃) : (fst R M₂ M₃).comp (f.prod g) = f
-/
theorem hasStrictFDerivAt_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    HasStrictFDerivAt (dfu.implicitFunctionOfProdDomain if₂u)
      (-(f'u ∘L .inr 𝕜 E₁ E₂).inverse ∘L (f'u ∘L .inl 𝕜 E₁ E₂)) u.1 := by
  suffices f'u ∘L (.prod (.id ..) (-(f'u ∘L .inr ..).inverse ∘L (f'u ∘L .inl ..))) = 0 from
    ((dfu.implicitFunctionDataOfProdDomain if₂u).hasStrictFDerivAt_implicitFunction _
      (ContinuousLinearMap.fst_comp_prod _ _) this).snd
  ext
  rw [f'u.comp_apply, ← f'u.comp_inl_add_comp_inr]
  simp [-ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_comp, map_neg, if₂u]
/-
**HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain** 是 Mathlib 中的一个定理，位于命名
空间 `HasStrictFDerivAt`。
形式化陈述：tendsto_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if
₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : Tendsto (dfu.implicitFunctionOfProdDo
main if₂u) (𝓝 u.1) (𝓝 u.2)
参数：dfu : HasStrictFDerivAt f f'u u；if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `HasStrictFDerivAt.continuousAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain`：hasStr
ictFDerivAt_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u
 : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : HasStrictFDer…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain`：
eventually_apply_eq_iff_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f 
f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ…
-/
theorem tendsto_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    Tendsto (dfu.implicitFunctionOfProdDomain if₂u) (𝓝 u.1) (𝓝 u.2) := by
  have := (dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain if₂u).continuousAt.tendsto
  rwa [(dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u).self_of_nhds.mp rfl] at this
/-
**HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain** 是 Mathlib 中的
一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：eventually_apply_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f
'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ x in 𝓝 u.1, f (x, df
u.implicitFunctionOfProdDomain if₂u x) = f u
参数：dfu : HasStrictFDerivAt f f'u u；if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain`：tendsto_implicit
FunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁
 E₂).IsInvertible) : Tendsto (dfu.implicitFu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Eventually.image_of_prod`：∀ {α : Type u_1} {β : Type u_2} {f : Fi
lter α} {g : Filter β} {y : α → β} {r : α → β → Prop},   Filter.Tendsto y f g → 
(∀ᶠ (p : α × β) in f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain`：
eventually_apply_eq_iff_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f 
f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
theorem eventually_apply_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1, f (x, dfu.implicitFunctionOfProdDomain if₂u x) = f u := by
  have hψ := dfu.tendsto_implicitFunctionOfProdDomain if₂u
  set ψ := dfu.implicitFunctionOfProdDomain if₂u
  suffices ∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u ↔ ψ x = ψ x by simpa using this
  apply Eventually.image_of_prod (r := fun x y => f (x, y) = f u ↔ ψ x = y) hψ
  rw [← nhds_prod_eq]
  exact dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u

end HasStrictFDerivAt

end

