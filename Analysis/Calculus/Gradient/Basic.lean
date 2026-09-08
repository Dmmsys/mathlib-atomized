/-
Copyright (c) 2023 Ziyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyu Wang, Chenyi Li, Sébastien Gouëzel, Penghao Yu, Zhipeng Cao
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Gradient

## Main Definitions

Let `f` be a function from a Hilbert Space `F` to `𝕜` (`𝕜` is `ℝ` or `ℂ`), `x` be a point in `F`
and `f'` be a vector in F. Then

  `HasGradientWithinAt f f' s x`

says that `f` has a gradient `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasGradientAt f f' x := HasGradientWithinAt f f' x univ`

## Main results

This file develops the following aspects of the theory of gradients:
* definitions of gradients, both within a set and on the whole space.
* translating between `HasGradientAtFilter` and `HasFDerivAtFilter`,
  `HasGradientWithinAt` and `HasFDerivWithinAt`, `HasGradientAt` and `HasFDerivAt`,
  `gradient` and `fderiv`.
* uniqueness of gradients.
* translating between `HasGradientAtFilter` and `HasDerivAtFilter`,
  `HasGradientAt` and `HasDerivAt`, `gradient` and `deriv` when `F = 𝕜`.
* the theorems about the inner product of the gradient.
* the congruence of the gradient.
* the gradient of constant functions.
* the continuity of a function admitting a gradient.
-/

@[expose] public section

@[expose] public section

open ComplexConjugate Topology InnerProductSpace Function Set

noncomputable section

variable {𝕜 F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {f : F → 𝕜} {f' x y : F}

/-- A function `f` has the gradient `f'` as derivative along the filter `L` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` when `x'` converges along the filter `L`. -/
/-
**HasGradientAtFilter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasGradientAtFilter (f : F -> 𝕜) (f' x : F) (L : Filter F)
参数：f : F -> 𝕜；f' x : F；L : Filter F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` has the gradient `f'` as derivative along the filter `L` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` when `x'` converges along the filter 
`L`.
-/
def HasGradientAtFilter (f : F → 𝕜) (f' x : F) (L : Filter F) :=
  HasFDerivAtFilter f (toDual 𝕜 F f') (L ×ˢ pure x)

/-- `f` has the gradient `f'` at the point `x` within the subset `s` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x` inside `s`. -/
/-
**HasGradientWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasGradientWithinAt (f : F -> 𝕜) (f' : F) (s : Set F) (x : F)
参数：f : F -> 𝕜；f' : F；s : Set F；x : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has the gradient `f'` at the point `x` within the subset `s` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x` inside `s
`.
-/
def HasGradientWithinAt (f : F → 𝕜) (f' : F) (s : Set F) (x : F) :=
  HasGradientAtFilter f f' x (𝓝[s] x)

/-- `f` has the gradient `f'` at the point `x` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x`. -/
/-
**HasGradientAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasGradientAt (f : F -> 𝕜) (f' x : F)
参数：f : F -> 𝕜；f' x : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has the gradient `f'` at the point `x` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x`.
-/
def HasGradientAt (f : F → 𝕜) (f' x : F) :=
  HasGradientAtFilter f f' x (𝓝 x)

/-- Gradient of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasGradientWithinAt f f' s x`), then
`f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x` inside `s`. -/
/-
**gradientWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gradientWithin (f : F -> 𝕜) (s : Set F) (x : F) : F
参数：f : F -> 𝕜；s : Set F；x : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Gradient of `f` at the point `x` within the set `s`, if it exists.  Zero otherwi
se.

If the derivative exists (i.e., `∃ f', HasGradientWithinAt f f' s x`), then
`f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x` inside `s`.
-/
def gradientWithin (f : F → 𝕜) (s : Set F) (x : F) : F :=
  (toDual 𝕜 F).symm (fderivWithin 𝕜 f s x)

/-- Gradient of `f` at the point `x`, if it exists.  Zero otherwise.
Denoted as `∇` within the Gradient namespace.

If the derivative exists (i.e., `∃ f', HasGradientAt f f' x`), then
`f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x`. -/
/-
**gradient** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gradient (f : F -> 𝕜) (x : F) : F
参数：f : F -> 𝕜；x : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Gradient of `f` at the point `x`, if it exists.  Zero otherwise.
Denoted as `∇` within the Gradient namespace.

If the derivative exists (i.e., `∃ f', HasGradientAt f f' x`), then
`f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x`.
-/
def gradient (f : F → 𝕜) (x : F) : F :=
  (toDual 𝕜 F).symm (fderiv 𝕜 f x)

@[inherit_doc]
scoped[Gradient] notation "∇" => gradient

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped Gradient

variable {s : Set F} {L : Filter F}
/-
**hasGradientWithinAt_iff_hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientWithinAt_iff_hasFDerivWithinAt {s : Set F} : HasGradientWithinA
t f f' s x ↔ HasFDerivWithinAt f (toDual 𝕜 F f') s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasGradientWithinAt_iff_hasFDerivWithinAt {s : Set F} :
    HasGradientWithinAt f f' s x ↔ HasFDerivWithinAt f (toDual 𝕜 F f') s x :=
  Iff.rfl
/-
**hasFDerivWithinAt_iff_hasGradientWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_iff_hasGradientWithinAt {frechet : StrongDual 𝕜 F} {s : 
Set F} : HasFDerivWithinAt f frechet s x ↔ HasGradientWithinAt f ((toDual 𝕜 F).s
ymm frechet) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasGradientWithinAt_iff_hasFDerivWithinAt`：hasGradientWithinAt_iff_hasFD
erivWithinAt {s : Set F} : HasGradientWithinAt f f' s x ↔ HasFDerivWithinAt f (t
oDual 𝕜 F f') s x
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasFDerivWithinAt_iff_hasGradientWithinAt {frechet : StrongDual 𝕜 F} {s : Set F} :
    HasFDerivWithinAt f frechet s x ↔ HasGradientWithinAt f ((toDual 𝕜 F).symm frechet) s x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, (toDual 𝕜 F).apply_symm_apply frechet]
/-
**hasGradientAt_iff_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientAt_iff_hasFDerivAt : HasGradientAt f f' x ↔ HasFDerivAt f (toDu
al 𝕜 F f') x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasGradientAt_iff_hasFDerivAt :
    HasGradientAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x :=
  Iff.rfl
/-
**hasFDerivAt_iff_hasGradientAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_iff_hasGradientAt {frechet : StrongDual 𝕜 F} : HasFDerivAt f f
rechet x ↔ HasGradientAt f ((toDual 𝕜 F).symm frechet) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasGradientAt_iff_hasFDerivAt`：hasGradientAt_iff_hasFDerivAt : HasGradie
ntAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasFDerivAt_iff_hasGradientAt {frechet : StrongDual 𝕜 F} :
    HasFDerivAt f frechet x ↔ HasGradientAt f ((toDual 𝕜 F).symm frechet) x := by
  rw [hasGradientAt_iff_hasFDerivAt, (toDual 𝕜 F).apply_symm_apply frechet]

alias ⟨HasGradientWithinAt.hasFDerivWithinAt, _⟩ := hasGradientWithinAt_iff_hasFDerivWithinAt

alias ⟨HasFDerivWithinAt.hasGradientWithinAt, _⟩ := hasFDerivWithinAt_iff_hasGradientWithinAt

alias ⟨HasGradientAt.hasFDerivAt, _⟩ := hasGradientAt_iff_hasFDerivAt

alias ⟨HasFDerivAt.hasGradientAt, _⟩ := hasFDerivAt_iff_hasGradientAt
/-
**gradient_eq_zero_of_not_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gradient_eq_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : ∇
 f x = 0
参数：h : ¬DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gradient.eq_1`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLike 𝕜] [inst_1
 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 : CompleteSp
ace…
· 使用定理 `fderiv_zero_of_not_differentiableAt`：fderiv_zero_of_not_differentiableAt
 (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
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
-/
theorem gradient_eq_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : ∇ f x = 0 := by
  rw [gradient, fderiv_zero_of_not_differentiableAt h, map_zero]

@[simp]
/-
**toDual_gradientWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toDual_gradientWithin : (toDual 𝕜 F) (gradientWithin f s x) = fderivWithin
 𝕜 f s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gradientWithin.eq_1`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLike 𝕜] [
inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 : Comp
leteSpace…
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
-/
lemma toDual_gradientWithin :
    (toDual 𝕜 F) (gradientWithin f s x) = fderivWithin 𝕜 f s x := by
  rw [gradientWithin, (toDual 𝕜 F).apply_symm_apply]

@[simp]
/-
**toDual_gradient** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toDual_gradient : (toDual 𝕜 F) (∇ f x) = fderiv 𝕜 f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gradient.eq_1`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLike 𝕜] [inst_1
 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 : CompleteSp
ace…
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
-/
lemma toDual_gradient : (toDual 𝕜 F) (∇ f x) = fderiv 𝕜 f x := by
  rw [gradient, (toDual 𝕜 F).apply_symm_apply]

@[simp]
/-
**toDual_comp_gradientWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toDual_comp_gradientWithin : (toDual 𝕜 F) ∘ gradientWithin f s = fderivWit
hin 𝕜 f s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `toDual_gradientWithin`：toDual_gradientWithin : (toDual 𝕜 F) (gradientWit
hin f s x) = fderivWithin 𝕜 f s x
-/
lemma toDual_comp_gradientWithin :
    (toDual 𝕜 F) ∘ gradientWithin f s = fderivWithin 𝕜 f s :=
  funext fun _ => toDual_gradientWithin

@[simp]
/-
**toDual_comp_gradient** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toDual_comp_gradient : (toDual 𝕜 F) ∘ ∇ f = fderiv 𝕜 f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `toDual_gradient`：toDual_gradient : (toDual 𝕜 F) (∇ f x) = fderiv 𝕜 f x
-/
lemma toDual_comp_gradient : (toDual 𝕜 F) ∘ ∇ f = fderiv 𝕜 f :=
  funext fun _ => toDual_gradient
/-
**HasGradientAt.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAt.unique {gradf gradg : F} (hf : HasGradientAt f gradf x) (hg 
: HasGradientAt f gradg x) : gradf = gradg
参数：hf : HasGradientAt f gradf x；hg : HasGradientAt f gradg x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Typ
e u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+*
 R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.unique`：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : H
asFDerivAt f f₁' x) : f' = f₁'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasGradientAt.hasFDerivAt`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLik
e 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 
: CompleteSpace…
-/
theorem HasGradientAt.unique {gradf gradg : F}
    (hf : HasGradientAt f gradf x) (hg : HasGradientAt f gradg x) :
    gradf = gradg :=
  (toDual 𝕜 F).injective (hf.hasFDerivAt.unique hg.hasFDerivAt)
/-
**DifferentiableAt.hasGradientAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.hasGradientAt (h : DifferentiableAt 𝕜 f x) : HasGradientA
t f (∇ f x) x
参数：h : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `toDual_gradient`：toDual_gradient : (toDual 𝕜 F) (∇ f x) = fderiv 𝕜 f x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.hasGradientAt (h : DifferentiableAt 𝕜 f x) :
    HasGradientAt f (∇ f x) x := by
  simpa [hasGradientAt_iff_hasFDerivAt] using h.hasFDerivAt
/-
**HasGradientAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAt.differentiableAt (h : HasGradientAt f f' x) : Differentiable
At 𝕜 f x
参数：h : HasGradientAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasGradientAt.hasFDerivAt`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLik
e 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 
: CompleteSpace…
-/
theorem HasGradientAt.differentiableAt (h : HasGradientAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt
/-
**DifferentiableWithinAt.hasGradientWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.hasGradientWithinAt (h : DifferentiableWithinAt 𝕜 f
 s x) : HasGradientWithinAt f (gradientWithin f s x) s x
参数：h : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `toDual_gradientWithin`：toDual_gradientWithin : (toDual 𝕜 F) (gradientWit
hin f s x) = fderivWithin 𝕜 f s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.hasGradientWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasGradientWithinAt f (gradientWithin f s x) s x := by
  simpa [hasGradientWithinAt_iff_hasFDerivWithinAt] using h.hasFDerivWithinAt
/-
**HasGradientWithinAt.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientWithinAt.differentiableWithinAt (h : HasGradientWithinAt f f' s
 x) : DifferentiableWithinAt 𝕜 f s x
参数：h : HasGradientWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasGradientWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} {F : Type u_2} [
inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F
]   [inst_3 : CompleteSpace…
-/
theorem HasGradientWithinAt.differentiableWithinAt (h : HasGradientWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.hasFDerivWithinAt.differentiableWithinAt

@[simp]
/-
**hasGradientWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientWithinAt_univ : HasGradientWithinAt f f' univ x ↔ HasGradientAt
 f f' x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasGradientWithinAt_iff_hasFDerivWithinAt`：hasGradientWithinAt_iff_hasFD
erivWithinAt {s : Set F} : HasGradientWithinAt f f' s x ↔ HasFDerivWithinAt f (t
oDual 𝕜 F f') s x
· 使用定理 `hasGradientAt_iff_hasFDerivAt`：hasGradientAt_iff_hasFDerivAt : HasGradie
ntAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
-/
theorem hasGradientWithinAt_univ : HasGradientWithinAt f f' univ x ↔ HasGradientAt f f' x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivWithinAt_univ

@[simp]
/-
**gradientWithin_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gradientWithin_univ : gradientWithin f univ = gradient f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gradientWithin_univ : gradientWithin f univ = gradient f := by
  ext; simp [gradientWithin, gradient]
/-
**DifferentiableOn.hasGradientAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.hasGradientAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x
) : HasGradientAt f (∇ f x) x
参数：h : DifferentiableOn 𝕜 f s；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasGradientAt`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLik
e 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 
: CompleteSpace…
· 使用定理 `DifferentiableOn.hasFDerivAt`：DifferentiableOn.hasFDerivAt (h : Differen
tiableOn 𝕜 f s) (hs : s in 𝓝 x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableOn.hasGradientAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasGradientAt f (∇ f x) x :=
  (h.hasFDerivAt hs).hasGradientAt
/-
**HasGradientAt.gradient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAt.gradient (h : HasGradientAt f f' x) : ∇ f x = f'
参数：h : HasGradientAt f f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientAt.unique`：HasGradientAt.unique {gradf gradg : F} (hf : HasGr
adientAt f gradf x) (hg : HasGradientAt f gradg x) : gradf = gradg
· 使用定理 `DifferentiableAt.hasGradientAt`：DifferentiableAt.hasGradientAt (h : Diff
erentiableAt 𝕜 f x) : HasGradientAt f (∇ f x) x
· 使用定理 `HasGradientAt.differentiableAt`：HasGradientAt.differentiableAt (h : HasG
radientAt f f' x) : DifferentiableAt 𝕜 f x
-/
theorem HasGradientAt.gradient (h : HasGradientAt f f' x) : ∇ f x = f' :=
  h.differentiableAt.hasGradientAt.unique h
/-
**gradient_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gradient_eq {f' : F -> F} (h : forall x, HasGradientAt f (f' x) x) : ∇ f =
 f'
参数：h : forall x, HasGradientAt f (f' x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasGradientAt.gradient`：HasGradientAt.gradient (h : HasGradientAt f f' x
) : ∇ f x = f'
-/
theorem gradient_eq {f' : F → F} (h : ∀ x, HasGradientAt f (f' x) x) : ∇ f = f' :=
  funext fun x => (h x).gradient

section OneDimension

variable {g : 𝕜 → 𝕜} {g' u : 𝕜} {L' : Filter 𝕜}

/-
**HasGradientAtFilter.hasDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAtFilter.hasDerivAtFilter (h : HasGradientAtFilter g g' u L') :
 HasDerivAtFilter g (conj g') (L' ×ˢ pure u)
参数：h : HasGradientAtFilter g g' u L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
theorem HasGradientAtFilter.hasDerivAtFilter (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g (conj g') (L' ×ˢ pure u) :=
  h
/-
**HasDerivAtFilter.hasGradientAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.hasGradientAtFilter (h : HasDerivAtFilter g g' (L' ×ˢ pur
e u)) : HasGradientAtFilter g (conj g') u L'
参数：h : HasDerivAtFilter g g' (L' ×ˢ pure u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasGradientAtFilter.eq_1`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLike
 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 :
 CompleteSpace…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem HasDerivAtFilter.hasGradientAtFilter (h : HasDerivAtFilter g g' (L' ×ˢ pure u)) :
    HasGradientAtFilter g (conj g') u L' := by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) g' = (toDual 𝕜 𝕜) (conj g') := by
    ext; simp
  rwa [HasGradientAtFilter, ← this]
/-
**HasGradientAt.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAt.hasDerivAt (h : HasGradientAt g g' u) : HasDerivAt g (conj g
') u
参数：h : HasGradientAt g g' u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivAt_iff_hasDerivAt`：hasFDerivAt_iff_hasDerivAt {f' : 𝕜 ->L[𝕜] F}
 : HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x
· 使用定理 `hasGradientAt_iff_hasFDerivAt`：hasGradientAt_iff_hasFDerivAt : HasGradie
ntAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x
-/
theorem HasGradientAt.hasDerivAt (h : HasGradientAt g g' u) : HasDerivAt g (conj g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt] at h
  simpa using h
/-
**HasDerivAt.hasGradientAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.hasGradientAt (h : HasDerivAt g g' u) : HasGradientAt g (conj g
') u
参数：h : HasDerivAt g g' u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasGradientAt_iff_hasFDerivAt`：hasGradientAt_iff_hasFDerivAt : HasGradie
ntAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x
· 使用定理 `hasFDerivAt_iff_hasDerivAt`：hasFDerivAt_iff_hasDerivAt {f' : 𝕜 ->L[𝕜] F}
 : HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem HasDerivAt.hasGradientAt (h : HasDerivAt g g' u) : HasGradientAt g (conj g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt]
  simpa
/-
**gradient_eq_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gradient_eq_deriv : ∇ g u = conj (deriv g u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasGradientAt.hasDerivAt`：HasGradientAt.hasDerivAt (h : HasGradientAt g 
g' u) : HasDerivAt g (conj g') u
· 使用定理 `DifferentiableAt.hasGradientAt`：DifferentiableAt.hasGradientAt (h : Diff
erentiableAt 𝕜 f x) : HasGradientAt f (∇ f x) x
· 使用定理 `RCLike.conj_conj`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarR
ing R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
· 使用定理 `gradient_eq_zero_of_not_differentiableAt`：gradient_eq_zero_of_not_differ
entiableAt (h : ¬DifferentiableAt 𝕜 f x) : ∇ f x = 0
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem gradient_eq_deriv : ∇ g u = conj (deriv g u) := by
  by_cases h : DifferentiableAt 𝕜 g u
  · rw [h.hasGradientAt.hasDerivAt.deriv, RCLike.conj_conj]
  · rw [gradient_eq_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h, map_zero]

end OneDimension

section OneDimensionReal

variable {g : ℝ → ℝ} {g' u : ℝ} {L' : Filter ℝ}

/-
**HasGradientAtFilter.hasDerivAtFilter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAtFilter.hasDerivAtFilter' (h : HasGradientAtFilter g g' u L') 
: HasDerivAtFilter g g' (L' ×ˢ pure u)
参数：h : HasGradientAtFilter g g' u L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientAtFilter.hasDerivAtFilter`：HasGradientAtFilter.hasDerivAtFilt
er (h : HasGradientAtFilter g g' u L') : HasDerivAtFilter g (conj g') (L' ×ˢ pur
e u)
-/
theorem HasGradientAtFilter.hasDerivAtFilter' (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g g' (L' ×ˢ pure u) := h.hasDerivAtFilter
/-
**HasDerivAtFilter.hasGradientAtFilter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.hasGradientAtFilter' (h : HasDerivAtFilter g g' (L' ×ˢ pu
re u)) : HasGradientAtFilter g g' u L'
参数：h : HasDerivAtFilter g g' (L' ×ˢ pure u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAtFilter.hasGradientAtFilter`：HasDerivAtFilter.hasGradientAtFilt
er (h : HasDerivAtFilter g g' (L' ×ˢ pure u)) : HasGradientAtFilter g (conj g') 
u L'
-/
theorem HasDerivAtFilter.hasGradientAtFilter' (h : HasDerivAtFilter g g' (L' ×ˢ pure u)) :
    HasGradientAtFilter g g' u L' := h.hasGradientAtFilter
/-
**HasGradientAt.hasDerivAt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAt.hasDerivAt' (h : HasGradientAt g g' u) : HasDerivAt g g' u
参数：h : HasGradientAt g g' u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientAt.hasDerivAt`：HasGradientAt.hasDerivAt (h : HasGradientAt g 
g' u) : HasDerivAt g (conj g') u
-/
theorem HasGradientAt.hasDerivAt' (h : HasGradientAt g g' u) :
    HasDerivAt g g' u := h.hasDerivAt
/-
**HasDerivAt.hasGradientAt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.hasGradientAt' (h : HasDerivAt g g' u) : HasGradientAt g g' u
参数：h : HasDerivAt g g' u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.hasGradientAt`：HasDerivAt.hasGradientAt (h : HasDerivAt g g' 
u) : HasGradientAt g (conj g') u
-/
theorem HasDerivAt.hasGradientAt' (h : HasDerivAt g g' u) :
    HasGradientAt g g' u := h.hasGradientAt
/-
**gradient_eq_deriv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gradient_eq_deriv' : ∇ g u = deriv g u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gradient_eq_deriv`：gradient_eq_deriv : ∇ g u = conj (deriv g u)
-/
theorem gradient_eq_deriv' : ∇ g u = deriv g u := gradient_eq_deriv

end OneDimensionReal

open Filter

section GradientProperties

/-
**hasGradientAtFilter_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientAtFilter_iff_isLittleO : HasGradientAtFilter f f' x L ↔ (fun x'
 : F => f x' - f x - ⟪f', x' - x⟫) =o[L] fun x' => x' - x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `hasFDerivAtFilter_iff_isLittleO`：hasFDerivAtFilter_iff_isLittleO {L : Fi
lter (E × E)} : HasFDerivAtFilter f f' L ↔ (fun p => f p.1 - f p.2 - f' (p.1 - p
.2)) =o[L] fun p => p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasGradientAtFilter_iff_isLittleO :
    HasGradientAtFilter f f' x L ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[L] fun x' => x' - x :=
  hasFDerivAtFilter_iff_isLittleO.trans <| by simp [Function.comp_def]
/-
**hasGradientWithinAt_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientWithinAt_iff_isLittleO : HasGradientWithinAt f f' s x ↔ (fun x'
 : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝[s] x] fun x' => x' - x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasGradientAtFilter_iff_isLittleO`：hasGradientAtFilter_iff_isLittleO : H
asGradientAtFilter f f' x L ↔ (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[L] fu
n x' => x' - x
-/
theorem hasGradientWithinAt_iff_isLittleO :
    HasGradientWithinAt f f' s x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝[s] x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO
/-
**hasGradientWithinAt_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientWithinAt_iff_tendsto : HasGradientWithinAt f f' s x ↔ Tendsto (
fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝[s] x) (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_iff_tendsto`：hasFDerivWithinAt_iff_tendsto : HasFDeriv
WithinAt f f' s x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) 
(𝓝[s] x) (𝓝 0)
-/
theorem hasGradientWithinAt_iff_tendsto :
    HasGradientWithinAt f f' s x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivWithinAt_iff_tendsto
/-
**hasGradientAt_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientAt_iff_isLittleO : HasGradientAt f f' x ↔ (fun x' : F => f x' -
 f x - ⟪f', x' - x⟫) =o[𝓝 x] fun x' => x' - x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasGradientAtFilter_iff_isLittleO`：hasGradientAtFilter_iff_isLittleO : H
asGradientAtFilter f f' x L ↔ (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[L] fu
n x' => x' - x
-/
theorem hasGradientAt_iff_isLittleO : HasGradientAt f f' x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝 x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO
/-
**hasGradientAt_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientAt_iff_tendsto : HasGradientAt f f' x ↔ Tendsto (fun x' => ‖x' 
- x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝 x) (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_iff_tendsto`：hasFDerivAt_iff_tendsto : HasFDerivAt f f' x ↔ 
Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0)
-/
theorem hasGradientAt_iff_tendsto :
    HasGradientAt f f' x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAt_iff_tendsto
/-
**HasGradientAtFilter.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAtFilter.isBigO_sub (h : HasGradientAtFilter f f' x L) : (fun x
' => f x' - f x) =O[L] fun x' => x' - x
参数：h : HasGradientAtFilter f f' x L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `HasFDerivAtFilter.isBigO_sub`：HasFDerivAtFilter.isBigO_sub (h : HasFDeri
vAtFilter f f' L) : (fun p => f p.1 - f p.2) =O[L] fun p => p.1 - p.2
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
-/
theorem HasGradientAtFilter.isBigO_sub (h : HasGradientAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  HasFDerivAtFilter.isBigO_sub h |>.comp_tendsto prod_pure.ge
/-
**hasGradientWithinAt_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientWithinAt_congr_set' {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] 
t) : HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x
参数：y : F；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_congr_set'`：hasFDerivWithinAt_congr_set' [T1Space E] (
y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt 
f f' t x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem hasGradientWithinAt_congr_set' {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h
/-
**hasGradientWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientWithinAt_congr_set {s t : Set F} (h : s =ᶠ[𝓝 x] t) : HasGradien
tWithinAt f f' s x ↔ HasGradientWithinAt f f' t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_congr_set`：hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] 
t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x
-/
theorem hasGradientWithinAt_congr_set {s t : Set F} (h : s =ᶠ[𝓝 x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h
/-
**hasGradientAt_iff_isLittleO_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientAt_iff_isLittleO_nhds_zero : HasGradientAt f f' x ↔ (fun h => f
 (x + h) - f x - ⟪f', h⟫) =o[𝓝 0] fun h => h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_iff_isLittleO_nhds_zero`：hasFDerivAt_iff_isLittleO_nhds_zero
 : HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h
-/
theorem hasGradientAt_iff_isLittleO_nhds_zero : HasGradientAt f f' x ↔
    (fun h => f (x + h) - f x - ⟪f', h⟫) =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero

end GradientProperties

section Inner

/-
**HasGradientWithinAt.fderivWithin_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasGradientWithinAt.fderivWithin_apply (h : HasGradientWithinAt f f' s x) 
(hs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x y = ⟪f', y⟫
参数：h : HasGradientWithinAt f f' s x；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasGradientWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} {F : Type u_2} [
inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F
]   [inst_3 : CompleteSpace…
· 使用定理 `InnerProductSpace.toDual_apply_apply`：toDual_apply_apply {x y : E} : toD
ual 𝕜 E x y = ⟪x, y⟫
-/
lemma HasGradientWithinAt.fderivWithin_apply
    (h : HasGradientWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x y = ⟪f', y⟫ := by
  rw [h.hasFDerivWithinAt.fderivWithin hs, toDual_apply_apply]
/-
**HasGradientAt.fderiv_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasGradientAt.fderiv_apply (h : HasGradientAt f f' x) : fderiv 𝕜 f x y = ⟪
f', y⟫
参数：h : HasGradientAt f f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasGradientAt.hasFDerivAt`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLik
e 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 
: CompleteSpace…
· 使用定理 `InnerProductSpace.toDual_apply_apply`：toDual_apply_apply {x y : E} : toD
ual 𝕜 E x y = ⟪x, y⟫
-/
lemma HasGradientAt.fderiv_apply (h : HasGradientAt f f' x) : fderiv 𝕜 f x y = ⟪f', y⟫ := by
  rw [h.hasFDerivAt.fderiv, toDual_apply_apply]

@[simp]
/-
**inner_gradientWithin_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inner_gradientWithin_left : ⟪gradientWithin f s x, y⟫ = fderivWithin 𝕜 f s
 x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gradientWithin.eq_1`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLike 𝕜] [
inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 : Comp
leteSpace…
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.toDual_apply_apply`：toDual_apply_apply {x y : E} : toD
ual 𝕜 E x y = ⟪x, y⟫
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
-/
lemma inner_gradientWithin_left :
    ⟪gradientWithin f s x, y⟫ = fderivWithin 𝕜 f s x y := by
  rw [gradientWithin, ← toDual_apply_apply (𝕜 := 𝕜) (E := F),
      LinearIsometryEquiv.apply_symm_apply]

@[simp]
/-
**inner_gradient_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inner_gradient_left : ⟪∇ f x, y⟫ = fderiv 𝕜 f x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `inner_gradientWithin_left`：inner_gradientWithin_left : ⟪gradientWithin f
 s x, y⟫ = fderivWithin 𝕜 f s x y
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inner_gradient_left : ⟪∇ f x, y⟫ = fderiv 𝕜 f x y := by
  simp [← gradientWithin_univ]

@[simp]
/-
**inner_gradientWithin_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inner_gradientWithin_right : ⟪x, gradientWithin f s y⟫ = conj (fderivWithi
n 𝕜 f s y x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用引理 `inner_gradientWithin_left`：inner_gradientWithin_left : ⟪gradientWithin f
 s x, y⟫ = fderivWithin 𝕜 f s x y
-/
lemma inner_gradientWithin_right :
    ⟪x, gradientWithin f s y⟫ = conj (fderivWithin 𝕜 f s y x) := by
  rw [← inner_conj_symm, inner_gradientWithin_left]

@[simp]
/-
**inner_gradient_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inner_gradient_right : ⟪x, ∇ f y⟫ = conj (fderiv 𝕜 f y x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用引理 `inner_gradient_left`：inner_gradient_left : ⟪∇ f x, y⟫ = fderiv 𝕜 f x y
-/
lemma inner_gradient_right : ⟪x, ∇ f y⟫ = conj (fderiv 𝕜 f y x) := by
  rw [← inner_conj_symm, inner_gradient_left]

end Inner

section congr

/-! ### Congruence properties of the Gradient -/

variable {f₀ f₁ : F → 𝕜} {f₀' f₁' : F} {t : Set F}

/-
**Filter.EventuallyEq.hasGradientAtFilter_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.hasGradientAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x 
= f₁ x) (h₁ : f₀' = f₁') : HasGradientAtFilter f₀ f₀' x L ↔ HasGradientAtFilter 
f₁ f₁' x L
参数：h₀ : f₀ =ᶠ[L] f₁；hx : f₀ x = f₁ x；h₁ : f₀' = f₁'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.hasFDerivAtFilter_iff`：Filter.EventuallyEq.hasFDeriv
AtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁) (h₁ : forall x, f₀' x = 
f₁' x) : HasFDerivAtFilter f₀ f…
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Filter.EventuallyEq.hasGradientAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasGradientAtFilter f₀ f₀' x L ↔ HasGradientAtFilter f₁ f₁' x L :=
  (h₀.prodMap <| by assumption).hasFDerivAtFilter_iff <| by simp [h₁]
/-
**HasGradientAtFilter.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAtFilter.congr_of_eventuallyEq (h : HasGradientAtFilter f f' x 
L) (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : HasGradientAtFilter f₁ f' x L
参数：h : HasGradientAtFilter f f' x L；hL : f₁ =ᶠ[L] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.hasGradientAtFilter_iff`：Filter.EventuallyEq.hasGrad
ientAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x) (h₁ : f₀' = f₁') : HasGra
dientAtFilter f₀ f₀' x L ↔ HasGra…
-/
theorem HasGradientAtFilter.congr_of_eventuallyEq (h : HasGradientAtFilter f f' x L)
    (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : HasGradientAtFilter f₁ f' x L := by
  rwa [hL.hasGradientAtFilter_iff hx rfl]
/-
**HasGradientWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientWithinAt.congr_mono (h : HasGradientWithinAt f f' s x) (ht : fo
rall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t subseteq s) : HasGradientWith
inAt f₁ f' t x
参数：h : HasGradientWithinAt f f' s x；ht : forall x in t, f₁ x = f x；hx : f₁ x = f
 x；h₁ : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.congr_mono`：HasFDerivWithinAt.congr_mono (h : HasFDeri
vWithinAt f f' s x) (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t subseteq s) : H
asFDerivWithinAt f…
-/
theorem HasGradientWithinAt.congr_mono (h : HasGradientWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasGradientWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁
/-
**HasGradientWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientWithinAt.congr (h : HasGradientWithinAt f f' s x) (hs : forall 
x in s, f₁ x = f x) (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x
参数：h : HasGradientWithinAt f f' s x；hs : forall x in s, f₁ x = f x；hx : f₁ x = f
 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientWithinAt.congr_mono`：HasGradientWithinAt.congr_mono (h : HasG
radientWithinAt f f' s x) (ht : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁
 : t subseteq s) : H…
-/
theorem HasGradientWithinAt.congr (h : HasGradientWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  h.congr_mono hs hx (by tauto)
/-
**HasGradientWithinAt.congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientWithinAt.congr_of_mem (h : HasGradientWithinAt f f' s x) (hs : 
forall x in s, f₁ x = f x) (hx : x in s) : HasGradientWithinAt f₁ f' s x
参数：h : HasGradientWithinAt f f' s x；hs : forall x in s, f₁ x = f x；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientWithinAt.congr`：HasGradientWithinAt.congr (h : HasGradientWit
hinAt f f' s x) (hs : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : HasGradient
WithinAt f₁ f' …
-/
theorem HasGradientWithinAt.congr_of_mem (h : HasGradientWithinAt f f' s x)
    (hs : ∀ x ∈ s, f₁ x = f x) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)
/-
**HasGradientWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientWithinAt.congr_of_eventuallyEq (h : HasGradientWithinAt f f' s 
x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x
参数：h : HasGradientWithinAt f f' s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientAtFilter.congr_of_eventuallyEq`：HasGradientAtFilter.congr_of_
eventuallyEq (h : HasGradientAtFilter f f' x L) (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f
 x) : HasGradientAtFilter f₁ f'…
-/
theorem HasGradientWithinAt.congr_of_eventuallyEq (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ hx
/-
**HasGradientWithinAt.congr_of_eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientWithinAt.congr_of_eventuallyEq_of_mem (h : HasGradientWithinAt 
f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : HasGradientWithinAt f₁ f' s x
参数：h : HasGradientWithinAt f f' s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientWithinAt.congr_of_eventuallyEq`：HasGradientWithinAt.congr_of_
eventuallyEq (h : HasGradientWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ 
x = f x) : HasGradientWithinAt …
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
-/
theorem HasGradientWithinAt.congr_of_eventuallyEq_of_mem (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)
/-
**HasGradientAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAt.congr_of_eventuallyEq (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ
[𝓝 x] f) : HasGradientAt f₁ f' x
参数：h : HasGradientAt f f' x；h₁ : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientAtFilter.congr_of_eventuallyEq`：HasGradientAtFilter.congr_of_
eventuallyEq (h : HasGradientAtFilter f f' x L) (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f
 x) : HasGradientAtFilter f₁ f'…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem HasGradientAt.congr_of_eventuallyEq (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasGradientAt f₁ f' x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ :)
/-
**Filter.EventuallyEq.gradient_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.gradient_eq (hL : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ x = ∇ f x
参数：hL : f₁ =ᶠ[𝓝 x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.fderiv_eq`：Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[
𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x
-/
theorem Filter.EventuallyEq.gradient_eq (hL : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ x = ∇ f x := by
  unfold gradient
  rwa [Filter.EventuallyEq.fderiv_eq]
/-
**Filter.EventuallyEq.gradient** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 : CompleteSpace F] {f : F → 𝕜
} {x : F} {f₁ : F → 𝕜}, f₁ =ᶠ[nhds x] f → gradient f₁ =ᶠ[nhds x] gradient f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.EventuallyEq.eventuallyEq_nhds`：Filter.EventuallyEq.eventuallyEq_
nhds {f g : X -> α} (h : f =ᶠ[𝓝 x] g) : forallᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g
· 使用定理 `Filter.EventuallyEq.gradient_eq`：Filter.EventuallyEq.gradient_eq (hL : f
₁ =ᶠ[𝓝 x] f) : ∇ f₁ x = ∇ f x
-/
protected theorem Filter.EventuallyEq.gradient (h : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ =ᶠ[𝓝 x] ∇ f :=
  h.eventuallyEq_nhds.mono fun _ h => h.gradient_eq

end congr

/-! ### The Gradient of constant functions -/

section Const

variable (c : 𝕜) (s x L)

/-
**hasGradientAtFilter_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientAtFilter_const : HasGradientAtFilter (fun _ => c) 0 x L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasGradientAtFilter.eq_1`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLike
 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 :
 CompleteSpace…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
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
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasGradientAtFilter_const : HasGradientAtFilter (fun _ => c) 0 x L := by
  rw [HasGradientAtFilter, map_zero]; exact hasFDerivAtFilter_const c _
/-
**hasGradientWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientWithinAt_const : HasGradientWithinAt (fun _ => c) 0 s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasGradientAtFilter_const`：hasGradientAtFilter_const : HasGradientAtFilt
er (fun _ => c) 0 x L
-/
theorem hasGradientWithinAt_const : HasGradientWithinAt (fun _ => c) 0 s x :=
  hasGradientAtFilter_const _ _ _
/-
**hasGradientAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGradientAt_const : HasGradientAt (fun _ => c) 0 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasGradientAtFilter_const`：hasGradientAtFilter_const : HasGradientAtFilt
er (fun _ => c) 0 x L
-/
theorem hasGradientAt_const : HasGradientAt (fun _ => c) 0 x :=
  hasGradientAtFilter_const _ _ _
/-
**gradient_fun_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gradient_fun_const : ∇ (fun _ => c) x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderiv_fun_const`：fderiv_fun_const (c : F) : fderiv 𝕜 (fun _ : E => c) =
 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gradient_fun_const : ∇ (fun _ => c) x = 0 := by simp [gradient]
/-
**gradient_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gradient_const : ∇ (const F c) x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gradient_fun_const`：gradient_fun_const : ∇ (fun _ => c) x = 0
-/
theorem gradient_const : ∇ (const F c) x = 0 := gradient_fun_const x c

@[simp]
/-
**gradient_fun_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gradient_fun_const' : (∇ fun _ : F => c) = fun _ => 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `gradient_const`：gradient_const : ∇ (const F c) x = 0
-/
theorem gradient_fun_const' : (∇ fun _ : F => c) = fun _ => 0 :=
  funext fun x => gradient_const x c

@[simp]
/-
**gradient_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gradient_const' : ∇ (const F c) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gradient_fun_const'`：gradient_fun_const' : (∇ fun _ : F => c) = fun _ =>
 0
-/
theorem gradient_const' : ∇ (const F c) = 0 := gradient_fun_const' c

end Const

section Continuous

/-! ### Continuity of a function admitting a gradient -/

nonrec theorem HasGradientAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasGradientAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL

/-
**HasGradientWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientWithinAt.continuousWithinAt (h : HasGradientWithinAt f f' s x) 
: ContinuousWithinAt f s x
参数：h : HasGradientWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientAtFilter.tendsto_nhds`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [
inst_3 : CompleteSpace…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem HasGradientWithinAt.continuousWithinAt (h : HasGradientWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasGradientAtFilter.tendsto_nhds inf_le_left h
/-
**HasGradientAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasGradientAt.continuousAt (h : HasGradientAt f f' x) : ContinuousAt f x
参数：h : HasGradientAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGradientAtFilter.tendsto_nhds`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup F] [inst_2 : InnerProductSpace 𝕜 F]   [
inst_3 : CompleteSpace…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem HasGradientAt.continuousAt (h : HasGradientAt f f' x) : ContinuousAt f x :=
  HasGradientAtFilter.tendsto_nhds le_rfl h
/-
**HasGradientAt.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `HasGradientAt`。
形式化陈述：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup F] [inst_2 : InnerProductSpace 𝕜 F]   [inst_3 : CompleteSpace F] {f : F → 𝕜
} {s : Set F} {f' : F → F},   (∀ x ∈ s, HasGradientAt f (f' x) x) → ContinuousOn
 f s
参数：∀ x ∈ s, HasGradientAt f (f' x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasGradientAt.continuousAt`：HasGradientAt.continuousAt (h : HasGradientA
t f f' x) : ContinuousAt f x
-/
protected theorem HasGradientAt.continuousOn {f' : F → F} (h : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ContinuousOn f s :=
  fun x hx => (h x hx).continuousAt.continuousWithinAt

end Continuous

