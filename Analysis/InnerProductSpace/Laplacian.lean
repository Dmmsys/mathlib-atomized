/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.DerivNotation
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-!
# The Laplacian

This file defines the Laplacian for functions `f : E → F` on real, finite-dimensional, inner product
spaces `E`. In essence, we define the Laplacian of `f` as the second derivative, applied to the
canonical covariant tensor of `E`, as defined and discussed in
`Mathlib.Analysis.InnerProductSpace.CanonicalTensor`.

We show that the Laplacian is `ℝ`-linear on continuously differentiable functions, and establish the
standard formula for computing the Laplacian in terms of orthonormal bases of `E`.
-/

@[expose] public section

open Filter TensorProduct Topology

section secondDerivativeAPI

/-!
## Supporting API

The definition of the Laplacian of a function `f : E → F` involves the notion of the second
derivative, which can be seen as a continuous multilinear map `ContinuousMultilinearMap 𝕜 (fun (i :
Fin 2) ↦ E) F`, a bilinear map `E →ₗ[𝕜] E →ₗ[𝕜] F`, or a linear map on tensors `E ⊗[𝕜] E →ₗ[𝕜]
F`. This section provides convenience API to convert between these notions.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to bilinear maps
`E →ₗ[ℝ] E →ₗ[ℝ] ℝ`.
-/
/-
**bilinearIteratedFDerivWithinTwo** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：bilinearIteratedFDerivWithinTwo (f : E -> F) (s : Set E) : E -> E ->ₗ[𝕜] E
 ->ₗ[𝕜] F
参数：f : E -> F；s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience reformulation of the second iterated derivative, as a map from `E` t
o bilinear maps
`E →ₗ[ℝ] E →ₗ[ℝ] ℝ`.
-/
noncomputable def bilinearIteratedFDerivWithinTwo (f : E → F) (s : Set E) : E → E →ₗ[𝕜] E →ₗ[𝕜] F :=
  fun x ↦ (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x).toLinearMap₁₂

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to bilinear maps
`E →ₗ[ℝ] E →ₗ[ℝ] ℝ`.
-/
/-
**bilinearIteratedFDerivTwo** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：bilinearIteratedFDerivTwo (f : E -> F) : E -> E ->ₗ[𝕜] E ->ₗ[𝕜] F
参数：f : E -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience reformulation of the second iterated derivative, as a map from `E` t
o bilinear maps
`E →ₗ[ℝ] E →ₗ[ℝ] ℝ`.
-/
noncomputable def bilinearIteratedFDerivTwo (f : E → F) : E → E →ₗ[𝕜] E →ₗ[𝕜] F :=
  fun x ↦ (fderiv 𝕜 (fderiv 𝕜 f) x).toLinearMap₁₂

/--
Expression of `bilinearIteratedFDerivWithinTwo` in terms of `iteratedFDerivWithin`.
-/
/-
**bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv {e : E} {s : Set E} (f :
 E -> F) (hs : UniqueDiffOn 𝕜 s) (he : e in s) (e₁ e₂ : E) : bilinearIteratedFDe
rivWithinTwo 𝕜 f s e e₁ e₂ = iteratedFDerivWithin 𝕜 2 f s e ![e₁, e₂]
参数：f : E -> F；hs : UniqueDiffOn 𝕜 s；he : e in s；e₁ e₂ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `iteratedFDerivWithin_two_apply`：iteratedFDerivWithin_two_apply (f : E ->
 F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z in s) (m : Fin 2 -> E) : iteratedFDe
rivWithin 𝕜 2 f s z …
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Expression of `bilinearIteratedFDerivWithinTwo` in terms of `iteratedFDerivWithi
n`.
-/
lemma bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv {e : E} {s : Set E} (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s) (e₁ e₂ : E) :
    bilinearIteratedFDerivWithinTwo 𝕜 f s e e₁ e₂ = iteratedFDerivWithin 𝕜 2 f s e ![e₁, e₂] := by
  simp [iteratedFDerivWithin_two_apply f hs he ![e₁, e₂], bilinearIteratedFDerivWithinTwo]

/--
Expression of `bilinearIteratedFDerivTwo` in terms of `iteratedFDeriv`.
-/
/-
**bilinearIteratedFDerivTwo_eq_iteratedFDeriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bilinearIteratedFDerivTwo_eq_iteratedFDeriv (f : E -> F) (e e₁ e₂ : E) : b
ilinearIteratedFDerivTwo 𝕜 f e e₁ e₂ = iteratedFDeriv 𝕜 2 f e ![e₁, e₂]
参数：f : E -> F；e e₁ e₂ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `iteratedFDeriv_two_apply`：iteratedFDeriv_two_apply (f : E -> F) (z : E) 
(m : Fin 2 -> E) : iteratedFDeriv 𝕜 2 f z m = fderiv 𝕜 (fderiv 𝕜 f) z (m 0) (m 1
)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Expression of `bilinearIteratedFDerivTwo` in terms of `iteratedFDeriv`.
-/
lemma bilinearIteratedFDerivTwo_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    bilinearIteratedFDerivTwo 𝕜 f e e₁ e₂ = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  simp [iteratedFDeriv_two_apply f e ![e₁, e₂], bilinearIteratedFDerivTwo]

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to linear maps
`E ⊗[𝕜] E →ₗ[𝕜] F`.
-/
/-
**tensorIteratedFDerivWithinTwo** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tensorIteratedFDerivWithinTwo (f : E -> F) (s : Set E) : E -> E otimes[𝕜] 
E ->ₗ[𝕜] F
参数：f : E -> F；s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience reformulation of the second iterated derivative, as a map from `E` t
o linear maps
`E ⊗[𝕜] E →ₗ[𝕜] F`.
-/
noncomputable def tensorIteratedFDerivWithinTwo (f : E → F) (s : Set E) : E → E ⊗[𝕜] E →ₗ[𝕜] F :=
  fun e ↦ lift (bilinearIteratedFDerivWithinTwo 𝕜 f s e)

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to linear maps
`E ⊗[𝕜] E →ₗ[𝕜] F`.
-/
/-
**tensorIteratedFDerivTwo** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tensorIteratedFDerivTwo (f : E -> F) : E -> E otimes[𝕜] E ->ₗ[𝕜] F
参数：f : E -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience reformulation of the second iterated derivative, as a map from `E` t
o linear maps
`E ⊗[𝕜] E →ₗ[𝕜] F`.
-/
noncomputable def tensorIteratedFDerivTwo (f : E → F) : E → E ⊗[𝕜] E →ₗ[𝕜] F :=
  fun e ↦ lift (bilinearIteratedFDerivTwo 𝕜 f e)

/--
Expression of `tensorIteratedFDerivTwo` in terms of `iteratedFDerivWithin`.
-/
/-
**tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin {e : E} {s : Set E} 
(f : E -> F) (hs : UniqueDiffOn 𝕜 s) (he : e in s) (e₁ e₂ : E) : tensorIteratedF
DerivWithinTwo 𝕜 f s e (e₁ otimesₜ[𝕜] e₂) = iteratedFDerivWithin 𝕜 2 f s e ![e₁,
 e₂]
参数：f : E -> F；hs : UniqueDiffOn 𝕜 s；he : e in s；e₁ e₂ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv`：bilinearIteratedFDeri
vWithinTwo_eq_iteratedFDeriv {e : E} {s : Set E} (f : E -> F) (hs : UniqueDiffOn
 𝕜 s) (he : e in s) (e₁ e₂ : E) : bilin…
· 使用定理 `tensorIteratedFDerivWithinTwo.eq_1`：∀ (𝕜 : Type u_1) [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Type u_…
· 使用定理 `TensorProduct.lift.tmul`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSe
miring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type
 u_8} {P₂ : T…

--- 原说明 ---
Expression of `tensorIteratedFDerivTwo` in terms of `iteratedFDerivWithin`.
-/
lemma tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin {e : E} {s : Set E} (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s) (e₁ e₂ : E) :
    tensorIteratedFDerivWithinTwo 𝕜 f s e (e₁ ⊗ₜ[𝕜] e₂) =
      iteratedFDerivWithin 𝕜 2 f s e ![e₁, e₂] := by
  rw [← bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv f hs he, tensorIteratedFDerivWithinTwo,
    lift.tmul]

/--
Expression of `tensorIteratedFDerivTwo` in terms of `iteratedFDeriv`.
-/
/-
**tensorIteratedFDerivTwo_eq_iteratedFDeriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tensorIteratedFDerivTwo_eq_iteratedFDeriv (f : E -> F) (e e₁ e₂ : E) : ten
sorIteratedFDerivTwo 𝕜 f e (e₁ otimesₜ[𝕜] e₂) = iteratedFDeriv 𝕜 2 f e ![e₁, e₂]
参数：f : E -> F；e e₁ e₂ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `bilinearIteratedFDerivTwo_eq_iteratedFDeriv`：bilinearIteratedFDerivTwo_e
q_iteratedFDeriv (f : E -> F) (e e₁ e₂ : E) : bilinearIteratedFDerivTwo 𝕜 f e e₁
 e₂ = iteratedFDeriv 𝕜 2 f e ![e₁…
· 使用定理 `tensorIteratedFDerivTwo.eq_1`：∀ (𝕜 : Type u_1) [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {F : Type u_…
· 使用定理 `TensorProduct.lift.tmul`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSe
miring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type
 u_8} {P₂ : T…

--- 原说明 ---
Expression of `tensorIteratedFDerivTwo` in terms of `iteratedFDeriv`.
-/
lemma tensorIteratedFDerivTwo_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    tensorIteratedFDerivTwo 𝕜 f e (e₁ ⊗ₜ[𝕜] e₂) = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, tensorIteratedFDerivTwo, lift.tmul]

end secondDerivativeAPI

/-!
## Definition of the Laplacian
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F} {x : E} {s : Set E}

namespace InnerProductSpace

variable (f s) in
/--
Laplacian for functions on real inner product spaces, with respect to a set `s`. Use `open
InnerProductSpace` to access the notation `Δ[s]` for `InnerProductSpace.LaplacianWithin`.
-/
@[wikidata Q203484]
/-
**InnerProductSpace.laplacianWithin** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpace
`。
形式化陈述：laplacianWithin : E -> F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Laplacian for functions on real inner product spaces, with respect to a set `s`.
 Use `open
InnerProductSpace` to access the notation `Δ[s]` for `InnerProductSpace.Laplacia
nWithin`.
-/
noncomputable def laplacianWithin : E → F :=
  fun x ↦ tensorIteratedFDerivWithinTwo ℝ f s x (InnerProductSpace.canonicalCovariantTensor E)

@[inherit_doc]
scoped[InnerProductSpace] notation "Δ[" s "] " f:60 => laplacianWithin f s

noncomputable
/-
**InnerProductSpace.instLaplacian** 是 Mathlib 中的一个实例，位于命名空间 `InnerProductSpace`。
形式化陈述：instLaplacian : Laplacian (E -> F) (E -> F) where laplacian f x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLaplacian : Laplacian (E → F) (E → F) where
  laplacian f x := tensorIteratedFDerivTwo ℝ f x (InnerProductSpace.canonicalCovariantTensor E)

open Laplacian

/--
The Laplacian equals the Laplacian with respect to `Set.univ`.
-/
@[simp]
/-
**InnerProductSpace.laplacianWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space`。
形式化陈述：laplacianWithin_univ : Δ[(Set.univ : Set E)] f = Δ f
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
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Laplacian equals the Laplacian with respect to `Set.univ`.
-/
theorem laplacianWithin_univ :
    Δ[(Set.univ : Set E)] f = Δ f := by
  ext x
  simp [laplacian, tensorIteratedFDerivTwo, bilinearIteratedFDerivTwo,
    laplacianWithin, tensorIteratedFDerivWithinTwo, bilinearIteratedFDerivWithinTwo]

/-!
## Computation of Δ in Terms of Orthonormal Bases
-/

variable (f) in
/--
Standard formula, computing the Laplacian from any orthonormal basis.
-/
/-
**InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis** 是
 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis {ι : Type*} [Fint
ype ι] {e : E} (hs : UniqueDiffOn Real s) (he : e in s) (v : OrthonormalBasis ι 
Real E) : (Δ[s] f) e = ∑ i, iteratedFDerivWithin Real 2 f s e ![v i, v i]
参数：hs : UniqueDiffOn Real s；he : e in s；v : OrthonormalBasis ι Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.canonicalCovariantTensor_eq_sum`：InnerProductSpace.can
onicalCovariantTensor_eq_sum [FiniteDimensional Real E] {ι : Type*} [Fintype ι] 
(v : OrthonormalBasis ι Real E) : Inner…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin`：tensorIteratedFDe
rivWithinTwo_eq_iteratedFDerivWithin {e : E} {s : Set E} (f : E -> F) (hs : Uniq
ueDiffOn 𝕜 s) (he : e in s) (e₁ e₂ : E) : t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Standard formula, computing the Laplacian from any orthonormal basis.
-/
theorem laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis {ι : Type*} [Fintype ι] {e : E}
    (hs : UniqueDiffOn ℝ s) (he : e ∈ s) (v : OrthonormalBasis ι ℝ E) :
    (Δ[s] f) e = ∑ i, iteratedFDerivWithin ℝ 2 f s e ![v i, v i] := by
  simp [InnerProductSpace.laplacianWithin, canonicalCovariantTensor_eq_sum E v,
    tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin f hs he]

variable (f) in
/--
Standard formula, computing the Laplacian from any orthonormal basis.
-/
/-
**InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis** 是 Mathlib 中的一
个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：laplacian_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι] (v : 
OrthonormalBasis ι Real E) : Δ f = fun x => ∑ i, iteratedFDeriv Real 2 f x ![v i
, v i]
参数：v : OrthonormalBasis ι Real E。
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
· 使用定理 `InnerProductSpace.canonicalCovariantTensor_eq_sum`：InnerProductSpace.can
onicalCovariantTensor_eq_sum [FiniteDimensional Real E] {ι : Type*} [Fintype ι] 
(v : OrthonormalBasis ι Real E) : Inner…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `tensorIteratedFDerivTwo_eq_iteratedFDeriv`：tensorIteratedFDerivTwo_eq_it
eratedFDeriv (f : E -> F) (e e₁ e₂ : E) : tensorIteratedFDerivTwo 𝕜 f e (e₁ otim
esₜ[𝕜] e₂) = iteratedFDeriv 𝕜 2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Standard formula, computing the Laplacian from any orthonormal basis.
-/
theorem laplacian_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) :
    Δ f = fun x ↦ ∑ i, iteratedFDeriv ℝ 2 f x ![v i, v i] := by
  ext x
  simp [laplacian, canonicalCovariantTensor_eq_sum E v, tensorIteratedFDerivTwo_eq_iteratedFDeriv]

variable (f) in
/--
Standard formula, computing the Laplacian from the standard orthonormal basis of a real inner
product space.
-/
/-
**InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis*
* 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis {e : E} (hs : 
UniqueDiffOn Real s) (he : e in s) : (Δ[s] f) e = ∑ i, iteratedFDerivWithin Real
 2 f s e ![(stdOrthonormalBasis Real E) i, (stdOrthonormalBasis Real E) i]
参数：hs : UniqueDiffOn Real s；he : e in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_orthonormalBas
is`：laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis {ι : Type*} [Fintyp
e ι] {e : E} (hs : UniqueDiffOn Real s) (he : e in s) (v : Ortho…

--- 原说明 ---
Standard formula, computing the Laplacian from the standard orthonormal basis of
 a real inner
product space.
-/
theorem laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis {e : E} (hs : UniqueDiffOn ℝ s)
    (he : e ∈ s) :
    (Δ[s] f) e = ∑ i, iteratedFDerivWithin ℝ 2 f s e
      ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] := by
  apply laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he (stdOrthonormalBasis ℝ E)

variable (f) in
/--
Standard formula, computing the Laplacian from the standard orthonormal basis of a real inner
product space.
-/
/-
**InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis** 是 Mathlib 
中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：laplacian_eq_iteratedFDeriv_stdOrthonormalBasis : Δ f = fun x => ∑ i, iter
atedFDeriv Real 2 f x ![(stdOrthonormalBasis Real E) i, (stdOrthonormalBasis Rea
l E) i]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`：laplacia
n_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι] (v : OrthonormalBas
is ι Real E) : Δ f = fun x => ∑ i, iteratedFDeriv Re…

--- 原说明 ---
Standard formula, computing the Laplacian from the standard orthonormal basis of
 a real inner
product space.
-/
theorem laplacian_eq_iteratedFDeriv_stdOrthonormalBasis :
    Δ f = fun x ↦
      ∑ i, iteratedFDeriv ℝ 2 f x ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] :=
  laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)

/-- For a function on `ℝ`, the Laplacian is the second derivative: version within a set. -/
/-
**InnerProductSpace.laplacianWithin_eq_iteratedDerivWithin_real** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductSpace`。
形式化陈述：laplacianWithin_eq_iteratedDerivWithin_real {e : Real} {s : Set Real} (f :
 Real -> F) (hs : UniqueDiffOn Real s) (he : e in s) : (Δ[s] f) e = iteratedDeri
vWithin 2 f s e
参数：f : Real -> F；hs : UniqueDiffOn Real s；he : e in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_orthonormalBas
is`：laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis {ι : Type*} [Fintyp
e ι] {e : E} (hs : UniqueDiffOn Real s) (he : e in s) (v : Ortho…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrthonormalBasis.singleton_apply`：singleton_apply (i) : OrthonormalBasis
.singleton ι 𝕜 i = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
For a function on `ℝ`, the Laplacian is the second derivative: version within a 
set.
-/
theorem laplacianWithin_eq_iteratedDerivWithin_real {e : ℝ} {s : Set ℝ} (f : ℝ → F)
    (hs : UniqueDiffOn ℝ s) (he : e ∈ s) :
    (Δ[s] f) e = iteratedDerivWithin 2 f s e := by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
        (OrthonormalBasis.singleton (Fin 1) ℝ),
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, OrthonormalBasis.singleton_apply,
    Finset.sum_const, Finset.card_singleton, one_smul, iteratedDerivWithin_eq_iteratedFDerivWithin]
  congr with i
  fin_cases i <;> simp

/-- For a function on `ℝ`, the Laplacian is the second derivative. -/
@[simp]
/-
**InnerProductSpace.laplacian_eq_iteratedDeriv_real** 是 Mathlib 中的一个定理，位于命名空间 `I
nnerProductSpace`。
形式化陈述：laplacian_eq_iteratedDeriv_real {e : Real} (f : Real -> F) : Δ f e = itera
tedDeriv 2 f e
参数：f : Real -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.laplacianWithin_univ`：laplacianWithin_univ : Δ[(Set.un
iv : Set E)] f = Δ f
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `InnerProductSpace.laplacianWithin_eq_iteratedDerivWithin_real`：laplacian
Within_eq_iteratedDerivWithin_real {e : Real} {s : Set Real} (f : Real -> F) (hs
 : UniqueDiffOn Real s) (he : e in s) : (Δ[s] f) e …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R

--- 原说明 ---
For a function on `ℝ`, the Laplacian is the second derivative.
-/
theorem laplacian_eq_iteratedDeriv_real {e : ℝ} (f : ℝ → F) :
    Δ f e = iteratedDeriv 2 f e := by
  rw [← laplacianWithin_univ, ← iteratedDerivWithin_univ,
    laplacianWithin_eq_iteratedDerivWithin_real _ (by simp) (by simp)]

/--
Special case of the standard formula for functions on `ℂ`, with the standard real inner product
structure.
-/
/-
**InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_complexPlane** 是 Mat
hlib 中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：laplacianWithin_eq_iteratedFDerivWithin_complexPlane {e : Complex} {s : Se
t Complex} (f : Complex -> F) (hs : UniqueDiffOn Real s) (he : e in s) : (Δ[s] f
) e = iteratedFDerivWithin Real 2 f s e ![1, 1] + iteratedFDerivWithin Real 2 f 
s e ![Complex.I, Complex.I]
参数：f : Complex -> F；hs : UniqueDiffOn Real s；he : e in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_orthonormalBas
is`：laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis {ι : Type*} [Fintyp
e ι] {e : E} (hs : UniqueDiffOn Real s) (he : e in s) (v : Ortho…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Complex.coe_orthonormalBasisOneI`：Complex.coe_orthonormalBasisOneI : (Co
mplex.orthonormalBasisOneI : Fin 2 -> Complex) = ![1, I]
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Special case of the standard formula for functions on `ℂ`, with the standard rea
l inner product
structure.
-/
theorem laplacianWithin_eq_iteratedFDerivWithin_complexPlane {e : ℂ} {s : Set ℂ} (f : ℂ → F)
    (hs : UniqueDiffOn ℝ s) (he : e ∈ s) :
    (Δ[s] f) e = iteratedFDerivWithin ℝ 2 f s e ![1, 1]
      + iteratedFDerivWithin ℝ 2 f s e ![Complex.I, Complex.I] := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
    Complex.orthonormalBasisOneI]

/--
Special case of the standard formula for functions on `ℂ`, with the standard real inner product
structure.
-/
/-
**InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane** 是 Mathlib 中的一个定理，
位于命名空间 `InnerProductSpace`。
形式化陈述：laplacian_eq_iteratedFDeriv_complexPlane (f : Complex -> F) : Δ f = fun x 
=> iteratedFDeriv Real 2 f x ![1, 1] + iteratedFDeriv Real 2 f x ![Complex.I, Co
mplex.I]
参数：f : Complex -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`：laplacia
n_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι] (v : OrthonormalBas
is ι Real E) : Δ f = fun x => ∑ i, iteratedFDeriv Re…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Complex.coe_orthonormalBasisOneI`：Complex.coe_orthonormalBasisOneI : (Co
mplex.orthonormalBasisOneI : Fin 2 -> Complex) = ![1, I]
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Special case of the standard formula for functions on `ℂ`, with the standard rea
l inner product
structure.
-/
theorem laplacian_eq_iteratedFDeriv_complexPlane (f : ℂ → F) :
    Δ f = fun x ↦
      iteratedFDeriv ℝ 2 f x ![1, 1] + iteratedFDeriv ℝ 2 f x ![Complex.I, Complex.I] := by
  simp [laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]

/--
The Laplacian of a constant function is zero.
-/
/-
**InnerProductSpace.laplacian_const** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace
`。
形式化陈述：∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_3} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {c : F},   (Laplacian.laplacian fun x => c) =
 0
参数：Laplacian.laplacian fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`：lapla
cian_eq_iteratedFDeriv_stdOrthonormalBasis : Δ f = fun x => ∑ i, iteratedFDeriv 
Real 2 f x ![(stdOrthonormalBasis Real E) i, (stdOrthon…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDeriv_const_of_ne`：iteratedFDeriv_const_of_ne {n : Nat} (hn : n
 != 0) (c : F) : (iteratedFDeriv 𝕜 n fun _ : E => c) = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Laplacian of a constant function is zero.
-/
@[simp] theorem laplacian_const {c : F} :
    Laplacian.laplacian (fun (_ : E) ↦ c) = 0 := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_of_ne two_ne_zero,
    Pi.zero_def]

/-!
## Congruence Lemmata for Δ
-/

/--
If two functions agree in a neighborhood of a point, then so do their Laplacians.
-/
/-
**InnerProductSpace.laplacianWithin_congr_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `
InnerProductSpace`。
形式化陈述：laplacianWithin_congr_nhdsWithin (h : f₁ =ᶠ[𝓝[s] x] f₂) (hs : UniqueDiffOn
 Real s) : Δ[s] f₁ =ᶠ[𝓝[s] x] Δ[s] f₂
参数：h : f₁ =ᶠ[𝓝[s] x] f₂；hs : UniqueDiffOn Real s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.EventuallyEq.iteratedFDerivWithin`：∀ (𝕜 : Type u) [inst : Nontriv
iallyNormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type uF} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormal
Basis`：laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis {e : E} (hs :
 UniqueDiffOn Real s) (he : e in s) : (Δ[s] f) e = ∑ i, iteratedFDe…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If two functions agree in a neighborhood of a point, then so do their Laplacians
.
-/
theorem laplacianWithin_congr_nhdsWithin (h : f₁ =ᶠ[𝓝[s] x] f₂) (hs : UniqueDiffOn ℝ s) :
    Δ[s] f₁ =ᶠ[𝓝[s] x] Δ[s] f₂ := by
  filter_upwards [EventuallyEq.iteratedFDerivWithin (𝕜 := ℝ) h 2,
    eventually_mem_nhdsWithin] with x h₁x h₂x
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs h₂x, h₁x]

/--
If two functions agree in a neighborhood of a point, then so do their Laplacians.
-/
/-
**InnerProductSpace.laplacian_congr_nhds** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space`。
形式化陈述：laplacian_congr_nhds (h : f₁ =ᶠ[𝓝 x] f₂) : Δ f₁ =ᶠ[𝓝 x] Δ f₂
参数：h : f₁ =ᶠ[𝓝 x] f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.EventuallyEq.iteratedFDeriv`：∀ (𝕜 : Type u) [inst : NontriviallyN
ormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Type uF} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`：lapla
cian_eq_iteratedFDeriv_stdOrthonormalBasis : Δ f = fun x => ∑ i, iteratedFDeriv 
Real 2 f x ![(stdOrthonormalBasis Real E) i, (stdOrthon…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If two functions agree in a neighborhood of a point, then so do their Laplacians
.
-/
theorem laplacian_congr_nhds (h : f₁ =ᶠ[𝓝 x] f₂) :
    Δ f₁ =ᶠ[𝓝 x] Δ f₂ := by
  filter_upwards [EventuallyEq.iteratedFDeriv ℝ h 2] with x hx
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hx]

/-!
## 𝕜-Linearity of Δ on Continuously Differentiable Functions
-/

/-- The Laplacian commutes with addition. -/
/-
**InnerProductSpace._root_.ContDiffWithinAt.laplacianWithin_add** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with addition.
-/
theorem _root_.ContDiffWithinAt.laplacianWithin_add (h₁ : ContDiffWithinAt ℝ 2 f₁ s x)
    (h₂ : ContDiffWithinAt ℝ 2 f₂ s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (f₁ + f₂)) x = (Δ[s] f₁) x + (Δ[s] f₂) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_add_distrib, iteratedFDerivWithin_add_apply h₁ h₂ hs hx]

/-- The Laplacian commutes with addition. -/
/-
**InnerProductSpace._root_.ContDiffAt.laplacian_add** 是 Mathlib 中的一个定理，位于命名空间 `I
nnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with addition.
-/
theorem _root_.ContDiffAt.laplacian_add (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) x = Δ f₁ x + Δ f₂ x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_add_distrib, iteratedFDeriv_add_apply h₁ h₂]

/-- The Laplacian commutes with addition. -/
/-
**InnerProductSpace._root_.ContDiffAt.laplacianWithin_add_nhdsWithin** 是 Mathlib
 中的一个定理，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with addition.
-/
theorem _root_.ContDiffAt.laplacianWithin_add_nhdsWithin (h₁ : ContDiffWithinAt ℝ 2 f₁ s x)
    (h₂ : ContDiffWithinAt ℝ 2 f₂ s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    Δ[s] (f₁ + f₂) =ᶠ[𝓝[s] x] (Δ[s] f₁) + Δ[s] f₂ := by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_add h₂y hs h₃y]

/-- The Laplacian commutes with addition. -/
/-
**InnerProductSpace._root_.ContDiffAt.laplacian_add_nhds** 是 Mathlib 中的一个定理，位于命名
空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with addition.
-/
theorem _root_.ContDiffAt.laplacian_add_nhds (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) =ᶠ[𝓝 x] (Δ f₁) + (Δ f₂) := by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_add h₂x

/-- The Laplacian commutes with negation. -/
/-
**InnerProductSpace.laplacianWithin_neg** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductS
pace`。
形式化陈述：laplacianWithin_neg (hs : UniqueDiffOn Real s) (hx : x in s) : (Δ[s] (-f))
 x = -(Δ[s] f) x
参数：hs : UniqueDiffOn Real s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormal
Basis`：laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis {e : E} (hs :
 UniqueDiffOn Real s) (he : e in s) : (Δ[s] f) e = ∑ i, iteratedFDe…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `iteratedFDerivWithin_neg_apply`：iteratedFDerivWithin_neg_apply {f : E ->
 F} (hu : UniqueDiffOn 𝕜 s) (hx : x in s) : iteratedFDerivWithin 𝕜 i (-f) s x = 
-iteratedFDerivWithi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousMultilinearMap.instIsNegApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Ring R] [inst_1 : (i : ι) → AddComm
Group (M₁ i)]   [inst_2 : AddCommGr…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Laplacian commutes with negation.
-/
theorem laplacianWithin_neg (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (-f)) x = -(Δ[s] f) x := by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx]
  rw [iteratedFDerivWithin_neg_apply hs hx]
  aesop

/-- The Laplacian commutes with negation. -/
/-
**InnerProductSpace.laplacian_neg** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：laplacian_neg : Δ (-f) = -(Δ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`：lapla
cian_eq_iteratedFDeriv_stdOrthonormalBasis : Δ f = fun x => ∑ i, iteratedFDeriv 
Real 2 f x ![(stdOrthonormalBasis Real E) i, (stdOrthon…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDeriv_neg`：iteratedFDeriv_neg {i : Nat} {f : E -> F} : iterated
FDeriv 𝕜 i (-f) = -iteratedFDeriv 𝕜 i f
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousMultilinearMap.instIsNegApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Ring R] [inst_1 : (i : ι) → AddComm
Group (M₁ i)]   [inst_2 : AddCommGr…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x

--- 原说明 ---
The Laplacian commutes with negation.
-/
theorem laplacian_neg :
    Δ (-f) = -(Δ f) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_neg]
  aesop

/-- The Laplacian commutes with subtraction. -/
/-
**InnerProductSpace._root_.ContDiffWithinAt.laplacianWithin_sub** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with subtraction.
-/
theorem _root_.ContDiffWithinAt.laplacianWithin_sub (h₁ : ContDiffWithinAt ℝ 2 f₁ s x)
    (h₂ : ContDiffWithinAt ℝ 2 f₂ s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (f₁ - f₂)) x = (Δ[s] f₁) x - (Δ[s] f₂) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_sub_distrib, iteratedFDerivWithin_sub_apply h₁ h₂ hs hx]

/-- The Laplacian commutes with subtraction. -/
/-
**InnerProductSpace._root_.ContDiffAt.laplacian_sub** 是 Mathlib 中的一个定理，位于命名空间 `I
nnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with subtraction.
-/
theorem _root_.ContDiffAt.laplacian_sub (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ - f₂) x = Δ f₁ x - Δ f₂ x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_sub_distrib, iteratedFDeriv_sub_apply h₁ h₂]

/-- The Laplacian commutes with subtraction. -/
/-
**InnerProductSpace._root_.ContDiffAt.laplacianWithin_sub_nhdsWithin** 是 Mathlib
 中的一个定理，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with subtraction.
-/
theorem _root_.ContDiffAt.laplacianWithin_sub_nhdsWithin (h₁ : ContDiffWithinAt ℝ 2 f₁ s x)
    (h₂ : ContDiffWithinAt ℝ 2 f₂ s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    Δ[s] (f₁ - f₂) =ᶠ[𝓝[s] x] (Δ[s] f₁) - Δ[s] f₂ := by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_sub h₂y hs h₃y]

/-- The Laplacian commutes with subtraction. -/
/-
**InnerProductSpace._root_.ContDiffAt.laplacian_sub_nhds** 是 Mathlib 中的一个定理，位于命名
空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with subtraction.
-/
theorem _root_.ContDiffAt.laplacian_sub_nhds (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ - f₂) =ᶠ[𝓝 x] (Δ f₁) - (Δ f₂) := by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_sub h₂x

/-- The Laplacian commutes with scalar multiplication. -/
/-
**InnerProductSpace.laplacianWithin_smul** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space`。
形式化陈述：laplacianWithin_smul (v : 𝕜) (hf : ContDiffWithinAt Real 2 f s x) (hs : Un
iqueDiffOn Real s) (hx : x in s) : (Δ[s] (v • f)) x = v • (Δ[s] f) x
参数：v : 𝕜；hf : ContDiffWithinAt Real 2 f s x；hs : UniqueDiffOn Real s；hx : x in s
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormal
Basis`：laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis {e : E} (hs :
 UniqueDiffOn Real s) (he : e in s) : (Δ[s] f) e = ∑ i, iteratedFDe…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iteratedFDerivWithin_const_smul_apply`：iteratedFDerivWithin_const_smul_a
pply (hf : ContDiffWithinAt 𝕜 i f s x) (hu : UniqueDiffOn 𝕜 s) (hx : x in s) : i
teratedFDerivWithin 𝕜 i (a …
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Laplacian commutes with scalar multiplication.
-/
theorem laplacianWithin_smul (v : 𝕜) (hf : ContDiffWithinAt ℝ 2 f s x) (hs : UniqueDiffOn ℝ s)
    (hx : x ∈ s) :
    (Δ[s] (v • f)) x = v • (Δ[s] f) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    iteratedFDerivWithin_const_smul_apply hf hs hx,
    Finset.smul_sum]

/-- The Laplacian commutes with scalar multiplication. -/
/-
**InnerProductSpace.laplacian_smul** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`
。
形式化陈述：laplacian_smul (v : 𝕜) (hf : ContDiffAt Real 2 f x) : Δ (v • f) x = v • (Δ
 f) x
参数：v : 𝕜；hf : ContDiffAt Real 2 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`：lapla
cian_eq_iteratedFDeriv_stdOrthonormalBasis : Δ f = fun x => ∑ i, iteratedFDeriv 
Real 2 f x ![(stdOrthonormalBasis Real E) i, (stdOrthon…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iteratedFDeriv_const_smul_apply`：iteratedFDeriv_const_smul_apply (hf : C
ontDiffAt 𝕜 i f x) : iteratedFDeriv 𝕜 i (a • f) x = a • iteratedFDeriv 𝕜 i f x
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Laplacian commutes with scalar multiplication.
-/
theorem laplacian_smul (v : 𝕜) (hf : ContDiffAt ℝ 2 f x) : Δ (v • f) x = v • (Δ f) x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_smul_apply hf,
    Finset.smul_sum]

/-- The Laplacian commutes with scalar multiplication. -/
/-
**InnerProductSpace.laplacianWithin_smul_nhds** 是 Mathlib 中的一个定理，位于命名空间 `InnerPr
oductSpace`。
形式化陈述：laplacianWithin_smul_nhds (v : 𝕜) (hf : ContDiffWithinAt Real 2 f s x) (hs
 : UniqueDiffOn Real s) : Δ[s] (v • f) =ᶠ[𝓝[s] x] v • (Δ[s] f)
参数：v : 𝕜；hf : ContDiffWithinAt Real 2 f s x；hs : UniqueDiffOn Real s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `ContDiffWithinAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `InnerProductSpace.laplacianWithin_smul`：laplacianWithin_smul (v : 𝕜) (hf
 : ContDiffWithinAt Real 2 f s x) (hs : UniqueDiffOn Real s) (hx : x in s) : (Δ[
s] (v • f)) x = v • (Δ[s] f)…

--- 原说明 ---
The Laplacian commutes with scalar multiplication.
-/
theorem laplacianWithin_smul_nhds
    (v : 𝕜) (hf : ContDiffWithinAt ℝ 2 f s x) (hs : UniqueDiffOn ℝ s) :
    Δ[s] (v • f) =ᶠ[𝓝[s] x] v • (Δ[s] f) := by
  filter_upwards [(hf.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using laplacianWithin_smul v h₁a hs

/-- The Laplacian commutes with scalar multiplication. -/
/-
**InnerProductSpace.laplacian_smul_nhds** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductS
pace`。
形式化陈述：laplacian_smul_nhds (v : 𝕜) (h : ContDiffAt Real 2 f x) : Δ (v • f) =ᶠ[𝓝 x
] v • (Δ f)
参数：v : 𝕜；h : ContDiffAt Real 2 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContDiffAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type uF} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InnerProductSpace.laplacian_smul`：laplacian_smul (v : 𝕜) (hf : ContDiffA
t Real 2 f x) : Δ (v • f) x = v • (Δ f) x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Laplacian commutes with scalar multiplication.
-/
theorem laplacian_smul_nhds (v : 𝕜) (h : ContDiffAt ℝ 2 f x) :
    Δ (v • f) =ᶠ[𝓝 x] v • (Δ f) := by
  filter_upwards [h.eventually (by simp)] with a ha
  simp [laplacian_smul v ha]

/-!
## Commutativity of Δ with Linear Operators

This section establishes commutativity with linear operators, showing in particular that `Δ`
commutes with taking real and imaginary parts of complex-valued functions.
-/

/-- The Laplacian commutes with left composition by continuous linear maps. -/
/-
**InnerProductSpace._root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left** 是 Ma
thlib 中的一个定理，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with left composition by continuous linear maps.
-/
theorem _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left {l : F →L[ℝ] G}
    (h : ContDiffWithinAt ℝ 2 f s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (l ∘ f)) x = (l ∘ (Δ[s] f)) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left h hs hx]

/-- The Laplacian commutes with left composition by continuous linear maps. -/
/-
**InnerProductSpace._root_.ContDiffAt.laplacian_CLM_comp_left** 是 Mathlib 中的一个定理
，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with left composition by continuous linear maps.
-/
theorem _root_.ContDiffAt.laplacian_CLM_comp_left {l : F →L[ℝ] G} (h : ContDiffAt ℝ 2 f x) :
    Δ (l ∘ f) x = (l ∘ (Δ f)) x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left h]

/-- The Laplacian commutes with left composition by continuous linear maps. -/
/-
**InnerProductSpace._root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left_nhds**
 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with left composition by continuous linear maps.
-/
theorem _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left_nhds {l : F →L[ℝ] G}
    (h : ContDiffWithinAt ℝ 2 f s x) (hs : UniqueDiffOn ℝ s) :
    Δ[s] (l ∘ f) =ᶠ[𝓝[s] x] l ∘ Δ[s] f := by
  filter_upwards [(h.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using h₁a.laplacianWithin_CLM_comp_left hs

/-- The Laplacian commutes with left composition by continuous linear maps. -/
/-
**InnerProductSpace._root_.ContDiffAt.laplacian_CLM_comp_left_nhds** 是 Mathlib 中
的一个定理，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian commutes with left composition by continuous linear maps.
-/
theorem _root_.ContDiffAt.laplacian_CLM_comp_left_nhds {l : F →L[ℝ] G} (h : ContDiffAt ℝ 2 f x) :
    Δ (l ∘ f) =ᶠ[𝓝 x] l ∘ (Δ f) := by
  filter_upwards [h.eventually (by simp)] with a ha
  rw [ha.laplacian_CLM_comp_left]

/-- The Laplacian commutes with left composition by continuous linear equivalences. -/
/-
**InnerProductSpace.laplacianWithin_CLE_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Inn
erProductSpace`。
形式化陈述：laplacianWithin_CLE_comp_left {l : F ≃L[Real] G} (hs : UniqueDiffOn Real s
) (hx : x in s) : (Δ[s] (l ∘ f)) x = (l ∘ (Δ[s] f)) x
参数：hs : UniqueDiffOn Real s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormal
Basis`：laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis {e : E} (hs :
 UniqueDiffOn Real s) (he : e in s) : (Δ[s] f) e = ∑ i, iteratedFDe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.iteratedFDerivWithin_comp_left`：ContinuousLinearEq
uiv.iteratedFDerivWithin_comp_left (g : F ≃L[𝕜] G) (f : E -> F) (hs : UniqueDiff
On 𝕜 s) (hx : x in s) (i : Nat) : iterated…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Laplacian commutes with left composition by continuous linear equivalences.
-/
theorem laplacianWithin_CLE_comp_left {l : F ≃L[ℝ] G} (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (l ∘ f)) x = (l ∘ (Δ[s] f)) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left _ hs hx]

/-- The Laplacian commutes with left composition by continuous linear equivalences. -/
/-
**InnerProductSpace.laplacian_CLE_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `InnerProd
uctSpace`。
形式化陈述：laplacian_CLE_comp_left {l : F ≃L[Real] G} : Δ (l ∘ f) = l ∘ (Δ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`：lapla
cian_eq_iteratedFDeriv_stdOrthonormalBasis : Δ f = fun x => ∑ i, iteratedFDeriv 
Real 2 f x ![(stdOrthonormalBasis Real E) i, (stdOrthon…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.iteratedFDeriv_comp_left`：ContinuousLinearEquiv.it
eratedFDeriv_comp_left {f : E -> F} {x : E} (g : F ≃L[𝕜] G) {i : Nat} : iterated
FDeriv 𝕜 i (g ∘ f) x = g.toContinuou…
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Laplacian commutes with left composition by continuous linear equivalences.
-/
theorem laplacian_CLE_comp_left {l : F ≃L[ℝ] G} :
    Δ (l ∘ f) = l ∘ (Δ f) := by
  ext x
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left]

end InnerProductSpace

