/-
Copyright (c) 2025 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schauder Bases and Generalized Bases

This file defines the theory of bases in Banach spaces, unifying the classical
sequential notion with modern generalized bases.

## Overview

A **basis** in a normed space allows every vector to be expanded as a (potentially infinite) linear
combination of basis vectors. Historically, this was defined strictly for sequences with convergence
of partial sums (the "classical Schauder basis").

However, modern functional analysis requires bases indexed by arbitrary sets
`β` (e.g., for non-separable spaces or Hilbert spaces), where convergence
is defined via nets over finite subsets (unconditional convergence).

This file provides a unified structure `GeneralSchauderBasis` that captures both:
* **Classical Schauder Bases:** Indexed by `ℕ`, using `SummationFilter.conditional`
  to enforce sequential convergence of partial sums.
* **Unconditional/Extended Bases:** Indexed by an arbitrary type `β`, using
  `SummationFilter.unconditional` to enforce convergence of the net of all finite subsets.

## Main Definitions

* `GeneralSchauderBasis β 𝕜 X L`: A structure representing a generalized Schauder basis for a
  normed space `X` over a field `𝕜`, indexed by a type `β` with a `SummationFilter L`.
* `SchauderBasis 𝕜 X`: The classical Schauder basis, an abbreviation for
  `GeneralSchauderBasis ℕ 𝕜 X (SummationFilter.conditional ℕ)`.
* `UnconditionalSchauderBasis β 𝕜 X`: An unconditional Schauder basis, an abbreviation for
  `GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)`.
* `GeneralSchauderBasis.proj b A`: The projection onto a finite set `A` of basis vectors,
  mapping `x ↦ ∑ i ∈ A, b.coord i x • b i`.
* `SchauderBasis.proj b n`: The `n`-th projection `X → X`,
  mapping `x ↦ ∑ i ∈ Finset.range n, b.coord i x • b i`.
* `UnconditionalSchauderBasis.enormProjBound`: The supremum of projection norms (`ℝ≥0∞`).
* `UnconditionalSchauderBasis.nnnormProjBound`: The supremum of projection norms (`ℝ≥0`),
  requires `[CompleteSpace X]`.
* `RankOneDecomposition 𝕜 X`: Data for constructing a Schauder basis from
  a sequence of finite-rank projections whose differences are rank one.
* `RankOneDecomposition.basis`: Constructs a `SchauderBasis` from a `RankOneDecomposition`.

## Main Results

* `GeneralSchauderBasis.linearIndependent`: A Schauder basis is linearly independent.
* `GeneralSchauderBasis.tendsto_proj`: The projections `proj A` converge to identity
  along the summation filter.
* `GeneralSchauderBasis.range_proj_eq_span`: The range of `proj A` is the span of the basis
  elements in `A`.
* `GeneralSchauderBasis.proj_comp`: Composition of projections satisfies
  `proj A (proj B x) = proj (A ∩ B) x`.
* `SchauderBasis.exists_norm_proj_le`: In a Banach space, the projections are uniformly bounded.
* `UnconditionalSchauderBasis.exists_norm_proj_le`: For unconditional bases, projections
  onto all finite sets are uniformly bounded.

## References

* [Albiac, Fernando. and Kalton, Nigel J., Topics in Banach Space Theory][Albiac_Kalton_2016].
* [Singer, Ivan, Bases in Banach spaces][Singer_1970].
* [Marti, Jürg T., Introduction to the theory of bases][MartiJurg1969].

-/

@[expose] public section

noncomputable section

open Filter Topology LinearMap Set ENNReal NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

open scoped Classical in
/--
A generalized Schauder basis indexed by `β` with summation along filter `L`.

The key fields are:
* `basis`: The basis vectors `e i` for `i : β`
* `coord`: The coordinate functionals `f i` for `i : β` in the dual space
* `ortho`: Biorthogonality condition `f i (e j) = if i = j then 1 else 0`
* `expansion`: Every `x` equals `∑ i, f i x • e i`, converging along `L`

See `SchauderBasis` for the classical `ℕ`-indexed case with conditional convergence,
and `UnconditionalSchauderBasis` for the unconditional case.
-/
@[ext]
/-
**GeneralSchauderBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(β : Type u_3) →   (𝕜 : Type u_4) →     (X : Type u_5) →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup X] → [NormedSpace
 𝕜 X] → SummationFilter β → Type (max (max u_3 u_4) u_5)
参数：max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generalized Schauder basis indexed by `β` with summation along filter `L`.

The key fields are:
* `basis`: The basis vectors `e i` for `i : β`
* `coord`: The coordinate functionals `f i` for `i : β` in the dual space
* `ortho`: Biorthogonality condition `f i (e j) = if i = j then 1 else 0`
* `expansion`: Every `x` equals `∑ i, f i x • e i`, converging along `L`

See `SchauderBasis` for the classical `ℕ`-indexed case with conditional converge
nce,
and `UnconditionalSchauderBasis` for the unconditional case.
-/
structure GeneralSchauderBasis (β : Type*) (𝕜 : Type*)
    (X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (L : SummationFilter β) where
  /-- The basis vectors. -/
  basis : β → X
  /-- Coordinate functionals. -/
  coord : β → StrongDual 𝕜 X
  /-- Biorthogonality. -/
  ortho (i j : β) : coord i (basis j) = (Pi.single j (1 : 𝕜) : β → 𝕜) i
  /-- The sum converges to `x` along the provided `SummationFilter L`. -/
  expansion (x : X) : HasSum (fun i ↦ (coord i) x • basis i) x L

variable {β : Type*}
variable {L : SummationFilter β}

/-- A classical Schauder basis indexed by `ℕ` with conditional convergence. -/
/-
**SchauderBasis** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SchauderBasis (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜] [NormedA
ddCommGroup X] [NormedSpace 𝕜 X]
参数：𝕜 : Type*；X : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A classical Schauder basis indexed by `ℕ` with conditional convergence.
-/
abbrev SchauderBasis (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  GeneralSchauderBasis ℕ 𝕜 X (SummationFilter.conditional ℕ)

/--
An unconditional Schauder basis indexed by `β`.

In the literature, this is known as:
* An **Extended Basis** [Marti, Jürg T., Introduction to the theory of bases][MartiJurg1969]:
Defined via convergence of the net of finite partial sums.
* An **Unconditional Basis** [Singer, Ivan., Bases in Banach spaces][Singer_1970]: On an arbitrary
set, convergence is necessarily unconditional.

This structure generalizes the classical Schauder basis by replacing sequential
convergence with summability over the directed set of finite subsets.
-/
/-
**UnconditionalSchauderBasis** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UnconditionalSchauderBasis (β : Type*) (𝕜 : Type*) (X : Type*) [Nontrivial
lyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
参数：β : Type*；𝕜 : Type*；X : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An unconditional Schauder basis indexed by `β`.

In the literature, this is known as:
* An **Extended Basis** [Marti, Jürg T., Introduction to the theory of bases][Ma
rtiJurg1969]:
Defined via convergence of the net of finite partial sums.
* An **Unconditional Basis** [Singer, Ivan., Bases in Banach spaces][Singer_1970
]: On an arbitrary
set, convergence is necessarily unconditional.

This structure generalizes the classical Schauder basis by replacing sequential
convergence with summability over the directed set of finite subsets.
-/
abbrev UnconditionalSchauderBasis (β : Type*)
    (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)

/-- Coercion from a `GeneralSchauderBasis` to the underlying basis function. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from a `GeneralSchauderBasis` to the underlying basis function.
-/
instance : CoeFun (GeneralSchauderBasis β 𝕜 X L) (fun _ ↦ β → X) where
  coe b := b.basis
attribute [coe] GeneralSchauderBasis.basis
namespace GeneralSchauderBasis

variable (b : GeneralSchauderBasis β 𝕜 X L)

/-- The basis vectors are linearly independent. -/
/-
**GeneralSchauderBasis.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `GeneralSchau
derBasis`。
形式化陈述：linearIndependent : LinearIndependent 𝕜 b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
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
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `GeneralSchauderBasis.ortho`：∀ {β : Type u_3} {𝕜 : Type u_4} {X : Type u_
5} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup X]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
The basis vectors are linearly independent.
-/
theorem linearIndependent : LinearIndependent 𝕜 b := by
  classical
  refine linearIndependent_iff.mpr (fun l hl ↦ l.ext ?_)
  simpa [l.linearCombination_apply, Finsupp.sum, b.ortho, Pi.single_apply] using
    fun i ↦ congr_arg (b.coord i) hl

/-- Projection onto a finite set of basis vectors. -/
/-
**GeneralSchauderBasis.proj** 是 Mathlib 中的一个定义，位于命名空间 `GeneralSchauderBasis`。
形式化陈述：proj (A : Finset β) : X ->L[𝕜] X
参数：A : Finset β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection onto a finite set of basis vectors.
-/
def proj (A : Finset β) : X →L[𝕜] X := ∑ i ∈ A, (b.coord i).smulRight (b i)

/-- The projection on the empty set is the zero map. -/
@[simp]
/-
**GeneralSchauderBasis.proj_empty** 是 Mathlib 中的一个定理，位于命名空间 `GeneralSchauderBasi
s`。
形式化陈述：proj_empty : b.proj ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The projection on the empty set is the zero map.
-/
theorem proj_empty : b.proj ∅ = 0 := by simp [proj]

/-- The action of the projection on a vector `x`. -/
@[simp]
/-
**GeneralSchauderBasis.proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `GeneralSchauderBasi
s`。
形式化陈述：proj_apply (A : Finset β) (x : X) : b.proj A x = ∑ i in A, b.coord i x • b
 i
参数：A : Finset β；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The action of the projection on a vector `x`.
-/
theorem proj_apply (A : Finset β) (x : X) : b.proj A x = ∑ i ∈ A, b.coord i x • b i := by
  simp [proj, _root_.sum_apply, ContinuousLinearMap.smulRight_apply]

open scoped Classical in
/-- The action of the projection on a basis element `e i`. -/
/-
**GeneralSchauderBasis.proj_apply_basis_mem** 是 Mathlib 中的一个定理，位于命名空间 `GeneralSc
hauderBasis`。
形式化陈述：proj_apply_basis_mem (A : Finset β) (i : β) : b.proj A (b i) = if i in A t
hen b i else 0
参数：A : Finset β；i : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GeneralSchauderBasis.proj_apply`：proj_apply (A : Finset β) (x : X) : b.p
roj A x = ∑ i in A, b.coord i x • b i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `GeneralSchauderBasis.ortho`：∀ {β : Type u_3} {𝕜 : Type u_4} {X : Type u_
5} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup X]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The action of the projection on a basis element `e i`.
-/
theorem proj_apply_basis_mem (A : Finset β) (i : β) :
    b.proj A (b i) = if i ∈ A then b i else 0 := by
  simp [b.ortho, Pi.single_apply]

/-- The projections `b.proj A x` converge to `x` along the summation filter. -/
/-
**GeneralSchauderBasis.tendsto_proj** 是 Mathlib 中的一个定理，位于命名空间 `GeneralSchauderBa
sis`。
形式化陈述：tendsto_proj (x : X) : Tendsto (fun A => b.proj A x) L.filter (𝓝 x)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `GeneralSchauderBasis.proj_apply`：proj_apply (A : Finset β) (x : X) : b.p
roj A x = ∑ i in A, b.coord i x • b i
· 使用定理 `GeneralSchauderBasis.expansion`：∀ {β : Type u_3} {𝕜 : Type u_4} {X : Typ
e u_5} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup X]   [ins
t_2 : NormedSpace 𝕜 …

--- 原说明 ---
The projections `b.proj A x` converge to `x` along the summation filter.
-/
theorem tendsto_proj (x : X) : Tendsto (fun A ↦ b.proj A x) L.filter (𝓝 x) := by
  simpa using! b.expansion x

/-- The range of the projection is the span of the basis elements in `A`. -/
/-
**GeneralSchauderBasis.range_proj_eq_span** 是 Mathlib 中的一个定理，位于命名空间 `GeneralScha
uderBasis`。
形式化陈述：range_proj_eq_span (A : Finset β) : (b.proj A).toLinearMap.range = Submodu
le.span 𝕜 (b '' A)
参数：A : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `GeneralSchauderBasis.proj_apply`：proj_apply (A : Finset β) (x : X) : b.p
roj A x = ∑ i in A, b.coord i x • b i
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `GeneralSchauderBasis.proj_apply_basis_mem`：proj_apply_basis_mem (A : Fin
set β) (i : β) : b.proj A (b i) = if i in A then b i else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)

--- 原说明 ---
The range of the projection is the span of the basis elements in `A`.
-/
theorem range_proj_eq_span (A : Finset β) :
    (b.proj A).toLinearMap.range = Submodule.span 𝕜 (b '' A) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, proj_apply]
    exact Submodule.sum_mem _ fun i hi ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    use b i
    rw [ContinuousLinearMap.coe_coe, proj_apply_basis_mem, if_pos (Finset.mem_coe.mp hi)]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- Composition of projections: `proj A (proj B x) = proj (A ∩ B) x`. -/
/-
**GeneralSchauderBasis.proj_comp** 是 Mathlib 中的一个定理，位于命名空间 `GeneralSchauderBasis
`。
形式化陈述：proj_comp (A B : Finset β) (x : X) : b.proj A (b.proj B x) = b.proj (A int
er B) x
参数：A B : Finset β；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GeneralSchauderBasis.proj_apply`：proj_apply (A : Finset β) (x : X) : b.p
roj A x = ∑ i in A, b.coord i x • b i
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GeneralSchauderBasis.ortho`：∀ {β : Type u_3} {𝕜 : Type u_4} {X : Type u_
5} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup X]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_ite_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   (∑ i ∈ s, if i ∈ t
 then f …
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Composition of projections: `proj A (proj B x) = proj (A ∩ B) x`.
-/
theorem proj_comp (A B : Finset β) (x : X) : b.proj A (b.proj B x) = b.proj (A ∩ B) x := by
  simp only [proj_apply, map_sum, map_smul, b.ortho, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', smul_ite, smul_zero, Finset.sum_ite_mem]
  congr 1
  ext _
  simp [and_comm]

/-- The dimension of the range of the projection `proj A` equals the cardinality of `A`. -/
/-
**GeneralSchauderBasis.finrank_range_proj** 是 Mathlib 中的一个定理，位于命名空间 `GeneralScha
uderBasis`。
形式化陈述：finrank_range_proj (A : Finset β) : Module.finrank 𝕜 (b.proj A).toLinearMa
p.range = A.card
参数：A : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GeneralSchauderBasis.range_proj_eq_span`：range_proj_eq_span (A : Finset 
β) : (b.proj A).toLinearMap.range = Submodule.span 𝕜 (b '' A)
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `finrank_span_eq_card`：finrank_span_eq_card [Nontrivial R] {ι : Type*} [F
intype ι] {b : ι -> M} (hb : LinearIndependent R b) : finrank R (span R (Set.ran
ge b)) = F…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `GeneralSchauderBasis.linearIndependent`：linearIndependent : LinearIndepe
ndent 𝕜 b
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s

--- 原说明 ---
The dimension of the range of the projection `proj A` equals the cardinality of 
`A`.
-/
theorem finrank_range_proj (A : Finset β) :
    Module.finrank 𝕜 (b.proj A).toLinearMap.range = A.card := by
  rw [range_proj_eq_span, Set.image_eq_range, finrank_span_eq_card]
  · exact Fintype.card_coe A
  · exact b.linearIndependent.comp (fun i : A ↦ i.val) Subtype.val_injective

end GeneralSchauderBasis

/-! ### Unconditional Schauder bases -/

namespace UnconditionalSchauderBasis

variable (b : UnconditionalSchauderBasis β 𝕜 X)

/-- The basis constant for unconditional bases (supremum over all finite sets) as `enorm`. -/
/-
**UnconditionalSchauderBasis.enormProjBound** 是 Mathlib 中的一个定义，位于命名空间 `Unconditi
onalSchauderBasis`。
形式化陈述：enormProjBound : Real>=0∞
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis constant for unconditional bases (supremum over all finite sets) as `e
norm`.
-/
noncomputable def enormProjBound : ℝ≥0∞ := ⨆ A : Finset β, ‖b.proj A‖ₑ

/-- The `enorm` of any projection is bounded by the basis constant. -/
/-
**UnconditionalSchauderBasis.enorm_proj_le_enormProjBound** 是 Mathlib 中的一个定理，位于命
名空间 `UnconditionalSchauderBasis`。
形式化陈述：enorm_proj_le_enormProjBound (A : Finset β) : ‖b.proj A‖ₑ <= b.enormProjBo
und
参数：A : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f

--- 原说明 ---
The `enorm` of any projection is bounded by the basis constant.
-/
theorem enorm_proj_le_enormProjBound (A : Finset β) : ‖b.proj A‖ₑ ≤ b.enormProjBound :=
  le_iSup (fun A ↦ ‖b.proj A‖ₑ) A

/-- Projections are uniformly bounded for unconditional bases. -/
/-
**UnconditionalSchauderBasis.exists_norm_proj_le** 是 Mathlib 中的一个定理，位于命名空间 `Unco
nditionalSchauderBasis`。
形式化陈述：exists_norm_proj_le [CompleteSpace X] : exists C : Real, forall A : Finset
 β, ‖b.proj A‖ <= C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `banach_steinhaus`：banach_steinhaus {ι : Type*} [CompleteSpace E] {g : ι 
-> E ->SL[σ₁₂] F} (h : forall x, exists C, forall i, ‖g i x‖ <= C) : exists C', 
forall…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_iff_vanishing_norm`：summable_iff_vanishing_norm [CompleteSpace 
E] {f : ι -> E} : Summable f ↔ forall ε > (0 : Real), exists s : Finset ι, foral
l t, Disjoint t s…
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `GeneralSchauderBasis.expansion`：∀ {β : Type u_3} {𝕜 : Type u_4} {X : Typ
e u_5} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup X]   [ins
t_2 : NormedSpace 𝕜 …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Finset.powerset_nonempty`：powerset_nonempty (s : Finset α) : s.powerset.
Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GeneralSchauderBasis.proj_apply`：proj_apply (A : Finset β) (x : X) : b.p
roj A x = ∑ i in A, b.coord i x • b i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Finset.disjoint_sdiff_inter`：disjoint_sdiff_inter (s t : Finset α) : Dis
joint (s \ t) (s inter t)
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `Finset.sdiff_union_inter`：sdiff_union_inter (s t : Finset α) : s \ t uni
on s inter t = s
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Projections are uniformly bounded for unconditional bases.
-/
theorem exists_norm_proj_le [CompleteSpace X] : ∃ C : ℝ, ∀ A : Finset β, ‖b.proj A‖ ≤ C := by
  classical
  apply banach_steinhaus
  intro x
  obtain ⟨A₀, hA₀⟩ := summable_iff_vanishing_norm.mp (b.expansion x).summable 1 zero_lt_one
  use (A₀.powerset.image fun B ↦ ‖b.proj B x‖).sup' ((Finset.powerset_nonempty A₀).image _) id + 1
  intro A
  have hdecomp : b.proj A x = b.proj (A ∩ A₀) x + b.proj (A \ A₀) x := by
    simp only [GeneralSchauderBasis.proj_apply]
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter A A₀).symm,
      Finset.union_comm, Finset.sdiff_union_inter]
  rw [hdecomp]
  -- -- The projection on the tail (A \ A₀) at `x` is bounded by 1
  have htail : ‖b.proj (A \ A₀) x‖ < 1 := by
    rw [GeneralSchauderBasis.proj_apply]
    exact hA₀ (A \ A₀) Finset.sdiff_disjoint
  apply (norm_add_le _ _).trans (add_le_add _ htail.le)
  -- The projection on (A ∩ A₀) at `x` is bounded by the `sup'`.
  exact Finset.le_sup' id <| Finset.mem_image_of_mem (fun B ↦ ‖b.proj B x‖)
      (Finset.mem_powerset.2 Finset.inter_subset_right)

/-- The basis constant for unconditional bases (supremum over all finite sets) as `nnnorm`.
    It requires completeness to guarantee that the supremum is finite,
    see lemma `bddAbove_range_nnnorm_proj` below. -/
/-
**UnconditionalSchauderBasis.nnnormProjBound** 是 Mathlib 中的一个定义，位于命名空间 `Uncondit
ionalSchauderBasis`。
形式化陈述：nnnormProjBound : Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis constant for unconditional bases (supremum over all finite sets) as `n
nnorm`.
    It requires completeness to guarantee that the supremum is finite,
    see lemma `bddAbove_range_nnnorm_proj` below.
-/
noncomputable def nnnormProjBound : ℝ≥0 := ⨆ A : Finset β, ‖b.proj A‖₊

/-- The projection norms are bounded above in a complete space. -/
/-
**UnconditionalSchauderBasis.bddAbove_range_nnnorm_proj** 是 Mathlib 中的一个定理，位于命名空
间 `UnconditionalSchauderBasis`。
形式化陈述：bddAbove_range_nnnorm_proj [CompleteSpace X] : BddAbove (Set.range (fun A 
: Finset β => ‖b.proj A‖₊))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnconditionalSchauderBasis.exists_norm_proj_le`：exists_norm_proj_le [Com
pleteSpace X] : exists C : Real, forall A : Finset β, ‖b.proj A‖ <= C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GeneralSchauderBasis.proj_empty`：proj_empty : b.proj ∅ = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖

--- 原说明 ---
The projection norms are bounded above in a complete space.
-/
theorem bddAbove_range_nnnorm_proj [CompleteSpace X] :
    BddAbove (Set.range (fun A : Finset β ↦ ‖b.proj A‖₊)) := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 ≤ C := by simpa [GeneralSchauderBasis.proj_empty] using hC ∅
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨A, rfl⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
  exact hC A

/-- The `nnnorm` of any projection is bounded by the basis constant. -/
/-
**UnconditionalSchauderBasis.nnnorm_proj_le_nnnormProjBound** 是 Mathlib 中的一个定理，位
于命名空间 `UnconditionalSchauderBasis`。
形式化陈述：nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) : ‖b.proj 
A‖₊ <= b.nnnormProjBound
参数：A : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `UnconditionalSchauderBasis.bddAbove_range_nnnorm_proj`：bddAbove_range_nn
norm_proj [CompleteSpace X] : BddAbove (Set.range (fun A : Finset β => ‖b.proj A
‖₊))

--- 原说明 ---
The `nnnorm` of any projection is bounded by the basis constant.
-/
theorem nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) :
    ‖b.proj A‖₊ ≤ b.nnnormProjBound :=
  le_ciSup (bddAbove_range_nnnorm_proj b) A

/-- The norm of any projection is bounded by the basis constant. -/
/-
**UnconditionalSchauderBasis.norm_proj_le_nnnormProjBound** 是 Mathlib 中的一个定理，位于命
名空间 `UnconditionalSchauderBasis`。
形式化陈述：norm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) : ‖b.proj A‖
 <= b.nnnormProjBound
参数：A : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnconditionalSchauderBasis.nnnorm_proj_le_nnnormProjBound`：nnnorm_proj_l
e_nnnormProjBound [CompleteSpace X] (A : Finset β) : ‖b.proj A‖₊ <= b.nnnormProj
Bound

--- 原说明 ---
The norm of any projection is bounded by the basis constant.
-/
theorem norm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) :
    ‖b.proj A‖ ≤ b.nnnormProjBound :=
  mod_cast b.nnnorm_proj_le_nnnormProjBound A

end UnconditionalSchauderBasis

/-! ### ℕ-indexed Schauder bases with conditional convergence -/

namespace SchauderBasis

variable (b : SchauderBasis 𝕜 X)

/-- The `n`-th projection `P_n = b.proj (Finset.range n)`, given by:
    `P_n x = ∑ i ∈ Finset.range n, b.coord i x • b i` -/
/-
**SchauderBasis.proj** 是 Mathlib 中的一个定义，位于命名空间 `SchauderBasis`。
形式化陈述：proj (n : Nat) : X ->L[𝕜] X
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th projection `P_n = b.proj (Finset.range n)`, given by:
    `P_n x = ∑ i ∈ Finset.range n, b.coord i x • b i`
-/
def proj (n : ℕ) : X →L[𝕜] X := GeneralSchauderBasis.proj b (Finset.range n)

/-- The projection at `0` is the zero map. -/
@[simp]
/-
**SchauderBasis.proj_zero** 是 Mathlib 中的一个定理，位于命名空间 `SchauderBasis`。
形式化陈述：proj_zero : b.proj 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchauderBasis.proj.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X]
 (b : Schaude…
· 使用定理 `Finset.range_zero`：range_zero : range 0 = ∅
· 使用定理 `GeneralSchauderBasis.proj_empty`：proj_empty : b.proj ∅ = 0

--- 原说明 ---
The projection at `0` is the zero map.
-/
theorem proj_zero : b.proj 0 = 0 := by rw [proj, Finset.range_zero, GeneralSchauderBasis.proj_empty]

/-- The action of the projection on a vector. -/
@[simp]
/-
**SchauderBasis.proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchauderBasis`。
形式化陈述：proj_apply (n : Nat) (x : X) : b.proj n x = ∑ i in Finset.range n, b.coord
 i x • b i
参数：n : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchauderBasis.proj.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X]
 (b : Schaude…
· 使用定理 `GeneralSchauderBasis.proj_apply`：proj_apply (A : Finset β) (x : X) : b.p
roj A x = ∑ i in A, b.coord i x • b i

--- 原说明 ---
The action of the projection on a vector.
-/
theorem proj_apply (n : ℕ) (x : X) : b.proj n x = ∑ i ∈ Finset.range n, b.coord i x • b i := by
  rw [proj, GeneralSchauderBasis.proj_apply]

/-- The action of the projection on a basis element `e i`. -/
/-
**SchauderBasis.proj_apply_basis_mem** 是 Mathlib 中的一个定理，位于命名空间 `SchauderBasis`。
形式化陈述：proj_apply_basis_mem (n i : Nat) : b.proj n (b i) = if i < n then b i else
 0
参数：n i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchauderBasis.proj.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X]
 (b : Schaude…
· 使用定理 `GeneralSchauderBasis.proj_apply_basis_mem`：proj_apply_basis_mem (A : Fin
set β) (i : β) : b.proj A (b i) = if i in A then b i else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The action of the projection on a basis element `e i`.
-/
theorem proj_apply_basis_mem (n i : ℕ) : b.proj n (b i) = if i < n then b i else 0 := by
  rw [proj, GeneralSchauderBasis.proj_apply_basis_mem]
  simp

/-- The range of the projection is the span of the first `n` basis elements. -/
/-
**SchauderBasis.range_proj_eq_span** 是 Mathlib 中的一个定理，位于命名空间 `SchauderBasis`。
形式化陈述：range_proj_eq_span (n : Nat) : (b.proj n).toLinearMap.range = Submodule.sp
an 𝕜 (b '' ↑(Finset.range n))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchauderBasis.proj.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X]
 (b : Schaude…
· 使用定理 `GeneralSchauderBasis.range_proj_eq_span`：range_proj_eq_span (A : Finset 
β) : (b.proj A).toLinearMap.range = Submodule.span 𝕜 (b '' A)

--- 原说明 ---
The range of the projection is the span of the first `n` basis elements.
-/
theorem range_proj_eq_span (n : ℕ) :
    (b.proj n).toLinearMap.range = Submodule.span 𝕜 (b '' ↑(Finset.range n)) := by
  rw [proj, GeneralSchauderBasis.range_proj_eq_span]

/-- The dimension of the range of the projection `P n` is `n`. -/
/-
**SchauderBasis.finrank_range_proj** 是 Mathlib 中的一个定理，位于命名空间 `SchauderBasis`。
形式化陈述：finrank_range_proj (n : Nat) : Module.finrank 𝕜 (b.proj n).toLinearMap.ran
ge = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchauderBasis.proj.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X]
 (b : Schaude…
· 使用定理 `GeneralSchauderBasis.finrank_range_proj`：finrank_range_proj (A : Finset 
β) : Module.finrank 𝕜 (b.proj A).toLinearMap.range = A.card
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n

--- 原说明 ---
The dimension of the range of the projection `P n` is `n`.
-/
theorem finrank_range_proj (n : ℕ) :
    Module.finrank 𝕜 (b.proj n).toLinearMap.range = n := by
  rw [proj, GeneralSchauderBasis.finrank_range_proj, Finset.card_range]

/-- The projections converge pointwise to the identity map. -/
/-
**SchauderBasis.tendsto_proj** 是 Mathlib 中的一个定理，位于命名空间 `SchauderBasis`。
形式化陈述：tendsto_proj (x : X) : Tendsto (fun n => b.proj n x) atTop (𝓝 x)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GeneralSchauderBasis.tendsto_proj`：tendsto_proj (x : X) : Tendsto (fun A
 => b.proj A x) L.filter (𝓝 x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SummationFilter.conditional_filter_eq_map_range`：conditional_filter_eq_m
ap_range : (conditional Nat).filter = atTop.map Finset.range

--- 原说明 ---
The projections converge pointwise to the identity map.
-/
theorem tendsto_proj (x : X) : Tendsto (fun n ↦ b.proj n x) atTop (𝓝 x) := by
  have := GeneralSchauderBasis.tendsto_proj b x
  rwa [SummationFilter.conditional_filter_eq_map_range] at this

/-- Composition of projections: `proj n (proj m x) = proj (min n m) x`. -/
/-
**SchauderBasis.proj_comp** 是 Mathlib 中的一个定理，位于命名空间 `SchauderBasis`。
形式化陈述：proj_comp (n m : Nat) (x : X) : b.proj n (b.proj m x) = b.proj (min n m) x
参数：n m : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GeneralSchauderBasis.proj_comp`：proj_comp (A B : Finset β) (x : X) : b.p
roj A (b.proj B x) = b.proj (A inter B) x
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p

--- 原说明 ---
Composition of projections: `proj n (proj m x) = proj (min n m) x`.
-/
theorem proj_comp (n m : ℕ) (x : X) : b.proj n (b.proj m x) = b.proj (min n m) x := by
  simp only [proj, GeneralSchauderBasis.proj_comp]
  congr 2
  ext _
  simp only [Finset.mem_inter, Finset.mem_range]
  omega

/-- The projections are uniformly bounded. -/
/-
**SchauderBasis.exists_norm_proj_le** 是 Mathlib 中的一个定理，位于命名空间 `SchauderBasis`。
形式化陈述：exists_norm_proj_le [CompleteSpace X] : exists C : Real, forall n : Nat, ‖
b.proj n‖ <= C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `banach_steinhaus`：banach_steinhaus {ι : Type*} [CompleteSpace E] {g : ι 
-> E ->SL[σ₁₂] F} (h : forall x, exists C, forall i, ‖g i x‖ <= C) : exists C', 
forall…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `Metric.isBounded_range_of_tendsto`：isBounded_range_of_tendsto (u : Nat -
> α) {x : α} (hu : Tendsto u atTop (𝓝 x)) : IsBounded (range u)
· 使用定理 `SchauderBasis.tendsto_proj`：tendsto_proj (x : X) : Tendsto (fun n => b.p
roj n x) atTop (𝓝 x)
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
The projections are uniformly bounded.
-/
theorem exists_norm_proj_le [CompleteSpace X] : ∃ C : ℝ, ∀ n : ℕ, ‖b.proj n‖ ≤ C := by
  apply banach_steinhaus
  intro x
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun n ↦ b.proj n x) (tendsto_proj b x))
  exact ⟨M, Set.forall_mem_range.mp hM⟩

/-- The basis constant for Schauder bases (supremum over projections) as `enorm`. -/
/-
**SchauderBasis.enormProjBound** 是 Mathlib 中的一个定义，位于命名空间 `SchauderBasis`。
形式化陈述：enormProjBound : Real>=0∞
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis constant for Schauder bases (supremum over projections) as `enorm`.
-/
noncomputable def enormProjBound : ℝ≥0∞ := ⨆ n, ‖b.proj n‖ₑ

/-- The enorm of any projection is bounded by the basis constant. -/
/-
**SchauderBasis.enorm_proj_le_enormProjBound** 是 Mathlib 中的一个定理，位于命名空间 `Schauder
Basis`。
形式化陈述：enorm_proj_le_enormProjBound (n : Nat) : ‖b.proj n‖ₑ <= b.enormProjBound
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f

--- 原说明 ---
The enorm of any projection is bounded by the basis constant.
-/
theorem enorm_proj_le_enormProjBound (n : ℕ) : ‖b.proj n‖ₑ ≤ b.enormProjBound :=
  le_iSup (fun i ↦ ‖b.proj i‖ₑ) n

/-- The basis constant for Schauder bases (supremum over projections) as `nnnorm`.
    Requires completeness to guarantee the supremum is finite,
    see lemma `bddAbove_range_nnnorm_proj` below. -/
/-
**SchauderBasis.nnnormProjBound** 是 Mathlib 中的一个定义，位于命名空间 `SchauderBasis`。
形式化陈述：nnnormProjBound : Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis constant for Schauder bases (supremum over projections) as `nnnorm`.
    Requires completeness to guarantee the supremum is finite,
    see lemma `bddAbove_range_nnnorm_proj` below.
-/
noncomputable def nnnormProjBound : ℝ≥0 := ⨆ n, ‖b.proj n‖₊

/-- The projection norms are bounded above in a complete space. -/
/-
**SchauderBasis.bddAbove_range_nnnorm_proj** 是 Mathlib 中的一个定理，位于命名空间 `SchauderBa
sis`。
形式化陈述：bddAbove_range_nnnorm_proj [CompleteSpace X] : BddAbove (Set.range (fun n 
: Nat => ‖b.proj n‖₊))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchauderBasis.exists_norm_proj_le`：exists_norm_proj_le [CompleteSpace X]
 : exists C : Real, forall n : Nat, ‖b.proj n‖ <= C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SchauderBasis.proj_zero`：proj_zero : b.proj 0 = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖

--- 原说明 ---
The projection norms are bounded above in a complete space.
-/
theorem bddAbove_range_nnnorm_proj [CompleteSpace X] :
    BddAbove (Set.range (fun n : ℕ ↦ ‖b.proj n‖₊)) := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 ≤ C := by simpa [proj_zero] using hC 0
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
  exact hC n

/-- The `nnnorm` of any projection is bounded by the basis constant. -/
/-
**SchauderBasis.nnnorm_proj_le_nnnormProjBound** 是 Mathlib 中的一个定理，位于命名空间 `Schaud
erBasis`。
形式化陈述：nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (n : Nat) : ‖b.proj n‖₊ <
= b.nnnormProjBound
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `SchauderBasis.bddAbove_range_nnnorm_proj`：bddAbove_range_nnnorm_proj [Co
mpleteSpace X] : BddAbove (Set.range (fun n : Nat => ‖b.proj n‖₊))

--- 原说明 ---
The `nnnorm` of any projection is bounded by the basis constant.
-/
theorem nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (n : ℕ) :
    ‖b.proj n‖₊ ≤ b.nnnormProjBound :=
  le_ciSup (bddAbove_range_nnnorm_proj b) n

/-- The norm of any projection is bounded by the basis constant. -/
/-
**SchauderBasis.norm_proj_le_nnnormProjBound** 是 Mathlib 中的一个定理，位于命名空间 `Schauder
Basis`。
形式化陈述：norm_proj_le_nnnormProjBound [CompleteSpace X] (n : Nat) : ‖b.proj n‖ <= b
.nnnormProjBound
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchauderBasis.nnnorm_proj_le_nnnormProjBound`：nnnorm_proj_le_nnnormProjB
ound [CompleteSpace X] (n : Nat) : ‖b.proj n‖₊ <= b.nnnormProjBound

--- 原说明 ---
The norm of any projection is bounded by the basis constant.
-/
theorem norm_proj_le_nnnormProjBound [CompleteSpace X] (n : ℕ) :
    ‖b.proj n‖ ≤ b.nnnormProjBound :=
  mod_cast b.nnnorm_proj_le_nnnormProjBound n

/-!
### Construction of Schauder basis

We explain how to construct a Schauder basis from a sequence `P n` of projections
satisfying `P n ∘ P m = P (min n m)`, converging to the identity pointwise, and such that each
`P (n+1) - P n` has rank one. The idea is to define the basis vectors as
`e n = (P (n+1) - P n) x` for some `x` such that this is non-zero, and then
show that these vectors form a Schauder basis. -/

/-- The difference operator `P (n + 1) - P n`. -/
/-
**SchauderBasis.succSub** 是 Mathlib 中的一个定义，位于命名空间 `SchauderBasis`。
形式化陈述：succSub (P : Nat -> X ->L[𝕜] X) (n : Nat) : X ->L[𝕜] X
参数：P : Nat -> X ->L[𝕜] X；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The difference operator `P (n + 1) - P n`.
-/
def succSub (P : ℕ → X →L[𝕜] X) (n : ℕ) : X →L[𝕜] X := P (n + 1) - P n

/-- The sum of `succSub` operators up to `n` equals `P n`. -/
@[simp]
/-
**SchauderBasis.sum_succSub** 是 Mathlib 中的一个引理，位于命名空间 `SchauderBasis`。
形式化陈述：sum_succSub (P : Nat -> X ->L[𝕜] X) (h0 : P 0 = 0) (n : Nat) : ∑ i in Fins
et.range n, succSub P i = P n
参数：P : Nat -> X ->L[𝕜] X；h0 : P 0 = 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `SchauderBasis.succSub.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜
 X] (P : ℕ → X →…
· 使用定理 `_private.Mathlib.Analysis.Normed.Module.Bases.0.SchauderBasis.sum_succSu
b._abel_1_2`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {X : Type u_1} 
[inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X] (P : ℕ → X →…

--- 原说明 ---
The sum of `succSub` operators up to `n` equals `P n`.
-/
lemma sum_succSub (P : ℕ → X →L[𝕜] X) (h0 : P 0 = 0) (n : ℕ) :
    ∑ i ∈ Finset.range n, succSub P i = P n := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, succSub]; abel

/-- The operators `succSub P i` satisfy a biorthogonality relation. -/
/-
**SchauderBasis.succSub_ortho** 是 Mathlib 中的一个引理，位于命名空间 `SchauderBasis`。
形式化陈述：succSub_ortho {P : Nat -> X ->L[𝕜] X} (hcomp : forall n m, forall x : X, P
 n (P m x) = P (min n m) x) (i j : Nat) (x : X) : succSub P i (succSub P j x) = 
if i = j then succSub P j x else 0
参数：hcomp : forall n m, forall x : X, P n (P m x) = P (min n m) x；i j : Nat；x : X
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_min_add_right`：∀ (a b c : ℕ), min (a + c) (b + c) = min a b + c
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.min_eq_left`：∀ {a b : ℕ}, a ≤ b → min a b = a
· 使用定理 `_private.Mathlib.Analysis.Normed.Module.Bases.0.SchauderBasis.succSub_or
tho._abel_1_2`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {X : Type u_1
} [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X] {P : ℕ → X →…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.lt_or_gt_of_ne`：∀ {a b : ℕ}, a ≠ b → a < b ∨ a > b
· 使用定理 `min_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a 
< b → min a b = a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `_private.Mathlib.Analysis.Normed.Module.Bases.0.SchauderBasis.succSub_or
tho._abel_1_3`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {X : Type u_1
} [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X] {P : ℕ → X →…
· 使用定理 `min_eq_right_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b
 < a → min a b = b
· 使用定理 `_private.Mathlib.Analysis.Normed.Module.Bases.0.SchauderBasis.succSub_or
tho._abel_1_4`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {X : Type u_1
} [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X] {P : ℕ → X →…

--- 原说明 ---
The operators `succSub P i` satisfy a biorthogonality relation.
-/
lemma succSub_ortho {P : ℕ → X →L[𝕜] X} (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
    (i j : ℕ) (x : X) : succSub P i (succSub P j x) = if i = j then succSub P j x else 0 := by
  simp only [succSub, _root_.sub_apply, map_sub, hcomp,
    Nat.add_min_add_right]
  split_ifs with h
  · rw [h, min_self, min_eq_right (Nat.le_succ j), Nat.min_eq_left (Nat.le_succ j)]
    abel
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left_of_lt h', min_eq_left (Nat.succ_le_of_lt h'),
        min_eq_left_of_lt (Nat.lt_succ_of_lt h')]
      abel
    · rw [min_eq_right_of_lt h', min_eq_right (Nat.succ_le_of_lt h'),
        min_eq_right_of_lt (Nat.lt_succ_of_lt h')]
      abel

/-- Assuming that the `finrank` of the range of `P n` is `n` then the `finrank` of the range of
    `succSub P n` is `1`. -/
/-
**SchauderBasis.finrank_range_succSub_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Schauder
Basis`。
形式化陈述：finrank_range_succSub_eq_one {P : Nat -> X ->L[𝕜] X} (hrank : forall n, Mo
dule.finrank 𝕜 (P n).toLinearMap.range = n) (hcomp : forall n m, forall x : X, P
 n (P m x) = P (min n m) x) (n : Nat) : Module.finrank 𝕜 (succSub P n).toLinearM
ap.range = 1
参数：hrank : forall n, Module.finrank 𝕜 (P n).toLinearMap.range = n；hcomp : forall
 n m, forall x : X, P n (P m x) = P (min n m) x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Submodule.add_mem_sup`：add_mem_sup {S T : Submodule R M} {s t : M} (hs :
 s in S) (ht : t in T) : s + t in S ⊔ T
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
Assuming that the `finrank` of the range of `P n` is `n` then the `finrank` of t
he range of
    `succSub P n` is `1`.
-/
lemma finrank_range_succSub_eq_one {P : ℕ → X →L[𝕜] X}
    (hrank : ∀ n, Module.finrank 𝕜 (P n).toLinearMap.range = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x) (n : ℕ) :
    Module.finrank 𝕜 (succSub P n).toLinearMap.range = 1 := by
  let U := (succSub P n).toLinearMap.range
  let V := (P n).toLinearMap.range
  let W := (P (n + 1)).toLinearMap.range
  have hV : V ≤ W := by
    rintro _ ⟨y, rfl⟩
    exact ⟨P n y, by simp [ContinuousLinearMap.coe_coe, hcomp]⟩
  have hUW : U ≤ W := by
    rintro _ ⟨y, rfl⟩
    exact Submodule.sub_mem W ⟨y, rfl⟩ (hV ⟨y, rfl⟩)
  have hW : W = U ⊔ V := by
    apply le_antisymm
    · rintro x ⟨y, hy⟩
      rw [← hy, ContinuousLinearMap.coe_coe, ← sub_add_cancel ((P (n + 1)) y) ((P n) y)]
      exact Submodule.add_mem_sup ⟨y, rfl⟩ ⟨y, rfl⟩
    · exact sup_le hUW hV
  have hdisj : U ⊓ V = ⊥ := eq_bot_iff.mpr fun x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ ↦ by
    simp only [Submodule.mem_bot]
    calc x = (P n) x := by rw [← hz, ContinuousLinearMap.coe_coe, hcomp, min_self]
         _ = 0       := by rw [← hy, ContinuousLinearMap.coe_coe]; simp [succSub, map_sub, hcomp]
  have : FiniteDimensional 𝕜 W := .of_finrank_pos (by rw [hrank]; exact Nat.succ_pos n)
  have : FiniteDimensional 𝕜 U := Submodule.finiteDimensional_of_le hUW
  have : FiniteDimensional 𝕜 V := Submodule.finiteDimensional_of_le hV
  have h_dim := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hdisj, finrank_bot, add_zero, ← hW, hrank, hrank, Nat.add_comm] at h_dim
  exact Nat.add_right_cancel h_dim.symm

variable (𝕜 X) in
/-- Data for constructing a Schauder basis from a sequence of finite-rank projections.

Given a sequence of continuous linear maps `P n : X →L[𝕜] X` satisfying:
* `P 0 = 0` and `finrank(range(P n)) = n`,
* `P n ∘ P m = P (min n m)` (the projections are nested and commute),
* `P n x → x` for every `x` (pointwise convergence to the identity),

the differences `succSub P n = P (n+1) - P n` are rank-one operators
(see `finrank_range_succSub_eq_one`). Choosing a nonzero vector `e n` in the range of each
`succSub P n` yields a Schauder basis for `X`.

Use `RankOneDecomposition.basis` to construct the `SchauderBasis` from this data. -/
/-
**SchauderBasis.RankOneDecomposition** 是 Mathlib 中的一个归纳类型，位于命名空间 `SchauderBasis`
。
形式化陈述：(𝕜 : Type u_1) →   [inst : NontriviallyNormedField 𝕜] → (X : Type u_2) → [
inst_1 : NormedAddCommGroup X] → [NormedSpace 𝕜 X] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Data for constructing a Schauder basis from a sequence of finite-rank projection
s.

Given a sequence of continuous linear maps `P n : X →L[𝕜] X` satisfying:
* `P 0 = 0` and `finrank(range(P n)) = n`,
* `P n ∘ P m = P (min n m)` (the projections are nested and commute),
* `P n x → x` for every `x` (pointwise convergence to the identity),

the differences `succSub P n = P (n+1) - P n` are rank-one operators
(see `finrank_range_succSub_eq_one`). Choosing a nonzero vector `e n` in the ran
ge of each
`succSub P n` yields a Schauder basis for `X`.

Use `RankOneDecomposition.basis` to construct the `SchauderBasis` from this data
.
-/
structure RankOneDecomposition where
  /-- The sequence of finite-rank projections. -/
  P : ℕ → X →L[𝕜] X
  /-- The sequence of candidate basis vectors. -/
  e : ℕ → X
  /-- The projections start at `0`. -/
  proj_zero : P 0 = 0
  /-- The `n`-th projection has rank `n`. -/
  finrank_range (n : ℕ) : Module.finrank 𝕜 (P n).toLinearMap.range = n
  /-- The projections commute and are nested `P n (P m) = P (min n m)`. -/
  proj_comp (n m : ℕ) (x : X) : P n (P m x) = P (min n m) x
  /-- The projections converge pointwise to the identity. -/
  proj_tendsto (x : X) : Tendsto (fun n ↦ P n x) atTop (𝓝 x)
  /-- The vector `e_n` lies in the range of the operator `succSub P n = P (n+1) - P n`. -/
  e_mem_range (n : ℕ) : e n ∈ (succSub P n).toLinearMap.range
  /-- The vector `e_n` is non-zero. -/
  e_ne_zero (n : ℕ) : e n ≠ 0

namespace RankOneDecomposition

variable (D : RankOneDecomposition 𝕜 X)

/-- There exists a coefficient scaling `e n` to match `(succSub D.P n) x`. -/
/-
**SchauderBasis.RankOneDecomposition.exists_coeff** 是 Mathlib 中的一个引理，位于命名空间 `Sch
auderBasis.RankOneDecomposition`。
形式化陈述：exists_coeff (n : Nat) (x : X) : exists c : 𝕜, c • D.e n = (succSub D.P n)
 x
参数：n : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SchauderBasis.finrank_range_succSub_eq_one`：finrank_range_succSub_eq_one
 {P : Nat -> X ->L[𝕜] X} (hrank : forall n, Module.finrank 𝕜 (P n).toLinearMap.r
ange = n) (hcomp : forall n m, f…
· 使用定理 `SchauderBasis.RankOneDecomposition.finrank_range`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [
inst_2 : NormedSpace 𝕜 X] (self : Scha…
· 使用定理 `SchauderBasis.RankOneDecomposition.proj_comp`：∀ {𝕜 : Type u_1} [inst : N
ontriviallyNormedField 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [inst
_2 : NormedSpace 𝕜 X] (self : Scha…
· 使用定理 `FiniteDimensional.of_finrank_pos`：of_finrank_pos (h : 0 < finrank K V) :
 FiniteDimensional K V
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `SchauderBasis.RankOneDecomposition.e_mem_range`：∀ {𝕜 : Type u_1} [inst :
 NontriviallyNormedField 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [in
st_2 : NormedSpace 𝕜 X] (self : Scha…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `SchauderBasis.RankOneDecomposition.e_ne_zero`：∀ {𝕜 : Type u_1} [inst : N
ontriviallyNormedField 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [inst
_2 : NormedSpace 𝕜 X] (self : Scha…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f

--- 原说明 ---
There exists a coefficient scaling `e n` to match `(succSub D.P n) x`.
-/
lemma exists_coeff (n : ℕ) (x : X) :
    ∃ c : 𝕜, c • D.e n = (succSub D.P n) x := by
  let S := (succSub D.P n).toLinearMap
  have hrank : Module.finrank 𝕜 S.range = 1 :=
    finrank_range_succSub_eq_one D.finrank_range D.proj_comp n
  have : FiniteDimensional 𝕜 S.range := .of_finrank_pos (hrank.symm ▸ zero_lt_one)
  have hspan : Submodule.span 𝕜 {D.e n} = S.range := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (D.e_mem_range n)
    · simp [hrank, finrank_span_singleton (D.e_ne_zero n)]
  exact Submodule.mem_span_singleton.mp (hspan.symm ▸ LinearMap.mem_range_self S x)

/-- The coefficient functional value for the basis construction. -/
/-
**SchauderBasis.RankOneDecomposition.basisCoeff** 是 Mathlib 中的一个定义，位于命名空间 `Schau
derBasis.RankOneDecomposition`。
形式化陈述：basisCoeff (n : Nat) (x : X) : 𝕜
参数：n : Nat；x : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SchauderBasis.RankOneDecomposition.exists_coeff`：exists_coeff (n : Nat) 
(x : X) : exists c : 𝕜, c • D.e n = (succSub D.P n) x

--- 原说明 ---
The coefficient functional value for the basis construction.
-/
def basisCoeff (n : ℕ) (x : X) : 𝕜 :=
  Classical.choose (exists_coeff D n x)

/-- The coefficient satisfies `basisCoeff D n x • D.e n = (succSub D.P n) x`. -/
@[simp]
/-
**SchauderBasis.RankOneDecomposition.basisCoeff_spec** 是 Mathlib 中的一个引理，位于命名空间 `
SchauderBasis.RankOneDecomposition`。
形式化陈述：basisCoeff_spec (n : Nat) (x : X) : basisCoeff D n x • D.e n = (succSub D.
P n) x
参数：n : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `SchauderBasis.RankOneDecomposition.exists_coeff`：exists_coeff (n : Nat) 
(x : X) : exists c : 𝕜, c • D.e n = (succSub D.P n) x

--- 原说明 ---
The coefficient satisfies `basisCoeff D n x • D.e n = (succSub D.P n) x`.
-/
lemma basisCoeff_spec (n : ℕ) (x : X) :
    basisCoeff D n x • D.e n = (succSub D.P n) x :=
  Classical.choose_spec (exists_coeff D n x)

/-- Constructs a Schauder basis from rank one decomposition. -/
/-
**SchauderBasis.RankOneDecomposition.basis** 是 Mathlib 中的一个定义，位于命名空间 `SchauderBa
sis.RankOneDecomposition`。
形式化陈述：basis : SchauderBasis 𝕜 X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a Schauder basis from rank one decomposition.
-/
def basis : SchauderBasis 𝕜 X :=
  let coeff := basisCoeff D
  have hcoeff : ∀ n x, (succSub D.P n) x = coeff n x • D.e n := fun n x ↦
    (basisCoeff_spec D n x).symm
  { basis := D.e
    coord := fun n ↦ LinearMap.mkContinuous
      { toFun := coeff n
        map_add' := fun x y ↦ smul_left_injective 𝕜 (D.e_ne_zero n) <| by
          simp only [add_smul, ← hcoeff, map_add]
        map_smul' := fun c x ↦ smul_left_injective 𝕜 (D.e_ne_zero n) <| by
          dsimp only [RingHom.id_apply]
          rw [smul_eq_mul, ← smul_smul, ← hcoeff, ← hcoeff, map_smul] }
      (‖succSub D.P n‖ / ‖D.e n‖)
      (fun x ↦ by
        rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (D.e_ne_zero n))]
        calc ‖coeff n x‖ * ‖D.e n‖ = ‖coeff n x • D.e n‖ := (norm_smul _ _).symm
          _ = ‖(succSub D.P n) x‖ := by rw [hcoeff]
          _ ≤ ‖succSub D.P n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _)
    ortho := fun i j ↦ smul_left_injective 𝕜 (D.e_ne_zero i) <| by
      obtain ⟨x, hx⟩ : ∃ x, (succSub D.P j) x = D.e j := D.e_mem_range j
      simp only [mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← hcoeff, ← hx, succSub_ortho D.proj_comp, hx]
      simp only [Pi.single_apply]
      split_ifs with h <;> simp [h]
    expansion := fun x ↦ by
      rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
      exact (D.proj_tendsto x).congr fun n ↦ by
        simp only [Function.comp, LinearMap.coe_mk, AddHom.coe_mk,
                   LinearMap.mkContinuous_apply, ← hcoeff]
        rw [← _root_.sum_apply, sum_succSub D.P D.proj_zero] }

/-- The projections of the constructed basis correspond to the input data `D.P`. -/
@[simp]
/-
**SchauderBasis.RankOneDecomposition.basis_proj** 是 Mathlib 中的一个定理，位于命名空间 `Schau
derBasis.RankOneDecomposition`。
形式化陈述：basis_proj : (basis D).proj = D.P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchauderBasis.proj_apply`：proj_apply (n : Nat) (x : X) : b.proj n x = ∑ 
i in Finset.range n, b.coord i x • b i
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SchauderBasis.sum_succSub`：sum_succSub (P : Nat -> X ->L[𝕜] X) (h0 : P 0
 = 0) (n : Nat) : ∑ i in Finset.range n, succSub P i = P n
· 使用定理 `SchauderBasis.RankOneDecomposition.proj_zero`：∀ {𝕜 : Type u_1} [inst : N
ontriviallyNormedField 𝕜] {X : Type u_2} [inst_1 : NormedAddCommGroup X]   [inst
_2 : NormedSpace 𝕜 X] (self : Scha…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `SchauderBasis.RankOneDecomposition.basisCoeff_spec`：basisCoeff_spec (n :
 Nat) (x : X) : basisCoeff D n x • D.e n = (succSub D.P n) x

--- 原说明 ---
The projections of the constructed basis correspond to the input data `D.P`.
-/
theorem basis_proj : (basis D).proj = D.P := by
  ext n _
  rw [SchauderBasis.proj_apply, ← sum_succSub D.P D.proj_zero n]
  simp only [_root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  dsimp [basis, mkContinuous_apply, IsLinearMap.mk'_apply]
  rw [basisCoeff_spec]

/-- The sequence of the constructed basis corresponds to the input data `D.e`. -/
@[simp]
/-
**SchauderBasis.RankOneDecomposition.basis_coe** 是 Mathlib 中的一个定理，位于命名空间 `Schaud
erBasis.RankOneDecomposition`。
形式化陈述：basis_coe : ⇑(basis D) = D.e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sequence of the constructed basis corresponds to the input data `D.e`.
-/
theorem basis_coe : ⇑(basis D) = D.e :=
  rfl

end RankOneDecomposition

end SchauderBasis

