/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Local frames in a vector bundle

Let `V → M` be a finite rank smooth vector bundle with standard fiber `F`.
A family of sections `s i` of `V → M` is called a **C^k local frame** on a set `U ⊆ M` iff each
section `s i` is `C^k` on `U`, and the section values `s i x` form a basis for each `x ∈ U`.
We define a predicate `IsLocalFrame` for a collection of sections to be a local frame on a set,
and define basic notions (such as the coefficients of a section w.r.t. a local frame, and
checking the smoothness of `t` via its coefficients in a local frame).

Given a basis `b` for `F` and a local trivialisation `e` for `V`, we construct a
**smooth local frame** on `V` w.r.t. `e` and `b`, i.e. a collection of sections `sᵢ` of `V`
which is smooth on `e.baseSet` such that `{sᵢ x}` is a basis of `V x` for each `x ∈ e.baseSet`.
Any section `s` of `e` can be uniquely written as `s = ∑ i, f^i sᵢ` near `x`,
and `s` is smooth at `x` iff the functions `f^i` are.

In this file, we prove the latter statement for finite-rank bundles (with coefficients in a
complete field). In the planned file `Mathlib/Geometry/Manifold/VectorBundle/OrthonormalFrame.lean`
(#26221), we will prove the same for real vector bundles of any rank which admit a `C^n` bundle
metric. This includes bundles of finite rank, modelled on a Hilbert space or on a Banach space which
has smooth partitions of unity.

## Main definitions and results

* `IsLocalFrameOn`: a family of sections `s i` of `V → M` is called a **C^k local frame** on a set
  `U ⊆ M` iff each section `s i` is `C^k` on `U`, and the section values `s i x` form a basis for
  each `x ∈ U`

Suppose `{sᵢ}` is a local frame on `U`, and `hs : IsLocalFrameOn s U`.
* `IsLocalFrameOn.toBasisAt hs`: for each `x ∈ U`, the vectors `sᵢ x` form a basis of `F`
* `IsLocalFrameOn.coeff hs` describes the coefficient of sections of `V` w.r.t. `{sᵢ}`.
  `hs.coeff i` is a family of fiberwise linear maps `Π x, V x →ₗ[𝕜] 𝕜`.
  The coefficient function of a section `t` is `(LinearMap.piApply (hs.coeff i)) t`.
* `IsLocalFrameOn.eventually_eq_sum_coeff_smul hs`: for a local frame `{sᵢ}` near `x`,
  for each section `t` we have `t = ∑ i, (LinearMap.piApply (hs.coeff i) t) • sᵢ` near `x`.
* `IsLocalFrameOn.coeff_sum_eq hs t hx` proves that
  `t x = ∑ i, hs.coeff i x (t x) • sᵢ x`, provided that `hx : x ∈ U`.
* `IsLocalFrameOn.coeff_congr hs`: the coefficient `hs.coeff i` of `t` in the local frame `{sᵢ}`
  only depends on `t` at `x`.
* `IsLocalFrameOn.eq_iff_coeff hs`: two sections `t` and `t'` are equal at `x` if and only if their
  coefficients at `x` w.r.t. `{sᵢ}` agree.
* `IsLocalFrameOn.contMDiffOn_of_coeff hs`: a section `t` is `C^k` on `U` if each coefficient
  `(LinearMap.piApply (hs.coeff i) t)` is `C^k` on `U`
* `IsLocalFrameOn.contMDiffAt_of_coeff hs`: a section `t` is `C^k` at `x ∈ U`
  if all of its frame coefficients are
* `IsLocalFrameOn.contMDiffOn_off_coeff hs`: a section `t` is `C^k` on an open set `t ⊆ U`
  ff all of its frame coefficients are
* `MDifferentiable` versions of the previous three statements

In the following lemmas, let `e` be a compatible local trivialisation of `V`, and `b` a basis of
the model fiber `F`.
* `Bundle.Trivialization.basisAt e b`: for each `x ∈ e.baseSet`,
  return the basis of `V x` induced by `e` and `b`
* `e.localFrame b`: the local frame on `V` induced by `e` and `b`.
  Use `e.localFrame b i` to access the i-th section in that frame.
* `e.contMDiffOn_localFrame_baseSet`: each section `e.localFrame b i` is smooth on `e.baseSet`
* `e.localFrameCoeff b i` describes the `i`-th coefficient of sections of `V` w.r.t.
  `e.localFrame b`: it is a family of fiberwise linear maps `Π x, V x →ₗ[𝕜] 𝕜`, and the coefficient
  function of a section `s` is `(LinearMap.piApply (e.localFrameCoeff b i)) s`.
* `e.eventually_eq_localFrame_sum_coeff_smul b`: near `x`, we have
  `s = ∑ i, (LinearMap.piApply (e.localFrameCoeff b i) s) • e.localFrame b i`
* `e.localFrameCoeff_congr b`: the coefficient `e.localFrameCoeff b i` of `s` in the local frame
  induced by `e` and `b` at `x` only depends on `s` at `x`.
* `e.contMDiffOn_localFrameCoeff`: if `s` is a `C^k` section, each coefficient
  `(LinearMap.piApply (e.localFrameCoeff b i) s)` is `C^k` on `e.baseSet`
* `e.contMDiffAt_iff_localFrameCoeff b`: a section `s` is `C^k` at `x ∈ e.baseSet`
  iff all of its frame coefficients are
* `e.contMDiffOn_iff_localFrameCoeff b`: a section `s` is `C^k` on an open set `t ⊆ e.baseSet`
  iff all of its frame coefficients are

## Note

This file proves smoothness criteria in terms of coefficients for local frames induced by a
trivialization. A fully frame-intrinsic converse for `IsLocalFrameOn` will be added later.

## Implementation notes

Local frames use the junk value pattern: they are defined on all of `M`, but their value is
only meaningful on the set on which they are a local frame.

## Tags
vector bundle, local frame, smoothness

-/

@[expose] public section
open Bundle Filter Function Topology Module

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : ℕ∞ω)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

noncomputable section

section IsLocalFrame

variable {ι : Type*} {s s' : ι → (x : M) → V x} {u u' : Set M} {x : M} {n : ℕ∞ω}

variable (I F n) in
/--
A family of sections `s i` of `V → M` is called a **C^k local frame** on a set `U ⊆ M` iff
- the section values `s i x` form a basis for each `x ∈ U`,
- each section `s i` is `C^k` on `U`.
-/
/-
**IsLocalFrameOn** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     ModelWithCorners 𝕜 E H →                 {M : Type u_4} →                  
 [inst_4 : TopologicalSpace M] →                     [ChartedSpace H M] →       
                (F : Type u_5) →                         [inst_6 : NormedAddComm
Group F] →                           [NormedSpace 𝕜 F] →                        
     {V : M → Type u_6} →                               [inst_8 : TopologicalSpa
ce (Bundle.TotalSpace F V)] →                                 [inst_9 : (x : M) 
→ AddCommGroup (V x)] →                                   [(x : M) → _root_.Modu
le 𝕜 (V x)] →                                     [inst : (x : M) → TopologicalS
pace (V x)] →                                       [FiberBundle F V] →         
                                {ι : Type u_7} → WithTop ℕ∞ → (ι → (x : M) → V x
) → Set M → Prop
参数：F : Type u_5；Bundle.TotalSpace F V；x : M；V x；x : M；V x；x : M；V x；ι → (x : M) 
→ V x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of sections `s i` of `V → M` is called a **C^k local frame** on a set `
U ⊆ M` iff
- the section values `s i x` form a basis for each `x ∈ U`,
- each section `s i` is `C^k` on `U`.
-/
structure IsLocalFrameOn (s : ι → (x : M) → V x) (u : Set M) where
  linearIndependent {x : M} (hx : x ∈ u) : LinearIndependent 𝕜 (s · x)
  generating {x : M} (hx : x ∈ u) : ⊤ ≤ Submodule.span 𝕜 (Set.range (s · x))
  contMDiffOn (i : ι) : CMDiff[u] n (T% (s i))

namespace IsLocalFrameOn

/-- If `s = s'` on `u` and `s i` is a local frame on `u`, then so is `s'`. -/
/-
**IsLocalFrameOn.congr** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：congr (hs : IsLocalFrameOn I F n s u) (hs' : forall i, forall x, x in u ->
 s i x = s' i x) : IsLocalFrameOn I F n s' u where linearIndependent
参数：hs : IsLocalFrameOn I F n s u；hs' : forall i, forall x, x in u -> s i x = s' 
i x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalFrameOn.linearIndependent`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLocalFrameOn.generating`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `IsLocalFrameOn.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `s = s'` on `u` and `s i` is a local frame on `u`, then so is `s'`.
-/
lemma congr (hs : IsLocalFrameOn I F n s u) (hs' : ∀ i, ∀ x, x ∈ u → s i x = s' i x) :
    IsLocalFrameOn I F n s' u where
  linearIndependent := by
    intro x hx
    have := hs.linearIndependent hx
    simp_all
  generating := by
    intro x hx
    have := hs.generating hx
    simp_all
  contMDiffOn i := (hs.contMDiffOn i).congr (by simp +contextual [hs'])
/-
**IsLocalFrameOn.mono** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：mono (hs : IsLocalFrameOn I F n s u) (hu'u : u' subseteq u) : IsLocalFrame
On I F n s u' where linearIndependent
参数：hs : IsLocalFrameOn I F n s u；hu'u : u' subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalFrameOn.linearIndependent`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `IsLocalFrameOn.generating`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `IsLocalFrameOn.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
-/
lemma mono (hs : IsLocalFrameOn I F n s u) (hu'u : u' ⊆ u) : IsLocalFrameOn I F n s u' where
  linearIndependent := by
    intro x hx
    exact hs.linearIndependent (hu'u hx)
  generating := by
    intro x hx
    exact hs.generating (hu'u hx)
  contMDiffOn i := (hs.contMDiffOn i).mono hu'u
/-
**IsLocalFrameOn.contMDiffAt** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：contMDiffAt (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hx : x in u) 
(i : ι) : CMDiffAt n (T% (s i)) x
参数：hs : IsLocalFrameOn I F n s u；hu : IsOpen u；hx : x in u；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `IsLocalFrameOn.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
lemma contMDiffAt (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hx : x ∈ u) (i : ι) :
    CMDiffAt n (T% (s i)) x :=
  (hs.contMDiffOn i).contMDiffAt <| hu.mem_nhds hx

/-- Given a local frame `{s i}` on `U ∋ x`, returns the basis `{s i}` of `V x` -/
/-
**IsLocalFrameOn.toBasisAt** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalFrameOn`。
形式化陈述：toBasisAt (hs : IsLocalFrameOn I F n s u) (hx : x in u) : Basis ι 𝕜 (V x)
参数：hs : IsLocalFrameOn I F n s u；hx : x in u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalFrameOn.linearIndependent`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `IsLocalFrameOn.generating`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…

--- 原说明 ---
Given a local frame `{s i}` on `U ∋ x`, returns the basis `{s i}` of `V x`
-/
def toBasisAt (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) : Basis ι 𝕜 (V x) :=
  Basis.mk (hs.linearIndependent hx) (hs.generating hx)

@[simp]
/-
**IsLocalFrameOn.toBasisAt_coe** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：toBasisAt_coe (hs : IsLocalFrameOn I F n s u) (hx : x in u) (i : ι) : toBa
sisAt hs hx i = s i x
参数：hs : IsLocalFrameOn I F n s u；hx : x in u；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.mk_apply`：mk_apply (i : ι) : Basis.mk hli hsp i = v i
· 使用定理 `IsLocalFrameOn.linearIndependent`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `IsLocalFrameOn.generating`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
-/
lemma toBasisAt_coe (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) (i : ι) :
    toBasisAt hs hx i = s i x := by
  simpa only [toBasisAt] using Basis.mk_apply (hs.linearIndependent hx) (hs.generating hx) i

/-- If `{sᵢ}` is a local frame on a vector bundle, `F` being finite-dimensional implies the
indexing set being finite. -/
@[instance_reducible]
/-
**IsLocalFrameOn.fintypeOfFiniteDimensional** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalFr
ameOn`。
形式化陈述：fintypeOfFiniteDimensional [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F] (h
s : IsLocalFrameOn I F n s u) (hx : x in u) : Fintype ι
参数：hs : IsLocalFrameOn I F n s u；hx : x in u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `{sᵢ}` is a local frame on a vector bundle, `F` being finite-dimensional impl
ies the
indexing set being finite.
-/
noncomputable def fintypeOfFiniteDimensional [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
    (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) : Fintype ι := by
  have : FiniteDimensional 𝕜 (V x) := by
    let phi := (trivializationAt F V x).linearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    exact Finite.equiv phi.symm
  exact FiniteDimensional.fintypeBasisIndex (hs.toBasisAt hx)

open scoped Classical in
/-- Coefficients of a section `s` of `V` w.r.t. a local frame `{s i}` on `u`.
Outside of `u`, this returns the junk value 0. -/
/-
**IsLocalFrameOn.coeff** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalFrameOn`。
形式化陈述：coeff (hs : IsLocalFrameOn I F n s u) (i : ι) : Π x : M, (V x ->ₗ[𝕜] 𝕜)
参数：hs : IsLocalFrameOn I F n s u；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coefficients of a section `s` of `V` w.r.t. a local frame `{s i}` on `u`.
Outside of `u`, this returns the junk value 0.
-/
def coeff (hs : IsLocalFrameOn I F n s u) (i : ι) : Π x : M, (V x →ₗ[𝕜] 𝕜) := fun x ↦
  if hx : x ∈ u then (hs.toBasisAt hx).coord i else 0

variable {x : M}

@[simp]
/-
**IsLocalFrameOn.coeff_apply_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn
`。
形式化陈述：coeff_apply_of_notMem (hs : IsLocalFrameOn I F n s u) (hx : x ∉ u) (i : ι)
 : hs.coeff i x = 0
参数：hs : IsLocalFrameOn I F n s u；hx : x ∉ u；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_apply_of_notMem (hs : IsLocalFrameOn I F n s u) (hx : x ∉ u) (i : ι) :
    hs.coeff i x = 0 := by
  simp [coeff, hx]

@[simp]
/-
**IsLocalFrameOn.coeff_apply_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：coeff_apply_of_mem (hs : IsLocalFrameOn I F n s u) (hx : x in u) (t : Π x 
: M, V x) (i : ι) : hs.coeff i x (t x) = (hs.toBasisAt hx).repr (t x) i
参数：hs : IsLocalFrameOn I F n s u；hx : x in u；t : Π x : M, V x；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_apply_of_mem (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) (t : Π x : M, V x) (i : ι) :
    hs.coeff i x (t x) = (hs.toBasisAt hx).repr (t x) i := by
  simp [coeff, hx]
/-
**IsLocalFrameOn.coeff_sum_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：coeff_sum_eq [Fintype ι] (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x
) (hx : x in u) : t x = ∑ i, hs.coeff i x (t x) • (s i x)
参数：hs : IsLocalFrameOn I F n s u；t : Π x : M, V x；hx : x in u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用引理 `IsLocalFrameOn.toBasisAt_coe`：toBasisAt_coe (hs : IsLocalFrameOn I F n s
 u) (hx : x in u) (i : ι) : toBasisAt hs hx i = s i x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
-/
lemma coeff_sum_eq [Fintype ι] (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hx : x ∈ u) :
    t x = ∑ i, hs.coeff i x (t x) • (s i x) := by
  simpa [coeff, hx] using (Basis.sum_repr (hs.toBasisAt hx) (t x)).symm
/-
**IsLocalFrameOn.eq_of_coeff_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：eq_of_coeff_eq [Finite ι] (hs : IsLocalFrameOn I F n s u) (hx : x in u) {t
 t' : Π x : M, V x} (h : forall i, hs.coeff i x (t x) = hs.coeff i x (t' x)) : t
 x = t' x
参数：hs : IsLocalFrameOn I F n s u；hx : x in u；h : forall i, hs.coeff i x (t x) = 
hs.coeff i x (t' x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalFrameOn.coeff_sum_eq`：coeff_sum_eq [Fintype ι] (hs : IsLocalFrame
On I F n s u) (t : Π x : M, V x) (hx : x in u) : t x = ∑ i, hs.coeff i x (t x) •
 (s i x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eq_of_coeff_eq [Finite ι] (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u)
    {t t' : Π x : M, V x}
    (h : ∀ i, hs.coeff i x (t x) = hs.coeff i x (t' x)) :
    t x = t' x := by
  let : Fintype ι := Fintype.ofFinite ι
  calc
    t x = ∑ i, hs.coeff i x (t x) • (s i x) := hs.coeff_sum_eq t hx
    _ = ∑ i, hs.coeff i x (t' x) • (s i x) := by simp [h]
    _ = t' x := (hs.coeff_sum_eq t' hx).symm

/-- A local frame locally spans the space of sections for `V`: for each local frame `s i` on an open
set `u` around `x`, we have `t = ∑ i, hs.coeff i x (t x) • (s i x)` near `x`. -/
/-
**IsLocalFrameOn.eventually_eq_sum_coeff_smul** 是 Mathlib 中的一个引理，位于命名空间 `IsLocal
FrameOn`。
形式化陈述：eventually_eq_sum_coeff_smul [Fintype ι] (hs : IsLocalFrameOn I F n s u) (
t : Π x : M, V x) (hu'' : u in 𝓝 x) : forallᶠ x' in 𝓝 x, t x' = ∑ i, hs.coeff i 
x' (t x') • (s i x')
参数：hs : IsLocalFrameOn I F n s u；t : Π x : M, V x；hu'' : u in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用引理 `IsLocalFrameOn.coeff_sum_eq`：coeff_sum_eq [Fintype ι] (hs : IsLocalFrame
On I F n s u) (t : Π x : M, V x) (hx : x in u) : t x = ∑ i, hs.coeff i x (t x) •
 (s i x)

--- 原说明 ---
A local frame locally spans the space of sections for `V`: for each local frame 
`s i` on an open
set `u` around `x`, we have `t = ∑ i, hs.coeff i x (t x) • (s i x)` near `x`.
-/
lemma eventually_eq_sum_coeff_smul [Fintype ι]
    (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hu'' : u ∈ 𝓝 x) :
    ∀ᶠ x' in 𝓝 x, t x' = ∑ i, hs.coeff i x' (t x') • (s i x') :=
  eventually_of_mem hu'' fun _ hx ↦ hs.coeff_sum_eq _ hx

variable {t t' : Π x : M, V x}

/-- The coefficients of `t` in a local frame at `x` only depend on `t` at `x`. -/
/-
**IsLocalFrameOn.coeff_congr** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：coeff_congr (hs : IsLocalFrameOn I F n s u) (htt' : t x = t' x) (i : ι) : 
hs.coeff i x (t x) = hs.coeff i x (t' x)
参数：hs : IsLocalFrameOn I F n s u；htt' : t x = t' x；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
The coefficients of `t` in a local frame at `x` only depend on `t` at `x`.
-/
lemma coeff_congr (hs : IsLocalFrameOn I F n s u) (htt' : t x = t' x) (i : ι) :
    hs.coeff i x (t x) = hs.coeff i x (t' x) := by
  by_cases hxe : x ∈ u <;> simp [coeff, hxe, htt']

/-- If `s` and `s'` are local frames which are equal at `x`,
a section `t` has equal frame coefficients in them. -/
/-
**IsLocalFrameOn.coeff_eq_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：coeff_eq_of_eq (hs : IsLocalFrameOn I F n s u) (hs' : IsLocalFrameOn I F n
 s' u) (hss' : forall i, s i x = s' i x) {t : Π x : M, V x} (i : ι) : hs.coeff i
 x (t x) = hs'.coeff i x (t x)
参数：hs : IsLocalFrameOn I F n s u；hs' : IsLocalFrameOn I F n s' u；hss' : forall i
, s i x = s' i x；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `IsLocalFrameOn.linearIndependent`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `IsLocalFrameOn.generating`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.mk.congr_simp`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_
5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 {v v_1 : ι → M}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
If `s` and `s'` are local frames which are equal at `x`,
a section `t` has equal frame coefficients in them.
-/
lemma coeff_eq_of_eq (hs : IsLocalFrameOn I F n s u) (hs' : IsLocalFrameOn I F n s' u)
    (hss' : ∀ i, s i x = s' i x) {t : Π x : M, V x} (i : ι) :
    hs.coeff i x (t x) = hs'.coeff i x (t x) := by
  by_cases hxe : x ∈ u
  · simp [coeff, hxe]
    simp_all only [toBasisAt]
  · simp [coeff, hxe]

/-- Two sections `s` and `t` are equal at `x` if and only if their coefficients w.r.t. some local
frame at `x` agree. -/
/-
**IsLocalFrameOn.eq_iff_coeff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`。
形式化陈述：eq_iff_coeff [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F] (hs : IsLocalFra
meOn I F n s u) (hx : x in u) : t x = t' x ↔ forall i, hs.coeff i x (t x) = hs.c
oeff i x (t' x)
参数：hs : IsLocalFrameOn I F n s u；hx : x in u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalFrameOn.coeff_congr`：coeff_congr (hs : IsLocalFrameOn I F n s u) 
(htt' : t x = t' x) (i : ι) : hs.coeff i x (t x) = hs.coeff i x (t' x)
· 使用引理 `IsLocalFrameOn.eq_of_coeff_eq`：eq_of_coeff_eq [Finite ι] (hs : IsLocalFr
ameOn I F n s u) (hx : x in u) {t t' : Π x : M, V x} (h : forall i, hs.coeff i x
 (t x) = hs.coeff i…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Two sections `s` and `t` are equal at `x` if and only if their coefficients w.r.
t. some local
frame at `x` agree.
-/
lemma eq_iff_coeff [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
    (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) :
    t x = t' x ↔ ∀ i, hs.coeff i x (t x) = hs.coeff i x (t' x) := by
  let := fintypeOfFiniteDimensional hs hx
  exact ⟨fun h i ↦ hs.coeff_congr h i, fun h ↦ hs.eq_of_coeff_eq hx h⟩

variable (hs : IsLocalFrameOn I F n s u) [VectorBundle 𝕜 F V]

/-- Given a local frame `s i ` on `u`, if a section `t` has `C^k` coefficients on `u` w.r.t. `s i`,
then `t` is `C^n` on `u`. -/
/-
**IsLocalFrameOn.contMDiffOn_of_coeff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`
。
形式化陈述：contMDiffOn_of_coeff [FiniteDimensional 𝕜 F] (h : forall i, CMDiff[u] n ((
LinearMap.piApply (hs.coeff i)) t)) : CMDiff[u] n (T% t)
参数：h : forall i, CMDiff[u] n ((LinearMap.piApply (hs.coeff i)) t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContMDiffOn.smul_section`：ContMDiffOn.smul_section (hf : CMDiff[u] n f) 
(hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (f • s))
· 使用定理 `IsLocalFrameOn.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用引理 `ContMDiffOn.sum_section`：ContMDiffOn.sum_section {s : Finset ι} (hs : fo
rall i in s, CMDiff[u] n (T% (t i ·))) : CMDiff[u] n (T% (fun x => (∑ i in s, (t
 i x))))
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalFrameOn.coeff_sum_eq`：coeff_sum_eq [Fintype ι] (hs : IsLocalFrame
On I F n s u) (t : Π x : M, V x) (hx : x in u) : t x = ∑ i, hs.coeff i x (t x) •
 (s i x)

--- 原说明 ---
Given a local frame `s i ` on `u`, if a section `t` has `C^k` coefficients on `u
` w.r.t. `s i`,
then `t` is `C^n` on `u`.
-/
lemma contMDiffOn_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, CMDiff[u] n ((LinearMap.piApply (hs.coeff i)) t)) :
    CMDiff[u] n (T% t) := by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : CMDiff[u] n (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section (hs.contMDiffOn i)
  have almost : CMDiff[u] n (T% (fun x ↦ ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) :=
    .sum_section fun i _ ↦ this i
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

/-- Given a local frame `s i` on a neighbourhood `u` of `x`,
if a section `t` has `C^k` coefficients at `x` w.r.t. `s i`, then `t` is `C^n` at `x`. -/
/-
**IsLocalFrameOn.contMDiffAt_of_coeff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFrameOn`
。
形式化陈述：contMDiffAt_of_coeff [FiniteDimensional 𝕜 F] (h : forall i, CMDiffAt n ((L
inearMap.piApply (hs.coeff i)) t) x) (hu : u in 𝓝 x) : CMDiffAt n (T% t) x
参数：h : forall i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x；hu : u in 𝓝 x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用引理 `ContMDiffAt.sum_section`：ContMDiffAt.sum_section {s : Finset ι} (hs : fo
rall i in s, CMDiffAt n (T% (t i ·)) x₀) : CMDiffAt n (T% (fun x => (∑ i in s, (
t i x)))) x₀
· 使用引理 `ContMDiffAt.smul_section`：ContMDiffAt.smul_section (hf : CMDiffAt n f x₀
) (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (f • s)) x₀
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `IsLocalFrameOn.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `IsLocalFrameOn.eventually_eq_sum_coeff_smul`：eventually_eq_sum_coeff_smu
l [Fintype ι] (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hu'' : u in 𝓝 
x) : forallᶠ x' in 𝓝 x, t x' = ∑ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Given a local frame `s i` on a neighbourhood `u` of `x`,
if a section `t` has `C^k` coefficients at `x` w.r.t. `s i`, then `t` is `C^n` a
t `x`.
-/
lemma contMDiffAt_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x) (hu : u ∈ 𝓝 x) :
    CMDiffAt n (T% t) x := by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : CMDiffAt n (T% (fun x ↦ ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) x :=
    .sum_section (fun i _ ↦ (h i).smul_section <| (hs.contMDiffOn i).contMDiffAt hu)
  exact almost.congr_of_eventuallyEq <| (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/-- Given a local frame `s i` on an open set `u` containing `x`, if a section `t` has `C^k`
coefficients at `x ∈ u` w.r.t. `s i`, then `t` is `C^n` at `x`. -/
/-
**IsLocalFrameOn.contMDiffAt_of_coeff_aux** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFram
eOn`。
形式化陈述：contMDiffAt_of_coeff_aux [FiniteDimensional 𝕜 F] (h : forall i, CMDiffAt n
 ((LinearMap.piApply (hs.coeff i)) t) x) (hu : IsOpen u) (hx : x in u) : CMDiffA
t n (T% t) x
参数：h : forall i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x；hu : IsOpen u
；hx : x in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `IsLocalFrameOn.contMDiffAt_of_coeff`：contMDiffAt_of_coeff [FiniteDimensi
onal 𝕜 F] (h : forall i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x) (hu 
: u in 𝓝 x) : CMDiffAt n …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
Given a local frame `s i` on an open set `u` containing `x`, if a section `t` ha
s `C^k`
coefficients at `x ∈ u` w.r.t. `s i`, then `t` is `C^n` at `x`.
-/
lemma contMDiffAt_of_coeff_aux [FiniteDimensional 𝕜 F]
    (h : ∀ i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x)
    (hu : IsOpen u) (hx : x ∈ u) : CMDiffAt n (T% t) x := by
  have := fintypeOfFiniteDimensional hs hx
  exact hs.contMDiffAt_of_coeff h (hu.mem_nhds hx)

section

variable (hs : IsLocalFrameOn I F 1 s u)

/-- Given a local frame `s i ` on `u`, if a section `t` has differentiable coefficients on `u`
w.r.t. `s i`, then `t` is differentiable on `u`. -/
/-
**IsLocalFrameOn.mdifferentiableOn_of_coeff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFr
ameOn`。
形式化陈述：mdifferentiableOn_of_coeff [FiniteDimensional 𝕜 F] (h : forall i, MDiff[u]
 ((LinearMap.piApply (hs.coeff i)) t)) : MDiff[u] (T% t)
参数：h : forall i, MDiff[u] ((LinearMap.piApply (hs.coeff i)) t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MDifferentiableOn.smul_section`：MDifferentiableOn.smul_section (hf : MDi
ff[u] f) (hs : MDiff[u] (T% s)) : MDiff[u] (T% (f • s))
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用定理 `IsLocalFrameOn.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `MDifferentiableOn.sum_section`：MDifferentiableOn.sum_section {ι : Type*}
 {s : Finset ι} {t : ι -> (x : B) -> E x} (hs : forall i in s, MDiff[u] (T% (t i
 ·))) : MDiff[u] (T…
· 使用定理 `MDifferentiableOn.congr`：MDifferentiableOn.congr (h : MDiff[s] f) (h₁ : 
forall y in s, f₁ y = f y) : MDiff[s] f₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalFrameOn.coeff_sum_eq`：coeff_sum_eq [Fintype ι] (hs : IsLocalFrame
On I F n s u) (t : Π x : M, V x) (hx : x in u) : t x = ∑ i, hs.coeff i x (t x) •
 (s i x)

--- 原说明 ---
Given a local frame `s i ` on `u`, if a section `t` has differentiable coefficie
nts on `u`
w.r.t. `s i`, then `t` is differentiable on `u`.
-/
lemma mdifferentiableOn_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, MDiff[u] ((LinearMap.piApply (hs.coeff i)) t)) :
    MDiff[u] (T% t) := by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : MDiff[u] (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero)
  have almost : MDiff[u] (T% (fun x ↦ ∑ i, hs.coeff i x (t x) • s i x)) :=
    .sum_section (fun i _ _ hx ↦ this i _ hx)
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

/-- Given a local frame `s i` on a neighbourhood `u` of `x`, if a section `t` has differentiable
coefficients at `x` w.r.t. `s i`, then `t` is differentiable at `x`. -/
/-
**IsLocalFrameOn.mdifferentiableAt_of_coeff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalFr
ameOn`。
形式化陈述：mdifferentiableAt_of_coeff [FiniteDimensional 𝕜 F] (h : forall i, MDiffAt 
((LinearMap.piApply (hs.coeff i)) t) x) (hu : u in 𝓝 x) : MDiffAt (T% t) x
参数：h : forall i, MDiffAt ((LinearMap.piApply (hs.coeff i)) t) x；hu : u in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用引理 `MDifferentiableAt.sum_section`：MDifferentiableAt.sum_section {ι : Type*}
 {s : Finset ι} {t : ι -> (x : B) -> E x} {x₀ : B} (hs : forall i in s, MDiffAt 
(T% (t i ·)) x₀) : …
· 使用引理 `MDifferentiableAt.smul_section`：MDifferentiableAt.smul_section (hf : MDi
ffAt f x₀) (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (f • s)) x₀
· 使用定理 `MDifferentiableOn.mdifferentiableAt`：MDifferentiableOn.mdifferentiableAt
 (h : MDiff[s] f) (hx : s in 𝓝 x) : MDiffAt f x
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用定理 `IsLocalFrameOn.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MDifferentiableAt.congr_of_eventuallyEq`：MDifferentiableAt.congr_of_even
tuallyEq (h : MDiffAt f x) (hL : f₁ =ᶠ[𝓝 x] f) : MDiffAt f₁ x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `IsLocalFrameOn.eventually_eq_sum_coeff_smul`：eventually_eq_sum_coeff_smu
l [Fintype ι] (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hu'' : u in 𝓝 
x) : forallᶠ x' in 𝓝 x, t x' = ∑ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Given a local frame `s i` on a neighbourhood `u` of `x`, if a section `t` has di
fferentiable
coefficients at `x` w.r.t. `s i`, then `t` is differentiable at `x`.
-/
lemma mdifferentiableAt_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, MDiffAt ((LinearMap.piApply (hs.coeff i)) t) x) (hu : u ∈ 𝓝 x) :
    MDiffAt (T% t) x := by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : MDiffAt (T% (fun x ↦ ∑ i, hs.coeff i x (t x) • s i x)) x :=
    .sum_section (fun i _ ↦ (h i).smul_section <|
      ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero).mdifferentiableAt hu)
  exact almost.congr_of_eventuallyEq <| (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/-- Given a local frame `s i` on open set `u` containing `x`, if a section `t`
has differentiable coefficients at `x ∈ u` w.r.t. `s i`, then `t` is differentiable at `x`. -/
/-
**IsLocalFrameOn.mdifferentiableAt_of_coeff_aux** 是 Mathlib 中的一个引理，位于命名空间 `IsLoc
alFrameOn`。
形式化陈述：mdifferentiableAt_of_coeff_aux [FiniteDimensional 𝕜 F] (h : forall i, MDif
fAt ((LinearMap.piApply (hs.coeff i)) t) x) (hu : IsOpen u) (hx : x in u) : MDif
fAt (T% t) x
参数：h : forall i, MDiffAt ((LinearMap.piApply (hs.coeff i)) t) x；hu : IsOpen u；hx
 : x in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `IsLocalFrameOn.mdifferentiableAt_of_coeff`：mdifferentiableAt_of_coeff [F
initeDimensional 𝕜 F] (h : forall i, MDiffAt ((LinearMap.piApply (hs.coeff i)) t
) x) (hu : u in 𝓝 x) : MDiffAt …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
Given a local frame `s i` on open set `u` containing `x`, if a section `t`
has differentiable coefficients at `x ∈ u` w.r.t. `s i`, then `t` is differentia
ble at `x`.
-/
lemma mdifferentiableAt_of_coeff_aux [FiniteDimensional 𝕜 F]
    (h : ∀ i, MDiffAt ((LinearMap.piApply (hs.coeff i)) t) x)
    (hu : IsOpen u) (hx : x ∈ u) : MDiffAt (T% t) x :=
  hs.mdifferentiableAt_of_coeff h (hu.mem_nhds hx)

end

end IsLocalFrameOn

end IsLocalFrame

namespace Bundle.Trivialization

variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I] {ι : Type*} {x : M}
  (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
  (b : Basis ι 𝕜 F)

/-- Given a compatible local trivialisation `e` of `V` and a basis `b` of the model fiber `F`,
return the corresponding basis of `V x`. -/
/-
**Bundle.Trivialization.basisAt** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization
`。
形式化陈述：basisAt (hx : x in e.baseSet) : Basis ι 𝕜 (V x)
参数：hx : x in e.baseSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a compatible local trivialisation `e` of `V` and a basis `b` of the model 
fiber `F`,
return the corresponding basis of `V x`.
-/
def basisAt (hx : x ∈ e.baseSet) : Basis ι 𝕜 (V x) :=
  b.map (e.linearEquivAt (R := 𝕜) x hx).symm

open scoped Classical in
/-- The local frame on `V` induced by a compatible local trivialization `e` of `V` and a basis
`b` of the model fiber `F`. Use `e.localFrame b i` to access the `i`-th section in that frame.

If `x` is outside of `e.baseSet`, this returns the junk value 0. -/
/-
**Bundle.Trivialization.localFrame** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializat
ion`。
形式化陈述：localFrame : ι -> (x : M) -> V x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The local frame on `V` induced by a compatible local trivialization `e` of `V` a
nd a basis
`b` of the model fiber `F`. Use `e.localFrame b i` to access the `i`-th section 
in that frame.

If `x` is outside of `e.baseSet`, this returns the junk value 0.
-/
def localFrame : ι → (x : M) → V x :=
  fun i x ↦ if hx : x ∈ e.baseSet then e.basisAt b hx i else 0

@[simp]
/-
**Bundle.Trivialization.localFrame_apply_of_mem_baseSet** 是 Mathlib 中的一个引理，位于命名空
间 `Bundle.Trivialization`。
形式化陈述：localFrame_apply_of_mem_baseSet {i : ι} (hx : x in e.baseSet) : e.localFra
me b i x = e.basisAt b hx i
参数：hx : x in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma localFrame_apply_of_mem_baseSet {i : ι} (hx : x ∈ e.baseSet) :
    e.localFrame b i x = e.basisAt b hx i := by
  simp [localFrame, hx]
/-
**Bundle.Trivialization.localFrame_apply_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Bu
ndle.Trivialization`。
形式化陈述：localFrame_apply_of_notMem {i : ι} (hx : x ∉ e.baseSet) : e.localFrame b i
 x = 0
参数：hx : x ∉ e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma localFrame_apply_of_notMem {i : ι} (hx : x ∉ e.baseSet) : e.localFrame b i x = 0 := by
  simp [localFrame, hx]

/-- Each local frame `{sᵢ} ∈ Γ(E)` of a `C^k` vector bundle, defined by a local trivialisation `e`,
is `C^k` on `e.baseSet`. -/
/-
**Bundle.Trivialization.contMDiffOn_localFrame_baseSet** 是 Mathlib 中的一个引理，位于命名空间
 `Bundle.Trivialization`。
形式化陈述：contMDiffOn_localFrame_baseSet (i : ι) : CMDiff[e.baseSet] n (T% (e.localF
rame b i))
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.contMDiffOn_section_baseSet_iff`：contMDiffOn_secti
on_baseSet_iff {s : forall x, E x} (e : Trivialization F (Bundle.TotalSpace.proj
 : Bundle.TotalSpace F E -> B)) [MemTrivial…
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `contMDiffOn_const`：contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => 
c) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用引理 `Bundle.Trivialization.localFrame_apply_of_mem_baseSet`：localFrame_apply_
of_mem_baseSet {i : ι} (hx : x in e.baseSet) : e.localFrame b i x = e.basisAt b 
hx i
· 使用定理 `Bundle.Trivialization.apply_mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E 
: B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSpace (B…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Each local frame `{sᵢ} ∈ Γ(E)` of a `C^k` vector bundle, defined by a local triv
ialisation `e`,
is `C^k` on `e.baseSet`.
-/
lemma contMDiffOn_localFrame_baseSet (i : ι) : CMDiff[e.baseSet] n (T% (e.localFrame b i)) := by
  rw [e.contMDiffOn_section_baseSet_iff]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [hy, basisAt]

variable (I) in
/-- `b.localFrame e i` is indeed a local frame on `e.baseSet` -/
/-
**Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet** 是 Mathlib 中的一个引理，位于命
名空间 `Bundle.Trivialization`。
形式化陈述：isLocalFrameOn_localFrame_baseSet : IsLocalFrameOn I F n (e.localFrame b) 
e.baseSet where contMDiffOn i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Bundle.Trivialization.localFrame_apply_of_mem_baseSet`：localFrame_apply_
of_mem_baseSet {i : ι} (hx : x in e.baseSet) : e.localFrame b i x = e.basisAt b 
hx i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用引理 `Bundle.Trivialization.contMDiffOn_localFrame_baseSet`：contMDiffOn_localF
rame_baseSet (i : ι) : CMDiff[e.baseSet] n (T% (e.localFrame b i))

--- 原说明 ---
`b.localFrame e i` is indeed a local frame on `e.baseSet`
-/
lemma isLocalFrameOn_localFrame_baseSet : IsLocalFrameOn I F n (e.localFrame b) e.baseSet where
  contMDiffOn i := e.contMDiffOn_localFrame_baseSet _ b i
  linearIndependent := by
    intro x hx
    convert! (e.basisAt b hx).linearIndependent
    simp [hx, basisAt]
  generating := by
    intro x hx
    convert! (e.basisAt b hx).span_eq.ge
    simp [hx, basisAt]
/-
**Bundle.Trivialization._root_.contMDiffAt_localFrame_of_mem** 是 Mathlib 中的一个引理，
位于命名空间 `Bundle.Trivialization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.contMDiffAt_localFrame_of_mem (i : ι) (hx : x ∈ e.baseSet) :
    CMDiffAt n (T% (e.localFrame b i)) x :=
  (e.isLocalFrameOn_localFrame_baseSet I n b).contMDiffAt e.open_baseSet hx _

variable [ContMDiffVectorBundle 1 F V I]

variable (I) in
/-- Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i`.

If x is outside of `e.baseSet`, this returns the junk value 0. -/
/-
**Bundle.Trivialization.localFrameCoeff** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：localFrameCoeff (i : ι) : Π x : M, (V x ->ₗ[𝕜] 𝕜)
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i`.

If x is outside of `e.baseSet`, this returns the junk value 0.
-/
def localFrameCoeff (i : ι) : Π x : M, (V x →ₗ[𝕜] 𝕜) :=
  (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff i

@[deprecated (since := "2026-07-26")] alias localFrame_coeff := localFrameCoeff

variable {e b}
variable {x x' : M}

variable (e b) in
@[simp]
/-
**Bundle.Trivialization.localFrameCoeff_apply_of_notMem_baseSet** 是 Mathlib 中的一个
引理，位于命名空间 `Bundle.Trivialization`。
形式化陈述：localFrameCoeff_apply_of_notMem_baseSet (hx : x ∉ e.baseSet) (i : ι) : e.l
ocalFrameCoeff I b i x = 0
参数：hx : x ∉ e.baseSet；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalFrameOn.coeff_apply_of_notMem`：coeff_apply_of_notMem (hs : IsLoca
lFrameOn I F n s u) (hx : x ∉ u) (i : ι) : hs.coeff i x = 0
· 使用引理 `Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet`：isLocalFrameOn_
localFrame_baseSet : IsLocalFrameOn I F n (e.localFrame b) e.baseSet where contM
DiffOn i
-/
lemma localFrameCoeff_apply_of_notMem_baseSet (hx : x ∉ e.baseSet) (i : ι) :
    e.localFrameCoeff I b i x = 0 := by
  simpa [localFrameCoeff] using
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff_apply_of_notMem hx i

@[deprecated (since := "2026-07-26")]
alias localFrame_coeff_apply_of_notMem_baseSet := localFrameCoeff_apply_of_notMem_baseSet

variable (e b) in
@[simp]
/-
**Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet** 是 Mathlib 中的一个引理，
位于命名空间 `Bundle.Trivialization`。
形式化陈述：localFrameCoeff_apply_of_mem_baseSet (hx : x in e.baseSet) (s : Π x : M, V
 x) (i : ι) : (localFrameCoeff I e b i x) (s x) = (e.basisAt b hx).repr (s x) i
参数：hx : x in e.baseSet；s : Π x : M, V x；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet`：isLocalFrameOn_
localFrame_baseSet : IsLocalFrameOn I F n (e.localFrame b) e.baseSet where contM
DiffOn i
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalFrameOn.linearIndependent`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `IsLocalFrameOn.generating`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.mk.congr_simp`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_
5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 {v v_1 : ι → M}…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
-/
lemma localFrameCoeff_apply_of_mem_baseSet (hx : x ∈ e.baseSet) (s : Π x : M, V x) (i : ι) :
    (localFrameCoeff I e b i x) (s x) = (e.basisAt b hx).repr (s x) i := by
  have he := e.isLocalFrameOn_localFrame_baseSet I 1 b
  have hbasis : e.basisAt b hx = he.toBasisAt hx := by
    ext j
    simp [IsLocalFrameOn.toBasisAt, localFrame, basisAt, hx]
  simp [localFrameCoeff, IsLocalFrameOn.coeff, hx, hbasis]

@[deprecated (since := "2026-07-26")]
alias localFrame_coeff_apply_of_mem_baseSet := localFrameCoeff_apply_of_mem_baseSet

variable {s s' : Π x : M, V x}
/-
**Bundle.Trivialization.eq_sum_localFrameCoeff_smul** 是 Mathlib 中的一个引理，位于命名空间 `B
undle.Trivialization`。
形式化陈述：eq_sum_localFrameCoeff_smul [Fintype ι] (hx : x' in e.baseSet) : s x' = ∑ 
i, e.localFrameCoeff I b i x' (s x') • e.localFrame b i x'
参数：hx : x' in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalFrameOn.coeff_sum_eq`：coeff_sum_eq [Fintype ι] (hs : IsLocalFrame
On I F n s u) (t : Π x : M, V x) (hx : x in u) : t x = ∑ i, hs.coeff i x (t x) •
 (s i x)
· 使用引理 `Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet`：isLocalFrameOn_
localFrame_baseSet : IsLocalFrameOn I F n (e.localFrame b) e.baseSet where contM
DiffOn i
-/
lemma eq_sum_localFrameCoeff_smul [Fintype ι] (hx : x' ∈ e.baseSet) :
    s x' = ∑ i, e.localFrameCoeff I b i x' (s x') • e.localFrame b i x' :=
  (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_sum_eq s hx

@[deprecated (since := "2026-07-26")]
alias eq_sum_localFrame_coeff_smul := eq_sum_localFrameCoeff_smul

variable (e b) in
/-- A local frame locally spans the space of sections for `V`: for each local trivialisation `e`
of `V` around `x`, we have
`s = ∑ i, (LinearMap.piApply (b.localFrameCoeff e i) s) • b.localFrame e i` near `x`. -/
/-
**Bundle.Trivialization.eventually_eq_localFrame_sum_coeff_smul** 是 Mathlib 中的一个
引理，位于命名空间 `Bundle.Trivialization`。
形式化陈述：eventually_eq_localFrame_sum_coeff_smul [Fintype ι] (hxe : x in e.baseSet)
 : forallᶠ x' in 𝓝 x, s x' = ∑ i, e.localFrameCoeff I b i x' (s x') • e.localFra
me b i x'
参数：hxe : x in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用引理 `Bundle.Trivialization.eq_sum_localFrameCoeff_smul`：eq_sum_localFrameCoef
f_smul [Fintype ι] (hx : x' in e.baseSet) : s x' = ∑ i, e.localFrameCoeff I b i 
x' (s x') • e.localFrame b i x'
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…

--- 原说明 ---
A local frame locally spans the space of sections for `V`: for each local trivia
lisation `e`
of `V` around `x`, we have
`s = ∑ i, (LinearMap.piApply (b.localFrameCoeff e i) s) • b.localFrame e i` near
 `x`.
-/
lemma eventually_eq_localFrame_sum_coeff_smul [Fintype ι] (hxe : x ∈ e.baseSet) :
    ∀ᶠ x' in 𝓝 x, s x' = ∑ i, e.localFrameCoeff I b i x' (s x') • e.localFrame b i x' :=
  eventually_nhds_iff.mpr ⟨e.baseSet, fun _ ↦ e.eq_sum_localFrameCoeff_smul, e.open_baseSet, hxe⟩

variable (e b) in
/-- The representation of `s` in a local frame at `x` only depends on `s` at `x`. -/
/-
**Bundle.Trivialization.localFrameCoeff_congr** 是 Mathlib 中的一个引理，位于命名空间 `Bundle.
Trivialization`。
形式化陈述：localFrameCoeff_congr {i : ι} (hss' : s x = s' x) : e.localFrameCoeff I b 
i x (s x) = e.localFrameCoeff I b i x (s' x)
参数：hss' : s x = s' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalFrameOn.coeff_congr`：coeff_congr (hs : IsLocalFrameOn I F n s u) 
(htt' : t x = t' x) (i : ι) : hs.coeff i x (t x) = hs.coeff i x (t' x)
· 使用引理 `Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet`：isLocalFrameOn_
localFrame_baseSet : IsLocalFrameOn I F n (e.localFrame b) e.baseSet where contM
DiffOn i

--- 原说明 ---
The representation of `s` in a local frame at `x` only depends on `s` at `x`.
-/
lemma localFrameCoeff_congr {i : ι} (hss' : s x = s' x) :
    e.localFrameCoeff I b i x (s x) = e.localFrameCoeff I b i x (s' x) := by
  simpa using! (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_congr hss' i

@[deprecated (since := "2026-07-26")] alias localFrame_coeff_congr := localFrameCoeff_congr

variable {n}

variable (e) in
/-- Suppose `e` is a compatible trivialisation around `x ∈ M`, and `s` a bundle section.
Then the coefficient of `s` w.r.t. the local frame induced by `b` and `e`
equals the coefficient of "`s x` read in the trivialisation `e`" for `b i`. -/
/-
**Bundle.Trivialization.localFrameCoeff_eq_coeff** 是 Mathlib 中的一个引理，位于命名空间 `Bund
le.Trivialization`。
形式化陈述：localFrameCoeff_eq_coeff (hxe : x in e.baseSet) {i : ι} : e.localFrameCoef
f I b i x (s x) = b.repr (e ((T% s) x)).2 i
参数：hxe : x in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet`：localFrameCo
eff_apply_of_mem_baseSet (hx : x in e.baseSet) (s : Π x : M, V x) (i : ι) : (loc
alFrameCoeff I e b i x) (s x) = (e.basisAt b hx)…
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Suppose `e` is a compatible trivialisation around `x ∈ M`, and `s` a bundle sect
ion.
Then the coefficient of `s` w.r.t. the local frame induced by `b` and `e`
equals the coefficient of "`s x` read in the trivialisation `e`" for `b i`.
-/
lemma localFrameCoeff_eq_coeff (hxe : x ∈ e.baseSet) {i : ι} :
    e.localFrameCoeff I b i x (s x) = b.repr (e ((T% s) x)).2 i := by
  simp [e.localFrameCoeff_apply_of_mem_baseSet b hxe, basisAt]

@[deprecated (since := "2026-07-26")] alias localFrame_coeff_eq_coeff := localFrameCoeff_eq_coeff

end Bundle.Trivialization

/-! ### Determining smoothness of a section via its local frame coefficients
We show that for finite rank bundles over a complete field, a section is smooth iff its coefficients
in a local frame induced by a local trivialisation are. In many contexts, this statement holds for
*any* local frame (e.g., for all real bundles which admit a continuous bundle metric, as is
proven in `OrthonormalFrame.lean`).
-/

variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
  {ι : Type*} (b : Basis ι 𝕜 F) {s : Π x : M, V x} {t : Set M} {k : ℕ∞ω} {x x' : M}
  [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle k F V I]

set_option backward.isDefEq.respectTransparency false in
/-- If `s` is `C^k` at `x`, so is its coefficient `b.localFrameCoeff e i` in the local frame
near `x` induced by `e` and `b` -/
/-
**contMDiffAt_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffAt_localFrameCoeff (hxe : x in e.baseSet) (hs : CMDiffAt k (T% s)
 x) (i : ι) : CMDiffAt k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x
参数：hxe : x in e.baseSet；hs : CMDiffAt k (T% s) x；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.Trivialization.contMDiffAt_section_iff`：contMDiffAt_section_iff {
s : forall x, E x} {x₀ : B} (e : Trivialization F (Bundle.TotalSpace.proj : Bund
le.TotalSpace F E -> B)) [MemTrivia…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffAt_iff_contDiffAt`：contMDiffAt_iff_contDiffAt {f : E -> E'} {x 
: E} : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.clm_apply`：ContDiffAt.clm_apply {f : E -> F ->L[𝕜] G} {g : E 
-> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun 
x => (f x)…
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
· 使用定理 `ContMDiffAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is `C^k` at `x`, so is its coefficient `b.localFrameCoeff e i` in the loc
al frame
near `x` induced by `e` and `b`
-/
lemma contMDiffAt_localFrameCoeff (hxe : x ∈ e.baseSet) (hs : CMDiffAt k (T% s) x) (i : ι) :
    CMDiffAt k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  -- step 1: on e.baseSet, we know compute the coefficient very well
  let aux := fun x ↦ b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices CMDiffAt k aux x by
    apply this.congr_of_eventuallyEq ?_
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrameCoeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is `C^k`
  have h₁ : CMDiffAt k (fun x ↦ (e ((T% s) x)).2) x := by
    simpa using (e.contMDiffAt_section_iff hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F →ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : CMDiffAt k breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
    contMDiffAt_iff_contDiffAt.mpr <| by fun_prop
  exact this.comp x h₁

@[deprecated (since := "2026-07-26")]
alias contMDiffAt_localFrame_coeff := contMDiffAt_localFrameCoeff

/-- If `s` is `C^k` on `t ⊆ e.baseSet`, so is its coefficient `b.localFrameCoeff e i`
in the local frame induced by `e` -/
/-
**contMDiffOn_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_localFrameCoeff (ht : IsOpen t) (ht' : t subseteq e.baseSet) (
hs : CMDiff[t] k (T% s)) (i : ι) : CMDiff[t] k ((LinearMap.piApply (e.localFrame
Coeff I b i)) s)
参数：ht : IsOpen t；ht' : t subseteq e.baseSet；hs : CMDiff[t] k (T% s)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `contMDiffAt_localFrameCoeff`：contMDiffAt_localFrameCoeff (hxe : x in e.b
aseSet) (hs : CMDiffAt k (T% s) x) (i : ι) : CMDiffAt k ((LinearMap.piApply (e.l
ocalFrameCoeff I …
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If `s` is `C^k` on `t ⊆ e.baseSet`, so is its coefficient `b.localFrameCoeff e i
`
in the local frame induced by `e`
-/
lemma contMDiffOn_localFrameCoeff (ht : IsOpen t) (ht' : t ⊆ e.baseSet)
    (hs : CMDiff[t] k (T% s)) (i : ι) :
    CMDiff[t] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) :=
  fun _ hx ↦ (contMDiffAt_localFrameCoeff b (ht' hx)
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_localFrame_coeff := contMDiffOn_localFrameCoeff

/-- If `s` is `C^k` on `e.baseSet`, so is its coefficient `b.localFrameCoeff e i`
in the local frame induced by `e` -/
/-
**contMDiffOn_baseSet_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_baseSet_localFrameCoeff (hs : CMDiff[e.baseSet] k (T% s)) (i :
 ι) : CMDiff[e.baseSet] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s)
参数：hs : CMDiff[e.baseSet] k (T% s)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `contMDiffOn_localFrameCoeff`：contMDiffOn_localFrameCoeff (ht : IsOpen t)
 (ht' : t subseteq e.baseSet) (hs : CMDiff[t] k (T% s)) (i : ι) : CMDiff[t] k ((
LinearMap.piApply…
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `subset_refl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] (a : α), a ⊆ a

--- 原说明 ---
If `s` is `C^k` on `e.baseSet`, so is its coefficient `b.localFrameCoeff e i`
in the local frame induced by `e`
-/
lemma contMDiffOn_baseSet_localFrameCoeff (hs : CMDiff[e.baseSet] k (T% s)) (i : ι) :
    CMDiff[e.baseSet] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) :=
  contMDiffOn_localFrameCoeff b e.open_baseSet (subset_refl _) hs _

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_baseSet_localFrame_coeff := contMDiffOn_baseSet_localFrameCoeff

/-- A section `s` of `V` is `C^k` at `x ∈ e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrameCoeff e i) s)` in a local frame near `x` is -/
/-
**contMDiffAt_iff_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_localFrameCoeff (hx : x' in e.baseSet) : CMDiffAt k (T% s)
 x' ↔ forall i, CMDiffAt k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x'
参数：hx : x' in e.baseSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `contMDiffAt_localFrameCoeff`：contMDiffAt_localFrameCoeff (hxe : x in e.b
aseSet) (hs : CMDiffAt k (T% s) x) (i : ι) : CMDiffAt k ((LinearMap.piApply (e.l
ocalFrameCoeff I …
· 使用引理 `IsLocalFrameOn.contMDiffAt_of_coeff`：contMDiffAt_of_coeff [FiniteDimensi
onal 𝕜 F] (h : forall i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x) (hu 
: u in 𝓝 x) : CMDiffAt n …
· 使用引理 `Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet`：isLocalFrameOn_
localFrame_baseSet : IsLocalFrameOn I F n (e.localFrame b) e.baseSet where contM
DiffOn i
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…

--- 原说明 ---
A section `s` of `V` is `C^k` at `x ∈ e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrameCoeff e i) s)` in a local frame ne
ar `x` is
-/
lemma contMDiffAt_iff_localFrameCoeff (hx : x' ∈ e.baseSet) :
    CMDiffAt k (T% s) x' ↔ ∀ i, CMDiffAt k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x' :=
  ⟨fun h i ↦ contMDiffAt_localFrameCoeff b hx h i,
    fun hi ↦ (e.isLocalFrameOn_localFrame_baseSet I k b).contMDiffAt_of_coeff hi
    (e.open_baseSet.mem_nhds hx)⟩

@[deprecated (since := "2026-07-26")]
alias contMDiffAt_iff_localFrame_coeff := contMDiffAt_iff_localFrameCoeff

/-- A section `s` of `V` is `C^k` on `t ⊆ e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrameCoeff e i) s)` in a local frame near `x` is -/
/-
**contMDiffOn_iff_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_iff_localFrameCoeff (ht : IsOpen t) (ht' : t subseteq e.baseSe
t) : CMDiff[t] k (T% s) ↔ forall i, CMDiff[t] k ((LinearMap.piApply (e.localFram
eCoeff I b i)) s)
参数：ht : IsOpen t；ht' : t subseteq e.baseSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `contMDiffOn_localFrameCoeff`：contMDiffOn_localFrameCoeff (ht : IsOpen t)
 (ht' : t subseteq e.baseSet) (hs : CMDiff[t] k (T% s)) (i : ι) : CMDiff[t] k ((
LinearMap.piApply…
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `contMDiffAt_iff_localFrameCoeff`：contMDiffAt_iff_localFrameCoeff (hx : x
' in e.baseSet) : CMDiffAt k (T% s) x' ↔ forall i, CMDiffAt k ((LinearMap.piAppl
y (e.localFrameCoeff …
· 使用定理 `ContMDiffWithinAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
A section `s` of `V` is `C^k` on `t ⊆ e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrameCoeff e i) s)` in a local frame ne
ar `x` is
-/
lemma contMDiffOn_iff_localFrameCoeff (ht : IsOpen t) (ht' : t ⊆ e.baseSet) :
    CMDiff[t] k (T% s) ↔ ∀ i, CMDiff[t] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) := by
  refine ⟨fun h i ↦ contMDiffOn_localFrameCoeff b ht ht' h _, fun h x hx ↦ ?_⟩
  exact (contMDiffAt_iff_localFrameCoeff b (ht' hx)).mpr
    (fun i ↦ (h i x hx).contMDiffAt (ht.mem_nhds hx)) |>.contMDiffWithinAt

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_iff_localFrame_coeff := contMDiffOn_iff_localFrameCoeff

/-- A section `s` of `V` is `C^k` on a trivialisation domain `e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrameCoeff e i) s)` in a local frame near `x` is -/
/-
**contMDiffOn_baseSet_iff_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_baseSet_iff_localFrameCoeff : CMDiff[e.baseSet] k (T% s) ↔ for
all i, CMDiff[e.baseSet] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `contMDiffOn_iff_localFrameCoeff`：contMDiffOn_iff_localFrameCoeff (ht : I
sOpen t) (ht' : t subseteq e.baseSet) : CMDiff[t] k (T% s) ↔ forall i, CMDiff[t]
 k ((LinearMap.piAppl…
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `subset_refl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] (a : α), a ⊆ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A section `s` of `V` is `C^k` on a trivialisation domain `e.baseSet` iff each of
 its
coefficients `(LinearMap.piApply (b.localFrameCoeff e i) s)` in a local frame ne
ar `x` is
-/
lemma contMDiffOn_baseSet_iff_localFrameCoeff :
    CMDiff[e.baseSet] k (T% s) ↔
      ∀ i, CMDiff[e.baseSet] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) := by
  rw [contMDiffOn_iff_localFrameCoeff b e.open_baseSet (subset_refl _)]

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_baseSet_iff_localFrame_coeff := contMDiffOn_baseSet_iff_localFrameCoeff

-- Differentiability of a section can be checked in terms of its local frame coefficients
section MDifferentiable

set_option backward.isDefEq.respectTransparency false in
/-- If `s` is differentiable at `x`, so is its coefficient `b.localFrameCoeff e i` in the local
frame near `x` induced by `e` and `b` -/
/-
**mdifferentiableAt_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_localFrameCoeff (hxe : x in e.baseSet) (hs : MDiffAt (T%
 s) x) (i : ι) : MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x
参数：hxe : x in e.baseSet；hs : MDiffAt (T% s) x；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.Trivialization.mdifferentiableAt_section_iff`：mdifferentiableAt_s
ection_iff (e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)) [MemTr
ivializationAtlas e] (s : Π b : B, E b) {…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mdifferentiableAt_iff_differentiableAt`：mdifferentiableAt_iff_differenti
ableAt : MDiffAt f x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `ContinuousLinearMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
· 使用定理 `MDifferentiableAt.congr_of_eventuallyEq`：MDifferentiableAt.congr_of_even
tuallyEq (h : MDiffAt f x) (hL : f₁ =ᶠ[𝓝 x] f) : MDiffAt f₁ x
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is differentiable at `x`, so is its coefficient `b.localFrameCoeff e i` i
n the local
frame near `x` induced by `e` and `b`
-/
lemma mdifferentiableAt_localFrameCoeff
    (hxe : x ∈ e.baseSet) (hs : MDiffAt (T% s) x) (i : ι) :
    MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  -- step 1: on `e.baseSet`, we know the coefficient very well
  let aux := fun x ↦ b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices MDiffAt aux x by
    apply this.congr_of_eventuallyEq
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrameCoeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is differentiable
  have h₁ : MDiffAt (fun x ↦ (e ((T% s) x)).2) x := by
    simpa using (e.mdifferentiableAt_section_iff I s hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F →ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜) breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
    mdifferentiableAt_iff_differentiableAt.mpr <| by fun_prop
  exact this.comp x h₁

@[deprecated (since := "2026-07-26")]
alias mdifferentiableAt_localFrame_coeff := mdifferentiableAt_localFrameCoeff

/-- If `s` is differentiable on `t ⊆ e.baseSet`, so is its coefficient `b.localFrameCoeff e i`
in the local frame induced by `e` -/
/-
**mdifferentiableOn_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_localFrameCoeff (ht : IsOpen t) (ht' : t subseteq e.base
Set) (hs : MDiff[t] (T% s)) (i : ι) : MDiff[t] ((LinearMap.piApply (e.localFrame
Coeff I b i)) s)
参数：ht : IsOpen t；ht' : t subseteq e.baseSet；hs : MDiff[t] (T% s)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `mdifferentiableAt_localFrameCoeff`：mdifferentiableAt_localFrameCoeff (hx
e : x in e.baseSet) (hs : MDiffAt (T% s) x) (i : ι) : MDiffAt ((LinearMap.piAppl
y (e.localFrameCoeff I …
· 使用定理 `MDifferentiableOn.mdifferentiableAt`：MDifferentiableOn.mdifferentiableAt
 (h : MDiff[s] f) (hx : s in 𝓝 x) : MDiffAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If `s` is differentiable on `t ⊆ e.baseSet`, so is its coefficient `b.localFrame
Coeff e i`
in the local frame induced by `e`
-/
lemma mdifferentiableOn_localFrameCoeff (ht : IsOpen t) (ht' : t ⊆ e.baseSet)
    (hs : MDiff[t] (T% s)) (i : ι) : MDiff[t] ((LinearMap.piApply (e.localFrameCoeff I b i)) s) :=
  fun _ hx ↦ (mdifferentiableAt_localFrameCoeff b (ht' hx)
    (hs.mdifferentiableAt (ht.mem_nhds hx)) i).mdifferentiableWithinAt

@[deprecated (since := "2026-07-26")]
alias mdifferentiableOn_localFrame_coeff := mdifferentiableOn_localFrameCoeff

/-- If `s` is differentiable on `e.baseSet`, so is its coefficient `b.localFrameCoeff e i` in the
local frame induced by `e` -/
/-
**mdifferentiableOn_baseSet_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_baseSet_localFrameCoeff (hs : MDiff[e.baseSet] (T% s)) (
i : ι) : MDiff[e.baseSet] ((LinearMap.piApply (e.localFrameCoeff I b i)) s)
参数：hs : MDiff[e.baseSet] (T% s)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableOn_localFrameCoeff`：mdifferentiableOn_localFrameCoeff (ht
 : IsOpen t) (ht' : t subseteq e.baseSet) (hs : MDiff[t] (T% s)) (i : ι) : MDiff
[t] ((LinearMap.piApply…
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `subset_refl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] (a : α), a ⊆ a

--- 原说明 ---
If `s` is differentiable on `e.baseSet`, so is its coefficient `b.localFrameCoef
f e i` in the
local frame induced by `e`
-/
lemma mdifferentiableOn_baseSet_localFrameCoeff (hs : MDiff[e.baseSet] (T% s)) (i : ι) :
    MDiff[e.baseSet] ((LinearMap.piApply (e.localFrameCoeff I b i)) s) :=
  mdifferentiableOn_localFrameCoeff b e.open_baseSet (subset_refl _) hs _

@[deprecated (since := "2026-07-26")]
alias mdifferentiableOn_baseSet_localFrame_coeff := mdifferentiableOn_baseSet_localFrameCoeff

/-- A section `s` of `V` is differentiable at `x ∈ e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrameCoeff e i) s)` in a local frame near `x` is -/
/-
**mdifferentiableAt_iff_localFrameCoeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_iff_localFrameCoeff (hx : x' in e.baseSet) : MDiffAt (T%
 s) x' ↔ forall i, MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x'
参数：hx : x' in e.baseSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `mdifferentiableAt_localFrameCoeff`：mdifferentiableAt_localFrameCoeff (hx
e : x in e.baseSet) (hs : MDiffAt (T% s) x) (i : ι) : MDiffAt ((LinearMap.piAppl
y (e.localFrameCoeff I …
· 使用引理 `IsLocalFrameOn.mdifferentiableAt_of_coeff_aux`：mdifferentiableAt_of_coef
f_aux [FiniteDimensional 𝕜 F] (h : forall i, MDiffAt ((LinearMap.piApply (hs.coe
ff i)) t) x) (hu : IsOpen u) (hx : …
· 使用引理 `Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet`：isLocalFrameOn_
localFrame_baseSet : IsLocalFrameOn I F n (e.localFrame b) e.baseSet where contM
DiffOn i
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…

--- 原说明 ---
A section `s` of `V` is differentiable at `x ∈ e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrameCoeff e i) s)` in a local frame ne
ar `x` is
-/
lemma mdifferentiableAt_iff_localFrameCoeff (hx : x' ∈ e.baseSet) :
    MDiffAt (T% s) x' ↔ ∀ i, MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x' :=
  ⟨fun h i ↦ mdifferentiableAt_localFrameCoeff b hx h i, fun hi ↦
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).mdifferentiableAt_of_coeff_aux hi e.open_baseSet hx⟩

@[deprecated (since := "2026-07-26")]
alias mdifferentiableAt_iff_localFrame_coeff := mdifferentiableAt_iff_localFrameCoeff

end MDifferentiable

end

