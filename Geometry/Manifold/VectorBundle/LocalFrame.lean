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
  (n : Nat∞ω)
  {V : M -> Type*} [TopologicalSpace (TotalSpace F V)]
  [forall x, AddCommGroup (V x)] [forall x, Module 𝕜 (V x)]
  [forall x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

noncomputable section

section IsLocalFrame

variable {ι : Type*} {s s' : ι -> (x : M) -> V x} {u u' : Set M} {x : M} {n : Nat∞ω}

variable (I F n) in
/--
Definition of `IsLocalFrameOn` / `IsLocalFrameOn` 的定义

English:
structure IsLocalFrameOn
  parameters: (s : ι -> (x : M) -> V x) (u : Set M)
  axioms and operations (3):
    - linearIndependent({x : M} (hx : x in u)) : LinearIndependent 𝕜 (s · x)
    - generating({x : M} (hx : x in u)) : ⊤ <= Submodule.span 𝕜 (Set.range (s · x))
    - contMDiffOn((i : ι)) : CMDiff[u] n (T% (s i))

中文:
结构 是LocalFrameOn
  参数: (s : ι -> (x : M) -> V x) (u : 集合 M)
  公理与运算 (3 个):
    - linearIndependent({x : M} (hx : x in u)) : LinearIndependent 𝕜 (s · x)
    - generating({x : M} (hx : x in u)) : ⊤ <= 子模.span 𝕜 (集合.range (s · x))
    - contMDiffOn((i : ι)) : CMDiff[u] n (T% (s i))
-/
structure IsLocalFrameOn (s : ι -> (x : M) -> V x) (u : Set M) where
  linearIndependent {x : M} (hx : x in u) : LinearIndependent 𝕜 (s · x)
  generating {x : M} (hx : x in u) : ⊤ <= Submodule.span 𝕜 (Set.range (s · x))
  contMDiffOn (i : ι) : CMDiff[u] n (T% (s i))

namespace IsLocalFrameOn

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: (hs : IsLocalFrameOn I F n s u) (hs' : forall i, forall x, x in u -> s i x = s' i x)
  proof: by
    intro x hx
    have := hs.linearIndependent hx
    simp_all
  generating := by
    intro x hx
    have := hs.generating hx
    simp_all
  contMDiffOn i := (hs.contMDiffOn i).congr (by simp +contextual [hs'])

中文:
引理 congr
  条件: (hs : 是LocalFrameOn I F n s u) (hs' : 对任意 i, 对任意 x, x in u -> s i x = s' i x)
  证明: by
    intro x hx
    have := hs.linearIndependent hx
    simp_all
  generating := by
    intro x hx
    have := hs.generating hx
    simp_all
  contMDiffOn i := (hs.contMDiffOn i).congr (by simp +contextual [hs'])

Depends on / 依赖: contMDiffOn, contextual, generating, hs.contMDiffOn, hs.generating, hs.linearIndependent, linearIndependent
-/
lemma congr (hs : IsLocalFrameOn I F n s u) (hs' : forall i, forall x, x in u -> s i x = s' i x) :
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

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: (hs : IsLocalFrameOn I F n s u) (hu'u : u' subseteq u)
  statement: IsLocalFrameOn I F n s u' where
  proof: by
    intro x hx
    exact hs.linearIndependent (hu'u hx)
  generating := by
    intro x hx
    exact hs.generating (hu'u hx)
  contMDiffOn i := (hs.contMDiffOn i).mono hu'u

中文:
引理 mono
  条件: (hs : 是LocalFrameOn I F n s u) (hu'u : u' subseteq u)
  结论: 是LocalFrameOn I F n s u' where
  证明: by
    intro x hx
    exact hs.linearIndependent (hu'u hx)
  generating := by
    intro x hx
    exact hs.generating (hu'u hx)
  contMDiffOn i := (hs.contMDiffOn i).mono hu'u

Depends on / 依赖: contMDiffOn, generating, hs.contMDiffOn, hs.generating, hs.linearIndependent, linearIndependent
-/
lemma mono (hs : IsLocalFrameOn I F n s u) (hu'u : u' subseteq u) : IsLocalFrameOn I F n s u' where
  linearIndependent := by
    intro x hx
    exact hs.linearIndependent (hu'u hx)
  generating := by
    intro x hx
    exact hs.generating (hu'u hx)
  contMDiffOn i := (hs.contMDiffOn i).mono hu'u

/--
lemma `contMDiffAt` / 引理 `contMDiffAt`

English:
lemma contMDiffAt
  given: (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hx : x in u) (i : ι)
  proof: (hs.contMDiffOn i).contMDiffAt hu.mem_nhds hx

中文:
引理 contMDiffAt
  条件: (hs : 是LocalFrameOn I F n s u) (hu : 是开集 u) (hx : x in u) (i : ι)
  证明: (hs.contMDiffOn i).contMDiffAt hu.mem_nhds hx

Depends on / 依赖: contMDiffAt, contMDiffOn, hs.contMDiffOn, hu.mem_nhds, mem_nhds
-/
lemma contMDiffAt (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hx : x in u) (i : ι) :
    CMDiffAt n (T% (s i)) x :=
(hs.contMDiffOn i).contMDiffAt hu.mem_nhds hx

/--
Definition of `toBasisAt` / `toBasisAt` 的定义

English:
definition toBasisAt
  signature: (hs : IsLocalFrameOn I F n s u) (hx : x in u)
  body: Basis.mk (hs.linearIndependent hx) (hs.generating hx)

@[simp]

中文:
定义 toBasisAt
  签名: (hs : 是LocalFrameOn I F n s u) (hx : x in u)
  定义体: Basis.mk (hs.linearIndependent hx) (hs.generating hx)

@[simp]

Depends on / 依赖: Basis.mk, generating, hs.generating, hs.linearIndependent, linearIndependent
-/
def toBasisAt (hs : IsLocalFrameOn I F n s u) (hx : x in u) : Basis ι 𝕜 (V x) :=
  Basis.mk (hs.linearIndependent hx) (hs.generating hx)

@[simp]
/--
lemma `toBasisAt_coe` / 引理 `toBasisAt_coe`

English:
lemma toBasisAt_coe
  given: (hs : IsLocalFrameOn I F n s u) (hx : x in u) (i : ι)
  proof: by
  simpa only [toBasisAt] using Basis.mk_apply (hs.linearIndependent hx) (hs.generating hx) i

中文:
引理 toBasisAt_coe
  条件: (hs : 是LocalFrameOn I F n s u) (hx : x in u) (i : ι)
  证明: by
  simpa only [toBasisAt] using Basis.mk_apply (hs.linearIndependent hx) (hs.generating hx) i

Depends on / 依赖: Basis.mk_apply, generating, hs.generating, hs.linearIndependent, linearIndependent, mk_apply, toBasisAt
-/
lemma toBasisAt_coe (hs : IsLocalFrameOn I F n s u) (hx : x in u) (i : ι) :
    toBasisAt hs hx i = s i x := by
  simpa only [toBasisAt] using Basis.mk_apply (hs.linearIndependent hx) (hs.generating hx) i

/-- If `{sᵢ}` is a local frame on a vector bundle, `F` being finite-dimensional implies the
indexing set being finite. -/
@[instance_reducible]
/--
Definition of `fintypeOfFiniteDimensional` / `fintypeOfFiniteDimensional` 的定义

English:
definition fintypeOfFiniteDimensional
  signature: [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
  body: by
  have : FiniteDimensional 𝕜 (V x) := by
    let phi := (trivializationAt F V x).linearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    exact Finite.equiv phi.symm
  exact FiniteDimensional.fintypeBasisIndex (hs.toBasisAt hx)

中文:
定义 fintypeOfFiniteDimensional
  签名: [向量丛 𝕜 F V] [有限维 𝕜 F]
  定义体: by
  have : FiniteDimensional 𝕜 (V x) := by
    let phi := (trivializationAt F V x).linearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    exact Finite.equiv phi.symm
  exact FiniteDimensional.fintypeBasisIndex (hs.toBasisAt hx)

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, Finite, Finite.equiv, FiniteDimensional, FiniteDimensional.fintypeBasisIndex, fintypeBasisIndex, hs.toBasisAt, linearEquivAt, mem_baseSet_trivializationAt, phi.symm, toBasisAt, trivializationAt
-/
noncomputable def fintypeOfFiniteDimensional [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
    (hs : IsLocalFrameOn I F n s u) (hx : x in u) : Fintype ι := by
  have : FiniteDimensional 𝕜 (V x) := by
    let phi := (trivializationAt F V x).linearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    exact Finite.equiv phi.symm
  exact FiniteDimensional.fintypeBasisIndex (hs.toBasisAt hx)

open scoped Classical in
/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (hs : IsLocalFrameOn I F n s u) (i : ι)
  body: fun x =>
  if hx : x in u then (hs.toBasisAt hx).coord i else 0

中文:
定义 coeff
  签名: (hs : 是LocalFrameOn I F n s u) (i : ι)
  定义体: fun x =>
  if hx : x in u then (hs.toBasisAt hx).coord i else 0
-/
def coeff (hs : IsLocalFrameOn I F n s u) (i : ι) : Π x : M, (V x ->ₗ[𝕜] 𝕜) := fun x =>
  if hx : x in u then (hs.toBasisAt hx).coord i else 0

variable {x : M}

@[simp]
/--
lemma `coeff_apply_of_notMem` / 引理 `coeff_apply_of_notMem`

English:
lemma coeff_apply_of_notMem
  given: (hs : IsLocalFrameOn I F n s u) (hx : x ∉ u) (i : ι)
  proof: by
  simp [coeff, hx]

@[simp]

中文:
引理 coeff_apply_of_notMem
  条件: (hs : 是LocalFrameOn I F n s u) (hx : x ∉ u) (i : ι)
  证明: by
  simp [coeff, hx]

@[simp]
-/
lemma coeff_apply_of_notMem (hs : IsLocalFrameOn I F n s u) (hx : x ∉ u) (i : ι) :
    hs.coeff i x = 0 := by
  simp [coeff, hx]

@[simp]
/--
lemma `coeff_apply_of_mem` / 引理 `coeff_apply_of_mem`

English:
lemma coeff_apply_of_mem
  given: (hs : IsLocalFrameOn I F n s u) (hx : x in u) (t : Π x : M, V x) (i : ι)
  proof: by
  simp [coeff, hx]

中文:
引理 coeff_apply_of_mem
  条件: (hs : 是LocalFrameOn I F n s u) (hx : x in u) (t : Π x : M, V x) (i : ι)
  证明: by
  simp [coeff, hx]
-/
lemma coeff_apply_of_mem (hs : IsLocalFrameOn I F n s u) (hx : x in u) (t : Π x : M, V x) (i : ι) :
    hs.coeff i x (t x) = (hs.toBasisAt hx).repr (t x) i := by
  simp [coeff, hx]

/--
lemma `coeff_sum_eq` / 引理 `coeff_sum_eq`

English:
lemma coeff_sum_eq
  given: [Fintype ι] (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hx : x in u)
  proof: by
  simpa [coeff, hx] using (Basis.sum_repr (hs.toBasisAt hx) (t x)).symm

中文:
引理 coeff_sum_eq
  条件: [有限类型 ι] (hs : 是LocalFrameOn I F n s u) (t : Π x : M, V x) (hx : x in u)
  证明: by
  simpa [coeff, hx] using (Basis.sum_repr (hs.toBasisAt hx) (t x)).symm

Depends on / 依赖: Basis.sum_repr, hs.toBasisAt, sum_repr, toBasisAt
-/
lemma coeff_sum_eq [Fintype ι] (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hx : x in u) :
    t x = ∑ i, hs.coeff i x (t x) • (s i x) := by
  simpa [coeff, hx] using (Basis.sum_repr (hs.toBasisAt hx) (t x)).symm

/--
lemma `eq_of_coeff_eq` / 引理 `eq_of_coeff_eq`

English:
lemma eq_of_coeff_eq
  statement: [Finite ι] (hs : IsLocalFrameOn I F n s u) (hx : x in u)
  proof: by
  let : Fintype ι := Fintype.ofFinite ι
  calc
    t x = ∑ i, hs.coeff i x (t x) • (s i x) := hs.coeff_sum_eq t hx
    _ = ∑ i, hs.coeff i x (t' x) • (s i x) := by simp [h]
    _ = t' x := (hs.coeff_sum_eq t' hx).symm

中文:
引理 eq_of_coeff_eq
  结论: [有限 ι] (hs : 是LocalFrameOn I F n s u) (hx : x in u)
  证明: by
  let : Fintype ι := Fintype.ofFinite ι
  calc
    t x = ∑ i, hs.coeff i x (t x) • (s i x) := hs.coeff_sum_eq t hx
    _ = ∑ i, hs.coeff i x (t' x) • (s i x) := by simp [h]
    _ = t' x := (hs.coeff_sum_eq t' hx).symm

Depends on / 依赖: Fintype, Fintype.ofFinite, coeff_sum_eq, hs.coeff, hs.coeff_sum_eq, ofFinite
-/
lemma eq_of_coeff_eq [Finite ι] (hs : IsLocalFrameOn I F n s u) (hx : x in u)
    {t t' : Π x : M, V x}
    (h : forall i, hs.coeff i x (t x) = hs.coeff i x (t' x)) :
    t x = t' x := by
  let : Fintype ι := Fintype.ofFinite ι
  calc
    t x = ∑ i, hs.coeff i x (t x) • (s i x) := hs.coeff_sum_eq t hx
    _ = ∑ i, hs.coeff i x (t' x) • (s i x) := by simp [h]
    _ = t' x := (hs.coeff_sum_eq t' hx).symm

/--
lemma `eventually_eq_sum_coeff_smul` / 引理 `eventually_eq_sum_coeff_smul`

English:
lemma eventually_eq_sum_coeff_smul
  statement: [Fintype ι]
  proof: eventually_of_mem hu'' fun _ hx => hs.coeff_sum_eq _ hx

中文:
引理 eventually_eq_sum_coeff_smul
  结论: [有限类型 ι]
  证明: eventually_of_mem hu'' fun _ hx => hs.coeff_sum_eq _ hx

Depends on / 依赖: coeff_sum_eq, eventually_of_mem, hs.coeff_sum_eq
-/
lemma eventually_eq_sum_coeff_smul [Fintype ι]
    (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hu'' : u in 𝓝 x) :
    forallᶠ x' in 𝓝 x, t x' = ∑ i, hs.coeff i x' (t x') • (s i x') :=
  eventually_of_mem hu'' fun _ hx => hs.coeff_sum_eq _ hx

variable {t t' : Π x : M, V x}

/--
lemma `coeff_congr` / 引理 `coeff_congr`

English:
lemma coeff_congr
  given: (hs : IsLocalFrameOn I F n s u) (htt' : t x = t' x) (i : ι)
  proof: by
  by_cases hxe : x in u <;> simp [coeff, hxe, htt']

中文:
引理 coeff_congr
  条件: (hs : 是LocalFrameOn I F n s u) (htt' : t x = t' x) (i : ι)
  证明: by
  by_cases hxe : x in u <;> simp [coeff, hxe, htt']
-/
lemma coeff_congr (hs : IsLocalFrameOn I F n s u) (htt' : t x = t' x) (i : ι) :
    hs.coeff i x (t x) = hs.coeff i x (t' x) := by
  by_cases hxe : x in u <;> simp [coeff, hxe, htt']

/--
lemma `coeff_eq_of_eq` / 引理 `coeff_eq_of_eq`

English:
lemma coeff_eq_of_eq
  statement: (hs : IsLocalFrameOn I F n s u) (hs' : IsLocalFrameOn I F n s' u)
  proof: by
  by_cases hxe : x in u
  · simp [coeff, hxe]
    simp_all only [toBasisAt]
  · simp [coeff, hxe]

中文:
引理 coeff_eq_of_eq
  结论: (hs : 是LocalFrameOn I F n s u) (hs' : 是LocalFrameOn I F n s' u)
  证明: by
  by_cases hxe : x in u
  · simp [coeff, hxe]
    simp_all only [toBasisAt]
  · simp [coeff, hxe]

Depends on / 依赖: toBasisAt
-/
lemma coeff_eq_of_eq (hs : IsLocalFrameOn I F n s u) (hs' : IsLocalFrameOn I F n s' u)
    (hss' : forall i, s i x = s' i x) {t : Π x : M, V x} (i : ι) :
    hs.coeff i x (t x) = hs'.coeff i x (t x) := by
  by_cases hxe : x in u
  · simp [coeff, hxe]
    simp_all only [toBasisAt]
  · simp [coeff, hxe]

/--
lemma `eq_iff_coeff` / 引理 `eq_iff_coeff`

English:
lemma eq_iff_coeff
  statement: [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
  proof: by
  let := fintypeOfFiniteDimensional hs hx
  exact ⟨fun h i => hs.coeff_congr h i, fun h => hs.eq_of_coeff_eq hx h⟩

中文:
引理 eq_iff_coeff
  结论: [向量丛 𝕜 F V] [有限维 𝕜 F]
  证明: by
  let := fintypeOfFiniteDimensional hs hx
  exact ⟨fun h i => hs.coeff_congr h i, fun h => hs.eq_of_coeff_eq hx h⟩

Depends on / 依赖: coeff_congr, eq_of_coeff_eq, fintypeOfFiniteDimensional, hs.coeff_congr, hs.eq_of_coeff_eq
-/
lemma eq_iff_coeff [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
    (hs : IsLocalFrameOn I F n s u) (hx : x in u) :
    t x = t' x ↔ forall i, hs.coeff i x (t x) = hs.coeff i x (t' x) := by
  let := fintypeOfFiniteDimensional hs hx
  exact ⟨fun h i => hs.coeff_congr h i, fun h => hs.eq_of_coeff_eq hx h⟩

variable (hs : IsLocalFrameOn I F n s u) [VectorBundle 𝕜 F V]

/--
lemma `contMDiffOn_of_coeff` / 引理 `contMDiffOn_of_coeff`

English:
lemma contMDiffOn_of_coeff
  statement: [FiniteDimensional 𝕜 F]
  proof: by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : CMDiff[u] n (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section (hs.contMDiffOn i)
  have almost : CMDiff[u] n (T% (fun x => ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) :=
    .sum_section fun i _ => this i
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

中文:
引理 contMDiffOn_of_coeff
  结论: [有限维 𝕜 F]
  证明: by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : CMDiff[u] n (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section (hs.contMDiffOn i)
  have almost : CMDiff[u] n (T% (fun x => ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) :=
    .sum_section fun i _ => this i
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

Depends on / 依赖: CMDiff, LinearMap, LinearMap.piApply, TotalSpace, TotalSpace.mk, almost, almost.congr, coeff_sum_eq, contMDiffOn, eq_empty_or_nonempty, fintypeOfFiniteDimensional, hs.coeff, hs.coeff_sum_eq, hs.contMDiffOn, piApply, smul_section, sum_section, u.eq_empty_or_nonempty
-/
lemma contMDiffOn_of_coeff [FiniteDimensional 𝕜 F]
    (h : forall i, CMDiff[u] n ((LinearMap.piApply (hs.coeff i)) t)) :
    CMDiff[u] n (T% t) := by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : CMDiff[u] n (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section (hs.contMDiffOn i)
  have almost : CMDiff[u] n (T% (fun x => ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) :=
    .sum_section fun i _ => this i
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

/--
lemma `contMDiffAt_of_coeff` / 引理 `contMDiffAt_of_coeff`

English:
lemma contMDiffAt_of_coeff
  statement: [FiniteDimensional 𝕜 F]
  proof: by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : CMDiffAt n (T% (fun x => ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) x :=
    .sum_section (fun i _ => (h i).smul_section <| (hs.contMDiffOn i).contMDiffAt hu)
exact almost.congr_of_eventuallyEq (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

中文:
引理 contMDiffAt_of_coeff
  结论: [有限维 𝕜 F]
  证明: by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : CMDiffAt n (T% (fun x => ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) x :=
    .sum_section (fun i _ => (h i).smul_section <| (hs.contMDiffOn i).contMDiffAt hu)
exact almost.congr_of_eventuallyEq (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

Depends on / 依赖: CMDiffAt, LinearMap, LinearMap.piApply, almost, almost.congr_of_eventuallyEq, congr_of_eventuallyEq, contMDiffAt, contMDiffOn, eventually_eq_sum_coeff_smul, fintypeOfFiniteDimensional, hs.coeff, hs.contMDiffOn, hs.eventually_eq_sum_coeff_smul, mem_of_mem_nhds, piApply, smul_section, sum_section
-/
lemma contMDiffAt_of_coeff [FiniteDimensional 𝕜 F]
    (h : forall i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x) (hu : u in 𝓝 x) :
    CMDiffAt n (T% t) x := by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : CMDiffAt n (T% (fun x => ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) x :=
    .sum_section (fun i _ => (h i).smul_section <| (hs.contMDiffOn i).contMDiffAt hu)
exact almost.congr_of_eventuallyEq (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/--
lemma `contMDiffAt_of_coeff_aux` / 引理 `contMDiffAt_of_coeff_aux`

English:
lemma contMDiffAt_of_coeff_aux
  statement: [FiniteDimensional 𝕜 F]
  proof: by
  have := fintypeOfFiniteDimensional hs hx
  exact hs.contMDiffAt_of_coeff h (hu.mem_nhds hx)

中文:
引理 contMDiffAt_of_coeff_aux
  结论: [有限维 𝕜 F]
  证明: by
  have := fintypeOfFiniteDimensional hs hx
  exact hs.contMDiffAt_of_coeff h (hu.mem_nhds hx)

Depends on / 依赖: contMDiffAt_of_coeff, fintypeOfFiniteDimensional, hs.contMDiffAt_of_coeff, hu.mem_nhds, mem_nhds
-/
lemma contMDiffAt_of_coeff_aux [FiniteDimensional 𝕜 F]
    (h : forall i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x)
    (hu : IsOpen u) (hx : x in u) : CMDiffAt n (T% t) x := by
  have := fintypeOfFiniteDimensional hs hx
  exact hs.contMDiffAt_of_coeff h (hu.mem_nhds hx)

section

variable (hs : IsLocalFrameOn I F 1 s u)

/--
lemma `mdifferentiableOn_of_coeff` / 引理 `mdifferentiableOn_of_coeff`

English:
lemma mdifferentiableOn_of_coeff
  statement: [FiniteDimensional 𝕜 F]
  proof: by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : MDiff[u] (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero)
  have almost : MDiff[u] (T% (fun x => ∑ i, hs.coeff i x (t x) • s i x)) :=
    .sum_section (fun i _ _ hx => this i _ hx)
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

中文:
引理 mdifferentiableOn_of_coeff
  结论: [有限维 𝕜 F]
  证明: by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : MDiff[u] (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero)
  have almost : MDiff[u] (T% (fun x => ∑ i, hs.coeff i x (t x) • s i x)) :=
    .sum_section (fun i _ _ hx => this i _ hx)
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

Depends on / 依赖: LinearMap, LinearMap.piApply, TotalSpace, TotalSpace.mk, almost, almost.congr, coeff_sum_eq, contMDiffOn, eq_empty_or_nonempty, fintypeOfFiniteDimensional, hs.coeff, hs.coeff_sum_eq, hs.contMDiffOn, mdifferentiableOn, one_ne_zero, piApply, smul_section, sum_section, u.eq_empty_or_nonempty
-/
lemma mdifferentiableOn_of_coeff [FiniteDimensional 𝕜 F]
    (h : forall i, MDiff[u] ((LinearMap.piApply (hs.coeff i)) t)) :
    MDiff[u] (T% t) := by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : MDiff[u] (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero)
  have almost : MDiff[u] (T% (fun x => ∑ i, hs.coeff i x (t x) • s i x)) :=
    .sum_section (fun i _ _ hx => this i _ hx)
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

/--
lemma `mdifferentiableAt_of_coeff` / 引理 `mdifferentiableAt_of_coeff`

English:
lemma mdifferentiableAt_of_coeff
  statement: [FiniteDimensional 𝕜 F]
  proof: by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : MDiffAt (T% (fun x => ∑ i, hs.coeff i x (t x) • s i x)) x :=
    .sum_section (fun i _ => (h i).smul_section <|
      ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero).mdifferentiableAt hu)
exact almost.congr_of_eventuallyEq (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

中文:
引理 mdifferentiableAt_of_coeff
  结论: [有限维 𝕜 F]
  证明: by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : MDiffAt (T% (fun x => ∑ i, hs.coeff i x (t x) • s i x)) x :=
    .sum_section (fun i _ => (h i).smul_section <|
      ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero).mdifferentiableAt hu)
exact almost.congr_of_eventuallyEq (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

Depends on / 依赖: MDiffAt, almost, almost.congr_of_eventuallyEq, congr_of_eventuallyEq, contMDiffOn, eventually_eq_sum_coeff_smul, fintypeOfFiniteDimensional, hs.coeff, hs.contMDiffOn, hs.eventually_eq_sum_coeff_smul, mdifferentiableAt, mdifferentiableOn, mem_of_mem_nhds, one_ne_zero, smul_section, sum_section
-/
lemma mdifferentiableAt_of_coeff [FiniteDimensional 𝕜 F]
    (h : forall i, MDiffAt ((LinearMap.piApply (hs.coeff i)) t) x) (hu : u in 𝓝 x) :
    MDiffAt (T% t) x := by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : MDiffAt (T% (fun x => ∑ i, hs.coeff i x (t x) • s i x)) x :=
    .sum_section (fun i _ => (h i).smul_section <|
      ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero).mdifferentiableAt hu)
exact almost.congr_of_eventuallyEq (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/--
lemma `mdifferentiableAt_of_coeff_aux` / 引理 `mdifferentiableAt_of_coeff_aux`

English:
lemma mdifferentiableAt_of_coeff_aux
  statement: [FiniteDimensional 𝕜 F]
  proof: hs.mdifferentiableAt_of_coeff h (hu.mem_nhds hx)

中文:
引理 mdifferentiableAt_of_coeff_aux
  结论: [有限维 𝕜 F]
  证明: hs.mdifferentiableAt_of_coeff h (hu.mem_nhds hx)

Depends on / 依赖: hs.mdifferentiableAt_of_coeff, hu.mem_nhds, mdifferentiableAt_of_coeff, mem_nhds
-/
lemma mdifferentiableAt_of_coeff_aux [FiniteDimensional 𝕜 F]
    (h : forall i, MDiffAt ((LinearMap.piApply (hs.coeff i)) t) x)
    (hu : IsOpen u) (hx : x in u) : MDiffAt (T% t) x :=
  hs.mdifferentiableAt_of_coeff h (hu.mem_nhds hx)

end

end IsLocalFrameOn

end IsLocalFrame

namespace Bundle.Trivialization

variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I] {ι : Type*} {x : M}
  (e : Trivialization F (TotalSpace.proj : TotalSpace F V -> M)) [MemTrivializationAtlas e]
  (b : Basis ι 𝕜 F)

/--
Definition of `basisAt` / `basisAt` 的定义

English:
definition basisAt
  signature: (hx : x in e.baseSet)
  body: b.map (e.linearEquivAt (R := 𝕜) x hx).symm

中文:
定义 basisAt
  签名: (hx : x in e.baseSet)
  定义体: b.map (e.linearEquivAt (R := 𝕜) x hx).symm

Depends on / 依赖: b.map, e.linearEquivAt, linearEquivAt
-/
def basisAt (hx : x in e.baseSet) : Basis ι 𝕜 (V x) :=
  b.map (e.linearEquivAt (R := 𝕜) x hx).symm

open scoped Classical in
/--
Definition of `localFrame` / `localFrame` 的定义

English:
definition localFrame
  signature: : ι -> (x : M) -> V x
  body: fun i x => if hx : x in e.baseSet then e.basisAt b hx i else 0

@[simp]

中文:
定义 localFrame
  签名: : ι -> (x : M) -> V x
  定义体: fun i x => if hx : x in e.baseSet then e.basisAt b hx i else 0

@[simp]

Depends on / 依赖: baseSet, basisAt, e.baseSet, e.basisAt
-/
def localFrame : ι -> (x : M) -> V x :=
  fun i x => if hx : x in e.baseSet then e.basisAt b hx i else 0

@[simp]
/--
lemma `localFrame_apply_of_mem_baseSet` / 引理 `localFrame_apply_of_mem_baseSet`

English:
lemma localFrame_apply_of_mem_baseSet
  given: {i : ι} (hx : x in e.baseSet)
  proof: by
  simp [localFrame, hx]

中文:
引理 localFrame_apply_of_mem_baseSet
  条件: {i : ι} (hx : x in e.baseSet)
  证明: by
  simp [localFrame, hx]

Depends on / 依赖: localFrame
-/
lemma localFrame_apply_of_mem_baseSet {i : ι} (hx : x in e.baseSet) :
    e.localFrame b i x = e.basisAt b hx i := by
  simp [localFrame, hx]

/--
lemma `localFrame_apply_of_notMem` / 引理 `localFrame_apply_of_notMem`

English:
lemma localFrame_apply_of_notMem
  given: {i : ι} (hx : x ∉ e.baseSet)
  statement: e.localFrame b i x = 0
  proof: by
  simp [localFrame, hx]

中文:
引理 localFrame_apply_of_notMem
  条件: {i : ι} (hx : x ∉ e.baseSet)
  结论: e.localFrame b i x = 0
  证明: by
  simp [localFrame, hx]

Depends on / 依赖: localFrame
-/
lemma localFrame_apply_of_notMem {i : ι} (hx : x ∉ e.baseSet) : e.localFrame b i x = 0 := by
  simp [localFrame, hx]

/--
lemma `contMDiffOn_localFrame_baseSet` / 引理 `contMDiffOn_localFrame_baseSet`

English:
lemma contMDiffOn_localFrame_baseSet
  given: (i : ι)
  statement: CMDiff[e.baseSet] n (T% (e.localFrame b i))
  proof: by
  rw [e.contMDiffOn_section_baseSet_iff]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [hy, basisAt]

中文:
引理 contMDiffOn_localFrame_baseSet
  条件: (i : ι)
  结论: CMDiff[e.baseSet] n (T% (e.localFrame b i))
  证明: by
  rw [e.contMDiffOn_section_baseSet_iff]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [hy, basisAt]

Depends on / 依赖: basisAt, contMDiffOn_const, contMDiffOn_section_baseSet_iff, e.contMDiffOn_section_baseSet_iff
-/
lemma contMDiffOn_localFrame_baseSet (i : ι) : CMDiff[e.baseSet] n (T% (e.localFrame b i)) := by
  rw [e.contMDiffOn_section_baseSet_iff]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [hy, basisAt]

variable (I) in
/--
lemma `isLocalFrameOn_localFrame_baseSet` / 引理 `isLocalFrameOn_localFrame_baseSet`

English:
lemma isLocalFrameOn_localFrame_baseSet
  statement: IsLocalFrameOn I F n (e.localFrame b) e.baseSet where
  proof: e.contMDiffOn_localFrame_baseSet _ b i
  linearIndependent := by
    intro x hx
    convert! (e.basisAt b hx).linearIndependent
    simp [hx, basisAt]
  generating := by
    intro x hx
    convert! (e.basisAt b hx).span_eq.ge
    simp [hx, basisAt]

中文:
引理 isLocalFrameOn_localFrame_baseSet
  结论: 是LocalFrameOn I F n (e.localFrame b) e.baseSet where
  证明: e.contMDiffOn_localFrame_baseSet _ b i
  linearIndependent := by
    intro x hx
    convert! (e.basisAt b hx).linearIndependent
    simp [hx, basisAt]
  generating := by
    intro x hx
    convert! (e.basisAt b hx).span_eq.ge
    simp [hx, basisAt]

Depends on / 依赖: contMDiffOn_localFrame_baseSet, e.contMDiffOn_localFrame_baseSet
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

/--
lemma `_root_.contMDiffAt_localFrame_of_mem` / 引理 `_root_.contMDiffAt_localFrame_of_mem`

English:
lemma _root_.contMDiffAt_localFrame_of_mem
  given: (i : ι) (hx : x in e.baseSet)
  proof: (e.isLocalFrameOn_localFrame_baseSet I n b).contMDiffAt e.open_baseSet hx _

中文:
引理 _root_.contMDiffAt_localFrame_of_mem
  条件: (i : ι) (hx : x in e.baseSet)
  证明: (e.isLocalFrameOn_localFrame_baseSet I n b).contMDiffAt e.open_baseSet hx _

Depends on / 依赖: contMDiffAt, e.isLocalFrameOn_localFrame_baseSet, e.open_baseSet, isLocalFrameOn_localFrame_baseSet, open_baseSet
-/
lemma _root_.contMDiffAt_localFrame_of_mem (i : ι) (hx : x in e.baseSet) :
    CMDiffAt n (T% (e.localFrame b i)) x :=
  (e.isLocalFrameOn_localFrame_baseSet I n b).contMDiffAt e.open_baseSet hx _

variable [ContMDiffVectorBundle 1 F V I]

variable (I) in
/--
Definition of `localFrameCoeff` / `localFrameCoeff` 的定义

English:
definition localFrameCoeff
  signature: (i : ι)
  body: (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff i

@[deprecated (since := "2026-07-26")] alias localFrame_coeff := localFrameCoeff

中文:
定义 localFrameCoeff
  签名: (i : ι)
  定义体: (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff i

@[deprecated (since := "2026-07-26")] alias localFrame_coeff := localFrameCoeff

Depends on / 依赖: e.isLocalFrameOn_localFrame_baseSet, isLocalFrameOn_localFrame_baseSet
-/
def localFrameCoeff (i : ι) : Π x : M, (V x ->ₗ[𝕜] 𝕜) :=
  (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff i

@[deprecated (since := "2026-07-26")] alias localFrame_coeff := localFrameCoeff

variable {e b}
variable {x x' : M}

variable (e b) in
@[simp]
/--
lemma `localFrameCoeff_apply_of_notMem_baseSet` / 引理 `localFrameCoeff_apply_of_notMem_baseSet`

English:
lemma localFrameCoeff_apply_of_notMem_baseSet
  given: (hx : x ∉ e.baseSet) (i : ι)
  proof: by
  simpa [localFrameCoeff] using
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff_apply_of_notMem hx i

@[deprecated (since := "2026-07-26")]
alias localFrame_coeff_apply_of_notMem_baseSet := localFrameCoeff_apply_of_notMem_baseSet

中文:
引理 localFrameCoeff_apply_of_notMem_baseSet
  条件: (hx : x ∉ e.baseSet) (i : ι)
  证明: by
  simpa [localFrameCoeff] using
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff_apply_of_notMem hx i

@[deprecated (since := "2026-07-26")]
alias localFrame_coeff_apply_of_notMem_baseSet := localFrameCoeff_apply_of_notMem_baseSet

Depends on / 依赖: coeff_apply_of_notMem, e.isLocalFrameOn_localFrame_baseSet, isLocalFrameOn_localFrame_baseSet, localFrameCoeff
-/
lemma localFrameCoeff_apply_of_notMem_baseSet (hx : x ∉ e.baseSet) (i : ι) :
    e.localFrameCoeff I b i x = 0 := by
  simpa [localFrameCoeff] using
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff_apply_of_notMem hx i

@[deprecated (since := "2026-07-26")]
alias localFrame_coeff_apply_of_notMem_baseSet := localFrameCoeff_apply_of_notMem_baseSet

variable (e b) in
@[simp]
/--
lemma `localFrameCoeff_apply_of_mem_baseSet` / 引理 `localFrameCoeff_apply_of_mem_baseSet`

English:
lemma localFrameCoeff_apply_of_mem_baseSet
  given: (hx : x in e.baseSet) (s : Π x : M, V x) (i : ι)
  proof: by
  have he := e.isLocalFrameOn_localFrame_baseSet I 1 b
  have hbasis : e.basisAt b hx = he.toBasisAt hx := by
    ext j
    simp [IsLocalFrameOn.toBasisAt, localFrame, basisAt, hx]
  simp [localFrameCoeff, IsLocalFrameOn.coeff, hx, hbasis]

@[deprecated (since := "2026-07-26")]
alias localFrame_coeff_apply_of_mem_baseSet := localFrameCoeff_apply_of_mem_baseSet

中文:
引理 localFrameCoeff_apply_of_mem_baseSet
  条件: (hx : x in e.baseSet) (s : Π x : M, V x) (i : ι)
  证明: by
  have he := e.isLocalFrameOn_localFrame_baseSet I 1 b
  have hbasis : e.basisAt b hx = he.toBasisAt hx := by
    ext j
    simp [IsLocalFrameOn.toBasisAt, localFrame, basisAt, hx]
  simp [localFrameCoeff, IsLocalFrameOn.coeff, hx, hbasis]

@[deprecated (since := "2026-07-26")]
alias localFrame_coeff_apply_of_mem_baseSet := localFrameCoeff_apply_of_mem_baseSet

Depends on / 依赖: IsLocalFrameOn, IsLocalFrameOn.coeff, IsLocalFrameOn.toBasisAt, basisAt, e.basisAt, e.isLocalFrameOn_localFrame_baseSet, hbasis, he.toBasisAt, isLocalFrameOn_localFrame_baseSet, localFrame, localFrameCoeff, toBasisAt
-/
lemma localFrameCoeff_apply_of_mem_baseSet (hx : x in e.baseSet) (s : Π x : M, V x) (i : ι) :
    (localFrameCoeff I e b i x) (s x) = (e.basisAt b hx).repr (s x) i := by
  have he := e.isLocalFrameOn_localFrame_baseSet I 1 b
  have hbasis : e.basisAt b hx = he.toBasisAt hx := by
    ext j
    simp [IsLocalFrameOn.toBasisAt, localFrame, basisAt, hx]
  simp [localFrameCoeff, IsLocalFrameOn.coeff, hx, hbasis]

@[deprecated (since := "2026-07-26")]
alias localFrame_coeff_apply_of_mem_baseSet := localFrameCoeff_apply_of_mem_baseSet

variable {s s' : Π x : M, V x}

/--
lemma `eq_sum_localFrameCoeff_smul` / 引理 `eq_sum_localFrameCoeff_smul`

English:
lemma eq_sum_localFrameCoeff_smul
  given: [Fintype ι] (hx : x' in e.baseSet)
  proof: (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_sum_eq s hx

@[deprecated (since := "2026-07-26")]
alias eq_sum_localFrame_coeff_smul := eq_sum_localFrameCoeff_smul

中文:
引理 eq_sum_localFrameCoeff_smul
  条件: [有限类型 ι] (hx : x' in e.baseSet)
  证明: (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_sum_eq s hx

@[deprecated (since := "2026-07-26")]
alias eq_sum_localFrame_coeff_smul := eq_sum_localFrameCoeff_smul

Depends on / 依赖: coeff_sum_eq, isLocalFrameOn_localFrame_baseSet
-/
lemma eq_sum_localFrameCoeff_smul [Fintype ι] (hx : x' in e.baseSet) :
    s x' = ∑ i, e.localFrameCoeff I b i x' (s x') • e.localFrame b i x' :=
  (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_sum_eq s hx

@[deprecated (since := "2026-07-26")]
alias eq_sum_localFrame_coeff_smul := eq_sum_localFrameCoeff_smul

variable (e b) in
/--
lemma `eventually_eq_localFrame_sum_coeff_smul` / 引理 `eventually_eq_localFrame_sum_coeff_smul`

English:
lemma eventually_eq_localFrame_sum_coeff_smul
  given: [Fintype ι] (hxe : x in e.baseSet)
  proof: eventually_nhds_iff.mpr ⟨e.baseSet, fun _ => e.eq_sum_localFrameCoeff_smul, e.open_baseSet, hxe⟩

中文:
引理 eventually_eq_localFrame_sum_coeff_smul
  条件: [有限类型 ι] (hxe : x in e.baseSet)
  证明: eventually_nhds_iff.mpr ⟨e.baseSet, fun _ => e.eq_sum_localFrameCoeff_smul, e.open_baseSet, hxe⟩

Depends on / 依赖: baseSet, e.baseSet, e.eq_sum_localFrameCoeff_smul, e.open_baseSet, eq_sum_localFrameCoeff_smul, eventually_nhds_iff, eventually_nhds_iff.mpr, open_baseSet
-/
lemma eventually_eq_localFrame_sum_coeff_smul [Fintype ι] (hxe : x in e.baseSet) :
    forallᶠ x' in 𝓝 x, s x' = ∑ i, e.localFrameCoeff I b i x' (s x') • e.localFrame b i x' :=
  eventually_nhds_iff.mpr ⟨e.baseSet, fun _ => e.eq_sum_localFrameCoeff_smul, e.open_baseSet, hxe⟩

variable (e b) in
/--
lemma `localFrameCoeff_congr` / 引理 `localFrameCoeff_congr`

English:
lemma localFrameCoeff_congr
  given: {i : ι} (hss' : s x = s' x)
  proof: by
  simpa using! (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_congr hss' i

@[deprecated (since := "2026-07-26")] alias localFrame_coeff_congr := localFrameCoeff_congr

中文:
引理 localFrameCoeff_congr
  条件: {i : ι} (hss' : s x = s' x)
  证明: by
  simpa using! (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_congr hss' i

@[deprecated (since := "2026-07-26")] alias localFrame_coeff_congr := localFrameCoeff_congr

Depends on / 依赖: coeff_congr, isLocalFrameOn_localFrame_baseSet
-/
lemma localFrameCoeff_congr {i : ι} (hss' : s x = s' x) :
    e.localFrameCoeff I b i x (s x) = e.localFrameCoeff I b i x (s' x) := by
  simpa using! (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_congr hss' i

@[deprecated (since := "2026-07-26")] alias localFrame_coeff_congr := localFrameCoeff_congr

variable {n}

variable (e) in
/--
lemma `localFrameCoeff_eq_coeff` / 引理 `localFrameCoeff_eq_coeff`

English:
lemma localFrameCoeff_eq_coeff
  given: (hxe : x in e.baseSet) {i : ι}
  proof: by
  simp [e.localFrameCoeff_apply_of_mem_baseSet b hxe, basisAt]

@[deprecated (since := "2026-07-26")] alias localFrame_coeff_eq_coeff := localFrameCoeff_eq_coeff

中文:
引理 localFrameCoeff_eq_coeff
  条件: (hxe : x in e.baseSet) {i : ι}
  证明: by
  simp [e.localFrameCoeff_apply_of_mem_baseSet b hxe, basisAt]

@[deprecated (since := "2026-07-26")] alias localFrame_coeff_eq_coeff := localFrameCoeff_eq_coeff

Depends on / 依赖: basisAt, e.localFrameCoeff_apply_of_mem_baseSet, localFrameCoeff_apply_of_mem_baseSet
-/
lemma localFrameCoeff_eq_coeff (hxe : x in e.baseSet) {i : ι} :
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
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V -> M)} [MemTrivializationAtlas e]
  {ι : Type*} (b : Basis ι 𝕜 F) {s : Π x : M, V x} {t : Set M} {k : Nat∞ω} {x x' : M}
  [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle k F V I]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `contMDiffAt_localFrameCoeff` / 引理 `contMDiffAt_localFrameCoeff`

English:
lemma contMDiffAt_localFrameCoeff
  given: (hxe : x in e.baseSet) (hs : CMDiffAt k (T% s) x) (i : ι)
  proof: by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  -- step 1: on e.baseSet, we know compute the coefficient very well
  let aux := fun x => b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices CMDiffAt k aux x by
    apply this.congr_of_eventuallyEq ?_
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrameCoeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is `C^k`
  have h₁ : CMDiffAt k (fun x => (e ((T% s) x)).2) x := by
    simpa using (e.contMDiffAt_section_iff hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F ->ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : CMDiffAt k breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
contMDiffAt_iff_contDiffAt.mpr by fun_prop
  exact this.comp x h₁

@[deprecated (since := "2026-07-26")]
alias contMDiffAt_localFrame_coeff := contMDiffAt_localFrameCoeff

中文:
引理 contMDiffAt_localFrameCoeff
  条件: (hxe : x in e.baseSet) (hs : CMDiffAt k (T% s) x) (i : ι)
  证明: by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  -- step 1: on e.baseSet, we know compute the coefficient very well
  let aux := fun x => b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices CMDiffAt k aux x by
    apply this.congr_of_eventuallyEq ?_
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrameCoeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is `C^k`
  have h₁ : CMDiffAt k (fun x => (e ((T% s) x)).2) x := by
    simpa using (e.contMDiffAt_section_iff hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F ->ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : CMDiffAt k breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
contMDiffAt_iff_contDiffAt.mpr by fun_prop
  exact this.comp x h₁

@[deprecated (since := "2026-07-26")]
alias contMDiffAt_localFrame_coeff := contMDiffAt_localFrameCoeff
-/
lemma contMDiffAt_localFrameCoeff (hxe : x in e.baseSet) (hs : CMDiffAt k (T% s) x) (i : ι) :
    CMDiffAt k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  -- step 1: on e.baseSet, we know compute the coefficient very well
  let aux := fun x => b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices CMDiffAt k aux x by
    apply this.congr_of_eventuallyEq ?_
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrameCoeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is `C^k`
  have h₁ : CMDiffAt k (fun x => (e ((T% s) x)).2) x := by
    simpa using (e.contMDiffAt_section_iff hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F ->ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : CMDiffAt k breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
contMDiffAt_iff_contDiffAt.mpr by fun_prop
  exact this.comp x h₁

@[deprecated (since := "2026-07-26")]
alias contMDiffAt_localFrame_coeff := contMDiffAt_localFrameCoeff

/--
lemma `contMDiffOn_localFrameCoeff` / 引理 `contMDiffOn_localFrameCoeff`

English:
lemma contMDiffOn_localFrameCoeff
  statement: (ht : IsOpen t) (ht' : t subseteq e.baseSet)
  proof: fun _ hx => (contMDiffAt_localFrameCoeff b (ht' hx)
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_localFrame_coeff := contMDiffOn_localFrameCoeff

中文:
引理 contMDiffOn_localFrameCoeff
  结论: (ht : 是开集 t) (ht' : t subseteq e.baseSet)
  证明: fun _ hx => (contMDiffAt_localFrameCoeff b (ht' hx)
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_localFrame_coeff := contMDiffOn_localFrameCoeff

Depends on / 依赖: contMDiffAt, contMDiffAt_localFrameCoeff, contMDiffWithinAt, hs.contMDiffAt, ht.mem_nhds, mem_nhds
-/
lemma contMDiffOn_localFrameCoeff (ht : IsOpen t) (ht' : t subseteq e.baseSet)
    (hs : CMDiff[t] k (T% s)) (i : ι) :
    CMDiff[t] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) :=
  fun _ hx => (contMDiffAt_localFrameCoeff b (ht' hx)
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_localFrame_coeff := contMDiffOn_localFrameCoeff

/--
lemma `contMDiffOn_baseSet_localFrameCoeff` / 引理 `contMDiffOn_baseSet_localFrameCoeff`

English:
lemma contMDiffOn_baseSet_localFrameCoeff
  given: (hs : CMDiff[e.baseSet] k (T% s)) (i : ι)
  proof: contMDiffOn_localFrameCoeff b e.open_baseSet (subset_refl _) hs _

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_baseSet_localFrame_coeff := contMDiffOn_baseSet_localFrameCoeff

中文:
引理 contMDiffOn_baseSet_localFrameCoeff
  条件: (hs : CMDiff[e.baseSet] k (T% s)) (i : ι)
  证明: contMDiffOn_localFrameCoeff b e.open_baseSet (subset_refl _) hs _

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_baseSet_localFrame_coeff := contMDiffOn_baseSet_localFrameCoeff

Depends on / 依赖: contMDiffOn_localFrameCoeff, e.open_baseSet, open_baseSet, subset_refl
-/
lemma contMDiffOn_baseSet_localFrameCoeff (hs : CMDiff[e.baseSet] k (T% s)) (i : ι) :
    CMDiff[e.baseSet] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) :=
  contMDiffOn_localFrameCoeff b e.open_baseSet (subset_refl _) hs _

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_baseSet_localFrame_coeff := contMDiffOn_baseSet_localFrameCoeff

/--
lemma `contMDiffAt_iff_localFrameCoeff` / 引理 `contMDiffAt_iff_localFrameCoeff`

English:
lemma contMDiffAt_iff_localFrameCoeff
  given: (hx : x' in e.baseSet)
  proof: ⟨fun h i => contMDiffAt_localFrameCoeff b hx h i,
    fun hi => (e.isLocalFrameOn_localFrame_baseSet I k b).contMDiffAt_of_coeff hi
    (e.open_baseSet.mem_nhds hx)⟩

@[deprecated (since := "2026-07-26")]
alias contMDiffAt_iff_localFrame_coeff := contMDiffAt_iff_localFrameCoeff

中文:
引理 contMDiffAt_iff_localFrameCoeff
  条件: (hx : x' in e.baseSet)
  证明: ⟨fun h i => contMDiffAt_localFrameCoeff b hx h i,
    fun hi => (e.isLocalFrameOn_localFrame_baseSet I k b).contMDiffAt_of_coeff hi
    (e.open_baseSet.mem_nhds hx)⟩

@[deprecated (since := "2026-07-26")]
alias contMDiffAt_iff_localFrame_coeff := contMDiffAt_iff_localFrameCoeff

Depends on / 依赖: contMDiffAt_localFrameCoeff, contMDiffAt_of_coeff, e.isLocalFrameOn_localFrame_baseSet, e.open_baseSet.mem_nhds, isLocalFrameOn_localFrame_baseSet, mem_nhds, open_baseSet
-/
lemma contMDiffAt_iff_localFrameCoeff (hx : x' in e.baseSet) :
    CMDiffAt k (T% s) x' ↔ forall i, CMDiffAt k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x' :=
  ⟨fun h i => contMDiffAt_localFrameCoeff b hx h i,
    fun hi => (e.isLocalFrameOn_localFrame_baseSet I k b).contMDiffAt_of_coeff hi
    (e.open_baseSet.mem_nhds hx)⟩

@[deprecated (since := "2026-07-26")]
alias contMDiffAt_iff_localFrame_coeff := contMDiffAt_iff_localFrameCoeff

/--
lemma `contMDiffOn_iff_localFrameCoeff` / 引理 `contMDiffOn_iff_localFrameCoeff`

English:
lemma contMDiffOn_iff_localFrameCoeff
  given: (ht : IsOpen t) (ht' : t subseteq e.baseSet)
  proof: by
  refine ⟨fun h i => contMDiffOn_localFrameCoeff b ht ht' h _, fun h x hx => ?_⟩
  exact (contMDiffAt_iff_localFrameCoeff b (ht' hx)).mpr
.contMDiffWithinAt (fun i => (h i x hx).contMDiffAt (ht.mem_nhds hx))

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_iff_localFrame_coeff := contMDiffOn_iff_localFrameCoeff

中文:
引理 contMDiffOn_iff_localFrameCoeff
  条件: (ht : 是开集 t) (ht' : t subseteq e.baseSet)
  证明: by
  refine ⟨fun h i => contMDiffOn_localFrameCoeff b ht ht' h _, fun h x hx => ?_⟩
  exact (contMDiffAt_iff_localFrameCoeff b (ht' hx)).mpr
.contMDiffWithinAt (fun i => (h i x hx).contMDiffAt (ht.mem_nhds hx))

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_iff_localFrame_coeff := contMDiffOn_iff_localFrameCoeff

Depends on / 依赖: contMDiffAt, contMDiffAt_iff_localFrameCoeff, contMDiffOn_localFrameCoeff, contMDiffWithinAt, ht.mem_nhds, mem_nhds
-/
lemma contMDiffOn_iff_localFrameCoeff (ht : IsOpen t) (ht' : t subseteq e.baseSet) :
    CMDiff[t] k (T% s) ↔ forall i, CMDiff[t] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) := by
  refine ⟨fun h i => contMDiffOn_localFrameCoeff b ht ht' h _, fun h x hx => ?_⟩
  exact (contMDiffAt_iff_localFrameCoeff b (ht' hx)).mpr
.contMDiffWithinAt (fun i => (h i x hx).contMDiffAt (ht.mem_nhds hx))

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_iff_localFrame_coeff := contMDiffOn_iff_localFrameCoeff

/--
lemma `contMDiffOn_baseSet_iff_localFrameCoeff` / 引理 `contMDiffOn_baseSet_iff_localFrameCoeff`

English:
lemma contMDiffOn_baseSet_iff_localFrameCoeff
  proof: by
  rw [contMDiffOn_iff_localFrameCoeff b e.open_baseSet (subset_refl _)]

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_baseSet_iff_localFrame_coeff := contMDiffOn_baseSet_iff_localFrameCoeff

中文:
引理 contMDiffOn_baseSet_iff_localFrameCoeff
  证明: by
  rw [contMDiffOn_iff_localFrameCoeff b e.open_baseSet (subset_refl _)]

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_baseSet_iff_localFrame_coeff := contMDiffOn_baseSet_iff_localFrameCoeff

Depends on / 依赖: contMDiffOn_iff_localFrameCoeff, e.open_baseSet, open_baseSet, subset_refl
-/
lemma contMDiffOn_baseSet_iff_localFrameCoeff :
    CMDiff[e.baseSet] k (T% s) ↔
      forall i, CMDiff[e.baseSet] k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) := by
  rw [contMDiffOn_iff_localFrameCoeff b e.open_baseSet (subset_refl _)]

@[deprecated (since := "2026-07-26")]
alias contMDiffOn_baseSet_iff_localFrame_coeff := contMDiffOn_baseSet_iff_localFrameCoeff

-- Differentiability of a section can be checked in terms of its local frame coefficients
section MDifferentiable

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mdifferentiableAt_localFrameCoeff` / 引理 `mdifferentiableAt_localFrameCoeff`

English:
lemma mdifferentiableAt_localFrameCoeff
  proof: by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  -- step 1: on `e.baseSet`, we know the coefficient very well
  let aux := fun x => b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices MDiffAt aux x by
    apply this.congr_of_eventuallyEq
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrameCoeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is differentiable
  have h₁ : MDiffAt (fun x => (e ((T% s) x)).2) x := by
    simpa using (e.mdifferentiableAt_section_iff I s hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F ->ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜) breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
mdifferentiableAt_iff_differentiableAt.mpr by fun_prop
  exact this.comp x h₁

@[deprecated (since := "2026-07-26")]
alias mdifferentiableAt_localFrame_coeff := mdifferentiableAt_localFrameCoeff

中文:
引理 mdifferentiableAt_localFrameCoeff
  证明: by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  -- step 1: on `e.baseSet`, we know the coefficient very well
  let aux := fun x => b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices MDiffAt aux x by
    apply this.congr_of_eventuallyEq
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrameCoeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is differentiable
  have h₁ : MDiffAt (fun x => (e ((T% s) x)).2) x := by
    simpa using (e.mdifferentiableAt_section_iff I s hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F ->ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜) breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
mdifferentiableAt_iff_differentiableAt.mpr by fun_prop
  exact this.comp x h₁

@[deprecated (since := "2026-07-26")]
alias mdifferentiableAt_localFrame_coeff := mdifferentiableAt_localFrameCoeff
-/
lemma mdifferentiableAt_localFrameCoeff
    (hxe : x in e.baseSet) (hs : MDiffAt (T% s) x) (i : ι) :
    MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  -- step 1: on `e.baseSet`, we know the coefficient very well
  let aux := fun x => b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices MDiffAt aux x by
    apply this.congr_of_eventuallyEq
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrameCoeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is differentiable
  have h₁ : MDiffAt (fun x => (e ((T% s) x)).2) x := by
    simpa using (e.mdifferentiableAt_section_iff I s hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F ->ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜) breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
mdifferentiableAt_iff_differentiableAt.mpr by fun_prop
  exact this.comp x h₁

@[deprecated (since := "2026-07-26")]
alias mdifferentiableAt_localFrame_coeff := mdifferentiableAt_localFrameCoeff

/--
lemma `mdifferentiableOn_localFrameCoeff` / 引理 `mdifferentiableOn_localFrameCoeff`

English:
lemma mdifferentiableOn_localFrameCoeff
  statement: (ht : IsOpen t) (ht' : t subseteq e.baseSet)
  proof: fun _ hx => (mdifferentiableAt_localFrameCoeff b (ht' hx)
    (hs.mdifferentiableAt (ht.mem_nhds hx)) i).mdifferentiableWithinAt

@[deprecated (since := "2026-07-26")]
alias mdifferentiableOn_localFrame_coeff := mdifferentiableOn_localFrameCoeff

中文:
引理 mdifferentiableOn_localFrameCoeff
  结论: (ht : 是开集 t) (ht' : t subseteq e.baseSet)
  证明: fun _ hx => (mdifferentiableAt_localFrameCoeff b (ht' hx)
    (hs.mdifferentiableAt (ht.mem_nhds hx)) i).mdifferentiableWithinAt

@[deprecated (since := "2026-07-26")]
alias mdifferentiableOn_localFrame_coeff := mdifferentiableOn_localFrameCoeff

Depends on / 依赖: hs.mdifferentiableAt, ht.mem_nhds, mdifferentiableAt, mdifferentiableAt_localFrameCoeff, mdifferentiableWithinAt, mem_nhds
-/
lemma mdifferentiableOn_localFrameCoeff (ht : IsOpen t) (ht' : t subseteq e.baseSet)
    (hs : MDiff[t] (T% s)) (i : ι) : MDiff[t] ((LinearMap.piApply (e.localFrameCoeff I b i)) s) :=
  fun _ hx => (mdifferentiableAt_localFrameCoeff b (ht' hx)
    (hs.mdifferentiableAt (ht.mem_nhds hx)) i).mdifferentiableWithinAt

@[deprecated (since := "2026-07-26")]
alias mdifferentiableOn_localFrame_coeff := mdifferentiableOn_localFrameCoeff

/--
lemma `mdifferentiableOn_baseSet_localFrameCoeff` / 引理 `mdifferentiableOn_baseSet_localFrameCoeff`

English:
lemma mdifferentiableOn_baseSet_localFrameCoeff
  given: (hs : MDiff[e.baseSet] (T% s)) (i : ι)
  proof: mdifferentiableOn_localFrameCoeff b e.open_baseSet (subset_refl _) hs _

@[deprecated (since := "2026-07-26")]
alias mdifferentiableOn_baseSet_localFrame_coeff := mdifferentiableOn_baseSet_localFrameCoeff

中文:
引理 mdifferentiableOn_baseSet_localFrameCoeff
  条件: (hs : MDiff[e.baseSet] (T% s)) (i : ι)
  证明: mdifferentiableOn_localFrameCoeff b e.open_baseSet (subset_refl _) hs _

@[deprecated (since := "2026-07-26")]
alias mdifferentiableOn_baseSet_localFrame_coeff := mdifferentiableOn_baseSet_localFrameCoeff

Depends on / 依赖: e.open_baseSet, mdifferentiableOn_localFrameCoeff, open_baseSet, subset_refl
-/
lemma mdifferentiableOn_baseSet_localFrameCoeff (hs : MDiff[e.baseSet] (T% s)) (i : ι) :
    MDiff[e.baseSet] ((LinearMap.piApply (e.localFrameCoeff I b i)) s) :=
  mdifferentiableOn_localFrameCoeff b e.open_baseSet (subset_refl _) hs _

@[deprecated (since := "2026-07-26")]
alias mdifferentiableOn_baseSet_localFrame_coeff := mdifferentiableOn_baseSet_localFrameCoeff

/--
lemma `mdifferentiableAt_iff_localFrameCoeff` / 引理 `mdifferentiableAt_iff_localFrameCoeff`

English:
lemma mdifferentiableAt_iff_localFrameCoeff
  given: (hx : x' in e.baseSet)
  proof: ⟨fun h i => mdifferentiableAt_localFrameCoeff b hx h i, fun hi =>
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).mdifferentiableAt_of_coeff_aux hi e.open_baseSet hx⟩

@[deprecated (since := "2026-07-26")]
alias mdifferentiableAt_iff_localFrame_coeff := mdifferentiableAt_iff_localFrameCoeff

中文:
引理 mdifferentiableAt_iff_localFrameCoeff
  条件: (hx : x' in e.baseSet)
  证明: ⟨fun h i => mdifferentiableAt_localFrameCoeff b hx h i, fun hi =>
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).mdifferentiableAt_of_coeff_aux hi e.open_baseSet hx⟩

@[deprecated (since := "2026-07-26")]
alias mdifferentiableAt_iff_localFrame_coeff := mdifferentiableAt_iff_localFrameCoeff

Depends on / 依赖: e.isLocalFrameOn_localFrame_baseSet, e.open_baseSet, isLocalFrameOn_localFrame_baseSet, mdifferentiableAt_localFrameCoeff, mdifferentiableAt_of_coeff_aux, open_baseSet
-/
lemma mdifferentiableAt_iff_localFrameCoeff (hx : x' in e.baseSet) :
    MDiffAt (T% s) x' ↔ forall i, MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x' :=
  ⟨fun h i => mdifferentiableAt_localFrameCoeff b hx h i, fun hi =>
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).mdifferentiableAt_of_coeff_aux hi e.open_baseSet hx⟩

@[deprecated (since := "2026-07-26")]
alias mdifferentiableAt_iff_localFrame_coeff := mdifferentiableAt_iff_localFrameCoeff

end MDifferentiable

end
