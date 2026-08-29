/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Topology.VectorBundle.FiniteDimensional
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The tensoriality criterion

Given vector bundles `V` and `W` over a manifold `M`, one can construct a section of the hom-bundle
`Π x, V x →L[𝕜] W x` from a *tensorial* operation sending sections of `V` to sections of `W`.
This file provides this construction.

In fact, we define tensoriality, and provide the above criterion, in slightly greater generality:
for operations sending sections of `V` to a vector space `A` (which in the above application is the
fibre `W x`), the construction produces a continuous linear map `V x →L[𝕜] A`.

## Main definitions

* `TensorialAt`: Propositional structure stating that an operation on sections of a vector bundle
  `V` is tensorial.

* `TensorialAt.mkHom`: An operation on sections of `V` which is tensorial at `x` defines a
  continuous linear map out of `V x`.

* `TensorialAt.mkHom₂`: An operation on sections of `V` and `V'` which is tensorial at `x` in both
  arguments defines a continuous bilinear map out of `V x` and `V' x`.

-/

open Bundle FiberBundle Topology Module

open scoped Manifold ContDiff

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M -> Type*} [TopologicalSpace (TotalSpace F V)]
  [forall x, AddCommGroup (V x)] [forall x, Module 𝕜 (V x)]
  [forall x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

variable
  (F' : Type*) [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {V' : M -> Type*} [TopologicalSpace (TotalSpace F' V')]
  [forall x, AddCommGroup (V' x)] [forall x, Module 𝕜 (V' x)] [forall x : M, TopologicalSpace (V' x)]
  [FiberBundle F' V']

variable {A : Type*} [AddCommGroup A] [Module 𝕜 A]

/--
Definition of `TensorialAt` / `TensorialAt` 的定义

English:
structure TensorialAt
  parameters: (Φ : (Π x : M, V x) -> A) (x : M)
  axioms and operations (2):
    - smul : forall {f : M -> 𝕜} {σ : Π x : M, V x}, MDiffAt f x -> MDiffAt (T% σ) x -> Φ (f • σ) = f x • Φ σ
    - add : forall {σ σ'}, MDiffAt (T% σ) x -> MDiffAt (T% σ') x -> Φ (σ + σ') = Φ σ + Φ σ'

中文:
结构 TensorialAt
  参数: (Φ : (Π x : M, V x) -> A) (x : M)
  公理与运算 (2 个):
    - smul : 对任意 {f : M -> 𝕜} {σ : Π x : M, V x}, MDiffAt f x -> MDiffAt (T% σ) x -> Φ (f • σ) = f x • Φ σ
    - add : 对任意 {σ σ'}, MDiffAt (T% σ) x -> MDiffAt (T% σ') x -> Φ (σ + σ') = Φ σ + Φ σ'
-/
structure TensorialAt (Φ : (Π x : M, V x) -> A) (x : M) : Prop where
  smul : forall {f : M -> 𝕜} {σ : Π x : M, V x}, MDiffAt f x -> MDiffAt (T% σ) x -> Φ (f • σ) = f x • Φ σ
  add : forall {σ σ'}, MDiffAt (T% σ) x -> MDiffAt (T% σ') x -> Φ (σ + σ') = Φ σ + Φ σ'

variable {Φ : (Π x : M, V x) -> A} {x : M}
variable {I F F'}

namespace TensorialAt

/--
theorem `«local»` / 定理 `«local»`

English:
theorem «local»
  statement: (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
  proof: by
  classical
  -- Introduce the indicator function of a neighbourhood `t` of `x` on which equality holds,
  -- and cut off the two sections `σ` and `σ'` using this indicator function.
  let ψ (x' : M) : 𝕜 := if σ x' = σ' x' then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hσσ'.self_of_nhds]
  hav

中文:
定理 «local»
  结论: (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
  证明: by
  classical
  -- Introduce the indicator function of a neighbourhood `t` of `x` on which equality holds,
  -- and cut off the two sections `σ` and `σ'` using this indicator function.
  let ψ (x' : M) : 𝕜 := if σ x' = σ' x' then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hσσ'.self_of_nhds]
  hav
-/
protected theorem «local» (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : forallᶠ x' in 𝓝 x, σ x' = σ' x') :
    Φ σ = Φ σ' := by
  classical
  -- Introduce the indicator function of a neighbourhood `t` of `x` on which equality holds,
  -- and cut off the two sections `σ` and `σ'` using this indicator function.
  let ψ (x' : M) : 𝕜 := if σ x' = σ' x' then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hσσ'.self_of_nhds]
  have (x' : M) : (ψ • σ) x' = (ψ • σ') x' := by
    dsimp [ψ]
    split_ifs with hx' <;> simp [hx']
  have hψ' : MDiffAt ψ x := by
    have : MDiffAt (fun (_x : M) => (1 : 𝕜)) x := mdifferentiableAt_const
    exact this.congr_of_eventuallyEq (hσσ'.mono fun x' hx' => by simp [ψ, hx'])
  calc Φ σ
    _ = Φ (ψ • σ) := by simp [hΦ.smul hψ' hσ, hψx]
    _ = Φ (ψ • σ') := by rw [funext this]
    _ = Φ σ' := by simp [hΦ.smul hψ' hσ', hψx]

variable [VectorBundle 𝕜 F V] [VectorBundle 𝕜 F' V']

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  given: (hΦ : TensorialAt I F Φ x)
  statement: Φ 0 = 0
  proof: by
  calc
    Φ 0 = Φ ((0 : M -> 𝕜) • (0 : Π x, V x)) := by simp
    _ = 0 • Φ 0 := hΦ.smul mdifferentiableAt_const (mdifferentiable_zeroSection ..)
    _ = 0 := by simp

中文:
定理 zero
  条件: (hΦ : TensorialAt I F Φ x)
  结论: Φ 0 = 0
  证明: by
  calc
    Φ 0 = Φ ((0 : M -> 𝕜) • (0 : Π x, V x)) := by simp
    _ = 0 • Φ 0 := hΦ.smul mdifferentiableAt_const (mdifferentiable_zeroSection ..)
    _ = 0 := by simp

Depends on / 依赖: mdifferentiableAt_const, mdifferentiable_zeroSection
-/
theorem zero (hΦ : TensorialAt I F Φ x) : Φ 0 = 0 := by
  calc
    Φ 0 = Φ ((0 : M -> 𝕜) • (0 : Π x, V x)) := by simp
    _ = 0 • Φ 0 := hΦ.smul mdifferentiableAt_const (mdifferentiable_zeroSection ..)
    _ = 0 := by simp

/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  statement: (hΦ : TensorialAt I F Φ x) {ι : Type*} {s : Finset ι} (σ : ι -> Π x : M, V x)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact hΦ.zero
  | insert a s ha h =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
      simp only [Finset.sum_insert ha, ← h hσ.2]
      exact hΦ.add (hσ.1) (.sum_section hσ.2)

中文:
定理 求和
  结论: (hΦ : TensorialAt I F Φ x) {ι : 类型} {s : 有限集 ι} (σ : ι -> Π x : M, V x)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact hΦ.zero
  | insert a s ha h =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
      simp only [Finset.sum_insert ha, ← h hσ.2]
      exact hΦ.add (hσ.1) (.sum_section hσ.2)

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, Finset.sum_empty, Finset.sum_insert, classical, forall_eq_or_imp, induction_on, insert, mem_insert, sum_empty, sum_insert, sum_section
-/
theorem sum (hΦ : TensorialAt I F Φ x) {ι : Type*} {s : Finset ι} (σ : ι -> Π x : M, V x)
    (hσ : forall i in s, MDiffAt (T% (σ i)) x) :
    Φ (fun x' => ∑ i in s, σ i x') = ∑ i in s, Φ (σ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact hΦ.zero
  | insert a s ha h =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
      simp only [Finset.sum_insert ha, ← h hσ.2]
      exact hΦ.add (hσ.1) (.sum_section hσ.2)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F']
  [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 1 F' V' I]

/--
lemma `pointwise` / 引理 `pointwise`

English:
lemma pointwise
  statement: (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
  proof: by
  -- Select a local frame `s` for the bundle `V` near `x`,
  -- and let `c` be the family of linear maps evaluating the coefficients of a section relative to
  -- this frame
  let t := trivializationAt F V x
  have x_mem : x in t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  let b :

中文:
引理 pointwise
  结论: (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
  证明: by
  -- Select a local frame `s` for the bundle `V` near `x`,
  -- and let `c` be the family of linear maps evaluating the coefficients of a section relative to
  -- this frame
  let t := trivializationAt F V x
  have x_mem : x in t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  let b :
-/
lemma pointwise (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : σ x = σ' x) :
    Φ σ = Φ σ' := by
  -- Select a local frame `s` for the bundle `V` near `x`,
  -- and let `c` be the family of linear maps evaluating the coefficients of a section relative to
  -- this frame
  let t := trivializationAt F V x
  have x_mem : x in t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  let b := Basis.ofVectorSpace 𝕜 F
  let s := t.localFrame b
  let c := t.localFrameCoeff I b
  have hs (i) : MDiffAt (T% (s i)) x :=
    (contMDiffAt_localFrame_of_mem 1 _ b i x_mem).mdifferentiableAt (by simp)
  have hc {σ : (x : M) -> V x} (hσ : MDiffAt (T% σ) x) (i) :
      MDiffAt (LinearMap.piApply (c i) σ) x :=
    mdifferentiableAt_localFrameCoeff b x_mem hσ i
  -- By the locality of the operation `(Φ · x)`, its value on `σ` agrees with the value of `Φ` on
  -- the expansion of `σ` into coefficients relative to the frame.
  have hΦ_eq {σ : (x : M) -> V x} (hσ : MDiffAt (T% σ) x) :
      Φ σ = Φ (fun x' => ∑ i, c i x' (σ x') • s i x') :=
    hΦ.local hσ
      (.sum_section fun i _ => (hc hσ i).smul_section (hs i))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem)
  -- Now evaluate using the tensoriality properties.
  rw [hΦ_eq hσ]; rw [hΦ_eq hσ']; rw [hΦ.sum]; rw [hΦ.sum]
  · congr! 1 with i
    calc Φ ((LinearMap.piApply (c i) σ) • (s i))
        = c i x (σ x) • Φ (s i) := hΦ.smul (hc hσ i) (hs i)
      _ = c i x (σ' x) • Φ (s i) := by rw [hσσ']
      _ = Φ ((LinearMap.piApply (c i) σ') • (s i)) :=
.symm hΦ.smul (hc hσ' i) (hs i)
  · exact fun i _ => (hc hσ' i).smul_section (hs i)
  · exact fun i _ => (hc hσ i).smul_section (hs i)

/--
lemma `pointwise₂` / 引理 `pointwise₂`

English:
lemma pointwise₂
  proof: by
  trans Φ σ' τ
  · exact (hΦ₁ _ hτ).pointwise hσ hσ' hσσ'
  · exact (hΦ₂ _ hσ').pointwise hτ hτ' hττ'

中文:
引理 pointwise₂
  证明: by
  trans Φ σ' τ
  · exact (hΦ₁ _ hτ).pointwise hσ hσ' hσσ'
  · exact (hΦ₂ _ hσ').pointwise hτ hτ' hττ'

Depends on / 依赖: pointwise
-/
lemma pointwise₂
    {Φ : (Π x : M, V x) -> (Π x : M, V' x) -> A} {x}
    (hΦ₁ : forall τ, MDiffAt (T% τ) x -> TensorialAt I F (Φ · τ) x)
    (hΦ₂ : forall σ, MDiffAt (T% σ) x -> TensorialAt I F' (Φ σ ·) x)
    {σ σ' : Π x : M, V x} {τ τ' : Π x : M, V' x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hτ : MDiffAt (T% τ) x) (hτ' : MDiffAt (T% τ') x)
    (hσσ' : σ x = σ' x) (hττ' : τ x = τ' x) :
    Φ σ τ = Φ σ' τ' := by
  trans Φ σ' τ
  · exact (hΦ₁ _ hτ).pointwise hσ hσ' hσσ'
  · exact (hΦ₂ _ hσ').pointwise hτ hτ' hττ'

variable [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul 𝕜 A]

/--
Definition of `mkHom` / `mkHom` 的定义

English:
definition mkHom
  body: have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : IsTopologicalAddGroup (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toContinuousAddEquiv.isTopologicalAddGroup
  have (x : M) : ContinuousSMul 𝕜 (V x)

中文:
定义 mkHom
  定义体: have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : IsTopologicalAddGroup (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toContinuousAddEquiv.isTopologicalAddGroup
  have (x : M) : ContinuousSMul 𝕜 (V x)

Depends on / 依赖: ContinuousSMul, FiberBundle, FiberBundle.t2Space, FiniteDimensional, IsTopologicalAddGroup, LinearMap, LinearMap.toContinuousLinearMap, T2Space, VectorBundle, VectorBundle.continuousLinearEquivAt, VectorBundle.finiteDimensional, continuousLinearEquivAt, continuousSMul, extend, finiteDimensional, isTopologicalAddGroup, map_add, mdifferentiableAt_e, mdifferentiableAt_extend, t2Space
-/
noncomputable def mkHom
    -- `Φ` and `x` explicit to make it easier to generate the side condition at point of use
    (Φ : (Π x : M, V x) -> A) (x : M) (hΦ : TensorialAt I F Φ x) :
    V x ->L[𝕜] A :=
  have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : IsTopologicalAddGroup (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toContinuousAddEquiv.isTopologicalAddGroup
  have (x : M) : ContinuousSMul 𝕜 (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).continuousSMul
  LinearMap.toContinuousLinearMap {
    toFun v := Φ (extend F v)
    map_add' v₁ v₂ := by
      rw [← hΦ.add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
apply hΦ.pointwise (mdifferentiableAt_extend ..)
        mdifferentiableAt_add_section (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
      simp
    map_smul' c v := by
      dsimp
      rw [← hΦ.smul (f := fun _ => c) (mdifferentiable_const ..) (mdifferentiableAt_extend ..)]
apply hΦ.pointwise (mdifferentiableAt_extend ..)
        mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)
      simp }

/--
theorem `mkHom_apply` / 定理 `mkHom_apply`

English:
theorem mkHom_apply
  statement: {Φ : (Π x : M, V x) -> A} {x} (hΦ : TensorialAt I F (Φ ·) x)
  proof: hΦ.pointwise (mdifferentiableAt_extend ..) hσ (by simp)

中文:
定理 mkHom_apply
  结论: {Φ : (Π x : M, V x) -> A} {x} (hΦ : TensorialAt I F (Φ ·) x)
  证明: hΦ.pointwise (mdifferentiableAt_extend ..) hσ (by simp)

Depends on / 依赖: mdifferentiableAt_extend, pointwise
-/
theorem mkHom_apply {Φ : (Π x : M, V x) -> A} {x} (hΦ : TensorialAt I F (Φ ·) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    mkHom Φ x hΦ (σ x) = Φ σ :=
  hΦ.pointwise (mdifferentiableAt_extend ..) hσ (by simp)

/--
theorem `mkHom_apply_eq_extend` / 定理 `mkHom_apply_eq_extend`

English:
theorem mkHom_apply_eq_extend
  given: {Φ : (Π x : M, V x) -> A} {x} (hΦ : TensorialAt I F Φ x) (σ : V x)
  proof: rfl

中文:
定理 mkHom_apply_eq_extend
  条件: {Φ : (Π x : M, V x) -> A} {x} (hΦ : TensorialAt I F Φ x) (σ : V x)
  证明: rfl
-/
theorem mkHom_apply_eq_extend {Φ : (Π x : M, V x) -> A} {x} (hΦ : TensorialAt I F Φ x) (σ : V x) :
    mkHom Φ x hΦ σ = Φ (extend F σ) :=
  rfl

/--
Definition of `mkHom₂` / `mkHom₂` 的定义

English:
definition mkHom₂
  body: have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : T2Space (V' x) := FiberBundle.t2Space F' V' x
  have : FiniteDimensional 𝕜 (V' x) := VectorBundle.finiteDimensional 𝕜 F' V' x
  have : IsTopologicalAddGroup (V x) :

中文:
定义 mkHom₂
  定义体: have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : T2Space (V' x) := FiberBundle.t2Space F' V' x
  have : FiniteDimensional 𝕜 (V' x) := VectorBundle.finiteDimensional 𝕜 F' V' x
  have : IsTopologicalAddGroup (V x) :

Depends on / 依赖: FiberBundle, FiberBundle.t2Space, FiniteDimensional, IsTopologicalAddGroup, T2Space, VectorBundle, VectorBundle.continuousLinearEquivAt, VectorBundle.finiteDimensional, continuousLinearEquivAt, finiteDimensional, isTopol, isTopologicalAddGroup, t2Space, toContinuousAddEquiv, toContinuousAddEquiv.isTopol, toContinuousAddEquiv.isTopologicalAddGroup
-/
noncomputable def mkHom₂
    -- `Φ` and `x` explicit to make it easier to generate the side conditions at point of use
    (Φ : (Π x : M, V x) -> (Π x : M, V' x) -> A) (x : M)
    (hΦ₁ : forall τ, MDiffAt (T% τ) x -> TensorialAt I F (Φ · τ) x)
    (hΦ₂ : forall σ, MDiffAt (T% σ) x -> TensorialAt I F' (Φ σ) x) :
    V x ->L[𝕜] V' x ->L[𝕜] A :=
  have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : T2Space (V' x) := FiberBundle.t2Space F' V' x
  have : FiniteDimensional 𝕜 (V' x) := VectorBundle.finiteDimensional 𝕜 F' V' x
  have : IsTopologicalAddGroup (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toContinuousAddEquiv.isTopologicalAddGroup
  have : IsTopologicalAddGroup (V' x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F' V' x).toContinuousAddEquiv.isTopologicalAddGroup
  have (x : M) : ContinuousSMul 𝕜 (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).continuousSMul
  have (x : M) : ContinuousSMul 𝕜 (V' x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F' V' x).continuousSMul
  have H : IsBilinearMap 𝕜
    (fun (v : V x) (w : V' x) => Φ (extend F v) (extend F' w)) :=
  { add_left v₁ v₂ w := by
      rw [← (hΦ₁ _ (mdifferentiableAt_extend ..)).add (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..) _
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..) _ rfl
      · exact mdifferentiableAt_add_section (mdifferentiableAt_extend ..)
          (mdifferentiableAt_extend ..)
      · simp
    smul_left c v w := by
      rw [← (hΦ₁ _ (mdifferentiableAt_extend ..)).smul (f := fun _ => c) (mdifferentiable_const ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..)
        (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..))
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
      · simp
      · rfl
    add_right v w₁ w₂ := by
      rw [← (hΦ₂ _ (mdifferentiableAt_extend ..)).add (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..)
(mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
        mdifferentiableAt_add_section (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
      · rfl
      · simp
    smul_right c v w := by
      rw [← (hΦ₂ _ (mdifferentiableAt_extend ..)).smul (f := fun _ => c) (mdifferentiable_const ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..)
(mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
        mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)
      · rfl
      · simp }
  H.toLinearMap.toContinuousBilinearMap

/--
theorem `mkHom₂_apply` / 定理 `mkHom₂_apply`

English:
theorem mkHom₂_apply
  proof: TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..) hσ (mdifferentiableAt_extend ..) hτ
    (by simp) (by simp)

中文:
定理 mkHom₂_apply
  证明: TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..) hσ (mdifferentiableAt_extend ..) hτ
    (by simp) (by simp)

Depends on / 依赖: TensorialAt, TensorialAt.pointwise, mdifferentiableAt_extend
-/
theorem mkHom₂_apply
    {Φ : (Π x : M, V x) -> (Π x : M, V' x) -> A} {x}
    (hΦ₁ : forall τ, MDiffAt (T% τ) x -> TensorialAt I F (Φ · τ) x)
    (hΦ₂ : forall σ, MDiffAt (T% σ) x -> TensorialAt I F' (Φ σ) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) {τ : Π x : M, V' x} (hτ : MDiffAt (T% τ) x) :
    mkHom₂ Φ x hΦ₁ hΦ₂ (σ x) (τ x) = Φ σ τ :=
  TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..) hσ (mdifferentiableAt_extend ..) hτ
    (by simp) (by simp)

/--
theorem `mkHom₂_apply_eq_extend` / 定理 `mkHom₂_apply_eq_extend`

English:
theorem mkHom₂_apply_eq_extend
  proof: rfl

中文:
定理 mkHom₂_apply_eq_extend
  证明: rfl
-/
theorem mkHom₂_apply_eq_extend
    {Φ : (Π x : M, V x) -> (Π x : M, V' x) -> A} {x}
    (hΦ₁ : forall τ, MDiffAt (T% τ) x -> TensorialAt I F (Φ · τ) x)
    (hΦ₂ : forall σ, MDiffAt (T% σ) x -> TensorialAt I F' (Φ σ) x)
    (σ : V x) (τ : V' x) :
    mkHom₂ Φ x hΦ₁ hΦ₂ σ τ = Φ (extend F σ) (extend F' τ) :=
  rfl

end TensorialAt
