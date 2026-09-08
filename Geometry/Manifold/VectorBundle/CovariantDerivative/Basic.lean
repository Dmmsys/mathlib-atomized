/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# Covariant derivatives

This file defines covariant derivatives (aka Koszul connections) on vector bundles over manifolds.

There are versions of the story: a local unbundled one and a global bundled one.
The local version is used by the global version but also (in other files) when
seeing a global object in a local trivialization.

In the whole file `M` is a manifold over any nontrivially normed field `𝕜` and `V` is
a vector bundle over `M` with model fiber `F`.

## Main definitions and constructions

* `IsCovariantDerivativeOn`: A function from sections of a vector bundle `V` over a manifold `M` to
  sections of $Hom(TM, V)$ is a *covariant derivative* on a set `s` in `M` if it is additive and
  satisfies the Leibniz rule when applied to sections that are differentiable at a point of `s`.
* `ContMDiffCovariantDerivativeOn`: A covariant derivative ∇ on some set is called *of class* `C^k`
  iff, whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇_X σ` is a `C^k`
  section. This is a class so typeclass inference can deduce this automatically.
* `IsCovariantDerivativeOn.add_one_form`: Adding a one-form taking values in the endomorphisms of
  the vector bundle to a covariant derivative on a set gives a covariant derivative on that set.
* `IsCovariantDerivativeOn.difference`: The difference of two covariant derivatives on a set,
  as a one-form taking values in the endomorphism bundle.
* `CovariantDerivative`: a globally defined covariant derivative on a vector bundle, as a bundled
  object.
* `ContMDiffCovariantDerivative`: A covariant derivative ∇ is called *of class* `C^k`
  iff, whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇_X σ` is a `C^k`
  section. This is a class so typeclass inference can deduce this automatically.
* `CovariantDerivative.addOneForm`: Adding a one-form taking values in the endomorphisms of the
  vector bundle to a covariant derivative gives a covariant derivative.
* `CovariantDerivative.difference`: The difference of two covariant derivatives, as a one-form
  taking values in the endomorphism bundle.

## Implementation notes

On paper there are several equivalent ways to define covariant derivatives on a vector bundle
`V → M`. The most common one starts with a function `∇` taking as input a global smooth vector field
`X` and a global smooth section `σ` and giving as output a global smooth section `∇_X σ`, before
proving the result that `(∇_X σ) x` at a point `x` only depends on the value of the vector field at
that point and the 1-jet of the section at that point.

Here we ask for a map sending a global section `σ` of `V` to a global section `∇ σ` of `Hom(TM, V)`.
So the fact that `(∇_X σ) x` depends only on `X x` is baked into the definition.
Note also that we don’t put any differentiability restriction on `σ` and `X`, the type of
the covariant derivative map is simply `(Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))`.
But the conditions on this map involve differentiability, see the definition of
`IsCovariantDerivativeOn`.

This file proves that `(∇_X σ) x` depends only on the germ of `σ` at `x`, but not the stronger
statement that it depends only the 1-jet of `σ` at `x`. This will be proved in a later file.
-/

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public noncomputable section

/-! ## Local unbundled theory -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

/-- A function from sections of a vector bundle `V` on a manifold `M` to sections of $Hom(TM, E)$
is a *covariant derivative* over a set `s` in `M` if it is additive and satisfies the Leibniz rule
when applied to sections that are differentiable at a point of `s`.

Caution, the argument order is nonstandard: `cov σ x (X x)` corresponds to `∇_X σ x` on paper.
-/
/-
**IsCovariantDerivativeOn** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：IsCovariantDerivativeOn (cov : (Π x : M, V x) -> (Π x : M, TangentSpace I 
x ->L[𝕜] V x)) (s : Set M
参数：cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from sections of a vector bundle `V` on a manifold `M` to sections of
 $Hom(TM, E)$
is a *covariant derivative* over a set `s` in `M` if it is additive and satisfie
s the Leibniz rule
when applied to sections that are differentiable at a point of `s`.

Caution, the argument order is nonstandard: `cov σ x (X x)` corresponds to `∇_X 
σ x` on paper.
-/
structure IsCovariantDerivativeOn
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (s : Set M := Set.univ) : Prop where
  add {σ σ' : Π x : M, V x} {x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hx : x ∈ s := by trivial) :
    cov (σ + σ') x = cov σ x + cov σ' x
  leibniz {σ : Π x : M, V x} {g : M → 𝕜} {x}
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x ∈ s := by trivial) :
    cov (g • σ) x = g x • cov σ x + (d% g x).smulRight (σ x)

/--
A covariant derivative ∇ is called of class `C^k` iff, whenever `X` is a `C^k` section and `σ` a
`C^{k+1}` section, the result `∇_X σ` is a `C^k` section. This is a class so typeclass inference can
deduce this automatically. We will prove in a later file that any `C^(k+1)` covariant derivative
is `C^k`.
-/
/-
**ContMDiffCovariantDerivativeOn** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：ContMDiffCovariantDerivativeOn [IsManifold I 1 M] [VectorBundle 𝕜 F V] (k 
: Nat∞ω) (cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)) (u : S
et M) where contMDiff : forall {σ : Π x : M, V x}, CMDiff[u] (k + 1) (T% σ) -> l
etI cov (x : M) : TotalSpace (E ->L[𝕜] F) fun x => TangentSpace I x ->L[𝕜] V x
参数：k : Nat∞ω；cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)；u : 
Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A covariant derivative ∇ is called of class `C^k` iff, whenever `X` is a `C^k` s
ection and `σ` a
`C^{k+1}` section, the result `∇_X σ` is a `C^k` section. This is a class so typ
eclass inference can
deduce this automatically. We will prove in a later file that any `C^(k+1)` cova
riant derivative
is `C^k`.
-/
class ContMDiffCovariantDerivativeOn [IsManifold I 1 M] [VectorBundle 𝕜 F V] (k : ℕ∞ω)
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (u : Set M) where
  contMDiff : ∀ {σ : Π x : M, V x}, CMDiff[u] (k + 1) (T% σ) →
    letI cov (x : M) : TotalSpace (E →L[𝕜] F) fun x ↦ TangentSpace I x →L[𝕜] V x := ⟨x, cov σ x⟩
    ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) k cov u
    -- TODO elaborators are not working here. We want to use `T% (cov σ)` and CMDiff[u] k f

variable {F}

namespace IsCovariantDerivativeOn

/-! ### Changing set

In this section, we change `s` in `IsCovariantDerivativeOn F cov s`, proving the condition is
monotone and local.
-/

section changing_set

/-
**IsCovariantDerivativeOn.mono** 是 Mathlib 中的一个引理，位于命名空间 `IsCovariantDerivativeO
n`。
形式化陈述：mono {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)} {s t
 : Set M} (hcov : IsCovariantDerivativeOn F cov t) (hst : s subseteq t) : IsCova
riantDerivativeOn F cov s where add hσ hσ' hx
参数：Π x : M, V x；Π x : M, TangentSpace I x ->L[𝕜] V x；hcov : IsCovariantDerivativ
eOn F cov t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCovariantDerivativeOn.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `IsCovariantDerivativeOn.leibniz`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
-/
lemma mono
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s t : Set M}
    (hcov : IsCovariantDerivativeOn F cov t) (hst : s ⊆ t) : IsCovariantDerivativeOn F cov s where
  add hσ hσ' hx := hcov.add hσ hσ' (hst hx)
  leibniz hσ hcov' hx := hcov.leibniz hσ hcov' (hst hx)
/-
**IsCovariantDerivativeOn.iUnion** 是 Mathlib 中的一个引理，位于命名空间 `IsCovariantDerivativ
eOn`。
形式化陈述：iUnion {ι : Type*} {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L
[𝕜] V x)} {s : ι -> Set M} (hcov : forall i, IsCovariantDerivativeOn F cov (s i)
) : IsCovariantDerivativeOn F cov (⋃ i, s i) where add hσ hσ' hx
参数：Π x : M, V x；Π x : M, TangentSpace I x ->L[𝕜] V x；hcov : forall i, IsCovarian
tDerivativeOn F cov (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsCovariantDerivativeOn.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsCovariantDerivativeOn.leibniz`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
-/
lemma iUnion {ι : Type*} {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {s : ι → Set M} (hcov : ∀ i, IsCovariantDerivativeOn F cov (s i)) :
    IsCovariantDerivativeOn F cov (⋃ i, s i) where
  add hσ hσ' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).add hσ hσ'
  leibniz hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).leibniz hσ hf'

end changing_set

-- TODO: prove that `cov σ x` depends on `σ` only via the 1-jet of `σ` at `x`.
-- This will be easy using the projection formula about Ehresmann connections,
-- which will be added in the planned file `CovariantDerivative/Ehresmann.lean`.
-- In the mean-time we use the following weaker results (which are convenient to apply anyway).

/-- Given a covariant derivative `cov` on a neighborhood `s` of a point `x`, if sections `σ` and
`σ'` agree on `s` and are differentiable at `x`, then `cov σ x = cov σ x'`. -/
/-
**IsCovariantDerivativeOn.congr_of_eqOn** 是 Mathlib 中的一个引理，位于命名空间 `IsCovariantDe
rivativeOn`。
形式化陈述：congr_of_eqOn {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V
 x)} {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) {σ σ' : Π x : M, V x} 
{x : M} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hxs : s in 𝓝 x) (hσσ'
 : forall x in s, σ x = σ' x) : cov σ x = cov σ' x
参数：Π x : M, V x；Π x : M, TangentSpace I x ->L[𝕜] V x；hcov : IsCovariantDerivativ
eOn F cov s；hσ : MDiffAt (T% σ) x；hσ' : MDiffAt (T% σ') x；hxs : s in 𝓝 x；hσσ' : 
forall x in s, σ x = σ' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `hasMFDerivAt_const`：hasMFDerivAt_const (c : M') (x : M) : HasMFDerivAt% 
(fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] TangentSpace% c)
· 使用定理 `HasMFDerivAt.congr_of_eventuallyEq`：HasMFDerivAt.congr_of_eventuallyEq (
h : HasMFDerivAt% f x f') (h₁ : f₁ =ᶠ[𝓝 x] f) : HasMFDerivAt% f₁ x f'
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsCovariantDerivativeOn.leibniz`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `ContinuousLinearMap.smulRight.congr_simp`：∀ {M₁ : Type u_4} [inst : Topo
logicalSpace M₁] [inst_1 : AddCommMonoid M₁] {M₂ : Type u_6}   [inst_2 : Topolog
icalSpace M₂] [inst_3 : AddCom…
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
· 使用定理 `ContinuousLinearMap.zero_smulRight`：zero_smulRight {x : M₂} : (0 : M₁ ->
L[R] S).smulRight x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Given a covariant derivative `cov` on a neighborhood `s` of a point `x`, if sect
ions `σ` and
`σ'` agree on `s` and are differentiable at `x`, then `cov σ x = cov σ x'`.
-/
lemma congr_of_eqOn
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ σ' : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hxs : s ∈ 𝓝 x) (hσσ' : ∀ x ∈ s, σ x = σ' x) :
    cov σ x = cov σ' x := by
  classical
  have hxs' : x ∈ s := mem_of_mem_nhds hxs
  let ψ (x' : M) : 𝕜 := if x' ∈ s then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hxs']
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have H (x' : M) : ((ψ : M → 𝕜) • σ) x' = ((ψ : M → 𝕜) • σ') x' := by
    dsimp [ψ]
    split_ifs with hx's
    · simpa using hσσ' _ hx's
    · simp
  have hψ' : HasMFDerivAt I 𝓘(𝕜) ψ x 0 := by
    have : HasMFDerivAt I 𝓘(𝕜, 𝕜) (fun (_x : M) ↦ (1 : 𝕜)) x 0 := hasMFDerivAt_const ..
    refine this.congr_of_eventuallyEq ?_
    apply Filter.eventuallyEq_of_mem hxs
    intro t ht
    simp [ψ, ht]
  have := hcov.leibniz hσ hψ'.mdifferentiableAt
  -- Then, it's a chain of (dependent) equalities.
  calc cov σ x
    _ = cov ((ψ : M → 𝕜) • σ) x := by
      simp [hcov.leibniz hσ hψ'.mdifferentiableAt, hψx, mvfderiv, hψ'.mfderiv]
    _ = cov ((ψ : M → 𝕜) • σ') x := by rw [funext H]
    _ = cov σ' x := by
      simp [hcov.leibniz hσ' hψ'.mdifferentiableAt, hψx, mvfderiv, hψ'.mfderiv]

open Filter Set in
/-- Given a covariant derivative `cov` on a neighborhood `s` of a point `x`, if sections `σ` and
`σ'` agree near `x` and are differentiable at `x`, then `cov σ x = cov σ x'`. -/
/-
**IsCovariantDerivativeOn.congr_of_eventuallyEq** 是 Mathlib 中的一个引理，位于命名空间 `IsCov
ariantDerivativeOn`。
形式化陈述：congr_of_eventuallyEq {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x 
->L[𝕜] V x)} {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) {σ σ' : Π x : 
M, V x} {x : M} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hxs : s in 𝓝 
x) (hσσ' : forallᶠ x in 𝓝 x, σ x = σ' x) : cov σ x = cov σ' x
参数：Π x : M, V x；Π x : M, TangentSpace I x ->L[𝕜] V x；hcov : IsCovariantDerivativ
eOn F cov s；hσ : MDiffAt (T% σ) x；hσ' : MDiffAt (T% σ') x；hxs : s in 𝓝 x；hσσ' : 
forallᶠ x in 𝓝 x, σ x = σ' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCovariantDerivativeOn.congr_of_eqOn`：congr_of_eqOn {cov : (Π x : M, V 
x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)} {s : Set M} (hcov : IsCovariantDer
ivativeOn F cov s) {σ σ' : …
· 使用引理 `IsCovariantDerivativeOn.mono`：mono {cov : (Π x : M, V x) -> (Π x : M, Ta
ngentSpace I x ->L[𝕜] V x)} {s t : Set M} (hcov : IsCovariantDerivativeOn F cov 
t) (hst : s subset…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Given a covariant derivative `cov` on a neighborhood `s` of a point `x`, if sect
ions `σ` and
`σ'` agree near `x` and are differentiable at `x`, then `cov σ x = cov σ x'`.
-/
lemma congr_of_eventuallyEq
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ σ' : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hxs : s ∈ 𝓝 x) (hσσ' : ∀ᶠ x in 𝓝 x, σ x = σ' x) :
    cov σ x = cov σ' x := by
  rw [eventually_iff_exists_mem] at hσσ'
  choose s' hs' b using hσσ'
  exact (hcov.mono inter_subset_left).congr_of_eqOn hσ hσ' (inter_mem hxs hs') fun x hx ↦ b x hx.2

/-! ### Computational properties -/

section computational_properties

variable {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}

/-
**IsCovariantDerivativeOn.zero** 是 Mathlib 中的一个引理，位于命名空间 `IsCovariantDerivativeO
n`。
形式化陈述：zero [VectorBundle 𝕜 F V] (hcov : IsCovariantDerivativeOn F cov s) {x} (hx
 : x in s
参数：hcov : IsCovariantDerivativeOn F cov s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsCovariantDerivativeOn.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `Bundle.mdifferentiableAt_zeroSection`：mdifferentiableAt_zeroSection {x :
 B} : MDiffAt (zeroSection F E) x
-/
lemma zero [VectorBundle 𝕜 F V] (hcov : IsCovariantDerivativeOn F cov s)
    {x} (hx : x ∈ s := by trivial) :
    cov 0 x = 0 := by
  simpa using (hcov.add (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : cov (0 + 0) x = _)
/-
**IsCovariantDerivativeOn.smul_const** 是 Mathlib 中的一个定理，位于命名空间 `IsCovariantDeriv
ativeOn`。
形式化陈述：smul_const (hcov : IsCovariantDerivativeOn F cov s) {σ : Π x : M, V x} {x}
 (a : 𝕜) (hσ : MDiffAt (T% σ) x) (hx : x in s
参数：hcov : IsCovariantDerivativeOn F cov s；a : 𝕜；hσ : MDiffAt (T% σ) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.smulRight.congr_simp`：∀ {M₁ : Type u_4} [inst : Topo
logicalSpace M₁] [inst_1 : AddCommMonoid M₁] {M₂ : Type u_6}   [inst_2 : Topolog
icalSpace M₂] [inst_3 : AddCom…
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderiv_const`：mfderiv_const : mfderiv% (fun _ : M => c) x = (0 : Tangen
tSpace% x ->L[𝕜] TangentSpace% c)
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
· 使用定理 `ContinuousLinearMap.zero_smulRight`：zero_smulRight {x : M₂} : (0 : M₁ ->
L[R] S).smulRight x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsCovariantDerivativeOn.leibniz`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
-/
theorem smul_const (hcov : IsCovariantDerivativeOn F cov s)
    {σ : Π x : M, V x} {x} (a : 𝕜)
    (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    cov (a • σ) x = a • cov σ x := by
  simpa [mvfderiv] using! hcov.leibniz (g := fun _ ↦ a) hσ mdifferentiableAt_const

end computational_properties

/-! ### Operations

In this section we prove that:

* affine combinations of covariant derivatives are covariant derivatives
* adding a one-form taking values in the endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. See `IsCovariantDerivativeOn.add_one_form`.
* subtracting two covariant derivatives on some set gives a one-form taking values in
  the endomorphisms of the vector bundle. See `IsCovariantDerivativeOn.difference`.

Note: morally this means covariant derivatives form an affine space over the vector space of
one-forms taking values in the endomorphisms of the bundle, but we don’t package it that way yet.
-/
section operations

variable {s : Set M} {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}

/-- An affine combination of covariant derivatives is a covariant derivative. -/
@[simps]
/-
**IsCovariantDerivativeOn.affine_combination** 是 Mathlib 中的一个引理，位于命名空间 `IsCovari
antDerivativeOn`。
形式化陈述：affine_combination (hcov : IsCovariantDerivativeOn F cov s) {cov' : (Π x :
 M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)} (hcov' : IsCovariantDerivati
veOn F cov' s) (g : M -> 𝕜) : IsCovariantDerivativeOn F (fun σ => (g • (cov σ)) 
+ (1 - g) • (cov' σ)) s where add hσ hσ' hx
参数：hcov : IsCovariantDerivativeOn F cov s；Π x : M, V x；Π x : M, TangentSpace I x
 ->L[𝕜] V x；hcov' : IsCovariantDerivativeOn F cov' s；g : M -> 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsCovariantDerivativeOn.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
An affine combination of covariant derivatives is a covariant derivative.
-/
lemma affine_combination (hcov : IsCovariantDerivativeOn F cov s)
    {cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov' : IsCovariantDerivativeOn F cov' s) (g : M → 𝕜) :
    IsCovariantDerivativeOn F (fun σ ↦ (g • (cov σ)) + (1 - g) • (cov' σ)) s where
  add hσ hσ' hx := by
    simp [hcov.add hσ hσ', hcov'.add hσ hσ']
    module
  leibniz hσ hφ hx := by
    simp [hcov.leibniz hσ hφ, hcov'.leibniz hσ hφ]
    module

/-- An affine combination of two `C^k` connections is a `C^k` connection. -/
/-
**IsCovariantDerivativeOn._root_.ContMDiffCovariantDerivativeOn.affine_combinati
on** 是 Mathlib 中的一个引理，位于命名空间 `IsCovariantDerivativeOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine combination of two `C^k` connections is a `C^k` connection.
-/
lemma _root_.ContMDiffCovariantDerivativeOn.affine_combination [IsManifold I 1 M]
    [VectorBundle 𝕜 F V]
    {cov cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {u : Set M} {f : M → 𝕜} {n : ℕ∞ω} (hf : CMDiff[u] n f)
    (Hcov : ContMDiffCovariantDerivativeOn (F := F) n cov u)
    (Hcov' : ContMDiffCovariantDerivativeOn (F := F) n cov' u) :
    ContMDiffCovariantDerivativeOn F n (fun σ ↦ (f • (cov σ)) + (1 - f) • (cov' σ)) u where
  contMDiff hσ := by
    apply ContMDiffOn.add_section
    · exact hf.smul_section <| Hcov.contMDiff hσ
    · exact (contMDiffOn_const.sub hf).smul_section <| Hcov'.contMDiff hσ

/-- A finite affine combination of covariant derivatives is a covariant derivative. -/
/-
**IsCovariantDerivativeOn.finite_affine_combination** 是 Mathlib 中的一个引理，位于命名空间 `I
sCovariantDerivativeOn`。
形式化陈述：finite_affine_combination {ι : Type*} {s : Finset ι} {u : Set M} {cov : ι 
-> (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)} (h : forall i, IsCo
variantDerivativeOn F (cov i) u) {f : ι -> M -> 𝕜} (hf : ∑ i in s, f i = 1) : Is
CovariantDerivativeOn F (fun σ x => ∑ i in s, (f i x) • (cov i) σ x) u where add
 hσ hσ' hx
参数：Π x : M, V x；Π x : M, TangentSpace I x ->L[𝕜] V x；h : forall i, IsCovariantDe
rivativeOn F (cov i) u；hf : ∑ i in s, f i = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `IsCovariantDerivativeOn.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsCovariantDerivativeOn.leibniz`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
A finite affine combination of covariant derivatives is a covariant derivative.
-/
lemma finite_affine_combination {ι : Type*} {s : Finset ι}
    {u : Set M} {cov : ι → (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (h : ∀ i, IsCovariantDerivativeOn F (cov i) u) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    IsCovariantDerivativeOn F (fun σ x ↦ ∑ i ∈ s, (f i x) • (cov i) σ x) u where
  add hσ hσ' hx := by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    rw [← smul_add, (h i).add hσ hσ' hx]
  leibniz {σ g x} hσ hg hx := by
    calc ∑ i ∈ s, f i x • cov i (g • σ) x
      _ = ∑ i ∈ s, (g x • f i x • cov i σ x + f i x • (d% g x).smulRight (σ x)) := by
          congr! 1 with i hi
          rw [(h i).leibniz hσ hg]
          simp [mvfderiv]
          module
      _ = g x • ∑ i ∈ s, f i x • cov i σ x + (∑ i ∈ s, f i) x • (d% g x).smulRight (σ x) := by
          rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul]
      _ = g x • ∑ i ∈ s, f i x • cov i σ x + (d% g x).smulRight (σ x) := by rw [hf]; simp

/-- An affine combination of finitely many `C^k` connections on `u` is a `C^k` connection on `u`. -/
/-
**IsCovariantDerivativeOn._root_.ContMDiffCovariantDerivativeOn.finite_affine_co
mbination** 是 Mathlib 中的一个引理，位于命名空间 `IsCovariantDerivativeOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine combination of finitely many `C^k` connections on `u` is a `C^k` conne
ction on `u`.
-/
lemma _root_.ContMDiffCovariantDerivativeOn.finite_affine_combination [IsManifold I 1 M]
    {n : ℕ∞ω} [VectorBundle 𝕜 F V] {ι : Type*} {s : Finset ι} {u : Set M}
    {cov : ι → (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivativeOn F n (cov i) u)
    {f : ι → M → 𝕜} (hf : ∀ i ∈ s, CMDiff[u] n (f i)) :
    ContMDiffCovariantDerivativeOn F n (fun σ x ↦ ∑ i ∈ s, (f i x) • (cov i) σ x) u where
  contMDiff {σ} hσ := by
    simpa using ContMDiffOn.sum_section
      (fun i hi ↦ (hf i hi).smul_section <| (hcov i hi).contMDiff hσ)

/-- Adding a one-form taking values in the endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. -/
/-
**IsCovariantDerivativeOn.add_one_form** 是 Mathlib 中的一个引理，位于命名空间 `IsCovariantDer
ivativeOn`。
形式化陈述：add_one_form (hcov : IsCovariantDerivativeOn F cov s) (A : Π x : M, V x ->
L[𝕜] TangentSpace I x ->L[𝕜] V x) : IsCovariantDerivativeOn F (fun σ x => cov σ 
x + A x (σ x)) s where add hσ hσ' hx
参数：hcov : IsCovariantDerivativeOn F cov s；A : Π x : M, V x ->L[𝕜] TangentSpace I
 x ->L[𝕜] V x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsCovariantDerivativeOn.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basi
c.0.IsCovariantDerivativeOn.add_one_form._abel_1_1`：∀ {𝕜 : Type u_3} [inst : Non
triviallyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `IsCovariantDerivativeOn.leibniz`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Adding a one-form taking values in the endomorphisms of the vector bundle to a c
ovariant
  derivative gives a covariant derivative.
-/
lemma add_one_form (hcov : IsCovariantDerivativeOn F cov s)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) :
    IsCovariantDerivativeOn F (fun σ x ↦ cov σ x + A x (σ x)) s where
  add hσ hσ' hx := by
    simp [hcov.add hσ hσ']
    abel
  leibniz hσ hg hx := by
    simp [hcov.leibniz hσ hg]
    module

section difference

/-- The difference of two covariant derivatives, as a function `Γ(V) → Γ(Hom(TM, V))`.
Future lemmas will upgrade this to a one-form taking values in the endomorphisms of `V`. -/
/-
**IsCovariantDerivativeOn.differenceAux** 是 Mathlib 中的一个定义，位于命名空间 `IsCovariantDe
rivativeOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The difference of two covariant derivatives, as a function `Γ(V) → Γ(Hom(TM, V))
`.
Future lemmas will upgrade this to a one-form taking values in the endomorphisms
 of `V`.
-/
private def differenceAux
    (cov cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)) :
    (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x) :=
  fun σ ↦ cov σ - cov' σ

variable
  {cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {s : Set M}
  (hcov : IsCovariantDerivativeOn F cov s)
  (hcov' : IsCovariantDerivativeOn F cov' s)
/-
**IsCovariantDerivativeOn.differenceAux_tensorial** 是 Mathlib 中的一个定理，位于命名空间 `IsC
ovariantDerivativeOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem differenceAux_tensorial (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (x : M) (hx : x ∈ s) : TensorialAt I F (differenceAux cov cov' · x) x where
  smul hf hσ := by
    simp [differenceAux, hcov.leibniz hσ hf, hcov'.leibniz hσ hf]
    module
  add hσ hσ' := by
    simp [differenceAux, hcov.add hσ hσ', hcov'.add hσ hσ']
    abel

-- We need more assumptions to use the tensoriality criterion in order to build the difference
-- operation.
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

open scoped Classical in
/-- The difference of two covariant derivatives, as a one-form taking values in the
endomorphisms of `V`. -/
/-
**IsCovariantDerivativeOn.difference** 是 Mathlib 中的一个定义，位于命名空间 `IsCovariantDeriv
ativeOn`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     {I : ModelWithCorners 𝕜 E H} →                 {M : Type u_4} →            
       [inst_4 : TopologicalSpace M] →                     [inst_5 : ChartedSpac
e H M] →                       {F : Type u_5} →                         [inst_6 
: NormedAddCommGroup F] →                           [inst_7 : NormedSpace 𝕜 F] →
                             {V : M → Type u_6} →                               
[inst_8 : TopologicalSpace (Bundle.TotalSpace F V)] →                           
      [inst_9 : (x : M) → AddCommGroup (V x)] →                                 
  [inst_10 : (x : M) → _root_.Module 𝕜 (V x)] →                                 
    [inst_11 : (x : M) → TopologicalSpace (V x)] →                              
         [inst_12 : ∀ (x : M), IsTopologicalAddGroup (V x)] →                   
                      [inst_13 : ∀ (x : M), ContinuousSMul 𝕜 (V x)] →           
                                [inst_14 : FiberBundle F V] →                   
                          {cov cov' : ((x : M) → V x) → (x : M) → TangentSpace I
 x →L[𝕜] V x} →                                               {s : Set M} →     
                                            IsCovariantDerivativeOn F cov s →   
                                                IsCovariantDerivativeOn F cov' s
 →                                                     [CompleteSpace 𝕜] →      
                                                 [FiniteDimensional 𝕜 F] →      
                                                   [inst_17 : VectorBundle 𝕜 F V
] →                                                           [ContMDiffVectorBu
ndle 1 F V I] →                                                             (x :
 M) → V x →L[𝕜] TangentSpace I x →L[𝕜] V x
参数：Bundle.TotalSpace F V；x : M；V x；x : M；V x；x : M；V x；x : M；V x；x : M；V x；(x : 
M) → V x；x : M；x : M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basi
c.0.IsCovariantDerivativeOn.differenceAux_tensorial`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
The difference of two covariant derivatives, as a one-form taking values in the
endomorphisms of `V`.
-/
@[no_expose] def difference (x : M) : V x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  if hxs : x ∈ s then
    TensorialAt.mkHom _ x (differenceAux_tensorial hcov hcov' _ hxs)
  else
    0

@[simp]
/-
**IsCovariantDerivativeOn.difference_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsCovarian
tDerivativeOn`。
形式化陈述：difference_apply {x : M} (hx : x in s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basi
c.0.IsCovariantDerivativeOn.differenceAux_tensorial`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `TensorialAt.mkHom_apply`：mkHom_apply {Φ : (Π x : M, V x) -> A} {x} (hΦ :
 TensorialAt I F (Φ ·) x) {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) : mkHom Φ x
 hΦ (σ x) = Φ…
-/
lemma difference_apply {x : M} (hx : x ∈ s := by trivial) {σ : Π x, V x} (hσ : MDiffAt (T% σ) x) :
    difference hcov hcov' x (σ x) = cov σ x - cov' σ x := by
  simp only [difference, hx, reduceDIte]
  rw [TensorialAt.mkHom_apply _ hσ]
  rfl

end difference

end operations

end IsCovariantDerivativeOn

/-! ## Bundled global covariant derivatives -/

variable (I F V) in
/--
Bundled global covariant derivative on a vector bundle.
Caution, the argument order is nonstandard: `cov σ x (X x)` corresponds to `∇_X σ x` on paper.
-/
@[ext]
/-
**CovariantDerivative** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     ModelWithCorners 𝕜 E H →                 {M : Type u_4} →                  
 [inst_4 : TopologicalSpace M] →                     [ChartedSpace H M] →       
                (F : Type u_5) →                         [inst_6 : NormedAddComm
Group F] →                           [NormedSpace 𝕜 F] →                        
     (V : M → Type u_6) →                               [inst_8 : TopologicalSpa
ce (Bundle.TotalSpace F V)] →                                 [inst_9 : (x : M) 
→ AddCommGroup (V x)] →                                   [inst_10 : (x : M) → _
root_.Module 𝕜 (V x)] →                                     [inst_11 : (x : M) →
 TopologicalSpace (V x)] →                                       [∀ (x : M), IsT
opologicalAddGroup (V x)] →                                         [∀ (x : M), 
ContinuousSMul 𝕜 (V x)] →                                           [FiberBundle
 F V] → Type (max (max u_2 u_4) u_6)
参数：F : Type u_5；V : M → Type u_6；Bundle.TotalSpace F V；x : M；V x；x : M；V x；x : M
；V x；x : M；V x；x : M；V x；max (max u_2 u_4) u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled global covariant derivative on a vector bundle.
Caution, the argument order is nonstandard: `cov σ x (X x)` corresponds to `∇_X 
σ x` on paper.
-/
structure CovariantDerivative where
  /-- The covariant derivative as a function. -/
  toFun : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)
  isCovariantDerivativeOnUniv : IsCovariantDerivativeOn F toFun Set.univ

namespace CovariantDerivative

attribute [coe] toFun

/-- Coercion of a `CovariantDerivative` to function -/
/-
**CovariantDerivative.** 是 Mathlib 中的一个实例，位于命名空间 `CovariantDerivative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of a `CovariantDerivative` to function
-/
instance : CoeFun (CovariantDerivative I F V)
    fun _ ↦ (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x) :=
  ⟨fun e ↦ e.toFun⟩
/-
**CovariantDerivative.isCovariantDerivativeOn** 是 Mathlib 中的一个引理，位于命名空间 `Covaria
ntDerivative`。
形式化陈述：isCovariantDerivativeOn (cov : CovariantDerivative I F V) {s : Set M} : Is
CovariantDerivativeOn F cov s
参数：cov : CovariantDerivative I F V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCovariantDerivativeOn.mono`：mono {cov : (Π x : M, V x) -> (Π x : M, Ta
ngentSpace I x ->L[𝕜] V x)} {s t : Set M} (hcov : IsCovariantDerivativeOn F cov 
t) (hst : s subset…
· 使用定理 `CovariantDerivative.isCovariantDerivativeOnUniv`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `trivial`：True
-/
lemma isCovariantDerivativeOn (cov : CovariantDerivative I F V) {s : Set M} :
    IsCovariantDerivativeOn F cov s :=
  cov.isCovariantDerivativeOnUniv.mono (fun _ _ ↦ trivial)

@[simp]
/-
**CovariantDerivative.zero** 是 Mathlib 中的一个引理，位于命名空间 `CovariantDerivative`。
形式化陈述：zero [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V) : cov 0 = 0
参数：cov : CovariantDerivative I F V。
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
· 使用引理 `IsCovariantDerivativeOn.zero`：zero [VectorBundle 𝕜 F V] (hcov : IsCovari
antDerivativeOn F cov s) {x} (hx : x in s
· 使用定理 `CovariantDerivative.isCovariantDerivativeOnUniv`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V) : cov 0 = 0 := by
  ext1 x
  simp [cov.isCovariantDerivativeOnUniv.zero]

/-- If `cov` is a covariant derivative on each set in an open cover, it is a covariant derivative.
-/
/-
**CovariantDerivative.ofIsCovariantDerivativeOnOfOpenCover** 是 Mathlib 中的一个定义，位于
命名空间 `CovariantDerivative`。
形式化陈述：ofIsCovariantDerivativeOnOfOpenCover {ι : Type*} {s : ι -> Set M} {cov : (
Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)} (hcov : forall i, IsCov
ariantDerivativeOn F cov (s i)) (hs : ⋃ i, s i = Set.univ) : CovariantDerivative
 I F V
参数：Π x : M, V x；Π x : M, TangentSpace I x ->L[𝕜] V x；hcov : forall i, IsCovarian
tDerivativeOn F cov (s i)；hs : ⋃ i, s i = Set.univ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `cov` is a covariant derivative on each set in an open cover, it is a covaria
nt derivative.
-/
def ofIsCovariantDerivativeOnOfOpenCover {ι : Type*} {s : ι → Set M}
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : ∀ i, IsCovariantDerivativeOn F cov (s i)) (hs : ⋃ i, s i = Set.univ) :
    CovariantDerivative I F V :=
  ⟨cov, hs ▸ IsCovariantDerivativeOn.iUnion hcov⟩

@[deprecated (since := "2026-07-26")]
alias of_isCovariantDerivativeOn_of_open_cover := ofIsCovariantDerivativeOnOfOpenCover

@[simp]
/-
**CovariantDerivative.of_isCovariantDerivativeOn_of_open_cover_coe** 是 Mathlib 中
的一个引理，位于命名空间 `CovariantDerivative`。
形式化陈述：of_isCovariantDerivativeOn_of_open_cover_coe {ι : Type*} {s : ι -> Set M} 
{cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)} (hcov : forall 
i, IsCovariantDerivativeOn F cov (s i)) (hs : ⋃ i, s i = Set.univ) : ofIsCovaria
ntDerivativeOnOfOpenCover hcov hs = cov
参数：Π x : M, V x；Π x : M, TangentSpace I x ->L[𝕜] V x；hcov : forall i, IsCovarian
tDerivativeOn F cov (s i)；hs : ⋃ i, s i = Set.univ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_isCovariantDerivativeOn_of_open_cover_coe {ι : Type*} {s : ι → Set M}
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : ∀ i, IsCovariantDerivativeOn F cov (s i)) (hs : ⋃ i, s i = Set.univ) :
    ofIsCovariantDerivativeOnOfOpenCover hcov hs = cov := rfl

/--
A covariant derivative ∇ is called of class `C^k` iff, whenever `X` is a `C^k` section and `σ` a
`C^{k+1}` section, the result `∇_X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
We will prove in a later file that any `C^(k+1)` covariant derivative is `C^k`.
-/
/-
**CovariantDerivative.ContMDiffCovariantDerivative** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CovariantDerivative`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     {I : ModelWithCorners 𝕜 E H} →                 {M : Type u_4} →            
       [inst_4 : TopologicalSpace M] →                     [inst_5 : ChartedSpac
e H M] →                       {F : Type u_5} →                         [inst_6 
: NormedAddCommGroup F] →                           [inst_7 : NormedSpace 𝕜 F] →
                             {V : M → Type u_6} →                               
[inst_8 : TopologicalSpace (Bundle.TotalSpace F V)] →                           
      [inst_9 : (x : M) → AddCommGroup (V x)] →                                 
  [inst_10 : (x : M) → _root_.Module 𝕜 (V x)] →                                 
    [inst_11 : (x : M) → TopologicalSpace (V x)] →                              
         [inst_12 : ∀ (x : M), IsTopologicalAddGroup (V x)] →                   
                      [inst_13 : ∀ (x : M), ContinuousSMul 𝕜 (V x)] →           
                                [inst_14 : FiberBundle F V] →                   
                          [IsManifold I 1 M] →                                  
             [VectorBundle 𝕜 F V] → CovariantDerivative I F V → WithTop ℕ∞ → Pro
p
参数：Bundle.TotalSpace F V；x : M；V x；x : M；V x；x : M；V x；x : M；V x；x : M；V x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A covariant derivative ∇ is called of class `C^k` iff, whenever `X` is a `C^k` s
ection and `σ` a
`C^{k+1}` section, the result `∇_X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
We will prove in a later file that any `C^(k+1)` covariant derivative is `C^k`.
-/
class ContMDiffCovariantDerivative [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    (cov : CovariantDerivative I F V) (k : ℕ∞ω) where
  contMDiff : ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ

@[simp]
/-
**CovariantDerivative.contMDiffCovariantDerivativeOn_univ_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CovariantDerivative`。
形式化陈述：contMDiffCovariantDerivativeOn_univ_iff [IsManifold I 1 M] [VectorBundle 𝕜
 F V] {cov : CovariantDerivative I F V} {k : Nat∞ω} : ContMDiffCovariantDerivati
veOn F k cov.toFun Set.univ ↔ ContMDiffCovariantDerivative cov k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantDerivative.ContMDiffCovariantDerivative.contMDiff`：∀ {𝕜 : Type 
u_1} {inst : NontriviallyNormedField 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGr
oup E}   {inst_2 : NormedSpace 𝕜 E} {H : Type u_…
-/
lemma contMDiffCovariantDerivativeOn_univ_iff [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {cov : CovariantDerivative I F V} {k : ℕ∞ω} :
    ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ ↔ ContMDiffCovariantDerivative cov k :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.contMDiff⟩

section operations

/-! ### Operations

In this section we prove that:

* affine combinations of covariant derivatives are covariant derivatives
* adding a one-form taking values in the endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. See `CovariantDerivative.addOneForm`.
* subtracting two covariant derivatives on some set gives a one-form taking values in the
  endomorphisms of the vector bundle. See `CovariantDerivative.difference`.

Note: morally this means covariant derivatives form an affine space over the vector space of
one-forms taking values in the endomorphisms of the bundle, but we don’t package it that way yet.
-/

/-- An affine combination of covariant derivatives as a covariant derivative. -/
@[simps]
/-
**CovariantDerivative.affineCombination** 是 Mathlib 中的一个定义，位于命名空间 `CovariantDeri
vative`。
形式化陈述：affineCombination (cov cov' : CovariantDerivative I F V) (g : M -> 𝕜) : Co
variantDerivative I F V where toFun
参数：cov cov' : CovariantDerivative I F V；g : M -> 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine combination of covariant derivatives as a covariant derivative.
-/
def affineCombination (cov cov' : CovariantDerivative I F V) (g : M → 𝕜) :
    CovariantDerivative I F V where
  toFun := fun σ ↦ (g • (cov σ)) + (1 - g) • (cov' σ)
  isCovariantDerivativeOnUniv :=
    cov.isCovariantDerivativeOn.affine_combination cov'.isCovariantDerivativeOn _

@[deprecated (since := "2026-07-26")] alias affine_combination := affineCombination

/-- A finite affine combination of covariant derivatives as a covariant derivative. -/
/-
**CovariantDerivative.finiteAffineCombination** 是 Mathlib 中的一个定义，位于命名空间 `Covaria
ntDerivative`。
形式化陈述：finiteAffineCombination {ι : Type*} {s : Finset ι} (cov : ι -> CovariantDe
rivative I F V) {f : ι -> M -> 𝕜} (hf : ∑ i in s, f i = 1) : CovariantDerivative
 I F V where toFun t x
参数：cov : ι -> CovariantDerivative I F V；hf : ∑ i in s, f i = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite affine combination of covariant derivatives as a covariant derivative.
-/
def finiteAffineCombination {ι : Type*} {s : Finset ι}
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    CovariantDerivative I F V where
  toFun t x := ∑ i ∈ s, (f i x) • (cov i) t x
  isCovariantDerivativeOnUniv := IsCovariantDerivativeOn.finite_affine_combination
    (fun i ↦ (cov i).isCovariantDerivativeOn) hf

@[deprecated (since := "2026-07-26")] alias finite_affine_combination := finiteAffineCombination

/-- An affine combination of two `C^k` connections is a `C^k` connection. -/
/-
**CovariantDerivative.ContMDiffCovariantDerivative.affineCombination** 是 Mathlib
 中的一个定理，位于命名空间 `CovariantDerivative.ContMDiffCovariantDerivative`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {F : Type u_5} [inst_6 : NormedAddCom
mGroup F]   [inst_7 : NormedSpace 𝕜 F] {V : M → Type u_6} [inst_8 : TopologicalS
pace (Bundle.TotalSpace F V)]   [inst_9 : (x : M) → AddCommGroup (V x)] [inst_10
 : (x : M) → _root_.Module 𝕜 (V x)]   [inst_11 : (x : M) → TopologicalSpace (V x
)] [inst_12 : ∀ (x : M), IsTopologicalAddGroup (V x)]   [inst_13 : ∀ (x : M), Co
ntinuousSMul 𝕜 (V x)] [inst_14 : FiberBundle F V] [inst_15 : IsManifold I 1 M]  
 [inst_16 : VectorBundle 𝕜 F V] (cov cov' : CovariantDerivative I F V) {f : M → 
𝕜} {n : WithTop ℕ∞},   ContMDiff I (modelWithCornersSelf 𝕜 𝕜) n f →     cov.Cont
MDiffCovariantDerivative n →       cov'.ContMDiffCovariantDerivative n → (cov.af
fineCombination cov' f).ContMDiffCovariantDerivative n
参数：Bundle.TotalSpace F V；x : M；V x；x : M；V x；x : M；V x；x : M；V x；x : M；V x；cov c
ov' : CovariantDerivative I F V；modelWithCornersSelf 𝕜 𝕜；cov.affineCombination c
ov' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffCovariantDerivativeOn.affine_combination`：∀ {𝕜 : Type u_1} [ins
t : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `CovariantDerivative.ContMDiffCovariantDerivative.contMDiff`：∀ {𝕜 : Type 
u_1} {inst : NontriviallyNormedField 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGr
oup E}   {inst_2 : NormedSpace 𝕜 E} {H : Type u_…

--- 原说明 ---
An affine combination of two `C^k` connections is a `C^k` connection.
-/
lemma ContMDiffCovariantDerivative.affineCombination [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  (cov cov' : CovariantDerivative I F V)
    {f : M → 𝕜} {n : ℕ∞ω} (hf : CMDiff n f)
    (hcov : ContMDiffCovariantDerivative cov n) (hcov' : ContMDiffCovariantDerivative cov' n) :
    ContMDiffCovariantDerivative (affineCombination cov cov' f) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.affine_combination hf.contMDiffOn hcov.contMDiff hcov'.contMDiff

@[deprecated (since := "2026-07-26")]
alias ContMDiffCovariantDerivative.affine_combination :=
  ContMDiffCovariantDerivative.affineCombination

/-- An affine combination of finitely many `C^k` connections is a `C^k` connection. -/
/-
**CovariantDerivative.ContMDiffCovariantDerivative.finiteAffineCombination** 是 M
athlib 中的一个定理，位于命名空间 `CovariantDerivative.ContMDiffCovariantDerivative`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {F : Type u_5} [inst_6 : NormedAddCom
mGroup F]   [inst_7 : NormedSpace 𝕜 F] {V : M → Type u_6} [inst_8 : TopologicalS
pace (Bundle.TotalSpace F V)]   [inst_9 : (x : M) → AddCommGroup (V x)] [inst_10
 : (x : M) → _root_.Module 𝕜 (V x)]   [inst_11 : (x : M) → TopologicalSpace (V x
)] [inst_12 : ∀ (x : M), IsTopologicalAddGroup (V x)]   [inst_13 : ∀ (x : M), Co
ntinuousSMul 𝕜 (V x)] [inst_14 : FiberBundle F V] [inst_15 : IsManifold I 1 M]  
 [inst_16 : VectorBundle 𝕜 F V] {ι : Type u_7} {s : Finset ι} (cov : ι → Covaria
ntDerivative I F V) {f : ι → M → 𝕜}   (hf : ∑ i ∈ s, f i = 1) {n : WithTop ℕ∞}, 
  (∀ i ∈ s, ContMDiff I (modelWithCornersSelf 𝕜 𝕜) n (f i)) →     (∀ i ∈ s, (cov
 i).ContMDiffCovariantDerivative n) →       (CovariantDerivative.finiteAffineCom
bination cov hf).ContMDiffCovariantDerivative n
参数：Bundle.TotalSpace F V；x : M；V x；x : M；V x；x : M；V x；x : M；V x；x : M；V x；cov :
 ι → CovariantDerivative I F V；hf : ∑ i ∈ s, f i = 1；∀ i ∈ s, ContMDiff I (model
WithCornersSelf 𝕜 𝕜) n (f i)；∀ i ∈ s, (cov i).ContMDiffCovariantDerivative n；Cov
ariantDerivative.finiteAffineCombination cov hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffCovariantDerivativeOn.finite_affine_combination`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `CovariantDerivative.ContMDiffCovariantDerivative.contMDiff`：∀ {𝕜 : Type 
u_1} {inst : NontriviallyNormedField 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGr
oup E}   {inst_2 : NormedSpace 𝕜 E} {H : Type u_…
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…

--- 原说明 ---
An affine combination of finitely many `C^k` connections is a `C^k` connection.
-/
lemma ContMDiffCovariantDerivative.finiteAffineCombination [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {ι : Type*} {s : Finset ι} (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜}
    (hf : ∑ i ∈ s, f i = 1) {n : ℕ∞ω} (hf' : ∀ i ∈ s, CMDiff n (f i))
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivative (cov i) n) :
    ContMDiffCovariantDerivative (finiteAffineCombination cov hf) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.finite_affine_combination
      (fun i hi ↦ (hcov i hi).contMDiff) (fun i hi ↦ (hf' i hi).contMDiffOn)

@[deprecated (since := "2026-07-26")]
alias ContMDiffCovariantDerivative.finite_affine_combination :=
  ContMDiffCovariantDerivative.finiteAffineCombination

-- TODO: prove a version with a locally finite sum, and deduce that C^k connections always
-- exist (using a partition of unity argument)

/-- Adding a one-form taking values in the endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. -/
/-
**CovariantDerivative.addOneForm** 是 Mathlib 中的一个定义，位于命名空间 `CovariantDerivative`
。
形式化陈述：addOneForm (cov : CovariantDerivative I F V) (A : Π (x : M), V x ->L[𝕜] Ta
ngentSpace I x ->L[𝕜] V x) : CovariantDerivative I F V where toFun
参数：cov : CovariantDerivative I F V；A : Π (x : M), V x ->L[𝕜] TangentSpace I x ->
L[𝕜] V x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adding a one-form taking values in the endomorphisms of the vector bundle to a c
ovariant
  derivative gives a covariant derivative.
-/
def addOneForm (cov : CovariantDerivative I F V)
    (A : Π (x : M), V x →L[𝕜] TangentSpace I x →L[𝕜] V x) : CovariantDerivative I F V where
  toFun := fun σ x ↦ cov σ x + A x (σ x)
  isCovariantDerivativeOnUniv := cov.isCovariantDerivativeOnUniv.add_one_form A

section difference

-- We need more assumptions to use the tensoriality criterion in order to build the difference
-- operation.
variable [CompleteSpace 𝕜] [IsManifold I 1 M] [FiniteDimensional 𝕜 F]
  [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

/-- The difference of two covariant derivatives, as a one-form taking values in the
endomorphisms of `V`. -/
/-
**CovariantDerivative.difference** 是 Mathlib 中的一个定义，位于命名空间 `CovariantDerivative`
。
形式化陈述：difference (cov cov' : CovariantDerivative I F V) : Π (x : M), V x ->L[𝕜] 
TangentSpace I x ->L[𝕜] V x
参数：cov cov' : CovariantDerivative I F V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantDerivative.isCovariantDerivativeOnUniv`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
The difference of two covariant derivatives, as a one-form taking values in the
endomorphisms of `V`.
-/
def difference (cov cov' : CovariantDerivative I F V) :
    Π (x : M), V x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv

end difference
end operations

end CovariantDerivative

