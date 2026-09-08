/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Derivatives of operations on continuous multilinear maps

In this file,

- `ι` is an index type (`Fin n` in many applications);
- `E`, `F i`, `G i`, `H`, are normed spaces for each `i : ι`;
- `f x` is a continuous multilinear map from `Π i, G i` to `H`, depending on a parameter `x : E`;
- for each `i : ι`, `g i x` is a continuous linear map `F i → G i`,
  depending on a parameter `x : E`.

Given this data, for each `x` we can define a continuous multilinear map from `Π i, F i` to `H`
given by `(f x).compContinuousLinearMap (fun i ↦ g i x) v = f x (fun i ↦ g i x (v i))`.

As a map between functional spaces,
`ContinuousMultilinearMap.compContinuousLinearMap` is multilinear in `(f; g i)`.
Thus its derivative with respect to each map (`f` or `g i`)
is given by substituting `f'` or `g' i` instead of `f` or `g i`
in `(f x).compContinuousLinearMap (fun i ↦ g i x)`,
and the full differential is given by the sum of these terms.

In terms of bundled maps, the derivative with respect to `f`
is given by `ContinuousMultilinearMap.compContinuousLinearMapL`
and the sum of terms that represent the derivatives with respect to `g i`
is given by `ContinuousMultilinearMap.fderivCompContinuousLinearMap`.

All statements in the first section are claiming this, for various notions of differentiation.
The second section deduces the corresponding differentiability results when `ι` is finite.
-/

public section

variable {𝕜 ι E : Type*} {F G : ι → Type*} {H : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {f : E → ContinuousMultilinearMap 𝕜 G H} {f' : E →L[𝕜] ContinuousMultilinearMap 𝕜 G H}
  {g : ∀ i, E → F i →L[𝕜] G i} {g' : ∀ i, E →L[𝕜] F i →L[𝕜] G i}
  {s : Set E} {x : E}

open ContinuousMultilinearMap

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

/-
**ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap (fg : C
ontinuousMultilinearMap 𝕜 G H × forall i, F i ->L[𝕜] G i) : HasStrictFDerivAt (f
un fg : ContinuousMultilinearMap 𝕜 G H × forall i, F i ->L[𝕜] G i => fg.1.compCo
ntinuousLinearMap fg.2) (compContinuousLinearMapL fg.2 ∘L .fst _ _ _ + fg.1.fder
ivCompContinuousLinearMap fg.2 ∘L .snd _ _ _) fg
参数：fg : ContinuousMultilinearMap 𝕜 G H × forall i, F i ->L[𝕜] G i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContinuousMultilinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 :
 NormedSpace 𝕜 F] {ι : Type u_2}…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.prod_ext`：prod_ext {f g : M × M₂ ->L[R] M₃} (hl : f.
comp (inl _ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ 
_ _)) : f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ContinuousMultilinearMap.linearDeriv_apply`：linearDeriv_apply : f.linear
Deriv x y = ∑ i, f (Function.update x i (y i))
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_ap
ply_apply`：∀ (𝕜 : Type u) {ι : Type v} (E : ι → Type wE) (E₁ : ι → Type wE₁) (G 
: Type wG) [inst : NontriviallyNormedField 𝕜]   [inst_1 : (i : ι) → Sem…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictFDerivAt.clm_apply`：HasStrictFDerivAt.clm_apply (hc : HasStrict
FDerivAt c c' x) (hu : HasStrictFDerivAt u u' x) : HasStrictFDerivAt (fun y => (
c y) (u y)) ((c x…
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
（共 32 条，此处仅展示前 30 条）
-/
theorem ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg : ContinuousMultilinearMap 𝕜 G H × ∀ i, F i →L[𝕜] G i) :
    HasStrictFDerivAt
      (fun fg : ContinuousMultilinearMap 𝕜 G H × ∀ i, F i →L[𝕜] G i ↦
        fg.1.compContinuousLinearMap fg.2)
      (compContinuousLinearMapL fg.2 ∘L .fst _ _ _ +
        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
      fg := by
  have := (compContinuousLinearMapContinuousMultilinear 𝕜 F G H).hasStrictFDerivAt fg.2
  convert! this.comp fg hasStrictFDerivAt_snd |>.clm_apply hasStrictFDerivAt_fst
  ext <;> simp [fderivCompContinuousLinearMap]
/-
**HasStrictFDerivAt.continuousMultilinearMapCompContinuousLinearMap** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.continuousMultilinearMapCompContinuousLinearMap (hf : Ha
sStrictFDerivAt f f' x) (hg : forall i, HasStrictFDerivAt (g i) (g' i) x) : HasS
trictFDerivAt (fun x => (f x).compContinuousLinearMap (g · x)) (compContinuousLi
nearMapL (g · x) ∘L f' + (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') 
x
参数：hf : HasStrictFDerivAt f f' x；hg : forall i, HasStrictFDerivAt (g i) (g' i) x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap`：Cont
inuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap (fg : ContinuousM
ultilinearMap 𝕜 G H × forall i, F i ->L[𝕜] G i) : HasStr…
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictFDerivAt_pi`：hasStrictFDerivAt_pi : HasStrictFDerivAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') x ↔ forall i, HasStrictFDerivAt (φ i) (φ' 
i) x
-/
theorem HasStrictFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : HasStrictFDerivAt f f' x) (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g · x))
      (compContinuousLinearMapL (g · x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') x :=
  hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x))
    |>.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))
/-
**HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap (hf : HasFDeri
vAt f f' x) (hg : forall i, HasFDerivAt (g i) (g' i) x) : HasFDerivAt (fun x => 
(f x).compContinuousLinearMap (g · x)) (compContinuousLinearMapL (g · x) ∘L f' +
 (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') x
参数：hf : HasFDerivAt f f' x；hg : forall i, HasFDerivAt (g i) (g' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap`：Cont
inuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap (fg : ContinuousM
ultilinearMap 𝕜 G H × forall i, F i ->L[𝕜] G i) : HasStr…
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivAt_pi`：hasFDerivAt_pi : HasFDerivAt (fun x i => φ i x) (Continu
ousLinearMap.pi φ') x ↔ forall i, HasFDerivAt (φ i) (φ' i) x
-/
theorem HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : HasFDerivAt f f' x) (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g · x))
      (compContinuousLinearMapL (g · x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') x := by
  convert!
    hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x)) |>.hasFDerivAt |>.comp x
      (hf.prodMk (hasFDerivAt_pi.2 hg))
/-
**HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap (hf : Ha
sFDerivWithinAt f f' s x) (hg : forall i, HasFDerivWithinAt (g i) (g' i) s x) : 
HasFDerivWithinAt (fun x => (f x).compContinuousLinearMap (g · x)) (compContinuo
usLinearMapL (g · x) ∘L f' + (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi 
g') s x
参数：hf : HasFDerivWithinAt f f' s x；hg : forall i, HasFDerivWithinAt (g i) (g' i)
 s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap`：Cont
inuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap (fg : ContinuousM
ultilinearMap 𝕜 G H × forall i, F i ->L[𝕜] G i) : HasStr…
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_pi`：hasFDerivWithinAt_pi : HasFDerivWithinAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') s x ↔ forall i, HasFDerivWithinAt (φ i) (φ
' i) s x
-/
theorem HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : HasFDerivWithinAt f f' s x) (hg : ∀ i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ (f x).compContinuousLinearMap (g · x))
      (compContinuousLinearMapL (g · x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') s x := by
  convert!
    hasStrictFDerivAt_compContinuousLinearMap
          (f x, (g · x)) |>.hasFDerivAt |>.comp_hasFDerivWithinAt
      x (hf.prodMk (hasFDerivWithinAt_pi.2 hg))
/-
**fderivWithin_continuousMultilinearMapCompContinuousLinearMap** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：fderivWithin_continuousMultilinearMapCompContinuousLinearMap (hf : Differe
ntiableWithinAt 𝕜 f s x) (hg : forall i, DifferentiableWithinAt 𝕜 (g i) s x) (hs
 : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (fun x => (f x).compContinuousLine
arMap (g · x)) s x = compContinuousLinearMapL (g · x) ∘L fderivWithin 𝕜 f s x + 
(f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i => fderivWithin 𝕜 (g i)
 s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : forall i, DifferentiableWithinAt 𝕜 (
g i) s x；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap`：HasFD
erivWithinAt.continuousMultilinearMapCompContinuousLinearMap (hf : HasFDerivWith
inAt f f' s x) (hg : forall i, HasFDerivWithinAt (g i) …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) s x =
      compContinuousLinearMapL (g · x) ∘L fderivWithin 𝕜 f s x +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i ↦ fderivWithin 𝕜 (g i) s x :=
  hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (fun i ↦ (hg i).hasFDerivWithinAt) |>.fderivWithin hs
/-
**fderiv_continuousMultilinearMapCompContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：fderiv_continuousMultilinearMapCompContinuousLinearMap (hf : Differentiabl
eAt 𝕜 f x) (hg : forall i, DifferentiableAt 𝕜 (g i) x) : fderiv 𝕜 (fun x => (f x
).compContinuousLinearMap (g · x)) x = compContinuousLinearMapL (g · x) ∘L fderi
v 𝕜 f x + (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i => fderiv 𝕜 (
g i) x
参数：hf : DifferentiableAt 𝕜 f x；hg : forall i, DifferentiableAt 𝕜 (g i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap`：HasFDerivAt
.continuousMultilinearMapCompContinuousLinearMap (hf : HasFDerivAt f f' x) (hg :
 forall i, HasFDerivAt (g i) (g' i) x) : HasFDeri…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) x =
      compContinuousLinearMapL (g · x) ∘L fderiv 𝕜 f x +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i ↦ fderiv 𝕜 (g i) x :=
  hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (fun i ↦ (hg i).hasFDerivAt) |>.fderiv

end HasFDerivAt

variable [Finite ι]

/-
**DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap (hf
 : DifferentiableWithinAt 𝕜 f s x) (hg : forall i, DifferentiableWithinAt 𝕜 (g i
) s x) : DifferentiableWithinAt 𝕜 (fun x => (f x).compContinuousLinearMap (g · x
)) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : forall i, DifferentiableWithinAt 𝕜 (
g i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap`：HasFD
erivWithinAt.continuousMultilinearMapCompContinuousLinearMap (hf : HasFDerivWith
inAt f f' s x) (hg : forall i, HasFDerivWithinAt (g i) …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) :
    DifferentiableWithinAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (fun i ↦ (hg i).hasFDerivWithinAt) |>.differentiableWithinAt
/-
**DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap (hf : Dif
ferentiableAt 𝕜 f x) (hg : forall i, DifferentiableAt 𝕜 (g i) x) : Differentiabl
eAt 𝕜 (fun x => (f x).compContinuousLinearMap (g · x)) x
参数：hf : DifferentiableAt 𝕜 f x；hg : forall i, DifferentiableAt 𝕜 (g i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap`：HasFDerivAt
.continuousMultilinearMapCompContinuousLinearMap (hf : HasFDerivAt f f' x) (hg :
 forall i, HasFDerivAt (g i) (g' i) x) : HasFDeri…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) :
    DifferentiableAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (fun i ↦ (hg i).hasFDerivAt) |>.differentiableAt
/-
**DifferentiableOn.continuousMultilinearMapCompContinuousLinearMap** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.continuousMultilinearMapCompContinuousLinearMap (hf : Dif
ferentiableOn 𝕜 f s) (hg : forall i, DifferentiableOn 𝕜 (g i) s) : Differentiabl
eOn 𝕜 (fun x => (f x).compContinuousLinearMap (g · x)) s
参数：hf : DifferentiableOn 𝕜 f s；hg : forall i, DifferentiableOn 𝕜 (g i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap`：
DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap (hf : Dif
ferentiableWithinAt 𝕜 f s x) (hg : forall i, DifferentiableW…
-/
theorem DifferentiableOn.continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableOn 𝕜 f s) (hg : ∀ i, DifferentiableOn 𝕜 (g i) s) :
    DifferentiableOn 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) s := fun x hx ↦
  (hf x hx).continuousMultilinearMapCompContinuousLinearMap (hg · x hx)
/-
**Differentiable.continuousMultilinearMapCompContinuousLinearMap** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：Differentiable.continuousMultilinearMapCompContinuousLinearMap (hf : Diffe
rentiable 𝕜 f) (hg : forall i, Differentiable 𝕜 (g i)) : Differentiable 𝕜 (fun x
 => (f x).compContinuousLinearMap (g · x))
参数：hf : Differentiable 𝕜 f；hg : forall i, Differentiable 𝕜 (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap`：Differ
entiableAt.continuousMultilinearMapCompContinuousLinearMap (hf : DifferentiableA
t 𝕜 f x) (hg : forall i, DifferentiableAt 𝕜 (g i) x) :…
-/
theorem Differentiable.continuousMultilinearMapCompContinuousLinearMap
    (hf : Differentiable 𝕜 f) (hg : ∀ i, Differentiable 𝕜 (g i)) :
    Differentiable 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) := fun x ↦
  (hf x).continuousMultilinearMapCompContinuousLinearMap (hg · x)
