/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Sam Lindauer
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-!
# Exterior derivative of a differential form on a normed space

In this file we define the exterior derivative of a differential form on a normed space.
Under certain smoothness assumptions, we prove that this operation is linear in the form
and the second exterior derivative of a form is zero.

We represent a differential `n`-form on `E` taking values in `F` as `E → E [⋀^Fin n]→L[𝕜] F`.

## Implementation notes

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDeriv_apply`.

## TODO

- Introduce notation for:
  - an unbundled `n`-form on a normed space;
  - a bundled `C^r`-smooth `n`-form on a normed space;
  - same for manifolds (not defined yet).
- Introduce bundled `C^r`-smooth `n`-forms on normed spaces and manifolds.
  - Discuss the future API and the use cases that need to be covered on Zulip.
  - Introduce new types & notation, copy the API.
- Add shorter and more readable definitions (or abbreviations?)
  for `0`-forms (`constOfIsEmpty`) and `1`-forms (`ofSubsingleton`),
  sync with the API for `ContinuousMultilinearMap`.
-/

@[expose] public section

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n m k : ℕ} {r : WithTop ℕ∞}
  {ω ω₁ ω₂ : E → E [⋀^Fin n]→L[𝕜] F} {s t : Set E} {x : E}

/-- Exterior derivative of a differential form.

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDeriv_apply`.
-/
/-
**extDeriv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：extDeriv (ω : E -> E [⋀^Fin n]->L[𝕜] F) (x : E) : E [⋀^Fin (n + 1)]->L[𝕜] 
F
参数：ω : E -> E [⋀^Fin n]->L[𝕜] F；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exterior derivative of a differential form.

There are a few competing definitions of the exterior derivative of a differenti
al form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i},
 \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDeri
v_apply`.
-/
noncomputable def extDeriv (ω : E → E [⋀^Fin n]→L[𝕜] F) (x : E) : E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .alternatizeUncurryFin (fderiv 𝕜 ω x)

/-- Exterior derivative of a differential form within a set.

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDerivWithin_apply`.
-/
/-
**extDerivWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：extDerivWithin (ω : E -> E [⋀^Fin n]->L[𝕜] F) (s : Set E) (x : E) : E [⋀^F
in (n + 1)]->L[𝕜] F
参数：ω : E -> E [⋀^Fin n]->L[𝕜] F；s : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exterior derivative of a differential form within a set.

There are a few competing definitions of the exterior derivative of a differenti
al form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i},
 \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDeri
vWithin_apply`.
-/
noncomputable def extDerivWithin (ω : E → E [⋀^Fin n]→L[𝕜] F) (s : Set E) (x : E) :
    E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .alternatizeUncurryFin (fderivWithin 𝕜 ω s x)

@[simp]
/-
**extDerivWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_univ (ω : E -> E [⋀^Fin n]->L[𝕜] F) : extDerivWithin ω univ
 = extDeriv ω
参数：ω : E -> E [⋀^Fin n]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extDerivWithin.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 …
· 使用定理 `extDeriv.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : No
ntriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 …
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
-/
theorem extDerivWithin_univ (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDerivWithin ω univ = extDeriv ω := by
  ext1 x
  rw [extDerivWithin, extDeriv, fderivWithin_univ]
/-
**extDerivWithin_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_add (hsx : UniqueDiffWithinAt 𝕜 s x) (hω₁ : DifferentiableW
ithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) : extDerivWithin (ω₁ +
 ω₂) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x
参数：hsx : UniqueDiffWithinAt 𝕜 s x；hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x；hω₂ : Di
fferentiableWithinAt 𝕜 ω₂ s x。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_add`：fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf 
: DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : fderiv
Within…
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_add`：alternatizeUncurryFi
n_add (f g : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) : alternatizeUncurryFin (f + g) = alt
ernatizeUncurryFin f + alternatizeUncurr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extDerivWithin_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    extDerivWithin (ω₁ + ω₂) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x := by
  simp [extDerivWithin, fderivWithin_add hsx hω₁ hω₂, alternatizeUncurryFin_add]
/-
**extDerivWithin_fun_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_fun_add (hsx : UniqueDiffWithinAt 𝕜 s x) (hω₁ : Differentia
bleWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) : extDerivWithin (
fun x => ω₁ x + ω₂ x) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x
参数：hsx : UniqueDiffWithinAt 𝕜 s x；hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x；hω₂ : Di
fferentiableWithinAt 𝕜 ω₂ s x。
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
· 使用定理 `extDerivWithin_add`：extDerivWithin_add (hsx : UniqueDiffWithinAt 𝕜 s x) 
(hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) 
: extDer…
-/
theorem extDerivWithin_fun_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    extDerivWithin (fun x ↦ ω₁ x + ω₂ x) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x :=
  extDerivWithin_add hsx hω₁ hω₂
/-
**extDeriv_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ 
x) : extDeriv (ω₁ + ω₂) x = extDeriv ω₁ x + extDeriv ω₂ x
参数：hω₁ : DifferentiableAt 𝕜 ω₁ x；hω₂ : DifferentiableAt 𝕜 ω₂ x。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `extDerivWithin_add`：extDerivWithin_add (hsx : UniqueDiffWithinAt 𝕜 s x) 
(hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) 
: extDer…
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extDeriv_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    extDeriv (ω₁ + ω₂) x = extDeriv ω₁ x + extDeriv ω₂ x := by
  simp [← extDerivWithin_univ, extDerivWithin_add, *, DifferentiableAt.differentiableWithinAt]
/-
**extDeriv_fun_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_fun_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜
 ω₂ x) : extDeriv (fun x => ω₁ x + ω₂ x) x = extDeriv ω₁ x + extDeriv ω₂ x
参数：hω₁ : DifferentiableAt 𝕜 ω₁ x；hω₂ : DifferentiableAt 𝕜 ω₂ x。
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
· 使用定理 `extDeriv_add`：extDeriv_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : Differ
entiableAt 𝕜 ω₂ x) : extDeriv (ω₁ + ω₂) x = extDeriv ω₁ x + extDeriv ω₂ x
-/
theorem extDeriv_fun_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    extDeriv (fun x ↦ ω₁ x + ω₂ x) x = extDeriv ω₁ x + extDeriv ω₂ x :=
  extDeriv_add hω₁ hω₂
/-
**extDerivWithin_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F) (hsx : UniqueDi
ffWithinAt 𝕜 s x) : extDerivWithin (c • ω) s x = c • extDerivWithin ω s x
参数：c : 𝕜；ω : E -> E [⋀^Fin n]->L[𝕜] F；hsx : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用引理 `fderivWithin_const_smul_field`：fderivWithin_const_smul_field (c : R) (hs
 : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f
 s x
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_smul`：alternatizeUncurryF
in_smul {S : Type*} [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F] 
[SMulCommClass 𝕜 S F] (c : S) (f : E ->L[…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extDerivWithin_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (c • ω) s x = c • extDerivWithin ω s x := by
  simp [extDerivWithin, fderivWithin_const_smul_field, hsx, alternatizeUncurryFin_smul]
/-
**extDerivWithin_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_fun_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F) (hsx : Uniq
ueDiffWithinAt 𝕜 s x) : extDerivWithin (fun x => c • ω x) s x = c • extDerivWith
in ω s x
参数：c : 𝕜；ω : E -> E [⋀^Fin n]->L[𝕜] F；hsx : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extDerivWithin_smul`：extDerivWithin_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->
L[𝕜] F) (hsx : UniqueDiffWithinAt 𝕜 s x) : extDerivWithin (c • ω) s x = c • extD
erivWithi…
-/
theorem extDerivWithin_fun_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F)
    (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (fun x ↦ c • ω x) s x = c • extDerivWithin ω s x :=
  extDerivWithin_smul c ω hsx
/-
**extDeriv_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F) : extDeriv (c • ω) x 
= c • extDeriv ω x
参数：c : 𝕜；ω : E -> E [⋀^Fin n]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `extDerivWithin_smul`：extDerivWithin_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->
L[𝕜] F) (hsx : UniqueDiffWithinAt 𝕜 s x) : extDerivWithin (c • ω) s x = c • extD
erivWithi…
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extDeriv_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDeriv (c • ω) x = c • extDeriv ω x := by
  simp [← extDerivWithin_univ, extDerivWithin_smul]
/-
**extDeriv_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_fun_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F) : extDeriv (c • ω
) x = c • extDeriv ω x
参数：c : 𝕜；ω : E -> E [⋀^Fin n]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extDeriv_smul`：extDeriv_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F) : ex
tDeriv (c • ω) x = c • extDeriv ω x
-/
theorem extDeriv_fun_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDeriv (c • ω) x = c • extDeriv ω x :=
  extDeriv_smul c ω

/-- The exterior derivative of a `0`-form given by a function `f` within a set
is the 1-form given by the derivative of `f` within the set. -/
/-
**extDerivWithin_constOfIsEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_constOfIsEmpty (f : E -> F) (hs : UniqueDiffWithinAt 𝕜 s x)
 : extDerivWithin (fun x => constOfIsEmpty 𝕜 E (Fin 0) (f x)) s x = .ofSubsingle
ton _ _ _ (0 : Fin 1) (fderivWithin 𝕜 f s x)
参数：f : E -> F；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `LinearIsometryEquiv.comp_fderivWithin`：comp_fderivWithin {f : G -> E} {s
 : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (iso ∘ f) s 
x = (iso : E ->L[𝕜] F).comp…
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_constOfIsEmptyLIE_comp`：a
lternatizeUncurryFin_constOfIsEmptyLIE_comp (f : E ->L[𝕜] F) : alternatizeUncurr
yFin (constOfIsEmptyLIE 𝕜 E F (Fin 0) ∘L f) = ofSubsingleto…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The exterior derivative of a `0`-form given by a function `f` within a set
is the 1-form given by the derivative of `f` within the set.
-/
theorem extDerivWithin_constOfIsEmpty (f : E → F) (hs : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (fun x ↦ constOfIsEmpty 𝕜 E (Fin 0) (f x)) s x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderivWithin 𝕜 f s x) := by
  simp only [extDerivWithin, ← constOfIsEmptyLIE_apply, ← Function.comp_def _ f,
    (constOfIsEmptyLIE 𝕜 E F (Fin 0)).comp_fderivWithin hs,
    alternatizeUncurryFin_constOfIsEmptyLIE_comp]

/-- The exterior derivative of a `0`-form given by a function `f`
is the 1-form given by the derivative of `f`. -/
/-
**extDeriv_constOfIsEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_constOfIsEmpty (f : E -> F) (x : E) : extDeriv (fun x => constOfI
sEmpty 𝕜 E (Fin 0) (f x)) x = .ofSubsingleton _ _ _ (0 : Fin 1) (fderiv 𝕜 f x)
参数：f : E -> F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `extDerivWithin_constOfIsEmpty`：extDerivWithin_constOfIsEmpty (f : E -> F
) (hs : UniqueDiffWithinAt 𝕜 s x) : extDerivWithin (fun x => constOfIsEmpty 𝕜 E 
(Fin 0) (f x)) s x …
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The exterior derivative of a `0`-form given by a function `f`
is the 1-form given by the derivative of `f`.
-/
theorem extDeriv_constOfIsEmpty (f : E → F) (x : E) :
    extDeriv (fun x ↦ constOfIsEmpty 𝕜 E (Fin 0) (f x)) x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderiv 𝕜 f x) := by
  simp [← extDerivWithin_univ, extDerivWithin_constOfIsEmpty, fderivWithin_univ]
/-
**Filter.EventuallyEq.extDerivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.extDerivWithin_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x =
 ω₂ x) : extDerivWithin ω₁ s x = extDerivWithin ω₂ s x
参数：hs : ω₁ =ᶠ[𝓝[s] x] ω₂；hx : ω₁ x = ω₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Filter.EventuallyEq.extDerivWithin_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x := by
  simp only [extDerivWithin, alternatizeUncurryFin, hs.fderivWithin_eq hx]
/-
**Filter.EventuallyEq.extDerivWithin_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.extDerivWithin_eq_of_mem (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx :
 x in s) : extDerivWithin ω₁ s x = extDerivWithin ω₂ s x
参数：hs : ω₁ =ᶠ[𝓝[s] x] ω₂；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.extDerivWithin_eq`：Filter.EventuallyEq.extDerivWithi
n_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) : extDerivWithin ω₁ s x = extDer
ivWithin ω₂ s x
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
-/
theorem Filter.EventuallyEq.extDerivWithin_eq_of_mem (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x ∈ s) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  hs.extDerivWithin_eq (mem_of_mem_nhdsWithin hx hs :)
/-
**Filter.EventuallyEq.extDerivWithin_eq_of_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.extDerivWithin_eq_of_insert (hs : ω₁ =ᶠ[𝓝[insert x s] 
x] ω₂) : extDerivWithin ω₁ s x = extDerivWithin ω₂ s x
参数：hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.extDerivWithin_eq`：Filter.EventuallyEq.extDerivWithi
n_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) : extDerivWithin ω₁ s x = extDer
ivWithin ω₂ s x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem Filter.EventuallyEq.extDerivWithin_eq_of_insert (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x := by
  apply Filter.EventuallyEq.extDerivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)
/-
**Filter.EventuallyEq.extDerivWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.extDerivWithin' (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t subset
eq s) : extDerivWithin ω₁ t =ᶠ[𝓝[s] x] extDerivWithin ω₂ t
参数：hs : ω₁ =ᶠ[𝓝[s] x] ω₂；ht : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_eventually_nhdsWithin`：eventually_eventually_nhdsWithin {a : 
α} {s : Set α} {p : α -> Prop} : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x)
 ↔ forallᶠ x in 𝓝[s] a…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.EventuallyEq.extDerivWithin_eq`：Filter.EventuallyEq.extDerivWithi
n_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) : extDerivWithin ω₁ s x = extDer
ivWithin ω₂ s x
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
-/
theorem Filter.EventuallyEq.extDerivWithin' (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t ⊆ s) :
    extDerivWithin ω₁ t =ᶠ[𝓝[s] x] extDerivWithin ω₂ t :=
  (eventually_eventually_nhdsWithin.2 hs).mp <| eventually_mem_nhdsWithin.mono fun _y hys hs =>
    EventuallyEq.extDerivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)
/-
**Filter.EventuallyEq.extDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventuall
yEq`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {n : ℕ}   {ω₁ ω₂ : E → E [⋀^Fin 
n]→L[𝕜] F} {s : Set E} {x : E},   ω₁ =ᶠ[nhdsWithin x s] ω₂ → extDerivWithin ω₁ s
 =ᶠ[nhdsWithin x s] extDerivWithin ω₂ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.extDerivWithin'`：Filter.EventuallyEq.extDerivWithin'
 (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t subseteq s) : extDerivWithin ω₁ t =ᶠ[𝓝[s] x] ex
tDerivWithin ω₂ t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
protected theorem Filter.EventuallyEq.extDerivWithin (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) :
    extDerivWithin ω₁ s =ᶠ[𝓝[s] x] extDerivWithin ω₂ s :=
  hs.extDerivWithin' .rfl
/-
**Filter.EventuallyEq.extDerivWithin_eq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.extDerivWithin_eq_nhds (h : ω₁ =ᶠ[𝓝 x] ω₂) : extDerivW
ithin ω₁ s x = extDerivWithin ω₂ s x
参数：h : ω₁ =ᶠ[𝓝 x] ω₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.extDerivWithin_eq`：Filter.EventuallyEq.extDerivWithi
n_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) : extDerivWithin ω₁ s x = extDer
ivWithin ω₂ s x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
theorem Filter.EventuallyEq.extDerivWithin_eq_nhds (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  (h.filter_mono nhdsWithin_le_nhds).extDerivWithin_eq h.self_of_nhds
/-
**extDerivWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_congr (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) : extDerivWith
in ω₁ s x = extDerivWithin ω₂ s x
参数：hs : EqOn ω₁ ω₂ s；hx : ω₁ x = ω₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.extDerivWithin_eq`：Filter.EventuallyEq.extDerivWithi
n_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) : extDerivWithin ω₁ s x = extDer
ivWithin ω₂ s x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Set.EqOn.eventuallyEq`：Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α 
-> β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem extDerivWithin_congr (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).extDerivWithin_eq hx
/-
**extDerivWithin_congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_congr' (hs : EqOn ω₁ ω₂ s) (hx : x in s) : extDerivWithin ω
₁ s x = extDerivWithin ω₂ s x
参数：hs : EqOn ω₁ ω₂ s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extDerivWithin_congr`：extDerivWithin_congr (hs : EqOn ω₁ ω₂ s) (hx : ω₁ 
x = ω₂ x) : extDerivWithin ω₁ s x = extDerivWithin ω₂ s x
-/
theorem extDerivWithin_congr' (hs : EqOn ω₁ ω₂ s) (hx : x ∈ s) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  extDerivWithin_congr hs (hs hx)
/-
**Filter.EventuallyEq.extDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {n : ℕ}   {ω₁ ω₂ : E → E [⋀^Fin 
n]→L[𝕜] F} {x : E}, ω₁ =ᶠ[nhds x] ω₂ → extDeriv ω₁ =ᶠ[nhds x] extDeriv ω₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.extDerivWithin`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
protected theorem Filter.EventuallyEq.extDeriv (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDeriv ω₁ =ᶠ[𝓝 x] extDeriv ω₂ := by
  simp only [← nhdsWithin_univ, ← extDerivWithin_univ] at *
  exact h.extDerivWithin
/-
**Filter.EventuallyEq.extDeriv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.extDeriv_eq (h : ω₁ =ᶠ[𝓝 x] ω₂) : extDeriv ω₁ x = extD
eriv ω₂ x
参数：h : ω₁ =ᶠ[𝓝 x] ω₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `Filter.EventuallyEq.extDeriv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem Filter.EventuallyEq.extDeriv_eq (h : ω₁ =ᶠ[𝓝 x] ω₂) : extDeriv ω₁ x = extDeriv ω₂ x :=
  h.extDeriv.self_of_nhds
/-
**extDerivWithin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_apply (h : DifferentiableWithinAt 𝕜 ω s x) (hs : UniqueDiff
WithinAt 𝕜 s x) (v : Fin (n + 1) -> E) : extDerivWithin ω s x v = ∑ i, (-1) ^ i.
val • fderivWithin 𝕜 (ω · (i.removeNth v)) s x (v i)
参数：h : DifferentiableWithinAt 𝕜 ω s x；hs : UniqueDiffWithinAt 𝕜 s x；v : Fin (n +
 1) -> E。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurry
Fin_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 1) -> E) : alternatiz
eUncurryFin f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `fderivWithin_continuousAlternatingMap_apply_const_apply`：fderivWithin_co
ntinuousAlternatingMap_apply_const_apply (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : 
DifferentiableWithinAt 𝕜 c s x) (u : ι -> F) …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extDerivWithin_apply (h : DifferentiableWithinAt 𝕜 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (v : Fin (n + 1) → E) :
    extDerivWithin ω s x v =
      ∑ i, (-1) ^ i.val • fderivWithin 𝕜 (ω · (i.removeNth v)) s x (v i) := by
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply, *]
/-
**extDeriv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_apply (h : DifferentiableAt 𝕜 ω x) (v : Fin (n + 1) -> E) : extDe
riv ω x v = ∑ i, (-1) ^ i.val • fderiv 𝕜 (ω · (i.removeNth v)) x (v i)
参数：h : DifferentiableAt 𝕜 ω x；v : Fin (n + 1) -> E。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `extDerivWithin_apply`：extDerivWithin_apply (h : DifferentiableWithinAt 𝕜
 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x) (v : Fin (n + 1) -> E) : extDerivWithin 
ω s x v = …
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extDeriv_apply (h : DifferentiableAt 𝕜 ω x) (v : Fin (n + 1) → E) :
    extDeriv ω x v = ∑ i, (-1) ^ i.val • fderiv 𝕜 (ω · (i.removeNth v)) x (v i) := by
  simp [← extDerivWithin_univ, extDerivWithin_apply h.differentiableWithinAt]

/-- The second exterior derivative of a sufficiently smooth differential form is zero. -/
/-
**extDerivWithin_extDerivWithin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_extDerivWithin_apply (hω : ContDiffWithinAt 𝕜 r ω s x) (hr 
: minSmoothness 𝕜 2 <= r) (hs : UniqueDiffOn 𝕜 s) (hx : x in closure (interior s
)) (h'x : x in s) : extDerivWithin (extDerivWithin ω s) s x = 0
参数：hω : ContDiffWithinAt 𝕜 r ω s x；hr : minSmoothness 𝕜 2 <= r；hs : UniqueDiffOn
 𝕜 s；hx : x in closure (interior s)；h'x : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `ContDiffWithinAt.fderivWithin_right`：ContDiffWithinAt.fderivWithin_right
 (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (
hx₀s : x₀ in s) : ContDif…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `UniqueDiffOn.uniqueDiffWithinAt`：UniqueDiffOn.uniqueDiffWithinAt {s : Se
t E} {x} (hs : UniqueDiffOn R s) (h : x in s) : UniqueDiffWithinAt R s x
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_
comp_of_symmetric`：alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmet
ric {f : E ->L[𝕜] E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F} (hf : forall x y, f x y = f y x…
· 使用定理 `ContDiffWithinAt.isSymmSndFDerivWithinAt`：ContDiffWithinAt.isSymmSndFDer
ivWithinAt {n : Nat∞ω} (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2
 <= n) (hs : UniqueDiffOn 𝕜 s)…

--- 原说明 ---
The second exterior derivative of a sufficiently smooth differential form is zer
o.
-/
theorem extDerivWithin_extDerivWithin_apply (hω : ContDiffWithinAt 𝕜 r ω s x)
    (hr : minSmoothness 𝕜 2 ≤ r) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ closure (interior s))
    (h'x : x ∈ s) : extDerivWithin (extDerivWithin ω s) s x = 0 := calc
  extDerivWithin (extDerivWithin ω s) s x
    = alternatizeUncurryFin (fderivWithin 𝕜 (fun y ↦
        alternatizeUncurryFin (fderivWithin 𝕜 ω s y)) s x) := rfl
  _ = alternatizeUncurryFin (alternatizeUncurryFinCLM _ _ _ ∘L
        fderivWithin 𝕜 (fderivWithin 𝕜 ω s) s x) := by
    congr 1
    have : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 ω s) s x := by
      refine (hω.fderivWithin_right hs ?_ h'x).differentiableWithinAt one_ne_zero
      exact le_minSmoothness.trans hr
    exact alternatizeUncurryFinCLM _ _ _ |>.hasFDerivAt.comp_hasFDerivWithinAt x
      this.hasFDerivWithinAt |>.fderivWithin (hs.uniqueDiffWithinAt h'x)
  _ = 0 := alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric <|
    hω.isSymmSndFDerivWithinAt hr hs hx h'x

/-- The second exterior derivative of a sufficiently smooth differential form is zero. -/
/-
**extDerivWithin_extDerivWithin_eqOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_extDerivWithin_eqOn (hω : ContDiffOn 𝕜 r ω s) (hr : minSmoo
thness 𝕜 2 <= r) (hs : UniqueDiffOn 𝕜 s) : EqOn (extDerivWithin (extDerivWithin 
ω s) s) 0 (s inter closure (interior s))
参数：hω : ContDiffOn 𝕜 r ω s；hr : minSmoothness 𝕜 2 <= r；hs : UniqueDiffOn 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `extDerivWithin_extDerivWithin_apply`：extDerivWithin_extDerivWithin_apply
 (hω : ContDiffWithinAt 𝕜 r ω s x) (hr : minSmoothness 𝕜 2 <= r) (hs : UniqueDif
fOn 𝕜 s) (hx : x in closu…
· 使用定理 `ContDiffOn.contDiffWithinAt`：ContDiffOn.contDiffWithinAt (h : ContDiffOn
 𝕜 n f s) (hx : x in s) : ContDiffWithinAt 𝕜 n f s x

--- 原说明 ---
The second exterior derivative of a sufficiently smooth differential form is zer
o.
-/
theorem extDerivWithin_extDerivWithin_eqOn (hω : ContDiffOn 𝕜 r ω s) (hr : minSmoothness 𝕜 2 ≤ r)
    (hs : UniqueDiffOn 𝕜 s) :
    EqOn (extDerivWithin (extDerivWithin ω s) s) 0 (s ∩ closure (interior s)) := by
  rintro x ⟨h'x, hx⟩
  exact extDerivWithin_extDerivWithin_apply (hω.contDiffWithinAt h'x) hr hs hx h'x

/-- The second exterior derivative of a sufficiently smooth differential form is zero. -/
/-
**extDeriv_extDeriv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_extDeriv_apply (hω : ContDiffAt 𝕜 r ω x) (hr : minSmoothness 𝕜 2 
<= r) : extDeriv (extDeriv ω) x = 0
参数：hω : ContDiffAt 𝕜 r ω x；hr : minSmoothness 𝕜 2 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `extDerivWithin_extDerivWithin_apply`：extDerivWithin_extDerivWithin_apply
 (hω : ContDiffWithinAt 𝕜 r ω s x) (hr : minSmoothness 𝕜 2 <= r) (hs : UniqueDif
fOn 𝕜 s) (hx : x in closu…
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
The second exterior derivative of a sufficiently smooth differential form is zer
o.
-/
theorem extDeriv_extDeriv_apply (hω : ContDiffAt 𝕜 r ω x) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (extDeriv ω) x = 0 := by
  simp only [← extDerivWithin_univ]
  apply extDerivWithin_extDerivWithin_apply (s := univ) hω.contDiffWithinAt hr <;> simp

/-- The second exterior derivative of a sufficiently smooth differential form is zero. -/
/-
**extDeriv_extDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_extDeriv (h : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 <= r) : ext
Deriv (extDeriv ω) = 0
参数：h : ContDiff 𝕜 r ω；hr : minSmoothness 𝕜 2 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `extDeriv_extDeriv_apply`：extDeriv_extDeriv_apply (hω : ContDiffAt 𝕜 r ω 
x) (hr : minSmoothness 𝕜 2 <= r) : extDeriv (extDeriv ω) x = 0
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x

--- 原说明 ---
The second exterior derivative of a sufficiently smooth differential form is zer
o.
-/
theorem extDeriv_extDeriv (h : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (extDeriv ω) = 0 :=
  funext fun _ ↦ extDeriv_extDeriv_apply h.contDiffAt hr

/-- Exterior derivative within a set commutes with pullback. -/
/-
**extDerivWithin_pullback** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDerivWithin_pullback {ω : F -> F [⋀^Fin n]->L[𝕜] G} {f : E -> F} {t : S
et F} (hω : DifferentiableWithinAt 𝕜 ω t (f x)) (hf : ContDiffWithinAt 𝕜 r f s x
) (hr : minSmoothness 𝕜 2 <= r) (hs : UniqueDiffOn 𝕜 s) (hxc : x in closure (int
erior s)) (hxs : x in s) (hst : MapsTo f s t) : extDerivWithin (fun x => (ω (f x
)).compContinuousLinearMap (fderivWithin 𝕜 f s x)) s x = (extDerivWithin ω t (f 
x)).compContinuousLinearMap (fderivWithin 𝕜 f s x)
参数：hω : DifferentiableWithinAt 𝕜 ω t (f x)；hf : ContDiffWithinAt 𝕜 r f s x；hr : 
minSmoothness 𝕜 2 <= r；hs : UniqueDiffOn 𝕜 s；hxc : x in closure (interior s)；hxs
 : x in s；hst : MapsTo f s t。
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `ContDiffWithinAt.fderivWithin_right`：ContDiffWithinAt.fderivWithin_right
 (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (
hx₀s : x₀ in s) : ContDif…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extDerivWithin.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `fderivWithin_continuousAlternatingMapCompContinuousLinearMap`：fderivWith
in_continuousAlternatingMapCompContinuousLinearMap (hf : DifferentiableWithinAt 
𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) (hs…
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_add`：alternatizeUncurryFi
n_add (f g : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) : alternatizeUncurryFin (f + g) = alt
ernatizeUncurryFin f + alternatizeUncurr…
· 使用定理 `fderivWithin_fun_comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_fderivCompContinuousLinea
rMap_eq_zero`：alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero (f : F
 [⋀^Fin n]->L[𝕜] G) (g : E ->L[𝕜] F) {h : E ->L[𝕜] E ->L[𝕜] F} (hsymm : fo…
· 使用定理 `ContDiffWithinAt.isSymmSndFDerivWithinAt`：ContDiffWithinAt.isSymmSndFDer
ivWithinAt {n : Nat∞ω} (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2
 <= n) (hs : UniqueDiffOn 𝕜 s)…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Exterior derivative within a set commutes with pullback.
-/
theorem extDerivWithin_pullback {ω : F → F [⋀^Fin n]→L[𝕜] G} {f : E → F} {t : Set F}
    (hω : DifferentiableWithinAt 𝕜 ω t (f x)) (hf : ContDiffWithinAt 𝕜 r f s x)
    (hr : minSmoothness 𝕜 2 ≤ r) (hs : UniqueDiffOn 𝕜 s)
    (hxc : x ∈ closure (interior s)) (hxs : x ∈ s) (hst : MapsTo f s t) :
    extDerivWithin (fun x ↦ (ω (f x)).compContinuousLinearMap (fderivWithin 𝕜 f s x)) s x =
      (extDerivWithin ω t (f x)).compContinuousLinearMap (fderivWithin 𝕜 f s x) := by
  have hdf : DifferentiableWithinAt 𝕜 f s x :=
    hf.differentiableWithinAt <| (two_pos.trans_le <| le_minSmoothness.trans hr).ne'
  have hd2f : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (le_minSmoothness.trans hr) hxs).differentiableWithinAt one_ne_zero
  rw [extDerivWithin,
    fderivWithin_continuousAlternatingMapCompContinuousLinearMap (by exact hω.comp x hdf hst) hd2f
      (hs x hxs),
    alternatizeUncurryFin_add, fderivWithin_fun_comp _ hω hdf hst (hs x hxs), extDerivWithin,
    alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero, add_zero]
  · ext v
    simp +unfoldPartialApp [alternatizeUncurryFin_apply, Fin.removeNth, Function.comp_def]
  · apply hf.isSymmSndFDerivWithinAt <;> assumption

/-- Exterior derivative commutes with pullback. -/
/-
**extDeriv_pullback** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extDeriv_pullback {ω : F -> F [⋀^Fin n]->L[𝕜] G} {f : E -> F} (hω : Differ
entiableAt 𝕜 ω (f x)) (hf : ContDiffAt 𝕜 r f x) (hr : minSmoothness 𝕜 2 <= r) : 
extDeriv (fun x => (ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)) x = (extDer
iv ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)
参数：hω : DifferentiableAt 𝕜 ω (f x)；hf : ContDiffAt 𝕜 r f x；hr : minSmoothness 𝕜 
2 <= r。
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `extDerivWithin_pullback`：extDerivWithin_pullback {ω : F -> F [⋀^Fin n]->
L[𝕜] G} {f : E -> F} {t : Set F} (hω : DifferentiableWithinAt 𝕜 ω t (f x)) (hf :
 ContDiffWith…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
Exterior derivative commutes with pullback.
-/
theorem extDeriv_pullback {ω : F → F [⋀^Fin n]→L[𝕜] G} {f : E → F}
    (hω : DifferentiableAt 𝕜 ω (f x)) (hf : ContDiffAt 𝕜 r f x) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)) x =
      (extDeriv ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x) := by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← contDiffWithinAt_univ,
    ← fderivWithin_univ] at *
  apply extDerivWithin_pullback (r := r) <;> simp [*]
