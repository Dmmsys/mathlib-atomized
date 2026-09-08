/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Analysis.Normed.Operator.Prod

/-! ## Equivalence of smoothness with the basic definition for functions between vector spaces

* `contMDiff_iff_contDiff`: for functions between vector spaces,
  manifold-smoothness is equivalent to usual smoothness.
* `ContinuousLinearMap.contMDiff`: continuous linear maps between normed spaces are smooth

Smoothness of addition and scalar multiplication in normed spaces is proven not here but in
`Mathlib/Geometry/Manifold/Algebra/LieGroup.lean` and `Mathlib/Geometry/Manifold/Algebra/SMul.lean`
in the form of `LieAddGroup` and `ContMDiffSMul` instances.

-/

public section

open Set ChartedSpace
open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare normed spaces `E'`, `F`, `F'`, `F₁`, `F₂`, `F₃`, `F₄`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  -- declare functions, sets, points and smoothness indices
  {s : Set M} {x : M} {n : WithTop ℕ∞}

section Module

set_option backward.isDefEq.respectTransparency false in
/-
**contMDiffWithinAt_iff_contDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_contDiffWithinAt {f : E -> E'} {s : Set E} {x : E} :
 ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.refl_apply`：∀ (X : Type u_7) [inst : TopologicalSp
ace X], ↑(OpenPartialHomeomorph.refl X) = id
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x
-/
theorem contMDiffWithinAt_iff_contDiffWithinAt {f : E → E'} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x := by
  simp +contextual only [ContMDiffWithinAt, liftPropWithinAt_iff',
    ContDiffWithinAtProp, iff_def, mfld_simps]
  exact ContDiffWithinAt.continuousWithinAt

alias ⟨ContMDiffWithinAt.contDiffWithinAt, ContDiffWithinAt.contMDiffWithinAt⟩ :=
  contMDiffWithinAt_iff_contDiffWithinAt
/-
**contMDiffAt_iff_contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_contDiffAt {f : E -> E'} {x : E} : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜
, E') n f x ↔ ContDiffAt 𝕜 n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用定理 `contMDiffWithinAt_iff_contDiffWithinAt`：contMDiffWithinAt_iff_contDiffWi
thinAt {f : E -> E'} {s : Set E} {x : E} : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n 
f s x ↔ ContDiffWithinAt 𝕜 n…
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contMDiffAt_iff_contDiffAt {f : E → E'} {x : E} :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f x ↔ ContDiffAt 𝕜 n f x := by
  rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_contDiffWithinAt, contDiffWithinAt_univ]

alias ⟨ContMDiffAt.contDiffAt, ContDiffAt.contMDiffAt⟩ := contMDiffAt_iff_contDiffAt
/-
**contMDiffOn_iff_contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_iff_contDiffOn {f : E -> E'} {s : Set E} : ContMDiffOn 𝓘(𝕜, E)
 𝓘(𝕜, E') n f s ↔ ContDiffOn 𝕜 n f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem contMDiffOn_iff_contDiffOn {f : E → E'} {s : Set E} :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s ↔ ContDiffOn 𝕜 n f s :=
  forall_congr' <| by simp [contMDiffWithinAt_iff_contDiffWithinAt]

alias ⟨ContMDiffOn.contDiffOn, ContDiffOn.contMDiffOn⟩ := contMDiffOn_iff_contDiffOn
/-
**contMDiff_iff_contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_iff_contDiff {f : E -> E'} : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ Co
ntDiff 𝕜 n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `contMDiffOn_iff_contDiffOn`：contMDiffOn_iff_contDiffOn {f : E -> E'} {s 
: Set E} : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s ↔ ContDiffOn 𝕜 n f s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contMDiff_iff_contDiff {f : E → E'} : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← contMDiffOn_univ, contMDiffOn_iff_contDiffOn]

alias ⟨ContMDiff.contDiff, ContDiff.contMDiff⟩ := contMDiff_iff_contDiff
/-
**ContDiffWithinAt.comp_contMDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.comp_contMDiffWithinAt {g : F -> F'} {f : M -> F} {s : Se
t M} {t : Set F} {x : M} (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContMDiffWi
thinAt I 𝓘(𝕜, F) n f s x) (h : s subseteq f ⁻¹' t) : ContMDiffWithinAt I 𝓘(𝕜, F'
) n (g ∘ f) s x
参数：hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x；
h : s subseteq f ⁻¹' t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `ContDiffWithinAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
-/
theorem ContDiffWithinAt.comp_contMDiffWithinAt {g : F → F'} {f : M → F} {s : Set M} {t : Set F}
    {x : M} (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x)
    (h : s ⊆ f ⁻¹' t) : ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x :=
  hg.contMDiffWithinAt.comp x hf h
/-
**ContDiffAt.comp_contMDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.comp_contMDiffWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {
x : M} (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x) 
: ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x
参数：hg : ContDiffAt 𝕜 n g (f x)；hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt`：ContMDiffAt.comp_contMDiffWithinAt {
g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithin
At I I' n f s x) : ContM…
· 使用定理 `ContDiffAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
-/
theorem ContDiffAt.comp_contMDiffWithinAt {g : F → F'} {f : M → F} {s : Set M}
    {x : M} (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x :=
  hg.contMDiffAt.comp_contMDiffWithinAt x hf
/-
**ContDiffAt.comp_contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.comp_contMDiffAt {g : F -> F'} {f : M -> F} {x : M} (hg : ContD
iffAt 𝕜 n g (f x)) (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) : ContMDiffAt I 𝓘(𝕜, F') n
 (g ∘ f) x
参数：hg : ContDiffAt 𝕜 n g (f x)；hf : ContMDiffAt I 𝓘(𝕜, F) n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contMDiffWithinAt`：ContDiffAt.comp_contMDiffWithinAt {g 
: F -> F'} {f : M -> F} {s : Set M} {x : M} (hg : ContDiffAt 𝕜 n g (f x)) (hf : 
ContMDiffWithinAt I 𝓘(𝕜…
-/
theorem ContDiffAt.comp_contMDiffAt {g : F → F'} {f : M → F} {x : M} (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) : ContMDiffAt I 𝓘(𝕜, F') n (g ∘ f) x :=
  hg.comp_contMDiffWithinAt hf
/-
**ContDiff.comp_contMDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp_contMDiffWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x 
: M} (hg : ContDiff 𝕜 n g) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x) : ContMDif
fWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x
参数：hg : ContDiff 𝕜 n g；hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contMDiffWithinAt`：ContDiffAt.comp_contMDiffWithinAt {g 
: F -> F'} {f : M -> F} {s : Set M} {x : M} (hg : ContDiffAt 𝕜 n g (f x)) (hf : 
ContMDiffWithinAt I 𝓘(𝕜…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.comp_contMDiffWithinAt {g : F → F'} {f : M → F} {s : Set M} {x : M}
    (hg : ContDiff 𝕜 n g) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x :=
  hg.contDiffAt.comp_contMDiffWithinAt hf
/-
**ContDiff.comp_contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp_contMDiffAt {g : F -> F'} {f : M -> F} {x : M} (hg : ContDif
f 𝕜 n g) (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) : ContMDiffAt I 𝓘(𝕜, F') n (g ∘ f) x
参数：hg : ContDiff 𝕜 n g；hf : ContMDiffAt I 𝓘(𝕜, F) n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contMDiffWithinAt`：ContDiff.comp_contMDiffWithinAt {g : F 
-> F'} {f : M -> F} {s : Set M} {x : M} (hg : ContDiff 𝕜 n g) (hf : ContMDiffWit
hinAt I 𝓘(𝕜, F) n f s…
-/
theorem ContDiff.comp_contMDiffAt {g : F → F'} {f : M → F} {x : M} (hg : ContDiff 𝕜 n g)
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) : ContMDiffAt I 𝓘(𝕜, F') n (g ∘ f) x :=
  hg.comp_contMDiffWithinAt hf
/-
**ContDiff.comp_contMDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp_contMDiff {g : F -> F'} {f : M -> F} (hg : ContDiff 𝕜 n g) (
hf : ContMDiff I 𝓘(𝕜, F) n f) : ContMDiff I 𝓘(𝕜, F') n (g ∘ f)
参数：hg : ContDiff 𝕜 n g；hf : ContMDiff I 𝓘(𝕜, F) n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contMDiffAt`：ContDiffAt.comp_contMDiffAt {g : F -> F'} {
f : M -> F} {x : M} (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContMDiffAt I 𝓘(𝕜, F) n 
f x) : ContMDiffA…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.comp_contMDiff {g : F → F'} {f : M → F} (hg : ContDiff 𝕜 n g)
    (hf : ContMDiff I 𝓘(𝕜, F) n f) : ContMDiff I 𝓘(𝕜, F') n (g ∘ f) := fun x =>
  hg.contDiffAt.comp_contMDiffAt (hf x)

end Module

/-! ### Linear maps between normed spaces are smooth -/

/-
**ContinuousLinearMap.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.contMDiff (L : E ->L[𝕜] F) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F)
 n L
参数：L : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' 
: Type u…
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f

--- 原说明 ---
### Linear maps between normed spaces are smooth
-/
theorem ContinuousLinearMap.contMDiff (L : E →L[𝕜] F) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L :=
  L.contDiff.contMDiff
/-
**ContinuousLinearMap.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.contMDiffAt (L : E ->L[𝕜] F) {x} : ContMDiffAt 𝓘(𝕜, E)
 𝓘(𝕜, F) n L x
参数：L : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.contMDiff`：ContinuousLinearMap.contMDiff (L : E ->L[
𝕜] F) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L
-/
theorem ContinuousLinearMap.contMDiffAt (L : E →L[𝕜] F) {x} : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L x :=
  L.contMDiff _
/-
**ContinuousLinearMap.contMDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.contMDiffWithinAt (L : E ->L[𝕜] F) {s x} : ContMDiffWi
thinAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L s x
参数：L : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `ContinuousLinearMap.contMDiffAt`：ContinuousLinearMap.contMDiffAt (L : E 
->L[𝕜] F) {x} : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L x
-/
theorem ContinuousLinearMap.contMDiffWithinAt (L : E →L[𝕜] F) {s x} :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L s x :=
  L.contMDiffAt.contMDiffWithinAt
/-
**ContinuousLinearMap.contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.contMDiffOn (L : E ->L[𝕜] F) {s} : ContMDiffOn 𝓘(𝕜, E)
 𝓘(𝕜, F) n L s
参数：L : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `ContinuousLinearMap.contMDiff`：ContinuousLinearMap.contMDiff (L : E ->L[
𝕜] F) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L
-/
theorem ContinuousLinearMap.contMDiffOn (L : E →L[𝕜] F) {s} : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n L s :=
  L.contMDiff.contMDiffOn
/-
**ContMDiffWithinAt.clm_precomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} {x : M} 
(hf : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f s x) : ContMDiffWithinAt I 𝓘(𝕜,
 (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n (fun y => (f y).precomp F₃ : M -> (F₂ -
>L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) s x
参数：hf : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContDiff.comp_contMDiffWithinAt`：ContDiff.comp_contMDiffWithinAt {g : F 
-> F'} {f : M -> F} {s : Set M} {x : M} (hg : ContDiff 𝕜 n g) (hf : ContMDiffWit
hinAt I 𝓘(𝕜, F) n f s…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
-/
theorem ContMDiffWithinAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) s x :=
  ContDiff.comp_contMDiffWithinAt (g := (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip)
    (ContinuousLinearMap.contDiff _) hf

nonrec theorem ContMDiffAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  hf.clm_precomp
/-
**ContMDiffOn.clm_precomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} (hf : ContMDif
fOn I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f s) : ContMDiffOn I 𝓘(𝕜, (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ -
>L[𝕜] F₃)) n (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] 
F₃)) s
参数：hf : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffWithinAt.clm_precomp`：ContMDiffWithinAt.clm_precomp {f : M -> F
₁ ->L[𝕜] F₂} {s : Set M} {x : M} (hf : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n 
f s x) : ContMDiffW…
-/
theorem ContMDiffOn.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) n f s) :
    ContMDiffOn I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) s := fun x hx ↦
  (hf x hx).clm_precomp
/-
**ContMDiff.clm_precomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} (hf : ContMDiff I 𝓘(𝕜, F₁ ->
L[𝕜] F₂) n f) : ContMDiff I 𝓘(𝕜, (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n (fun y 
=> (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃))
参数：hf : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffAt.clm_precomp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
-/
theorem ContMDiff.clm_precomp {f : M → F₁ →L[𝕜] F₂} (hf : ContMDiff I 𝓘(𝕜, F₁ →L[𝕜] F₂) n f) :
    ContMDiff I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) := fun x ↦
  (hf x).clm_precomp
/-
**ContMDiffWithinAt.clm_postcomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} {x : M}
 (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f s x) : ContMDiffWithinAt I 𝓘(𝕜
, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n (fun y => (f y).postcomp F₁ : M -> (F₁
 ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) s x
参数：hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContDiff.comp_contMDiffWithinAt`：ContDiff.comp_contMDiffWithinAt {g : F 
-> F'} {f : M -> F} {s : Set M} {x : M} (hg : ContDiff 𝕜 n g) (hf : ContMDiffWit
hinAt I 𝓘(𝕜, F) n f s…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
-/
theorem ContMDiffWithinAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) s x :=
  ContDiff.comp_contMDiffWithinAt (F' := (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃))
    (g := ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃) (ContinuousLinearMap.contDiff _) hf

nonrec theorem ContMDiffAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  hf.clm_postcomp

nonrec theorem ContMDiffOn.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f s) :
    ContMDiffOn I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) s := fun x hx ↦
  (hf x hx).clm_postcomp
/-
**ContMDiff.clm_postcomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} (hf : ContMDiff I 𝓘(𝕜, F₂ -
>L[𝕜] F₃) n f) : ContMDiff I 𝓘(𝕜, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n (fun y
 => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃))
参数：hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffAt.clm_postcomp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {H : Type u_…
-/
theorem ContMDiff.clm_postcomp {f : M → F₂ →L[𝕜] F₃} (hf : ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f) :
    ContMDiff I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) := fun x ↦
  (hf x).clm_postcomp
/-
**ContMDiffWithinAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁}
 {s : Set M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s x) (hf :
 ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n f s x) : ContMDiffWithinAt I 𝓘(𝕜, F₂ -
>L[𝕜] F₃) n (fun x => (g x).comp (f x)) s x
参数：hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s x；hf : ContMDiffWithinAt I 
𝓘(𝕜, F₂ ->L[𝕜] F₁) n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContDiff.comp_contMDiffWithinAt`：ContDiff.comp_contMDiffWithinAt {g : F 
-> F'} {f : M -> F} {s : Set M} {x : M} (hg : ContDiff 𝕜 n g) (hf : ContMDiffWit
hinAt I 𝓘(𝕜, F) n f s…
· 使用定理 `ContDiff.clm_comp`：ContDiff.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E -
>L[𝕜] F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (g 
x).comp…
· 使用定理 `contDiff_fst`：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)
· 使用定理 `contDiff_snd`：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)
· 使用定理 `ContMDiffWithinAt.prodMk_space`：ContMDiffWithinAt.prodMk_space {f : M ->
 E'} {g : M -> F'} (hf : ContMDiffWithinAt I 𝓘(𝕜, E') n f s x) (hg : ContMDiffWi
thinAt I 𝓘(𝕜, F') n …
-/
theorem ContMDiffWithinAt.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M} {x : M}
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (fun x => (g x).comp (f x)) s x :=
  ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (contDiff_fst.clm_comp contDiff_snd) (hg.prodMk_space hf)
/-
**ContMDiffAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {x : 
M} (hg : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L
[𝕜] F₁) n f x) : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n (fun x => (g x).comp (f x)) 
x
参数：hg : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g x；hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜]
 F₁) n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffWithinAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `ContMDiffWithinAt.clm_comp`：ContMDiffWithinAt.clm_comp {g : M -> F₁ ->L[
𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜
, F₁ ->L[𝕜] F₃) …
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem ContMDiffAt.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (fun x => (g x).comp (f x)) x :=
  (hg.contMDiffWithinAt.clm_comp hf.contMDiffWithinAt).contMDiffAt Filter.univ_mem
/-
**ContMDiffOn.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : 
Set M} (hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₂
 ->L[𝕜] F₁) n f s) : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n (fun x => (g x).comp (f 
x)) s
参数：hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s；hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜]
 F₁) n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffWithinAt.clm_comp`：ContMDiffWithinAt.clm_comp {g : M -> F₁ ->L[
𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜
, F₁ ->L[𝕜] F₃) …
-/
theorem ContMDiffOn.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f s) :
    ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (fun x => (g x).comp (f x)) s := fun x hx =>
  (hg x hx).clm_comp (hf x hx)
/-
**ContMDiff.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} (hg : C
ontMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g) (hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n f) : C
ontMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n fun x => (g x).comp (f x)
参数：hg : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g；hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n
 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffAt.clm_comp`：ContMDiffAt.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : 
M -> F₂ ->L[𝕜] F₁} {x : M} (hg : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g x) (hf : C
ontMDiffAt…
-/
theorem ContMDiff.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁}
    (hg : ContMDiff I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g) (hf : ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f) :
    ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₃) n fun x => (g x).comp (f x) := fun x => (hg x).clm_comp (hf x)

/-- Applying a linear map to a vector is smooth within a set. Version in vector spaces. For
versions in nontrivial vector bundles, see `ContMDiffWithinAt.clm_apply_of_inCoordinates` and
`ContMDiffWithinAt.clm_bundle_apply`. -/
/-
**ContMDiffWithinAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set
 M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g s x) (hf : ContMDif
fWithinAt I 𝓘(𝕜, F₁) n f s x) : ContMDiffWithinAt I 𝓘(𝕜, F₂) n (fun x => g x (f 
x)) s x
参数：hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g s x；hf : ContMDiffWithinAt I 
𝓘(𝕜, F₁) n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContDiffWithinAt.comp_contMDiffWithinAt`：ContDiffWithinAt.comp_contMDiff
WithinAt {g : F -> F'} {f : M -> F} {s : Set M} {t : Set F} {x : M} (hg : ContDi
ffWithinAt 𝕜 n g t (f x)) (hf…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `ContDiff.clm_apply`：ContDiff.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F
} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x
)
· 使用定理 `contDiff_fst`：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)
· 使用定理 `contDiff_snd`：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)
· 使用定理 `ContMDiffWithinAt.prodMk_space`：ContMDiffWithinAt.prodMk_space {f : M ->
 E'} {g : M -> F'} (hf : ContMDiffWithinAt I 𝓘(𝕜, E') n f s x) (hg : ContMDiffWi
thinAt I 𝓘(𝕜, F') n …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Applying a linear map to a vector is smooth within a set. Version in vector spac
es. For
versions in nontrivial vector bundles, see `ContMDiffWithinAt.clm_apply_of_inCoo
rdinates` and
`ContMDiffWithinAt.clm_bundle_apply`.
-/
theorem ContMDiffWithinAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M} {x : M}
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₁) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F₂) n (fun x => g x (f x)) s x :=
  ContDiffWithinAt.comp_contMDiffWithinAt (t := univ)
    (g := fun x : (F₁ →L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply ContDiff.contDiffAt; exact contDiff_fst.clm_apply contDiff_snd) (hg.prodMk_space hf)
    (by simp_rw [preimage_univ, subset_univ])

/-- Applying a linear map to a vector is smooth. Version in vector spaces. For
versions in nontrivial vector bundles, see `ContMDiffAt.clm_apply_of_inCoordinates` and
`ContMDiffAt.clm_bundle_apply`. -/
nonrec theorem ContMDiffAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₁) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₂) n (fun x => g x (f x)) x :=
  hg.clm_apply hf

/-
**ContMDiffOn.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M} (h
g : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₁) n f s) 
: ContMDiffOn I 𝓘(𝕜, F₂) n (fun x => g x (f x)) s
参数：hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g s；hf : ContMDiffOn I 𝓘(𝕜, F₁) n f s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffWithinAt.clm_apply`：ContMDiffWithinAt.clm_apply {g : M -> F₁ ->
L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L
[𝕜] F₂) n g s x) …
-/
theorem ContMDiffOn.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₁) n f s) :
    ContMDiffOn I 𝓘(𝕜, F₂) n (fun x => g x (f x)) s := fun x hx => (hg x hx).clm_apply (hf x hx)
/-
**ContMDiff.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} (hg : ContMDiff 
I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g) (hf : ContMDiff I 𝓘(𝕜, F₁) n f) : ContMDiff I 𝓘(𝕜, F₂)
 n fun x => g x (f x)
参数：hg : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g；hf : ContMDiff I 𝓘(𝕜, F₁) n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffAt.clm_apply`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
-/
theorem ContMDiff.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁}
    (hg : ContMDiff I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g) (hf : ContMDiff I 𝓘(𝕜, F₁) n f) :
    ContMDiff I 𝓘(𝕜, F₂) n fun x => g x (f x) := fun x => (hg x).clm_apply (hf x)
/-
**ContMDiffWithinAt.cle_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜]
 F₄} {s : Set M} {x : M} (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x =
> ((f x).symm : F₂ ->L[𝕜] F₁)) s x) (hg : ContMDiffWithinAt I 𝓘(𝕜, F₃ ->L[𝕜] F₄)
 n (fun x => (g x : F₃ ->L[𝕜] F₄)) s x) : ContMDiffWithinAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃
) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃
) ->L[𝕜] (F₂ ->L[𝕜] F₄)) s x
参数：hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[
𝕜] F₁)) s x；hg : ContMDiffWithinAt I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->
L[𝕜] F₄)) s x。
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
· 使用定理 `ContMDiffWithinAt.clm_comp`：ContMDiffWithinAt.clm_comp {g : M -> F₁ ->L[
𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜
, F₁ ->L[𝕜] F₃) …
· 使用定理 `ContMDiffWithinAt.clm_precomp`：ContMDiffWithinAt.clm_precomp {f : M -> F
₁ ->L[𝕜] F₂} {s : Set M} {x : M} (hf : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n 
f s x) : ContMDiffW…
· 使用定理 `ContMDiffWithinAt.clm_postcomp`：ContMDiffWithinAt.clm_postcomp {f : M ->
 F₂ ->L[𝕜] F₃} {s : Set M} {x : M} (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) 
n f s x) : ContMDiff…
-/
theorem ContMDiffWithinAt.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄}
    {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) s x)
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₃ →L[𝕜] F₄) n (fun x ↦ (g x : F₃ →L[𝕜] F₄)) s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) s x :=
  show ContMDiffWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
    (fun y ↦ (((f y).symm : F₂ →L[𝕜] F₁).precomp F₄).comp ((g y : F₃ →L[𝕜] F₄).postcomp F₁)) s x
  from hf.clm_precomp (F₃ := F₄) |>.clm_comp <| hg.clm_postcomp (F₁ := F₁)

nonrec theorem ContMDiffAt.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) x)
    (hg : ContMDiffAt I 𝓘(𝕜, F₃ →L[𝕜] F₄) n (fun x ↦ (g x : F₃ →L[𝕜] F₄)) x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) x :=
  hf.cle_arrowCongr hg
/-
**ContMDiffOn.cle_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {
s : Set M} (hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ -
>L[𝕜] F₁)) s) (hg : ContMDiffOn I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜
] F₄)) s) : ContMDiffOn I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n (fun y =>
 (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) s
参数：hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)
) s；hg : ContMDiffOn I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜] F₄)) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffWithinAt.cle_arrowCongr`：ContMDiffWithinAt.cle_arrowCongr {f : 
M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : Set M} {x : M} (hf : ContMDiffWith
inAt I 𝓘(𝕜, F₂ ->L[𝕜] …
-/
theorem ContMDiffOn.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₁) n (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) s)
    (hg : ContMDiffOn I 𝓘(𝕜, F₃ →L[𝕜] F₄) n (fun x ↦ (g x : F₃ →L[𝕜] F₄)) s) :
    ContMDiffOn I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) s := fun x hx ↦
  (hf x hx).cle_arrowCongr (hg x hx)
/-
**ContMDiff.cle_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} (hf
 : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[𝕜] F₁))) (hg 
: ContMDiff I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜] F₄))) : ContMDiff 
I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n (fun y => (f y).arrowCongr (g y) 
: M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄))
参数：hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[𝕜] F₁))；
hg : ContMDiff I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜] F₄))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffAt.cle_arrowCongr`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
-/
theorem ContMDiff.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄}
    (hf : ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₁) n (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)))
    (hg : ContMDiff I 𝓘(𝕜, F₃ →L[𝕜] F₄) n (fun x ↦ (g x : F₃ →L[𝕜] F₄))) :
    ContMDiff I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) := fun x ↦
  (hf x).cle_arrowCongr (hg x)
/-
**ContMDiffWithinAt.clm_prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] 
F₄} {s : Set M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s x) (h
f : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₄) n f s x) : ContMDiffWithinAt I 𝓘(𝕜, F
₁ × F₂ ->L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) s x
参数：hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s x；hf : ContMDiffWithinAt I 
𝓘(𝕜, F₂ ->L[𝕜] F₄) n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContDiff.comp_contMDiffWithinAt`：ContDiff.comp_contMDiffWithinAt {g : F 
-> F'} {f : M -> F} {s : Set M} {x : M} (hg : ContDiff 𝕜 n g) (hf : ContMDiffWit
hinAt I 𝓘(𝕜, F) n f s…
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `ContMDiffWithinAt.prodMk_space`：ContMDiffWithinAt.prodMk_space {f : M ->
 E'} {g : M -> F'} (hf : ContMDiffWithinAt I 𝓘(𝕜, E') n f s x) (hg : ContMDiffWi
thinAt I 𝓘(𝕜, F') n …
-/
theorem ContMDiffWithinAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) s x :=
  ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).contDiff
    (hg.prodMk_space hf)

nonrec theorem ContMDiffAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) x :=
  hg.clm_prodMap hf
/-
**ContMDiffOn.clm_prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s
 : Set M} (hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s) (hf : ContMDiffOn I 𝓘(𝕜,
 F₂ ->L[𝕜] F₄) n f s) : ContMDiffOn I 𝓘(𝕜, F₁ × F₂ ->L[𝕜] F₃ × F₄) n (fun x => (
g x).prodMap (f x)) s
参数：hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s；hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜]
 F₄) n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffWithinAt.clm_prodMap`：ContMDiffWithinAt.clm_prodMap {g : M -> F
₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M} {x : M} (hg : ContMDiffWithinAt
 I 𝓘(𝕜, F₁ ->L[𝕜] F…
-/
theorem ContMDiffOn.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f s) :
    ContMDiffOn I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) s := fun x hx =>
  (hg x hx).clm_prodMap (hf x hx)
/-
**ContMDiff.clm_prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} (hg 
: ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g) (hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₄) n f) 
: ContMDiff I 𝓘(𝕜, F₁ × F₂ ->L[𝕜] F₃ × F₄) n fun x => (g x).prodMap (f x)
参数：hg : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g；hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₄) n
 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffAt.clm_prodMap`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
-/
theorem ContMDiff.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄}
    (hg : ContMDiff I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g) (hf : ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f) :
    ContMDiff I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n fun x => (g x).prodMap (f x) := fun x =>
  (hg x).clm_prodMap (hf x)
