/-
Copyright (c) 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Standard constructions on vector bundles

This file contains several standard constructions on vector bundles:

* `Bundle.Trivial.vectorBundle 𝕜 B F`: the trivial vector bundle with scalar field `𝕜` and model
  fiber `F` over the base `B`

* `VectorBundle.prod`: for vector bundles `E₁` and `E₂` with scalar field `𝕜` over a common base,
  a vector bundle structure on their direct sum `E₁ ×ᵇ E₂` (the notation stands for
  `fun x ↦ E₁ x × E₂ x`).

* `VectorBundle.pullback`: for a vector bundle `E` over `B`, a vector bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags
Vector bundle, direct sum, pullback
-/

public section

noncomputable section

open Bundle Set FiberBundle

/-! ### The trivial vector bundle -/

namespace Bundle.Trivial

variable (𝕜 : Type*) (B : Type*) (F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [TopologicalSpace B]

/-
**Bundle.Trivial.trivialization.isLinear** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
al.trivialization`。
形式化陈述：∀ (𝕜 : Type u_1) (B : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] [inst_3 : T
opologicalSpace B],   Bundle.Trivialization.IsLinear 𝕜 (Bundle.Trivial.trivializ
ation B F)
参数：𝕜 : Type u_1；B : Type u_2；F : Type u_3；Bundle.Trivial.trivialization B F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance trivialization.isLinear : (trivialization B F).IsLinear 𝕜 where
  linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

variable {𝕜} in
/-
**Bundle.Trivial.trivialization.coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.T
rivial.trivialization`。
形式化陈述：∀ {𝕜 : Type u_1} (B : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] [inst_3 : T
opologicalSpace B] (b : B),   Bundle.Trivialization.coordChangeL 𝕜 (Bundle.Trivi
al.trivialization B F) (Bundle.Trivial.trivialization B F) b =     ContinuousLin
earEquiv.refl 𝕜 F
参数：B : Type u_2；F : Type u_3；b : B；Bundle.Trivial.trivialization B F；Bundle.Triv
ial.trivialization B F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `Bundle.Trivial.trivialization.isLinear`：∀ (𝕜 : Type u_1) (B : Type u_2) 
(F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coordChangeL_apply'`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSp
ace F]   [inst_2 : TopologicalS…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem trivialization.coordChangeL (b : B) :
    (trivialization B F).coordChangeL 𝕜 (trivialization B F) b =
      ContinuousLinearEquiv.refl 𝕜 F := by
  ext v
  rw [Trivialization.coordChangeL_apply']
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]
/-
**Bundle.Trivial.vectorBundle** 是 Mathlib 中的一个实例，位于命名空间 `Bundle.Trivial`。
形式化陈述：vectorBundle : VectorBundle 𝕜 F (Bundle.Trivial B F) where trivialization_
linear' e he
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivial.eq_trivialization`：eq_trivialization (e : Trivialization 
F (π F (Bundle.Trivial B F))) [i : MemTrivializationAtlas e] : e = trivializatio
n B F
· 使用定理 `Bundle.Trivial.trivialization.isLinear`：∀ (𝕜 : Type u_1) (B : Type u_2) 
(F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bundle.Trivial.trivialization.coordChangeL`：∀ {𝕜 : Type u_1} (B : Type u
_2) (F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGro
up F]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
instance vectorBundle : VectorBundle 𝕜 F (Bundle.Trivial B F) where
  trivialization_linear' e he := by
    rw [eq_trivialization B F e]
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain rfl := eq_trivialization B F e
    obtain rfl := eq_trivialization B F e'
    simp only [trivialization.coordChangeL]
    exact continuous_const.continuousOn
/-
**Bundle.Trivial.linearMapAt_trivialization** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Tr
ivial`。
形式化陈述：∀ (𝕜 : Type u_1) (B : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] [inst_3 : T
opologicalSpace B] (x : B),   Bundle.Trivialization.linearMapAt 𝕜 (Bundle.Trivia
l.trivialization B F) x = LinearMap.id
参数：𝕜 : Type u_1；B : Type u_2；F : Type u_3；x : B；Bundle.Trivial.trivialization B 
F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Bundle.Trivial.trivialization.isLinear`：∀ (𝕜 : Type u_1) (B : Type u_2) 
(F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bundle.Trivial.trivialization_baseSet`：∀ (B : Type u_1) (F : Type u_2) [
inst : TopologicalSpace B] [inst_1 : TopologicalSpace F],   (Bundle.Trivial.triv
ialization B F).baseSet = S…
-/
@[simp] lemma linearMapAt_trivialization (x : B) :
    (trivialization B F).linearMapAt 𝕜 x = LinearMap.id := by
  ext v
  rw [Trivialization.coe_linearMapAt_of_mem _ (by simp)]
  rfl
/-
**Bundle.Trivial.continuousLinearMapAt_trivialization** 是 Mathlib 中的一个定理，位于命名空间 
`Bundle.Trivial`。
形式化陈述：∀ (𝕜 : Type u_1) (B : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] [inst_3 : T
opologicalSpace B] (x : B),   Bundle.Trivialization.continuousLinearMapAt 𝕜 (Bun
dle.Trivial.trivialization B F) x = ContinuousLinearMap.id 𝕜 F
参数：𝕜 : Type u_1；B : Type u_2；F : Type u_3；x : B；Bundle.Trivial.trivialization B 
F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Bundle.Trivial.trivialization.isLinear`：∀ (𝕜 : Type u_1) (B : Type u_2) 
(F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearMapAt_apply`：∀ (R : Type u_1) {B :
 Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R] 
  [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivial.linearMapAt_trivialization`：∀ (𝕜 : Type u_1) (B : Type u_
2) (F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGrou
p F]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma continuousLinearMapAt_trivialization (x : B) :
    (trivialization B F).continuousLinearMapAt 𝕜 x = ContinuousLinearMap.id 𝕜 F := by
  ext; simp
/-
**Bundle.Trivial.symm** 是 Mathlib 中的一个引理，位于命名空间 `Bundle.Trivial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symmₗ_trivialization (x : B) :
    (trivialization B F).symmₗ 𝕜 x = LinearMap.id := by
  ext; simp [trivialization_symm_apply B F]
/-
**Bundle.Trivial.symmL_trivialization** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivial`
。
形式化陈述：∀ (𝕜 : Type u_1) (B : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] [inst_3 : T
opologicalSpace B] (x : B),   Bundle.Trivialization.symmL 𝕜 (Bundle.Trivial.triv
ialization B F) x = ContinuousLinearMap.id 𝕜 F
参数：𝕜 : Type u_1；B : Type u_2；F : Type u_3；x : B；Bundle.Trivial.trivialization B 
F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Bundle.Trivial.trivialization.isLinear`：∀ (𝕜 : Type u_1) (B : Type u_2) 
(F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivial.trivialization_baseSet`：∀ (B : Type u_1) (F : Type u_2) [
inst : TopologicalSpace B] [inst_1 : TopologicalSpace F],   (Bundle.Trivial.triv
ialization B F).baseSet = S…
· 使用定理 `Bundle.Trivial.trivialization_symm_apply`：∀ (B : Type u_1) (F : Type u_2
) [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] [inst_2 : Zero F] (b
 : B)   (f : F), (Bundle.Trivi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma symmL_trivialization (x : B) :
    (trivialization B F).symmL 𝕜 x = ContinuousLinearMap.id 𝕜 F := by
  ext; simp [trivialization_symm_apply B F]

set_option backward.isDefEq.respectTransparency false in
/-
**Bundle.Trivial.continuousLinearEquivAt_trivialization** 是 Mathlib 中的一个定理，位于命名空
间 `Bundle.Trivial`。
形式化陈述：∀ (𝕜 : Type u_1) (B : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] [inst_3 : T
opologicalSpace B] (x : B),   Bundle.Trivialization.continuousLinearEquivAt 𝕜 (B
undle.Trivial.trivialization B F) x ⋯ =     ContinuousLinearEquiv.refl 𝕜 F
参数：𝕜 : Type u_1；B : Type u_2；F : Type u_3；x : B；Bundle.Trivial.trivialization B 
F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `Bundle.Trivial.trivialization.isLinear`：∀ (𝕜 : Type u_1) (B : Type u_2) 
(F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
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
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_apply`：∀ (R : Type u_1) {B
 : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R
]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivial.trivialization_apply`：∀ (B : Type u_1) (F : Type u_2) [in
st : TopologicalSpace B] [inst_1 : TopologicalSpace F]   (a : Bundle.TotalSpace 
F (Bundle.Trivial B F)), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma continuousLinearEquivAt_trivialization (x : B) :
    (trivialization B F).continuousLinearEquivAt 𝕜 x (mem_univ _) =
      ContinuousLinearEquiv.refl 𝕜 F := by
  ext; simp

end Bundle.Trivial

/-! ### Direct sum of two vector bundles -/

section

variable (𝕜 : Type*) {B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] (F₁ : Type*)
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type*) [TopologicalSpace (TotalSpace F₁ E₁)]
  (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)]

namespace Bundle.Trivialization

variable {F₁ E₁ F₂ E₂}
variable [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

/-
**Bundle.Trivialization.prod.isLinear** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triviali
zation.prod`。
形式化陈述：∀ (𝕜 : Type u_1) {B : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : TopologicalSpace B] {F₁ : Type u_3}   [inst_2 : NormedAddCommGroup F₁] [inst_
3 : NormedSpace 𝕜 F₁] {E₁ : B → Type u_4}   [inst_4 : TopologicalSpace (Bundle.T
otalSpace F₁ E₁)] {F₂ : Type u_5} [inst_5 : NormedAddCommGroup F₂]   [inst_6 : N
ormedSpace 𝕜 F₂] {E₂ : B → Type u_6} [inst_7 : TopologicalSpace (Bundle.TotalSpa
ce F₂ E₂)]   [inst_8 : (x : B) → AddCommMonoid (E₁ x)] [inst_9 : (x : B) → _root
_.Module 𝕜 (E₁ x)]   [inst_10 : (x : B) → AddCommMonoid (E₂ x)] [inst_11 : (x : 
B) → _root_.Module 𝕜 (E₂ x)]   (e₁ : Bundle.Trivialization F₁ Bundle.TotalSpace.
proj) (e₂ : Bundle.Trivialization F₂ Bundle.TotalSpace.proj)   [Bundle.Trivializ
ation.IsLinear 𝕜 e₁] [Bundle.Trivialization.IsLinear 𝕜 e₂],   Bundle.Trivializat
ion.IsLinear 𝕜 (e₁.prod e₂)
参数：𝕜 : Type u_1；Bundle.TotalSpace F₁ E₁；Bundle.TotalSpace F₂ E₂；x : B；E₁ x；x : B
；E₁ x；x : B；E₂ x；x : B；E₂ x；e₁ : Bundle.Trivialization F₁ Bundle.TotalSpace.proj
；e₂ : Bundle.Trivialization F₂ Bundle.TotalSpace.proj；e₁.prod e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `Bundle.Trivialization.linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type 
u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalS…
-/
instance prod.isLinear [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] : (e₁.prod e₂).IsLinear 𝕜 where
  linear := fun _ ⟨h₁, h₂⟩ =>
    (((e₁.linear 𝕜 h₁).mk' _).prodMap ((e₂.linear 𝕜 h₂).mk' _)).isLinear

@[simp]
/-
**Bundle.Trivialization.coordChangeL_prod** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：coordChangeL_prod [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.Is
Linear 𝕜] ⦃b⦄ (hb : (b in e₁.baseSet ∧ b in e₂.baseSet) ∧ b in e₁'.baseSet ∧ b i
n e₂'.baseSet) : ((e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b : F₁ × F₂ ->L[𝕜] 
F₁ × F₂) = (e₁.coordChangeL 𝕜 e₁' b : F₁ ->L[𝕜] F₁).prodMap (e₂.coordChangeL 𝕜 e
₂' b)
参数：hb : (b in e₁.baseSet ∧ b in e₂.baseSet) ∧ b in e₁'.baseSet ∧ b in e₂'.baseSe
t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.prod.isLinear`：∀ (𝕜 : Type u_1) {B : Type u_2} [in
st : NontriviallyNormedField 𝕜] [inst_1 : TopologicalSpace B] {F₁ : Type u_3}   
[inst_2 : NormedAddCommGr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.ext_iff`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `ContinuousLinearMap.coe_prodMap'`：coe_prodMap' (f₁ : M₁ ->L[R] M₂) (f₂ :
 M₃ ->L[R] M₄) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Bundle.Trivialization.coordChangeL_apply'`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSp
ace F]   [inst_2 : TopologicalS…
-/
theorem coordChangeL_prod [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] ⦃b⦄
    (hb : (b ∈ e₁.baseSet ∧ b ∈ e₂.baseSet) ∧ b ∈ e₁'.baseSet ∧ b ∈ e₂'.baseSet) :
    ((e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b : F₁ × F₂ →L[𝕜] F₁ × F₂) =
      (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁).prodMap (e₂.coordChangeL 𝕜 e₂' b) := by
  rw [ContinuousLinearMap.ext_iff, ContinuousLinearMap.coe_prodMap']
  rintro ⟨v₁, v₂⟩
  change
    (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
      (e₁.coordChangeL 𝕜 e₁' b v₁, e₂.coordChangeL 𝕜 e₂' b v₂)
  rw [e₁.coordChangeL_apply e₁', e₂.coordChangeL_apply e₂', (e₁.prod e₂).coordChangeL_apply']
  exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]

variable {e₁ e₂} [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
/-
**Bundle.Trivialization.prod_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializa
tion`。
形式化陈述：prod_apply' [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {x : B} (hx₁ : x in e₁.baseSet
) (hx₂ : x in e₂.baseSet) (v₁ : E₁ x) (v₂ : E₂ x) : prod e₁ e₂ ⟨x, (v₁, v₂)⟩ = ⟨
x, e₁.continuousLinearEquivAt 𝕜 x hx₁ v₁, e₂.continuousLinearEquivAt 𝕜 x hx₂ v₂⟩
参数：hx₁ : x in e₁.baseSet；hx₂ : x in e₂.baseSet；v₁ : E₁ x；v₂ : E₂ x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply' [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {x : B} (hx₁ : x ∈ e₁.baseSet)
    (hx₂ : x ∈ e₂.baseSet) (v₁ : E₁ x) (v₂ : E₂ x) :
    prod e₁ e₂ ⟨x, (v₁, v₂)⟩ =
      ⟨x, e₁.continuousLinearEquivAt 𝕜 x hx₁ v₁, e₂.continuousLinearEquivAt 𝕜 x hx₂ v₂⟩ :=
  rfl

end Bundle.Trivialization

open Trivialization

variable [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, AddCommMonoid (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

set_option backward.defeqAttrib.useBackward true in
/-- The product of two vector bundles is a vector bundle. -/
/-
**VectorBundle.prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：VectorBundle.prod [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂] : VectorBu
ndle 𝕜 (F₁ × F₂) (E₁ ×ᵇ E₂) where trivialization_linear'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.prod.isLinear`：∀ (𝕜 : Type u_1) {B : Type u_2} [in
st : NontriviallyNormedField 𝕜] [inst_1 : TopologicalSpace B] {F₁ : Type u_3}   
[inst_2 : NormedAddCommGr…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `ContinuousOn.prod_mapL`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField
 𝕜] {M₁ : Type u_5} {M₂ : Type u_6} {M₃ : Type u_7} {M₄ : Type u_8}   [inst_1 : 
SeminormedAd…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_coordChange`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3}
 {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → Add
CommMonoid (E …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContinuousLinearMap.ext_iff`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Bundle.Trivialization.coordChangeL_apply'`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSp
ace F]   [inst_2 : TopologicalS…

--- 原说明 ---
The product of two vector bundles is a vector bundle.
-/
instance VectorBundle.prod [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂] :
    VectorBundle 𝕜 (F₁ × F₂) (E₁ ×ᵇ E₂) where
  trivialization_linear' := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨e₁', e₂', he₁', he₂', rfl⟩
    refine (((continuousOn_coordChange 𝕜 e₁ e₁').mono ?_).prod_mapL 𝕜
      ((continuousOn_coordChange 𝕜 e₂ e₂').mono ?_)).congr ?_ <;>
      dsimp only [prod_baseSet, mfld_simps]
    · mfld_set_tac
    · mfld_set_tac
    · rintro b hb
      rw [ContinuousLinearMap.ext_iff]
      rintro ⟨v₁, v₂⟩
      change (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
        (e₁.coordChangeL 𝕜 e₁' b v₁, e₂.coordChangeL 𝕜 e₂' b v₂)
      rw [e₁.coordChangeL_apply e₁', e₂.coordChangeL_apply e₂', (e₁.prod e₂).coordChangeL_apply']
      exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]

variable {𝕜 F₁ E₁ F₂ E₂}

@[simp]
/-
**Bundle.Trivialization.continuousLinearEquivAt_prod** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：Bundle.Trivialization.continuousLinearEquivAt_prod {e₁ : Trivialization F₁
 (π F₁ E₁)} {e₂ : Trivialization F₂ (π F₂ E₂)} [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {
x : B} (hx : x in (e₁.prod e₂).baseSet) : (e₁.prod e₂).continuousLinearEquivAt 𝕜
 x hx = (e₁.continuousLinearEquivAt 𝕜 x hx.1).prodCongr (e₂.continuousLinearEqui
vAt 𝕜 x hx.2)
参数：π F₁ E₁；π F₂ E₂；hx : x in (e₁.prod e₂).baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.ext`：ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ -> M₂
) = g) : f = g
· 使用定理 `Bundle.Trivialization.prod.isLinear`：∀ (𝕜 : Type u_1) {B : Type u_2} [in
st : NontriviallyNormedField 𝕜] [inst_1 : TopologicalSpace B] {F₁ : Type u_3}   
[inst_2 : NormedAddCommGr…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_apply`：∀ (R : Type u_1) {B
 : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R
]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.Prod.left_inv`：∀ {B : Type u_1} [inst : Topologica
lSpace B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Type u_3}   [
inst_2 : TopologicalSpace…
· 使用定理 `Bundle.Trivialization.Prod.right_inv`：∀ {B : Type u_1} [inst : Topologic
alSpace B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Type u_3}   
[inst_2 : TopologicalSpace…
· 使用定理 `Bundle.Trivialization.Prod.continuous_to_fun`：∀ {B : Type u_1} [inst : T
opologicalSpace B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Type
 u_3}   [inst_2 : TopologicalSpace…
· 使用定理 `Bundle.Trivialization.Prod.continuous_inv_fun`：∀ {B : Type u_1} [inst : 
TopologicalSpace B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Typ
e u_3}   [inst_2 : TopologicalSpace…
· 使用定理 `Bundle.Trivialization.prod.eq_1`：∀ {B : Type u_1} [inst : TopologicalSpa
ce B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Type u_3}   [inst
_2 : TopologicalSpace…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.prod_apply'`：prod_apply' [e₁.IsLinear 𝕜] [e₂.IsLin
ear 𝕜] {x : B} (hx₁ : x in e₁.baseSet) (hx₂ : x in e₂.baseSet) (v₁ : E₁ x) (v₂ :
 E₂ x) : prod e₁ e₂ ⟨x,…
-/
theorem Bundle.Trivialization.continuousLinearEquivAt_prod {e₁ : Trivialization F₁ (π F₁ E₁)}
    {e₂ : Trivialization F₂ (π F₂ E₂)} [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {x : B}
    (hx : x ∈ (e₁.prod e₂).baseSet) :
    (e₁.prod e₂).continuousLinearEquivAt 𝕜 x hx =
      (e₁.continuousLinearEquivAt 𝕜 x hx.1).prodCongr (e₂.continuousLinearEquivAt 𝕜 x hx.2) := by
  ext v : 2
  obtain ⟨v₁, v₂⟩ := v
  rw [(e₁.prod e₂).continuousLinearEquivAt_apply 𝕜, Trivialization.prod]
  exact (congr_arg Prod.snd (prod_apply' 𝕜 hx.1 hx.2 v₁ v₂) :)

end

/-! ### Pullbacks of vector bundles -/

section

variable (R 𝕜 : Type*) {B : Type*} (F : Type*) (E : B → Type*) {B' : Type*} (f : B' → B)

-- This instance exists to avoid an nsmul diamond.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [∀ x : B, AddCommMonoid (E x)] [i : ∀ x, Module R (E x)] (x : B') :
    SMul R ((f *ᵖ E) x) :=
  inferInstanceAs <| SMul R (E (f x))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [i : ∀ x : B, AddCommMonoid (E x)] (x : B') : AddCommMonoid ((f *ᵖ E) x) :=
  inferInstanceAs <| AddCommMonoid (E (f x))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [∀ x : B, AddCommMonoid (E x)] [i : ∀ x, Module R (E x)] (x : B') :
    Module R ((f *ᵖ E) x) :=
  inferInstanceAs <| Module R (E (f x))

variable {E F} [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B] [∀ x, AddCommMonoid (E x)]
  [∀ x, Module 𝕜 (E x)] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]
/-
**Bundle.Trivialization.pullback_linear** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bundle.Trivialization.pullback_linear (e : Trivialization F (π F E)) [e.Is
Linear 𝕜] (f : K) : (e.pullback (B'
参数：e : Trivialization F (π F E)；f : K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Bundle.Trivialization.linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type 
u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalS…
-/
instance Bundle.Trivialization.pullback_linear (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (f : K) : (e.pullback (B' := B') f).IsLinear 𝕜 where
  linear _ h := e.linear 𝕜 h
/-
**VectorBundle.pullback** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：VectorBundle.pullback [forall x, TopologicalSpace (E x)] [FiberBundle F E]
 [VectorBundle 𝕜 F E] (f : K) : VectorBundle 𝕜 F ((f : B' -> B) *ᵖ E) where triv
ialization_linear'
参数：E x；f : K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `continuousOn_coordChange`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3}
 {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → Add
CommMonoid (E …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.coordChangeL_apply'`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSp
ace F]   [inst_2 : TopologicalS…
-/
instance VectorBundle.pullback [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (f : K) : VectorBundle 𝕜 F ((f : B' → B) *ᵖ E) where
  trivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine ((continuousOn_coordChange 𝕜 e e').comp
      (map_continuous f).continuousOn fun b hb => hb).congr ?_
    rintro b (hb : f b ∈ e.baseSet ∩ e'.baseSet); ext v
    change ((e.pullback f).coordChangeL 𝕜 (e'.pullback f) b) v = (e.coordChangeL 𝕜 e' (f b)) v
    rw [e.coordChangeL_apply e' hb, (e.pullback f).coordChangeL_apply' _]
    exacts [rfl, hb]

end

