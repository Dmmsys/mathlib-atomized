/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic

/-!
# Presentation of a cokernel

If `f : M₁ →ₗ[A] M₂` is a linear map between modules,
`pres₂` is a presentation of `M₂` and `g₁ : ι → M₁` is
a family of generators of `M₁` (which is expressed as
`hg₁ : Submodule.span A (Set.range g₁) = ⊤`), then we
provide a way to obtain a presentation of the cokernel of `f`.
It requires an additional data `data : pres₂.CokernelData f g₁`,
which consists of liftings of the images by `f` of
the generators of `M₁` as linear combinations of the
generators of `M₂`. Then, we obtain a presentation
`pres₂.cokernel data hg₁ : Presentation A (M₂ ⧸ LinearMap.range f)`.

More generally, if we have an exact sequence `M₁ → M₂ → M₃ → 0`,
we obtain a presentation of `M₃`, see `Presentation.ofExact`.

-/

@[expose] public section

universe w w₁ w₂₀ w₂₁ v₁ v₂ v₃ u

namespace Module

variable {A : Type u} [Ring A] {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

namespace Presentation

section Cokernel

variable (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) (f : M₁ →ₗ[A] M₂)
  {ι : Type w₁} (g₁ : ι → M₁)

/-- Given a linear map `f : M₁ →ₗ[A] M₂`, a presentation of `M₂` and a choice
of generators of `M₁`, this structure specifies a lifting of the image by `f`
of each generator of `M₁` as a linear combination of the generators of `M₂`. -/
/-
**Module.Presentation.CokernelData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module.Presentat
ion`。
形式化陈述：{A : Type u} →   [inst : Ring A] →     {M₁ : Type v₁} →       {M₂ : Type v
₂} →         [inst_1 : AddCommGroup M₁] →           [inst_2 : _root_.Module A M₁
] →             [inst_3 : AddCommGroup M₂] →               [inst_4 : _root_.Modu
le A M₂] →                 Module.Presentation A M₂ → (M₁ →ₗ[A] M₂) → {ι : Type 
w₁} → (ι → M₁) → Type (max (max u w₁) w₂₀)
参数：M₁ →ₗ[A] M₂；ι → M₁；max (max u w₁) w₂₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linear map `f : M₁ →ₗ[A] M₂`, a presentation of `M₂` and a choice
of generators of `M₁`, this structure specifies a lifting of the image by `f`
of each generator of `M₁` as a linear combination of the generators of `M₂`.
-/
structure CokernelData where
  /-- a lifting of `f (g₁ i)` in `pres₂.G →₀ A` -/
  lift (i : ι) : pres₂.G →₀ A
  π_lift (i : ι) : pres₂.π (lift i) = f (g₁ i)

/-- Constructor for `Presentation.CokernelData` in case we have a chosen set-theoretic
section of the projection `(pres₂.G →₀ A) → M₂`. -/
@[simps]
/-
**Module.Presentation.CokernelData.ofSection** 是 Mathlib 中的一个定义，位于命名空间 `Module.P
resentation.CokernelData`。
形式化陈述：{A : Type u} →   [inst : Ring A] →     {M₁ : Type v₁} →       {M₂ : Type v
₂} →         [inst_1 : AddCommGroup M₁] →           [inst_2 : _root_.Module A M₁
] →             [inst_3 : AddCommGroup M₂] →               [inst_4 : _root_.Modu
le A M₂] →                 (pres₂ : Module.Presentation A M₂) →                 
  (f : M₁ →ₗ[A] M₂) →                     {ι : Type w₁} →                       
(g₁ : ι → M₁) →                         (s : M₂ → pres₂.G →₀ A) → (∀ (m₂ : M₂), 
pres₂.π (s m₂) = m₂) → pres₂.CokernelData f g₁
参数：pres₂ : Module.Presentation A M₂；f : M₁ →ₗ[A] M₂；g₁ : ι → M₁；s : M₂ → pres₂.G
 →₀ A；∀ (m₂ : M₂), pres₂.π (s m₂) = m₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Presentation.CokernelData` in case we have a chosen set-theoret
ic
section of the projection `(pres₂.G →₀ A) → M₂`.
-/
def CokernelData.ofSection (s : M₂ → (pres₂.G →₀ A))
    (hs : ∀ (m₂ : M₂), pres₂.π (s m₂) = m₂) :
    pres₂.CokernelData f g₁ where
  lift i := s (f (g₁ i))
  π_lift i := by simp [hs]
/-
**Module.Presentation.nonempty_cokernelData** 是 Mathlib 中的一个实例，位于命名空间 `Module.Pr
esentation`。
形式化陈述：nonempty_cokernelData : Nonempty (pres₂.CokernelData f g₁)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用引理 `Module.Relations.Solution.IsPresentation.surjective_π`：surjective_π : Fu
nction.Surjective solution.π
· 使用定理 `Module.Presentation.toIsPresentation`：∀ {A : Type u} [inst : Ring A] {M 
: Type v} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module A M]   (self : Modul
e.Presentation A M), self.…
-/
instance nonempty_cokernelData :
    Nonempty (pres₂.CokernelData f g₁) := by
  obtain ⟨s, hs⟩ := pres₂.surjective_π.hasRightInverse
  exact ⟨CokernelData.ofSection _ _ _ s hs⟩

variable {g₁ f} (data : pres₂.CokernelData f g₁)

/-- The shape of the presentation by generators and relations of the cokernel
of `f : M₁ →ₗ[A] M₂`. It consists of a generator for each generator of `M₂`, and
there are two types of relations: one for each relation in the presentation in `M₂`,
and one for each generator of `M₁`. -/
@[simps]
/-
**Module.Presentation.cokernelRelations** 是 Mathlib 中的一个定义，位于命名空间 `Module.Presen
tation`。
形式化陈述：cokernelRelations : Relations A where G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shape of the presentation by generators and relations of the cokernel
of `f : M₁ →ₗ[A] M₂`. It consists of a generator for each generator of `M₂`, and
there are two types of relations: one for each relation in the presentation in `
M₂`,
and one for each generator of `M₁`.
-/
def cokernelRelations : Relations A where
  G := pres₂.G
  R := Sum pres₂.R ι
  relation
    | .inl r => pres₂.relation r
    | .inr i => data.lift i

/-- The obvious solution in `M₂ ⧸ LinearMap.range f` to the equations in
`pres₂.cokernelRelations data`. -/
@[simps]
/-
**Module.Presentation.cokernelSolution** 是 Mathlib 中的一个定义，位于命名空间 `Module.Present
ation`。
形式化陈述：cokernelSolution : (pres₂.cokernelRelations data).Solution (M₂ ⧸ LinearMap
.range f) where var g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious solution in `M₂ ⧸ LinearMap.range f` to the equations in
`pres₂.cokernelRelations data`.
-/
def cokernelSolution :
    (pres₂.cokernelRelations data).Solution (M₂ ⧸ LinearMap.range f) where
  var g := Submodule.mkQ _ (pres₂.var g)
  linearCombination_var_relation := by
    intro x
    erw [← Finsupp.apply_linearCombination]
    obtain (r | i) := x
    · erw [pres₂.linearCombination_var_relation]
      dsimp
    · erw [data.π_lift]
      simp

variable (hg₁ : Submodule.span A (Set.range g₁) = ⊤)

namespace cokernelSolution

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel can be defined by generators and relations. -/
/-
**Module.Presentation.cokernelSolution.isPresentationCore** 是 Mathlib 中的一个定义，位于命
名空间 `Module.Presentation.cokernelSolution`。
形式化陈述：isPresentationCore : Relations.Solution.IsPresentationCore.{w} (pres₂.coke
rnelSolution data) where desc s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Presentation.toIsPresentation`：∀ {A : Type u} [inst : Ring A] {M 
: Type v} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module A M]   (self : Modul
e.Presentation A M), self.…

--- 原说明 ---
The cokernel can be defined by generators and relations.
-/
noncomputable def isPresentationCore :
    Relations.Solution.IsPresentationCore.{w}
      (pres₂.cokernelSolution data) where
  desc s := (LinearMap.range f).liftQ (pres₂.desc
    { var := s.var
      linearCombination_var_relation :=
        fun r ↦ s.linearCombination_var_relation (.inl r) }) (by
          rw [LinearMap.range_eq_map, ← hg₁, Submodule.map_span, Submodule.span_le,
            Set.image_subset_iff]
          rintro _ ⟨i, rfl⟩
          rw [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, ← data.π_lift,
            Relations.Solution.IsPresentation.π_desc_apply]
          exact s.linearCombination_var_relation (.inr i))
  postcomp_desc s := by aesop
  postcomp_injective h := by
    ext : 1
    apply pres₂.toIsPresentation.postcomp_injective
    ext g
    exact Relations.Solution.congr_var h g

include hg₁ in
/-
**Module.Presentation.cokernelSolution.isPresentation** 是 Mathlib 中的一个引理，位于命名空间 
`Module.Presentation.cokernelSolution`。
形式化陈述：isPresentation : (pres₂.cokernelSolution data).IsPresentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Relations.Solution.IsPresentationCore.isPresentation`：isPresentat
ion {solution : relations.Solution M} (h : IsPresentationCore.{max u v w₀} solut
ion) : solution.IsPresentation where bijective
-/
lemma isPresentation : (pres₂.cokernelSolution data).IsPresentation :=
  (isPresentationCore pres₂ data hg₁).isPresentation

end cokernelSolution

/-- The presentation of the cokernel of a linear map `f : M₁ →ₗ[A] M₂` that is obtained
from a presentation `pres₂` of `M₂`, a choice of generators `g₁ : ι → M₁` of `M₁`,
and an additional data in `pres₂.CokernelData f g₁`. -/
@[simps!]
/-
**Module.Presentation.cokernel** 是 Mathlib 中的一个定义，位于命名空间 `Module.Presentation`。
形式化陈述：cokernel : Presentation A (M₂ ⧸ LinearMap.range f)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Presentation.cokernelSolution.isPresentation`：isPresentation : (p
res₂.cokernelSolution data).IsPresentation

--- 原说明 ---
The presentation of the cokernel of a linear map `f : M₁ →ₗ[A] M₂` that is obtai
ned
from a presentation `pres₂` of `M₂`, a choice of generators `g₁ : ι → M₁` of `M₁
`,
and an additional data in `pres₂.CokernelData f g₁`.
-/
def cokernel : Presentation A (M₂ ⧸ LinearMap.range f) :=
  ofIsPresentation (cokernelSolution.isPresentation pres₂ data hg₁)

end Cokernel

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given an exact sequence of `A`-modules `M₁ → M₂ → M₃ → 0`, this is the presentation
of `M₃` that is obtained from a presentation `pres₂` of `M₂`, a choice of generators
`g₁ : ι → M₁` of `M₁`, and an additional data in a `Presentation.CokernelData` structure. -/
@[simps!]
/-
**Module.Presentation.ofExact** 是 Mathlib 中的一个定义，位于命名空间 `Module.Presentation`。
形式化陈述：ofExact {f : M₁ ->ₗ[A] M₂} {g : M₂ ->ₗ[A] M₃} (pres₂ : Presentation.{w₂₀, 
w₂₁} A M₂) {ι : Type w₁} {g₁ : ι -> M₁} (data : pres₂.CokernelData f g₁) (hfg : 
Function.Exact f g) (hg : Function.Surjective g) (hg₁ : Submodule.span A (Set.ra
nge g₁) = ⊤) : Presentation A M₃
参数：pres₂ : Presentation.{w₂₀, w₂₁} A M₂；data : pres₂.CokernelData f g₁；hfg : Fun
ction.Exact f g；hg : Function.Surjective g；hg₁ : Submodule.span A (Set.range g₁)
 = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an exact sequence of `A`-modules `M₁ → M₂ → M₃ → 0`, this is the presentat
ion
of `M₃` that is obtained from a presentation `pres₂` of `M₂`, a choice of genera
tors
`g₁ : ι → M₁` of `M₁`, and an additional data in a `Presentation.CokernelData` s
tructure.
-/
noncomputable def ofExact {f : M₁ →ₗ[A] M₂} {g : M₂ →ₗ[A] M₃}
    (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) {ι : Type w₁} {g₁ : ι → M₁}
    (data : pres₂.CokernelData f g₁)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hg₁ : Submodule.span A (Set.range g₁) = ⊤) :
    Presentation A M₃ :=
  (pres₂.cokernel data hg₁).ofLinearEquiv (hfg.linearEquivOfSurjective hg)

end Presentation

end Module

